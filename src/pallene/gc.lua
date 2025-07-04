-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local ir = require "pallene.ir"
local flow = require "pallene.flow"
local types = require "pallene.types"
local tagged_union = require "pallene.tagged_union"

-- GARBAGE COLLECTION
-- ==================
-- For proper garbage collection in Pallene we must ensure that at every potential garbage
-- collection site all the live GC values must be saved to the the Lua stack, where the GC can see
-- them. The way that we do this is that whenever we assign to a local variable that has a GC type
-- we also assign the same value to the Lua stack.
--
-- Potential garbage collection points are explicit ir.CheckGC nodes and function calls. Per the
-- Pallene calling convention, functions can assume that the initial values of function parameters
-- have already been saved by the caller.
--
-- As an optimization, we don't save values to the Lua stack if the associated variable dies before
-- it reaches a potential garbage collection site. The current implementation uses flow analysis to
-- find live variables. So we don't forget, I'm listing here some ideas to improve the analysis ...
-- But it should be said that we don't know if implementing them would be worth the trouble.
--
--   1) Insert fewer checkGC calls in our functions, or move the checkGC calls to places with fewer
--      live variables. (For example, the end of the scope)
--
--   2) Identify functions that don't call the GC (directly or indirectly) and don't treat calls to
--      them as potential GC sites. (Function inlining might mitigate this for small functions)
--
--   3) Use SSA form or some form of reaching definitions analysis so that we we only need to mirror
--      the writes that reach a GC site, instead of always mirroring all writes to a variable if one
--      of them reaches a GC site.

local gc = {}

local function cmd_uses_gc(cmd)
    local tag = cmd._tag
    assert(tagged_union.typename(tag) == "ir.Cmd")
    return tag == "ir.Cmd.CallStatic" or
           tag == "ir.Cmd.CallDyn" or
           tag == "ir.Cmd.CheckGC"
end

local function is_barrier_for_checkgc_optimization(cmd)
    local tag = cmd._tag
    assert(tagged_union.typename(tag) == "ir.Cmd")
    return tag == "ir.Cmd.CallStatic" or
           tag == "ir.Cmd.CallDyn" or
           ir.is_jump(cmd)
end

local function Definition(block_i, cmd_i, var_i)
    return {
        block_i = block_i,
        cmd_i   = cmd_i,
        var_i   = var_i,
    }
end

local function make_definition_list(func)
    local def_list = {}  -- { Definition }
    local cmd_def_map  = {}  -- { block_id => { cmd_id => {definition_id} } }
    local var_def_map  = {}  -- { var_id => {definition_id}? }
    for var_i, var in ipairs(func.vars) do
        if types.is_gc(var.typ) then
            var_def_map[var_i] = {}
        else
            var_def_map[var_i] = false
        end
    end
    for block_i, block in ipairs(func.blocks) do
        local block_map = {}
        cmd_def_map[block_i] = block_map
        for cmd_i, cmd in ipairs(block.cmds) do
            local cmd_map = {}
            block_map[cmd_i] = cmd_map
            for _, dst in ipairs(ir.get_dsts(cmd)) do
                local typ = func.vars[dst].typ
                if types.is_gc(typ) then
                    local def = Definition(block_i,cmd_i,dst)
                    table.insert(def_list, def)
                    local def_id = #def_list
                    table.insert(cmd_map, def_id)

                    local var_defs = var_def_map[dst]
                    table.insert(var_defs, def_id)
                end
            end
        end
    end
    return def_list, cmd_def_map, var_def_map
end

-- Move CheckGC commands to the end of blocks or just before other possible gc-calling commands
function gc.optimize_gc_checks(module)
    local moved_count = 0
    local removed_count = 0
    for _, func in ipairs(module.functions) do
        for _, block in ipairs(func.blocks) do
            local insert_gc_check = false
            local new_cmds = {}
            for _, cmd in ipairs(block.cmds) do
                if cmd._tag == "ir.Cmd.CheckGC" then
                    insert_gc_check = true
                    moved_count = moved_count + 1
                    removed_count = removed_count + 1
                else
                    if insert_gc_check and is_barrier_for_checkgc_optimization(cmd) then
                        table.insert(new_cmds, ir.Cmd.CheckGC)
                        insert_gc_check = false
                        removed_count = removed_count - 1
                    end
                    table.insert(new_cmds, cmd)
                end
            end
            if insert_gc_check then
                table.insert(new_cmds, ir.Cmd.CheckGC)
                removed_count = removed_count - 1
            end
            block.cmds = new_cmds
        end
    end

    print("moved checkgc: "..moved_count)
    print("removed checkgc: "..removed_count)

    return module, {}
end

local function make_live_variables_framework(func)

    local entry_constant_set = {}
    for _, var in ipairs(func.ret_vars) do
        entry_constant_set[var] = true
    end

    local function cmd_transfer_function(block_i, cmd_i, gk)
        local cmd = func.blocks[block_i].cmds[cmd_i]
        for _, dst in ipairs(ir.get_dsts(cmd)) do
            local typ = func.vars[dst].typ
            if types.is_gc(typ) then
                gk:kill(dst)
            end
        end

        for _, src in ipairs(ir.get_srcs(cmd)) do
            if src._tag == "ir.Value.LocalVar" then
                local typ = func.vars[src.id].typ
                if types.is_gc(typ) then
                    gk:gen(src.id)
                end
            end
        end
    end

    local args = flow.SetFrameworkArguments()
    args.direction             = flow.Order.Backwards
    args.set_operation         = flow.SetOperation.Union
    args.entry_constant_set    = entry_constant_set
    args.cmd_transfer_function = cmd_transfer_function
    args.block_list            = func.blocks
    local framework = flow.make_set_framework(args)

    return framework
end

-- Returns information that is used for allocating variables into the Lua stack.
-- The returned data is:
--      * live_gc_vars:
--          for each command, has a list of GC'd variables that are alive during that command.
--      * live_at_same_time:
--          for each GC'd variable, indicates what other GC'd variables are alive at the same time,
--          that is, if both are alive during the same command for some command in the function.
--      * max_frame_size:
--          what's the maximum number of slots of the Lua stack used for storing GC'd variables
--          during the function.
local function compute_stack_slots(func)

    -- 1) Find live GC'd variables for each basic block
    local live_vars_framework = make_live_variables_framework(func)
    local sets_list = flow.flow_analysis(func.blocks, live_vars_framework)

    -- 2) Find which GC'd variables are live at each GC spot in the program and
    --    which  GC'd variables are live at the same time
    local live_gc_vars = {} -- { block_id => { cmd_id => {var_id}? } }
    local live_at_same_time = {} -- { var_id => { var_id => bool? }? }

    -- initialize live_gc_vars
    for _, block in ipairs(func.blocks) do
        local live_on_cmds = {}
        for cmd_i = 1, #block.cmds do
            live_on_cmds[cmd_i] = false
        end
        table.insert(live_gc_vars, live_on_cmds)
    end

    for block_i, block in ipairs(func.blocks) do
        local block_alive_set = sets_list[block_i]
        for cmd_i = #block.cmds, 1, -1 do
            local cmd = block.cmds[cmd_i]
            if cmd_uses_gc(cmd) then
                local cmd_live_set = block_alive_set.cmds[cmd_i - 1] or block_alive_set.finish
                local live_list = {}
                for var,_ in pairs(cmd_live_set) do
                    table.insert(live_list, var)
                end
                live_gc_vars[block_i][cmd_i] = live_list
                for var1,_ in pairs(cmd_live_set) do
                    for var2,_ in pairs(cmd_live_set) do
                        if not live_at_same_time[var1] then
                            live_at_same_time[var1] = {}
                        end
                        live_at_same_time[var1][var2] = true
                    end
                end
            end
        end
    end

    -- 3) Allocate variables to Lua stack slots, ensuring that variables with overlapping lifetimes
    -- get different stack slots. IMPORTANT: stack slots are 0-based. The C we generate prefers
    -- that.

    local max_frame_size = 0
    local slot_of_variable = {} -- { var_id => integer? }

    for v_id = 1, #func.vars do
        slot_of_variable[v_id] = false
    end

    for v1, set in pairs(live_at_same_time) do
        local taken_slots = {}  -- { stack_slot => bool? }
        for v2,_ in pairs(set) do
            local v2_slot = slot_of_variable[v2]
            if v2_slot then
                taken_slots[v2_slot] = true
            end
        end
        for slot = 0, #func.vars do
            if not taken_slots[slot] then
                slot_of_variable[v1] = slot
                max_frame_size = math.max(max_frame_size, slot + 1)
                break
            end
        end
        assert(slot_of_variable[v1], "should always find a slot")
    end

    return live_gc_vars, max_frame_size, slot_of_variable
end

local function make_reaching_definitions_frameworks(func, cmd_def_map, var_def_map)

    local function cmd_transfer_function(block_i, cmd_i, gk)
        local cmd = func.blocks[block_i].cmds[cmd_i]
        for _, dst in ipairs(ir.get_dsts(cmd)) do
            local typ = func.vars[dst].typ
            if types.is_gc(typ) then
                local var_defs = var_def_map[dst]
                for _, def_i in ipairs(var_defs) do
                    gk:kill(def_i)
                end
            end
        end
        local current_defs = cmd_def_map[block_i][cmd_i]
        if current_defs then
            for _, def_i in ipairs(current_defs) do
                gk:gen(def_i)
            end
        end
    end

    local args = flow.SetFrameworkArguments()
    args.direction             = flow.Order.Forward
    args.set_operation         = flow.SetOperation.Union
    args.entry_constant_set    = {}
    args.cmd_transfer_function = cmd_transfer_function
    args.block_list            = func.blocks
    local framework = flow.make_set_framework(args)

    return framework
end

local function compute_vars_to_mirror(func)

    -- 1) Register definitions of GC'd variables
    local def_list, cmd_def_map, var_def_map = make_definition_list(func)

    -- 2) Find reaching definitions for each basic block
    local framework =
        make_reaching_definitions_frameworks(func, cmd_def_map, var_def_map)
    local sets_list = flow.flow_analysis(func.blocks, framework)

    -- 3) Find which definitions reach commands that might call the GC, that is, which definitions
    -- writes have to be mirroed to the stack
    local vars_to_mirror = {}  -- { block_id => { cmd_id => set of var_i } }
    for block_i, block in ipairs(func.blocks) do
        local block_defs = {}
        vars_to_mirror[block_i] = block_defs
        for cmd_i = 1, #block.cmds do
            block_defs[cmd_i] = {}
        end
    end
    for block_i, block in ipairs(func.blocks) do
        local defs_block = sets_list[block_i]
        for cmd_i, cmd in ipairs(block.cmds) do
            if cmd_uses_gc(cmd) then
                local defs_cmd = defs_block.cmds[cmd_i]
                for def_i, _ in pairs(defs_cmd) do
                    local def = def_list[def_i]
                    vars_to_mirror[def.block_i][def.cmd_i][def.var_i] = true
                end
            end
        end
    end

    return vars_to_mirror
end

function gc.compute_gc_info(func)
    local live_gc_vars, max_frame_size, slot_of_variable = compute_stack_slots(func)
    local vars_to_mirror = compute_vars_to_mirror(func)
    return {
        live_gc_vars = live_gc_vars,
        max_frame_size = max_frame_size,
        slot_of_variable = slot_of_variable,
        vars_to_mirror = vars_to_mirror,
    }
end

return gc
