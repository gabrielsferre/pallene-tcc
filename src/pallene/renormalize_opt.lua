-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local renormalize_opt = {}

local ir = require("pallene.ir")
local flow = require("pallene.flow")

local function make_loop_tracked_arrays_framework(func, loop_id)

    local loop = func.for_loops[loop_id]

    local set_elements_list = {}
    for var_i = 1, #func.vars do
        set_elements_list[var_i] = var_i
    end

    local function cmd_transfer_function(block_i, cmd_i, gk)
        local block_is_in_loop =
            block_i >= loop.body_first_block_id and block_i <= loop.body_last_block_id
        local cmd = func.blocks[block_i].cmds[cmd_i]

        local cmd_tag = cmd._tag
        if      cmd_tag ~= "ir.Cmd.RenormArray" and
                cmd_tag ~= "ir.Cmd.GetArr" and
                cmd_tag ~= "ir.Cmd.SetArr" then
            local src_list = ir.get_srcs(cmd)
            for _, src in ipairs(src_list) do
                if src._tag == "Value.LocalVar" then
                    gk:kill(src.id)
                end
            end
        end

        local dst_list = ir.get_dsts(cmd)
        for _, dst in ipairs(dst_list) do
            gk:kill(dst)
        end

        if not block_is_in_loop and cmd._tag == "ir.Cmd.NewArr" then
            gk:gen(cmd.dst)
        end

        return gk
    end

    local args = flow.SetFrameworkArguments()
    args.direction             = flow.Order.Forward
    args.set_operation         = flow.SetOperation.Intersection(set_elements_list)
    args.entry_constant_set    = {}
    args.cmd_transfer_function = cmd_transfer_function
    args.block_list            = func.blocks
    local framework = flow.make_set_framework(args)

    return framework
end

local function get_arrays_whose_renormalize_cant_be_optimized(func, loop_id, tracked_arrays)

    local array_set = {}

    local loop = func.for_loops[loop_id]
    local iter_var_id = loop.iteration_variable_id
    local iter_var_is_modified = false
    for block_id = loop.body_first_block_id, loop.body_last_block_id do
        local block = func.blocks[block_id]
        local block_tracked = tracked_arrays[block_id].cmds
        for cmd_i, cmd in ipairs(block.cmds) do
            if cmd._tag ~= "ir.Cmd.ForStep" then
                local dsts = ir.get_dsts(cmd)
                for _, dst in ipairs(dsts) do
                    if dst == iter_var_id then
                        iter_var_is_modified = true
                    end
                end
            end

            if cmd._tag == "ir.Cmd.RenormArr" and cmd.src_arr._tag == "ir.Value.LocalVar" then
                local cmd_tracked = block_tracked[cmd_i]
                local array_id = assert(cmd.src_arr.id)
                local index_is_iter_var =
                    cmd.src_i._tag == "ir.Value.LocalVar" and cmd.src_i.id == iter_var_id
                if not (index_is_iter_var and cmd_tracked[array_id]) then
                    array_set[array_id] = true
                end
            end
        end
    end

    if iter_var_is_modified then
        -- If the iteration variable is modified, no renormalize can be optimized.
        -- It's easier to just put all variables in the set instead of picking only arrays.
        for _,var_id in ipairs(func.vars) do
            array_set[var_id] = true
        end
    end
    return array_set
end

local function process_function(func)

    for loop_id, loop in ipairs(func.for_loops) do

        local framework = make_loop_tracked_arrays_framework(func, loop_id)
        local tracked_arrays = flow.flow_analysis(func.blocks, framework)

        if loop.step_is_positive then
            local cannot_optimize =
                get_arrays_whose_renormalize_cant_be_optimized(func, loop_id, tracked_arrays)
            local arrays_to_optimize = {}

            -- erase renormalizes inside loop body
            for block_id = loop.body_first_block_id, loop.body_last_block_id do
                local block = func.blocks[block_id]
                for cmd_i, cmd in ipairs(block.cmds) do
                    if cmd._tag == "ir.Cmd.RenormArr" then
                        local src_arr = assert(cmd.src_arr)
                        if src_arr._tag == "ir.Value.LocalVar" and
                                not cannot_optimize[src_arr.id] then
                            arrays_to_optimize[src_arr.id] = true
                            block.cmds[cmd_i] = ir.Cmd.Nop
                        end
                    end
                end
            end

            -- insert renomalizes outside loop body
            local limit = loop.limit_value
            local new_block = ir.BasicBlock()
            local loc = loop.loc
            for array_var_id, _ in pairs(arrays_to_optimize) do
                -- we must create a new block for the renormalizes so we can skip them when the loop
                -- is not taken
                local renorm = ir.Cmd.RenormArr(loc, ir.Value.LocalVar(array_var_id), limit)
                table.insert(new_block.cmds, renorm)
                func.renormalize_count = func.renormalize_count + 1;
            end
            if #new_block.cmds > 0 then
                local new_block_id = loop.prep_block_id + 1
                local new_block_jump = ir.Cmd.Jmp(2)
                table.insert(new_block, new_block_jump)

                local prep_block = func.blocks[loop.prep_block_id]
                local prep_jump = assert(ir.get_jump(prep_block))

                ir.insert_block(func, new_block, new_block_id)
                assert(prep_jump._tag == "ir.Cmd.JmpIf")
                prep_jump.target_true = new_block_id
            end
        end
    end
end

function renormalize_opt.run(module)
    local count = 0
    for _, func in ipairs(module.functions) do
        func.renormalize_count = 0
        process_function(func)
        count = count + func.renormalize_count
    end
    print("renormalizes: "..count)

    return module, {}
end

return renormalize_opt
