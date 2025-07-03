-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

-- In this module we use data-flow analysis to detect when variables are used before being
-- initialized and when control flows to the end of a non-void function without returning. Make sure
-- that you call ir.clean first, so that it does the right thing in the presence of `while true`
-- loops.

local ir = require "pallene.ir"
local flow = require "pallene.flow"

local uninitialized = {}

local function cmd_sets_value_of_local_upvalue_box(cmd)
    return cmd._tag == "ir.Cmd.SetField" and cmd.rec_typ.is_upvalue_box and
                cmd.src_rec._tag == "ir.Value.LocalVar"
end

local function make_uninitialized_framework(func)
    local entry_constant_set = {}
    local nvars = #func.vars
    local nargs = #func.typ.arg_types
    for var_id = 1, nvars do
        local is_function_argument = var_id <= nargs
        if not is_function_argument then
            entry_constant_set[var_id] = true
        end
    end

    local function cmd_transfer_function(block_i, cmd_i, gk)
        local cmd = func.blocks[block_i].cmds[cmd_i]
        -- `SetField` instructions can count as initializers when the target is an upvalue box. This
        -- is because upvalue boxes are allocated, but not initialized upon declaration.
        if cmd_sets_value_of_local_upvalue_box(cmd) then
            gk:kill(assert(cmd.src_rec.id))
        end

        -- Artificial initializers introduced by the compiler do not count.
        if not (cmd._tag == "ir.Cmd.NewRecord" and cmd.rec_typ.is_upvalue_box) then
            for _, v_id in ipairs(ir.get_dsts(cmd)) do
                gk:kill(v_id)
            end
        end
    end

    local args = flow.SetFrameworkArguments()
    args.direction             = flow.Order.Forward
    args.set_operation         = flow.SetOperation.Union
    args.entry_constant_set    = entry_constant_set
    args.cmd_transfer_function = cmd_transfer_function
    args.block_list            = func.blocks
    local framework = flow.make_set_framework(args)

    return framework
end

function uninitialized.verify_variables(module)

    local errors = {}

    for _, func in ipairs(module.functions) do

        local framework = make_uninitialized_framework(func)
        local uninit = flow.flow_analysis(func.blocks, framework)

        -- check for errors
        local reported_variables = {} -- (only one error message per variable)

        local function report_error_if_uninitialized(cmd_uninit, src, loc)
            if src._tag == "ir.Value.LocalVar" and cmd_uninit[src.id] then
                local v = src.id
                if not reported_variables[v] then
                    reported_variables[v] = true
                    local name = assert(func.vars[v].name)
                    table.insert(errors, loc:format_error(
                        "error: variable '%s' is used before being initialized", name))
                end
            end
        end

        for block_i, block in ipairs(func.blocks) do
            local block_uninit = uninit[block_i].cmds
            for cmd_i, cmd in ipairs(block.cmds) do
                local cmd_uninit = block_uninit[cmd_i]
                local loc = cmd.loc
                if cmd_sets_value_of_local_upvalue_box(cmd) then
                    -- setting the value of a boxed upvalue counts as writing to the variable
                    -- instead of reading it, so we don't check if cmd.src_rec is initialized here
                    report_error_if_uninitialized(cmd_uninit, assert(cmd.src_v), loc)
                else
                    for _, src in ipairs(ir.get_srcs(cmd)) do
                        report_error_if_uninitialized(cmd_uninit, src, loc)
                    end
                end
            end
        end

        local exit_uninit = uninit[#func.blocks].finish
        if #func.ret_vars > 0 then
            local ret1 = func.ret_vars[1]
            if exit_uninit[ret1] then
                assert(func.loc)
                table.insert(errors, func.loc:format_error(
                    "control reaches end of function with non-empty return type"))
            end
        end
    end

    if #errors == 0 then
        return module, {}
    else
        return false, errors
    end
end

return uninitialized
