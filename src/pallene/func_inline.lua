-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local func_inline = {}

local tagged_union = require("pallene.tagged_union")
local util = require("pallene.util")
local ir = require("pallene.ir")

local function get_called_func_id(calling_func, src_f)
    local called_func_id = false
    local tag = src_f._tag
    if tag == "ir.Value.Upvalue" then
        called_func_id = assert(calling_func.f_id_of_upvalue[src_f.id])
    elseif tag == "ir.Value.LocalVar" then
        called_func_id = assert(calling_func.f_id_of_local[src_f.id])
    else
        tagged_union.error(tag)
    end
    return called_func_id
end

local function update_cmd_if_jumping_past_inline(
    cmd, block_id_of_inlined_call, count_of_inlined_blocks)
    local tag = cmd._tag
    local id_increment = count_of_inlined_blocks - 1
    if tag == "ir.Cmd.Jmp" then
        if cmd.target > block_id_of_inlined_call then
            cmd.target = cmd.target + id_increment
        end
    elseif tag == "ir.Cmd.JmpIf" then
        if cmd.target_true > block_id_of_inlined_call then
            cmd.target_true = cmd.target_true + id_increment
        end
        if cmd.target_false > block_id_of_inlined_call then
            cmd.target_false = cmd.target_false + id_increment
        end
    end
end

local function inline_func(src_func, dst_block_id, dst_cmd_id, dst_func)

    -- set local variables and upvalues

    local src_var_dst_var_map = {} -- { local_var_id => local_var_id }
    for src_var_id, src_var in ipairs(src_func.vars) do
        local dst_var = util.deep_copy(src_var)
        table.insert(dst_func.vars, dst_var)
        local dst_var_id = #dst_func.vars
        src_var_dst_var_map[src_var_id] = dst_var_id
    end

    local src_up_dst_up_map = {} -- { upvalue_id => upvalue_id }
    for src_up_id, src_up in ipairs(src_func.captured_vars) do
        local dst_up = util.deep_copy(src_up)
        table.insert(dst_func.captured_vars, dst_up)
        local dst_up_id = #dst_func.captured_vars
        src_up_dst_up_map[src_up_id] = dst_up_id
    end

    -- create new list of basic blocks

    local calling_command = dst_func.blocks[dst_block_id].cmds[dst_cmd_id]
    local new_block_list = {} -- { ir.BasicBlock }
    for src_block_i, src_block in ipairs(src_func.blocks) do
        local current_block = ir.BasicBlock()
        local is_first_block = src_block_i == 1
        if is_first_block then
            -- move arguments from caller's to callee's variables
            assert(#calling_command.srcs == #src_func.typ.arg_types)
            for value_i, value in ipairs(calling_command.srcs) do
                local dst = src_var_dst_var_map[value_i]
                local cmd = ir.Cmd.Move(calling_command.loc, dst, value)
                table.insert(current_block.cmds, cmd)
            end
        end

        -- copy commands from callee while adjusting indices
        local block_id_increment = dst_block_id - 1
        assert(block_id_increment >= 0)
        for _, src_cmd in ipairs(src_block.cmds) do
            local cmd_copy = util.deep_copy(src_cmd)
            for _, src in ipairs(ir.get_srcs(cmd_copy)) do
                local tag = src._tag
                if tag == "ir.Value.LocalVar" then
                    src.id = src_var_dst_var_map[src.id]
                elseif tag == "ir.Value.Upvalue" then
                    src.id = src_up_dst_up_map[src.id]
                end
            end
            local field_names = ir.get_value_field_names(cmd_copy)
            for _, dst_name in ipairs(field_names.dst) do
                local dst = cmd_copy[dst_name]
                local new_dst = src_var_dst_var_map[dst]
                cmd_copy[dst_name] = new_dst
            end
            for _, dsts_name in ipairs(field_names.dsts) do
                local dst_list = cmd_copy[dsts_name]
                for dst_i = 1, #dst_list do
                    local dst = dst_list[dst_i]
                    local new_dst = src_var_dst_var_map[dst]
                    dst_list[dst_i] = new_dst
                end
            end

            if(cmd_copy._tag == "ir.Cmd.Jmp") then
                cmd_copy.target = cmd_copy.target + block_id_increment
            elseif(cmd_copy._tag == "ir.Cmd.JmpIf") then
                cmd_copy.target_true = cmd_copy.target_true + block_id_increment
                cmd_copy.target_false = cmd_copy.target_false + block_id_increment
            end

            table.insert(current_block.cmds, cmd_copy)
        end

        local is_last_block = src_block_i == #src_func.blocks
        if is_last_block then
            -- move callee's returned values to caller's variables
            assert(not ir.get_jump(src_block),
                    "the last basic block of a function mustn't end with a jump")
            assert(#calling_command.dsts == #src_func.ret_vars)
            for ret_index, dst in ipairs(calling_command.dsts) do
                local original_ret_var_id = src_func.ret_vars[ret_index]
                local new_ret_var_id = src_var_dst_var_map[original_ret_var_id]
                local value = ir.Value.LocalVar(new_ret_var_id)
                local cmd = ir.Cmd.Move(calling_command.loc, dst, value)
                table.insert(current_block.cmds, cmd)
            end
        end
        table.insert(new_block_list, current_block)
    end

    assert(#new_block_list == #src_func.blocks)

    -- merge newly created blocks with the caller's old blocks

    -- move up and update jumps of the caller's blocks that come after the function call
    do
        local initial_block_list_size = #dst_func.blocks
        local final_block_list_size = #dst_func.blocks + #new_block_list - 1
        assert(final_block_list_size > 0)
        -- open up space in the list
        for i = initial_block_list_size + 1, final_block_list_size do
            dst_func.blocks[i] = false
        end

        -- moving blocks in decreasing index order so they don't overwrite
        for i = 0, initial_block_list_size - dst_block_id - 1 do
            local new_block_id = final_block_list_size - i
            local old_block_id = initial_block_list_size - i
            local block = dst_func.blocks[old_block_id]
            dst_func.blocks[new_block_id] = block
            local jump = ir.get_jump(block)
            if jump then
                update_cmd_if_jumping_past_inline(jump, dst_block_id, #new_block_list)
            end
        end
    end

    -- update jumps of blocks before or at the same block as the function call
    for block_i = 1, dst_block_id do
        local block =  dst_func.blocks[block_i]
        local jump = ir.get_jump(block)
        if jump then
            update_cmd_if_jumping_past_inline(jump, dst_block_id, #new_block_list)
        end
    end

    local next_block_id_after_inlined_func = false
    local next_cmd_id_after_inlined_func = false

    local old_call_block_backup = dst_func.blocks[dst_block_id]
    for new_block_i, new_block in ipairs(new_block_list) do
        local block_id_in_caller = new_block_i + dst_block_id - 1
        if new_block_i == 1 then
            -- add commands in the caller's block that come before the call
            local actual_new_block = ir.BasicBlock()
            for cmd_i = 1, dst_cmd_id - 1 do
                local cmd = old_call_block_backup.cmds[cmd_i]
                table.insert(actual_new_block.cmds, cmd)
            end

            for _, cmd in ipairs(new_block.cmds) do
                table.insert(actual_new_block.cmds, cmd)
            end
            dst_func.blocks[block_id_in_caller] = actual_new_block
        else
            dst_func.blocks[block_id_in_caller] = new_block
        end

        if new_block_i == #new_block_list then
            next_block_id_after_inlined_func = block_id_in_caller
            next_cmd_id_after_inlined_func = #new_block.cmds + 1

            -- append rest of caller's block instructions that come after the call
            for cmd_i = dst_cmd_id + 1, #old_call_block_backup.cmds do
                local cmd = old_call_block_backup.cmds[cmd_i]
                table.insert(new_block.cmds, cmd)
            end

        end
    end

    assert(next_block_id_after_inlined_func)
    assert(next_cmd_id_after_inlined_func)
    return next_block_id_after_inlined_func, next_cmd_id_after_inlined_func
end


local function inline_function_calls(module, func)
    -- can't loop through the function trivially because it's changing with the inlining
    local block_i = 1
    local cmd_i = 1
    while block_i <= #func.blocks do
        while cmd_i <= #func.blocks[block_i].cmds do
            local cmd = func.blocks[block_i].cmds[cmd_i]
            local tag = cmd._tag
            if tag == "ir.Cmd.CallStatic" then
                local called_func_id = get_called_func_id(func, cmd.src_f)
                local function_to_inline = module.functions[called_func_id]
                block_i, cmd_i = inline_func(function_to_inline, block_i, cmd_i, func)
            else
                cmd_i = cmd_i + 1
            end
        end
        block_i = block_i + 1
        cmd_i = 1
    end
end

local function InliningInfo()
    return {
        var_increment = 0,
        upvalue_increment = 0,
        block_id_increment = 0,
        func = false,        -- ir.Function
        new_block_list = {}, -- { ir.BasicBlock }
        caller_srcs = false, -- { ir.Value }
        caller_dsts = false, -- { local variable id }
        caller_loc = false,  -- Location
    }
end

local function make_new_blocks_for_inlining(inlining_info)
    local new_block_list = inlining_info.new_block_list
    local func = inlining_info.func
    for block_i, block in ipairs(func.blocks) do
        local new_block = ir.BasicBlock()
        local is_first_block = block_i == 1
        if is_first_block then
            -- move arguments from caller's to callee's variables
            assert(#inlining_info.caller_srcs == #func.typ.arg_types)
            for value_i, value in ipairs(inlining_info.caller_srcs) do
                -- the first local variables of a function are it's arguments, so we can index them
                -- by their order in the "srcs" list
                local var_new_id = value_i + inlining_info.var_increment
                local cmd = ir.Cmd.Move(inlining_info.loc, var_new_id, value)
                table.insert(new_block.cmds, cmd)
            end
        end

        -- copy commands from callee while adjusting indices
        local block_increment = inlining_info.block_id_increment
        for _, src_cmd in ipairs(block.cmds) do
            local cmd_copy = util.deep_copy(src_cmd)
            for _, src in ipairs(ir.get_srcs(cmd_copy)) do
                local tag = src._tag
                if tag == "ir.Value.LocalVar" then
                    src.id = src.id + inlining_info.var_increment
                elseif tag == "ir.Value.Upvalue" then
                    src.id = src.id + inlining_info.upvalue_increment
                end
            end
            local field_names = ir.get_value_field_names(cmd_copy)
            for _, dst_name in ipairs(field_names.dst) do
                local dst = cmd_copy[dst_name]
                local new_dst = dst + inlining_info.var_increment
                cmd_copy[dst_name] = new_dst
            end
            for _, dsts_name in ipairs(field_names.dsts) do
                local dst_list = cmd_copy[dsts_name]
                for dst_i = 1, #dst_list do
                    local dst = dst_list[dst_i]
                    local new_dst = dst + inlining_info.var_increment
                    dst_list[dst_i] = new_dst
                end
            end

            if(cmd_copy._tag == "ir.Cmd.Jmp") then
                cmd_copy.target = cmd_copy.target + block_increment
            elseif(cmd_copy._tag == "ir.Cmd.JmpIf") then
                cmd_copy.target_true = cmd_copy.target_true + block_increment
                cmd_copy.target_false = cmd_copy.target_false + block_increment
            end

            table.insert(new_block.cmds, cmd_copy)
        end

        local is_last_block = block_i == #func.blocks
        if is_last_block then
            -- move callee's returned values to caller's variables
            assert(not ir.get_jump(block),
                    "the last basic block of a function must not end with a jump")
            assert(#inlining_info.caller_dsts == #func.ret_vars)
            for ret_index, dst in ipairs(inlining_info.caller_dsts) do
                local original_ret_var_id = func.ret_vars[ret_index]
                local new_ret_var_id = original_ret_var_id + inlining_info.var_increment
                local value = ir.Value.LocalVar(new_ret_var_id)
                local cmd = ir.Cmd.Move(inlining_info.loc, dst, value)
                table.insert(new_block.cmds, cmd)
            end
        end
        table.insert(new_block_list, new_block)
    end

    assert(#new_block_list == #func.blocks)
end

local function inline_function_calls_(module, func)
    local inlining_info_map = {} -- { block_id => cmd_id => InliningInfo }
    local block_id_increments = {}     -- { block_id => integer }

    for block_i = 1, #func.blocks do
        block_id_increments[block_i] = 0
        inlining_info_map[block_i] = {}
    end

    local var_count = #func.vars
    local upvalue_count = #func.captured_vars

    for block_i, block in ipairs(func.blocks) do
        if block_i > 1 then
            block_id_increments[block_i] =
                block_id_increments[block_i] + block_id_increments[block_i - 1]
        end
        for cmd_i, cmd in ipairs(block.cmds) do
            if cmd._tag == "ir.Cmd.CallStatic" then
                local called_func_id = get_called_func_id(func, cmd.src_f)
                local called_func = module.functions[called_func_id]

                assert(#called_func.blocks > 0)

                local info = InliningInfo()
                info.func = called_func
                info.var_increment = var_count
                info.upvalue_increment = upvalue_count
                info.block_id_increment = block_id_increments[block_i] + block_i - 1
                info.caller_srcs = cmd.srcs
                info.caller_dsts = cmd.dsts
                info.caller_loc = cmd.loc
                inlining_info_map[block_i][cmd_i] = info

                make_new_blocks_for_inlining(info)

                var_count = var_count + #called_func.vars
                upvalue_count = upvalue_count + #called_func.captured_vars
                if block_i < #func.blocks  then
                    block_id_increments[block_i + 1] =
                        block_id_increments[block_i + 1] + #called_func.blocks - 1
                end
            end
        end
    end

    local new_block_count = #func.blocks + block_id_increments[#func.blocks]
    local new_blocks = {}
    for block_i = 1, new_block_count do
        new_blocks[block_i] = false
    end

    for block_i, block in ipairs(func.blocks) do
        local new_block_id = block_i + block_id_increments[block_i]
        new_blocks[new_block_id] = block

        for _, cmd in ipairs(block.cmds) do
            if(cmd._tag == "ir.Cmd.Jmp") then
                cmd.target = cmd.target + block_id_increments[cmd.target]
            elseif(cmd._tag == "ir.Cmd.JmpIf") then
                cmd.target_true = cmd.target_true + block_id_increments[cmd.target_true]
                cmd.target_false = cmd.target_false + block_id_increments[cmd.target_false]
            end
        end
    end

    return inlining_info_map, new_blocks
end

function func_inline.run(module)
    for _, func in ipairs(module.functions) do
        inline_function_calls_(module, func)
        inline_function_calls(module, func)
    end
    return module, {}
end

return func_inline
