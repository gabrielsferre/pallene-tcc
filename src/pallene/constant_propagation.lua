-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local constant_propagation = {}

local ir = require "pallene.ir"
local flow = require "pallene.flow"
local tagged_union = require "pallene.tagged_union"
local util = require "pallene.util"

local function find_constant_upvalues(func, constant_upvalues)
    for _, block in ipairs(func.blocks) do
        for _, cmd in ipairs(block.cmds) do
            if cmd._tag == "ir.Cmd.InitUpvalues" then
                local closure_constant_upvalues = constant_upvalues[cmd.f_id]
                for u_id, src in ipairs(cmd.srcs) do
                    if ir.is_constant(src) then
                        closure_constant_upvalues[u_id] = src
                    end
                end
            end
        end
    end
end

local function make_constant_propagation_framework(func)
    local var_set = {} -- { set of local_variable_id } set of relevant local variables
    for var_id, var in ipairs(func.vars) do
        local type_tag = var.typ._tag
        if  type_tag == "types.T.Nil" or
            type_tag == "types.T.Boolean" or
            type_tag == "types.T.Integer" or
            type_tag == "types.T.String" or
            type_tag == "types.T.Float" then

            var_set[var_id] = true
        end
    end

    local Value = util.define_local_tagged_union("Value", {
        Undef    = {}, -- undefined
        Nac      = {}, -- not a constant
        Constant = {"value"}, -- ir.Value
    })

    local arg_count = #func.typ.arg_types
    local entry_constant_value = {}
    local identity_element = {}

    for v_id, _ in pairs(var_set) do
        local is_input_variable = v_id <= arg_count
        if is_input_variable then
            entry_constant_value[v_id] = Value.Nac
        else
            entry_constant_value[v_id] = Value.Undef
        end
        identity_element[v_id] = Value.Undef
    end

    local function are_values_equal(v1, v2)
        local result
        if v1._tag ~= v2._tag then
            result = false
        elseif v1._tag == "Value.Constant" then
            result = v1.value == v2.value
        else
            result = true
        end
        return result
    end

    local function join_values(dest, src)
        local dest_tag = dest._tag
        local src_tag = src._tag

        if dest_tag == "Value.Nac" or src_tag == "Value.Nac" then
            dest = Value.Nac
        elseif src_tag == "Value.Undef" then
            dest = dest
        elseif dest_tag == "Value.Undef" then
            dest = util.deep_copy(src)
        else
            if dest.value == src.value then
                dest = dest
            else
                dest = Value.Nac
            end
        end
        return dest
    end

    local function join_maps(dest, src)
        for var_index, src_value in pairs(src) do
            local dest_value = dest[var_index]
            dest[var_index] = join_values(dest_value, src_value)
        end
        return dest
    end

    local function cmd_transfer_function(cmd, map)
        local cmd_tag = cmd._tag
        if cmd_tag == "ir.Cmd.Move" then
            local dst = cmd.dst
            if dst then
                local value
                local src = cmd.src
                local src_tag = src._tag
                if src_tag == "ir.Value.Upvalue" then
                    value = Value.Nac
                elseif src_tag == "ir.Value.LocalVar" then
                    value = map[src.id]
                elseif ir.is_constant(src) then
                    value = Value.Constant(src.value)
                else
                    tagged_union.error(src_tag)
                end
                map[dst] = value
            end
        else
            local dst_list = ir.get_dsts(cmd)
            for _, dst in ipairs(dst_list) do
                if map[dst] then
                    map[dst] = Value.Nac
                end
            end
        end
    end


    local function make_block_transfer_function(block_index)
        local block = func.blocks[block_index]
        local relevant_commands = {}
        for _, cmd in ipairs(block.cmds) do
            local dst_list = ir.get_dsts(cmd)
            for _, dst in ipairs(dst_list) do
                if var_set[dst] then
                    table.insert(relevant_commands, cmd)
                end
            end
        end

        local function block_transfer_function(map, old_map)
            for _, cmd in ipairs(relevant_commands) do
                cmd_transfer_function(cmd, map)
            end

            local map_changed = false
            for var_id, value in pairs(map) do
                if not are_values_equal(value, old_map[var_id]) then
                    map_changed = true
                    break
                end
            end
            return map_changed
        end

        return block_transfer_function
    end

    local function make_block_result(block_index, map)
        local block = func.blocks[block_index]
        local result = {} -- {cmd_i => {local_variable_id => {value}?}
        for cmd_i, cmd in ipairs(block.cmds) do
            local constants = {}
            result[cmd_i] = constants
            for var_i, value in pairs(map) do
                if value._tag == "Value.Constant" then
                    -- we wrap the value inside a table because it can be "nil"
                    constants[var_i] = {value.value}
                end
            end
            cmd_transfer_function(cmd, map)
        end
        return result
    end

    local function copy_map(dest, src)
        for var_i, src_val in pairs(src) do
            dest[var_i] = src_val
        end
        return dest
    end

    local fw = flow.Framework()

    fw.direction = flow.Order.Forward
    fw.identity_element = identity_element
    fw.entry_block_constant_value = entry_constant_value
    fw.join = join_maps
    fw.make_transfer_function = make_block_transfer_function
    fw.make_result = make_block_result
    fw.copy = copy_map

    return fw
end

local function make_ir_value(typ, value)
    local tag = typ._tag
    local ir_value
    if tag == "types.T.Nil" then
        ir_value = ir.Value.Nil
    elseif tag == "types.T.Boolean" then
        ir_value = ir.Value.Bool(value)
    elseif tag == "types.T.Integer" then
        ir_value = ir.Value.Integer(value)
    elseif tag == "types.T.Float" then
        ir_value = ir.Value.Float(value)
    elseif tag == "types.T.String" then
        ir_value = ir.Value.String(value)
    else
        assert(false, "this function is not supposed to handle this type")
    end
    return ir_value
end

local function process_function(func, constant_upvalues)

    local function aux_upvalues(src)
        local ir_value = src
        if src._tag == "ir.Value.Upvalue" and constant_upvalues[src.id] then
            ir_value = constant_upvalues[src.id]
        end
        return ir_value
    end

    -- substituite constant upvalues:
    -- substituting the upvalues before doing the constant folding anaysis makes the substitutions
    -- more effective.
    for _, block in ipairs(func.blocks) do
        for _, cmd in ipairs(block.cmds) do
            local field_names = ir.get_value_field_names(cmd)
            for _, src_name in ipairs(field_names.src) do
                local src = cmd[src_name]
                src = aux_upvalues(src)
                cmd[src_name] = src
            end
            for _, srcs_name in ipairs(field_names.srcs) do
                local srcs = cmd[srcs_name]
                for src_i, src in ipairs(srcs) do
                    src = aux_upvalues(src)
                    cmd[srcs_name][src_i] = src
                end
            end
        end
    end

    local framework = make_constant_propagation_framework(func)
    local analysis_result = flow.flow_analysis(func.blocks, framework)

    local function aux_local_variables(constant_variables, src)
        local ir_value = src
        if src._tag == "ir.Value.LocalVar" and constant_variables[src.id] then
            local value = constant_variables[src.id][1]
            local variable = func.vars[src.id]
            ir_value = make_ir_value(variable.typ, value)
        end
        return ir_value
    end

    for block_i, block in ipairs(func.blocks) do
        local block_result = analysis_result[block_i]
        for cmd_i, cmd in ipairs(block.cmds) do
            local constant_variables = block_result[cmd_i]
            local field_names = ir.get_value_field_names(cmd)
            for _, src_name in ipairs(field_names.src) do
                local src = cmd[src_name]
                src = aux_local_variables(constant_variables, src)
                cmd[src_name] = src
            end
            for _, srcs_name in ipairs(field_names.srcs) do
                local srcs = cmd[srcs_name]
                for src_i, src in ipairs(srcs) do
                    src = aux_local_variables(constant_variables, src)
                    cmd[srcs_name][src_i] = src
                end
            end
        end
    end
end

-- Implements a constant folding optimization for local and global variables. Only substitutes
-- variables that are of non reference types, like integers, floats and strings.
--
-- For local variables, uses flow analysis to identify which accesses can be replaced by literals.
-- For global variables and other variables that are used as upvalues, we take advantage of the fact
-- that an upvalue is enveloped inside a record if it's modified somewhere in the program and is not
-- enveloped if it's not modified. Whenever a global/upvalue is not enveloped, we assume it's
-- constant, hence any access to it can be switched by it's literal value.
function constant_propagation.run(module)
    local constant_upvalues = {} -- { function_id => {upvalue_id => ir.Value?} }
    for func_i = 1, #module.functions do
        constant_upvalues[func_i] = {}
    end
    for func_i, func in ipairs(module.functions) do
        process_function(func, constant_upvalues[func_i])
        find_constant_upvalues(func, constant_upvalues)
    end

    return module, {}
end

return constant_propagation
