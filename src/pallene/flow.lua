-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

-- Functions for doing flow analysis
--
-- The flow.lua file is designed as an API that helps doing flow analysis.
--
-- Flow Analysis introduction
--
-- We give a brief introduction of flow analysis just to get the reader acquainted with the
-- terminology being used here. To better understand the code you should know how flow analys work
-- already.
--
-- Doing flow analysis on a function consists of tracking down properties of it's code along each
-- command. These properties are represented using a set. Each basic block has a "start" set and a
-- "finish" set. The "start" set is the set of values available right before we start to process the
-- block's commands and the "finish" set is the set of values available right after we finish
-- processing the block's commands. Each block also has a "kill" and a "gen" set that help transform
-- the "start" set into the "finish" set. The "kill" set contains the values that will be removed
-- from the running set while "gen" (as in "generate") contains the values that will be added to it.
-- The flow analysis algorithm's input is a collection of "kill" and "gen" sets for each block and
-- the initial values for the "start" sets of each block. During it's runtime, the algorithm updates
-- the "start" and "finish" sets in a loop until they all converge to some value. The algorithm
-- requires a loop because a block's "start" set depends on the "finish" set of it's predecessors or
-- it's successors, depending on what order the flow analysis is being done (some analyses require
-- that we walk through the code backwards).
--
-- API usage:
--
-- When doing flow analysis, follow these steps. Also look at examples of usage inside the codebase,
-- as in "gc.lua".
--
--
-- 1) Create a FlowInfo object and the functions it receives as arguments (see the flow.FlowInfo
-- constructor to learn what those functions are supposed to do).
--
--
-- 2) Call the function "flow.flow_analysis" using as arguments the blocks of the functions you're
-- analysing and the "FlowInfo" object you created in step 3. "flow.flow_analysis" returns a list
-- that contains a set for each block in the function. The returned sets are the starting sets of
-- each corresponding block. To get the sets corresponding to the commands of a block, you'll have
-- to loop through them and update the set yourself. The next step teaches you how to do that.
--
--
-- 3) Having now the list of sets, iterate through blocks and commands (if you used Order.Backwards
-- previously, in step 3, then you'll have to iterate through the commands of the block backwards
-- too).
--
--     3.1) Inside the loop that iterates over a block's commands, call "flow.update_set" to update
--     the set.


local flow = {}

local ir = require "pallene.ir"
local util = require "pallene.util"
local tagged_union = require "pallene.tagged_union"
local define_union = tagged_union.in_namespace(flow, "flow")

define_union("Order", {
    Forward   = {},
    Backwards = {},
})

define_union("Operation", {
    Union        = {},
    Intersection = {},
})

function flow.GenKill()
    return {
        kill = {},  -- set of values
        gen  = {},  -- set of values
    }
end

local function FlowState()
    return {
        start  = nil,
        finish = nil,
        transfer_function = nil,
    }
end

-- "operation" is the operation that is used to merge sets. Before we start iterating over a
-- block's commands, we first merge the sets of the block's predecessors/successors to form
-- it's "start" set. The merging may be the union of the sets or the intersection of the
-- sets. "operation" defines which is it.

-- "compute_gen_kill" is a function that will be used for updating the running set as we
-- read commands. The first argument is the block index and the second is the command's
-- index inside the block. For indicating which elements should be inserted/removed
-- into/from the set, create a new flow.GenKill object and then call the API functions
-- "flow.kill_value" for removal and "flow.gen_value" for insertion. The "compute_gen_kill"
--  function must return the flow.GenKill object that you created.

-- "init_start" is a function that will be used for initializing the "start" sets. The
-- function is called once for each basic block. It's first argument is the "start" set of
-- the block and the second is the block's index.
function flow.Framework()
    return {
        direction                  = false,
        join                       = false,
        identity_element           = false,
        entry_block_constant_value = false,
        make_transfer_function     = false,
        make_result                = false,
        copy                       = false,
    }
end


local function make_state_list(block_list, framework)
    local state_list = {}
    local direction = framework.direction._tag
    local identity = framework.identity_element
    local first_block_start_value = framework.entry_block_constant_value
    local make_transfer_function = framework.make_transfer_function
    local copy = framework.copy
    for block_i = 1, #block_list do
        local block_state = FlowState()
        block_state.start = util.deep_copy(identity)
        block_state.finish = util.deep_copy(identity)
        block_state.transfer_function = make_transfer_function(block_i)
        state_list[block_i] = block_state

        if block_i == 1 and direction == "flow.Order.Forward" then
            copy(state_list[1].start, first_block_start_value)
        elseif block_i == #block_list and direction == "flow.Order.Backwards" then
            copy(state_list[#state_list].start, first_block_start_value)
        end
    end
    return state_list
end

function flow.flow_analysis(block_list, framework)
                               -- ({ir.BasicBlock}, flow.Framework) -> { block_id -> set }
    local state_list = make_state_list(block_list, framework)

    local join = framework.join
    local direction = framework.direction._tag
    local make_result = framework.make_result
    local copy = framework.copy
    local identity = framework.identity_element

    local succ_list = ir.get_successor_list(block_list)
    local pred_list = ir.get_predecessor_list(block_list)

    local block_order
    local merge_src_list
    local dirty_propagation_list
    if direction == "flow.Order.Forward"  then
        block_order = ir.get_successor_depth_search_topological_sort(succ_list)
        merge_src_list = pred_list
        dirty_propagation_list = succ_list
    elseif direction == "flow.Order.Backwards" then
        block_order = ir.get_predecessor_depth_search_topological_sort(pred_list)
        merge_src_list = succ_list
        dirty_propagation_list = pred_list
    else
        tagged_union.error(direction)
    end

    local dirty_flag = {} -- { block_id -> bool } keeps track of modified blocks
    for i = 1, #block_list do
        dirty_flag[i] = true
    end

    local first_block_i = block_order[1]

    local scratch = util.deep_copy(identity) -- temporaty storage

    local function update_block(block_i)
        local state = state_list[block_i]

        -- first block's starting set is supposed to be constant
        if block_i ~= first_block_i then
            local src_indices = merge_src_list[block_i]
            copy(scratch, identity)
            for _, src_index in ipairs(src_indices) do
                local src_state = state_list[src_index]
                scratch = join(scratch, src_state.finish)
            end
            copy(state.start, scratch)
        else
            copy(scratch, state.start)
        end

        local dirty_propagation = dirty_propagation_list[block_i]
        local state_changed = state.transfer_function(scratch, state.finish)
        if state_changed then
            copy(state.finish, scratch)
            for _, i in ipairs(dirty_propagation) do
                dirty_flag[i] = true
            end
        end
    end

    repeat
        local found_dirty_block = false
        for _,block_i in ipairs(block_order) do
            if dirty_flag[block_i] then
                found_dirty_block = true
                -- CAREFUL: we have to clean the dirty flag BEFORE updating the block or else a
                -- block that jumps to itself might set it's dirty flag to "true" during
                -- "update_block" and we'll then wrongly set it to "false" in here.
                dirty_flag[block_i] = false
                update_block(block_i)
            end
        end
    until not found_dirty_block

    local result = {} -- { block_id => format_dependent_on_the_framework }

    for block_i = 1, #block_list do
        local state = state_list[block_i]
        result[block_i] = make_result(block_i, state.start)
    end

    return result
end

define_union("SetOperation", {
    Union        = {},
    Intersection = {"set_elements_list"},
})

function flow.SetFrameworkArguments()
    return {
        direction             = false,
        set_operation         = false,
        entry_constant_set    = false,
        cmd_transfer_function = false,
        block_list            = false,
    }
end

function flow.make_set_framework(args)

    local direction = args.direction
    local set_operation = args.set_operation
    local entry_constant_set = args.entry_constant_set
    local cmd_transfer_function = args.cmd_transfer_function
    local block_list = args.block_list

    local join_sets
    local identity_set
    if set_operation._tag == "flow.SetOperation.Union" then
        join_sets = function (dest, src)
            for v, _ in pairs(src) do
                dest[v] = true
            end
            return dest
        end

        identity_set = {}

    elseif set_operation._tag == "flow.SetOperation.Intersection" then
        join_sets = function (dest, src)
            for v, _ in pairs(dest) do
                if not src[v] then
                    dest[v] = nil
                end
            end
            return dest
        end

        -- the intersection's identity set is the set containing all elements
        identity_set = {}
        for _, v in ipairs(set_operation.set_elements_list) do
            identity_set[v] = true
        end

    else
        tagged_union.error(set_operation._tag)
    end

    local GenKill = util.Class()
    function GenKill:init()
        self.gen_set = {}
        self.kill_set = {}
    end

    function GenKill:gen(v)
        self.gen_set[v] = true
        self.kill_set[v] = nil
    end

    function GenKill:kill(v)
        self.gen_set[v] = nil
        self.kill_set[v] = true
    end

    local function make_block_transfer_function(block_i)
        local gen_kill = GenKill.new()

        local block = block_list[block_i]

        local first
        local last
        local step
        if direction._tag == "flow.Order.Forward" then
            first = 1
            last = #block.cmds
            step = 1
        elseif direction._tag == "flow.Order.Backwards" then
            first = #block.cmds
            last = 1
            step = -1
        else
            tagged_union.error(direction._tag)
        end

        for cmd_i = first, last, step do
            cmd_transfer_function(block_i, cmd_i, gen_kill)
        end

        local function block_transfer_function(set, old_set)

            local gen_set = gen_kill.gen_set
            local kill_set = gen_kill.kill_set

            for v, _ in pairs(gen_set) do
                set[v] = true
                assert(not kill_set[v], "must not generate and kill the same value")
            end

            for v, _ in pairs(kill_set) do
                set[v] = nil
                assert(not gen_set[v], "must not generate and kill the same value")
            end

            local set_changed = false
            for v, _ in pairs(set) do
                if not old_set[v] then
                    set_changed = true
                    break
                end
            end
            if not set_changed then
                for v, _ in pairs(old_set) do
                    if not set[v] then
                        set_changed = true
                        break
                    end
                end
            end

            return set_changed
        end

        return block_transfer_function
    end

    local function copy_set(dest, src)
        for v, _ in pairs(dest) do
            if not src[v] then
                dest[v] = nil
            end
        end

        for v, _ in pairs(src) do
            dest[v] = true
        end
        return dest
    end

    local Set = util.Class()
    function Set:init(set)
        self.set = set
    end

    function Set:gen(v)
        self.set[v] = true
    end

    function Set:kill(v)
        self.set[v] = nil
    end

    local function make_block_result(block_i, set)
        local s = Set.new(set)
        local result = {
            cmds   = {}, -- { cmd_i => set }
            finish = {}, -- set
        }

        local block = block_list[block_i]

        local first
        local last
        local step
        if direction._tag == "flow.Order.Forward" then
            first = 1
            last = #block.cmds
            step = 1
        elseif direction._tag == "flow.Order.Backwards" then
            first = #block.cmds
            last = 1
            step = -1
        else
            tagged_union.error(direction._tag)
        end

        for cmd_i = 1, #block.cmds do
            result.cmds[cmd_i] = {}
        end

        for cmd_i = first, last, step do
            local cmd_set = result.cmds[cmd_i]
            copy_set(cmd_set, s.set)
            cmd_transfer_function(block_i, cmd_i, s)
        end
        copy_set(result.finish, s.set)
        return result
    end

    local fw = flow.Framework()

    fw.direction = direction
    fw.identity_element = identity_set
    fw.entry_block_constant_value = entry_constant_set
    fw.join = join_sets
    fw.make_transfer_function = make_block_transfer_function
    fw.make_result = make_block_result
    fw.copy = copy_set

    return fw
end


return flow
