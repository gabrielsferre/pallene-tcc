-- Copyright (c) 2020, The Pallene Developers
-- Pallene is licensed under the MIT license.
-- Please refer to the LICENSE and AUTHORS files for details
-- SPDX-License-Identifier: MIT

local util = {}

function util.abort(msg)
    io.stderr:write(msg, "\n")
    os.exit(1)
end

-- String templates for C and Lua code.
-- Replaces $VAR and ${VAR} placeholders in the `code` string, with values from `substs`.
--
-- Don't call this function in tail-call position; wrap the call in parens if necessary.
-- This way you can get an useful line number if there is a template error.
function util.render(code, substs)
    return (string.gsub(code,
        "%$({?)([A-Za-z_][A-Za-z_0-9]*)(}?)",
        function(open, k,close)
            local v = substs[k]

            if open == "{" and close == "" then
                error("unclosed ${ in template")
            end
            if not v then
                error("missing template variable " .. k)
            end
            if type(v) ~= "string" then
                error("template variable is not a string " .. k)
            end

            if open == "" then
                return v .. close
            else
                return v
            end
        end
    ))
end

--
-- Shell and filesystem stuff
--

function util.split_ext(file_name)
    local name, ext = string.match(file_name, "(.*)%.(.*)")
    return name, ext
end

function util.get_file_contents(file_name)
    local f, err = io.open(file_name, "r")
    if not f then
        return false, err
    end
    local s = f:read("a")
    f:close()
    if not s then
        return false, "unable to open file " .. file_name
    else
        return s
    end
end

function util.set_file_contents(file_name, contents)
    local f, err = io.open(file_name, "w")
    if not f then
        return false, err
    end
    f:write(contents)
    f:close()
    return true
end

function util.deep_copy(original)
    local original_type = type(original)
    local copy
    if original_type == 'table' then
        copy = {}
        for key, value in pairs(original) do
            copy[util.deep_copy(key)] = util.deep_copy(value)
        end
        setmetatable(copy, getmetatable(original))
    else
        copy = original
    end
    return copy
end

-- Quotes a command-line argument according to POSIX shell syntax.
-- Uses a whitelist of safe chars to avoid quoting too much
function util.shell_quote(str)
    if string.match(str, "^[%w./_-]+$") then
        return str
    else
        return "'" .. string.gsub(str, "'", "'\\''") .. "'"
    end
end

function util.execute(cmd)
    local ok = os.execute(cmd)
    if ok then
        return true
    else
        return false, "command failed: " .. cmd
    end
end

function util.outputs_of_execute(cmd)
    local out_file = os.tmpname()
    local err_file = os.tmpname()

    local redirected =
        cmd ..
        " > "  .. util.shell_quote(out_file) ..
        " 2> " .. util.shell_quote(err_file)

    local ok, err = util.execute(redirected)
    local out_content = assert(util.get_file_contents(out_file))
    local err_content = assert(util.get_file_contents(err_file))
    os.remove(out_file)
    os.remove(err_file)
    return ok, err, out_content, err_content
end

--
-- OOP
--

function util.Class()
    local cls = {}
    cls.__index = cls

    cls.new = function(...)
        local self = setmetatable({}, cls)
        self:init(...)
        return self
    end

    return cls
end

function util.define_local_tagged_union(type_name, constructors)
    local function is_valid_name_component(s)
        -- In particular this does not allow ".", which is our separator
        return string.match(s, "[A-Za-z_][A-Za-z_0-9]*")
    end

    local function make_tag(typ, const)
        assert(is_valid_name_component(typ))
        assert(is_valid_name_component(const))
        local tag = typ .. "." .. const
        return tag
    end

    local cons_table = {}
    for cons_name, fields in pairs(constructors) do
        local tag = make_tag(type_name, cons_name)

        local cons
        if #fields == 0 then
            cons = { _tag = tag }
        else
            cons = function(...)
                local args = table.pack(...)
                if args.n ~= #fields then
                    error(string.format(
                        "wrong number of arguments for %s. Expected %d but received %d.",
                        cons_name, #fields, args.n))
                end
                local node = { _tag = tag }
                for i, field in ipairs(fields) do
                    node[field] = args[i]
                end
                return node
            end
        end
        cons_table[cons_name] = cons
    end
    return cons_table
end

return util
