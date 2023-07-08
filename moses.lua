--- Utility-belt library for functional programming in Lua ([source](http://github.com/Yonaba/Moses))
-- @author [Roland Yonaba](http://github.com/Yonaba)
-- @copyright 2012-2018
-- @license [MIT](http://www.opensource.org/licenses/mit-license.php)
-- @release 2.1.0
-- @module moses
-- @set sort=true

local _MODULEVERSION             = '2.1.0'

-- Internalisation
local next, type, pcall          = next, type, pcall
local setmetatable, getmetatable = setmetatable, getmetatable
local t_insert, t_sort           = table.insert, table.sort
local t_remove, t_concat         = table.remove, table.concat
local randomseed, random, huge   = math.randomseed, math.random, math.huge
local floor, max, min, ceil      = math.floor, math.max, math.min, math.ceil
local wrap                       = coroutine.wrap
local yield                      = coroutine.yield
local rawget                     = rawget
local unpack                     = table.unpack or unpack
local pairs, ipairs              = pairs, ipairs
local error                      = error
local clock                      = os and os.clock or nil
---@class moses
local M                          = {}


-- ======== Private helpers

local function f_max(a, b) return a > b end

local function f_min(a, b) return a < b end

local function count(t) -- raw count of items in an map-table
    local i = 0
    for k, v in pairs(t) do i = i + 1 end
    return i
end

---@generic k, v, v2, vararg
---@param list { [k]:v }
---@param comp fun(_ans:v2, val:v2):boolean
---@param transform? fun(v:v, ...:vararg):v2
---@param ... vararg
---@return v2
local function extract(list, comp, transform, ...) -- extracts value from a list
    transform = transform or M.identity
    local _ans
    for _, v in pairs(list) do
        if not _ans then
            _ans = transform(v, ...)
        else
            local val = transform(v, ...)
            _ans = comp(_ans, val) and _ans or val
        end
    end
    return _ans
end

local function partgen(t, n, f, pad) -- generates array partitions
    for i = 0, #t, n do
        local s = M.slice(t, i + 1, i + n)
        if #s > 0 then
            while (#s < n and pad) do s[#s + 1] = pad end
            f(s)
        end
    end
end

local function partgen2(t, n, f, pad) -- generates overlapping array partitions
    for i = 0, #t, n - 1 do
        local s = M.slice(t, i + 1, i + n)
        if #s > 0 and i + 1 < #t then
            while (#s < n and pad) do s[#s + 1] = pad end
            f(s)
        end
    end
end

local function partgen3(t, n, f, pad) -- generates sliding array partitions
    for i = 0, #t, 1 do
        local s = M.slice(t, i + 1, i + n)
        if #s > 0 and i + n <= #t then
            while (#s < n and pad) do s[#s + 1] = pad end
            f(s)
        end
    end
end

---@source http://www.lua.org/pil/9.3.html
local function permgen(t, n, f)
    if n == 0 then f(t) end
    for i = 1, n do
        t[n], t[i] = t[i], t[n]
        permgen(t, n - 1, f)
        t[n], t[i] = t[i], t[n]
    end
end

local function signum(a) return a >= 0 and 1 or -1 end

-- Internal counter for unique ids generation
local unique_id_counter = -1

--- Operator functions
-- @section Operator functions

M.operator = {}
--- Returns a + b. <em>Aliased as `op.add`</em>.
-- @name operator.add
-- @param a a value
-- @param b a value
-- @return a + b
M.operator.add = function(a, b) return a + b end

--- Returns a - b. <em>Aliased as `op.sub`</em>.
-- @name operator.sub
-- @param a a value
-- @param b a value
-- @return a - b
M.operator.sub = function(a, b) return a - b end

--- Returns a * b. <em>Aliased as `op.mul`</em>.
-- @name operator.mul
-- @param a a value
-- @param b a value
-- @return a * b
M.operator.mul = function(a, b) return a * b end

--- Returns a / b. <em>Aliased as `op.div`</em>.
-- @name operator.div
-- @param a a value
-- @param b a value
-- @return a / b
M.operator.div = function(a, b) return a / b end

--- Returns a % b. <em>Aliased as `op.mod`</em>.
-- @name operator.mod
-- @param a a value
-- @param b a value
-- @return a % b
M.operator.mod = function(a, b) return a % b end

--- Returns a ^ b. <em>Aliased as `op.exp`, `op.pow`</em>.
-- @name operator.exp
-- @param a a value
-- @param b a value
-- @return a ^ b
M.operator.exp = function(a, b) return a ^ b end
M.operator.pow = M.operator.exp

--- Returns -a. <em>Aliased as `op.unm`, `op.neg`</em>.
-- @name operator.unm
-- @param a a value
-- @return -a
M.operator.unm = function(a) return -a end
M.operator.neg = M.operator.unm

--- Performs floor division (//) between `a` and `b`. It rounds the quotient towards minus infinity.
-- <em>Aliased as `op.floordiv`</em>.
-- @name operator.floordiv
-- @param a a value
-- @param b a value
-- @return a // b
M.operator.floordiv = function(a, b) return floor(a / b) end

--- Performs integer division between `a` and `b`. <em>Aliased as `op.intdiv`</em>.
-- @name operator.intdiv
-- @param a a value
-- @param b a value
-- @return a / b
M.operator.intdiv = function(a, b)
    return a >= 0 and floor(a / b) or ceil(a / b)
end

--- Checks if a equals b. <em>Aliased as `op.eq`</em>.
-- @name operator.eq
-- @param a a value
-- @param b a value
-- @return a == b
M.operator.eq = function(a, b) return a == b end

--- Checks if a not equals b. <em>Aliased as `op.neq`</em>.
-- @name operator.neq
-- @param a a value
-- @param b a value
-- @return a ~= b
M.operator.neq = function(a, b) return a ~= b end

--- Checks if a is strictly less than b. <em>Aliased as `op.lt`</em>.
-- @name operator.lt
-- @param a a value
-- @param b a value
-- @return a < b
M.operator.lt = function(a, b) return a < b end

--- Checks if a is strictly greater than b. <em>Aliased as `op.gt`</em>.
-- @name operator.gt
-- @param a a value
-- @param b a value
-- @return a > b
M.operator.gt = function(a, b) return a > b end

--- Checks if a is less or equal to b. <em>Aliased as `op.le`</em>.
-- @name operator.le
-- @param a a value
-- @param b a value
-- @return a <= b
M.operator.le = function(a, b) return a <= b end

--- Checks if a is greater or equal to b. <em>Aliased as `op.ge`</em>.
-- @name operator.ge
-- @param a a value
-- @param b a value
-- @return a >= b
M.operator.ge = function(a, b) return a >= b end

--- Returns logical a and b. <em>Aliased as `op.land`</em>.
-- @name operator.land
-- @param a a value
-- @param b a value
-- @return a and b
M.operator.land = function(a, b) return a and b end

--- Returns logical a or b. <em>Aliased as `op.lor`</em>.
-- @name operator.lor
-- @param a a value
-- @param b a value
-- @return a or b
M.operator.lor = function(a, b) return a or b end

--- Returns logical not a. <em>Aliased as `op.lnot`</em>.
-- @name operator.lnot
-- @param a a value
-- @return not a
M.operator.lnot = function(a) return not a end

--- Returns concatenation of a and b. <em>Aliased as `op.concat`</em>.
-- @name operator.concat
-- @param a a value
-- @param b a value
-- @return a .. b
M.operator.concat = function(a, b) return a .. b end

--- Returns the length of a. <em>Aliased as `op.len`</em>.
-- @name operator.length
-- @param a a value
-- @return #a
M.operator.length = function(a) return #a end
M.operator.len = M.operator.length

--- Table functions
-- @section Table functions

---Clears a table. All its values become nil.
---@generic k, v
---@param t { [k]:v } # a table
---@return { [k]:v } # the given table, cleared.
---<hr/>
---
---<b>e.g.</b>
---Clears a table. All its values becomes nil. Returns the passed-in table.
--[[
```lua
M.clear({1,2,'hello',true}) -- => {}
```
]]
function M.clear(t)
    for k in pairs(t) do t[k] = nil end
    return t
end

---Iterates on key-value pairs, calling `f (v, k)` at every step.
---<br/><em>Aliased as `forEach`</em>.
---@generic k, v
---@param t { [k]:v } # a table
---@param f fun(value:v, key:k) function, prototyped as `f (v, k)`
---@see eachi
---<hr/>
---
---<b>e.g.</b>
---Iterates over each value-key pair in the passed-in table.
--[[
```lua
M.each({4,2,1},print)

-- => 4 1
-- => 2 2
-- => 1 3
```
]]
---<hr/>
---
---<b>e.g.</b>
---The table can be map-like (both array part and hash part).
--[[
```lua
M.each({one = 1, two = 2, three = 3},print)

-- => 1 one
-- => 2 two
-- => 3 three
```
]]
function M.each(t, f)
    for index, value in pairs(t) do
        f(value, index)
    end
end

---Iterates on integer key-value pairs, calling `f(v, k)` every step.
---Only applies to values located at integer keys. The table can be a sparse array.
---Iteration will start from the lowest integer key found to the highest one.
---<br/><em>Aliased as `forEachi`</em>.
---@generic k, v
---@param t { [k]:v } # a table
---@param f fun(value:v, key:k) # a function, prototyped as `f (v, k)`
---@see each
---<hr/>
---
---<b>e.g.</b>
---Iterates only on integer keys in an array table. It returns value-key pairs.
--[[
```lua
local t = {a = 1, b = 2, [0] = 1, [-1] = 6, 3, x = 4, 5}
M.eachi(t,print)

-- => 6 -1
-- => 1 0
-- => 3 1
-- => 5 2
```
]]
---<hr/>
---
---<b>e.g.</b>
---The given array can be sparse, or even have a hash-like part.
--[[
```lua
M.each({one = 1, two = 2, three = 3},print)

-- => 1 one
-- => 2 two
-- => 3 three
```
]]
function M.eachi(t, f)
    local lkeys = M.sort(M.select(M.keys(t), M.isInteger))
    for k, key in ipairs(lkeys) do
        f(t[key], key)
    end
end

---Collects values at given keys and return them wrapped in an array.
---@generic k, v
---@param t { [k]:v } # a table
---@param ... k # variable number of keys to collect values
---@return v[] # an array-list of values
---<hr/>
---
---<b>e.g.</b>
---Collects values at given keys and returns them in an array.
--[[
```lua
local t = {4,5,6}
M.at(t,1,3) -- => "{4,6}"

local t = {a = 4, bb = true, ccc = false}
M.at(t,'a', 'ccc') -- => "{4, false}"
```
]]
function M.at(t, ...)
    local values = {}
    for _, key in ipairs({ ... }) do values[#values + 1] = t[key] end
    return values
end

---Adjusts the value at a given key using a function or a value. In case `f` is a function,
---<br/>it should be prototyped `f(v)`. It does not mutate the given table, but rather
---<br/>returns a new array. In case the given `key` does not exist in `t`, it throws an error.
---@generic k, v, v2
---@param t { [k]:v } # a table
---@param key k key
---@param f? (fun(value:v):v2)|v2 # function, prototyped as `f(v)` or a value
---@return { [k]:v|v2 }
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local t = {1,2,3}
M.adjust(t, 2, math.sin) -- => {1, 0.90929, 3}

local v = {x = 1}
M.adjust(t, 'x', 4) -- => {x = 4}
```
]]
function M.adjust(t, key, f)
    if (t[key] == nil) then error("key not existing in table") end
    local _t = M.clone(t)
    _t[key] = type(f) == 'function' and f(_t[key]) or f
    return _t
end

---Counts occurrences of a given value in a table. Uses `isEqual` to compare values.
---@param t table # a table
---@param val? any # a value to be searched in the table. If not given, the size of the table will be returned
---@return integer # the count of occurrences of the given value
---@see countf
---@see size
---<hr/>
---
---<b>e.g.</b>
---Counts the number of occurences of a given value in a table.
--[[
```lua
M.count({1,1,2,3,3,3,2,4,3,2},1) -- => 2
M.count({1,1,2,3,3,3,2,4,3,2},2) -- => 3
M.count({1,1,2,3,3,3,2,4,3,2},3) -- => 4
M.count({false, false, true},false) -- => 2
M.count({false, false, true},true) -- => 1
```
]]
---<hr/>
---
---<b>e.g.</b>
---Returns the size of the list in case no value was provided.
--[[
```lua
M.count({1,1,2,3,3}) -- => 5
```
]]
function M.count(t, val)
    if val == nil then return M.size(t) end
    local count = 0
    for k, v in pairs(t) do
        if M.isEqual(v, val) then count = count + 1 end
    end
    return count
end

---Counts the number of values passing a predicate test. Same as `count`, but uses an iterator.
---Returns the count for values passing the test `f (v, k)`
---@generic k, v
---@param t { [k]:v } # a table
---@param f fun(value:v, key:k):boolean # an iterator function, prototyped as `f (v, k)`
---@return integer # the count of values validating the predicate
---@see count
---@see size
---<hr/>
---
---<b>e.g.</b>
---Counts the number of values passing an iterator test.
--[[
```lua
M.countf({1,2,3,4,5,6}, function(v)
  return v%2==0
end) -- => 3

M.countf({print, pairs, os, assert, ipairs}, function(v)
  return type(v)=='function'
end) -- => 4
```
]]
function M.countf(t, f)
    local count = 0
    for k, v in pairs(t) do
        if f(v, k) then count = count + 1 end
    end
    return count
end

---Checks if all values in a collection are equal. Uses an optional `comp` function which is used
---to compare values and defaults to `isEqual` when not given.
---<br/><em>Aliased as `alleq`</em>.
---@generic k, v
---@param t { [k]:v } # a table
---@param comp? fun(pivot:v, value:v):boolean # a comparison function. Defaults to `isEqual`
---@return boolean # `true` when all values in `t` are equal, `false` otherwise.
---@see isEqual
---<hr/>
---
---<b>e.g.</b>
---Checks if all values in a collection are equal. Uses `M.isEqual` by default to compare values.
--[[
```lua
M.allEqual({1,1,1,1,1}, comp) -- => true
M.allEqual({1,1,2,1,1}, comp) -- => false

local t1 = {1, 2, {3}}
local t2 = {1, 2, {3}}
M.allEqual({t1, t2}) -- => true
```
]]
---<hr/>
---
---<b>e.g.</b>
---Can take an optional `comp` function which will be used to compare values.
--[[
```lua
local t1 = {x = 1, y = 0}
local t2 = {x = 1, y = 0}
local t3 = {x = 1, y = 2}
local t4 = {x = 1, y = 2}
local function compx(a, b) return a.x == b.x end
local function compy(a, b) return a.y == b.y end

M.allEqual({t1, t2}, compx) -- => true
M.allEqual({t1, t2}, compy) -- => true
M.allEqual({t3, t4}, compx) -- => true
M.allEqual({t3, t4}, compy) -- => true
M.allEqual({t1, t2, t3, t4}, compx) -- => true
M.allEqual({t1, t2, t3, t4}, compy) -- => false
```
]]
function M.allEqual(t, comp)
    local _, pivot = next(t)
    for _, v in pairs(t) do
        if comp then
            if not comp(pivot, v) then return false end
        else
            if not M.isEqual(pivot, v) then return false end
        end
    end
    return true
end

---Loops `n` times through a table. In case `n` is omitted, it will loop forever.
---In case `n` is lower or equal to 0, it returns an empty function.
---<br/><em>Aliased as `loop`</em>.
---@generic k, v
---@param t { [k]:v } # a table
---@param n integer # n the number of loops
---@return fun():(v,k) # an iterator function yielding value-key pairs from the passed-in table.
---<hr/>
---
---<b>e.g.</b>
---Returns a function which iterates on each value-key pair in a given table (similarly to `M.each`), except that it restarts iterating again `n` times.
---If `n` is not provided, it defaults to 1.
--[[
```lua
local t = {'a','b','c'}
for v in M.cycle(t, 2) do
  print(v)
end

-- => 'a'
-- => 'b'
-- => 'c'
-- => 'a'
-- => 'b'
-- => 'c'
```
]]
---<hr/>
---
---<b>e.g.</b>
---Supports array-like tables and map-like tables.
--[[
```lua
local t = {x = 1, y = 2, z = 3}
for v in M.cycle(t) do
  print(v)
end

-- => 2
-- => 1
-- => 3
```
]]
function M.cycle(t, n)
    n = n or 1
    if n <= 0 then return M.noop end
    local k, fk
    local i = 0
    while true do
        return function()
            k = k and next(t, k) or next(t)
            fk = not fk and k or fk
            if n then
                i = (k == fk) and i + 1 or i
                if i > n then
                    return
                end
            end
            return t[k], k
        end
    end
end

---Maps `f (v, k)` on value-key pairs, collects and returns the results.
---Uses `pairs` to iterate over elements in `t`.
---<br/><em>Aliased as `collect`</em>.
---@generic k, v, v2
---@param t { [k]:v } # a table
---@param f fun(value:v, key:k):v2? # an iterator function, prototyped as `f (v, k)`
---@return { [k]:v2 } # a table of results
---@see mapi
---<hr/>
---
---<b>e.g.</b>
---Executes a function on each value in a given array.
--[[
```lua
M.map({1,2,3},function(v)
  return v+10
end) -- => "{11,12,13}"
```
]]
---<hr width="50%"/>
---
---<br/>
---
--[[
```lua
M.map({a = 1, b = 2},function(v, k)
  return k..v
end) -- => "{a = 'a1', b = 'b2'}"
```
]]
---<hr/>
---
---<b>e.g.</b>
---It also maps both keys and values.
--[[
```lua
M.map({a = 1, b = 2},function(v, k)
  return k..k, v*2
end) -- => "{aa = 2, bb = 4}"
```
]]
function M.map(t, f)
    local _t = {}
    for index, value in pairs(t) do
        local k, kv, v = index, f(value, index)
        _t[v and kv or k] = v or kv
    end
    return _t
end

---Maps `f (v, k)` on value-key pairs, collects and returns the results.
---Uses `ipairs` to iterate over elements in `t`.
---@generic v, v2
---@param t v[] # a table
---@param f fun(value:v, index:integer):v2? # an iterator function, prototyped as `f (v, k)`
---@return v2[] # a table of results
---@see map
---<hr/>
---
---<b>e.g.</b>
---Executes a function on each value in a given array.
--[[
```lua
M.mapi({1,2,3},function(v)
  return v+10
end) -- => "{11,12,13}"
```
]]
---<hr/>
---
---<b>e.g.</b>
---It only works for the array-part of the given table.
--[[
```lua
M.mapi({a = 1, 2, 3, 4, 5},function(v, k)
  return k..v
end) -- => "{'12','23','34','45'}"
```
]]
function M.mapi(t, f)
    local _t = {}
    for index, value in ipairs(t) do
        local k, kv, v = index, f(value, index)
        _t[v and kv or k] = v or kv
    end
    return _t
end

---@generic orig_k, old_v, new_v
---@param t { [orig_k]: old_v}
---@param f fun(v:old_v, k:orig_k):new_v
---@return {[orig_k]: new_v}
function M.mapv(t, f)
    local _t = {}
    for index, value in pairs(t) do
        _t[index] = f(value, index)
    end
    return _t
end

---@generic old_k, old_v, new_k, new_v
---@param t { [old_k]: old_v}
---@param f fun(v:old_v, k:old_k):(new_k, new_v)
---@return {[new_k]: new_v}
function M.mapkv(t, f)
    local _t = {}
    for index, value in pairs(t) do
        local k, v = f(value, index)
        if k then
            _t[k] = v
        end
    end
    return _t
end

---@generic old_v, new_v
---@param t old_v[]
---@param f fun(v:old_v, i:integer):new_v
---@return new_v[]
function M.mapiv(t, f)
    local _t = {}
    for index, value in ipairs(t) do
        _t[index] = f(value, index)
    end
    return _t
end

---@generic old_v, new_k, new_v
---@param t old_v[]
---@param f fun(v:old_v, i:integer):(new_k, new_v)
---@return {[new_k]:new_v}
function M.mapikv(t, f)
    local _t = {}
    for index, value in ipairs(t) do
        local k, v = f(value, index)
        if k then
            _t[k] = v
        end
    end
    return _t
end

---Reduces a table, left-to-right. Folds the table from the first element to the last element
---to a single value, using a given iterator and an initial state.
---The iterator takes a state and a value and returns a new state.
---<br/><em>Aliased as `inject`, `foldl`</em>.
---@generic k, v, v2, v3
---@param t { [k]:v } # a table
---@param f fun(state:v|v2|v3, value:v):v3 # an iterator function, prototyped as `f (state, value)`
---@param state? v2 # an initial state of reduction. Defaults to the first value in the table.
---@return v3 # the final state of reduction
---@see best
---@see reduceRight
---@see reduceBy
---<hr/>
---
---<b>e.g.</b>
---Can sum all values in a table. In case `state` is not provided, it defaults to the first value in the given table `t`.
--[[
```lua
local function add(a,b) return a+b end
M.reduce({1,2,3,4},add) -- => 10
```
]]
---<hr/>
---
---<b>e.g.</b>
---Or concatenates all values.
--[[
```lua
local function concat(a,b) return a..b end
M.reduce({'a','b','c','d'},concat) -- => abcd
```
]]
function M.reduce(t, f, state)
    for k, value in pairs(t) do
        if state == nil then
            state = value
        else
            state = f(state, value)
        end
    end
    return state
end

---Returns the best value passing a selector function. Acts as a special case of
---`reduce`, using the first value in `t` as an initial state. It thens folds the given table,
---testing each of its values `v` and selecting the value passing the call `f(state,v)` every time.
---@generic k, v
---@param t { [k]:v } # a table
---@param f fun(state:v, value:v):boolean # an iterator function, prototyped as `f (state, value)`
---@return v # the final state of reduction
---@see reduce
---@see reduceRight
---@see reduceBy
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local words = {'Lua', 'Programming', 'Language'}
M.best(words, function(a,b) return #a > #b end) -- => 'Programming'
M.best(words, function(a,b) return #a < #b end) -- => 'Lua'
```
]]
function M.best(t, f)
    local _, state = next(t)
    for k, value in pairs(t) do
        if state == nil then
            state = value
        else
            state = f(state, value) and state or value
        end
    end
    return state
end

---Reduces values in a table passing a given predicate. Folds the table left-to-right, considering
---only values validating a given predicate.
---@generic k, v, v2, v3
---@param t { [k]:v } # a table
---@param f fun(state:v|v2|v3, value:v):v3 # an iterator function, prototyped as `f (state, value)`
---@param pred fun(value:v, key:k):boolean # a predicate function `pred (v, k)` to select values to be considered for reduction
---@param state? v2 # state an initial state of reduction. Defaults to the first value in the table of selected values.
---@return v3 # the final state of reduction
---@see reduce
---@see best
---@see reduceRight
---<hr/>
---
---<b>e.g.</b>
---Reduces a table considering only values matching a predicate.
---For example,let us define a set of values.
--[[
```lua
local val = {-1, 8, 0, -6, 3, -1, 7, 1, -9}
```
]]
---And a reduction function which will add up values.
--[[
```lua
local function add(a,b) return a+b end
```
]]
---We can also define some predicate functions.
--[[
```lua
-- predicate for negative values
local function neg(v) return v<=0 end

-- predicate for positive values
local function pos(v) return v>=0 end
```
]]
---Then we can perform reduction considering only negative or positive values :
--[[
```lua
M.reduceBy(val, add, neg) -- => -17
M.reduceBy(val, add, pos) -- => 19
```
]]
---An initial state can be passed in.
--[[
```lua
M.reduceBy(val, add, neg, 17) -- => 0
M.reduceBy(val, add, pos, -19) -- => 0
```
]]
function M.reduceBy(t, f, pred, state)
    return M.reduce(M.select(t, pred), f, state)
end

---Reduces a table, right-to-left. Folds the table from the last element to the first element
---to single value, using a given iterator and an initial state.
---The iterator takes a state and a value, and returns a new state.
---<br/><em>Aliased as `injectr`, `foldr`</em>.
---@generic k, v, v2, v3
---@param t { [k]:v } # a table
---@param f fun(state:v|v2|v3, value:v):v3 # an iterator function, prototyped as `f (state, value)`
---@param state? v2 # an initial state of reduction. Defaults to the last value in the table.
---@return v3 # the final state of reduction
---@see reduce
---@see best
---@see reduceBy
---<hr/>
---
---<b>e.g.</b>
---Similar to `M.reduce`, but performs from right to left.
--[[
```lua
local initial_state = 256
local function div(a,b) return a/b end
M.reduceRight({1,2,4,16},div,initial_state) -- => 2
```
]]
function M.reduceRight(t, f, state)
    return M.reduce(M.reverse(t), f, state)
end

---Reduces a table while saving intermediate states. Folds the table left-to-right
---using a given iterator and an initial state. The iterator takes a state and a value,
---and returns a new state. The result is an array of intermediate states.
---<br/><em>Aliased as `mapr`</em>
---@generic k, v, v2, v3
---@param t { [k]:v } # a table
---@param f fun(state:v|v2|v3, value:v):v3 # an iterator function, prototyped as `f (state, value)`
---@param state? v2 # an initial state of reduction. Defaults to the first value in the table.
---@return v3[] # an array of states
---@see mapReduceRight
---<hr/>
---
---<b>e.g.</b>
---Reduces while saving intermediate states.
--[[
```lua
local function concat(a,b) return a..b end
M.mapReduce({'a','b','c'},concat) -- => "{'a', 'ab', 'abc'}"
```
]]
function M.mapReduce(t, f, state)
    local _t = {}
    for i, value in pairs(t) do
        _t[i] = not state and value or f(state, value)
        state = _t[i]
    end
    return _t
end

----Reduces a table while saving intermediate states. Folds the table right-to-left
---using a given iterator and an initial state. The iterator takes a state and a value,
---and returns a new state. The result is an array of intermediate states.
---<br/><em>Aliased as `maprr`</em>
---@generic k, v, v2, v3
---@param t { [k]:v } # a table
---@param f fun(state:v|v2|v3, value:v):v3 # an iterator function, prototyped as `f (state, value)`
---@param state? v2 # an initial state of reduction. Defaults to the last value in the table.
---@return v3[] # an array of states
---<hr/>
---
---<b>e.g.</b>
---Reduces from right to left, while saving intermediate states.
--[[
```lua
local function concat(a,b) return a..b end
M.mapReduceRight({'a','b','c'},concat) -- => "{'c', 'cb', 'cba'}"
```
]]
---@see mapReduce
function M.mapReduceRight(t, f, state)
    return M.mapReduce(M.reverse(t), f, state)
end

---Performs a linear search for a value in a table. It does not work for nested tables.
---The given value can be a function prototyped as `f (v, value)` which should return true when
---any v in the table equals the value being searched.
---<br/><em>Aliased as `any`, `some`, `contains`</em>
---@generic k, v
---@param t { [k]:v } # a table
---@param value any|fun(v:v):boolean # a value to search for
---@return boolean # a boolean : `true` when found, `false` otherwise
---@see detect
---<hr/>
---
---<b>e.g.</b>
---Looks for a value in a table.
--[[
```lua
M.include({6,8,10,16,29},16) -- => true
M.include({6,8,10,16,29},1) -- => false

local complex_table = {18,{2,{3}}}
local collection = {6,{18,{2,6}},10,{18,{2,{3}}},29}
M.include(collection, complex_table) -- => true
```
]]
---<hr/>
---
---<b>e.g.</b>
---Handles iterator functions.
--[[
```lua
local function isUpper(v) return v:upper()== v end
M.include({'a','B','c'},isUpper) -- => true
```
]]
function M.include(t, value)
    local _iter = (type(value) == 'function') and value or M.isEqual
    for _, v in pairs(t) do
        if _iter(v, value) then return true end
    end
    return false
end

---Performs a linear search for a value in a table. Returns the key of the value if found.
---The given value can be a function prototyped as `f (v, value)` which should return true when
---any v in the table equals the value being searched. This function is similar to `find`,
---which is mostly meant to work with array.
---@generic k, v
---@param t { [k]:v } # a table
---@param value any|fun(arg:v):boolean # a value to search for
---@return k? # the key of the value when found or __nil__
---@see include
---@see find
---<hr/>
---
---<b>e.g.</b>
---Returns the index of a value in a table.
--[[
```lua
M.detect({6,8,10,16},8) -- => 2
M.detect({nil,true,0,true,true},false) -- => nil

local complex_table = {18,{2,6}}
local collection = {6,{18,{2,6}},10,{18,{2,{3}}},29}
M.detect(collection, complex_table) -- => 2
```
]]
---<hr/>
---
---<b>e.g.</b>
---Handles iterator functions.
--[[
```lua
local function isUpper(v)
  return v:upper()==v
end
M.detect({'a','B','c'},isUpper) -- => 2
```
]]
function M.detect(t, value)
    local _iter = (type(value) == 'function') and value or M.isEqual
    for key, arg in pairs(t) do
        if _iter(arg, value) then return key end
    end
end

---Returns all values having specified keys `props`.
---@generic k, v
---@param t { [k]:v } # a table
---@param props table # a set of keys
---@return v[]|nil # an array of values from the passed-in table
---@see findWhere
---<hr/>
---
---<b>e.g.</b>
---Looks through a table and returns all the values that matches all of the key-value pairs listed in `props`.
--[[
```lua
local items = {
  {height = 10, weight = 8, price = 500},
  {height = 10, weight = 15, price = 700},
  {height = 15, weight = 15, price = 3000},
  {height = 10, weight = 8, price = 3000},
}
M.where(items, {height = 10}) -- => {items[1], items[2], items[4]}
M.where(items, {weight = 15}) -- => {items[2], items[3]}
M.where(items, {prince = 3000}) -- => {items[3], items[4]}
M.where(items, {height = 10, weight = 15, prince = 700}) -- => {items[2]}
```
]]
function M.where(t, props)
    local r = M.select(t, function(v)
        for key in pairs(props) do
            if v[key] ~= props[key] then return false end
        end
        return true
    end)
    return #r > 0 and r or nil
end

---Returns the first value having specified keys `props`.
---@generic k, v
---@param t { [k]:v } # a table
---@param props table # a set of keys
---@return v? # a value from the passed-in table
---@see where
---<hr/>
---
---<b>e.g.</b>
---Looks through a table and returns the first value found that matches all of the key-value pairs listed in `props`.
--[[
```lua
local a = {a = 1, b = 2, c = 3}
local b = {a = 2, b = 3, d = 4}
local c = {a = 3, b = 4, e = 5}
M.findWhere({a, b, c}, {a = 3, b = 4}) == c -- => true
```
]]
function M.findWhere(t, props)
    local index = M.detect(t, function(v)
        for key in pairs(props) do
            if props[key] ~= v[key] then return false end
        end
        return true
    end)
    return index and t[index]
end

---Selects and returns values passing an iterator test.
---<br/><em>Aliased as `filter`</em>.
---@generic k, v
---@param t { [k]:v } # a table
---@param f fun(value:v, index:k):boolean # an iterator function, prototyped as `f (v, k)`
---@return v[] # the selected values
---@see reject
---<hr/>
---
---<b>e.g.</b>
---Collects values passing a validation test.
--[[
```lua
local function isEven(v) return v%2==0 end
local function isOdd(v) return v%2~=0 end

M.select({1,2,3,4,5,6,7}, isEven) -- => "{2,4,6}"
M.select({1,2,3,4,5,6,7}, isOdd) -- => "{1,3,5,7}"
```
]]
function M.select(t, f)
    local _t = {}
    for index, value in pairs(t) do
        if f(value, index) then _t[#_t + 1] = value end
    end
    return _t
end

---Clones a table while dropping values passing an iterator test.
---<br/><em>Aliased as `discard`</em>
---@generic k, v
---@param t { [k]:v } # a table
---@param f fun(value:v, index:k) # an iterator function, prototyped as `f (v, k)`
---@return v[] # the remaining values
---@see select
---<hr/>
---
---<b>e.g.</b>
---Removes all values failing (returning false or nil) a validation test:
--[[
```lua
local function isEven(v) return v%2==0 end
local function isOdd(v) return v%2~=0 end

M.reject({1,2,3,4,5,6,7}, isEven) -- => "{1,3,5,7}"
M.reject({1,2,3,4,5,6,7}, isOdd) -- => "{2,4,6}"
```
]]
function M.reject(t, f)
    local _t = {}
    for index, value in pairs(t) do
        if not f(value, index) then _t[#_t + 1] = value end
    end
    return _t
end

---Checks if all values in a table are passing an iterator test.
---<br/><em>Aliased as `every`</em>
---@generic k, v
---@param t { [k]:v } # a table
---@param f fun(value:v, index:k):boolean # an iterator function, prototyped as `f (v, k)`
---@return boolean # `true` if all values passes the predicate, `false` otherwise
---<hr/>
---
---<b>e.g.</b>
---Checks whether or not all elements pass a validation test.
--[[
```lua
local function isEven(v) return v%2==0 end
M.all({2,4,6}, isEven) -- => true
```
]]
function M.all(t, f)
    for index, value in pairs(t) do
        if not f(value, index) then return false end
    end
    return true
end

---Invokes a method on each value in a table.
---@generic k, v, v2
---@param t { [k]:v } # a table
---@param method fun(v:v, k:k):v2 # a function, prototyped as `f (v, k)`
---@return { [k]:v2 } # the result of the call `f (v, k)`
---@see pluck
---<hr/>
---
---<b>e.g.</b>
---Invokes a given function on each value in a table.
--[[
```lua
M.invoke({'a','bea','cdhza'},string.len) -- => "{1,3,5}"
```
]]
---<hr/>
---
---<b>e.g.</b>
---Can reference the method of the same name in each value.
--[[
```lua
local a, b, c, d = {id = 'a'}, {id = 'b'}, {id = 'c'}, {id = 'd'}
local function call(self) return self.id end
M.invoke({a,b,c,d},call) -- => "{'a','b','c','d'}"
```
]]
function M.invoke(t, method)
    return M.map(t, function(v, k)
        if (type(v) == 'table') then
            if v[method] then
                if M.isCallable(v[method]) then
                    return v[method](v, k)
                else
                    return v[method]
                end
            else
                if M.isCallable(method) then
                    return method(v, k)
                end
            end
        elseif M.isCallable(method) then
            return method(v, k)
        end
    end)
end

---Extracts values in a table having a given key.
---@generic k, v
---@param t { [any]:{ [k]:v } } # a table
---@param key any # a key, will be used to index in each value: `value[key]`
---@return v[] # an array of values having the given key
---<hr/>
---
---<b>e.g.</b>
---Fetches all values indexed with specific key in a table of objects.
--[[
```lua
local peoples = {
  {name = 'John', age = 23},{name = 'Peter', age = 17},
  {name = 'Steve', age = 15},{age = 33}}

M.pluck(peoples,'age') -- => "{23,17,15,33}"
M.pluck(peoples,'name') -- => "{'John', 'Peter', 'Steve'}"
```
]]
function M.pluck(t, key)
    local _t = {}
    for _, v in pairs(t) do
        if v[key] then _t[#_t + 1] = v[key] end
    end
    return _t
end

---Returns the max value in a collection. If a `transform` function is passed, it will
---be used to evaluate values by which all objects will be sorted.
---@generic k, v, v2, vararg
---@param t { [k]:v } # a table
---@param transform? fun(v:v, ...:vararg):v2 # a transformation function, prototyped as `transform (v, k)`, defaults to @{identity}
---@return v|v2 # the max value found
---@see min
---<hr/>
---
---<b>e.g.</b>
---Returns the maximum value in a collection.
--[[
```lua
M.max {1,2,3} -- => 3
M.max {'a','b','c'} -- => 'c'
```
]]
---<hr/>
---
---<b>e.g.</b>
---Can take an iterator function to extract a specific property.
--[[
```lua
local peoples = {
  {name = 'John', age = 23},{name = 'Peter', age = 17},
  {name = 'Steve', age = 15},{age = 33}}
M.max(peoples,function(people) return people.age end) -- => 33
```
]]
function M.max(t, transform)
    return extract(t, f_max, transform)
end

---Returns the min value in a collection. If a `transform` function is passed, it will
---be used to evaluate values by which all objects will be sorted.
---@generic k, v, v2, vararg
---@param t { [k]:v } # a table
---@param transform? fun(v:v, ...:vararg):v2 # a transformation function, prototyped as `transform (v, k)`, defaults to @{identity}
---@return v|v2 # the min value found
---@see max
---<hr/>
---
---<b>e.g.</b>
---Returns the minimum value in a collection.
--[[
```lua
M.min {1,2,3} -- => 1
M.min {'a','b','c'} -- => 'a'
```
]]
---<hr/>
---
---<b>e.g.</b>
---Can take an iterator function to extract a specific property.
--[[
```lua
local peoples = {
  {name = 'John', age = 23},{name = 'Peter', age = 17},
  {name = 'Steve', age = 15},{age = 33}}
M.min(peoples,function(people) return people.age end) -- => 15
```
]]
function M.min(t, transform)
    return extract(t, f_min, transform)
end

---Checks if two tables are the same. It compares if both tables features the same values,
---but not necessarily at the same keys.
---@param a table # a table
---@param b table # another table
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
---Tests whether or not all values in each of the passed-in tables exists in both tables.
--[[
```lua
local a = {'a','b','c','d'}
local b = {'b','a','d','c'}
M.same(a,b) -- => true

b[#b+1] = 'e'
M.same(a,b) -- => false
```
]]
function M.same(a, b)
    return M.all(a, function(v) return M.include(b, v) end)
        and M.all(b, function(v) return M.include(a, v) end)
end

---Sorts a table, in-place. If a comparison function is given, it will be used to sort values.
---@generic v
---@param t v[] # a table
---@param comp? fun(a:v, b:v):boolean # a comparison function prototyped as `comp (a, b)`, defaults to <tt><</tt> operator.
---@return v[] # the given table, sorted.
---@see sortBy
---<hr/>
---
---<b>e.g.</b>
---Sorts a collection.
--[[
```lua
M.sort({'b','a','d','c'}) -- => "{'a','b','c','d'}"
```
]]
---<hr/>
---
---<b>e.g.</b>
---Handles custom comparison functions.
--[[
```lua
M.sort({'b','a','d','c'}, function(a,b)
  return a:byte() > b:byte()
end) -- => "{'d','c','b','a'}"
```
]]
function M.sort(t, comp)
    t_sort(t, comp)
    return t
end

---Iterates on values with respect to key order. Keys are sorted using `comp` function
---which defaults to `math.min`. It returns upon each call a `key, value` pair.
---@generic k, v
---@param t { [k]:v } # a table
---@param comp? fun(a:k, b:k) # a comparison function. Defaults to `<` operator
---@return fun():(k,v)  # an iterator function
---@see sortedv
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local tbl = {}; tbl[3] = 5 ; tbl[2] = 6; tbl[5] = 8; tbl[4] = 10; tbl[1] = 12
for k, v in M.sortedk(tbl) do print(k, v) end

-- => 1 12
-- => 2 6
-- => 3 5
-- => 4 10
-- => 5 8

local function comp(a,b) return a > b end
for k, v in M.sortedk(tbl, comp) do print(k, v) end

-- => 5 8
-- => 4 10
-- => 3 5
-- => 2 6
-- => 1 12
```
]]
function M.sortedk(t, comp)
    local keys = M.keys(t)
    t_sort(keys, comp)
    local i = 0
    return function()
        i = i + 1
        return keys[i], t[keys[i]]
    end
end

---Iterates on values with respect to values order. Values are sorted using `comp` function
---which defaults to `math.min`. It returns upon each call a `key, value` pair.
---@generic k, v
---@param t { [k]:v } # a table
---@param comp? fun(a:v, b:v) # a comparison function. Defaults to `<` operator
---@return fun():(k,v) # an iterator function
---@see sortedk
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local tbl = {}; tbl[3] = 5 ; tbl[2] = 6; tbl[5] = 8; tbl[4] = 10; tbl[1] = 12
for k, v in M.sortedv(tbl) do print(k, v) end

-- => 3 5
-- => 2 6
-- => 5 8
-- => 4 10
-- => 1 12

local function comp(a,b) return a > b end
for k, v in M.sortedv(tbl, comp) do print(k, v) end

-- => 1 12
-- => 4 10
-- => 5 8
-- => 2 6
-- => 3 5
```
]]
function M.sortedv(t, comp)
    local keys = M.keys(t)
    comp = comp or f_min
    t_sort(keys, function(a, b) return comp(t[a], t[b]) end)
    local i = 0
    return function()
        i = i + 1
        return keys[i], t[keys[i]]
    end
end

---Sorts a table in-place using a transform. Values are ranked in a custom order of the results of
---running `transform (v)` on all values. `transform` may also be a string name property  sort by.
---`comp` is a comparison function.
---@generic k, v, v2
---@param t { [k]:v } # a table
---@param transform? (fun(t:v):v2)|string  # a `transform` function to sort elements prototyped as `transform (v)`. Defaults to @{identity}
---@param comp? fun(a:v|v2, b:v|v2):boolean # a comparison function, defaults to the `<` operator
---@return { [k]:v } # a new array of sorted values
---@see sort
---<hr/>
---
---<b>e.g.</b>
---Sorts items in a collection based on the result of running a transform function through every item in the collection.
--[[
```lua
local r = M.sortBy({1,2,3,4,5}, math.sin)
print(table.concat(r,','))

-- => {5,4,3,1,2}
```
]]
---<hr/>
---
---<b>e.g.</b>
---The transform function can also be a string name property.
--[[
```lua
local people = {
    {name = 'albert', age = 40},
    {name = 'louis', age = 55},
    {name = 'steve', age = 35},
    {name = 'henry', age = 19},
}
local r = M.sortBy(people, 'age')
M.each(r, function(v) print(v.age, v.name) end)

-- => 19    henry
-- => 35    steve
-- => 40    albert
-- => 55    louis
```
]]
---As seen above, the defaut comparison function is the `<` operator. For example, let us supply a different one to sort the list of people by decreasing age order :
--[[
```lua
local people = {
    {name = 'albert', age = 40},
    {name = 'louis', age = 55},
    {name = 'steve', age = 35},
    {name = 'henry', age = 19},
}
local r = M.sortBy(people, 'age', function(a,b) return a > b end)
M.each(r, function(v) print(v.age, v.name) end)

-- => 55    louis
-- => 40    albert
-- => 35    steve
-- => 19    henry
```
]]
---The `transform` function defaults to `M.indentity` and in that case, `M.sortBy` behaves like `M.sort`.
--[[
```lua
local r = M.sortBy({1,2,3,4,5})
print(table.concat(r,','))

-- => {1,2,3,4,5}
```
]]
function M.sortBy(t, transform, comp)
    local f = transform or M.identity
    if (type(transform) == 'string') then
        f = function(t) return t[transform] end
    end
    comp = comp or f_min
    t_sort(t, function(a, b) return comp(f(a), f(b)) end)
    return t
end

---Splits a table into subsets groups.
---@generic k, v, g
---@param t { [k]:v } # a table
---@param iter fun(v:v, k:k):g # an iterator function, prototyped as `iter (v, k)`
---@return { [g]:v[] } # a table of subsets groups
---<hr/>
---
---<b>e.g.</b>
---Groups values in a collection depending on their return value when passed to a predicate test.
--[[
```lua
M.groupBy({0,1,2,3,4,5,6},function(v)
  return v%2==0 and 'even' or 'odd'
end)
-- => "{odd = {1,3,5}, even = {0,2,4,6}}"

M.groupBy({0,'a',true, false,nil,b,0.5},type)
-- => "{number = {0,0.5}, string = {'a'}, boolean = {true, false}}"
```
]]
function M.groupBy(t, iter)
    local _t = {}
    for k, v in pairs(t) do
        local _key = iter(v, k)
        if _t[_key] then
            _t[_key][#_t[_key] + 1] = v
        else
            _t[_key] = { v }
        end
    end
    return _t
end

---Groups values in a collection and counts them.
---@generic k, v, g
---@param t { [k]:v } # a table
---@param iter fun(v:v, k:k):g # an iterator function, prototyped as `iter (v, k)`
---@return { [g]:integer } # a table of subsets groups names paired with their count
---<hr/>
---
---<b>e.g.</b>
---Groups values in a collection depending on their return value when passed to a predicate test.
--[[
```lua
M.countBy({0,1,2,3,4,5,6},function(v)
  return v%2==0 and 'even' or 'odd'
end) -- => "{odd = 3, even = 4}"
```
]]
function M.countBy(t, iter)
    local stats = {}
    for i, v in pairs(t) do
        local key = iter(v, i)
        stats[key] = (stats[key] or 0) + 1
    end
    return stats
end

---Counts the number of values in a collection. If being passed more than one argument
---it will return the count of all passed-in arguments.
---@param ... any # Optional variable number of arguments
---@return integer # a count
---@see count
---@see countf
---<hr/>
---
---<b>e.g.</b>
---When given a table, provides the count for the very number of values in that table.
--[[
```lua
M.size {1,2,3} -- => 3
M.size {one = 1, two = 2} -- => 2
```
]]
---<hr/>
---
---<b>e.g.</b>
---When given a vararg list of arguments, returns the count of these arguments.
--[[
```lua
M.size(1,2,3) -- => 3
M.size('a','b',{}, function() end) -- => 4
```
]]
function M.size(...)
    local args = { ... }
    local arg1 = args[1]
    return (type(arg1) == 'table') and count(args[1]) or count(args)
end

---Checks if all the keys of `other` table exists in table `t`. It does not
---compares values. The test is not commutative, i.e table `t` may contains keys
---not existing in `other`.
---@param t table # a table
---@param other table # another table
---@return boolean # `true` or `false`
---@see sameKeys
---<hr/>
---
---<b>e.g.</b>
---Checks whether a table has all the keys existing in another table.
--[[
```lua
M.contains({1,2,3,4},{1,2,3}) -- => true
M.contains({1,2,'d','b'},{1,2,3,5}) -- => true
M.contains({x = 1, y = 2, z = 3},{x = 1, y = 2}) -- => true
```
]]
function M.containsKeys(t, other)
    for key in pairs(other) do
        if not t[key] then return false end
    end
    return true
end

----Checks if both given tables have the same keys. It does not compares values.
---@param tA table # a table
---@param tB table # another table
---@return boolean # `true` or `false`
---@see containsKeys
---<hr/>
---
---<b>e.g.</b>
---Checks whether both tables features the same keys:
--[[
```lua
M.sameKeys({1,2,3,4},{1,2,3}) -- => false
M.sameKeys({1,2,'d','b'},{1,2,3,5}) -- => true
M.sameKeys({x = 1, y = 2, z = 3},{x = 1, y = 2}) -- => false
```
]]
function M.sameKeys(tA, tB)
    for key in pairs(tA) do
        if not tB[key] then return false end
    end
    for key in pairs(tB) do
        if not tA[key] then return false end
    end
    return true
end

--- Array functions
-- @section Array functions

---Samples `n` random values from an array. If `n` is not specified, returns a single element.
---It uses internally `shuffle` to shuffle the array before sampling values. If `seed` is passed,
---it will be used for shuffling.
---@generic v
---@param array v[] # an array
---@param n? integer # a number of elements to be sampled. Defaults to 1.
---@param seed? integer # an optional seed for shuffling
---@return v[] # an array of selected values
---@see sampleProb
---<hr/>
---
---<b>e.g.</b>
---Samples n values from array.
--[[
```lua
local array = M.range(1,20)
local sample = M.sample(array, 3)
print(table.concat(sample,','))

-- => {12,11,15}
```
]]
---<hr/>
---
---<b>e.g.</b>
---`n` defaults to 1. In that case, a single value will be returned.
--[[
```lua
local array = M.range(1,20)
local sample = M.sample(array)
print(sample)

-- => 12
```
]]
function M.sample(array, n, seed)
    n = n or 1
    if n == 0 then return {} end
    if n == 1 then
        if seed then randomseed(seed) end
        return { array[random(1, #array)] }
    end
    return M.slice(M.shuffle(array, seed), 1, n)
end

---Return elements from a sequence with a given probability. It considers each value independently.
---Providing a seed will result in deterministic sampling. Given the same seed it will return the same sample
---every time.
---@generic v
---@param array v[] # an array
---@param prob number # a probability for each element in array to be selected
---@param seed? integer # an optional seed for deterministic sampling
---@return v[] # an array of selected values
---@see sample
---<hr/>
---
---<b>e.g.</b>
---Returns an array of values randomly selected from a given array.
---In case seed is provided, it is used for deterministic sampling.
--[[
```lua
local array = M.range(1,20)
local sample = M.sampleProb(array, 0.2)
print(table.concat(sample,','))

-- => 5,11,12,15

sample = M.sampleProb(array, 0.2, os.time())
print(table.concat(sample,','))

-- => 1,6,10,12,15,20 (or similar)
```
]]
function M.sampleProb(array, prob, seed)
    if seed then randomseed(seed) end
    local t = {}
    for k, v in ipairs(array) do
        if random() < prob then t[#t + 1] = v end
    end
    return t
end

---Returns the n-top values satisfying a predicate. It takes a comparison function
---`comp` used to sort array values, and then picks the top n-values. It leaves the original array untouched.
---@generic v
---@param array v[] # an array
---@param n? integer # a number of values to retrieve. Defaults to 1.
---@param comp? fun(a:v, b:v) # comp a comparison function. Defaults to `<` operator.
---@return v[] # an array of top n values
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function comp(a,b) return a > b end
M.nsorted(array,5, comp) -- => {5,4,3,2,1}
```
]]
---<hr/>
---
---<b>e.g.</b>
---`n` defaults to 1 and `comp` defaults to the `<` operator.
--[[
```lua
local array = M.range(1,20)
M.nsorted(array) -- => {1}
```
]]
function M.nsorted(array, n, comp)
    comp = comp or f_min
    n = n or 1
    local values, count = {}, 0
    for _, v in M.sortedv(array, comp) do
        if count < n then
            count = count + 1
            values[count] = v
        else
            break
        end
    end
    return values
end

---Returns a shuffled copy of a given array. If a seed is provided, it will
---be used to init the built-in pseudo random number generator (using `math.randomseed`).
---@generic v
---@param array v[] # an array
---@param seed? integer # a seed
---@return v[] # a shuffled copy of the given array
---<hr/>
---
---<b>e.g.</b>
---Shuffles a given array.
--[[
```lua
local list = M.shuffle {1,2,3,4,5,6} -- => "{3,2,6,4,1,5}"
M.each(list,print)
```
]]
function M.shuffle(array, seed)
    if seed then randomseed(seed) end
    local _shuffled = {}
    for index, value in ipairs(array) do
        local randPos = floor(random() * index) + 1
        _shuffled[index] = _shuffled[randPos]
        _shuffled[randPos] = value
    end
    return _shuffled
end

---Converts a list of arguments to an array.
---@param ... any # a list of arguments
---@return { [integer]:any } # array of all passed-in args
---<hr/>
---
---<b>e.g.</b>
---Converts a vararg list of arguments to an array.
--[[
```lua
M.pack(1,2,8,'d','a',0) -- => "{1,2,8,'d','a',0}"
```
]]
function M.pack(...) return { ... } end

---Looks for the first occurrence of a given value in an array. Returns the value index if found.
---Uses `isEqual` to compare values.
---@generic v
---@param array v[] # an array of values
---@param value v # value to lookup for
---@param from? integer # the index from where the search will start. Defaults to 1.
---@return integer? # the index of the value if found in the array, __nil__ otherwise.
---@see detect
---<hr/>
---
---<b>e.g.</b>
---Looks for a value in a given array and returns the position of the first occurence.
--[[
```lua
local value = {3}
M.find({{4},{3},{2},{1}},value) -- => 2
```
]]
---<hr/>
---
---<b>e.g.</b>
---It can also start the search at a specific position in the array:
--[[
```lua
-- search value 4 starting from index 3
M.find({1,4,2,3,4,5},4,3) -- => 5
```
]]
function M.find(array, value, from)
    for i = from or 1, #array do
        if M.isEqual(array[i], value) then return i end
    end
end

---Returns an array where values are in reverse order. The passed-in array should not be sparse.
---@generic v
---@param array v[] # an array
---@return v[] # a reversed array
---<hr/>
---
---<b>e.g.</b>
---Reverses an array.
--[[
```lua
M.reverse({1,2,3,'d'}) -- => "{'d',3,2,1}"
```
]]
function M.reverse(array)
    local _array = {}
    for i = #array, 1, -1 do
        _array[#_array + 1] = array[i]
    end
    return _array
end

---Replaces elements in a given array with a given value. In case `i` and `j` are given
---it will only replaces values at indexes between `[i,j]`. In case `j` is greater than the array
---size, it will append new values, increasing the array size.
---@generic v, v2
---@param array v[] # an array
---@param value v2 # value
---@param i? integer # the index from which to start replacing values. Defaults to 1.
---@param j? integer # the index where to stop replacing values. Defaults to the array size.
---@return (v|v2)[] # the original array with values changed
---<hr/>
---
---<b>e.g.</b>
---Replaces all elements in a given array with a given value.
--[[
```lua
local array = M.range(1,5)
M.fill(array, 0) -- => {0,0,0,0,0}
```
]]
---<hr/>
---
---<b>e.g.</b>
---It can start replacing value at a specific index.
--[[
```lua
local array = M.range(1,5)
M.fill(array,0,3) -- => {1,2,0,0,0}
```
]]
---<hr/>
---
---<b>e.g.</b>
---It can replace only values within a specific range.
--[[
```lua
local array = M.range(1,5)
M.fill(array,0,2,4) -- => {1,0,0,0,5}
```
]]
---<hr/>
---
---<b>e.g.</b>
---In case the upper bound index i greather than the array size, it will enlarge the array.
--[[
```lua
local array = M.range(1,5)
M.fill(array,0,5,10) -- => {1,2,3,4,0,0,0,0,0,0}
```
]]
function M.fill(array, value, i, j)
    j = j or M.size(array)
    for i = i or 1, j do array[i] = value end
    return array
end

---Returns an array of `n` zeros.
---@param n integer # a number
---@return integer[] # an array
---@see ones
---@see vector
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.zeros(4) -- => {0,0,0,0}
```
]]
function M.zeros(n) return M.fill({}, 0, 1, n) end

---Returns an array of `n` 1's.
---@param n? integer # a number
---@return integer[] # an array
---@see zeros
---@see vector
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.ones(3) -- => {1,1,1}
```
]]
function M.ones(n) return M.fill({}, 1, 1, n) end

---Returns an array of `n` times a given value.
---@generic v
---@param value v # a value
---@param n? integer # a number
---@return v[] # an array
---@see zeros
---@see ones
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.vector(10, 4) -- => {10,10,10,10}
```
]]
function M.vector(value, n) return M.fill({}, value, 1, n) end

---Collects values from a given array. The passed-in array should not be sparse.
---This function collects values as long as they satisfy a given predicate and returns on the first falsy test.
---<br/><em>Aliased as `takeWhile`</em>
---@generic v
---@param array v[] # an array
---@param f fun(v:v, i:integer):boolean # an iterator function prototyped as `f (v, k)`
---@return v[] # a new table containing all values collected
---@see dropWhile
---<hr/>
---
---<b>e.g.</b>
---Collects values as long as they pass a given test. Stops on the first non-passing test.
--[[
```lua
M.selectWhile({2,4,5,8}, function(v)
  return v%2==0
end) -- => "{2,4}"
```
]]
function M.selectWhile(array, f)
    local t = {}
    for i, v in ipairs(array) do
        if f(v, i) then t[i] = v else break end
    end
    return t
end

---Collects values from a given array. The passed-in array should not be sparse.
---This function collects values as long as they do not satisfy a given predicate and returns on the first truthy test.
---<br/><em>Aliased as `rejectWhile`</em>
---@generic v
---@param array v[] # an array
---@param f fun(v:v, i:integer):boolean # an iterator function prototyped as `f (v, k)`
---@return v[] # a new table containing all values collected
---@see selectWhile
---<hr/>
---
---<b>e.g.</b>
---Removes values as long as they pass a given test. Stops on the first non-passing test.
--[[
```lua
M.dropWhile({2,4,5,8}, function(v)
  return v%2==0
end) -- => "{5,8}"
```
]]
function M.dropWhile(array, f)
    local _i
    for i, v in ipairs(array) do
        if not f(v, i) then
            _i = i
            break
        end
    end
    if (_i == nil) then return {} end
    return M.rest(array, _i)
end

---Returns the index at which a value should be inserted. This index is evaluated so
---that it maintains the sort. If a comparison function is passed, it will be used to sort
---values.
---@generic v
---@param array v[] # an array
---@param value v # the value to be inserted
---@param comp? fun(a:v, b:v):boolean # an comparison function prototyped as `f (a, b)`, defaults to <tt><</tt> operator.
---@param sort? boolean # whether or not the passed-in array should be sorted
---@return integer # the index at which the passed-in value should be inserted
---<hr/>
---
---<b>e.g.</b>
---Returns the index at which a value should be inserted to preserve order.
--[[
```lua
M.sortedIndex({1,2,3},4) -- => 4
```
]]
---<hr/>
---
---<b>e.g.</b>
---Can take a custom comparison functions.
--[[
```lua
local comp = function(a,b) return a<b end
M.sortedIndex({-5,0,4,4},3,comp) -- => 3
```
]]
function M.sortedIndex(array, value, comp, sort)
    local _comp = comp or f_min
    if (sort == true) then t_sort(array, _comp) end
    for i = 1, #array do
        if not _comp(array[i], value) then return i end
    end
    return #array + 1
end

---Returns the index of the first occurrence of value in an array.
---@generic v
---@param array v[] # an array
---@param value v # the value to search for
---@return integer? # the index of the passed-in value or __nil__
---@see lastIndexOf
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.indexOf({1,2,3},2) -- => 2
```
]]
function M.indexOf(array, value)
    for k = 1, #array do
        if array[k] == value then return k end
    end
end

---Returns the index of the last occurrence of value in an array.
---@generic v
---@param array v[] # an array
---@param value v # the value to search for
---@return integer? # the index of the last occurrence of the passed-in value or __nil__
---@see indexOf
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.lastIndexOf({1,2,2,3},2) -- => 3
```
]]
function M.lastIndexOf(array, value)
    local key = M.indexOf(M.reverse(array), value)
    if key then return #array - key + 1 end
end

---Returns the first index at which a predicate returns true.
---@generic v
---@param array v[] # an array
---@param pred fun(v:v, k:integer):boolean # a predicate function prototyped as `pred (v, k)`
---@return integer? # the index found or __nil__
---@see findLastIndex
---<hr/>
---
---<b>e.g.</b>
---Returns the first index at which a predicate passes a truth test.
--[[
```lua
local array = {1,2,3,4,5,6}
local function multipleOf3(v) return v%3==0 end
M.findIndex(array, multipleOf3) -- => 3
```
]]
function M.findIndex(array, pred)
    for k = 1, #array do
        if pred(array[k], k) then return k end
    end
end

--- Returns the last index at which a predicate returns true.
---@generic v
---@param array v[] # an array
---@param pred fun(v:v, k:integer):boolean # a predicate function prototyped as `pred (v, k)`
---@return integer? # the index found or __nil__
---@see findIndex
---<hr/>
---
---<b>e.g.</b>
---Returns the first index at which a predicate passes a truth test.
--[[
```lua
local array = {1,2,3,4,5,6}
local function multipleOf3(v) return v%3==0 end
M.findLastIndex(array, multipleOf3) -- => 6
```
]]
function M.findLastIndex(array, pred)
    local key = M.findIndex(M.reverse(array), pred)
    if key then return #array - key + 1 end
end

---Adds all passed-in values at the top of an array. The last elements will bubble to the
---top of the given array.
---@generic v, v2
---@param array v[] # an array
---@param ... v2 # variable number of arguments
---@return (v|v2)[] # the passed-in array with new values added
---@see prepend
---@see push
---<hr/>
---
---<b>e.g.</b>
---Adds given values at the top of an array. The latter values bubbles at the top.
--[[
```lua
local array = {1}
M.addTop(array,1,2,3,4) -- => "{4,3,2,1,1}"
```
]]
function M.addTop(array, ...)
    for k, v in ipairs({ ... }) do
        t_insert(array, 1, v)
    end
    return array
end

---Adds all passed-in values at the top of an array. As opposed to `addTop`, it preserves the order
---of the passed-in elements.
---@generic v, v2
---@param array v[] # an array
---@param ... v2 # a variable number of arguments
---@return (v|v2)[] # the passed-in array with new values added
---@see addTop
---@see push
---<hr/>
---
---<b>e.g.</b>
---Adds given values at the top of an array, preserving the order at which elements are passed-in.
--[[
```lua
local array = {'old_val'}
M.prepend(array,1,2,3,4) -- => "{1,2,3,4,'old_val'}"
```
]]
function M.prepend(array, ...)
    return M.append({ ... }, array)
end

----Pushes all passed-in values at the end of an array.
---@generic v, v2
---@param array v[] # an array
---@param ... v2 # a variable number of arguments
---@return (v|v2)[] # the passed-in array with new added values
---@see addTop
---@see prepend
---<hr/>
---
---<b>e.g.</b>
---Adds given values at the end of an array.
--[[
```lua
local array = {1}
M.push(array,1,2,3,4) -- => "{1,1,2,3,4}"
```
]]
function M.push(array, ...)
    for _, v in ipairs { ... } do
        array[#array + 1] = v
    end
    return array
end

----Removes and returns the values at the top of a given array.
---<br/><em>Aliased as `pop`</em>
---@generic v
---@param array v[] # an array
---@param n? integer # the number of values to be popped. Defaults to 1.
---@return v,v,v,v,v,v,v # the popped values
---@see unshift
---<hr/>
---
---<b>e.g.</b>
---Removes and returns the first value in an array.
--[[
```lua
local array = {1,2,3}
local shift = M.shift(array) -- => "shift = 1", "array = {2,3}"
```
]]
---<hr/>
---
---<b>e.g.</b>
---If `n` is supplied, returns `n` values.
--[[
```lua
local array = {1,2,3,4,5}
local a, b = M.shift(array, 2) -- => "a = 1, b = 2", "array = {3,4,5}"
```
]]
function M.shift(array, n)
    n = min(n or 1, #array)
    local ret = {}
    for i = 1, n do
        local retValue = array[1]
        ret[#ret + 1] = retValue
        t_remove(array, 1)
    end
    return unpack(ret)
end

---Removes and returns the values at the end of a given array.
---@generic v
---@param array v[] # an array
---@param n? integer # the number of values to be unshifted. Defaults to 1.
---@return v,v,v,v,v,v,v # the values
---@see shift
---<hr/>
---
---<b>e.g.</b>
---Removes and returns the last value in an array.
--[[
```lua
local array = {1,2,3}
local value = M.unshift(array) -- => "value = 3", "array = {1,2}"
```
]]
function M.unshift(array, n)
    n = min(n or 1, #array)
    local ret = {}
    for i = 1, n do
        local retValue = array[#array]
        ret[#ret + 1] = retValue
        t_remove(array)
    end
    return unpack(ret)
end

---Removes all provided values in a given array.
---<br/><em>Aliased as `remove`</em>
---@generic v
---@param array v[] # an array
---@param ... any # a variable number of values to be removed from the array
---@return v[] # the passed-in array with values removed
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.pull({1,2,1,2,3,4,3},1,2,3) -- => "{4}"
```
]]
function M.pull(array, ...)
    local values = { ... }
    for i = #array, 1, -1 do
        for _, rmValue in ipairs(values) do
            if M.isEqual(array[i], rmValue) then
                t_remove(array, i)
                break
            end
        end
    end
    return array
end

---Removes values at an index within the range `[start, finish]`.
---<br/><em>Aliased as `rmRange`, `chop`</em>
---@generic v
---@param array v[] # an array
---@param start? integer # the lower bound index, defaults to the first index in the array.
---@param finish? integer # the upper bound index, defaults to the array length.
---@return v[] # the passed-in array with values removed
---<hr/>
---
---<b>e.g.</b>
---Trims out all values index within a range.
--[[
```lua
local array = {1,2,3,4,5,6,7,8,9}
M.removeRange(array, 3,8) -- => "{1,2,9}"
```
]]
function M.removeRange(array, start, finish)
    start = start or 1
    finish = finish or #array
    if start > finish then
        error("start cannot be greater than finish.")
    end
    for i = finish, start, -1 do
        t_remove(array, i)
    end
    return array
end

---Chunks together consecutive values. Values are chunked on the basis of the return
---value of a provided predicate `f (v, k)`. Consecutive elements which return
---the same value are chunked together. Leaves the first argument untouched if it is not an array.
---@generic v
---@param array v[] # an array
---@param f? fun(v:v, k:integer):any # an iterator function prototyped as `f (v, k)`. Defaults to `identity`.
---@return v[][] # a table of chunks (arrays)
---@see zip
---<hr/>
---
---<b>e.g.</b>
---Iterates over an array aggregating consecutive values in subsets tables, on the basis of the return value of `f(v, k)`.
---Consecutive elements which return the same value are chunked together.
--[[
```lua
local t = {1,5,2,4,3,3,4}
M.chunk(t, function(v) return v%2==0 end) -- => "{{1,5},{2,4},{3,3},{4}}"
```
]]
---If not given, `f` defaults to `identity`.
--[[
```lua
local t = {1,5,2,4,3,3,4}
M.chunk(t) -- => "{{1},{5},{2},{4},{3,3},{4}}"
```
]]
function M.chunk(array, f)
    ---@diagnostic disable-next-line: unbalanced-assignments
    local ch, ck, prev, val = {}, 0
    f = f or M.identity
    for k, v in ipairs(array) do
        val = f(v, k)
        ck = ((val ~= prev) and (ck + 1) or ck)
        prev = (prev == nil) and val or prev
        if not ch[ck] then
            ch[ck] = { array[k] }
        else
            ch[ck][#ch[ck] + 1] = array[k]
        end
        prev = val
    end
    return ch
end

---Slices values indexed within `[start, finish]` range.
---<br/><em>Aliased as `M.sub`</em>
---@generic v
---@param array v[] # an array
---@param start? integer # the lower bound index, defaults to the first index in the array.
---@param finish? integer # the upper bound index, defaults to the array length.
---@return v[] # a new array of sliced values
---<hr/>
---
---<b>e.g.</b>
---Slices and returns a part of an array.
--[[
```lua
local array = {1,2,3,4,5,6,7,8,9}
M.slice(array, 3,6) -- => "{3,4,5,6}"
```
]]
function M.slice(array, start, finish)
    local t = {}
    for k = start or 1, finish or #array do
        t[#t + 1] = array[k]
    end
    return t
end

---Returns the first N values in an array.
---<br/><em>Aliased as `head`, `take` </em>
---@generic v
---@param array v[] # an array
---@param n? integer # the number of values to be collected, defaults to 1.
---@return v[] # a new array
---@see initial
---@see last
---@see rest
---<hr/>
---
---<b>e.g.</b>
---Returns the first N elements in an array.
--[[
```lua
local array = {1,2,3,4,5,6,7,8,9}
M.first(array,3) -- => "{1,2,3}"
```
]]
function M.first(array, n)
    n = n or 1
    local t = {}
    for k = 1, n do
        t[k] = array[k]
    end
    return t
end

---Returns all values in an array excluding the last N values.
---@generic v
---@param array v[] # an array
---@param n? integer # the number of values to be left, defaults to the array length.
---@return v[] # a new array
---@see first
---@see last
---@see rest
---<hr/>
---
---<b>e.g.</b>
---Excludes the last N elements in an array.
--[[
```lua
local array = {1,2,3,4,5,6,7,8,9}
M.initial(array,5) -- => "{1,2,3,4}"
```
]]
function M.initial(array, n)
    local l = #array
    n = n and l - (min(n, l)) or l - 1
    local t = {}
    for k = 1, n do
        t[k] = array[k]
    end
    return t
end

---Returns the last N values in an array.
---@generic v
---@param array v[] # an array
---@param n? integer # the number of values to be collected, defaults to the array length.
---@return v[] # a new array
---@see first
---@see initial
---@see rest
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local array = {1,2,3,4,5,6,7,8,9}
M.last(array,3) -- => "{7,8,9}"
```
]]
function M.last(array, n)
    local l = #array
    n = n and l - min(n - 1, l - 1) or 2
    local t = {}
    for k = n, l do
        t[#t + 1] = array[k]
    end
    return t
end

---Returns all values after index, including the given index itself.
---<br/><em>Aliased as `tail`</em>
---@generic v
---@param array v[] # an array
---@param index? integer # an index, defaults to 1
---@return v[] # a new array
---@see first
---@see initial
---@see last
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local array = {1,2,3,4,5,6,7,8,9}
M.rest(array,6) -- => "{6,7,8,9}"
```
]]
function M.rest(array, index)
    local t = {}
    for k = index or 1, #array do
        t[#t + 1] = array[k]
    end
    return t
end

---Returns the value at a given index.
---@generic v
---@param array v[] # an array
---@param index integer # an index
---@return v # the value at the given index
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local array = {1,2,3,4,5,6}
M.nth(array,3) -- => "3"
```
]]
function M.nth(array, index)
    return array[index]
end

---Returns all truthy values (removes `falses` and `nils`).
---@generic v
---@param array v[] # an array
---@return v[] # a new array
---<hr/>
---
---<b>e.g.</b>
---Trims out all falsy values.
--[[
```lua
M.compact {a,'aa',false,'bb',true} -- => "{'aa','bb',true}"
```
]]
function M.compact(array)
    local t = {}
    for k, v in pairs(array) do
        if v then t[#t + 1] = v end
    end
    return t
end

---Flattens a nested array. Passing `shallow` will only flatten at the first level.
---@generic v
---@param array v[] # an array
---@param shallow? boolean # specifies the flattening depth. Defaults to `false`.`
---@return v[] # a flattened array
---<hr/>
---
---<b>e.g.</b>
---Flattens a nested array.
--[[
```lua
M.flatten({1,{2,3},{4,5,{6,7}}}) -- => "{1,2,3,4,5,6,7}"
```
]]
function M.flatten(array, shallow)
    shallow = shallow or false
    local new_flattened
    local _flat = {}
    for key, value in ipairs(array) do
        if type(value) == 'table' then
            new_flattened = shallow and value or M.flatten(value)
            for k, item in ipairs(new_flattened) do _flat[#_flat + 1] = item end
        else
            _flat[#_flat + 1] = value
        end
    end
    return _flat
end

---Returns values from an array not present in all passed-in args.
---<br/><em>Aliased as `without` and `diff`</em>
---@generic v, v2
---@param array v[] # an array
---@param array2 v2[] # another array
---@return v[] # a new array
---@see union
---@see intersection
---@see symmetricDifference
---<hr/>
---
---<b>e.g.</b>
---Returns values in the given array not present in a second array.
--[[
```lua
local array = {1,2,'a',4,5}
M.difference(array,{1,'a'}) -- => "{2,4,5}"
```
]]
function M.difference(array, array2)
    if not array2 then return M.clone(array) end
    return M.select(array, function(value)
        return not M.include(array2, value)
    end)
end

---Returns the duplicate-free union of all passed in arrays.
---@generic v
---@param ... v[] # a variable number of arrays arguments
---@return v[] # a new array
---@see difference
---@see intersection
---@see symmetricDifference
---<hr/>
---
---<b>e.g.</b>
---Produces a duplicate-free union of all passed-in arrays.
--[[
```lua
local A = {'a'}
local B = {'a',1,2,3}
local C = {2,10}
M.union(A,B,C) -- => "{'a',1,2,3,10}"
```
]]
function M.union(...)
    return M.unique(M.flatten({ ... }))
end

---Returns the intersection of all passed-in arrays.
---Each value in the result is present in each of the passed-in arrays.
---@generic v
---@param ... v[] # a variable number of array arguments
---@return v[] # a new array
---@see difference
---@see union
---@see symmetricDifference
---<hr/>
---
---<b>e.g.</b>
---Returns the intersection (common-part) of all passed-in arrays:
--[[
```lua
local A = {'a'}
local B = {'a',1,2,3}
local C = {2,10,1,'a'}
M.intersection(A,B,C) -- => "{'a'}"
```
]]
function M.intersection(...)
    local arg = { ... }
    local array = arg[1]
    t_remove(arg, 1)
    local _intersect = {}
    for i, value in ipairs(array) do
        if M.all(arg, function(v) return M.include(v, value) end) then
            _intersect[#_intersect + 1] = value
        end
    end
    return _intersect
end

---Checks if all passed in arrays are disjunct.
---@param ... table # a variable number of arrays
---@return boolean # `true` if the intersection of all arrays is not empty, `false` otherwise.
---@see intersection
---<hr/>
---
---<b>e.g.</b>
---Checks if all passed in arrays are disjoint.
--[[
```lua
local A = {'a'}
local B = {'a',1,3}
local C = {3,10,2}

M.disjoint(A,B) -- => false
M.disjoint(A,C) -- => true
M.disjoint(B,C) -- => false
```
]]
function M.disjoint(...)
    return (#M.intersection(...) == 0)
end

---Performs a symmetric difference. Returns values from `array` not present in `array2` and also values
---from `array2` not present in `array`.
---<br/><em>Aliased as `symdiff`</em>
---@generic v, v2
---@param array v[] # an array
---@param array2 v2[] # another array
---@return (v|v2)[] # a new array
---@see difference
---@see union
---@see intersection
---<hr/>
---
---<b>e.g.</b>
---Returns values in the first array not present in the second and also values in the second array not present in the first one.
--[[
```lua
local array = {1,2,3}
local array2 = {1,4,5}
M.symmetricDifference(array, array2) -- => "{2,3,4,5}"
```
]]
function M.symmetricDifference(array, array2)
    return M.difference(
        M.union(array, array2),
        M.intersection(array, array2)
    )
end

---Produces a duplicate-free version of a given array.
---<br/><em>Aliased as `uniq`</em>
---@generic v
---@param array v[] # an array
---@return v[] # a new array, duplicate-free
---@see isunique
---@see duplicates
---<hr/>
---
---<b>e.g.</b>
---Makes an array duplicate-free.
--[[
```lua
M.unique {1,1,2,2,3,3,4,4,4,5} -- => "{1,2,3,4,5}"
```
]]
function M.unique(array)
    local ret = {}
    for i = 1, #array do
        if not M.find(ret, array[i]) then
            ret[#ret + 1] = array[i]
        end
    end
    return ret
end

---Checks if a given array contains distinct values. Such an array is made of distinct elements,
---which only occur once in this array.
---<br/><em>Aliased as `isuniq`</em>
---@generic v
---@param array v[] # an array
---@return boolean # `true` if the given array is unique, `false` otherwise.
---@see unique
---@see duplicates
---<hr/>
---
---<b>e.g.</b>
---Checks if a given array contains no duplicate value.
--[[
```lua
M.isunique({1,2,3,4,5}) -- => true
M.isunique({1,2,3,4,4}) -- => false
```
]]
function M.isunique(array)
    return #array == #(M.unique(array))
end

---Returns an array list of all duplicates in array.
---@generic v
---@param array v[] # an array
---@return v[] # an array-list of duplicates
---@see unique
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.duplicates({1,2,3,3,8,8,3,2,4}) -- => {2,3,8}
```
]]
function M.duplicates(array)
    local dict = M.invert(array)
    local dups = {}
    for k, v in ipairs(array) do
        if dict[v] ~= k and not M.find(dups, v) then
            dups[#dups + 1] = v
        end
    end
    return dups
end

---Merges values of each of the passed-in arrays in subsets.
---Only values indexed with the same key in the given arrays are merged in the same subset.
---<br/><em>Aliased as `transpose`</em>
---@param ... table # variable number of array arguments
---@return table[] # a new array
---@see zipWith
---<hr/>
---
---<b>e.g.</b>
---Zips values from different arrays, on the basis on their common keys.
--[[
```lua
local names = {'Bob','Alice','James'}
local ages = {22, 23}
M.zip(names,ages) -- => "{{'Bob',22},{'Alice',23},{'James'}}"
```
]]
function M.zip(...)
    local args = { ... }
    local n = M.max(args, function(array) return #array end)
    local _ans = {}
    for i = 1, n do
        if not _ans[i] then _ans[i] = {} end
        for _, array in ipairs(args) do
            if (array[i] ~= nil) then _ans[i][#_ans[i] + 1] = array[i] end
        end
    end
    return _ans
end

---Merges values using a given function.
---Only values indexed with the same key in the given arrays are merged in the same subset.
---Function `f` is used to combine values.
---<br/><em>Aliased as `transposeWith`</em>
---@generic v
---@param f fun(...):v # a function
---@param ... table # a variable number of array arguments
---@return v[] # a flat array of results
---@see zip
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local names = {'Bob','Alice','James'}; local ages = {22, 23, 25}
local function introduce(name, age) return 'I am '..name..' and I am '..age..' years old.' end
local t = M.zipWith(introduce,names,ages)
-- => {
-- =>  'I am Bob and I am 22 years old.'
-- =>  'I am Alice and I am 23 years old.'
-- =>  'I am James and I am 25 years old.'
-- => }
```
]]
function M.zipWith(f, ...)
    local args = { ... }
    local n = M.max(args, function(array) return #array end)
    local _ans = {}
    for i = 1, n do
        _ans[i] = f(unpack(M.pluck(args, i)))
    end
    return _ans
end

--- Clones array and appends values from another array.
---@generic v, v2
---@param array v[] # an array
---@param other v2[] # an array
---@return (v|v2)[] # a new array
---<hr/>
---
---<b>e.g.</b>
---Appends two arrays.
--[[
```lua
M.append({1,2,3},{'a','b'}) -- => "{1,2,3,'a','b'}"
```
]]
function M.append(array, other)
    local t = {}
    for i, v in ipairs(array) do t[i] = v end
    for i, v in ipairs(other) do t[#t + 1] = v end
    return t
end

---Interleaves arrays. It returns a single array made of values from all
---passed in arrays in their given order, interleaved.
---@param ... table # a variable list of arrays
---@return table # a new array
---@see interpose
---<hr/>
---
---<b>e.g.</b>
---Interleaves values from passed-in arrays.
--[[
```lua
t1 = {1, 2, 3}
t2 = {'a', 'b', 'c'}
M.interleave(t1, t2) -- => "{1,'a',2,'b',3,'c'}"
```
]]
function M.interleave(...)
    local args = { ... }
    local n = M.max(args, M.size)
    local t = {}
    for i = 1, n do
        for _, array in ipairs(args) do
            if array[i] then t[#t + 1] = array[i] end
        end
    end
    return t
end

---Interposes value in-between consecutive pair of values in array.
---<br/><em>Aliased as `intersperse`</em>
---@generic v, v2
---@name interpose
---@param array v[] # an array
---@param value v2 # a value
---@return (v|v2)[] # a new array
---@see interleave
---<hr/>
---
---<b>e.g.</b>
---Interposes a value between consecutive values in an arrays.
--[[
```lua
M.interpose({1,2,3}, 'a') -- => "{1,'a',2,'b',3,'c'}"
```
]]
function M.interpose(array, value)
    for k = #array, 2, -1 do
        t_insert(array, k, value)
    end
    return array
end

---Produces a flexible list of numbers. If one value is passed, will count from 1 to that value,
---with a default step of 1 (or -1). If two values are passed, will count from the first one to the second one,
---using a default step of 1 (or -1). A third value passed will be considered a step value.
---@param from? number # from the initial value of the range
---@param to? number # the final value of the range
---@param step? number step of count. Defaults to 1 or -1.
---@return number[] # a new array of numbers
---<hr/>
---
---<b>e.g.</b>
---Generates an arithmetic sequence.
--[[
```lua
M.range(1,4) -- => "{1,2,3,4}"
```
]]
---In case a single value is provided, it generates a sequence from 1 to that value.
--[[
```lua
M.range(3) -- => "{1,2,3}"
```
]]
---The incremental step can also be provided as third argument.
--[[
```lua
M.range(0,2,0.7) -- => "{0,0.7,1.4}"
```
]]
---It also handles negative progressions.
--[[
```lua
M.range(-5) -- => "{-1,-2,-3,-4,-5}"
M.range(5,1) -- => "{5,4,3,2,1}"
```
]]
function M.range(from, to, step)
    if (from == nil) and (to == nil) and (step == nil) then
        return {}
    elseif (from ~= nil) and (to == nil) and (step == nil) then
        from, to, step = signum(from), from, signum(from)
    elseif (from ~= nil) and (to ~= nil) and (step == nil) then
        step = signum(to - from)
    end
    local _ranged = { from }
    local steps = max(floor((to - from) / step), 0)
    for i = 1, steps do _ranged[#_ranged + 1] = from + step * i end
    return _ranged
end

---Creates an array list of `n` values, repeated.
---@generic v
---@param value v # a value to be repeated
---@param n integer # the number of repetitions of value.
---@return v[] # a new array of `n` values
---<hr/>
---
---<b>e.g.</b>
---Generates a list of n repetitions of a value.
--[[
```lua
M.rep(4,3) -- => "{4,4,4}"
```
]]
function M.rep(value, n)
    local ret = {}
    for i = 1, n do ret[i] = value end
    return ret
end

---Returns the powerset of array values. For instance, when given the set {1,2,3},
---returns `{{},{1},{2},{3},{1,2},{2,3},{1,3},{1,2,3}}`.
---@generic v
---@param array v[] # an array
---@return v[][] # an array
---<hr/>
---
---<b>e.g.</b>
---Returns the powerset of an array.
--[[
```lua
M.powerset {1,2,3} -- => "{{1},{2},{3},{1,2},{2,3},{1,2,3}}"
```
]]
function M.powerset(array)
    local n = #array
    local powerset = {}
    for _, v in ipairs(array) do
        for j = 1, #powerset do
            local set = powerset[j]
            t_insert(powerset, M.push(M.slice(set), v))
        end
        t_insert(powerset, { v })
    end
    t_insert(powerset, {})
    return powerset
end

---Iterator returning partitions of an array. It returns arrays of length `n`
---made of values from the given array. If the last partition has lower elements than `n` and
---`pad` is supplied, it will be adjusted to `n` of elements with `pad` value.
---@generic v
---@param array v[] # an array
---@param n? integer # the size of partitions. Defaults to 1.
---@param pad? v # pads a value to adjust the last subsequence to the `n` elements
---@return (fun():v[])|nil # an iterator function or __nil__
---@see overlapping
---@see aperture
---<hr/>
---
---<b>e.g.</b>
---Returns an iterator function for partitions of a given array.
--[[
```lua
local t = {1,2,3,4,5,6}
for p in M.partition(t,2) do
  print(table.concat(p, ','))
end

-- => 1,2
-- => 3,4
-- => 5,6

local t = {1,2,3,4,5,6}
for p in M.partition(t,4) do
  print(table.concat(p, ','))
end

-- => 1,2,3,4
-- => 5,6
```
]]
---In case the last partition has less elements than desired, a 3rd argument can be supplied to adjust the partition size.
--[[
```lua
local t = {1,2,3,4,5,6}
for p in M.partition(t,4,0) do
  print(table.concat(p, ','))
end

-- => 1,2,3,4
-- => 5,6,0,0
```
]]
function M.partition(array, n, pad)
    if n <= 0 then return end
    return wrap(function()
        partgen(array, n or 1, yield, pad)
    end)
end

---Iterator returning overlapping partitions of an array.
---If the last subsequence has lower elements than `n` and `pad` is
---supplied, it will be adjusted to `n` elements with `pad` value.
---@generic v
---@param array v[] # an array
---@param n? integer # the size of partitions. Defaults to 2.
---@param pad v # pads a value to adjust the last subsequence to the `n` elements
---@return (fun():v[])|nil # an iterator function or __nil__
---@see partition
---@see aperture
---<hr/>
---
---<b>e.g.</b>
---Returns an iterator function which provides overlapping subsequences of a given array.
--[[
```lua
local t = {1,2,3,4,5,6,7}
for p in M.overlapping(t,3) do
    print(table.concat(p,','))
end

-- => 1,2,3
-- => 3,4,5
-- => 5,6,7

for p in M.overlapping(t,4) do
    print(table.concat(p,','))
end

-- => 1,2,3,4
-- => 4,5,6,7

for p in M.overlapping(t,5) do
    print(table.concat(p,','))
end

-- => 1,2,3,4,5
-- => 5,6,7
```
]]
---In case the last subsequence wil not match the exact desired length, it can be adjusted with a 3rd argument `pad`.
--[[
```lua
local t = {1,2,3,4,5,6,7}
for p in M.overlapping(t,5,0) do
    print(table.concat(p,','))
end

-- => 1,2,3,4,5
-- => 5,6,7,0,0
```
]]
function M.overlapping(array, n, pad)
    if n <= 1 then return end
    return wrap(function()
        partgen2(array, n or 2, yield, pad)
    end)
end

---Iterator returning sliding partitions of an array.
---<br/><em>Aliased as `sliding`</em>
---@generic v
---@param array v[] # an array
---@param n? integer # the size of partitions. Defaults to 2 (and then behaves like `pairwise`)
---@return (fun():v[])|nil # an iterator function or __nil__
---@see partition
---@see overlapping
---@see pairwise
---<hr/>
---
---<b>e.g.</b>
---Returns an iterator function which provides sliding partitions of a given array.
--[[
```lua
local t = {1,2,3,4,5}
for p in M.aperture(t,4) do
  print(table.concat(p,','))
end

-- => 1,2,3,4
-- => 2,3,4,5

for p in M.aperture(t,3) do
  print(table.concat(p,','))
end

-- => 1,2,3
-- => 2,3,4
-- => 3,4,5
```
]]
function M.aperture(array, n)
    if n <= 1 then return end
    return wrap(function()
        partgen3(array, n or 2, yield)
    end)
end

---Iterator returning sliding pairs of an array.
---@generic v
---@param array v[] # an array
---@return fun():v[] # an iterator function
---@see overlapping
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local t = M.range(5)
for p in pairwise(t) do
  print(table.concat(p,','))
end

-- => 1,2
-- => 2,3
-- => 3,4
-- => 4,5
```
]]
---@diagnostic disable-next-line: return-type-mismatch
function M.pairwise(array) return M.aperture(array, 2) end

---Iterator returning the permutations of an array. It returns arrays made of all values
---from the passed-in array, with values permuted.
---@generic v
---@param array v[] # an array
---@return fun():v[] # an iterator function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
t = {'a','b','c'}
for p in M.permutation(t) do
  print(table.concat(p))
end

-- => 'bca'
-- => 'cba'
-- => 'cab'
-- => 'acb'
-- => 'bac'
-- => 'abc'
```
]]
function M.permutation(array)
    return wrap(function()
        permgen(array, #array, yield)
    end)
end

---Concatenates values in a given array. Handles booleans as well. If `sep` string is
---passed, it will be used as a separator. Passing `i` and `j` will result in concatenating
---only values within `[i, j]` range.
---<br/><em>Aliased as `join`</em>
---@generic v
---@param array v[] # a given array
---@param sep? string # a separator string, defaults to the empty string `''`.
---@param i? integer # the starting index, defaults to 1.
---@param j? integer # the final index, defaults to the array length.
---@return string # a string
---<hr/>
---
---<b>e.g.</b>
---Concatenates a given array values:
--[[
```lua
M.concat({'a',1,0,1,'b'}) -- => 'a101b'
```
]]
function M.concat(array, sep, i, j)
    return t_concat(M.map(array, tostring), sep, i, j)
end

---Returns all possible pairs built from given arrays.
---@generic v, v2
---@param array v[] # a first array
---@param array2 v2[] # a second array
---@return { [1]:v, [2]: v2 }[] # an array list of all pairs
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local t = M.xprod({1,2},{'a','b'})
-- => {{1,'a'},{1,'b'},{2,'a'},{2,'b'}}
```
]]
function M.xprod(array, array2)
    local p = {}
    for i, v1 in ipairs(array) do
        for j, v2 in ipairs(array2) do
            p[#p + 1] = { v1, v2 }
        end
    end
    return p
end

---Creates pairs from value and array. Value is always prepended to the pair.
---@generic v, v2
---@param value v # a value
---@param array v2[] # an array
---@return { [1]:v, [2]:v2 }[] # an array list of all pairs
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local t = M.xpairs(1, {1, 2, 3})
-- => {{1,1},{1,2},{1,3}}
```
]]
function M.xpairs(value, array)
    local xpairs = {}
    for k, v in ipairs(array) do
        xpairs[k] = { value, v }
    end
    return xpairs
end

---Creates pairs from value and array. Value is always appended as the last item to the pair.
---@generic v, v2
---@param value v # a value
---@param array v2[] # an array
---@return { [1]:v2, [2]:v }[] # an array list of all pairs
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local t = M.xpairsRight(1, {1, 2, 3})
-- => {{1,1},{2,1},{3,1}}
```
]]
function M.xpairsRight(value, array)
    local xpairs = {}
    for k, v in ipairs(array) do
        xpairs[k] = { v, value }
    end
    return xpairs
end

---Returns the sum of array values.
---@generic v
---@param array v[] # a given array
---@return v # the sum of array values
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.sum({1,2,3,4,5}) -- => 15
```
]]
function M.sum(array)
    local s = 0
    for k, v in ipairs(array) do s = s + v end
    return s
end

---Returns the product of array values.
---@generic v
---@param array v[] # a given array
---@return v # the product of array values
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.product({1,2,3,4,5}) -- => 120
```
]]
function M.product(array)
    local p = 1
    for k, v in ipairs(array) do p = p * v end
    return p
end

---Returns the mean of an array of numbers.
---<br/><em>Aliased as `average`</em>
---@param array number[] # an array of numbers
---@return number # a number
---@see sum
---@see product
---@see median
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.mean({1,2,3,4,5}) -- => 3
```
]]
function M.mean(array)
    return M.sum(array) / (#array)
end

---Returns the median of an array of numbers.
---@param array number[] # an array of numbers
---@return number|nil # a number
---@see sum
---@see product
---@see mean
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.median({1,2,3,4,5}) -- => 3
M.median({1,2,3,4}) -- => 2.5
```
]]
function M.median(array)
    local t = M.sort(M.clone(array))
    local n = #t
    if n == 0 then
        return
    elseif n == 1 then
        return t[1]
    end
    local mid = ceil(n / 2)
    return n % 2 == 0 and (t[mid] + t[mid + 1]) / 2 or t[mid]
end

--- Utility functions
-- @section Utility functions

---The no-operation function. Takes nothing, returns nothing. It is being used internally.
---@return nil
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.noop() -- => nil
```
]]
function M.noop() return end

---Returns the passed-in value. This function is used internally
---as a default iterator.
---@generic v
---@param value v # a value
---@return v # the passed-in value
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.identity(1) -- => 1
M.identity(false) -- => false
M.identity('hello!') -- => 'hello!'
```
]]
function M.identity(value) return value end

---Calls `f` with the supplied arguments. Returns the results of `f(...)`.
---@generic v
---@param f fun(...):v # a function
---@param ... any # a vararg list of args to `f`
---@return v # the result of `f(...)` call.
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.call(math.pow, 2, 3) -- => 8
M.call(string.len, 'hello' ) -- => 5
M.call(table.concat, {1,2,3,4,5}, ',', 2, 4) -- => {2,3,4}
```
]]
function M.call(f, ...)
    return f(...)
end

---Creates a constant function which returns the same output on every call.
---<br/><em>Aliased as `always`</em>
---@generic v
---@param value v # constant value
---@return fun():v # a constant function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local pi = M.constant(math.pi)
pi(1) -- => 3.1415926535898
pi(2) -- => 3.1415926535898
pi(math.pi) -- => 3.1415926535898
```
]]
function M.constant(value)
    return function() return value end
end

---Returns a function which applies `specs` on args. This function produces an object having
---the same structure than `specs` by mapping each property to the result of calling its
---associated function with the supplied arguments
---@generic k, v
---@param specs { [k]:(fun(...):v) } # table
---@return fun(...):{ [k]:v } # a function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local stats = M.applySpec({
  min = function(...) return math.min(...) end,
  max = function(...) return math.max(...) end,
})

stats(5,4,10,1,8) -- => {min = 1, max = 10}
```
]]
function M.applySpec(specs)
    return function(...)
        local spec = {}
        for i, f in pairs(specs) do spec[i] = f(...) end
        return spec
    end
end

---Threads `value` through a series of functions. If a function expects more than one args,
---it can be specified using an array list, where the first item is the function and the following
---are the remaining args neeeded. The value is used as the first input.
---@generic v, v2, v3, v4
---@param value v # a value
---@param ... (fun(state:v|v2):v2)|{ [1]:(fun(state:v|v4, value:v3):v4), [2]:v3 } a vararg list of functions or arrays
---@return v2|v4 # a value
---@see threadRight
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function inc(x) return x + 1 end
local function double(x) return 2 * x end
local function square(x) return x * x end
M.thread(2, inc, double, square) -- => 36
M.thread(3, double, inc, square) -- => 49
M.thread(4, square, double, inc) -- => 33
M.thread(5, square, inc, double) -- => 52

local function inc(x) return x + 1 end
local function add(x, y) return x * y end
local function pow(x, y) return x ^ y end
M.thread(2, inc, {add, 3}, {pow, 2}) -- => 36
M.thread(2, {add, 4}, inc, {pow, 2}) -- => 49
```
]]
function M.thread(value, ...)
    local state = value
    local arg = { ... }
    for _, t in ipairs(arg) do
        if type(t) == 'function' then
            state = t(state)
        elseif type(t) == 'table' then
            local f = t[1]
            t_remove(t, 1)
            state = M.reduce(t, f, state)
        end
    end
    return state
end

---Threads `value` through a series of functions. If a function expects more than one args,
---it can be specified using an array list, where the first item is the function and the following
---are the remaining args neeeded. The value is used as the last input.
---@generic v, v2, v3, v4
---@param value v # a value
---@param ... (fun(state:v|v2):v2)|{ [1]:(fun(state:v|v4, value:v3):v4), [2]:v3 } a vararg list of functions or arrays
---@return v2|v4 # a value
---@see thread
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function inc(x) return x + 1 end
local function add(x, y) return x * y end
local function pow(x, y) return x ^ y end
M.threadRight(2, inc, {add, 3}, {pow, 2}) -- => 64
M.threadRight(2, {add, 4}, inc, {pow, 2}) -- => 128
```
]]
function M.threadRight(value, ...)
    local state = value
    local arg = { ... }
    for k, t in ipairs(arg) do
        if type(t) == 'function' then
            state = t(state)
        elseif type(t) == 'table' then
            local f = t[1]
            t_remove(t, 1)
            t_insert(t, state)
            state = M.reduce(t, f)
        end
    end
    return state
end

---Returns a dispatching function. When called with arguments, this function invokes each of its functions
---in the passed-in order and returns the results of the first non-nil evaluation.
---@param ... function # a vararg list of functions
---@return function # a dispatch function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.dispatch(
  function() return nil end,
  function (v) return v+1 end,
  function (v) return 2*v end
)
f(5) -- => 6
f(7) -- => 8
```
]]
function M.dispatch(...)
    local funcs = { ... }
    return function(...)
        for k, f in ipairs(funcs) do
            local r = { f(...) }
            if #r > 0 then return unpack(r) end
        end
    end
end

---Memoizes a given function by caching the computed result.
---Useful for speeding-up slow-running functions.
---<br/><em>Aliased as `cache`</em>
---@generic v
---@param f fun(key:any):v # a function
---@return fun(Key:any):v # a new function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function fibonacci(n)
  return n < 2 and n or fibonacci(n-1)+fibonacci(n-2)
end
local mem_fibonacci = M.memoize(fibonacci)
fibonacci(20) -- => 6765 (but takes some time)
mem_fibonacci(20) -- => 6765 (takes less time)
```
]]
function M.memoize(f)
    local _cache = setmetatable({}, { __mode = 'kv' })
    return function(key)
        if (_cache[key] == nil) then
            _cache[key] = f(key)
        end
        return _cache[key]
    end
end

---Builds a list from a seed value. Accepts an iterator function, which
---returns either nil to stop iteration or two values : the value to add to the list
---of results and the seed to be used in the next call to the iterator function.
---@generic v, v2
---@param f fun(seed?:v2):(v?, v2?) an iterator function
---@param seed? v2 # a seed value
---@return v[] # an array of values
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function f(v)
  if v < 100 then return v, v * 2 end
end
local t = M.unfold(f, 10) -- => {10,20,40,80}
```
]]
function M.unfold(f, seed)
    ---@diagnostic disable-next-line: unbalanced-assignments
    local t, result = {}
    while true do
        result, seed = f(seed)
        if result ~= nil then
            t[#t + 1] = result
        else
            break
        end
    end
    return t
end

---Returns a version of `f` that runs only once. Successive calls to `f`
---will keep yielding the same output, no matter what the passed-in arguments are.
---It can be used to initialize variables.
---@generic v
---@param f fun(...):v # a function
---@return fun(...):v # a new function
---@see before
---@see after
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local sq = M.once(function(a) return a*a end)
sq(1) -- => 1
sq(2) -- => 1
sq(3) -- => 1
sq(4) -- => 1
sq(5) -- => 1
```
]]
function M.once(f)
    local _internal = 0
    local _args = {}
    return function(...)
        _internal = _internal + 1
        if _internal <= 1 then _args = { ... } end
        return f(unpack(_args))
    end
end

---Returns a version of `f` that will run no more than <em>count</em> times. Next calls will
---keep yielding the results of the count-th call.
---@generic v
---@param f fun(...):v # a function
---@param count integer # a count
---@return fun(...):v # a new function
---@see once
---@see after
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function greet(someone) return 'hello '..someone end
local greetOnly3people = M.before(greet, 3)
greetOnly3people('John') -- => 'hello John'
greetOnly3people('Moe') -- => 'hello Moe'
greetOnly3people('James') -- => 'hello James'
greetOnly3people('Joseph') -- => 'hello James'
greetOnly3people('Allan') -- => 'hello James'
```
]]
function M.before(f, count)
    local _internal = 0
    local _args = {}
    return function(...)
        _internal = _internal + 1
        if _internal <= count then _args = { ... } end
        return f(unpack(_args))
    end
end

---Returns a version of `f` that runs on the `count-th` call.
---Useful when dealing with asynchronous tasks.
---@generic v
---@param f fun(...):v a function
---@param count integer # the number of calls before `f` will start running.
---@return fun(...):v # a new function
---@see once
---@see before
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.after(M.identity,3)
f(1) -- => nil
f(2) -- => nil
f(3) -- => 3
f(4) -- => 4
```
]]
function M.after(f, count)
    local _limit, _internal = count, 0
    return function(...)
        _internal = _internal + 1
        if _internal >= _limit then return f(...) end
    end
end

---Composes functions. Each passed-in function consumes the return value of the function that follows.
---In math terms, composing the functions `f`, `g`, and `h` produces the function `f(g(h(...)))`.
---@param ... function # a variable number of functions
---@return function # a new function
---@see pipe
---Fix issue where functions passed into _.compose could be run twice:
---https://github.com/Yonaba/Moses/pull/15#issuecomment-139038895
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function f(x) return x^2 end
local function g(x) return x+1 end
local function h(x) return x/2 end
local compositae = M.compose(f,g,h)
compositae(10) -- => 36
compositae(20) -- => 121
```
]]
function M.compose(...)
    local f = M.reverse { ... }
    return function(...)
        ---@diagnostic disable-next-line: unbalanced-assignments
        local first, _temp = true
        for i, func in ipairs(f) do
            if first then
                first = false
                _temp = func(...)
            else
                _temp = func(_temp)
            end
        end
        return _temp
    end
end

---Pipes a value through a series of functions. In math terms,
---given some functions `f`, `g`, and `h` in that order, it returns `f(g(h(value)))`.
---@param value unknown # a value
---@param ... function # a variable number of functions
---@return unknown # the result of the composition of function calls.
---@see compose
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function f(x) return x^2 end
local function g(x) return x+1 end
local function h(x) return x/2 end
M.pipe(10,f,g,h) -- => 36
M.pipe(20,f,g,h) -- => 121
```
]]
function M.pipe(value, ...)
    return M.compose(...)(value)
end

---Returns the logical complement of a given function. For a given input, the returned
---function will output `false` if the original function would have returned `true`,
---and vice-versa.
---@param f function # a function
---@return function # logical complement of the given function `f`.
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.complement(function() return true end)() -- => false
```
]]
function M.complement(f)
    return function(...) return not f(...) end
end

---Calls a sequence of passed-in functions with the same argument.
---Returns a sequence of results.
---<br/><em>Aliased as `juxt`</em>
---@generic v
---@param value v # a value
---@param ... fun(value:v):unknown # a variable number of functions
---@return ... # a list of results
---<hr/>
---
---<b>e.g.</b>
---Calls a sequence of functions with the same input.
--[[
```lua
local function f(x) return x^2 end
local function g(x) return x+1 end
local function h(x) return x/2 end
M.juxtapose(10, f, g, h) -- => 100, 11, 5
```
]]
function M.juxtapose(value, ...)
    local res = {}
    for i, func in ipairs({ ... }) do
        res[i] = func(value)
    end
    return unpack(res)
end

---Wraps `f` inside of the `wrapper` function. It passes `f` as the first argument to `wrapper`.
---This allows the wrapper to execute code before and after `f` runs,
---adjust the arguments, and execute it conditionally.
---@generic f : function, ret
---@param f f # a function to be wrapped, prototyped as `f (...)`
---@param wrapper fun(f:f, ...):ret # wrapper function, prototyped as `wrapper (f, ...)`
---@return fun(...):ret # the results
---<hr/>
---
---<b>e.g.</b>
---Wraps a function inside a wrapper. Allows the wrapper to execute code before and after function run.
--[[
```lua
local greet = function(name) return "hi: " .. name end
local greet_backwards = M.wrap(greet, function(f,arg)
  return f(arg) ..'\nhi: ' .. arg:reverse()
end)
greet_backwards('John')

-- => hi: John
-- => hi: nhoJ
```
]]
function M.wrap(f, wrapper)
    return function(...) return wrapper(f, ...) end
end

---Runs `iter` function `n` times. Collects the results of each run and returns them in an array.
---@generic v
---@param iter fun(i:integer):v # an iterator function, prototyped as `iter (i)`
---@param n? integer # the number of times `iter` should be called. Defaults to 1.
---@return v[] # an array of results
---<hr/>
---
---<b>e.g.</b>
---Calls a given function `n` times.
--[[
```lua
local f = ('Lua programming'):gmatch('.')
M.times(f, 3) -- => {'L','u','a'}
```
]]
function M.times(iter, n)
    local results = {}
    for i = 1, (n or 1) do
        results[i] = iter(i)
    end
    return results
end

---Binds `v` to be the first argument to `f`. Calling `f (...)` will result to `f (v, ...)`.
---@generic v, ret
---@param f fun(v:v, ...):ret # a function
---@param v v # a value
---@return fun(...):ret # a function
---@see bind2
---@see bindn
---@see bindall
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local sqrt2 = M.bind(math.sqrt,2)
sqrt2() -- => 1.4142135623731
```
]]
function M.bind(f, v)
    return function(...)
        return f(v, ...)
    end
end

---Binds `v` to be the second argument to `f`. Calling `f (a, ...)` will result to `f (a, v, ...)`.
---@generic v, v2, ret
---@param f fun(t:v, v:v2, ...):ret # a function
---@param v v2 # a value
---@return fun(t:v, ...):ret # a function
---@see bind
---@see bindn
---@see bindall
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local last2 = M.bind(M.last,2)
last2({1,2,3,4,5,6}) -- => {5,6}
```
]]
function M.bind2(f, v)
    return function(t, ...)
        return f(t, v, ...)
    end
end

---Binds `...` to be the N-first arguments to function `f`.
---Calling `f (a1, a2, ..., aN)` will result to `f (..., a1, a2, ...,aN)`.
---@generic ret
---@param f fun(...):ret # a function
---@param ... any # a variable number of arguments
---@return fun(...):ret # a function
---@see bind
---@see bind2
---@see bindall
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function out(...) return table.concat {...} end
local out = M.bindn(out,'OutPut',':',' ')
out(1,2,3) -- => OutPut: 123
out('a','b','c','d') -- => OutPut: abcd
```
]]
function M.bindn(f, ...)
    local args = { ... }
    return function(...)
        return f(unpack(M.append(args, { ... })))
    end
end

---Binds methods to object. As such, whenever any of these methods is invoked, it
---always receives the object as its first argument.
---@generic o
---@param obj o # an abject
---@param ... string # a variable number of method names
---@return o # the passed-in object with all methods bound to the object itself.
---@see bind
---@see bind2
---@see bindn
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local window = {
    setPos = function(w,x,y) w.x, w.y = x, y end,
    setName = function(w,name) w.name = name end,
    getName = function(w) return w.name end,
}
window = M.bindall(window, 'setPos', 'setName', 'getName')
window.setPos(10,15)
print(window.x, window.y) -- => 10,15

window.setName('fooApp')
print(window.name) -- => 'fooApp'

print(window.getName()) -- => 'fooApp'
```
]]
function M.bindall(obj, ...)
    local methodNames = { ... }
    for i, methodName in ipairs(methodNames) do
        local method = obj[methodName]
        if method then obj[methodName] = M.bind(method, obj) end
    end
    return obj
end

---Returns a function which iterate over a set of conditions. It invokes each predicate,
---passing it given values. It returns the value of the corresponding function of the first
---predicate to return a non-nil value.
---@generic ret
---@param conds { [1]:(fun(...):boolean), [2]:(fun(...):ret) }[] # an array list of predicate-function pairs
---@return fun(...):ret # the result of invoking `f(...)` of the first predicate to return a non-nil value
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local multipleOf = M.cond({
  {function(v) return v%2==0 end, function(v) return v..' is multiple of 2' end},
  {function(v) return v%3==0 end, function(v) return v..' is multiple of 3' end},
  {function(v) return v%5==0 end, function(v) return v..' is multiple of 5' end},
  {function() return true end, function(v) return 'could not find an answer for '..v end}
})
for i = 15, 20 do
  print(multipleOf(i))
end

-- => 15 is multiple of 3
-- => 16 is multiple of 2
-- => could not find an answer for 17
-- => 18 is multiple of 2
-- => could not find an answer for 19
-- => 20 is multiple of 2
```
]]
function M.cond(conds)
    return function(...)
        for k, condset in ipairs(conds) do
            if condset[1](...) then
                return condset[2](...)
            end
        end
    end
end

---Returns a validation function. Given a set of functions, the validation function evaluates
---to `true` only when all its funcs returns `true`.
---@param ... fun(...):boolean # an array list of functions
---@return fun(...):boolean # `true` when all given funcs returns true with input, false otherwise
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.both(
function(x) return x > 0 end,
function(x) return x < 10 end,
function(x) return x % 2 == 0 end
)
f(2) -- => true
f(8) -- => true
f(9) -- => false
```
]]
function M.both(...)
    local funcs = { ... }
    return function(...)
        for k, f in ipairs(funcs) do
            if not f(...) then return false end
        end
        return true
    end
end

---Returns a validation function. Given a set of functions, the validation function evaluates
---to `true` when at least one of its funcs returns `true`.
---@param ... fun(...):boolean # an array list of functions
---@return fun(...):boolean # `true` when one of the given funcs returns `true` with input, `false` otherwise
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.either(
    function(x) return x > 0 end,
    function(x) return x % 2 == 0 end
)
f(0) -- => true
f(-3) -- => false
```
]]
function M.either(...)
    local funcs = { ... }
    return function(...)
        for k, f in ipairs(funcs) do
            if f(...) then return true end
        end
        return false
    end
end

---Returns a validation function. Given a set of functions, the validation function evaluates
---to `true` when neither of its func return `true`.
---@param ... fun(...):boolean an array list of functions
---@return fun(...):boolean # `true` when neither of the given funcs returns `true` with input, `false` otherwise
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.neither(
    function(x) return x > 10 end,
    function(x) return x % 2 == 0 end
)
f(12) -- => false
f(8) -- => false
f(7) -- => true
```
]]
function M.neither(...)
    local funcs = { ... }
    return function(...)
        for k, f in ipairs(funcs) do
            if f(...) then return false end
        end
        return true
    end
end

---Generates an unique ID for the current session. If given a string `template`, it
---will use this template for output formatting. Otherwise, if `template` is a function, it
---will evaluate `template (id)`.
---<br/><em>Aliased as `uid`</em>.
---@generic v
---@param template string|(fun(integer):v) # either a string or a function template to format the ID
---@return integer|string|v # an ID
---<hr/>
---
---<b>e.g.</b>
---Returns an unique integer ID.
--[[
```lua
M.uniqueId() -- => 1
```
]]
---Can handle string templates for formatted output.
--[[
```lua
M.uniqueId('ID%s') -- => 'ID2'
```
]]
---Or a function, for the same purpose.
--[[
```lua
local formatter = function(ID) return '$'..ID..'$' end
M.uniqueId(formatter) -- => '$ID1$'
```
]]
function M.uniqueId(template)
    unique_id_counter = unique_id_counter + 1
    if template then
        if type(template) == 'string' then
            return template:format(unique_id_counter)
        elseif type(template) == 'function' then
            return template(unique_id_counter)
        end
    end
    return unique_id_counter
end

---Produces an iterator which repeatedly apply a function `f` onto an input.
---Yields `value`, then `f(value)`, then `f(f(value))`, continuously.
---<br/><em>Aliased as `iter`</em>.
---@generic v
---@param f fun(value:v):v # a function
---@param value? v # an initial input to `f`
---@param n? integer # the number of times the iterator should run
---@return fun():v # an iterator function
---<hr/>
---
---<b>e.g.</b>
---Go through the powers of two using `iterator`.
--[[
```lua
local function po2(x) return x*2 end
local function iter_po2 = M.iterator(po2, 1)
iter_po2() -- => 2
iter_po2() -- => 4
iter_po2() -- => 8
```
]]
---if `n` is supplied, it will run at maximum `n` times.
--[[
```lua
local function po2(x) return x*2 end
local function iter_po2 = M.iterator(po2, 1, 3)
iter_po2() -- => 2
iter_po2() -- => 4
iter_po2() -- => 8
iter_po2() -- => nil
```
]]
function M.iterator(f, value, n)
    local cnt = 0
    return function()
        cnt = cnt + 1
        if n and cnt > n then return end
        value = f(value)
        return value
    end
end

---Consumes the first `n` values of a iterator then returns it.
---@generic f : function
---@param iter f # an iterator function
---@param n? integer # a number. Defaults to 1.
---@return f? # the given iterator or __nil__ when `iter` returns nothing
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local w = "hello"
local char = string.gmatch(w,'.')
local iter = M.skip(char, 3)
for w in iter do print(w) end -- => 'l', 'o'
```
]]
function M.skip(iter, n)
    for i = 1, (n or 1) do
        if iter() == nil then return end
    end
    return iter
end

---Iterates over an iterator and returns its values in an array.
---@generic v
---@param ... fun():v # an iterator function (returning a generator, a state and a value)
---@return v[] # an array of results
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local text = 'letters'
local chars = string.gmatch(text, '.')
M.tabulate(chars) -- => {'l','e','t','t','e','r','s'}
```
]]
function M.tabulate(...)
    local r = {}
    for v in ... do r[#r + 1] = v end
    return r
end

---Returns the length of an iterator. It consumes the iterator itself.
---@param ... function # an iterator function (returning a generator, a state and a value)
---@return integer # the iterator length
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local text = 'lua'
local chars = string.gmatch(text, '.')
M.iterlen(chars) -- => 3
chars() -- => nil
```
]]
function M.iterlen(...)
    local l = 0
    for v in ... do l = l + 1 end
    return l
end

---Casts value as an array if it is not one.
---@generic v
---@param value v # a value
---@return v[] # an array containing the given value
---<hr/>
---
---<b>e.g.</b>
---Casts the passed-in value to an array containing the value itself.
--[[
```lua
M.castArray(true) -- => {true}
M.castArray(2) -- => {2}
```
]]
---It leaves the given value untouched in case it is already a table.
--[[
```lua
local t = {1}
print(M.castArray(t) == t) -- => true
```
]]
function M.castArray(value)
    return (type(value) ~= 'table') and { value } or value
end

---Creates a function of `f` with arguments flipped in reverse order.
---@param f function # a function
---@return function # a function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function f(...) return table.concat({...}) end
local flipped = M.flip(f)
flipped('a','b','c') -- => 'cba'
```
]]
function M.flip(f)
    return function(...)
        return f(unpack(M.reverse({ ... })))
    end
end

---Returns a function that gets the nth argument.
---If `n` is negative, the nth argument from the end is returned.
---@param n integer # a number
---@return function # a function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.nthArg(3)
f('a','b','c') -- => 'c'

f = M.nthArg(-2)
f('a','b','c') -- => 'b'
```
]]
function M.nthArg(n)
    return function(...)
        local args = { ... }
        return args[(n < 0) and (#args + n + 1) or n]
    end
end

---Returns a function which accepts up to one arg. It ignores any additional arguments.
---@generic a1, ret
---@param f fun(arg:a1):ret # a function
---@return fun(arg:a1):ret # a function
---@see ary
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.unary(function (...) return ... end)
f('a') -- ==> 'a'
f('a','b','c') -- => 'a'
```
]]
function M.unary(f)
    return function(...)
        local args = { ... }
        return f(args[1])
    end
end

---Returns a function which accepts up to `n` args. It ignores any additional arguments.
---<br/><em>Aliased as `nAry`</em>.
---@generic ret
---@param f fun(...):ret # a function
---@param n? integer # a number. Defaults to 1.
---@return fun(...):ret # a function
---@see unary
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.ary(function (...) return ... end, 2)
f(1,2) -- ==> 1,2
f(1,2,3,4) -- => 1,2
f = M.unary(function (...) return ... end)
f('a','b','c') -- => 'a'
```
]]
function M.ary(f, n)
    n = n or 1
    return function(...)
        local args = { ... }
        local fargs = {}
        for i = 1, n do fargs[i] = args[i] end
        return f(unpack(fargs))
    end
end

---Returns a function with an arity of 0. The new function ignores any arguments passed to it.
---@generic ret
---@param f fun(...):ret # a function
---@return fun():ret # a new function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.noarg(function (x) return x or 'default' end)
f(1) -- => 'default'
f(function() end, 3) -- => 'default'
```
]]
function M.noarg(f)
    return function()
        return f()
    end
end

---Returns a function which runs with arguments rearranged. Arguments are passed to the
---returned function in the order of supplied `indexes` at call-time.
---@generic ret
---@param f fun(...):ret #  a function
---@param indexes integer[] # an array list of indexes
---@return fun(...):ret #  a function
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local f = M.rearg(function (...) return ... end, {5,4,3,2,1})
f('a','b','c','d','e') -- => 'e','d','c','b','a'
```
]]
function M.rearg(f, indexes)
    return function(...)
        local args = { ... }
        local reargs = {}
        for i, arg in ipairs(indexes) do reargs[i] = args[arg] end
        return f(unpack(reargs))
    end
end

---Creates a function that runs transforms on all arguments it receives.
---@param ... any # a set of functions which will receive all arguments to the returned function
---@return function # a function
---@see overEvery
---@see overSome
---@see overArgs
---<hr/>
---
---<b>e.g.</b>
---Get the tuple of min and max values from a set of values
--[[
```lua
local minmax = M.over(math.min, math.max)
minmax(5,10,12,4,3) -- => {3,12}
```
]]
function M.over(...)
    local transforms = { ... }
    return function(...)
        local r = {}
        for i, transform in ipairs(transforms) do
            r[#r + 1] = transform(...)
        end
        return r
    end
end

---Creates a validation function. The returned function checks if *all* of the given predicates return
---truthy when invoked with the arguments it receives.
---@param ... function # a list of `predicate` functions
---@return fun(...):boolean # a new function
---@see over
---@see overSome
---@see overArgs
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
function M.overEvery(...)
    local f = M.over(...)
    return function(...)
        return M.reduce(f(...), function(state, v) return state and v end)
    end
end

local function alleven(...)
    for i, v in ipairs({ ... }) do
        if v % 2 ~= 0 then return false end
    end
    return true
end

local function allpositive(...)
    for i, v in ipairs({ ... }) do
        if v < 0 then return false end
    end
    return true
end

local allok = M.overEvery(alleven, allpositive)

allok(2, 4, -1, 8) -- => false
allok(10, 3, 2, 6) -- => false
allok(8, 4, 6, 10) -- => true
```
]]
function M.overEvery(...)
    local f = M.over(...)
    return function(...)
        return M.reduce(f(...), function(state, v) return state and v end)
    end
end

---Creates a validation function. The return function checks if *any* of a given predicates return
---truthy when invoked with the arguments it receives.
---@param ... function # a list of predicate functions
---@return fun(...):boolean # a new function
---@see over
---@see overEvery
---@see overArgs
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function alleven(...)
    for i, v in ipairs({...}) do
        if v%2~=0 then return false end
    end
    return true
end

local function allpositive(...)
    for i, v in ipairs({...}) do
        if v < 0 then return false end
    end
    return true
end

local anyok = M.overSome(alleven,allpositive)

anyok(2,4,-1,8) -- => false
anyok(10,3,2,6) -- => true
anyok(-1,-5,-3) -- => false
```
]]
function M.overSome(...)
    local f = M.over(...)
    return function(...)
        return M.reduce(f(...), function(state, v) return state or v end)
    end
end

---Creates a function that invokes `f` with its arguments transformed. 1rst arguments will be passed to
---the 1rst transform, 2nd arg to the 2nd transform, etc. Remaining arguments will not be transformed.
---@param f function # a function
---@param ... function # a list of transforms funcs prototyped as `f (v)`
---@return function # the result of running `f` with its transformed arguments
---@see over
---@see overEvery
---@see overSome
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function f(x, y) return x, y end
local function triple(x) retun x*3 end
local function square(x) retun x^2 end
local new_f = M.overArgs(f, triple, square)

new_f(1,2) -- => 3, 4
new_f(10,10) -- => 30, 100
```
]]
---In case the number of arguments is greater than the number of transforms, the remaining args will be left as-is.
--[[
```lua
local function f(x, y, z) return x, y, z end
local function triple(x) retun x*3 end
local function square(x) retun x^2 end
local new_f = M.overArgs(f, triple, square)

new_f(1,2,3) -- => 3, 4, 3
new_f(10,10,10) -- => 30, 100, 10
```
]]
function M.overArgs(f, ...)
    local _argf = { ... }
    return function(...)
        local _args = { ... }
        for i = 1, #_argf do
            local func = _argf[i]
            if _args[i] then _args[i] = func(_args[i]) end
        end
        return f(unpack(_args))
    end
end

---Converges two functions into one.
---@param f function # a function
---@param g function # a function
---@param h function # a function
---@return function # a new version of function `f`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function pow2(x) return x*x end
local function pow3(x) return x*x*x end
local function sum(a,b) return a+b end
local poly = M.converge(sum, pow2, pow3)
poly(5) -- => 150 (ie. 5*5 + 5*5*5)
```
]]
function M.converge(f, g, h) return function(...) return f(g(...), h(...)) end end

---Partially apply a function by filling in any number of its arguments.
---One may pass a string `'_'` as a placeholder in the list of arguments to specify an argument
---that should not be pre-filled, but left open to be supplied at call-time.
---@generic ret
---@param f fun(...):ret # a function
---@param ... any # a list of partial arguments to `f`
---@return fun(...):ret # a new version of function f having some of it original arguments filled
---@see partialRight
---@see curry
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function diff(a, b) return a - b end
local diffFrom20 = M.partial(diff, 20) -- arg 'a' will be 20 by default
diffFrom20(5) -- => 15

local remove5 = M.partial(diff, '_', 5) -- arg 'a' will be given at call-time, but 'b' is set to 5
remove5(20) -- => 15
```
]]
function M.partial(f, ...)
    local partial_args = { ... }
    return function(...)
        local n_args = { ... }
        local f_args = {}
        for k, v in ipairs(partial_args) do
            f_args[k] = (v == '_') and M.shift(n_args) or v
        end
        return f(unpack(M.append(f_args, n_args)))
    end
end

---Similar to `partial`, but from the right.
---@generic ret
---@param f fun(...):ret # a function
---@param ... any # a list of partial arguments to `f`
---@return fun(...):ret # a new version of function f having some of it original arguments filled
---@see partialRight
---@see curry
---<hr/>
---
---<b>e.g.</b>
---Like `M.partial`, it partially applies a function by filling in any number of its arguments, but from the right.
--[[
```lua
local function concat(...) return table.concat({...},',') end
local concat_right = M.partialRight(concat,'a','b','c')
concat_right('d') -- => d,a,b,c

concat_right = M.partialRight(concat,'a','b')
concat_right('c','d') -- => c,d,a,b

concat_right = M.partialRight(concat,'a')
concat_right('b','c','d') -- => b,c,d,a
```
]]
---The string `'_'`, as always, can be used as a placeholder in the list of arguments to specify an argument that should not be pre-filled,
---but is rather left open to be supplied at call-time.
---In that case, the first args supplied at runtime will be used to fill the initial list of args while the remaining will be prepended.
--[[
```lua
local function concat(...) return table.concat({...},',') end
local concat_right = M.partialRight(concat,'a','_','c')
concat_right('d','b') -- => b,a,d,c

concat_right = M.partialRight(concat,'a','b','_')
concat_right('c','d') -- => d,a,b,c

concat_right = M.partialRight(concat,'_','a')
concat_right('b','c','d') -- => c,d,b,a
```
]]
function M.partialRight(f, ...)
    local partial_args = { ... }
    return function(...)
        local n_args = { ... }
        local f_args = {}
        for k = 1, #partial_args do
            f_args[k] = (partial_args[k] == '_') and M.shift(n_args) or partial_args[k]
        end
        return f(unpack(M.append(n_args, f_args)))
    end
end

---Curries a function. If the given function `f` takes multiple arguments, it returns another version of
---`f` that takes a single argument (the first of the arguments to the original function) and returns a new
---function that takes the remainder of the arguments and returns the result.
---@param f function # a function
---@param n_args integer # the number of arguments expected for `f`. Defaults to 2.
---@return function # a curried version of `f`
---@see partial
---@see partialRight
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function sumOf3args(x,y,z) return x + y + z end
local curried_sumOf3args = M.curry(sumOf3args, 3)
sumOf3args(1)(2)(3) -- => 6
sumOf3args(0)(6)(9) -- => 15
```
]]
---<hr/>
---
---<b>e.g.</b>
---`n_args` defaults to 2.
--[[
```lua
local function product(x,y) return x * y end
local curried_product = M.curry(product)
curried_product(5)(4) -- => 20
curried_product(3)(-5) -- => -15
curried_product(0)(1) -- => 0
```
]]
function M.curry(f, n_args)
    n_args = n_args or 2
    local _args = {}
    local function scurry(v)
        if n_args == 1 then return f(v) end
        if v ~= nil then _args[#_args + 1] = v end
        if #_args < n_args then
            return scurry
        else
            local r = { f(unpack(_args)) }
            _args = {}
            return unpack(r)
        end
    end

    return scurry
end

---Returns the execution time of `f (...)` in seconds and its returned values.
---@param f function # a function
---@param ... any # optional args to `f`
---@return number, ... # the execution time and the results of `f (...)`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local function wait_count(n)
    local i = 0
    while i < n do i = i + 1 end
    return i
end

local time, i = M.time(wait_count, 1e6) -- => 0.002 1000000
local time, i = M.time(wait_count, 1e7) -- => 0.018 10000000
```
]]
function M.time(f, ...)
    local stime = clock()
    local r = { f(...) }
    return clock() - stime, unpack(r)
end

--- Object functions
-- @section Object functions

---Returns the keys of the object properties.
---@generic k
---@param obj { [k]:unknown } an object
---@return k[] # an array of keys
---<hr/>
---
---<b>e.g.</b>
---Collects the names of an object attributes.
--[[
```lua
M.keys({1,2,3}) -- => "{1,2,3}"
M.keys({x = 0, y = 1}) -- => "{'y','x'}"
```
]]
function M.keys(obj)
    local keys = {}
    for key in pairs(obj) do keys[#keys + 1] = key end
    return keys
end

---Returns the values of the object properties.
---@generic v
---@param obj { [unknown]:v } # an object
---@return v[] # an array of values
---<hr/>
---
---<b>e.g.</b>
---Collects the values of an object attributes.
--[[
```lua
M.values({1,2,3}) -- => "{1,2,3}"
M.values({x = 0, y = 1}) -- => "{1,0}"
```
]]
function M.values(obj)
    local values = {}
    for key, value in pairs(obj) do values[#values + 1] = value end
    return values
end

---Returns the value at a given path in an object.
---Path is given as a vararg list of keys.
---@param obj unknown # an object
---@param ... any # a vararg list of keys
---@return unknown # a value or __nil__
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local entity = {
  pos = {x = 1, y = 2},
  engine = {
    left = {status = 'active', damage = 5},
    right = {status = 'off', damage = 10}
  },
  boost = false
}

M.path(entity,'pos','x') -- => 1
M.path(entity,'pos','y') -- => 2
M.path(entity,'engine','left','status') -- => 'active'
M.path(entity,'engine','right','damage') -- => 10
M.path(entity,'boost') -- => false
```
]]
function M.path(obj, ...)
    local value, path = obj, { ... }
    for i, p in ipairs(path) do
        if (value[p] == nil) then return end
        value = value[p]
    end
    return value
end

---Spreads object under property path onto provided object.
-- It is similar to `flattenPath`, but removes object under the property path.
---@param obj unknown # an object
---@param ... any # a property path given as a vararg list
---@return unknown # the passed-in object with changes
---@see flattenPath
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local obj = {a = 1, b = 2, c = {d = 3, e = 4, f = {g = 5}}}
M.spreadPath(obj, 'c', 'f')
-- => {a = 1, b = 2, d = 3, e = 4, g = 5, c = {f = {}}}
```
]]
function M.spreadPath(obj, ...)
    local path = { ... }
    for _, p in ipairs(path) do
        if obj[p] then
            for k, v in pairs(obj[p]) do
                obj[k] = v
                obj[p][k] = nil
            end
        end
    end
    return obj
end

---Flattens object under property path onto provided object.
---It is similar to `spreadPath`, but preserves object under the property path.
---@param obj unknown # an object
---@param ... any # a property path given as a vararg list
---@return unknown # the passed-in object with changes
---@see spreadPath
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local obj = {a = 1, b = 2, c = {d = 3, e = 4, f = {g = 5}}}
M.spreadPath(obj, 'c', 'f')
-- => {a = 1, b = 2, d = 3, e = 4, g = 5, c = {d = 3, e = 4, f = {g = 5}}}
```
]]
function M.flattenPath(obj, ...)
    local path = { ... }
    for _, p in ipairs(path) do
        if obj[p] then
            for k, v in pairs(obj[p]) do obj[k] = v end
        end
    end
    return obj
end

---Converts key-value pairs to an array-list of `[k, v]` pairs.
---@generic k, v
---@param obj { [k]:v } an object
---@return { [1]:k, [2]:v }[] # an array list of key-value pairs
---@see toObj
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local obj = {x = 1, y = 2, z = 3}
M.each(M.kvpairs(obj), function(v,k)
    print(k, table.concat(v,','))
end)

-- => 1 y,2
-- => 2 x,1
-- => 3 z,3
```
]]
function M.kvpairs(obj)
    local t = {}
    for k, v in pairs(obj) do t[#t + 1] = { k, v } end
    return t
end

---Converts an array list of `[k,v]` pairs to an object. Keys are taken
---from the 1rst column in the `[k,v]` pairs sequence, associated with values in the 2nd column.
---@generic k, v
---@param kvpairs { [1]:k, [2]:v }[] # an array-list of `[k,v]` pairs
---@return { [k]:v } # an object
---@see kvpairs
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local list_pairs = {{'x',1},{'y',2},{'z',3}}
local obj = M.toObj(list_pairs)

-- => {x = 1, y = 2, z = 3}
```
]]
function M.toObj(kvpairs)
    local obj = {}
    for _, v in ipairs(kvpairs) do
        obj[v[1]] = v[2]
    end
    return obj
end

---Swaps keys with values. Produces a new object where previous keys are now values,
---while previous values are now keys.
---<br/><em>Aliased as `mirror`</em>
---@generic k, v
---@param obj { [k]:v } # a given object
---@return { [v]:k } # a new object
---<hr/>
---
---<b>e.g.</b>
---Switches key-value pairs:
--[[
```lua
M.invert {'a','b','c'} -- => "{a=1, b=2, c=3}"
M.invert {x = 1, y = 2} -- => "{'x','y'}"
```
]]
function M.invert(obj)
    local _ret = {}
    for k, v in pairs(obj) do
        _ret[v] = k
    end
    return _ret
end

---Returns a function that will return the key property of any passed-in object.
---@generic k, v
---@param key k # a key property name
---@return fun(obj:{ [k]:v }):v # a function which should accept an object as argument
---@see propertyOf
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local who = M.property('name')
local people = {name = 'Henry'}
who(people) -- => 'Henry'
```
]]
function M.property(key)
    return function(obj) return obj[key] end
end

---Returns a function which will return the value of an object property.
---@generic k, v
---@param obj { [k]:v } # an object
---@return fun(key:k):v # a function which should accept a key property argument
---@see property
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local people = {name = 'Henry'}
print(M.propertyOf(people)('name')) -- => 'Henry'
```
]]
function M.propertyOf(obj)
    return function(key) return obj[key] end
end

---Converts any given value to a boolean
---@param value any # a value. Can be of any type
---@return boolean # `true` if value is true, `false` otherwise (false or nil).
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.toBoolean(true) -- => true
M.toBoolean(false) -- => false
M.toBoolean(nil) -- => false
M.toBoolean({}) -- => true
M.toBoolean(1) -- => true
```
]]
function M.toBoolean(value)
    return not not value
end

---Extends an object properties. It copies the properties of extra passed-in objects
---into the destination object, and returns the destination object. The last objects
---will override properties of the same name.
---@param destObj {} # a destination object
---@param ... {} # a list of objects
---@return {} # the destination object extended
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.extend({},{a = 'b', c = 'd'}) -- => "{a = 'b', c = 'd'}"
```
]]
function M.extend(destObj, ...)
    local sources = { ... }
    for k, source in ipairs(sources) do
        if type(source) == 'table' then
            for key, value in pairs(source) do destObj[key] = value end
        end
    end
    return destObj
end

---Returns a sorted list of all methods names found in an object. If the given object
---has a metatable implementing an `__index` field pointing to another table, will also recurse on this
---table if `recurseMt` is provided. If `obj` is omitted, it defaults to the library functions.
---<br/><em>Aliased as `methods`</em>.
---@param obj? {} # an object. Defaults to Moses library functions.
---@param recurseMt? boolean
---@return any[] # an array-list of methods names
---<hr/>
---
---<b>e.g.</b>
---Returns all functions names within an object.
--[[
```lua
M.functions(coroutine)
-- => "{'yield','wrap','status','resume','running','create'}"
```
]]
---<hr/>
---
---<b>e.g.</b>
---When given `recurseMt`, will also include `obj` metatable's functions.
--[[
```lua
local mt = {print = print}
local t = {assert = assert}
setmetatable(t, {__index = mt})
M.functions(t, true) -- => "{'assert','print'}"
```
]]
function M.functions(obj, recurseMt)
    obj = obj or M
    local _methods = {}
    for key, value in pairs(obj) do
        if type(value) == 'function' then
            _methods[#_methods + 1] = key
        end
    end
    if recurseMt then
        local mt = getmetatable(obj)
        if mt and mt.__index then
            local mt_methods = M.functions(mt.__index, recurseMt)
            for k, fn in ipairs(mt_methods) do
                _methods[#_methods + 1] = fn
            end
        end
    end
    return _methods
end

---Clones a given object properties. If `shallow` is passed will also clone nested array properties.
---@generic v
---@param obj v # an object
---@param shallow? boolean # whether or not nested array-properties should be cloned, defaults to false.
---@return v # a copy of the passed-in object
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local obj = {1,2,3}
local obj2 = M.clone(obj)
print(obj2 == obj) -- => false
print(M.isEqual(obj2, obj)) -- => true
```
]]
function M.clone(obj, shallow)
    if type(obj) ~= 'table' then return obj end
    local _obj = {}
    for i, v in pairs(obj) do
        if type(v) == 'table' then
            if not shallow then
                _obj[i] = M.clone(v, shallow)
            else
                _obj[i] = v
            end
        else
            _obj[i] = v
        end
    end
    return _obj
end

---Invokes interceptor with the object, and then returns object.
---The primary purpose of this method is to "tap into" a method chain, in order to perform operations
---on intermediate results within the chain.
---@generic o
---@param obj o # an object
---@param f fun(obj:o) # an interceptor function, should be prototyped as `f (obj)`
---@return o # the passed-in object
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local v = M.chain({1,2,3,4,5,6,7,8,9,10})
  :filter(function(v) return v%2~=0 end) -- retain odd values
  :tap(function(v) print('Max is', M.max(v)) end) -- Tap max value
  :map(function(v) return v^2 end)
  :value() -- =>	 Max is 89
```
]]
function M.tap(obj, f)
    f(obj)
    return obj
end

---Checks if a given object implements a property.
---@param obj any # an object
---@param key any # a key property to be checked
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.has(_,'has') -- => true
M.has(coroutine,'resume') -- => true
M.has(math,'random') -- => true
```
]]
function M.has(obj, key)
    return obj[key] ~= nil
end

---Returns an object copy having white-listed properties.
---<br/><em>Aliased as `choose`</em>.
---@generic k, v
---@param obj { [k]:v } # an object
---@param ... k # a variable number of string keys
---@return { [k]:v } # the filtered object
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local object = {a = 1, b = 2, c = 3}
M.pick(object,'a','c') -- => "{a = 1, c = 3}"
```
]]
function M.pick(obj, ...)
    local whitelist = M.flatten { ... }
    local _picked = {}
    for key, property in pairs(whitelist) do
        if (obj[property]) ~= nil then
            _picked[property] = obj[property]
        end
    end
    return _picked
end

---Returns an object copy without black-listed properties.
---<br/><em>Aliased as `drop`</em>.
---@generic k, v
---@param obj { [k]:v } # an object
---@param ... k # a variable number of string keys
---@return { [k]:v } # the filtered object
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local object = {a = 1, b = 2, c = 3}
M.omit(object,'a','c') -- => "{b = 2}"
```
]]
function M.omit(obj, ...)
    local blacklist = M.flatten { ... }
    local _picked = {}
    for key, value in pairs(obj) do
        if not M.include(blacklist, key) then
            _picked[key] = value
        end
    end
    return _picked
end

---Applies a template to an object, preserving non-nil properties.
---<br/><em>Aliased as `defaults`</em>.
---@param obj {} # an object
---@param template? {} # a template object. If `nil`, leaves `obj` untouched.
---@return {} # the passed-in object filled
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
local obj = {a = 0}
M.template(obj,{a = 1, b = 2, c = 3}) -- => "{a=0, c=3, b=2}"
```
]]
function M.template(obj, template)
    if not template then return obj end
    for i, v in pairs(template) do
        if not obj[i] then obj[i] = v end
    end
    return obj
end

---Performs a deep comparison test between two objects. Can compare strings, functions
---(by reference), nil, booleans. Compares tables by reference or by values. If `useMt`
---is passed, the equality operator `==` will be used if one of the given objects has a
---metatable implementing `__eq`.
---<br/><em>Aliased as `M.compare`, `M.matches`</em>
---@param objA any # an object
---@param objB any # another object
---@param useMt? boolean # whether or not `__eq` should be used, defaults to false.
---@return boolean # `true` or `false`
---@see allEqual
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isEqual(1,1) -- => true
M.isEqual(true,false) -- => false
M.isEqual(3.14,math.pi) -- => false
M.isEqual({3,4,5},{3,4,{5}}) -- => false
```
]]
function M.isEqual(objA, objB, useMt)
    local typeObjA = type(objA)
    local typeObjB = type(objB)

    if typeObjA ~= typeObjB then return false end
    if typeObjA ~= 'table' then return (objA == objB) end

    local mtA = getmetatable(objA)
    local mtB = getmetatable(objB)

    if useMt then
        if (mtA or mtB) and (mtA.__eq or mtB.__eq) then
            return mtA.__eq(objA, objB) or mtB.__eq(objB, objA) or (objA == objB)
        end
    end

    if M.size(objA) ~= M.size(objB) then return false end

    local vB
    for i, vA in pairs(objA) do
        vB = objB[i]
        if vB == nil or not M.isEqual(vA, vB, useMt) then return false end
    end

    for i in pairs(objB) do
        if objA[i] == nil then return false end
    end

    return true
end

---Invokes an object method. It passes the object itself as the first argument. if `method` is not
---callable, will return `obj[method]`.
---@param obj {} # an object
---@param method string # a string key to index in object `obj`, or a function.
---@return any # the returned value of `method (obj)` call
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.result('abc','len') -- => 3
M.result({'a','b','c'},table.concat) -- => 'abc'
```
]]
function M.result(obj, method)
    if obj[method] then
        if M.isCallable(obj[method]) then
            return obj[method](obj)
        else
            return obj[method]
        end
    end
    if M.isCallable(method) then
        return method(obj)
    end
end

---Checks if the given arg is a table.
---@param t any # value to be tested
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isTable({}) -- => true
M.isTable(math) -- => true
M.isTable(string) -- => true
```
]]
function M.isTable(t)
    return type(t) == 'table'
end

---Checks if the given argument is callable. Assumes `obj` is callable if
---it is either a function or a table having a metatable implementing `__call` metamethod.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isCallable(print) -- => true
M.isCallable(function() end) -- => true
M.isCallable(setmetatable({},{__index = string}).upper) -- => true
M.isCallable(setmetatable({},{__call = function() return end})) -- => true
```
]]
function M.isCallable(obj)
    return ((type(obj) == 'function') or
        ((type(obj) == 'table') and getmetatable(obj) and getmetatable(obj).__call ~= nil) or
        false)
end

---Checks if the given argument is an array. Assumes `obj` is an array
---if is a table with consecutive integer keys starting at 1.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isArray({}) -- => true
M.isArray({1,2,3}) -- => true
M.isArray({'a','b','c'}) -- => true
```
]]
function M.isArray(obj)
    if not (type(obj) == 'table') then return false end
    -- Thanks @Wojak and @Enrique García Cota for suggesting this
    -- See : http://love2d.org/forums/viewtopic.php?f=3&t=77255&start=40#p163624
    local i = 0
    for k in pairs(obj) do
        i = i + 1
        if obj[i] == nil then return false end
    end
    return true
end

---Checks if the given object is iterable with `pairs` (or `ipairs`).
---@param obj any # an object
---@return boolean # `true` if the object can be iterated with `pairs` (or `ipairs`), `false` otherwise
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isIterable({}) -- => true
M.isIterable(function() end) -- => false
M.isIterable(false) -- => false
M.isIterable(1) -- => false
```
]]
function M.isIterable(obj)
    return M.toBoolean((pcall(pairs, obj)))
end

---Extends Lua's `type` function. It returns the type of the given object and also recognises
---file userdata
---@param obj any # an object
---@return type|'file' # the given object type
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.type('string') -- => 'string'
M.type(table) -- => 'table'
M.type(function() end) -- => 'function'
M.type(io.open('f','w')) -- => 'file'
```
]]
function M.type(obj)
    local tp = type(obj)
    if tp == 'userdata' then
        local mt = getmetatable(obj)
        local stdout = io and io.stdout or nil
        if stdout ~= nil and mt == getmetatable(stdout) then
            return 'file'
        end
    end
    return tp
end

---Checks if the given pbject is empty. If `obj` is a string, will return `true`
---if `#obj == 0`. Otherwise, if `obj` is a table, will return whether or not this table
---is empty. If `obj` is `nil`, it will return true.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isEmpty('') -- => true
M.isEmpty({})  -- => true
M.isEmpty({'a','b','c'}) -- => false
```
]]
function M.isEmpty(obj)
    if (obj == nil) then return true end
    if type(obj) == 'string' then return #obj == 0 end
    if type(obj) == 'table' then return next(obj) == nil end
    return true
end

---Checks if the given argument is a string.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isString('') -- => true
M.isString('Hello') -- => false
M.isString({}) -- => false
```
]]
function M.isString(obj)
    return type(obj) == 'string'
end

---Checks if the given argument is a function.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isFunction(print) -- => true
M.isFunction(function() end) -- => true
M.isFunction({}) -- => false
```
]]
function M.isFunction(obj)
    return type(obj) == 'function'
end

---Checks if the given argument is nil.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isNil(nil) -- => true
M.isNil() -- => true
M.isNil({}) -- => false
```
]]
function M.isNil(obj)
    return obj == nil
end

---Checks if the given argument is a number.
---@param obj any # an object
---@return boolean # `true` or `false`
---@see isNaN
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isNumber(math.pi) -- => true
M.isNumber(math.huge) -- => true
M.isNumber(0/0) -- => true
M.isNumber() -- => false
```
]]
function M.isNumber(obj)
    return type(obj) == 'number'
end

--- Checks if the given argument is NaN (see [Not-A-Number](http://en.wikipedia.org/wiki/NaN)).
---@param obj any # an object
---@return boolean # `true` or `false`
---@see isNumber
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isNaN(1) -- => false
M.isNaN(0/0) -- => true
```
]]
function M.isNaN(obj)
    return type(obj) == 'number' and obj ~= obj
end

--- Checks if the given argument is a finite number.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isFinite(99e99) -- => true
M.isFinite(math.pi) -- => true
M.isFinite(math.huge) -- => false
M.isFinite(1/0) -- => false
M.isFinite(0/0) -- => false
```
]]
function M.isFinite(obj)
    if type(obj) ~= 'number' then return false end
    return obj > -huge and obj < huge
end

--- Checks if the given argument is a boolean.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isBoolean(true) -- => true
M.isBoolean(false) -- => true
M.isBoolean(1==1) -- => true
M.isBoolean(print) -- => false
```
]]
function M.isBoolean(obj)
    return type(obj) == 'boolean'
end

--- Checks if the given argument is an integer.
---@param obj any # an object
---@return boolean # `true` or `false`
---<hr/>
---
---<b>e.g.</b>
--[[
```lua
M.isInteger(math.pi) -- => false
M.isInteger(1) -- => true
M.isInteger(-1) -- => true
```
]]
function M.isInteger(obj)
    return type(obj) == 'number' and floor(obj) == obj
end

-- Aliases

do
    -- Table functions aliases
    M.forEach       = M.each
    M.forEachi      = M.eachi
    M.update        = M.adjust
    M.alleq         = M.allEqual
    M.loop          = M.cycle
    M.collect       = M.map
    M.inject        = M.reduce
    M.foldl         = M.reduce
    M.injectr       = M.reduceRight
    M.foldr         = M.reduceRight
    M.mapr          = M.mapReduce
    M.maprr         = M.mapReduceRight
    M.any           = M.include
    M.some          = M.include
    M.contains      = M.include
    M.filter        = M.select
    M.discard       = M.reject
    M.every         = M.all

    -- Array functions aliases
    M.takeWhile     = M.selectWhile
    M.rejectWhile   = M.dropWhile
    M.pop           = M.shift
    M.remove        = M.pull
    M.rmRange       = M.removeRange
    M.chop          = M.removeRange
    M.sub           = M.slice
    M.head          = M.first
    M.take          = M.first
    M.tail          = M.rest
    M.without       = M.difference
    M.diff          = M.difference
    M.symdiff       = M.symmetricDifference
    M.xor           = M.symmetricDifference
    M.uniq          = M.unique
    M.isuniq        = M.isunique
    M.transpose     = M.zip
    M.part          = M.partition
    M.perm          = M.permutation
    M.transposeWith = M.zipWith
    M.intersperse   = M.interpose
    M.sliding       = M.aperture
    M.mirror        = M.invert
    M.join          = M.concat
    M.average       = M.mean

    -- Utility functions aliases
    M.always        = M.constant
    M.cache         = M.memoize
    M.juxt          = M.juxtapose
    M.uid           = M.uniqueId
    M.iter          = M.iterator
    M.nAry          = M.ary

    -- Object functions aliases
    M.methods       = M.functions
    M.choose        = M.pick
    M.drop          = M.omit
    M.defaults      = M.template
    M.compare       = M.isEqual
    M.matches       = M.isEqual
end

M._VERSION     = 'Moses v' .. _MODULEVERSION
M._URL         = 'http://github.com/Yonaba/Moses'
M._LICENSE     = 'MIT <http://raw.githubusercontent.com/Yonaba/Moses/master/LICENSE>'
M._DESCRIPTION = 'utility-belt library for functional programming in Lua'
return M
