local old_next = next
next = nil
print(pairs({})) -- Output: <function> <object> nil
local t = {}
local a, b, c = pairs(t)
print(a == old_next) -- Output: true
print(b == t) -- Output: true

local t = {a = 1, b = 2, c = 3, [1] = 4, [2] = 5, [3] = 6}
local sum = 0
for k, v in pairs(t) do
  sum = sum + v
end
print(sum) -- Output: 21

local mt = {__pairs = function() return 1, 2, 3, 4 end}
setmetatable(t, mt)
print(pairs(t)) -- Output: 1 2 3

---
pairs(nil) -- Error: pairs: value is not an object: nil
