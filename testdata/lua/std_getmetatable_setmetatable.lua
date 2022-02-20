print(getmetatable(nil)) -- Output: nil
print(getmetatable(1)) -- Output: nil
print(getmetatable({})) -- Output: nil

local mt = {x = 1}
local a = {}
print(setmetatable(a, mt)) -- Output: nil
print(getmetatable(a) == mt) -- Output: true
