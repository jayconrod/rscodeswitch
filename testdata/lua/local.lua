local a
print(a) -- Output: nil

local a = 12
print(a) -- Output: 12

local a, b = 12
print(a) -- Output: 12
print(b) -- Output: nil
b = 34
print(b) -- Output: 34

g = 99
local g = 12
print(g) -- Output: 12

-- TODO: test that second expression gets evaluated
local a = 12, 34
print(a) -- Output: 12

local c<const> = 12
print(c) -- Output: 12
