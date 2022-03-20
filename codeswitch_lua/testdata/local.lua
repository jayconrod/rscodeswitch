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

local a = 12, 34
print(a) -- Output: 12

local c<const> = 12
print(c) -- Output: 12

local function printret(a)
  print(a)
  return a
end
local a = 12, printret(34) -- Output: 34
print(a) -- Output: 12

local function ret2()
  return 1, 2
end
local a, b = ret2()
print(a, b) -- Output: 1 2
local c, d = 0, ret2()
print(c, d) -- Output: 0 1
local e, f = ret2(), 9
print(e, f) -- Output: 1 9
