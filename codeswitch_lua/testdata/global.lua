print(x) -- Output: nil

a = 1
print(a) -- Output: 1

a, b = 1
print(b) -- Output: nil

a = 1, 2
print(a) -- Output: 1

local function printret(a)
  print(a)
  return a
end
a = 12, printret(34) -- Output: 34
print(a) -- Output: 12

local function ret2()
  return 1, 2
end
a, b = ret2()
print(a, b) -- Output: 1 2
c, d = 0, ret2()
print(c, d) -- Output: 0 1
e, f = ret2(), 9
print(e, f) -- Output: 1 9
