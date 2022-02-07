local function print0()
  print(0)
end
local function print1(a)
  print(a)
end
local function print2(a, b)
  print(a, b)
end
print0() -- Output: 0
print0(1) -- Output: 0
print1() -- Output: nil
print1(1) -- Output: 1
print1(1, 2) -- Output: 1
print1 "a" -- Output: a
print2() -- Output: nil nil
print2(1) -- Output: 1 nil
print2(1, 2) -- Output: 1 2

local function ret0()
  return
end
local function retsemi()
  return;
end
local function ret1()
  return 1
end
local function ret2()
  return 1, 2
end
print(ret0(), 9) -- Output: nil 9
print(retsemi(), 9) -- Output: nil 9
print(ret1(), 9) -- Output: 1 9
print(ret2(), 9) -- Output: 1 9
print(0, ret0()) -- Output: 0
print(0, retsemi()) -- Output: 0
print(0, ret1()) -- Output: 0 1
print(0, ret2()) -- Output: 0 1 2

local function retcallonly(f)
  return f()
end
local function retcallbegin(f)
  return f(), 9
end
local function retcallend(f)
  return 0, f()
end
print(0, retcallonly(ret0)) -- Output: 0
print(retcallonly(ret1)) -- Output: 1
print(retcallonly(ret2)) -- Output: 1 2
print(retcallbegin(ret0)) -- Output: nil 9
print(retcallbegin(ret1)) -- Output: 1 9
print(retcallbegin(ret2)) -- Output: 1 9
print(retcallend(ret0)) -- Output: 0
print(retcallend(ret1)) -- Output: 0 1
print(retcallend(ret2)) -- Output: 0 1 2
