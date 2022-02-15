-- Calling a variadic function with normal arguments should work.
-- The function should be able to access its non-variadic parameters.
local function f(...)
  return 1
end
print(f()) -- Output: 1
print(f(1)) -- Output: 1
print(f(1, 2)) -- Output: 1

local function f(a, ...)
  return a
end
print(f()) -- Output: nil
print(f(1)) -- Output: 1
print(f(1, 2)) -- Output: 1

local function f(a, b, ...)
  return a, b
end
print(f()) -- Output: nil nil
print(f(1)) -- Output: 1 nil
print(f(1, 2)) -- Output: 1 2
print(f(1, 2, 3)) -- Output: 1 2

-- The expression "..." should produce the first value or nil in contexts
-- where a single value is expected.
local function f(...)
  local a = ..., nil
  return a
end
print(f()) -- Output: nil
print(f(1)) -- Output: 1
print(f(1, 2)) -- Output: 1

-- The expression "..." should expand to all values in contexts where
-- multiple values are expected.
local function f(...)
  local a, b = ...
  return a, b
end
print(f()) -- Output: nil nil
print(f(1)) -- Output: 1 nil
print(f(1, 2)) -- Output: 1 2

local function ret_args(...)
  return ...
end
print(ret_args()) -- Output:
print(ret_args(1)) -- Output: 1
print(ret_args(1, 2)) -- Output: 1 2

local function count_args(a, ...)
  if a == nil then
    return 0
  else
    return 1 + count_args(...)
  end
end
print(count_args()) -- Output: 0
print(count_args(1)) -- Output: 1
print(count_args(1, 2)) -- Output: 2
print(count_args(1, 2, 3)) -- Output: 3
