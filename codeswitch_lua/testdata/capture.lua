local function curried_add(a)
  local function f(b)
    return a + b
  end
  return f
end
print(curried_add(2)(3)) -- Output: 5

local function capture_top_local()
  local x = 1
  local function f()
    return x
  end
  return f
end
print(capture_top_local()()) -- Output: 1

local function capture_nested_local()
  do
    local x = 1
    local function f()
      return x
    end
    return f
  end
end
print(capture_nested_local()()) -- Output: 1

local function return_captured_top_local()
  local x = 1
  local function f()
    return x
  end
  return x
end
print(return_captured_top_local()) -- Output: 1

local function return_captured_nested_local()
  do
    local x = 1
    local function f()
      return x
    end
    return x
  end
end
print(return_captured_nested_local()) -- Output: 1

local function deep_capture()
  local x = 1
  local function f()
    local function g()
      return x
    end
    return g
  end
  return f
end
print(deep_capture()()()) -- Output: 1

local function assign_capture_same()
  local x = 1
  local function f()
    return x
  end
  x = 2
  return x
end
print(assign_capture_same()) -- Output: 2

local function assign_capture_enclosing()
  local x = 1
  local function f()
    x = 2
    return x
  end
  return f
end
print(assign_capture_enclosing()()) -- Output: 2

local function new_counter()
  local n = 0
  local function next()
    n = n + 1
    return n
  end
  return next
end
local c = new_counter()
print(c(), c(), c()) -- Output: 1 2 3
