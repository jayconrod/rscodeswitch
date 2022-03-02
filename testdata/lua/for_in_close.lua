local mt = {__close = function() print("close") end}
local function make_closer()
  local c = {}
  setmetatable(c, mt)
  return c
end

local function range_fn(state, control)
  if control >= state then
    return nil
  else
    return control + 1
  end
end

local function range(n)
  return range_fn, n, 0, make_closer()
end

-- Close variable is closed when loop ends normally.
for i in range(2) do
  print(i)
end
-- Output: 1
-- Output: 2
-- Output: close

-- Close variable is closed on goto.
for i in range(2) do
  print(i)
  goto out
end
::out::
-- Output: 1
-- Output: close

-- Close variable is closed on break.
for i in range(2) do
  print(i)
  break
end
-- Output: 1
-- Output: close

-- Close variable is closed on return.
local function f()
  for i in range(2) do
    print(i)
    return
  end
end
f()
-- Output: 1
-- Output: close
