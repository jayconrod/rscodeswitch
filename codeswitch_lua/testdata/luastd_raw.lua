local mt = {
  __eq = function(l, r)
    print("eq", l, r)
    return false
  end,

  __index = function(t, i)
    print("index", t, i)
    return 99
  end,

  __newindex = function(t, i, v)
    print("newindex", t, i, v)
  end,

  __len = function(t)
    print("len", t)
    return 99
  end,
}
local t = {x = 12}
setmetatable(t, mt)

print(t == t) -- Output: eq <object> <object>
-- Output: false
print(rawequal(t, t)) -- Output: true

print(t.x) -- Output: 12
print(t.y) -- Output: index <object> y
-- Output: 99
print(rawget(t, "x")) -- Output: 12
print(rawget(t, "y")) -- Output: nil

print(#t) -- Output: len <object>
-- Output: 99
print(rawlen(t)) -- Output: 0

t.y = 98 -- Output: newindex <object> y 98
print(t.y) -- Output: index <object> y
-- Output: 99
rawset(t, "y", 98)
print(t.y) -- Output: 98
