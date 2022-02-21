-- Basic functionality
print(tostring()) -- Output: nil
print(tostring(true)) -- Output: true
print(tostring(1)) -- Output: 1
print(tostring(1.5)) -- Output: 1.5
print(tostring("a")) -- Output: a
print(tostring({})) -- Output: <object>
print(tostring(function() end)) -- Output: <function>

-- __tostring method is called by tostring.
local a = {x = 12}
print(tostring(a)) -- Output: <object>
local mt = {
  __tostring = function(self)
    return "object with x = " .. self.x
  end
}
print(tostring(mt)) -- Output: <object>
setmetatable(a, mt)
print(tostring(a)) -- Output: object with x = 12

-- __tostring method is called by print.
print(a) -- Output: object with x = 12

-- __name does nothing.
-- TODO: tostring should return something like "<joebob>".
-- This isn't strictly required by the reference.
mt.__name = "joebob"
print(tostring(a)) -- Output: object with x = 12
mt.__tostring = nil
print(tostring(a)) -- Output: <object>
mt.__name = 12
print(tostring(a)) -- Output: <object>

---
-- The __tostring method should cause an error if it's not a method.
local a = {}
local mt = {__tostring = 12}
setmetatable(a, mt)
tostring(a) -- Error: <unknown>: __tostring is not a method
