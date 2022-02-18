print(tostring()) -- Output: nil
print(tostring(true)) -- Output: true
print(tostring(1)) -- Output: 1
print(tostring(1.5)) -- Output: 1.5
print(tostring("a")) -- Output: a
print(tostring({})) -- Output: <object>
print(tostring(function() end)) -- Output: <function>

-- TODO: test with __tostring metatable method
