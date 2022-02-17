-- _ENV holds global variables, including definitions in the standard lib.
print(_ENV["print"] == print) -- Output: true
x = 12
print(_ENV["x"]) -- Output: 12

-- Assignment to _ENV is ignored.
_ENV = nil
print(_ENV == nil) -- Output: false

-- _G points to the same table.
print(_ENV == _G) -- Output: true
print(_G["x"]) -- Output: 12

-- _G can be assigned though
_G = nil
print(_G) -- Output: nil
