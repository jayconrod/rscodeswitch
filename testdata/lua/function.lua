-- New global function
function a() print(1) end
a() -- Output: 1

-- Redefinition of local
local b = nil
function b() print(2) end
b() -- Output: 2

-- Redefinition of captured local
local c = nil
local function cap() return c end
function c() print(3) end
cap()() -- Output: 3

-- Redefinition of parameter
local function d_parent(d)
  function d() print(4) end
  return d
end
d_parent()() -- Output: 4

-- Assign to field
local o = {}
function o.a(x) print(x) end
o.a(5) -- Output: 5

-- Assign to nested field
o.o = {}
function o.o.a(x) print(x) end
o.o.a(6) -- Output: 6

-- Assign to field with receiver
o.x = 7
function o:b() print(self.x) end
o:b() -- Output: 7

-- Assign to nested field with receiver
o.o.x = 8
function o.o:c() print(self.x) end
o.o:c() -- Output: 8
