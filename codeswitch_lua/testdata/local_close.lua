-- nil and false values are okay
local a<close> = nil
local b<close> = false

---
-- Values without __close metamethod are not, even if they get that method
-- before going out of scope.
local a<close> = 12 -- Error: value is not an object: integer

---
local b<close> = {} -- Error: variable 'b' has close attribute but is not closable

---
local mt = {__close = function() end}
local c<close> = {} -- Error: variable 'c' has close attribute but is not closable
setmetatable(c, mt)

---
-- Multiple close variables in the same statement are not allowed.
local a<close>, b<close> = nil, nil -- Error: multiple variables have 'close' attribute

---
-- Error is reported if __close metamethod is removed.
local mt = {__close = function() print("close") end}
local function make_a()
  local a = {}
  setmetatable(a, mt)
  return a
end
local a<close> = make_a()
setmetatable(a, nil)
-- Error: value is not an object: nil

---
-- Current __close method is called, even if it's not the one that the
-- table started with.
local mt1 = {__close = function() print("close1") end}
local mt2 = {__close = function() print("close2") end}
local function make_a()
  local a = {}
  setmetatable(a, mt1)
  return a
end
local a<close> = make_a()
setmetatable(a, mt2)
-- Output: close2

---
-- Variables closed in reverse order
local mt = {__close = function(self) print("close: s = " .. self.s) end}
local function make(s)
  local a = {s = s}
  setmetatable(a, mt)
  return a
end
local a<close> = make("a")
local b<close> = make("b")
-- Output: close: s = b
-- Output: close: s = a

---
-- Variable closed on goto out of block.
local mt = {__close = function(self) print("close: s = " .. self.s) end}
local function make(s)
  local a = {s = s}
  setmetatable(a, mt)
  return a
end
do
  local a<close> = make("a")
  goto out -- Output: close: s = a
  local b<close> = make("b")
end
::out::
print("out") -- Output: out

---
-- Variable closed on break
local mt = {__close = function(self) print("close: s = " .. self.s) end}
local function make(s)
  local a = {s = s}
  setmetatable(a, mt)
  return a
end
repeat
  local a<close> = make("a")
  break -- Output: close: s = a
  local b<close> = make("b")
until false

---
-- Variable closed on function end
local mt = {__close = function(self) print("close: s = " .. self.s) end}
local function make(s)
  local a = {s = s}
  setmetatable(a, mt)
  return a
end
local function f()
  local a<close> = make("a")
end
f() -- Output: close: s = a

---
-- Variable closed on function return
local mt = {__close = function(self) print("close: s = " .. self.s) end}
local function make(s)
  local a = {s = s}
  setmetatable(a, mt)
  return a
end
local function f()
  local a<close> = make("a")
  return
end
f() -- Output: close: s = a

---
-- Variable closed on error.
local mt = {__close = function(self) print("close: s = " .. self.s) end}
local function make(s)
  local a = {s = s}
  setmetatable(a, mt)
  return a
end
local function close_and_crash()
  local a<close> = make("a")
  error("crash")
end
local code = pcall(close_and_crash) -- Output: close: s = a
print(code) -- Output: false
