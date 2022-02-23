-- Load from string
local src = [[print("a")
return 1, 2]]
local f = load(src)
local a, b = f() -- Output: a
print(a, b) -- Output: 1 2

-- Load from function
local lines = {[1] = "print(\"b\")\n", [2] = "return 3, 4"}
local function make_loader(lines)
  local i = 1
  return function()
    local line = lines[i]
    i = i + 1
    return line
  end
end
local f = load(make_loader(lines))
local a, b = f() -- Output: b
print(a, b) -- Output: 3 4

---
load(nil) -- Error: <unknown>: chunk argument must be a string or a function
---
load("?") -- Error: chunk:1.1-1.2: unrecognized character: '?'
