-- Named access and assignment
local a = {}
print(a.x) -- Output: nil
a.x = 1
print(a.x) -- Output: 1
print(a["x"]) -- Output: 1

-- Indexed access and assignment with symbol
local a = {}
a["x"] = 1
print(a["x"]) -- Output: 1
print(a.x) -- Output: 1

-- Indexed access and assignment with small integer
local a = {}
a[10] = 1
print(a[10]) -- Output: 1

-- Indexed access and assignment with float that is an integer
local a = {}
a[2.5 - 1.5] = 1
print(a[2.5 - 1.5]) -- Output: 1
print(a[1]) -- Output: 1

-- Indexed access and assignment with float
local a = {}
a[-1.5] = 1
print(a[-1.5]) -- Output: 1

-- Indexed access and assignment with infinity
local a = {}
a[1.0/0.0] = 1
print(a[1.0/0.0]) -- Output: 1

-- Indexed access and assignment with positive and negative zero
local a = {}
a[-0.0] = 1
print(a[0.0]) -- Output: 1
print(a[0]) -- Output: 1

-- Table construction with symbol
local a = {x = 1}
print(a.x) -- Output: 1
print(a["x"]) -- Output: 1

-- Table construction with symbol index
local a = {["x"] = 1}
print(a.x) -- Output: 1

-- Table construction with integer index
local a = {[10] = 1}
print(a[10]) -- Output: 1

-- Table construction with float index
local a = {[-1.5] = 1}
print(a[-1.5]) -- Output: 1

-- Table construction with implicit index
local a = {10, 20, 30}
print(a[1], a[2], a[3]) -- Output: 10 20 30

-- Mixed table construction
local a = {x = 10, ["y"] = 20, 30}
print(a.x, a.y, a[1]) -- Output: 10 20 30

-- Mixed table construction with semicolons
local a = {x = 10; ["y"] = 20; 30}
print(a.x, a.y, a[1]) -- Output: 10 20 30
local a = {x = 10, ["y"] = 20, 30;}
print(a.x, a.y, a[1]) -- Output: 10 20 30
