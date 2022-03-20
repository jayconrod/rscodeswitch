print(next({})) -- Output: nil

local t = {a = 1}
print(next(t)) -- Output: a 1
print(next(t, nil)) -- Output: a 1
print(next(t, "a")) -- Output: nil

local t = {[1] = "a"}
print(next(t)) -- Output: 1 a
print(next(t, nil)) -- Output: 1 a
print(next(t, 1)) -- Output: nil

local t = {}
for i = 1, 5 do
  t[i] = i
end
t["a"] = 100
t["b"] = 200
local sum = 0
local k, v = next(t)
while k ~= nil do
  sum = sum + v
  k, v = next(t, k)
end
print(sum) -- Output: 315

---
next(nil) -- Error: next: value is not an object: nil
---
local nan = 0.0 / 0.0
next({}, nan) -- Error: next: index is not a valid key
---
next({}, "a") -- Error: next: index is not a key in receiver
---
next({}, 1) -- Error: next: index is not a key in receiver
