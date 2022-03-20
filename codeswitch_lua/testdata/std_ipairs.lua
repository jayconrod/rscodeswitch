print(ipairs({})) -- Output: <function> <object> 0 nil
print(ipairs(nil)) -- Output: <function> nil 0 nil

for i, v in ipairs({}) do
  print("no")
end

local t = {[0] = 0, [1] = 10, [2] = 20, [3] = 30, [5] = 50}
for i, v in ipairs(t) do
  print(i, v)
end
-- Output: 1 10
-- Output: 2 20
-- Output: 3 30
