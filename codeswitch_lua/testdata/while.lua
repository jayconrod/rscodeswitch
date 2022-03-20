while false do print("nope") end

local i = 0
while i < 3 do
  i = i + 1
  local i = "nope"
end
print(i) -- Output: 3
