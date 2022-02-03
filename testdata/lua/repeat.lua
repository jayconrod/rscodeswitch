repeat
  print("a") -- Output: a
until true

local i = 0
repeat
  i = i + 1
  local j = -i
until j <= -3
print(i) -- Output: 3
