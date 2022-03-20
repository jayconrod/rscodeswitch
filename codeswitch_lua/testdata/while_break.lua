while true do
  print(1) -- Output: 1
  break
end
print(2) -- Output: 2

while true do
  print(1) -- Output: 1
  while true do
    print(2) -- Output: 2
    break
  end
  print(3) -- Output: 3
  break
end
print(4) -- Output: 4
