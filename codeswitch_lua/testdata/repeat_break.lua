repeat
  print(1) -- Output: 1
  break
until false
print(2) -- Output: 2

repeat
  print(1) -- Output: 1
  repeat
    print(2) -- Output: 2
    break
  until false
  print(3) -- Output: 3
  break
until false
print(4) -- Output: 4
