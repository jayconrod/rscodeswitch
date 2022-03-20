local sum = 0
for i = 1, 3 do
  sum = sum + i
end
print(sum) -- Output: 6

sum = 0
for i = 1, 10, 2 do
  sum = sum + i
end
print(sum) -- Output: 25

sum = 0
for i = 0.5, 2 do
  sum = sum + i
end
print(sum) -- Output: 2

sum = 0
for i = 1, 2, 0.5 do
  sum = sum + i
end
print(sum) -- Output: 4.5

sum = 0
for i = 0.5, 2, 1.0 do
  sum = sum + i
end
print(sum) -- Output: 2

sum = 0
for i = 2, 0.5, -1.0 do
  sum = sum + i
end
print(sum) -- Output: 3
