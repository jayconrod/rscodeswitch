local function printret(x)
  print(x)
  return x
end

print(1 and printret(2)) -- Output: 2
-- Output: 2
print(0 and printret(2)) -- Output: 2
-- Output: 2
print(nil and printret(2)) -- Output: nil
print(false and printret(2)) -- Output: false

print(1 or printret(2)) -- Output: 1
print(0 or printret(2)) -- Output: 0
print(false or printret(2)) -- Output: 2
-- Output: 2
print(nil or printret(2)) -- Output: 2
-- Output: 2
