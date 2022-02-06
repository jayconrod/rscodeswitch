local function fac(n)
  local p = 1
  for i = 2, n do
    p = p * i
  end
  return p
end

print(fac(3)) -- Output: 6
