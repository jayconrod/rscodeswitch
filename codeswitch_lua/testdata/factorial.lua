local function fac_iter(n)
  local p = 1
  for i = 2, n do
    p = p * i
  end
  return p
end
print(fac_iter(5)) -- Output: 120

local function fac_rec(n)
  if n < 2 then
    return 1
  else
    return n * fac_rec(n - 1)
  end
end
print(fac_rec(5)) -- Output: 120
