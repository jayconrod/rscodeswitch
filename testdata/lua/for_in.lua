local function range_fn(state, control)
  print("range_fn", state, control)
  if control >= state then
    return nil, "end"
  else
    return control + 1, "ok"
  end
end

local function range(n)
  print("range", n)
  return range_fn, n, 0, nil
end

for a, b, c in range(3) do
  print("loop", a, b, c)
end
-- Output: range 3
-- Output: range_fn 3 0
-- Output: loop 1 ok nil
-- Output: range_fn 3 1
-- Output: loop 2 ok nil
-- Output: range_fn 3 2
-- Output: loop 3 ok nil
-- Output: range_fn 3 3
