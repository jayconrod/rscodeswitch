local a = {
  x = 12,
  get_x = function(self) return self.x end
}
print(a.get_x(a)) -- Output: 12
print(a:get_x()) -- Output: 12

local function print_get_a()
  print("once")
  return a
end
print(print_get_a():get_x()) -- Output: once
-- Output: 12
