local mt = {
  __call = function(a, b, ...)
    print("call", a, b, ...)
    return 1, 2, 3
  end
}
local t = {}
setmetatable(t, mt)

print(t("a", "b", "c"))
-- Output: call a b c
-- Output: 1 2 3
