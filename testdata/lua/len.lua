-- String length
print(#"") -- Output: 0
print(#"ab") -- Output: 2
print(#"☃") -- Output: 3

-- Table length
local a = {}
print(#a) -- Output: 0
a.x = 1
print(#a) -- Output: 0
a[0] = 1
print(#a) -- Output: 0
a[1] = 1
print(#a) -- Output: 1
a[3] = 1
print(#a) -- Output: 3
a[3] = nil
print(#a) -- Output: 1
a[3.0] = 1
print(#a) -- Output: 3
a[3.5 + 0.5] = 1
print(#a) -- Output: 4
a[0x7FFFFFFFFFFFFFFE] = 1
print(#a) -- Output: 9223372036854775806
a[0x7FFFFFFFFFFFFFFF] = 1
print(#a) -- Output: 9223372036854775806
