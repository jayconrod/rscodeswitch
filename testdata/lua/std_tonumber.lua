tonumber() -- Error: tonumber: requires at least one argument
---
print(tonumber(nil)) -- Output: nil
print(tonumber(true)) -- Output: nil
print(tonumber({})) -- Output: nil
print(tonumber("bloop")) -- Output: nil
print(tonumber("\xFF")) -- Output: nil

print(tonumber(0)) -- Output: 0
print(tonumber(0.5)) -- Output: 0.5
print(tonumber(9223372036854775807)) -- Output: 9223372036854775807
print(tonumber(1.0/0.0)) -- Output: inf
print(tonumber(0.0/0.0)) -- Output: NaN

print(tonumber("1")) -- Output: 1
print(tonumber("0xA")) -- Output: 10
print(tonumber("-0xA")) -- Output: -10
print(tonumber(" 1")) -- Output: 1
print(tonumber("1 ")) -- Output: 1
print(tonumber("-1")) -- Output: -1
print(tonumber("+1")) -- Output: 1
print(tonumber("-1.5")) -- Output: -1.5
print(tonumber("-9223372036854775807")) -- Output: -9223372036854775807
print(tonumber("-9223372036854775808")) -- Output: -9223372036854775808
print(tonumber("-9223372036854775809")) -- Output: -9223372036854776000
---
tonumber(nil, 10) -- Error: tonumber: for first argument, expected string, got nil
---
tonumber(10, 10) -- Error: tonumber: for first argument, expected string, got integer
---
tonumber("10", "ten") -- Error: tonumber: base argument out of range
---
tonumber("10", -10) -- Error: tonumber: base argument out of range
---
print(tonumber(nil, nil)) -- Output: nil
print(tonumber("99", nil)) -- Output: 99

print(tonumber("100", 2)) -- Output: 4
print(tonumber("2", 2)) -- Output: nil
print(tonumber("7FFFFFFFFFFFFFFF", 16)) -- Output: 9223372036854775807
print(tonumber("-1", 10)) -- Output: -1
print(tonumber("+1", 10)) -- Output: 1
print(tonumber(" 1", 10)) -- Output: 1
print(tonumber("1 ", 10)) -- Output: 1

-- NOTE: The main Lua implementation parses the numbers below as negative
-- integers. Seems like a bug that they allow overflow?
print(tonumber("8000000000000000", 16)) -- Output: nil
print(tonumber("8000000000000001", 16)) -- Output: nil

print(tonumber("z", 36)) -- Output: 35
print(tonumber("Z", 36)) -- Output: 35

print(tonumber("0x1", 16)) -- Output: nil
print(tonumber("1.5", 10)) -- Output: nil
