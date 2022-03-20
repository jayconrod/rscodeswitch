print((1)) -- Output: 1

print(not true) -- Output: false
print(not false) -- Output: true
print(not 1) -- Output: false
print(not "ok") -- Output: false

print(-1) -- Output: -1
print(-9223372036854775808) -- Output: -9223372036854776000
print(-1.5) -- Output: -1.5

print(~1) -- Output: -2
print(~1.0) -- Output: -2

print(2 ^ 0) -- Output: 1
print(2 ^ 1) -- Output: 2
print(2 ^ 4) -- Output: 16
print(4 ^ 0.5) -- Output: 2
print(4 ^ -1) -- Output: 0.25
print((-4) ^ 0.5) -- Output: NaN
print(-4 ^ 0.5) -- Output: -2

print(2 * 3) -- Output: 6

print(3 / 2) -- Output: 1.5
print(3 / 2.0) -- Output: 1.5
print(1 / 0) -- Output: inf

print(3.5 // 2.5) -- Output: 1.5

print(3.5 % 2.5) -- Output: 1

print(2 + 1) -- Output: 3

print(2 - 1) -- Output: 1
print(1 - 2) -- Output: -1

print("a" .. "b") -- Output: ab
print("a" .. 1) -- Output: a1
print(1 .. "a") -- Output: 1a

print(1 << 64) -- Output: 0
print(1 << 63) -- Output: -9223372036854775808
print(1 << 1) -- Output: 2
print(1 << 0) -- Output: 1
print(2 << -1) -- Output: 1
print(-1 << -63) -- Output: 1
print(-1 << -64) -- Output: 0

print(-1 >> 64) -- Output: 0
print(1 << 63 >> 63) -- Output: 1
print(-1 >> 63) -- Output: 1
print(2 >> 1) -- Output: 1
print(2 >> 0) -- Output: 2
print(2 >> -1) -- Output: 4
print(-1 >> -63) -- Output: -9223372036854775808
print(-1 >> -64) -- Output: 0

print(15 & 7) -- Output: 7
print(10 ~ 15) -- Output: 5
print(10 | 5) -- Output: 15

print(1 == 1) -- Output: true
print(1 == 1.0) -- Output: true
print(0 == -0) -- Output: true
print(0/0 == 0/0) -- Output: false
print(1 == "1") -- Output: false
print("a" == "a") -- Output: true
print("a" == "b") -- Output: false

print(1 ~= 1) -- Output: false
print(1 ~= 1.0) -- Output: false
print(0 ~= -0) -- Output: false
print(0/0 ~= 0/0) -- Output: true
print(1 ~= "1") -- Output: true
print("a" ~= "a") -- Output: false
print("a" ~= "b") -- Output: true
