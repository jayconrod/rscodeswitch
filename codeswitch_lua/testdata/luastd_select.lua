print(select(10, "a", "b", "c")) -- Output:
print(select(4, "a", "b", "c")) -- Output:
print(select(3, "a", "b", "c")) -- Output: c
print(select(2, "a", "b", "c")) -- Output: b c
print(select(1, "a", "b", "c")) -- Output: a b c

print(select(-1, "a", "b", "c")) -- Output: c
print(select(-2, "a", "b", "c")) -- Output: b c
print(select(-3, "a", "b", "c")) -- Output: a b c
print(select(-4, "a", "b", "c")) -- Output: a b c

print(select(1.5 * 2.0, "a", "b", "c")) -- Output: c
---
select(nil) -- Error: select: index argument must be "#" or integer
---
select(0.5) -- Error: select: could not convert value to integer
---
select(0) -- Error: select: index argument may not be zero
