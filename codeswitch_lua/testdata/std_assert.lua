print(".", assert(true)) -- Output: .
print(".", assert(true, "ok")) -- Output: .
---
assert(false) -- Error: assertion failed!
---
assert(false, "custom message") -- Error: custom message
