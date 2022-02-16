print(".", assert(true)) -- Output: .
print(".", assert(true, "ok")) -- Output: .
---
assert(false) -- Error: <unknown>: assertion failed!
---
assert(false, "custom message") -- Error: <unknown>: custom message
