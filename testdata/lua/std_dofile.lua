a, b = dofile("testdata/lua/std_dofile_ret.lua") -- Output: dofile
print(a, b) -- Output: 1 2
---
dofile("testdata/lua/std_dofile_err.lua") -- Error: testdata/lua/std_dofile_err.lua:1.1-1.2: unrecognized character: '?'
