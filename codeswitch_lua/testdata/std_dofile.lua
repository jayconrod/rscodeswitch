a, b = dofile("testdata/std_dofile_ret.lua") -- Output: dofile
print(a, b) -- Output: 1 2
---
dofile("testdata/std_dofile_err.lua") -- Error: testdata/std_dofile_err.lua:1.1-1.2: unrecognized character: '?'
