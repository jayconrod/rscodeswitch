f = loadfile("testdata/lua/std_loadfile_ret.lua") -- Output: loadfile
print(f()) -- Output: 1 2
---
loadfile("testdata/lua/std_loadfile_err.lua") -- Error: testdata/lua/std_loadfile_err.lua:1.1-1.2: unrecognized character: '?'
