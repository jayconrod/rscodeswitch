function maybe_crash(c)
  if c then
    error("crash")
  else
    print("ok")
    return 12
  end
end

local code, result = pcall(maybe_crash, false) -- Output: ok
print(code) -- Output: true
print(result) -- Output: 12

local code, err = pcall(maybe_crash, true)
print(code) -- Output: false
print(err) -- Output: testdata/lua/luastd_pcall.lua:3: maybe_crash: crash
