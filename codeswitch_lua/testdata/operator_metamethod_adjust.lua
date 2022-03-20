-- Check that metamethod returns are adjusted to the correct length.

local function return0() end
local function return2() return 1, 2 end

local mt_return0 = {
  __add = return0,
  __sub = return0,
  __mul = return0,
  __div = return0,
  __mod = return0,
  __pow = return0,
  __unm = return0,
  __idiv = return0,
  __band = return0,
  __bor = return0,
  __bxor = return0,
  __bnot = return0,
  __shl = return0,
  __shr = return0,
  __eq = return0,
  __lt = return0,
  __le = return0,
  __concat = return0,
  __len = return0,
  __index = return0,
}

print("control", return2()) -- Output: control 1 2

local t0 = {}
setmetatable(t0, mt_return0)
print("add0", t0 + t0) -- Output: add0 nil
print("sub0", t0 - t0) -- Output: sub0 nil
print("mul0", t0 * t0) -- Output: mul0 nil
print("div0", t0 / t0) -- Output: div0 nil
print("mod0", t0 % t0) -- Output: mod0 nil
print("pow0", t0 ^ t0) -- Output: pow0 nil
print("unm0", -t0) -- Output: unm0 nil
print("idiv0", t0 // t0) -- Output: idiv0 nil
print("band0", t0 & t0) -- Output: band0 nil
print("bor0", t0 | t0) -- Output: bor0 nil
print("bxor0", t0 ~ t0) -- Output: bxor0 nil
print("bnot0", ~t0) -- Output: bnot0 nil
print("shl0", t0 << t0) -- Output: shl0 nil
print("shr0", t0 >> t0) -- Output: shr0 nil
print("eq0", t0 == t0) -- Output: eq0 nil
print("lt0", t0 < t0) -- Output: lt0 nil
print("le0", t0 <= t0) -- Output: le0 nil
print("concat0", t0 .. t0) -- Output: concat0 nil
print("len0", #t0) -- Output: len0 nil
print("index0", t0.x) -- Output: index0 nil

local mt_return2 = {
  __add = return2,
  __sub = return2,
  __mul = return2,
  __div = return2,
  __mod = return2,
  __pow = return2,
  __unm = return2,
  __idiv = return2,
  __band = return2,
  __bor = return2,
  __bxor = return2,
  __bnot = return2,
  __shl = return2,
  __shr = return2,
  __eq = return2,
  __lt = return2,
  __le = return2,
  __concat = return2,
  __len = return2,
  __index = return2,
}

local t2 = {}
setmetatable(t2, mt_return2)
print("add2", t2 + t2) -- Output: add2 1
print("sub2", t2 - t2) -- Output: sub2 1
print("mul2", t2 * t2) -- Output: mul2 1
print("div2", t2 / t2) -- Output: div2 1
print("mod2", t2 % t2) -- Output: mod2 1
print("pow2", t2 ^ t2) -- Output: pow2 1
print("unm2", -t2) -- Output: unm2 1
print("idiv2", t2 // t2) -- Output: idiv2 1
print("band2", t2 & t2) -- Output: band2 1
print("bor2", t2 | t2) -- Output: bor2 1
print("bxor2", t2 ~ t2) -- Output: bxor2 1
print("bnot2", ~t2) -- Output: bnot2 1
print("shl2", t2 << t2) -- Output: shl2 1
print("shr2", t2 >> t2) -- Output: shr2 1
print("eq2", t2 == t2) -- Output: eq2 1
print("lt2", t2 < t2) -- Output: lt2 1
print("le2", t2 <= t2) -- Output: le2 1
print("concat2", t2 .. t2) -- Output: concat2 1
print("len2", #t2) -- Output: len2 1
print("index2", t2.x) -- Output: index2 1
