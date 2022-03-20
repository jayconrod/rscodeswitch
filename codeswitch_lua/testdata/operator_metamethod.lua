local function unwrap(v)
  if getmetatable(v) then
    return v.x
  else
    return v
  end
end

local mt = nil
mt = {
  __add = function(l, r)
    print("add", l, r)
    return unwrap(l) + unwrap(r)
  end,

  __sub = function(l, r)
    print("sub", l, r)
    return unwrap(l) - unwrap(r)
  end,

  __mul = function(l, r)
    print("mul", l, r)
    return unwrap(l) * unwrap(r)
  end,

  __div = function(l, r)
    print("div", l, r)
    return unwrap(l) / unwrap(r)
  end,

  __mod = function(l, r)
    print("mod", l, r)
    return unwrap(l) % unwrap(r)
  end,

  __pow = function(l, r)
    print("pow", l, r)
    return unwrap(l) ^ unwrap(r)
  end,

  __unm = function(n)
    print("unm", n)
    return -unwrap(n)
  end,

  __idiv = function(l, r)
    print("idiv", l, r)
    return unwrap(l) // unwrap(r)
  end,

  __band = function(l, r)
    print("band", l, r)
    return unwrap(l) & unwrap(r)
  end,

  __bor = function(l, r)
    print("bor", l, r)
    return unwrap(l) | unwrap(r)
  end,

  __bxor = function(l, r)
    print("bxor", l, r)
    return unwrap(l) ~ unwrap(r)
  end,

  __bnot = function(i)
    print("bnot", i)
    return ~unwrap(i)
  end,

  __shl = function(l, r)
    print("shl", l, r)
    return unwrap(l) << unwrap(r)
  end,

  __shr = function(l, r)
    print("shr", l, r)
    return unwrap(l) >> unwrap(r)
  end,

  __eq = function(l, r)
    print("eq", l, r)
    return unwrap(l) == unwrap(r)
  end,

  __lt = function(l, r)
    print("lt", l, r)
    return unwrap(l) < unwrap(r)
  end,

  __le = function(l, r)
    print("le", l, r)
    return unwrap(l) <= unwrap(r)
  end,

  __concat = function(l, r)
    print("concat", l, r)
    return unwrap(l) .. unwrap(r)
  end,

  __len = function(t)
    print("len", t)
    return #unwrap(t)
  end,

  __index = function(t, i)
    print("index", t, i)
    return mt[i]
  end,

  __newindex = function(t, i, v)
    print("newindex", t, i, v)
  end,

  __tostring = function(self) return tostring(self.x) end,
}

local function wrap(v)
  local t = {x = v}
  setmetatable(t, mt)
  return t
end

local mt_default = {
  __index = {x = "default"}
}

local a, b, x, y = wrap(1), wrap(2), 3, 4
local t = wrap {[1] = 1, [2] = 2}
local t_default = {}
setmetatable(t_default, mt_default)
local r = nil

r = a + b -- Output: add 1 2
print(r) -- Output: 3
r = a + y -- Output: add 1 4
r = x + b -- Output: add 3 2
r = x + y

r = a - b -- Output: sub 1 2
print(r) -- Output: -1
r = a - y -- Output: sub 1 4
r = x - b -- Output: sub 3 2
r = x - y

r = a * b -- Output: mul 1 2
print(r) -- Output: 2
r = a * y -- Output: mul 1 4
r = x * b -- Output: mul 3 2
r = x * y

r = a / b -- Output: div 1 2
print(r) -- Output: 0.5
r = a / y -- Output: div 1 4
r = x / b -- Output: div 3 2
r = x / y

r = a % b -- Output: mod 1 2
print(r) -- Output: 1
r = a % y -- Output: mod 1 4
r = x % b -- Output: mod 3 2
r = x % y

r = a ^ b -- Output: pow 1 2
print(r) -- Output: 1
r = a ^ y -- Output: pow 1 4
r = x ^ b -- Output: pow 3 2
r = x ^ y

r = -a -- Output: unm 1
print(r) -- Output: -1

r = a // b -- Output: idiv 1 2
print(r) -- Output: 0
r = a // y -- Output: idiv 1 4
r = x // b -- Output: idiv 3 2
r = x // y

r = a & b -- Output: band 1 2
print(r) -- Output: 0
r = a & y -- Output: band 1 4
r = x & b -- Output: band 3 2
r = x & y

r = a | b -- Output: bor 1 2
print(r) -- Output: 3
r = a | y -- Output: bor 1 4
r = x | b -- Output: bor 3 2
r = x | y

r = a ~ b -- Output: bxor 1 2
print(r) -- Output: 3
r = a ~ y -- Output: bxor 1 4
r = x ~ b -- Output: bxor 3 2
r = x ~ y

r = ~a -- Output: bnot 1
print(r) -- Output: -2

r = a << b -- Output: shl 1 2
print(r) -- Output: 4
r = a << y -- Output: shl 1 4
r = x << b -- Output: shl 3 2
r = x << y

r = a >> b -- Output: shr 1 2
print(r) -- Output: 0
r = a >> y -- Output: shr 1 4
r = x >> b -- Output: shr 3 2
r = x >> y

r = a .. b -- Output: concat 1 2
print(r) -- Output: 12
r = a .. y -- Output: concat 1 4
r = x .. b -- Output: concat 3 2
r = x .. y

r = #t -- Output: len <object>
print(r) -- Output: 2

r = a == b -- Output: eq 1 2
print(r) -- Output: false
r = a == y -- Output: eq 1 4
r = x == b -- Output: eq 3 2
r = x == y

r = a ~= b -- Output: eq 1 2
print(r) -- Output: true

r = a < b -- Output: lt 1 2
print(r) -- Output: true
r = a < y -- Output: lt 1 4
r = x < b -- Output: lt 3 2
r = x < y

r = a > b -- Output: lt 2 1
print(r) -- Output: false
r = a > y -- Output: lt 4 1
r = x > b -- Output: lt 2 3
r = x > y

r = a <= b -- Output: le 1 2
print(r) -- Output: true
r = a <= y -- Output: le 1 4
r = x <= b -- Output: le 3 2
r = x <= y

r = a >= b -- Output: le 2 1
print(r) -- Output: false
r = a >= y -- Output: le 4 1
r = x >= b -- Output: le 2 3
r = x >= y

r = t.__index -- Output: index <object> __index
print(r) -- Output: <function>
r = t_default.x
print(r) -- Output: default

t.missing = 99 -- Output: newindex <object> missing 99
