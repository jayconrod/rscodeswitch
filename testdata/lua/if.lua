if true then
  print("a") -- Output: a
end

if false then
  print("b")
end

if true then
  print("a") -- Output: a
else
  print("b")
end

if false then
  print("a")
else
  print("b") -- Output: b
end

if false then
  print("a")
elseif false then
  print("b")
elseif true then
  print("c") -- Output: c
end

if false then
  print("a")
elseif false then
  print("b")
else
  print("c") -- Output: c
end

if true then
  if false then
    print("a")
  else
    print("b") -- Output: b
  end
end
