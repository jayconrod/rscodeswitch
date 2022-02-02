goto a
print("do not print")
::a::
print("skipped") -- Output: skipped

do
  local x = 12
  goto outer
  print(x)
end
::outer::
print("outer") -- Output: outer
