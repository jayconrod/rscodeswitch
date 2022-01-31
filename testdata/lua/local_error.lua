local const<const> = 12
const = 34 -- Error: attempt to assign to const variable 'const'

local close<close> = 12 -- Error: close is not implemented yet

local bogus<bogus> = 12 -- Error: unknown attribute: 'bogus'
