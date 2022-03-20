local const<const> = 12
const = 34 -- Error: attempt to assign to const variable 'const'

local close<close> = nil
close = 12 -- Error: attempt to assign to const variable 'close'

local bogus<bogus> = 12 -- Error: unknown attribute: 'bogus'
