from pdr import PDR
from z3 import *

x = BitVec('x', 8)
y = BitVec('y', 8)
z = Bool('z')
variables = [x,y,z]
primes = PDR.prime(variables)
primes[0] = BitVec('x\'', 8)
primes[1] = BitVec('y\'', 8)
xp, yp, zp = primes
pdr = PDR([x, y, z], primes,
    And(x == 0),
    Or(And(xp == x + 1, x < 15), xp == x),
    x < 16
    )
pdr.run()