from pdr import PDR
from z3 import *

def generate_variables(N): return [Bool(chr(ord('a') + i)) for i in range(N)]
def prime(variables): return [Bool(var.__str__() + '\'') for var in variables]

def verify_program(title, variables, primes, init, trans, post):
    print title
    print "---------------------------------------"
    print "Init:", init
    print "Trans:", trans
    print "Post:", post
    pdr = PDR(variables, primes, init, trans, post)
    sat, output = pdr.run()
    if sat:
        print "SAT:\n", output
    else:
        print "UNSAT:\n", output
    print
    print

def counter():
    variables = [BitVec('x', 8)]
    primes = [BitVec('x\'', 8)]
    verify_program("Counter example, value remains less than 10", variables, primes, And(x == 0), Or(And(xp == x + 1, x < 64), xp == x), x < 10)

def add_sub():
    variables = [BitVec('x', 5), BitVec('y', 5)]
    x, y = variables
    primes = [BitVec('x\'', 5), BitVec('y\'', 5)]
    xp, yp = primes
    init = And(x == 4, y == 3)
    trans = And(xp == x + y, yp == x - y)
    post = Not(x == 32)
    verify_program("Addition and subtraction", variables, primes, init, trans, post)

def shifter():
    variables = generate_variables(4)
    primes = prime(variables)
    init = And(*[var == False for var in variables[1:]])
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = variables[-1] == False
    verify_program("Shifter, maintain MSB False", variables, primes, init, trans, post)

def shifter_any_true():
    variables = generate_variables(4)
    primes = prime(variables)
    init = variables[0] == True
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = Or(*[var for var in variables])
    verify_program("Shifter, maintain at least one bit True", variables, primes, init, trans, post)

def run_all():
    [test() for test in tests[1:]]
tests = [run_all, counter, shifter, shifter_any_true, add_sub]
if __name__ == "__main__":
    test_lookup = {test.__name__: test for test in tests}
    if len(sys.argv) != 2:
        print "Usage: python test_pdy.py [", ", ".join([test.__name__ for test in tests]), "]"
        exit()

    test_lookup[sys.argv[1]]()