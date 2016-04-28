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

def counter_unsat():
    variables = [BitVec('x', 8)]
    x = variables[0]
    primes = [BitVec('x\'', 8)]
    xp = primes[0]
    verify_program("Counter (unsatisfiable)",
        variables, primes, And(x == 0), Or(And(xp == x + 1, x < 64), xp == x), x != 10)

def counter_sat():
    variables = [BitVec('x', 5)]
    x = variables[0]
    primes = [BitVec('x\'', 5)]
    xp = primes[0]
    verify_program("Counter (satisfiable)",
        variables, primes, And(x == 0), Or(And(xp == x + 1, x < 6), xp == x), x < 7)

def add_sub_unsat():
    variables = [BitVec('x', 6), BitVec('y', 6)]
    x, y = variables
    primes = [BitVec('x\'', 6), BitVec('y\'', 6)]
    xp, yp = primes
    init = And(x == 4, y == 3)
    trans = And(xp == x + y, yp == x - y)
    post = Not(x == 32)
    verify_program("Addition and subtraction (unsatisfiable)",
        variables, primes, init, trans, post)

def add_sub_sat():
    variables = [BitVec('x', 3), BitVec('y', 3)]
    x, y = variables
    primes = [BitVec('x\'', 3), BitVec('y\'', 3)]
    xp, yp = primes
    init = And(x == 4, y == 3)
    trans = And(xp == x + y, yp == x - y)
    post = Not(x == 2)
    verify_program("Addition and subtraction (satisfiable)",
        variables, primes, init, trans, post)

def shifter_sat():
    variables = generate_variables(4)
    primes = prime(variables)
    init = And(*[var == False for var in variables[1:]])
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = variables[-1] == False
    verify_program("Shifter (unsatisfiable), maintain MSB False",
        variables, primes, init, trans, post)

def shifter_unsat():
    variables = generate_variables(4)
    primes = prime(variables)
    init = variables[0] == True
    trans = And(*[primes[i] == variables[i - 1] for i in range(len(variables))])
    post = Or(*[var for var in variables])
    verify_program("Shifter (satisfiable), maintain at least one bit True",
        variables, primes, init, trans, post)

def run_all():
    [test() for test in tests[1:]]
tests = [run_all, counter_sat, counter_unsat, shifter_sat, shifter_unsat, add_sub_sat, add_sub_unsat]
if __name__ == "__main__":
    test_lookup = {test.__name__: test for test in tests}
    if len(sys.argv) != 2:
        print "Usage: python test_pdy.py [", ", ".join([test.__name__ for test in tests]), "]"
        exit()

    test_lookup[sys.argv[1]]()