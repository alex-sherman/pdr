from z3 import *

class Cube(object):
    def __init__(self, model, variable_lookup, i = None):
        self.values = [variable_lookup[str(v)] == model[v] for v in model]
        self.i = i

    @property
    def cube(self):
        return And(*self.values)

    @property
    def not_cube(self):
        return Or(*[Not(value) for value in self.values])

    def __repr__(self):
        return "{" + ("" if self.i == None else str(self.i) + ": ") + str(self.cube) + "}"

class PDR(object):    
    def __init__(self, variables, primes, init, trans, post):
        self.variables = variables
        self.variable_dict = {str(v): v for v in self.variables}
        self.primes = primes
        self.vTOp = zip(variables, primes)
        self.init = init
        self.trans = trans
        self.post = post
        self.postPrime = substitute(post, self.vTOp)

        self.stack_frames = [init]
        self.stack_trace = []

    def getBadCube(self):
        s = Solver()
        s.add(And(Not(self.post), self.stack_frames[self.N]))
        if s.check() == sat:
            return Cube(s.model(), self.variable_dict, self.N)
        return None

    def newFrame(self):
        self.stack_frames.append(True)

    def isBlocked(self, cube):
        s = Solver()
        s.add(Not(And(self.stack_frames[cube.i], cube.cube)))
        return s.check() == unsat

    def solveRelative(self, cube):
        cubePrime = substitute(cube.cube, self.vTOp)
        s = Solver()
        s.add(self.stack_frames[cube.i - 1])
        s.add(self.trans)
        s.add(cubePrime)
        if s.check() == unsat:
            return None
        #print "Model:",s.model()
        return s.model()

    def blockCube(self, tcube):
        self.stack_trace.append(tcube)

        while len(self.stack_trace) > 0:
            cube = self.stack_trace[-1]
            assert(not self.isBlocked(cube))
            solution = self.solveRelative(cube)
            if solution == None:
                self.stack_trace.pop()
                for i in range(1, cube.i + 1):
                    self.stack_frames[i] = simplify(And(self.stack_frames[i], cube.not_cube))

            else:
                candidate = {v: solution[v] for v in solution if str(v) in self.variable_dict}
                candidateCube = Cube(candidate, self.variable_dict, cube.i - 1)
                self.stack_trace.append(candidateCube)
                if candidateCube.i == 0:
                    return False
        return True

    def run(self): 
        self.newFrame()
        while True:        
            cube = self.blockCube()
            if cube:
                if not self.conflict(cube):
                    return False, self.stack_trace
            else:
                check_frame = self.stack_frames[self.N - 1]
                s = Solver()
                s.add(And(self.trans, check_frame, 
                    Not(substitute(check_frame, self.vTOp))))
                invariant = s.check() == unsat
                if invariant:
                    return True, check_frame
                self.newFrame()

    @property
    def N(self):
        return len(self.stack_frames) - 1
    
