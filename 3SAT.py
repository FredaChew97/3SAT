from random import sample, choice, shuffle
from itertools import product
from numpy import arange
from time import time


class SAT():
    # ======================================#
    # Methods function as:                  #
    # Basic Initialize                      #
    # Print Total variables and clauses     #
    # Set, Flip and Get Variable            #
    # ======================================#

    def __init__(self):
        # Initially generate an empty 3SAT with its instances
        self.variables = []  # Variables (Literal) Names:1,2,... as in  v1,v2,...
        self.clauses = []  # Clauses:  [1,2,-3]  as in v1 and v2 and NOT v3
        self.numV = 0  # Total number of variables
        self.numC = 0  # Total number of clauses
        self.config = []  # Current assignment value of the variables

    def __repr__(self):
        # To print out the current variables and clauses available in string form
        r = "SAT instance with " + str(self.numV) + " variables and " + str(self.numC) + " clauses: \n"
        for c in self.clauses:
            r += str(c) + "\n"
        return r

    # This area is for checking purpose
    # sat = SAT()
    # print(SAT.__repr__)
    # print(sat.__repr__)
    # print(sat.__repr__())

    def set_variable(self, variable, value):
        # To ensure the value is assigned to the variable
        # Is applied to greedy(non-exact method)
        self.config[abs(variable) - 1] = value

    def flip_variable(self, variable):
        # To flip the variable's value
        # Is applied to GRASP (non-exact method)
        self.config[abs(variable) - 1] = not self.config[abs(variable) - 1]

    def get_variable(self, variable):
        # To get the variable's assigned value
        # Is applied in clause method to return one value for the clause
        return self.config[abs(variable) - 1]

    # =========================================================================#
    # Evaluation methods include:                                              #
    # Create values (literals) for one clause, return the positive literal     #
    # Identify and return once the value is FALSE, else continue until the end #
    # Analyze and evaluate all available clauses                               #
    # Identify the unsatisfied clauses count and return in ratio form          #
    # =========================================================================#

    def clause_v(self, clause):
        # Return one clause value
        v1 = self.get_variable(clause[0])
        v2 = self.get_variable(clause[1])
        v3 = self.get_variable(clause[2])
        # If less than 0, negate to opposite boolean value, which is positive integer value
        if clause[0] < 0: v1 = not v1
        if clause[1] < 0: v2 = not v2
        if clause[2] < 0: v3 = not v3
        return (v1 or v2 or v3)

    def value(self):
        # To return False once the clause value is False.
        # Else it will continue to loop all clauses until ends and return True if no False value is found midway
        for c in self.clauses:
            if self.clause_v(c) == False:
                return False
        return True

    def full_value(self):
        # Analyze all clauses and stop once done
        # This is applied in Exhaustive Search(Exact Method) to evaluate all clauses
        val = True
        for c in self.clauses:
            val &= self.clause_v(c)
        return val

    def unsatisfied_ratio(self):
        # To identify the unsatisfied clauses counts and return in ratio form (count/self.numC)
        # This is applied in Greedy and GRASP (Non-Exact Method)
        count = 0
        for c in self.clauses:
            if self.clause_v(c) == False:
                count += 1
        return count / self.numC

    # ==========================================================#
    # Random Constructions and functions as:                    #
    # Generate three literals randomly per clause               #
    # Generate random 3SAT with user input of no.V and no.C     #
    # Random config as assignment of variables                  #
    # Generate random YES 3SAT as all the clauses r satisfiable #
    # ==========================================================#

    def random_c(self):
        # uses sample () and choice () to generate three literals for a clause
        # Three random variables in a clause
        # This is applied in random_inst and random_yes_inst
        c = sample(self.variables, 3)
        c[0] *= choice([-1, 1])
        c[1] *= choice([-1, 1])
        c[2] *= choice([-1, 1])
        return c

    def random_inst(self, numV, numC):
        # A random 3SAT with input of no.variables and no.clauses
        self.numV = numV
        self.variables = list(range(1, numV + 1))
        self.config = [False] * numV
        self.numC = numC
        self.clauses = []
        for c in range(numC):
            self.clauses.append(self.random_c())

        # return self
    # Exclude return self when done checking

    def random_config(self):
        # Assignment of variables
        # is design to be part of random_yes_inst(self,numV,numC) method
        self.config = [choice([True, False]) for numV in range(self.numV)]


    def random_yes_inst(self,numV, numC):
        # A random 'yes' 3SAT instance with numV variables and numC clauses as input
        # Random configuration is choose to be satisfied
        # Choose clauses that satisfy, means must at least one literal as positive per clause
        self.numV = numV
        self.variables = list(range(1, numV + 1))
        self.random_config()
        self.numC = numC
        self.clauses = []
        for numC in range(self.numC):
            c = self.random_c()  # contains (self.variables,3)
            while self.clause_v(c) == False:  # change c, which is the literals  until it becomes True
                c[choice([0, 1, 2])] *= -1  # thru flip terminals (negating)
            self.clauses.append(c)
        if self.value() != True:
            print("Error!")
        return self
        # Exclude self when done checking

# For checking purpose
# sat = SAT()
# print(sat.__init__())
# print(sat.__repr__())
# print(sat.random_inst(3,5))
# print(sat.random_yes_inst(10,5))

    # =============================================#
    # Exact Method Solution - Exhaustive Search    #
    # Non-Exact Method Solution - Greedy and GRASP #
    # =============================================#
    def exhaustive(self):
        # 3SAT problem is solve using exhaustive search
        # The search process will stop when a solution to the problem is found
        # The iteration of searching through possible Boolean variable assignments
        # Is thru for loop
        for self.config in product([True, False], repeat=self.numV):
            if self.value() == True:
                return True
        return False

    def full_exhaustive(self):
        # Full_exhaustive(self) method iterate all possible Boolean variable assignments
        #  Through for loop and the self decision will result in True if
        #  Self.config satisfied
        self.dcs = False
        for self.config in product([True, False], repeat=self.numV):
            self.dcs |= self.full_value()
        return self.dcs

    def greedy(self):
        # Greedy Search is used to find the variable tht appear most in clauses
        # the first nested for loop count the occurrence of literal(v) among clauses (c)
        # after the first nested for loop, the literals are sort in decreasing order based on the occurrence
        # the second for loop ensure all the literals (v) in the literal occur is set to TRUE
        # after the second for loop,it return unsatisfied ratio method
        literals_occur = [[i, 0] for i in range(-self.numV, self.numV + 1)]
        for c in self.clauses:
            for v in c:
                literals_occur[v + self.numV][1] += 1
        literals_occur.sort(key=lambda a: a[1])
        for v in literals_occur:
            self.set_variable(v[0], v[0] > 0)
        return self.unsatisfied_ratio()

    def rand_greedy(self, block_size=2):
        # randomize greedy algorithm is similar to greedy search algorithm
        # diff is where it randomize block by block through for loop
        # other steps are similar to greedy method itself
        literals_occur = [[i, 0] for i in range(-self.numV, self.numV + 1)]
        for c in self.clauses:
            for v in c:
                literals_occur[v + self.numV][1] += 1
        literals_occur.sort(key=lambda a: a[1])
        for i in range(0, len(literals_occur), block_size):
            tmp = literals_occur[i:i + block_size]
            shuffle(tmp)
            literals_occur[i:i + block_size] = tmp
        for v in literals_occur:
            self.set_variable(v[0], v[0] > 0)
        return self.unsatisfied_ratio()

    def GRASP(self, max_rep=100):
        # GRASP as non-exact method is a solving strategy known as the meta-heuristic
        # goal: find the optimal solution
        # in first for loop: terminate condition is 100 counts
        # the greedy cand will have random solution from ran_greedy method in block size in 2,3,4
        # after candidate solution is stored in greed_cand, focus on local search part
        # in nested for loop (first), change the literal v by applying flip.variable()
        # then compare with neighbour cand and if greed_cand is better than neighbour cand, replace the value
        # another flip variable is to try to change the next variable
        # if best is greater than greed_cand, replace the best value with greed_cand
        best = 1
        for i in range(max_rep):
            greed_cand = self.rand_greedy(choice([2, 3, 4]))  # random block_size from {2,3,4}
            best_v = 0
            for v in self.variables:
                self.flip_variable(v)  # try changing variable v
                neigh_cand = self.unsatisfied_ratio()
                if neigh_cand < greed_cand:
                    greed_cand = neigh_cand
                    best_v = v
                self.flip_variable(v)
            if greed_cand < best:
                best = greed_cand
        return best

    # ===================================================#
    # Average time Testing taken to run Exhaustive Search#
    # Quality Testing on  Greedy and GRASP               #
    # ===================================================#
# create a global variable for SAT()
# DO NOT COMMENT OUT CODE
sat = SAT()
show_n = []
show_tm = []

def Exact_Method_Test():
        # This method is used to test on the Effectiveness of the Exhaustive Search by increasing the numV and numC
        # The method will initially display the string "Exhaustive Search Result"
        # initial variables - mx_repeats, n , tm , tm1
        # the while loop statement is where it will continue to loop until result of tm1-tm is larger than 60
        # time() - time in second
        # for loop will loop in range of 100 instances
        # random_yes_inst (numVariable, numClauses)
        # run exhaustive method
        # print out average time result based on the input n (increasing)
        # show_n,show_tm are to show in graph later
        # increase value n to continue

        print("n\tExhaustive Search Results")
        # print("Tg 1: Ensure Exhaustive runs on input of v no. and cls no. and display the first runs average time")
        mx_repeats = 100
        n = 10
        # m = 10
        tm = tm1 = 0
        while tm1 - tm < 60:
            tm = time()
            for repeats in range(mx_repeats):
                # print(sat.random_yes_inst(n,2*n))  # variable , clauses
                sat.random_yes_inst(n,30)
                dcs = sat.exhaustive()
                # print(dcs)
            tm1 = time()
            # print(str("Average time based on 100 repeats") + "\t" + str((tm1 - tm) / mx_repeats))
            print(str(n) + "\t" + str((tm1 - tm) / mx_repeats))
            show_n.append(n)
            # print(str(m) + "\t" + str((tm1 - tm) / mx_repeats))
            # show_n.append(m)
            show_tm.append((tm1 - tm) / mx_repeats)
            n += 1
            # m += 1

# # create a global variable
sat = SAT()
show_rho = []
show_greedy = []
show_grasp = []

def Non_Exact_Method_Test():
        # test greedy search and GRASP
        # This method initially print out the average time used for Greedy and GRASP string
        # The maximum repeat for the for loop will be 100
        # the initial numV will be 10
        # the rho for the outer nested for loop also known as Pearson Correlation Coefficient
        # it will be calculated in numC/numV
        # So, the numC is the multiplication of rho and numV
        # then the first inner for loop will be loop for 100 times by adding up the quality for greedy and grasp
        # the second inner loop will take the average of 100 repeats and print out the result in rho and GRASP,Greedy
        # loop again until rho = 9
        print("rho\tGreedy\tGRASP")
        mx_repeats = 50
        numV = 10
        for rho in arange(1, 10, 1):
            numC = int(rho * numV)
            quality = [0] * 2
            for repeat in range(mx_repeats):
                sat.random_yes_inst(numV, numC)
                # print(sat.random_yes_inst(numV, numC))
                quality[0] += sat.greedy()
                quality[1] += sat.GRASP()
            for i in range(2): quality[i] = '{:1.4f}'.format(1 - quality[i] / mx_repeats)
            print(str(rho) + '\t' + "\t".join(quality))
            # print("\t".join(quality))
            show_rho.append(rho)
            show_greedy.append(quality[0])
            show_grasp.append(quality[1])

Non_Exact_Method_Test()

Exact_Method_Test()

