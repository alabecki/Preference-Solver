import sympy.abc
#from sympy.logic.boolalg import Not, And, Or
from sympy import*
from sympy.logic.inference import satisfiable, valid
#from sympy.logic.boolalg import to_cnf
from mpmath import*
#import mpmath
from itertools import product
#import pprint
import re

#A, B, C, D, E, F, G, H, I, J, K, L, M, N = symbols("A, B, C, D, E, F, G, H, I, J, K, L, M, N")


string = "(b -> ~a|c)  $ 0.3"
split = re.split("-> | \$ ", string)

print (string)
print(split)

for p in split:
	print(p)
