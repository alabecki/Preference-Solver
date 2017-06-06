
from sympy import Symbol
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.inference import satisfiable, valid
from sympy.logic.boolalg import Not, And, Or
from mpmath import*

from itertools import product
from preference_classes import Rule
from preference_classes import World
from preference_classes import Constraint
from preferences_query_functions import*
import os
import re
from copy import deepcopy

#		Functions_______________________________________________________________________________________________________________________________________________

#Prompts user to enter the name if a file, if the file does not exist, it reiterates.

def get_file():
	while True:
		file_name = input("Please input the name of a text-file containing a set of rules \n")
		file_name = file_name + ".txt"
		if(os.path.exists(file_name)):
			_file = open(file_name, "r+")
			print("Name of file: %s \n" % (file_name))
			return _file
		else:
			print("The file you selected does not exist, please try again\n")
            #filename = input("Select the first/second/third file:")

# Scans the rule file for atomic formulas (letters). This is needed to construct the worlds
def obtain_atomic_formulas(file):
	propositions = set()
	for line in file:
		if line.startswith("(") or line.startswith("!"):
			prop_char = set()
			for char in line:
				#print(str(char))
				if(str(char).isalpha()):
					prop_char.add(str(char))
			for item in prop_char:
				new = Symbol(item)
				propositions.add(new)
	return propositions						#returns the set of propositions involved in the set of rules


# Parses each line of the rule file to create a a dictionary of rules, distinguishing the item, body and head. The key is the name of the rule
# while the value is the Rule object itself
def construct_rules_dict(file):
	lines = []
	for line in file:
		if line.startswith("("):
			#line.replace(" ", "")			#any line starting with a "(" is interpreted as a rule
			line = re.sub(r'\s+', '', line)
			print("Print line: %s" % (line))
			lines.append(line.strip())
	steps = []
	for line in lines:
		steps.append(re.split("->|\$", line))
			#i = re.sub(r'\s+', '', i)
	for step in steps:
		print("step: %s " % (step))
		#print("[0], [1] %s %s " % (step[0], step[1]))
		#if len(step[0]) > 1:
		step[0] = step[0][1:]
		#else:
			#step[0] = step[0].replace("()", " ")
			#step[0] = step[0][0:0]
		print(len(step))
		print (len(step[1]))
		step[1] = step[1][:-1]
		print("[0], [1] %s %s " % (step[0], step[1]))
	rules = {}
	count = 0
	for line in steps:
		name = "r" + str(count)
		if len(line) == 2:
			item = line[0] + " -> " + line[1]
			new = Rule(name, item, line[0], line[1])
		if len(line) == 3:
			print("Three...")
			item = line[0] + " -> " + line[1] +  " " + line[2]
			new = Rule(name, item, line[0], line[1], float(line[2]))
		rules.update({name: new})
		count += 1
	return rules



def add_rules_from_file(file, rules):
	lines = []
	for line in file:
		if line.startswith("("):				#any line starting with a "(" is interpreted as a rule
			lines.append(line.strip())
	temp1 = [line[1:] for line in lines]		#remove "(" at the beginning of the rule
	temp2 = [line[:-1] for line in temp1]		#remove the ")" at the end of the rule
	temp3 = [line.split("->") for line in temp2]
	count = len(rules.keys())										#used to assign each rule with a unique name
	for line in temp3:
		item = line[0] + "->" + line[1]				#stores the original rule
		name = "r" + str(count)						#gives each rule a unique name "r" plus an integer
		new = Rule(name, item, line[0], line[1])	#creates a new Rule object there line[0] and line[1] are the body and head
		rules.update({name: new})					#adds the new rule to the dictionary of rules
		count += 1


def add_rule(rule, rules):
	count = len(rules)
	temp1 = rule[1:]
	temp2 = temp1[:-1]
	temp3 = temp2.split("->")
	#print("New body: %s, new head: %s \n" % (temp3[0], temp3[1]))
	item = temp3[0] + "->" + temp3[1]
	name = "r" + str(count)
	new = Rule(name, item, temp3[0], temp3[1])
	rules.update({name: new})


def add_constraints(file):
	lines = []
	for line in file:
		if line.startswith("!"):
			lines.append(line.strip())
		#for line in lines:
	temp1 = [line[1:] for line in lines]		#remove "!(" at the beginning of the rule
	#temp2 = [line[:-1] for line in temp1]		#remove the ")" at the end of the rule
	constraints = {}
	count = 0
	for line in temp1:
		#print(temp1)
		name = "c" + str(count)
		new = Constraint(name, line)
		constraints.update({name: new})
		count += 1
	return constraints

def add_constraints_from_file(file, constraints):
	lines = []
	for line in file:
		if line.startswith("!"):
			lines.append(line.strip())
	temp1 = [line[1:] for line in lines]		#remove "!(" at the beginning of the rule
	#temp2 = [line[:-1] for line in temp1]		#remove the ")" at the end of the rule
	count = len(constraints )
	for line in temp1:
		name = "c" + str(count)
		new = Constraint(name, line)
		constraints.update({name: new})
		count += 1
	return constraints


# Uses the output of obtain_atomic_formulas first create a table of Boolean values corresponding to a world. It then constructs its "state" as a dictionary
# where the keys are propositions and the values are Booleans. The names and states are passed on as arguments to create a list of World objects.
def construct_worlds(propositions):
	num_worlds = list(range(2**len(propositions)))	#calculates number of rows in the table from which the worlds will be obtained
	world_names = ["w" + str(i) for i in num_worlds]	#creates a unique name for each world: "w" plus an integer
	n = len(propositions)								#number of propositions for table creation
	table = list(product([False, True], repeat=n))		#creation of a truth table
	worlds = {}											#initiates an empty list of worlds
	count = 0
	for row in table:
		state = dict(zip(propositions, row))
		name = world_names[count]			#each state is a dictionary associating a truth value with each propositional
		new = World(name, state)			#new world object is created with the name and state as attributes
		worlds[name] = new								#the new world is added to the list of worlds
		count +=1
	return worlds

# Assigns each rule head and rule body a set of possible worlds, namely those in which it is true
#Since a given rule body/head will typically not include all atomic propositions found within the rule-set, directly applying  a
# SAT solver on this formulas will not give us the worlds we are looking for, since each world should assign truth values to all
# propositions found in the rule-set. So given a body/head x, if P is a proposition found in the set of rules but not in x, then x will be
#augmented with &(P | ~P).

def assign_extensions(formula, worlds, propositions):
	extension = []
	if str(formula).isspace() or len(formula) == 0:			#if the formula is empty it will be treated as a toutology
		#print("Check Empty\n")
		for w in worlds.values():
			extension.append(w.state)
		return extension
	else:
		props_in_formula = set()		#store propositions found in the formula
		for char in str(formula):
			add = Symbol(char)
			props_in_formula.add(add)
		props_not_in_form = propositions.difference(props_in_formula)	#Determine which propositions are missing from the rule's body
		supplement = Symbol('')
		print(formula)
		form_cnf = to_cnf(formula)
		for p in props_not_in_form:
			supplement = Or(p, Not(p))							#Loop aguments (P | ~P) for each P not found in body
			form_cnf = And(form_cnf, supplement)
		#print("__form_cnf: %s \n" % (form_cnf))
		form_SAT = satisfiable(form_cnf, all_models = True)  #The sympy SAT solver is applied to the augmented formula
		form_SAT_list = list(form_SAT)				       #the ouput of satisfiable() is an itterator object so we turn it into a list
		if(len(form_SAT_list) == 1 and form_SAT_list[0] == False):		#check to handle inconsistencies
			extension = []
			return extension
		else:
			for state in form_SAT_list:		#We now turn each state in which the body is true into a dictionary so that
				new = {}						#they may be directly compared with each world state
				#if get_world_from_state(state, worlds) == None:
					#continue
				#else:
				for key, value in state.items():
					new[key] = value
					extension.append(new)
	return extension


# Now that that head/body of each rule is assigned a set of world states, we can determine the domination relation
#in each world in a straightforward manner in terms of the definition of the relation
def domination_relations(rules):
	print("Calculating Domination Relations___________________________________________________________________________________\n")
	dominations = set()
	for k1, r1 in rules.items():	#and compare each rule with each of the others
		for k2, r2 in rules.items():
				#The following simply applies the definition of rule domination to the extensions of the rules in each world
				#First check for "improper" domination
			#print(r1.body, r2.body)
			if not r1.body and not r2.body:
				#(str(r1.body).isspace() or str(r2.body).isspace() ):
				print("Check empty")
				continue
			#if str(r1.body).isspace():
			if not r1.body:
				continue
			elif not r2.body:
			#str(r2.body).isspace():
				r1h_cnf = to_cnf(r1.head)
				r2h_cnf = to_cnf(r2.head)
				temp3 = And(r1h_cnf, r2h_cnf )
				notbothheads = Not(temp3)
				if valid(notbothheads) == True:
					r2.dominatedBy.add(r1)
			#	print("Check if either one has empty body")
			else:
				print("r2 body: %s" % (r1.body))
				r1b_cnf = to_cnf(r1.body)
				print("r2 body: %s" % (r2.body))
				r2b_cnf = to_cnf(r2.body)
				r1h_cnf = to_cnf(r1.head)
				r2h_cnf = to_cnf(r2.head)
				temp1 = Not(r1.body)
				temp2 = Not(r2.body)
				r1b_r2b = Or(temp1, r2b_cnf)
				r2b_r1b = Or(temp2, r1b_cnf)
				temp3 = And(r1h_cnf, r2h_cnf )
				notbothheads = Not(temp3)
				#print("First: %s, %s \n" % (r1b_r2b, notbothheads) )
				if((valid(r1b_r2b) == True) and valid(notbothheads) == True):
					if(valid(r2b_r1b) == False or valid(notbothheads) == False):
						new = (r1.name, r2.name)
						dominations.add(new)
						if (r2.item != r1.item):
							r2.dominatedBy.add(r1)

# We use the extensions assigned to rules and the domination relations to determine which rules are violated in each world
def dom_dom_check(world, rule, flag):
	for dom in rule.dominatedBy:
		#print("Dominated by %s\n" % (dom.name
		if(world.state not in dom.bodyExtension):
			#print("In recursion: this dom %s is neutral \n" % (dom.name))
			continue
		else:
			#print("This dom %s is not neutral \n" % (dom.name))
			flag = flag + 1
			#print("%s overides.... \n" % (dom.name))
			#print("Flag in rec: %s \b" % (flag))
			dom_dom_check(world, dom, flag)
	#print("About to return from recursion")
	return flag


def assign_rule_violations(worlds, rules):
	print("Assigning rule violations ________________________________________________________________________________")
	for world in worlds.values():
		for k, rule in rules.items():
			#First check if the rule is False in the world under consideration
			if(world.state in rule.bodyExtension and world.state not in rule.headExtension):
			#Now make sure that, if the rule is dominated by any other rules in this world, then that other rule
			#is Neutral in this world.
				if len(rule.dominatedBy) == 0:
					world.F.add(k)
					world.weightedF += rule.weight
				else:
					flag = False
					for dom in rule.dominatedBy:
						if (world.state in dom.bodyExtension):
							flag = True
					if flag == False:
						world.F.add(k)
						world.weightedF += rule.weight


def assign_rule_violations_recursive(worlds, rules, dominations):
	print("Assigning rule violations ________________________________________________________________________________")
	for world in worlds.values():
		for k, rule in rules.items():
			#First check if the rule is False in the world under consideration
			if(world.state in rule.bodyExtension and world.state not in rule.headExtension):
			#Now make sure that, if the rule is dominated by any other rules in this world, then that other rule
			#is Neutral in this world.
				flag = 0
				for dom in rule.dominatedBy:
					if (world.state not in dom.bodyExtension):
						continue
					flag += 1
					#print("Flag before recusion %s \n" % (flag))
					flag = dom_dom_check(world, dom, flag)
					#print("Just got back from recusion and flag is %s \n" % (flag))
				if flag % 2 == 0:
					world.F.add(k)
					world.weightedF += rule.weight
				else:
					continue

# We use the violation set F to see which worlds are best. Given the set of F (rule violations) for each world w, w1 is a "best" world if
# and only if there is no world w2 such that w1.F is a proper subset of w2.F (proper subset is used because we want to # find those members that minimal according to the partial preorder defined in Definition 3.6)
def best_worlds_by_subset(worlds):
	best_worlds = {}
	for w1 in worlds.values():
		check = True
		for w2 in worlds.values():
			if w1.F > w2.F:
				check = False
		if check == True:
			best_worlds[w1.name] = w1
			#best_worlds.add(w1.name)
	return best_worlds

def best_worlds_by_cardinality(worlds):
	best_worlds = {}
	sorted_worlds = sorted(worlds.values(), key =lambda x: len(x.F))
	best = len(sorted_worlds[0].F)
	for i in sorted_worlds:
		if(len(i.F) > best):
			return best_worlds
		else:
			best_worlds[i.name] = i

def best_worlds_by_weighted_cardinality(worlds):
	best_worlds = {}
	sorted_worlds = sorted(worlds.values(), key =lambda x: x.weightedF)
	best = sorted_worlds[0].weightedF
	for w in sorted_worlds:
		print(w.weightedF)
		if w.weightedF > best:
			return best_worlds
		else:
			best_worlds[w.name] = w

def add_proposition(propositions, p):
	for char in p:
		if (str(char).isalpha()):
			propositions.add(Symbol(char))

def reconstruct_worlds(propositions, constraints):
	#worlds2 = deepcopy(worlds)
	_worlds2 = construct_worlds(propositions)
	for k, constraint in constraints.items():
		constraint.extension = assign_extensions(constraint.item, _worlds2, propositions)
	worlds2 = {}
	flag = True
	for w, world in _worlds2.items():
		flag = True
		for constraint in constraints.values():
		#	print("World: %s, constraint %s \n" % (world.state, constraint.item))
			if world.state not in constraint.extension:
				flag = False
		if flag == True:
			worlds2[w] = world
	return worlds2


def get_min_F_subset(f_ext, worlds):
	f_min = set()
	for e1 in f_ext:
		w1 = get_world_from_state(e1, worlds)
		f_min.add(worlds[w1])
		for e2 in f_ext:
			w2 = get_world_from_state(e2, worlds)
			if worlds[w2].F < worlds[w1].F:
				f_min.remove(worlds[w1])
				break
	return f_min

def get_min_F_weight(f_ext, worlds):
	f_min = set()
	best = 99999999
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if worlds[world].weightedF < best:
			best = worlds[world].weightedF
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if worlds[world].weightedF == best:
			f_min.add(worlds[world])
	return f_min

def get_min_F_card(f_ext, worlds):
	f_min = set()
	best = 99999999
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if len(worlds[world].F) < best:
			best = len(worlds[world].F)
	for w in f_ext:
		world = get_world_from_state(w, worlds)
		if len(worlds[world].F) == best:
			f_min.add(worlds[world])
	return f_min




def obligation_implication(f1_min, f2ext, worlds):
	Flag = True
	for w in f1_min:
		if w.state not in f2ext:
			Flag = False
			return False
	if Flag == True:
		return True
	else:
		return False

def permissable_implication(f1_min, f2ext, worlds):
	Flag = False
	for w in f1_min:
		if w.state in f2ext:
			Flag = True
			return True
	if Flag == True:
		return True
	else:
		return False


def implicit_rule(r, worlds, worlds2, propositions2, rules2):
	add_rule(r, rules2)
	for k, rule in rules2.items():
		rule.bodyExtension = assign_extensions(rule.body, worlds2, propositions2)
		rule.headExtension = assign_extensions(rule.head, worlds2, propositions2)
	domination_relations(rules2)
	assign_rule_violations(worlds2, rules2)

	flag = True
	for w2i, world2i in worlds2.items():
		for w2j, world2j in worlds2.items():
			if world2i.F < world2j.F:
				if worlds[w2i].F >= worlds[w2j].F:
					flag = False
					return flag
			elif world2i.F >= world2j.F:
				if worlds[w2i].F < worlds[w2j].F:
					flag = False
					return flag
	flag = True
	return flag

#def implicit_rule(r, best_worlds, rules2, worlds2, propositions2):
	#first add r as a new rule
	#add_rule(r, rules2)
	#for k, rule in rules2.items():
		#rule.bodyExtension = assign_extensions(rule.body, worlds2, propositions2)
#		rule.headExtension = assign_extensions(rule.head, worlds2, propositions2)
	#dominations2 = set()
	#domination_relations(rules2, dominations2)
	#assign_rule_violations(worlds2, rules2, dominations2)
	#new_best_worlds = find_best_world(worlds2)
	#print("New best worlds: \n")
	#for k, v in new_best_worlds.items():
	#	print("%s: %s \n" % (k, v.state))
	#print("Old best  worlds: \n")
	#for k, v in best_worlds.items():
	#	print("%s: %s \n" % (k, v.state))
	#old = set(best_worlds.keys())
	#new = set(new_best_worlds.keys())
	#if old == new:
	#	return True
	#else:
	#	return False
