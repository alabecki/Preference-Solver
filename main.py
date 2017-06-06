#
#		Naive Preferences Solver_____________________________________________________________________________________________________________________________
#
#	The program reads txt files composed of rules in the following format:
#		(b, h), where a and b are formulas of propositional logic
#		b is the "body" of the rule, while h is the "head"
#		"&" is used for "and", "|" is used for "or", and "~" is used for negation
#		Example: ( (~P | (~Q | R)), (Q & P) )
#
#		The program makes use of the SAT solver included in sympy, which requires mpath
#		It also utilizes the Symbol object, with which formulas are encoded for the purpose of using the SAT solver
#
#
#		Import Libraries_____________________________________________________________________________________________________________________________________
from sympy import Symbol
from sympy.abc import*
from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Not, And, Or
from sympy.logic.inference import satisfiable, valid
from mpmath import*
from itertools import product
import sys
from copy import deepcopy

import re
from preferences_core_functions import*
from preferences_query_functions import*
from preference_classes import*

evaluation_method = {
	"1": "By subset relationships in terms of rule violation \n",
	"2": "In terms of the cadinality of rule violations \n",
	"3": "In terms of the weighted cardinality of rule violations \n"
}


commands = {
	"1": "Show the set of most preferable  worlds",
	"2": "Compare two specific worlds with resepect to preference",
	"3": "Show which rules are violated at each world",
	"4": "Show the best worlds at which a formula is true",
	"5": "Determine whether, given R, the truth of 'a' makes 'b' obligatory (user povides a and b)",
	"6": "Determine whether, given R, the truth 'a' makes 'b' permissible (user provides a and b)",
	"7": "Determine whether, given our preferences, a further rule is implied (user provides new rule (a, b))",
	"8": "Add rule to R",
	"9": "Augment current rules with rules from an additional file",
	"10": "Additional Queries",
	"11": "I am done with this file"
}

debugging = {
	"1": "Show the world states at which a given rule is true",
	"2": "Show the world states at which a given rule is violated",
	"3": "Show which rules are false at a given world",
	"4": "Show which rules are verified  at a given world",
	"5": "Show which rules are neutral relative to a given world",
	"6": "Show set of domination relations between rules",
	"7": "Show the worst worlds",
	"8": "Show the body extension of a rule",
	"9": "Show the head extension of a rule",
	"10": "Print body of a rule",
	"11": "Print head of a rule",
	"12": "Show constraints",
	"13": "Show weights of rules"
}

#Main_____________________________________________________________________________________________________________________


print("__________________________________________________________________________\n")
print("Welcome to the Naive Preferences Solver\n")
print("___________________________________________________________________________\n")

while(True):
	do = ""
	print("What would you like to do? \n")
	while(do != "1" and do !="2"):
		do = input("(1) Open a file, (2), exit program\n")
		if(do == "2"):
			sys.exit()
		if(do == "1"):
			file = get_file()
		else:
			print("I'm sorry, could you repeat your command? \n")

	print("Processing rules____________________________________________________________ \n")

	propositions = obtain_atomic_formulas(file)

	file.seek(0)

	rules = construct_rules_dict(file)		#parces input text, make a Rule object for each rule, saves objects in dictionary
	file.seek(0)

	constraints = add_constraints(file)		#parces and saves contraints in a dictionary

	for k, v in rules.items():
		print(k, v.item)

	_worlds = construct_worlds(propositions)



	for k, v in constraints.items():
		print(k, v.item)

	worlds = reconstruct_worlds(propositions, constraints)

	print("Worlds after constraints: \n")
	#for w in worlds.values():
		#print(w.state)

	for k, rule in rules.items():
		rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
		rule.headExtension = assign_extensions(rule.head, worlds, propositions)

	domination_relations(rules)

	assign_rule_violations(worlds, rules)

	_continue = True

	while(True):

		print("________________________________________________________________________________ \n")
		print(" What would you like to know? \n")

		for k, v in commands.items():
			print("%s: %s \n" % (k, v))
		com = input()
		if(com == "1"):
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			method = input()
			if method == "1":
				best_worlds = best_worlds_by_subset(worlds)
			if method == "2":
				best_worlds = best_worlds_by_cardinality(worlds)
			if method == "3":
				best_worlds = best_worlds_by_weighted_cardinality(worlds)
			print(" The most preferred worlds are: \n")
			for k, v in best_worlds.items():
				print("%s: %s \n" % (k, v.state))
		elif(com == "2"):
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			method = input()
			print("Which two worlds would you like to compare? \n")
			for world in worlds.values():
				print("%s: %s \n" % (world.name, world.state))
			_pair = input("which two worlds would you like to compare? (write as: 'wi, wj', where i, j are integers) \n")
			pair = _pair.split(",")
			if method == "1":
				compare_worlds_by_subset(pair[0], pair[1], worlds)
			if method == "2":
				compare_worlds_by_cardinality(pair[0], pair[1], worlds)
			if method == "3":
				compare_worlds_by_weighted_cardinality(pair[0], pair[1], worlds)

		elif(com == "3"):
			print("The following worlds violate the following rules: \n")
			for world in worlds.values():
				print("%s %s: %s , %s\n" % (world.name, world.state, world.F, world.weightedF))

		elif(com == "4"):
			formula = input("Please write a formula to check \n")
			formula_ext = assign_extensions(formula, worlds, propositions)
			print("How would you like to evaulate the preference relationship between worlds? \n")
			for k, v in evaluation_method.items():
				print(k, v)
			method = input()
			if method == "1":
				formula_min = get_min_F_subset(formula_ext, worlds)
				for w in formula_min:
					print (w.name, w.state, w.F)
			if method == "2":
				formula_min = get_min_F_card(formula_ext, worlds)
				for w in formula_min:
					print (w.name, w.state, w.F)
			if method == "3":
				formula_min = get_min_F_weight(formula_ext, worlds)
				for w in formula_min:
					print (w.name, w.state, w.weightedF)

			print(" The most best %s-worlds are: \n" % (formula))
			for w in formula_min:
				print (w.name, w.state, w.F)

		elif(com == "5"):
			p = input("Please enter the first formula using &, ~, and | as operators \n")
			q = input("Please enter the second fomula using &, ~, and | as operators \n")
			current_num_proposition = len(propositions)
			propositions2 = deepcopy(propositions)
			add_proposition(propositions2, p)
			add_proposition(propositions2, q)

			if len(propositions2) == current_num_proposition:
				p_ext = assign_extensions(p, worlds, propositions)
				p_min = get_min_F(p_ext, worlds)
				q_ext = assign_extensions(q, worlds, propositions)
				b = obligation_implication(p_min, q_ext, worlds)
				if b == True:
					print("Given our preferences, %s obgliates %s \n" % (p, q))
				if b == False:
					print("Given our preferences, %s does not obligate %s \n" % (p, q))

			else:
				worlds_extended = reconstruct_worlds(propositions2, constraints)
				rules2 = deepcopy(rules)
				for k, rule in rules2.items():
					rule.bodyExtension = assign_extensions(rule.body, worlds_extended, propositions2)
					rule.headExtension = assign_extensions(rule.head, worlds_extended, propositions2)
				domination_relations(rules2)
				assign_rule_violations(worlds_extended, rules2)
				p_ext = assign_extensions(p, worlds_extended, propositions2)

				p_min = get_min_F(p_ext, worlds_extended)
				q_ext = assign_extensions(q, worlds_extended, propositions2)
				b = obligation_implication(p_min, q_ext, worlds_extended)
				if b == True:
					print("Given our preferences, %s obgliates %s \n" % (p, q))
				if b == False:
					print("Given our preferences, %s does not obligate %s \n" % (p, q))

		elif(com == "6"):
			p = input("Please enter the first formula using &, ~, and | as operators \n")
			q = input("Please enter the second fomula using &, ~, and | as operators \n")
			current_num_proposition = len(propositions)
			propositions2 = deepcopy(propositions)
			add_proposition(propositions2, p)
			add_proposition(propositions2, q)

			if len(propositions2) == current_num_proposition:
				p_ext = assign_extensions(p, worlds, propositions)
				p_min = get_min_F(p_ext, worlds)
				q_ext = assign_extensions(q, worlds, propositions)
				b = permissable_implication(p_min, q_ext, worlds)
				if b == True:
					print("Given our preferences, %s is permissable, given %s  \n" % (q, p))
				if b == False:
					print("Given our preferences, %s is not permissible, given %s \n" % (q, p))

			else:
				worlds_extended = reconstruct_worlds(propositions2, constraints)
				rules2 = deepcopy(rules)
				for k, rule in rules2.items():
					rule.bodyExtension = assign_extensions(rule.body, worlds_extended, propositions2)
					rule.headExtension = assign_extensions(rule.head, worlds_extended, propositions2)
				domination_relations(rules2)
				assign_rule_violations(worlds_extended, rules2)
				p_ext = assign_extensions(p, worlds, propositions)

				p_min = get_min_F(p_ext, worlds_extended)
				q_ext = assign_extensions(q, worlds_extended, propositions2)
				b = permissable_implication(p_min, q_ext, worlds_extended)
				if b == True:
					print("Given our preferences, %s is permissable, given %s  \n" % (q, p))
				if b == False:
					print("Given our preferences, %s is not permissible, given %s \n" % (q, p))


		elif(com == "7"):
			r = input("Please enter a new rule in the same format as in the txt. file \n")
			current_num_proposition = len(propositions)
			propositions2 = deepcopy(propositions)
			add_proposition(propositions2, r)
			if len(propositions2) == current_num_proposition:
				rules2 = deepcopy(rules)
				worlds2 = reconstruct_worlds(propositions, constraints)
				if implicit_rule(r, worlds, worlds2, propositions, rules2) == True:
					print("Yes, %s is implied by the other rules \n" % (r))
				else:
					print("No, %s is not implied by the other rules \n" % (r))
			else:
				worlds_extended = reconstruct_worlds(propositions2, constraints)
				worlds2 = reconstruct_worlds(propositions2, constraints)
				for k, rule in rules.items():
					rule.bodyExtension = assign_extensions(rule.body, worlds_extended, propositions2)
					rule.headExtension = assign_extensions(rule.head, worlds_extended, propositions2)
				assign_rule_violations(worlds_extended, rules, dominations)
				rules2 = deepcopy(rules)
				#if(len(propositions > current_num_proposition)):
				if implicit_rule(r, worlds_extended, worlds2, propositions2, rules2) == True:
					print("Yes, %s is implied by the other rules \n" % (r))
				else:
					print("No, %s is not implied by the other rules \n" % (r))

		elif(com == "8"):
			new_rule = input("Please input a new rule in the same format as used in the txt. file \n")
			add_proposition(propositions, new_rule)
			worlds = reconstruct_worlds(propositions, constraints)
			add_rule(new_rule, rules)
			for k, rule in rules.items():
				print(k, rule.item)
				rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
				rule.headExtension = assign_extensions(rule.head, worlds, propositions)
			domination_relations(rules)
			assign_rule_violations(worlds, rules)

		elif(com == "9"):
			new_file = get_file()
			new_propositions = obtain_atomic_formulas(new_file)
			propositions = propositions | new_propositions
			new_file.seek(0)
			add_rules_from_file(new_file, rules)
			new_file.seek(0)
			add_constraints_from_file(new_file, constraints)
			worlds = reconstruct_worlds(propositions,constraints)
			for k, rule in rules.items():
				rule.bodyExtension = assign_extensions(rule.body, worlds, propositions)
				rule.headExtension = assign_extensions(rule.head, worlds, propositions)
			domination_relations(rules)
			assign_rule_violations(worlds, rules)
			print("The new rules have been merged with the old ones \n")

		elif(com == "10"):
			com1 = " "
			_choices = list(range(1, 16))
			choices = ''.join(str(e) for e in _choices)
			while (str(com1) not in choices):
				for k, v in debugging.items():
					print("%s: %s \n" % (k, v))
				com1 = input()

				if com1 == "1":
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					result = find_rule_extension(_rule, rules, worlds)
					print("%s is true in the following worlds:\n" % (_rule))
					for w in result:
						print(w)

				elif(com1 == "2"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					result = find_rule_violations(_rule, rules, worlds)
					if (result) == {}:
						print("%s is not violated in any world" % (_rule))
					else:
						print("%s is violated in the following worlds:\n" % (_rule))
						for w in result:
							print("%s : %s \n" % (w.name, w.state))

				elif(com1 == "3"):
					print("The following worlds violate the following rules: \n")
					for world in worlds.values():
						print("%s %s: %s \n" % (world.name, world.state, world.F))

				elif(com1 == "4"):
					print("\n")
					for w in worlds.values():
						item = print_false_rules_at_w(w.name, rules, worlds)
						print(w.state, item)

				elif(com1 == "4"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_rules_true_at_w(_world, rules, worlds)
					print("The following rules are true in " + _world)
					print(result)

				elif(com1 == "5"):
					print("For which world would you like to make your query?")
					for world in worlds.values():
						print("%s: %s \n" % (world.name, world.state))
					print("For which world would you like to make your query? (type in name) \n")
					_world =check_world_input(worlds)
					result = print_rules_neutral_at_w(_world, rules, worlds)
					print("The following rules are neutral in " + _world)
					print(result)

				elif(com1 == "6"):
					print("The following domination relations obtain: \n" )
					for rule in rules.values():
						if (len(rule.dominatedBy) != 0):
							print("%s is dominated by: " % (rule.name))
							for dom in rule.dominatedBy:
								print(dom.name)

				elif(com1 == "7"):
					print("How would you like to evaulate the preference relationship between worlds? \n")
					for k, v in evaluation_method.items():
						print("The worst worlds are: \n")
						print(k, v)
					method = input()
					if method == "1":
						res = worst_worlds_by_subset(worlds)
						print("The worst worlds are: \n")
						for v in res.values():
							print("%s: %s \n" % (v.name, v.F))
					elif method == "2":
						res = worst_worlds_by_cardinality(worlds)
						print("The worst worlds are: \n")
						for v in res.values():
							print("%s: %s \n" % (v.name, v.F))
					elif method == "3":
						res = worst_worlds_by_weighted_cardinality(worlds)
						print("The worst worlds are: \n")
						for v in res.values():
							print("%s: %s \n" % (v.name, v.weightedF))

				elif(com1 == "8"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print("Body extension of %s is:  %s \n" % (rules[_rule].body, rules[_rule].bodyExtension))
				elif(com1 == "9"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print("Head extension of %s is:  %s \n" % (rules[_rule].head, rules[_rule].headExtension))

				elif(com1 == "10"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print(rules[_rule].body)
				elif(com1 == "11"):
					print("For which rule would you like to make your query? (type in name) \n")
					for k, rule in rules.items():
						print("%s: %s \n" % (k, rule.item))
					_rule =  check_rule_input(rules)
					print(rules[_rule].head)

				elif(com1 == "12"):
					for k, v in constraints:
						print(v.name, v.item)


				elif (com1 == "13"):
					for rule in rules.values():
						print("%s: %s - %s \n" % (rule.name, rule.item, rule.weight) )

				else:
					print("I'm sorry, you did not input a recognized command, please try again. \n")
		elif(com == "10"):
			file.close()
			break
		else:
			print("I'm sorry, you did not input a recognized command, please try again. \n")
		more = ""
		while(more != "y" and more != "n"):
			more = input("Would you like to make another query?  (y, n) \n")
		if(more == 'n'):
			break
