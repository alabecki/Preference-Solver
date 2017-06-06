#Query Functions

from copy import deepcopy

#Since the F attribute of worlds is a set (the set of rules violated by a world) we can compare different worlds through
#set operations with respect to F
def compare_worlds_by_subset(u, v, worlds):
	v = v.lstrip()
	if (worlds[u].F >= worlds[v].F):
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		return
	elif worlds[v].F > worlds[u].F:
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		return
	else:
		print("%s and %s are not comparable in terms of preference \n" % (worlds[u].name, worlds[v].name))
		return

def compare_worlds_by_cardinality(u, v, worlds):
	v = v.lstrip()
	if (len(worlds[u].F) >= len(worlds[v].F)):
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		return
	elif len(worlds[v].F) >= len(worlds[u].F):
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		return

def compare_worlds_by_weighted_cardinality(u, v, worlds):
	v = vlstrip()
	if(worlds[u].weightedF <= worlds[v].weightedF):
		print(" %s is preferable to %s \n " % (worlds[u].name, worlds[v].name))
		return
	elif (worlds[v].weightedF <= worlds[u].weightedF):
		print("%s is preferable to %s \n" % (worlds[u].name, worlds[v].name))
		return


def get_rule_names(rules):
	result = []
	for k in rules.keys():
		result.append(k)
	return result

def get_world_names(worlds):
	result = []
	for w in worlds.values():
		result.append(w.name)
	return result

#Query function to fetch the worlds in which a rule is "true"
def find_rule_extension(rule_name, rules, worlds):
	result = []
	temp = rules[rule_name]
	for w in temp.bodyExtension:
		if w in temp.headExtension:
			result.append(w)
	return result

#Query function to fetch the worlds in which a rule is "false"
def find_rule_false(rule_name, rules, worlds):
	result = []
	temp = rules[rule_name]
	for w in temp.bodyExtension:
		if(w not in temp.headExtension):
			if w not in result:
				result.append(w)
	return result

#This is used in the rare case where we have a world state (from the extension of a Rule, and need to find the world
#object corresponding to that state
def get_world_from_state(_state, worlds):
	result = ''
#	print("State " + str(_state))
	for world in worlds.values():
		#print("World " + str(world.state))
		if world.state == _state:
	#		print("check")
			result = world.name
			return result

# The remaining functions are used for various queries that the user might make.
def find_rule_violations(rule_name, rules, worlds):
	result = []
	false = find_rule_false(rule_name, rules, worlds)
	for w in false:
		#world = worlds[w]
		world = get_world_from_state(w, worlds)
		#temp = int(world[1:])
		for r, rule in rules.items():
			a = (r, rule_name)
			if( (a not in worlds[world].dom) or (worlds[world].state not in rule.bodyExtension) ):
				if worlds[world] not in result:
					print(worlds[world].name)
					result.append(worlds[world])
	return result

def print_violations(world_name, worlds):
	result = []
	for d in worlds[world_name].F:
		result.append(d)
	return result

def print_false_rules_at_w(_world, rules, worlds):
	result = []
	for k, rule in rules.items():
		if(worlds[_world].state in rule.bodyExtension and worlds[_world].state not in rule.headExtension):
			result.append(rule.name)
	return result

def print_rules_true_at_w(_world, rules, worlds):
	result = []
	for k, rule in rules.items():
		if(worlds[_world].state in rule.bodyExtension and worlds[_world].state in rule.headExtension):
			result.append(rule.name)
	return result

def print_rules_neutral_at_w(_world, rules, worlds):
	result = []
	for k, rule in rules.items():
		if(worlds[_world].state not in rule.bodyExtension):
			result.append(rule.name)
	return result

def worst_worlds_by_subset(worlds):
	most_violated = deepcopy(worlds)
	for w1, world1 in worlds.items():
		for w2, world2 in worlds.items():
			if world2.F > world1.F:
				del most_violated[w1]
				break
	return most_violated

def worst_worlds_by_cardinality(worlds):
	most_violated = { }
	sorted_worlds = sorted(worlds.values(), key = lambda x: len(x.F), reverse = True)
	most = len(sorted_worlds[0].F)
	cont = True
	for i in sorted_worlds:
		print("World: %s, has F: %s \n" % (i.name, i.F))
		if( len(i.F) < most ):
			print("go\n")
			return most_violated
		else:
			print("Stay \n")
			most_violated[i.name] = i

def worst_worlds_by_weighted_cardinality(worlds):
	most_violated = { }
	sorted_worlds = sorted(worlds.values(), key = lambda x: x.weightedF, reverse = True)
	most = sorted_worlds[0].weightedF
	cont = True
	for w in sorted_worlds:
		print("World: %s, has F: %s \n" % (w.name, w.F))
		if w.weightedF < most:
			print("go\n")
			return most_violated
		else:
			print("Stay \n")
			most_violated[w.name] = w



def dom_of_r_in_w(_rule, _world, rules, worlds):
	result = []
	#_temp = re.findall(r'\d+', _world)
	#temp = int(_temp[0])
	for r, rule in rules.items():
		a = (r, _rule)
		if a in worlds[_world].dom:
            #print("Does this ever happen?")
			result.append(r)
	return result

def check_rule_input(rules):
	_rule = ""
	rule_names = get_rule_names(rules)
	while(_rule not in rule_names):
		_rule = input()
		if _rule not in rule_names:
			print("You did not enter a rule name, please try again\n")
	return _rule

def check_world_input(worlds):
	_world = ""
	world_names = get_world_names(worlds)
	while(_world not in world_names):
		_world = input()
		if(_world not in world_names):
			print("You did not enter a world name, please try again \n")
	return _world

def check_rule_world_pair_input(worlds, rules):
	while(True):
		pair = input()
		pair = re.sub(r"\s+", "", pair)
		while("," not in pair):
			print("There must be a comma between the rule and the world\n")
			pair = input()
			pair = re.sub(r"\s+", "", pair)
		pair = pair.split(",")
		rule_names = get_rule_names(rules)
		world_names = get_world_names(worlds)

		while(pair[0] not in rule_names or pair[1] not in world_names):
			print("pair: %s \n" % (pair))
			print("You did not enter a rule/world pair or did not enter it in the correct format (ri, wj), please try again \n")
			pair = input()
			pair = re.sub(r"\s+", "", pair)
			pair = pair.split(",")
			rule_names = get_rule_names(rules)
			world_names = get_world_names(worlds)

			if(pair[0] not in rule_names or pair[1] not in world_names):
				print("You did not enter a rule/world pair or did not enter it in the correct format (ri, wj), please try again \n")
		return pair
