#		Classes_______________________________________________________________________________________________________________________________________________
# One class is used to store attributes of rules and one class is used to sture attributes of worlds (states).

class Rule(object):
	def __init__(self, _name, _item, _body, _head, weight = 1.0):
		self.name = _name							# Name of rule for purpose of retrieval (r1, r2, ...)
		self.item = _item							# Item is the actual rule itself
		self.body = _body							# The body of the rule
		self.head = _head							# The head of the rule

		self.bodyExtension = []						# the world states at which the body of the rule is True
													# each element of the form {A: True, B: False, .... }
		self.headExtension = []						# the worlds states at which the head of the rule is True
													# each element of the form {A: True, B: False, .... }
		self.dominatedBy = set()
		self.weight = weight

class World(object):
	def __init__ (self, _name, _state):
		self.name = _name							# Name of the world (w1, w2, ...)
		self.state = _state							# The State of the world in the form of {A: True, B: False, .... }
		self.F = set()								# The set of rules violated in the world
		self.dom = set()							# The set of domination relations between rules in the world
		self.weightedF = 0.0

class Constraint(object):
	def __init__ (self, name, item):
		self.name = name
		self.item = item
		self.extension = []
