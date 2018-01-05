from pyparsing import ( ParseException, ParseSyntaxException,
						Literal, opAssoc, operatorPrecedence,Group, Keyword,
						ParserElement,delimitedList, Forward, Suppress,alphanums, alphas,
						Word)
import pyparsing as p
import copy,random
import cPickle as cp
import time

class KB(object):
	def __init__(self):
		self.sentences = []
		self.variables = {}
		self.instances = []
		self.sentenceids =[]
		self.instanceCounter = 0

	def addSentences(self,sentence):
		if hash(sentence) not in self.sentenceids:
			self.sentenceids.append(hash(sentence))
			self.sentences.append(sentence)

	def check(self,query):
		curr_sentence = []
		predicate_names = []
		for parsed_input in query:
			if parsed_input == '|':
				continue
			try:
				predicate = Predicates(parsed_input[1],list(parsed_input[2]),'~' == parsed_input[0])
				predicate_name = parsed_input[1]
			except:
				predicate = Predicates(parsed_input[0],list(parsed_input[1]),False)
				predicate_name = parsed_input[0]
			curr_sentence[predicate.name] =predicate
			predicate_names.append(predicate_name)
		newsentence = Sentence(curr_sentence,predicate_names)
		#print newsentence
		#print "Checked"
		#print hash(newsentence)
		if hash(newsentence) in self.sentenceids:
			return True
		else:
			return False


	def tell(self,sentence):
		curr_sentence = []
		predicate_names = []
		vars = {}
		for parsed_input in sentence:
			if parsed_input == '|':
				continue
			try:
				predicate = Predicates(parsed_input[1],list(parsed_input[2]),'~' == parsed_input[0])
				predicate_name = parsed_input[1]
				for arg in predicate.arguments:
					if arg.islower():
						if arg in vars:
							p = vars.get(arg)
							predicate.arguments[predicate.arguments.index(arg)] = p
						else:
							vars.setdefault(arg,"x"+str(self.instanceCounter))
							self.instanceCounter = self.instanceCounter + 1
							p = vars.get(arg)
							predicate.arguments[predicate.arguments.index(arg)] = p

			except:
				predicate = Predicates(parsed_input[0],list(parsed_input[1]),False)
				predicate_name = parsed_input[0]
				for arg in predicate.arguments:
					if arg.islower():
						if arg in vars:
							p = vars.get(arg)
							predicate.arguments[predicate.arguments.index(arg)] = p
						else:
							vars.setdefault(arg,"x"+str(self.instanceCounter))
							self.instanceCounter = self.instanceCounter + 1
							p = vars.get(arg)
							predicate.arguments[predicate.arguments.index(arg)] = p
			curr_sentence.append(predicate)
			predicate_names.append(predicate_name)
		newsentence = Sentence(curr_sentence,predicate_names)
		if hash(newsentence) not in self.sentenceids:
			self.sentenceids.append(hash(newsentence))
			self.sentences.append(newsentence)

	def add_query(self,query):
		curr_query = []
		predicate_names = []
		for parsed_input in query:
			if(len(parsed_input) == 3):
				predicate = Predicates(parsed_input[1],list(parsed_input[2]),'~' != parsed_input[0])
				predicate_name = parsed_input[1]
				predicate.literal = True
			else:
				predicate = Predicates(parsed_input[0],list(parsed_input[1]),True)
				predicate_name = parsed_input[0]
				predicate.literal = True
			curr_query.append(predicate)
			predicate_names.append(predicate_name)
		newsentence = Sentence(curr_query,predicate_names)
		self.sentenceids.append(hash(newsentence))
		self.sentences.append(newsentence)

	def printKB(self):
		for sentence in self.sentences:
			print sentence

	def resolve(self,x,y):
		unifier = {}
		found = False
		match = None
		pr = None
		if hash(x) == hash(y):
			return None
		for predicate in x.predicates:
			for pp in y.predicates:
				if pp.name == predicate.name and pp.negated != predicate.negated:
					match = pp
					unifier = self.unify(match,predicate,{})
					#print "Unifier is " + str(unifier)
					if(type(unifier) == bool and unifier == False):
						continue
					elif(type(unifier) == dict):
						dellist = []
						for k,v in unifier.iteritems():
							if v in predicate.arguments and v in match.arguments:
								dellist.append(k)
						for ele in dellist:
							del unifier[ele]
						if(len(unifier) > 0):
							unifications = unifier
							found = True
							pr = predicate
							match = pp
							break
						elif len(unifier) == 0:
							if predicate.name == match.name and predicate.literal == match.literal:
								if sorted(predicate.arguments) == sorted(match.arguments):
									if predicate.negated !=match.negated:
										found = True
										pr = predicate
										match = pp
										break
						else:
							continue
		newS = []
		newN = []
		sentence = None
		if type(unifier) == bool and unifier == False:
			return sentence
		if not found:
			return sentence
		else:
			tempx = cp.loads(cp.dumps(x,-1))#copy.deepcopy(x)
			tempy = cp.loads(cp.dumps(y,-1))#copy.deepcopy(y)
			temppr = cp.loads(cp.dumps(pr,-1))#copy.deepcopy(pr)
			tempmatch = cp.loads(cp.dumps(match,-1))#copy.deepcopy(match)
			for unikey in unifier:
				if unikey in temppr.arguments:
					temppr.arguments[temppr.arguments.index(unikey)] = unifications[unikey]
				if unikey in tempmatch.arguments:
					tempmatch.arguments[tempmatch.arguments.index(unikey)] = unifications[unikey]
			for pred in tempy.predicates:
				for unikey in unifier:
					if unikey in pred.arguments:
						pred.arguments[pred.arguments.index(unikey)] = unifications[unikey]
				pred.literal = True
				for arg in pred.arguments:
					if arg.islower():
						pred.literal =False

			for pred in tempx.predicates:
				for unikey in unifier:
					if unikey in pred.arguments:
						pred.arguments[pred.arguments.index(unikey)] = unifications[unikey]
				pred.literal = True
				for arg in pred.arguments:
					if arg.islower():
						pred.literal =False
			for pred in tempy.predicates:
				if pred.name == temppr.name and sorted(pred.arguments) == sorted(temppr.arguments) and pred.negated != temppr.negated:
					continue
				else:
					newS.append(pred)
					newN.append(pred.name)

			for pred in tempx.predicates:
				if pred.name == tempmatch.name and sorted(pred.arguments) == sorted(tempmatch.arguments) and pred.negated!= tempmatch.negated:
					continue
				else:
					newS.append(pred)
					newN.append(pred.name)
			sentence = Sentence(newS,newN)
			#sentence = self.clean(sentence)
#			print str(x) + " " + str(y) + "=  " + str(sentence)
			return sentence


	def unify_var(self,var,x,sub):
		if var in sub:
			return self.unify(sub.get(var),x,sub)
		elif x in sub:
			return self.unify(var,sub.get(x),sub)
		else:
			sub.setdefault(var,x)
			return sub

		# if type(failure) == dict:
		# 	if var not in failure:
		# 		failure[var] = x
		# 	else:
		# 		return failure
		# else:
		# 	failure = dict()
		# 	failure[var] = x
		# return failure


	def unify(self,x,y,failure):
		#print x
		#print y
		if failure == False:
			return False
		elif x == y:
			return failure
		elif type(x) == str and type(y) == str and x.islower():
			return self.unify_var(x,y,failure)
		elif type(y) == str and type(x) == str and y.islower():
			return self.unify_var(y,x,failure)
		elif type(x) == Predicates and type(y) == Predicates:
			return self.unify(x.arguments,y.arguments,self.unify(x.name,y.name,failure))
		elif type(x) == list and type(y) == list and len(x) > 0 and len(y) > 0:
			if x and y:
				return self.unify(x[1:],y[1:],self.unify(x[0],y[0],failure))
			return failure
		else:
			return False




class Sentence(object):
	def __init__(self,predicates,predicatenames):
		self.predicates = predicates
		self.predicatenames = predicatenames

	def __str__(self):
		x= "Sentence : "
		x = x +  str(self.predicatenames) + "\n"
		for val in self.predicates:
			x = x + str(val) + ""
		return x + "\n"

	def __hash__(self):
		return hash((cp.dumps(sorted(self.predicatenames)),cp.dumps(self.predicates)))


class Predicates(object):
	def __init__(self, predicatename, arguments,negated):
		self.negated = negated
		self.name = predicatename
		self.arguments = arguments
		self.literal = True
		for arg in arguments:
			if arg.islower():
				self.literal = False
				break

	def __str__(self):

		x =  "Predicate "
		if self.negated:
			x = x + "~"

		x = x + str(self.name) + "(" + str(self.arguments) + ")"

		return x


def ask(kB, query):
	start = time.time()
	#print "Query is " + str(query)
	newKB = cp.loads(cp.dumps(kB,-1))#copy.deepcopy(kB)
	newKB.add_query(query)
	count = 0
	while True:
		newSentences = []
		newids = []
		for i in range(0, len(newKB.sentences)):
			for j in range(i+1, len(newKB.sentences)):
				count = count+1
				x = newKB.sentences[i]
				y = newKB.sentences[j]
				z = newKB.resolve(x, y)
				if type(z) == Sentence and z is not None:
					if len(z.predicates) == 0:
						#print "MAtch returned null"
						#print len(newKB.sentences)
						return "TRUE"
					if hash(z) not in newids:
						newSentences.append(z)
						newids.append(hash(z))
					elapsed = (time.time()-start)
					#print elapsed
					#print len(newKB.sentences)
					if elapsed > 15:
						#print len(newKB.sentences)
						return "FALSE"
					else:
						continue
			#print count
		subset = True
		if len(newSentences) > 0:
			for s in newSentences:
				if hash(s) not in newKB.sentenceids:
					subset = False
					break
			if subset:
				"Subset condition satisfied"
				#print len(newKB.sentences)
				return "FALSE"
		elif len(newSentences) == 0:
			break
		for s in newSentences:
			#print "ADDED to KB - " + str(s)
			newKB.addSentences(s)
	#print len(newKB.sentences)
	return "FALSE"

#Defining all the sentence constructs
lb = Suppress("(")
rb = Suppress(")")
_or = Literal("|")
_not = Literal("~")
comma = Suppress(",")
space = Suppress(" ")
argument = p.Word(alphanums) | p.Word(alphanums.title())
arglist = lb + argument + p.ZeroOrMore(p.Optional(comma) + argument) + rb
predicate = p.Optional(_not) + p.Word(alphanums) + p.Group(arglist)
validsentence = p.Group(predicate) +p.ZeroOrMore(p.ZeroOrMore(space) + p.Optional(_or) +  p.ZeroOrMore(space) +  p.Group(predicate))



kB = KB()
with open("input.txt") as in_file:
	numqueries = int(in_file.readline().rstrip())
	queries = []
	for i in range(numqueries):
		s = in_file.readline().rstrip()
		s = validsentence.parseString(s)
		queries.append(s)
	numsentences = int(in_file.readline().rstrip())
	inputSentences = []
	for i in range(numsentences):
		s = in_file.readline().rstrip()
		#print s
		s = validsentence.parseString(s)
		inputSentences.append(s)
	for mysentence in inputSentences:
		kB.tell(mysentence)
	#print "KB Addition done"

answers = []
for query in queries:
	answer = ask(kB, query)
	#print answer
	answers.append(answer)
#print answers
with open("output.txt",'w+') as write_file:
	for answer in answers:
		write_file.write(str(answer) + '\r\n')
write_file.close()