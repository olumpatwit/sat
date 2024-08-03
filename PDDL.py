import copy
import sys
from functools import total_ordering
from collections import defaultdict
from CDCL import cdcl
from SAT import Element
def is_variable(x):
    return x.islower()
class Predicate:
    def __init__(self, func, args):
        self.func = func
        self.args = args
    def groundvar(self, old, new):
        new = tuple(new if arg == old else arg for arg in self.args)
        if new == self.args:
            return self
        else:
            return Predicate(self.func, new)
    def __eq__(self, other):
        return self.func == other.func and self.args == other.args
    def __hash__(self):
        return hash(self.func)^hash(self.args)
    def __repr__(self):
        args = ",".join(self.args)
        return f"{self.func}({args})"
    @staticmethod
    def parse(part):
        part = part.strip().rstrip(")")
        func, args = part.split("(")
        args = args.split(",")
        return Predicate(func, tuple(arg.strip() for arg in args))
    @staticmethod
    def parse_set(line):
        line = line.strip()
        # Split by close-paren since space is also in internal args
        return frozenset({Predicate.parse(subchunk) for subchunk in line.split(")") if subchunk})
    def __hash__(self):
        return hash((self.func, self.args))
    def tosat(self, time, neg=False):
        return Element(f"{self} ({time})", neg)
@total_ordering
class Action:
    def __init__(self, name, args, pre, preneg, delete, add):
        self.name = name
        self.args = args
        self.pre = pre
        self.preneg = preneg
        self.delete = delete
        self.add = add
    def grounded(self):
        return all(not is_variable(x) for x in self.args)
    def ground(self, new):
        newobj = copy.deepcopy(self)
        for var in self.args:
            if is_variable(var):
                old = var
                break
        else:
            raise RuntimeError("Attempt to ground action with no vars")
        newobj.args = [new if arg == old else arg for arg in newobj.args]
        for prop in ("pre","preneg","delete","add"):
            data = getattr(newobj, prop)
            data = frozenset({elem.groundvar(old, new) for elem in data})
            setattr(newobj, prop, data)
        if newobj.preneg&newobj.pre or newobj.add&newobj.delete:
            # Impossible action, ignore
            return None
        else:
            return newobj
    def __repr__(self):
        args = ",".join(self.args)
        return f"{self.name} {args}"
    __str__ = __repr__
    def applicable(self, known):
        return self.pre.issubset(known) and self.preneg.isdisjoint(known)
    @staticmethod
    def parse(chunk):
        tocreate = {}
        header, *params = chunk.splitlines()
        name, *args = header.split()
        for what, line in zip(("pre", "preneg", "del", "add"), params):
            assert line.startswith(what+":")
            line = line.replace(what + ":", "")
            tocreate[what] = Predicate.parse_set(line)
        # Avoid a clash with the Python del keyword
        tocreate["delete"] = tocreate.pop("del")
        return Action(name, args, **tocreate)
    def __lt__(self, other):
        return (self.name, self.args) < (other.name, other.args)
    def tosat(self, time, neg=False):
        return Element(f"A{time}({self})", neg)
def parse_world(data):
    data = "\n".join(line for line in data.splitlines()
                     if not line.startswith("#"))
    data = data.strip()
    chunks = data.split("\n\n")

    # First chunk is headers
    predicates, constants, _ignore = chunks.pop(0).splitlines()
    predicates = Predicate.parse_set(predicates.lstrip("predicates:"))
    constants = constants.lstrip("constants:").split()

    # Last chunk is goal
    initial, goal = chunks.pop().splitlines()
    initial = Predicate.parse_set(initial.lstrip("initial:"))
    goal = Predicate.parse_set(goal.lstrip("goal:"))

    # Other chunks are actions
    actions = [Action.parse(chunk) for chunk in chunks]
    return predicates, constants, actions, initial, goal
def ground_world(constants, actions):
    grounded = []
    ungrounded = []
    for action in actions:
        if action.grounded():
            grounded.append(action)
        else:
            ungrounded.append(action)
    while ungrounded:
        action = ungrounded.pop()
        for constant in constants:
            new = action.ground(constant)
            if new:
                if new.grounded():
                    grounded.append(new)
                else:
                    ungrounded.append(new)
    return grounded
def load_sat(file, times):
    return list(world_to_sat(parse_world(open(file,"r").read()),times))
def world_to_sat(world, times):
    predicates, constants, actions, initial, goal = world
    actions = ground_world(constants, actions)
    for t in range(times):
        addme = defaultdict(set)
        deleteme = defaultdict(set)
        interesting = set(initial)
        for action in actions:
            # Action prerequisite states
            # A1(TurnOn(switch)) -> off(switch, 0)
            # A -> b == ~A or B
            for pre in action.pre:
                interesting.add(pre)
                yield {action.tosat(t, True), pre.tosat(t)}
            for preneg in action.preneg:
                interesting.add(preneg)
                yield {action.tosat(t, True), preneg.tosat(t, True)}
            for add in action.add:
                interesting.add(add)
                addme[add].add(action)
                yield {action.tosat(t, True), add.tosat(t+1)}
            for delete in action.delete:
                yield {action.tosat(t, True), delete.tosat(t+1,True)}
                deleteme[delete].add(action)
            # Action exclusion states
            for action2 in actions:
                if id(action2) < id(action):
                    yield {action.tosat(t, True), action2.tosat(t, True)}
        # State propogation axioms
        for state in interesting:
            # Unless you performed an action that added a state it isn't added
            clause = {state.tosat(t+1, True),state.tosat(t)}
            for action in addme[state]:
                clause.add(action.tosat(t))
            yield clause
            # Unless you performed an action that deleted the state it isn't deleted
            clause = {state.tosat(t+1,False),state.tosat(t, True)}
            for action in deleteme[state]:
                clause.add(action.tosat(t))
            yield clause
    for state in goal:
        if state not in interesting:
            raise ValueError("Impossible goal state")
        yield {state.tosat(t+1)}
    for state in interesting:
        yield {state.tosat(0, not (state in initial))}
def actions(x):
    results = cdcl(x)
    if results:
        return sorted(k for k,v in cdcl(x).items() if k[0] == "A" and v)
    else:
        return results
