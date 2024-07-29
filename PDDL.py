import copy
import sys
from functools import total_ordering
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
