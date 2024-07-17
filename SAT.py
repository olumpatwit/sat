import random
class Element:
    def __init__(self, term, negated = False):
        self.negated = negated
        self.term = term
    def negate(self):
        return Element(self.term, not self.negated)
    def __repr__(self):
        return f"not({self.term})" if self.negated else self.term
    def __eq__(self, other):
        return self.term == other.term and self.negated == other.negated
    def __hash__(self):
        base = hash(self.term)
        return ~base if self.negate else base
def DPLL(clauses):
    if not clauses:
        return True
    for clause in clauses:
        if len(clause) == 0:
            return False
        if len(clause) == 1:
            one, = clause
            return DPLL(simplify(clauses, one))
    clause = clauses[0]
    base = next(iter(clause))
    return DPLL(simplify(clauses, base)) or \
           DPLL(simplify(clauses, base.negate()))
def simplify(clauses, assume):
    new = []
    remove = assume.negate()
    for clause in clauses:
        if assume not in clause:
            new.append(clause-{remove})
    return new
def generate_random_clause(k, m, n):
    poss = [Element(str(i)) for i in range(n)]
    output = []
    for _ in range(m):
        new = random.sample(poss, k)
        for i, clause in enumerate(new):
            if random.randrange(2):
                new[i] = clause.negate()
        output.append(set(new))
    return output
