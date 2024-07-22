import random
class Element:
    __slots__ = ("negated", "term")
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
        return True, {}
    for clause in clauses:
        if len(clause) == 0:
            return False, None
        if len(clause) == 1:
            one, = clause
            found, sofar = DPLL(simplify(clauses, one))
            if found:
                sofar[one.term] = not one.negated
            return found, sofar
    clause = clauses[0]
    base = next(iter(clause))
    first, sofar =  DPLL(simplify(clauses, base))
    if first:
        sofar[base.term] = not base.negated
        return True, sofar
    second, sofar = DPLL(simplify(clauses, base.negate()))
    if second:
        sofar[base.term] = base.negated
    return second, sofar
def makecset(clauses):
    if len(clauses) < 3:
        return [clauses]
    csets = []
    rvmap = {}
    for clause in clauses:
        guess = None
        for term in clause:
            term = term.term
            old = rvmap.get(term)
            if guess:
                if old:
                    for oldterm in old:
                        rvmap[oldterm] = guess
                        guess.add(oldterm)
                else:
                   guess.add(term)
            else:
                guess = old or {term}
            rvmap[term] = guess
            
    rv = {}
    for clause in clauses:
        entry = rvmap[next(iter(clause)).term]
        try:
            rv[tuple(entry)].append(clause)
        except KeyError:
            rv[tuple(entry)] = [clause]
    return list(rv.values())
def DPLL2(clauses, skip_cset=0):
    if not clauses:
        return True, {}
    for clause in clauses:
        if len(clause) == 0:
            return False, None
        if len(clause) == 1:
            one, = clause
            found, sofar = DPLL2(simplify(clauses, one), skip_cset-1)
            if found:
                sofar[one.term] = not one.negated
            return found, sofar
    if not skip_cset:
        cset = makecset(clauses)
        if len(cset) > 1:
            sofar = {}
            for subset in cset:
                found, foundmap = DPLL2(subset, 10)
                if not found:
                    return False, None
                sofar.update(foundmap)
            return True, foundmap
        skip_cset = 11
    clause = clauses[0]
    base = next(iter(clause))
    first, sofar =  DPLL2(simplify(clauses, base), skip_cset-1)
    if first:
        sofar[base.term] = not base.negated
        return True, sofar
    second, sofar = DPLL2(simplify(clauses, base.negate()), skip_cset-1)
    if second:
        sofar[base.term] = base.negated
    return second, sofar

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
            if randbool():
                new[i] = clause.negate()
        output.append(set(new))
    return output
def randbool():
    return random.randint(0, 1)
def satisfies(clause, terms):
    for var in clause:
        if var.term in terms and var.negated != terms[var.term]:
            return True
    return False
def satisfies_list(clauses, terms):
    return all(satisfies(clause, terms) for clause in clauses)
def walksat(clauses, p, limit):
    # Bootstrapping
    terms = {}
    for clause in clauses:
        for term in clause:
            if term.term not in terms:
                terms[term.term] = randbool()
    # Main loop
    for _ in range(limit):
        for clause in clauses:
            if not satisfies(clause, terms):
                break
        else:
            return terms
        if random.random() <= p:
            choice = random.choice(list(clause))
        else:
            choice = max(clause, key=lambda term:satisfied_choices(clauses, terms, term.term))
        choice = choice.term
        terms[choice] = not terms[choice]
def satisfied_choices(clauses, terms, alt):
    terms[alt] = not terms[alt]
    rv = len([clause for clause in clauses if satisfies(clause, terms)])
    terms[alt] = not terms[alt]
    return rv
