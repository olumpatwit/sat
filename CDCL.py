import sys
import random
from dataclasses import dataclass
from collections import defaultdict,deque
from SAT import *
import SAT
@dataclass
class Assignment:
    value: bool
    antecedent: list | None
    dl: int  # decision level
    
def build_bcp_map(clauses, terms = None):
    terms = terms or defaultdict(set)
    for clause in clauses:
        for term in clause:
            terms[term].add(frozenset(clause))
    return terms
def bcp(clausemap, assignments, base, dl):
    if not isinstance(base, list):
        assignments[base.term] = Assignment(not base.negated, None, dl)
    todo = deque([base])
    while todo:
        what = todo.popleft()
        if isinstance(what, list):
            clauses = what
        else:
            neg = what.negate()
            clauses = clausemap[neg]
        for clause in clauses:
            unseen = []
            for term in clause:
                if term.term in assignments:
                    if assignments[term.term].value == (not term.negated):
                        break
                    # Else we know it's false, carry on
                else:
                    unseen.append(term)
            else:
                if not unseen:
                    return (True, clause)
                elif len(unseen) == 1:
                    var, = unseen
                    assignments[var.term] = Assignment(not var.negated,
                                                       clause, dl)
                    todo.append(var)
    return False, None
def resolve_conflict(clause, assignments, dl):
    final_clause = set(clause)
    while True:
        poss = {term for term in final_clause if assignments[term.term].dl == dl}
        if len(poss) == 1:
            break
        for lit in final_clause:
            resolvent = assignments[lit.term].antecedent
            if resolvent:
                break
        final_clause.update(resolvent)
        final_clause.remove(lit)
        final_clause.remove(lit.negate())
    decision_levels = sorted({assignments[literal.term].dl for literal in final_clause})
    try:
        return decision_levels[-2], frozenset(final_clause)
    except IndexError:
        return 0, frozenset(final_clause)
def n(term):
    return e(term).negate()
def e(term):
    return Element(str(term))
backtracks = 0
def cdcl(clauses):
    global backtracks
    clausemap = build_bcp_map(clauses)
    assignments = {}
    dl = 0
    conflict, clause = bcp(clausemap, assignments, clauses, dl)
    if conflict:
        return False
    while True:
        try:
            guess = max((k for k in clausemap if k.term not in assignments),
                        key=lambda x:len(clausemap[x]))
        except ValueError:
            break
        dl += 1
        conflict, clause = bcp(clausemap, assignments, guess, dl)
        if not conflict:
            continue
        while True:
            if dl == 0:
                return False
            b, new_clause = resolve_conflict(clause, assignments, dl)
            build_bcp_map([new_clause],clausemap)
            for term in list(assignments):
                if assignments[term].dl > b:
                    del assignments[term]
            backtracks = backtracks + 1
            dl = b
            conflict, clause = bcp(clausemap, assignments, [new_clause], dl)
            if not conflict:
                break
    rv = {k:v.value for k,v in assignments.items()}
    assert satisfies_list(clauses, rv)
    return rv
if __name__ == "__main__":
    clauses = [{n(2),n(3),n(4),e(5)},{n(1),n(5),e(6)},{n(5),e(7)},
           {n(1),n(6),n(7)},{n(1),n(2),e(5)},{n(1),n(3),e(5)},
           {n(1),n(4),e(5)},{n(1),e(2),e(3),e(4),e(5),n(6)}]

    for x in range(10,500,10):
        clauses = generate_random_clause(3,x*4,x)
        import timeit
        print("---",x)
        print("cdcl", timeit.timeit("print(cdcl(clauses))","from __main__ import cdcl,clauses",number=1))
        print("cdcl" ,backtracks)
        if x < 125:
            print("dpll", timeit.timeit("DPLL2(clauses)","from __main__ import DPLL2,clauses",number=1))
            print("dpll", SAT.falsechecks)
        SAT.falsechecks = backtracks = 0
    cdcl([[n(1),n(0)],[e(1),e(0)]])
    print("Welcome to the new world")
    nn=230
    g = generate_random_clause(3,int(4*nn),nn)
    print(cdcl(g))
