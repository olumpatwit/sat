from collections import defaultdict,deque
import random
from SAT import satisfies_list,Element,generate_random_clause
def build_bcp_map(clauses, terms = None):
    terms = terms or defaultdict(list)
    for clause in clauses:
        for term in clause:
            terms[term.term].append(clause)
    return terms
def bcp(clausemap, model, base, decid=0, valid_decids=(0,),
        implication_map=None):
    if implication_map is None:
        implication_map = {}
    todo = deque([base])
    if not isinstance(base, set):
        model[base] = (True,decid)
        model[base.negate()] = (False,decid)
    loop_counter = 0
    while todo:
        loop_counter += 1
        what = todo.popleft()
        if isinstance(what, set):
            clauses = [what]
        else:
            assert model[what][0]
            assert not model[what.negate()][0]
            assert model[what][1] in valid_decids
            assert model[what.negate()][1] in valid_decids
            clauses = clausemap[what.term]
        for clause in clauses:
            unseen = []
            for term in clause:
                if term in model and model[term][1] in valid_decids:
                    if model[term][0]:
                        break
                    # Else we know it's false, carry on
                else:
                    unseen.append(term)
            else:
                if len(unseen) == 1:
                    var, = unseen
                    model[var] = (True, decid)
                    model[var.negate()] = (False, decid)
                    implication_map[var] = clause
                    todo.append(var)
                if len(unseen) == 0:
                    return True, resolve_conflict(clause, implication_map)
        if loop_counter > 100:
            raise ValueError
    return False, implication_map
def resolve_conflict(clause, implication_map):
    seen = set()
    final_clause = set(clause)
    todo = final_clause
    possible = []
    while True:
        for resolvent in final_clause-seen:
            seen.add(resolvent)
            if resolvent.negate() in implication_map:
                possible.append(resolvent)
        if len(possible) > 1:
            resolvent = possible.pop()
            final_clause.update(implication_map[resolvent.negate()])
            final_clause.remove(resolvent)
            final_clause.remove(resolvent.negate())
        else:
            return final_clause
def n(term):
    return e(term).negate()
def e(term):
    return Element(str(term))
def cdcc(clauses):
    model = {}
    clausemap = build_bcp_map(clauses)
    for term in clausemap:
        model[e(term)] = False,-9999
        model[n(term)] = False,-9999
    decid = -1
    valid_decids = []
    impmaps = []
    conflict = False
    guess = 3
    while True:
        if conflict:
            conflict, other = bcp(clausemap, model, new_clause,
                                  best_decid, valid_decids,
                                  impmaps[best_decid])
        else:
            decid = decid + 1
            valid_decids.append(decid)
            del guess
            try:
                guess = random.choice([var for var in clausemap
                                       if model[e(var)][1] not in valid_decids])
            except (IndexError,ValueError):
                dct = {k.term:v[0] for k, v in model.items() if v[1] in valid_decids
                        and not k.negated}
                return dct
            guess = random.choice([e,n])(guess)
            conflict, other = bcp(clausemap, model, guess, decid, valid_decids)
        if conflict:
            new_clause = other
            build_bcp_map([new_clause], clausemap)
            best_decid = -9999
            for term in new_clause:
                if model[term][1] != decid and model[term][1] in valid_decids:
                    best_decid = max(best_decid, model[term][1])
            if best_decid == -9999:
                return False
            valid_decids = [x for x in valid_decids if x <= best_decid]
        else:
            impmaps.append(other)
clauses = [{n(2),n(3),n(4),e(5)},{n(1),n(5),e(6)},{n(5),e(7)},
           {n(1),n(6),n(7)},{n(1),n(2),e(5)},{n(1),n(3),e(5)},
           {n(1),n(4),e(5)},{n(1),e(2),e(3),e(4),e(5),n(6)}]
c = cdcc(clauses)
assert satisfies_list(clauses, c)
print(c)
