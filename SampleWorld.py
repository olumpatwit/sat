import math
import sys
from queue import PriorityQueue
from SAT import Element
from CDCL import cdcl
def read_world(file):
    num_cols = int(file.readline())
    num_rows = int(file.readline())
    grid = []
    start_pos = None
    samples = []
    for row_idx in range(num_rows):
        row = file.readline().strip()
        start_idx = row.find("@")
        # Find the start
        if start_idx >= 0:
            start_pos = row_idx, start_idx
        sample_idx = -1
        # Find the samples to add
        while (sample_idx := row.find("*", sample_idx+1)) >= 0:
            samples.append((row_idx, sample_idx))
        grid.append(row)
    return tuple(grid), (start_pos, frozenset(samples))
def make_move(name, time, negated):
    return Element(f"{name}({time})", negated)
def world_to_sat(world, times):
    grid, (start_pos, samples) = world
    deltas = {"Up":(-1,0),"Down":(1,0),"Left":(0,-1),"Right":(0,1),}
    for t in range(times):
        saw = set()
        for i, row in enumerate(grid):
            for j, col in enumerate(row):
                at = f"At({i},{j},{t})"
                nothere = Element(at, True)
                here = Element(at)
                for name, (ii, jj) in deltas.items():
                    iii, jjj = i+ii,j+jj
                    if 0 <= iii < len(grid) and 0 <= jjj < len(row):
                        # Set MovedDownTo(x,y,t) if and only if
                        # you moved down to x,y,t
                        new = f"Moved{name}To({iii},{jjj},{t+1})"
                        yield {nothere,
                               make_move(name, t, True),
                               Element(new)}
                        yield {Element(new, True),
                               here}
                        yield {Element(new, True),
                               make_move(name, t, False)}
                    else:
                        # Impossible move - either your not there
                        # or you didn't do it
                        yield {nothere,
                               make_move(name,t,True)}
                # If there's something worth sampling, record that
                # otherwise no sampling here
                if (i, j) in samples:
                    # SampledNow(...) is set if and only
                    # if you sampled there now
                    yield {nothere,
                           make_move("Sample", t, True),
                           Element(f"SampledNow({i},{j},{t})")}
                    yield {here,
                           Element(f"SampledNow({i},{j},{t})",True)}
                    yield {make_move("Sample", t, False),
                           Element(f"SampledNow({i},{j},{t})",True)}
                    # Sampled(..., t+1) = Sampled(...,t) or SampledNow(...,t)
                    yield {Element(f"Sampled({i},{j},{t})",True),
                           Element(f"Sampled({i},{j},{t+1})")}
                    yield {Element(f"SampledNow({i},{j},{t})",True),
                           Element(f"Sampled({i},{j},{t+1})")}
                    yield {Element(f"Sampled({i},{j},{t})"),
                           Element(f"SampledNow({i},{j},{t})"),
                           Element(f"Sampled({i},{j},{t+1})",True)}
                else:
                    yield {nothere, make_move("Sample", t, True)}
                    yield {Element(f"SampledNow({i},{j},{t})", True)}

                # Now assert you didn't teleport or walk onto a wall
                if grid[i][j] == "#":
                    yield {nothere}
                elif t == 0:
                    if (i, j) != start_pos:
                        yield {nothere}
                else:
                    todo = {nothere}
                    for name in deltas:
                        todo.add(Element(f"Moved{name}To({i},{j},{t})"))
                    todo.add(Element(f"SampledNow({i},{j},{t-1})"))
                    yield todo
                    # The SAT solver isn't forced to assume an At(...)
                    # for any time, but if it doesn't it can't get anywhere
                    # hopefully
        # End of for loop for each square
        # Assert you didn't move from a wall
        for i in range(len(grid[0])):
            yield {Element(f"MovedDownTo(0,{i},{t})",True)}
            yield {Element(f"MovedUpTo({len(grid)-1},{i},{t})",True)}
        for j in range(len(grid)):
            yield {Element(f"MovedRightTo({j},0,{t})",True)}
            yield {Element(f"MovedLeftTo({j},{len(grid[0])-1},{t})",True)}
        onlyone = set(deltas.keys())
        onlyone.add("Sample")
        # You performed at least one action
        yield {make_move(x, t, False) for x in onlyone}
        # You did not perform more than one action
        for key in onlyone:
            for key2 in onlyone:
                if key < key2:
                    yield {make_move(key, t, True),
                           make_move(key2, t, True)}
    # Start state
    yield {Element(f"At({start_pos[0]},{start_pos[1]},0)")}
    # Goal states
    for i, j in samples:
        yield {Element(f"Sampled({i},{j},0)",True)}
        yield {Element(f"Sampled({i},{j},{times})")}
def load_world(path, times):
    return list(world_to_sat(read_world(open(path,"r")),times))
def actions(world):
    solved = cdcl(world)
    if not solved:
        return False
    def key(clause):
        if "," in clause:
            return int(clause[clause.rindex(","):-1])
        else:
            return int(clause[clause.index("(")+1:-1])
    return sorted((k for k in solved if solved[k] and k[:2] != "At"
                  and k[:5] != "Moved" 
                  and k[:k.index("(")] not in ("SampledNow","Sampled")),
                  key=key)
