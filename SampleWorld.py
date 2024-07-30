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
        for i, row in enumerate(grid):
            for j, col in enumerate(row):
                at = f"At({i},{j},{t+1})"
                nothere = Element(at, True)
                for name, (ii, jj) in deltas.items():
                    iii, jjj = i+ii,j+jj
                    if 0 <= iii < len(grid) and 0 <= jjj < len(row):
                        # Either: you're not there, you don't do the move
                        # or you're where it takes you
                        new = f"At({iii},{jjj},{t+1})"
                        yield {nothere,
                               make_move(name, t, True),
                               Element(new)}
                    else:
                        # Impossible move - either your not there
                        # or you didn't do it
                        yield {nothere,
                               make_move(name,t,True)}
                # If there's something worth sampling, record that
                # otherwise no sampling here
                if (i, j) in samples:
                    yield {nothere,
                           make_move("Sample", t, True),
                           Element(f"Sampled({i},{j},{t+1})")}
                    # Any sample state survives
                    yield {Element(f"Sampled({i},{j},{t})",True),
                           Element(f"Sampled({i},{j},{t+1})")}
                else:
                    yield {nothere, make_move("Sample", t, True)}
        # End of for loop for each square
        onlyone = set(deltas.keys())
        onlyone.add("Sample")
        # You performed at least one action
        yield {make_move(x, t, False) for x in onlyone}
        # You did not perform more than one action
        for key in onlyone:
            exclude = {make_move(key, t, False)}
            exclude.update({make_move(key2, t, True)
                            for key2 in onlyone if key2 != key})
    # Start state
    yield {Element(f"At{start_pos[0],start_pos[1],0}")}
    # Goal states
    for square in samples:
        yield {Element(f"Sampled({i},{j},0)",True)}
        yield {Element(f"Sampled({i},{j},{times})")}
