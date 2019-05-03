#!/usr/bin/env python3
def bitmask(to, fr):
    bit_to = 1<<to
    return (bit_to | (bit_to - 1)) & ~((1<<fr)-1)

def bitmask2(to, fr):
    bit_to = 1<<to
    return bit_to + (bit_to - (1 << fr))

for stop in range(32):
    for start in range(stop+1):
        assert(bitmask(stop, start) == bitmask2(stop, start))
