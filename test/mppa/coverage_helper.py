import fileinput
import sys

all_loads_stores = "lbs lbz lhz lo lq ld lhs lws sb sd sh so sq sw".split(" ")

all_bconds = "wnez weqz wltz wgez wlez wgtz dnez deqz dltz dgez dlez dgtz".split(" ")

all_iconds = "ne eq lt ge le gt ltu geu leu gtu".split(" ")

all_fconds = "one ueq oeq une olt uge oge ult".split(" ")

replaces_a = [(["cb.", "cmoved."], all_bconds),
              (["compd.", "compw."], all_iconds),
              (["fcompd.", "fcompw."], all_fconds),
              (all_loads_stores, [".xs", ""])]

replaces_dd = [(["addx", "sbfx"], ["2d", "4d", "8d", "16d"])]
replaces_dw = [(["addx", "sbfx"], ["2w", "4w", "8w", "16w"])]

macros_binds = {"%a": replaces_a, "%dd": replaces_dd, "%dw": replaces_dw}

def expand_macro(fullinst, macro, replaceTable):
    inst = fullinst.replace(macro, "")
    for (searchlist, mods) in replaceTable:
        if inst in searchlist:
            return [fullinst.replace(macro, mod) for mod in mods]
    raise NameError

insts = []
for line in fileinput.input():
    fullinst = line[:-1]
    try:
        for macro in macros_binds:
            if macro in fullinst:
                insts.extend(expand_macro(fullinst, macro, macros_binds[macro]))
                break
        else:
            insts.append(fullinst)
    except NameError:
        print >> sys.stderr, fullinst + " could not be found any match for macro " + macro
        sys.exit(1)

for inst in insts:
    print inst
occurs = {}
