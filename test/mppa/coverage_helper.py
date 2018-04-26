import fileinput

occurs = {}

for line in fileinput.input():
    line_noc = line.replace('\n', '')
    if line_noc not in occurs:
        occurs[line_noc] = 0
    occurs[line_noc] += 1

# HACK: Removing all the instructions with "%a", replacing them with all their variations
# Also removing all instructions starting with '.'
pruned_occurs = dict(occurs)
for inst in occurs:
    if inst[0] == '.':
        del pruned_occurs[inst]
    if "%a" not in inst:
        continue
    inst_no_a = inst.replace(".%a", "")
    if inst_no_a in ("compw", "compd"):
        del pruned_occurs[inst]
        for mod in ("ne", "eq", "lt", "gt", "le", "ge", "ltu", "leu", "geu",
                    "gtu", "all", "any", "nall", "none"):
            pruned_occurs[inst_no_a + "." + mod] = 1
    elif inst_no_a in ("cb"):
        del pruned_occurs[inst]
        for mod in ("wnez", "weqz", "wltz", "wgez", "wlez", "wgtz", "deqz", "dnez",
                    "dltz", "dgez", "dlez", "dgtz"):
            pruned_occurs[inst_no_a + "." + mod] = 1
    else:
        assert False, "Found instruction with %a: " + inst
occurs = pruned_occurs

for inst in sorted(occurs):
    print inst
