#!/usr/bin/env python3
"""Mutation matrix for the lineage regression harness.

Usage: mutation_matrix.py WORKDIR
WORKDIR must already contain the extracted checker (lineage_check_extracted.ml/.mli),
admissibility.ml, jurisdiction.ml and lineage_regression.ml, i.e. the output
directory of run_lineage_regression.sh.  Each mutant textually alters the
EXTRACTED checker, is compiled with the harness, and is run; the matrix records
which stage of the harness detects it.
"""
import re, subprocess, sys, os, shutil

W = sys.argv[1]
SRC = open(os.path.join(W, "lineage_check_extracted.ml")).read()

MUTANTS = [
  ("M1  drop the d_B descent test (L1)",
   lambda s: re.sub(r"let descends_b g =\n\s+mem g\.lin_dB \(ancestors g g\.lin_ground\)", "let descends_b g =\n  false", s)),
  ("M2  ignore dispositions (L2)",
   lambda s: s.replace("(negb (disposed_b g n))", "true", 1)),
  ("M3  count raw shared ancestors as undisclosed (L2)",
   lambda s: s.replace("(negb (mem n g.lin_raw))", "true", 1)),
  ("M4  source need not be claim-relevant (L3)",
   lambda s: s.replace("(mem n g.lin_relevant)", "true", 1)),
  ("M5  source may be an ancestor of d_A (L3)",
   lambda s: s.replace("(negb (mem n (ancestors g g.lin_dA)))", "true", 1)),
  ("M6  coverage gaps ignored (open becomes accepted)",
   lambda s: s.replace("| n :: l -> LineageOpen (n :: l))", "| n :: l -> LineageAccepted)", 1)),
  ("M7  skip relevance-is-raw check (WF)",
   lambda s: re.sub(r"let relevant_b g =\n(?:.*\n)*?\n", "let relevant_b _ = true\n\n", s, count=1)),
  ("M8  skip cycle detection (WF)",
   lambda s: re.sub(r"let cycle_at g =\n(?:.*\n)*?\n", "let cycle_at _ = None\n\n", s, count=1)),
  ("M9  skip distinguished-derived check (WF)",
   lambda s: re.sub(r"let distinguished_b g =\n(?:.*\n)*?\n", "let distinguished_b _ = true\n\n", s, count=1)),
  ("M10 skip declared-parents check (WF)",
   lambda s: re.sub(r"let declared_parents_b g =\n(?:.*\n)*?\n", "let declared_parents_b _ = true\n\n", s, count=1)),
  ("M11 ancestors: parents only (no saturation)",
   lambda s: s.replace("iter g (length (lin_nodes g)) (seed g n)", "seed g n", 1)),
  ("M12 ancestors: one saturation step only",
   lambda s: s.replace("iter g (length (lin_nodes g)) (seed g n)", "iter g 1 (seed g n)", 1)),
  ("M13 ancestors: two saturation steps only",
   lambda s: s.replace("iter g (length (lin_nodes g)) (seed g n)", "iter g 2 (seed g n)", 1)),
]

def run(name, mutate):
    d = os.path.join(W, "mut"); shutil.rmtree(d, ignore_errors=True); os.makedirs(d)
    for f in ("lineage_check_extracted.mli","admissibility.ml","jurisdiction.ml","lineage_regression.ml"):
        shutil.copy(os.path.join(W, f), d)
    m = mutate(SRC)
    if m == SRC: return name, "NOT APPLIED", None
    open(os.path.join(d, "lineage_check_extracted.ml"), "w").write(m)
    r = subprocess.run("ocamlfind ocamlc -package unix -linkpkg -w -a lineage_check_extracted.mli lineage_check_extracted.ml admissibility.ml jurisdiction.ml lineage_regression.ml -o mut",
                       shell=True, cwd=d, capture_output=True, text=True)
    if r.returncode: return name, "COMPILE ERROR: " + r.stderr[:200], None
    out = subprocess.run("./mut", shell=True, cwd=d, capture_output=True, text=True).stdout
    # which suites detect the mutant, and which populations
    suites = {"fixed": False, "random": False, "shallow": False, "deep": False}
    pops = []
    m1 = re.search(r"case study: (\d+)/(\d+) agree", out)
    if m1 and m1.group(1) != m1.group(2): suites["fixed"] = True
    m2 = re.search(r"random differential: (\d+)/(\d+) agree", out)
    if m2 and m2.group(1) != m2.group(2): suites["random"] = True
    for line in out.splitlines():
        m3 = re.match(r"(.+?)\s+n=\d+\s+intended-verdict (\d+)/(\d+)\s+handwritten-flags (\d+)/(\d+)", line)
        if m3 and (m3.group(2) != m3.group(3) or m3.group(4) != m3.group(5)):
            lab = m3.group(1).strip(); pops.append(lab)
            suites["deep" if lab.startswith("deep:") else "shallow"] = True
    return name, "detected" if any(suites.values()) else "UNDETECTED", (suites, pops)

rows = [run(n, f) for n, f in MUTANTS]
mark = lambda b: "x" if b else "."
print("| mutant | fixed | random | shallow strat. | deep strat. |")
print("|---|:-:|:-:|:-:|:-:|")
for n, v, info in rows:
    if info is None:
        print(f"| {n} | {v} | | | |"); continue
    su, _ = info
    print(f"| {n} | {mark(su['fixed'])} | {mark(su['random'])} | {mark(su['shallow'])} | {mark(su['deep'])} |")
print()
ok = [(n, i[0]) for n, v, i in rows if i is not None]
tot = len(rows)
def cnt(pred): return sum(1 for _, su in ok if pred(su))
print(f"total mutants: {tot}")
print(f"detected by the union of all suites: {cnt(lambda su: any(su.values()))}/{tot}")
print(f"detected by the stratified suite alone (shallow + deep): {cnt(lambda su: su['shallow'] or su['deep'])}/{tot}")
print(f"detected by shallow-stratified alone: {cnt(lambda su: su['shallow'])}/{tot}")
print(f"detected by deep-stratified alone: {cnt(lambda su: su['deep'])}/{tot}")
print(f"detected by random alone: {cnt(lambda su: su['random'])}/{tot}")
print(f"detected by fixed case study alone: {cnt(lambda su: su['fixed'])}/{tot}")
miss = [n for n, su in ok if not any(su.values())]
notrun = [n for n, v, i in rows if i is None]
if miss or notrun: print("NOT DETECTED:", miss, "NOT RUN:", notrun)
sys.exit(1 if (miss or notrun) else 0)
