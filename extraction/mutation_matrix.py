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
  ("M14 omit ground != d_A (L1)",
   lambda s: re.sub(
       r"let ground_eq_a g =\n\s+\(=\) g\.lin_ground g\.lin_dA",
       "let ground_eq_a _ =\n  false",
       s,
       count=1)),

  ("M15 omit ground != d_B (L1)",
   lambda s: re.sub(
       r"let ground_eq_b g =\n\s+\(=\) g\.lin_ground g\.lin_dB",
       "let ground_eq_b _ =\n  false",
       s,
       count=1)),

  ("M16 exclude ground itself from L3 candidates",
   lambda s: s.replace(
       "existsb (source_pred g) (g.lin_ground :: (ancestors g g.lin_ground))",
       "existsb (source_pred g) (ancestors g g.lin_ground)",
       1)),

  ("M17 require ground to be derived again (WF)",
   lambda s: s.replace(
       "(mem g.lin_ground (lin_nodes g))",
       "(mem g.lin_ground (map fst g.lin_derived))",
       1)),
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
    suites = {
        "fixed": False,
        "random": False,
        "shallow": False,
        "deep": False,
        "v6": False,
    }
    pops = []
    m1 = re.search(r"case study: (\d+)/(\d+) agree", out)
    if m1 and m1.group(1) != m1.group(2): suites["fixed"] = True
    m2 = re.search(r"random differential: (\d+)/(\d+) agree", out)
    if m2 and m2.group(1) != m2.group(2): suites["random"] = True
    m_v6 = re.search(r"v6 edge cases: (\d+)/(\d+) pass", out)
    if m_v6 and m_v6.group(1) != m_v6.group(2):
        suites["v6"] = True
    for line in out.splitlines():
        m3 = re.match(r"(.+?)\s+n=\d+\s+intended-verdict (\d+)/(\d+)\s+handwritten-flags (\d+)/(\d+)", line)
        if m3 and (m3.group(2) != m3.group(3) or m3.group(4) != m3.group(5)):
            lab = m3.group(1).strip(); pops.append(lab)
            suites["deep" if lab.startswith("deep:") else "shallow"] = True
    return name, "detected" if any(suites.values()) else "UNDETECTED", (suites, pops)

rows = [run(n, f) for n, f in MUTANTS]
mark = lambda b: "x" if b else "."
print("| mutant | fixed | random | shallow strat. | deep strat. | v6 edge |")
print("|---|:-:|:-:|:-:|:-:|:-:|")
for n, v, info in rows:
    if info is None:
        print(f"| {n} | {v} | | | | |"); continue
    su, _ = info
    print(
        f"| {n} | {mark(su['fixed'])} | {mark(su['random'])} | "
        f"{mark(su['shallow'])} | {mark(su['deep'])} | {mark(su['v6'])} |"
    )
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
print(
    f"detected by v6 edge suite alone: "
    f"{cnt(lambda su: su['v6'])}/{tot}"
)

v6_only = [
    n for n, su in ok
    if su["v6"]
    and not (su["fixed"] or su["random"] or su["shallow"] or su["deep"])
]
print("detected only by v6 edge suite:", v6_only)

miss = [n for n, su in ok if not any(su.values())]
notrun = [n for n, v, i in rows if i is None]
if miss or notrun: print("NOT DETECTED:", miss, "NOT RUN:", notrun)
sys.exit(1 if (miss or notrun) else 0)
