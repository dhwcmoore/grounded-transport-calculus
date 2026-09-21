grounded-transport-calculus

# Proposed project

Suggested folder name:

```text
grounded-transport-calculus
```

Working title:

> Grounded Transport: Proof-Relevant Rewriting for Processual Ontologies

The central claim is:

> Substitutability is not always exhausted by extensional equality. In lineage-sensitive systems, substitution requires an exhibited process connecting the terms, and contexts must preserve that processual warrant.

## 1. What we already have

| Existing result | Location/source | Status |
|---|---|---|
| Admissibility characterisation | Accepted admissibility paper, Theorem 2.3 | Proved |
| Grounded seam coherence | *The Work of Exactness* | Defined |
| Grounding entails extensional seam coherence | *The Work of Exactness* | Proved |
| Ungrounded agreement counterexample | *The Work of Exactness* | Proved |
| Dynamic seam naturality | Manuscript and formalisation | Defined |
| Transport across a grounded seam | `GroundedSeam.v`, `seam_transport` | Machine checked |
| Composition of evolution | `GroundedSeam.v`, `evolution_compose` | Machine checked |
| Copied value need not be grounded | `GroundedSeam.v`, `copied_not_grounded` | Machine checked |
| Boolean reflection lemmas | `GroundedSeam.v` | Machine checked |
| Lineage audit | OCaml supplement | Implemented |
| Regional repair-or-separator obstruction | Regional Obstruction Calculus | Separate proved obstruction |
| Fork, order, and quorum obstructions | PCBS work | Separate obstruction family |

### The existing transport theorem

We do indeed already have a transportation theorem. In its current seam-specific form, it says roughly:

If

\[
\Phi_{A,t}=\widehat{\Phi}_t\circ M_t
\]

and the grounding equations hold across the seam

\[
A_t \xleftarrow{\mathrm{back}_t}\Sigma_t
\xrightarrow{\mathrm{fwd}_t}B_t,
\]

then, on seam states,

\[
\Phi_{B,t}\circ\mathrm{fwd}_t
=
\widehat{\Phi}_t\circ M_t\circ\mathrm{back}_t.
\]

This is the machine-checked theorem `seam_transport`.

Its limitation is important: it transports the factorisation along the exhibited seam. It does not automatically construct a factorisation for all \(B\)-states lying outside the image of \(\mathrm{fwd}_t\).

So the new preservation theorem should be presented as a generalisation of `seam_transport`.

## 2. Status of the five proposed contributions

| Proposed contribution | Current status | What remains |
|---|---|---|
| Grounded transport calculus | Partly present in the seam formalisation | Abstract it into a generic proof-relevant, directed calculus |
| Erasure theorem | Grounding-to-extension result already exists | State and prove the generic erasure result |
| Preservation theorem | `seam_transport` and `evolution_compose` exist | Generalise to arbitrary grounded-proper contexts |
| Obstruction theorem | Core ingredients already proved | Package them as one generic lineage-sensitive obstruction theorem |
| Warrant classification theorem | Conceptual taxonomy exists | Define the four debts formally and prove classifier properties |

The accurate novelty claim is therefore:

> We are extracting a general calculus from an already verified special case, connecting it to the existing admissibility obstruction, and adding a formal classification of transport failure.

## 3. The formal core we need to build

### A. Directed proof-relevant transport

Start with a generic judgement:

\[
\mathsf{GTrans}_R(x,y) : \mathsf{Type}.
\]

An inhabitant is evidence that \(x\) may be transported to \(y\). It should contain, or point to:

- the directed transformation;
- an exhibited construction or seam;
- lineage evidence;
- grounding equations;
- any required authorisation or institutional warrant.

It should support:

\[
\mathsf{id}_x : \mathsf{GTrans}(x,x)
\]

and

\[
\mathsf{compose} :
\mathsf{GTrans}(x,y)
\to
\mathsf{GTrans}(y,z)
\to
\mathsf{GTrans}(x,z).
\]

We should not initially require symmetry. Whiteheadian transition, derivation, maintenance and construction are naturally directed.

### B. Erased relation

Define:

\[
x \preccurlyeq_G y
\quad\Longleftrightarrow\quad
\exists w:\mathsf{GTrans}(x,y),\ \top.
\]

In Coq this can initially be an ordinary existential or `inhabited`. Later, if necessary, we can distinguish propositional truncation from computational witness retention.

Prove:

1. identity gives reflexivity;
2. witness composition gives transitivity;
3. every grounded transport entails the relevant ordinary relation;
4. witness erasure forgets lineage and construction information.

We should be cautious about saying that erasure always “recovers” a pre-existing setoid exactly. The general result is soundness:

\[
\mathsf{GTrans}(x,y)\to R(x,y).
\]

Exact recovery,

\[
R(x,y)\leftrightarrow \|\mathsf{GTrans}(x,y)\|,
\]

requires an additional completeness or representability hypothesis. It will usually fail in precisely the cases we care about.

### C. Grounded-proper contexts

Define:

\[
\mathsf{GroundedProper}(F)
\]

to mean that \(F\) maps transport witnesses compositionally:

\[
\mathsf{map}_F :
\mathsf{GTrans}_A(x,y)
\to
\mathsf{GTrans}_B(Fx,Fy).
\]

The laws should include:

\[
\mathsf{map}_F(\mathsf{id})=\mathsf{id}
\]

and

\[
\mathsf{map}_F(v\circ w)
=
\mathsf{map}_F(v)\circ\mathsf{map}_F(w).
\]

This is the proof-relevant analogue of Rocq’s `Proper`. Ordinary `Proper` preserves a relation. `GroundedProper` preserves the warrant for that relation.

### D. Generic preservation theorem

The generic theorem should say:

> Every grounded-proper context transports valid grounded witnesses, and nested grounded-proper contexts transport them compositionally.

Schematic statement:

\[
w:\mathsf{GTrans}(x,y)
\quad\Longrightarrow\quad
\mathsf{map}_C(w):
\mathsf{GTrans}(C[x],C[y]).
\]

Then prove that the existing seam construction is an instance. `seam_transport` becomes a corollary or canonical example rather than a disconnected theorem.

## 4. The obstruction theorem

We have already proved its mathematical engine in the admissibility work.

For an observation map

\[
M:X\to O
\]

and a predicate or valuation

\[
\Phi:X\to V,
\]

the admissibility theorem says:

\[
\Phi=\widehat{\Phi}\circ M
\]

for some \(\widehat{\Phi}\) if and only if \(\Phi\) is constant on the fibres of \(M\).

Thus a pair

\[
M(x)=M(y)
\qquad\text{and}\qquad
\Phi(x)\neq\Phi(y)
\]

is a certificate that \(\Phi\) cannot be determined from the observations alone.

The new obstruction theorem should specialise this to rewriting:

> If \(x\) and \(y\) are observationally equivalent but a lineage-sensitive predicate distinguishes them, then observational equivalence cannot justify substitution for that predicate.

Formally:

\[
x\sim_M y
\land
P(x)\neq P(y)
\quad\Longrightarrow\quad
\neg\mathsf{Proper}(\sim_M,\equiv)(P).
\]

The stronger grounded interpretation is:

\[
M(x)=M(y)
\]

does not imply

\[
\mathsf{GTrans}(x,y).
\]

The existing “ungrounded agreement” construction and `copied_not_grounded` supply the canonical counterexample.

So we have not yet proved this exact generic theorem under this exact name, but we have proved both its abstract factorisation principle and its central seam counterexample.

## 5. Warrant Debt classification

A failed transport should produce evidence, not just `false`.

Use something like:

```coq
Inductive WarrantDebt :=
| ObservationalDebt
| ConstructionDebt
| MaintenanceDebt
| InstitutionalDebt.
```

But a single exclusive constructor is probably too weak because several debts may coexist. A better result is a report containing independently checkable defects:

```coq
Record DebtReport := {
  observational_debt : option ObservationalFailure;
  construction_debt  : option ConstructionFailure;
  maintenance_debt   : option MaintenanceFailure;
  institutional_debt : option InstitutionalFailure
}.
```

The intended meanings are:

| Debt | Missing warrant |
|---|---|
| Observational | The proposed valuation does not factor through the available observations |
| Construction | No exhibited seam, derivation or ground connects the states |
| Maintenance | The warrant is not preserved through update, evolution or composition |
| Institutional | No declared rule, authority or practice licenses the transformation |

The formal theorem should have two parts:

- **Soundness:** every reported debt corresponds to a failed transport obligation.
- **Relative completeness:** if transport fails, at least one debt is reported, assuming the underlying obligations and institutional authorisations are decidable.

“Institutional debt” cannot be inferred from mathematics alone. The system must accept a policy, authority relation or declared institutional judgement as input.

## 6. Suggested project structure

```text
grounded-transport-calculus/
├── README.md
├── STATUS.md
├── _CoqProject
├── dune-project
├── theories/
│   ├── Core/
│   │   ├── GroundedTransport.v
│   │   ├── Erasure.v
│   │   └── Composition.v
│   ├── Contexts/
│   │   ├── GroundedProper.v
│   │   └── ContextualPreservation.v
│   ├── Obstructions/
│   │   ├── FibreObstruction.v
│   │   ├── LineageObstruction.v
│   │   └── UngroundedAgreement.v
│   ├── Debt/
│   │   ├── WarrantDebt.v
│   │   └── DebtClassifier.v
│   └── Instances/
│       ├── GroundedSeam.v
│       └── DynamicSeam.v
├── examples/
│   ├── CopiedCoordinates.v
│   ├── SeamTransport.v
│   └── MaintenanceFailure.v
├── extraction/
│   └── lineage_audit.ml
├── paper/
│   ├── outline.md
│   ├── theorem-ledger.md
│   └── notation.md
└── legacy/
    ├── original-GroundedSeam.v
    └── provenance.md
```

Keep the original checked file unchanged in `legacy/` until its theorems have been reproduced as instances of the new calculus.

## 7. Development order

### Phase 1: Inventory and preservation

- Copy the current `GroundedSeam.v`.
- Copy the OCaml lineage audit.
- Record every existing theorem and its assumptions.
- Run the existing checks unchanged.
- Create a theorem ledger marking results as existing, generalised, new or conjectural.

### Phase 2: Minimal generic calculus

Implement only:

- `GroundedTransport`;
- identity;
- composition;
- erased relation;
- erasure soundness.

Do not begin with a large expression language or custom rewriting tactic.

### Phase 3: Contextual transport

- Define `GroundedProper`.
- Prove identity and composition instances.
- Prove contextual preservation.
- Instantiate the framework with grounded seams.
- Recover `seam_transport`.

This is the first major checkpoint.

### Phase 4: Obstruction

- Import or restate the fibre-factorisation theorem.
- Prove observational equivalence is insufficient for lineage-sensitive predicates.
- Reconstruct `copied_not_grounded` as the canonical model.
- State clearly that this is a failure of warrant, not necessarily a failure of extensional agreement.

### Phase 5: Warrant Debt

- Define the four failure obligations.
- Decide whether reports use lists, finite sets or a record of optional evidence.
- Implement a classifier.
- Prove soundness.
- Prove relative completeness under decidability assumptions.

### Phase 6: Rewriting interface

Only after the semantics are stable:

- connect the erased relation to Rocq `Proper`;
- add `GroundedProper` instances;
- explore notation or tactics for witness-carrying rewriting;
- distinguish ordinary `rewrite`, `setoid_rewrite`, and grounded transport.

## 8. The first deliverable

The best first milestone is a small formal kernel with four machine-checked results:

1. `grounded_transport_refl`
2. `grounded_transport_compose`
3. `erasure_sound`
4. `grounded_proper_compose`

Then add the seam instance and prove:

```coq
Corollary existing_seam_transport :
  ...
```

using the generic preservation theorem.

That establishes the project’s central claim: the earlier transportation theorem was not an isolated construction. It was the first instance of a general proof-relevant rewriting calculus.
