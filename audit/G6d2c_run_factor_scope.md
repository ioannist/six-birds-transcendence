# G6d-2c: §7.4 stop report and hybrid resolution

## Original stop boundary (historical)

No Lean implementation or status change in the original stop packet. The existing build is
green. C6/C8 extraction is stopped before introducing a finite-context premise.
This report concerns the **generic** run-to-factor reduction, not the soundness
of the committed POS-04 results and not the truth of TTH-06's conditional
soundness claim.

## Missing recipe-language contract

The accepted design permits state/context-dependent required resources and
effective budget/recharge (`G6d_generic_handoff_design.md:264–265`), with
unbounded run counters and tapes (`:112–120`). Its controlled-data sketch names
`FiniteLedgerRecipes` (`:249`), but neither defines that instruction language
nor proves that its interpreted resource/response conditions factor through a
finite context. There is no implemented `FiniteLedgerRecipes` in the generic
Lean layer.

Finite source tables, finite actions and finite resource names do not imply
finite **behavioral** context. A finite recipe can inspect an unbounded counter.
Likewise, a finite list of audit roots does not make its future closure finite.
The entry requirement (`:271–273`) rejects unrepresentable entries; it does not
establish representability after every future step.

The necessary missing assertion has this mathematical content. For the defined
run updater and computed reachable closure, there must be a constructed finite
factor projection `proj` and a proved run invariant `Inv` such that:

1. Every acquisition entry satisfies `Inv`.
2. Every admitted supported response preserves `Inv`.
3. On **every** reachable `Inv` run, each relevant action's availability,
   ownership, required/retained resources, response support and projected
   successors agree with the finite factor interpretation.
4. The actual ledger equations preserve affordability/solvency and the actual
   writer/tick/progress/record equations preserve their advancement conditions.
   Counter values need not be finite: they are governed by the run invariant.
5. Any omitted run context is proved irrelevant to those decisions. A factor
   response must lift from each corresponding run context, not only from a
   selected representative.

The unresolved choice is the permitted raw recipe language, not a request to
assume that the existing POS-04 lift is sound. If `FiniteLedgerRecipes` was
intended to exclude arbitrary counter/tape tests, that boundary needs to be
specified before extraction; the current sketch alone does not determine it.

This cannot be a supplied `finiteContextsClosed : Prop`, an arbitrary projection
with no commuting laws, or a renamed response/solvency verdict. The projection
and invariant must be constructed from a specified raw instruction language;
the laws must follow from its interpretation or checked raw equations.

## Why unrestricted context dependence cannot supply that assertion

A mathematical obstruction to automatic extraction is a deterministic run
counter `n`, initialized at zero and updated to `n+1`, over a singleton physical
factor. A nominal disturbance has an always-available advancing response; a
second disturbance requests one named target-owned resource, available exactly
when `n` is a square. Thus the nominal supported closure contains every counter
value, and the other disturbance makes resource context response-relevant. This availability test is a finite arithmetic recipe; it needs neither
infinitely many resource names nor an infinite source table. It is an
illustration of the unspecified instruction-language boundary, **not** a newly
declared FIACH model or an evaluated clause/control.

The singleton projection already loses availability: at counters 1 and 2 the
physical factor is identical, but the resource decisions differ. More strongly,
no deterministic finite context can exactly reproduce both the successor and
that availability output on the entire advancing closure:

- Exact row/support projection of the deterministic nominal advancing step
  must give a deterministic successor on reachable finite contexts; introducing
  extra positive branches would not preserve the actual probability-one row.
- The orbit of any deterministic finite context eventually repeats and hence
  is eventually periodic, with some positive period `p`.
- Its availability output would therefore also be eventually periodic.
- Choose a square `k²` beyond the transient prefix, with `2k+1 > p`.
  Periodicity would make `k²+p` available. But
  `k² < k²+p < (k+1)²`, so it is not a square: a contradiction.

Thus *if* the design's context-dependent recipes include such tests, an exact
finite reduction in the specified sense is impossible. The current sketch does
not exclude them. Requiring a special finite-state recipe grammar would resolve
this case, but choosing that grammar now restricts the raw-model contract and
needs the owner's decision. The example does not claim that a valid autonomy
certificate exists for such a resource schedule. It shows why the requested
reduction is not derivable for arbitrary raw recipes before validity is checked.
A conservative rejection checker is a possible design, but must be explicitly
specified; it is not an exact reduction of all raw contexts.

## Existing laws that do suffice on POS-04

POS-04 has a narrower, genuine proved lift mechanism:

- `Assigned/C6Dynamics.lean:82–96`: budget is the assigned fixed budget;
  the updater preserves residue and updates funding by its ledger equation.
- `Assigned/C6Acceptance.lean:54–55`: acceptance checks positive conserved
  unit funding. `c6_accept_record_advancement` (`:113`) derives funded record
  growth; it is not a supplied advancement flag.
- `G6_lane_spec.md:202–214`: responses quantify over declared route-register
  contexts, with conserved budget and unit advances.
- `G6_lane_spec.md:235–242`: unbounded counters lift that finite factor under
  these particular checked laws.

These facts do not entail closure for arbitrary changing tapes, resource guards
or ledger recipes. Generalizing their constants while retaining exactly their
context behavior would silently make a fixed family the generic contract.

`ViableSet.lean:3–5` explicitly makes no run-to-factor claim. Its greatest-set
proof is valid for a supplied finite retention operator. It cannot prove that
an infinite run's availability or resource obligations descend to that operator.
G0's separate TTS-04 contract (`G0_generic_contracts.md:359`) checks an
all-run affordability invariant for its policy; that is not a general theorem
that every context-dependent resource recipe has a finite quotient.

## Owner decision required (historical; resolved below)

Two honest paths are available; neither is applied here:

1. **Specify the finite instruction language and its lift checks.** Raw resource
   and response recipes may depend on a finite, declared context machine, plus
   an unbounded ledger governed by proved inductive affordability laws.
   Construct that machine/projection from raw data and prove all closure laws.
   Explicitly decide which unbounded-context recipes are excluded or rejected,
   and whether this is an approved restriction of G0/G6. No fixed POS-04 unit
   ledger, two-route domain or ten-state carrier becomes a generic assumption.
2. **Keep unrestricted run-context recipes.** Prove an infinite-state controlled
   invariant on the defined run space. Use the finite viable-set engine only
   where a separate exact lift has actually been proved. This is the larger
   follow-up identified in design §7.4.

A mere finite-context closure hypothesis is insufficient under the packet's
rule. No new hypothesis, statement narrowing, model declaration, registry edit,
or status promotion has been made. Completion of generic C6/C8 and its POS-04
family equivalences remains open pending this decision.

## Original stop checks and statement changes (historical)

- `cd lean && lake build`: exit 0 (373 jobs).
- `scripts/validate_lean.sh`: exit 0; inventory matches, probes exit 0,
  no untrusted axioms, no placeholders or high-confidence vacuity findings.
- `git diff --check`: clean. Only this new note is changed; Lean, scripts,
  registries and frozen science files are untouched.
- Statement-change list: (a) none; (b) none. The counter/tape argument above is
  a mathematical scope obstruction, not a new certified TTN witness or model.


## Resolution: hybrid architecture adopted

Manager decision, Eddy ACCEPT-WITH-FIXES: retain unrestricted raw run-context
recipes, option 2. The preceding stop report is historical; it is not a pending
request to restrict the recipe language.

- The square-counter example **fails full autonomy**. Counter 2 is nominally
  reachable, but the resource-request disturbance has no available response.
  An infinite invariant cannot change that failure.
- Other unrestricted recipes may be proved autonomous using a run-space
  invariant, with all obligations proved against the defined raw semantics.
- The finite constructor is a sound, potentially incomplete certifier.
  Completeness needs a precisely specified fragment, proved exact lifting and
  decidable checks; it is not asserted for arbitrary raw recipes.
- (b) architectural change: auxiliary invariant witnesses are allowed.
  Supplied dynamics, observations and autonomy verdicts remain prohibited.

No row wording or status is changed by this resolution. The architectural
addendum in G6d_generic_handoff_design.md records the implementation order.


The first implementation boundary after resolution is the strategy/play
induction kernel and its sound finite-constructor helper. See
[G6d2c_hybrid_game_kernel.md](G6d2c_hybrid_game_kernel.md). This does not yet
bind the generic raw components or prove POS-04 C6/C8 equivalences.
