#!/usr/bin/env python3
"""W4: extract exact Lean results and check their named theorem pins.

Python 3.12 stdlib only. Existing CSTTT oleans are used; no build is run.
Scratch files and small diagnostic logs stay in lean/.validate-logs/.
The specification below contains expressions and proof projections, not values.
--check repeats extraction, declaration/axiom checks and kernel pin checks before
comparing bytes. Candidate findings are NOT licensed paper-facing entries.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import csv
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'paper/data'
LEDGER = ROOT / 'paper/prewriting/claim_ledger.csv'
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
sys.path.insert(0, str(ROOT / 'scripts'))
from validate_lean import make_probe, parse_probe  # noqa: E402

PS = 'CSTTT.PaperSupport'
P = 'CSTTT.POS04'
N = 'CSTTT.TargetTheory.GenericHandoff.NativeComposition'
F = 'CSTTT.FullNative'
V = F + '.Viability'
B = F + '.Binding'
J = F + '.JointClaims'
I = F + '.Internalized'
T = 'CSTTT.FullNative02'
R = 'CSTTT.RobustnessTheory.POS04RationalMargin'
PR = 'CSTTT.TargetTheory.GenericHandoff.ProfileRules'
O = 'CSTTT.Objecthood.T1Audit'


def spec(key, kind, expr, pin, claim, model, description, proof,
         view=None):
    return dict(key=key, kind=kind, expr=expr, pin=pin, claim=claim, model=model,
                description=description, proof=proof, view=view)


def specs():
    """Only theorem identities, input choices and readout expressions are frozen.

    VALUE in a proof view is substituted exclusively from fresh Lean output.
    Equality projections preserve the original pin rather than replacing it
    with a new scratch theorem. A definitional view is explicitly distinguished.
    """
    out = [
        spec('pos04_tagged_ambient_states', 'integer',
             f'({P}.tags.flatMap (fun tag => {P}.ambientStates.map (fun s => (tag,s)))).length',
             PS+'.pos04_tagged_ambient_count', 'TTH-06-INST', 'POS-04 tagged ambient carrier',
             'Tagged ambient states, including exits outside the maintained kernel.', 'exact pinned'),
        spec('pos04_tagged_lethal_states', 'integer',
             f'({P}.tags.flatMap (fun tag => ({P}.ambientStates.filter {P}.isLethalHazard).map (fun s => (tag,s)))).length',
             PS+'.pos04_tagged_lethal_count', 'TTH-06-INST', 'POS-04 tagged ambient carrier',
             'Tagged ambient states satisfying the actual lethal hazard predicate.', 'exact pinned'),
        spec('pos04_c1_epsilon', 'rational', P+'.c1Epsilon',
             PS+'.pos04_c1_epsilon', 'TTH-06-INST', 'POS-04 perturbed C1',
             'Frozen perturbation epsilon of the POS-04 C1 audit.', 'exact pinned'),
        spec('g7_native_factor_states', 'integer', N+'.factors.length',
             PS+'.g7_native_factor_count', 'TTH-07', 'G7 native eight-factor process',
             'States in the actual G7 native factor enumeration.', 'exact pinned'),
        spec('full_native_02_physical_states', 'integer', F+'.states.length',
             F+'.state_domain', 'TTF-05', 'FULL-NATIVE-02 / canonical32 and flat32',
             'Physical states shared by the two installed ROMs.', 'exact pinned.2'),
        spec('full_native_02_c8_factor_states', 'integer', V+'.carrier.length',
             V+'.carrier_exact', 'TTF-05', 'FULL-NATIVE-02 physical/charge factor',
             'Physical state and stored-charge factor cardinality.', 'exact pinned.2'),
        spec('full_native_02_operational_core_states', 'integer',
             f'({V}.carrier.filter {T}.Viability.core).length',
             T+'.Viability.sixteen_inside_charged_states', 'TTF-05',
             'FULL-NATIVE-02 renewable operational C8',
             'Inside charged factors in the operational core, including cold residents.',
             'exact pinned'),
        spec('pos04_c3_trajectory', 'integer_list',
             f'[{P}.classCount ({P}.profile0 ({P}.positiveLowerRule .source)), '
             f'{P}.classCount (w4PosStep .positive .source '
             f'({P}.profile0 ({P}.positiveLowerRule .source))), '
             f'{P}.classCount (w4PosStep .positive .source '
             f'(w4Memo {O}.kernel w4PosComplete '
             f'(w4PosStep .positive .source ({P}.profile0 ({P}.positiveLowerRule .source)))))]',
             P+'.c3_trajectory_each_tag', 'TTH-06-INST', 'POS-04 / source tag',
             'Initial, first and second predictive class counts.',
             'simp only [w4PosStep_eq,w4Memo_eq]\n  exact pinned .source'),
        spec('g7_c3_trajectory', 'integer_list',
             f'[{PR}.count {N}.profile ({PR}.seed {N}.profile), '
             f'{PR}.count {N}.profile ({PR}.first {N}.profile), '
             f'{PR}.count {N}.profile ({PR}.second {N}.profile)]',
             N+'.recursive_profile', 'TTH-07', 'G7 native eight-factor process',
             'Initial, first and second class counts of the G7 factor.',
             f'have p : {PR}.RecursiveProfile {N}.profile := pinned false\n'
             f'  simp only [{PR}.RecursiveProfile] at p\n'
             '  rw [p.1, p.2.1, p.2.2.1]\n  rfl'),
        spec('full_native_02_c3_trajectory', 'integer_list',
             f'[{PR}.count ({F}.profile {F}.model) ({PR}.seed ({F}.profile {F}.model)), '
             f'{PR}.count ({F}.profile {F}.model) '
             f'{F}.classFormula, '
             f'{PR}.count ({F}.profile {F}.model) '
             f'(w4Step ({F}.profile {F}.model) {F}.classFormula)]',
             F+'.profile_trajectory', 'TTF-05', 'FULL-NATIVE-02 / canonical32',
             'Canonical installed physical profile class counts.',
             f'simp only [w4Step_eq]\n'
             f'  rw [← {F}.first_profile_equation]\n'
             f'  change [_,_,{PR}.count ({F}.profile {F}.model) '
             f'({PR}.second ({F}.profile {F}.model))] = _\n'
             '  rw [pinned.1, pinned.2.1, pinned.2.2]'),
        spec('g7_strict_chain_system_ids', 'integer_list',
             f'[({N}.PublicationCorridor.left (false,false,false)).source, '
             f'({N}.PublicationCorridor.left (false,false,false)).target, '
             f'({N}.PublicationCorridor.right (false,false,false)).target]',
             N+'.PublicationCorridor.carrier_chain', 'TTH-07', 'G7 native strict chain',
             'Source, intermediate and final system identifiers.',
             'have p := pinned (false,false,false)\n  rw [p.1,p.2.1,p.2.2.2]'),
        spec('pos04_c1_recurrent_mass', 'rational', P+'.taggedCoreMass .source',
             P+'.c1_core_mass_each_tag', 'TTH-06-INST', 'POS-04 C1',
             'Stationary mass on the recurrent states.', 'exact pinned .source'),
        spec('pos04_c1_total_variation', 'rational', P+'.taggedTV .source',
             P+'.c1_tv_each_tag', 'TTH-06-INST', 'POS-04 C1',
             'Total variation from the declared recurrent uniform distribution.',
             'exact pinned .source'),
        spec('pos04_c1_idempotence_defect', 'rational', P+'.taggedDefect .source',
             P+'.c1_defect_each_tag', 'TTH-06-INST', 'POS-04 perturbed C1',
             'Exact defect of the declared perturbed two-step matrix.', 'exact pinned .source'),
        spec('pos04_staged_clause_count','integer',P+'.stagedClauseMap.length',
             P+'.staged_map_count','TTH-06-INST','POS-04 staged package map',
             'Number of clause entries in the frozen staged map.', 'exact pinned'),
    ]
    # One pin fixes both actual joint laws, without conflating POS-04 and G28.
    for key, run, side in [('g28_canonical_joint_mass', 'canonicalExecution', '1'),
                            ('g28_flat_joint_mass', 'flatExecution', '2')]:
        out.append(spec(key, 'rational',
                        f'{F}.RecombinationBoundary.jointLaw {F}.RecombinationBoundary.{run} [false] [0]',
                        F+'.RecombinationBoundary.actual_joint_countertrace', 'TTN-14',
                        'FULL-NATIVE-01 G28 / '+run,
                        'Joint observation mass after one actual maintenance action.',
                        'exact pinned.'+side))
    for key, right, side in [('g27_c7_left_joint_mass','false','1'),
                              ('g27_c7_right_joint_mass','true','2')]:
        out.append(spec(key, 'rational',
                        f'{B}.emittedLaw ({F}.rationalRows {F}.model) {B}.joint '
                        f'({B}.splitState {F}.PhysicalExecution.source.resident.current {right}) [false] [0]',
                        B+'.split_joint_gap', 'TTF-05', 'FULL-NATIVE-01 G27 C7',
                        'Next maintenance joint mass at the supported physical split.',
                        f'exact (pinned {F}.PhysicalExecution.source.resident.current).{side}'))
    condpin = J+'.conditioning_factorization_countertrace'
    out.extend([
        spec('g26_conditioning_event_weights','rational_list',f'{J}.eventRows.map Prod.snd',
             J+'.actual_conditioning_weights','JOINT-COND','FULL-NATIVE-01 G26 actual joint row',
             'Unconditioned probabilities of the two retained correlated outcomes.', 'exact pinned.1'),
        spec('g26_conditioning_event_mass','rational',J+'.eventMass',
             J+'.actual_conditioning_weights','JOINT-COND','FULL-NATIVE-01 G26 actual joint row',
             'Total unconditioned mass of the shared conditioning event.', 'exact pinned.2'),
        spec('g26_conditioning_relative_weights','rational_list',
             f'(let ws := {J}.eventRows.map Prod.snd; '
             f'ws.map (fun q => q/(ws.head?.get (by dsimp only [ws]; rw [{J}.actual_conditioning_weights.1]; rfl))))',
             J+'.actual_conditioning_weights','JOINT-COND','FULL-NATIVE-01 G26 actual joint row',
             'Correlated outcome weights relative to the first positive outcome.',
             'simp only [pinned.1]\n  decide +kernel +revert'),
        spec('g26_conditioned_joint_mass','option_rational',
             f'{J}.conditionedJoint [] [{J}.correlatedObservation false]',
             condpin,'JOINT-COND','FULL-NATIVE-01 G26 shared-event conditioning',
             'Conditioned joint mass of the selected correlated observation.', 'exact pinned.1'),
        spec('g26_conditioned_left_mass','option_rational',
             f'{J}.conditionedBranch false [] [({J}.correlatedObservation false).1]',
             condpin,'JOINT-COND','FULL-NATIVE-01 G26 shared-event conditioning',
             'Conditioned left marginal mass.', 'exact pinned.2.1'),
        spec('g26_conditioned_right_mass','option_rational',
             f'{J}.conditionedBranch true [] [({J}.correlatedObservation false).2]',
             condpin,'JOINT-COND','FULL-NATIVE-01 G26 shared-event conditioning',
             'Conditioned right marginal mass.', 'exact pinned.2.2.1'),
        spec('g26_product_of_conditioned_marginals','option_rational',
             f'(do let l ← {J}.conditionedBranch false [] [({J}.correlatedObservation false).1]; '
             f'let r ← {J}.conditionedBranch true [] [({J}.correlatedObservation false).2]; pure (l*r))',
             condpin,'JOINT-COND','FULL-NATIVE-01 G26 shared-event conditioning',
             'Product of the two separately conditioned marginal masses.',
             'rw [pinned.2.1,pinned.2.2.1]\n  decide +kernel'),
    ])
    for key, flavor, side in [('g25_source_holonomy_mass','source','1'),
                               ('g25_native_holonomy_mass','native','2')]:
        entry = spec(key,'option_rational',
                        f'{I}.holonomyReadout .{flavor} ({I}.root .{flavor} 0)',
                        I+'.holonomy_readouts_exact','TTF-05',
                        'G25 nine-state reversible internalized control / '+flavor,
                        'Law-gated holonomy mass of the separate reversible control.',
                        f'exact (pinned 0).{side}')
        entry['value_from'] = key.replace('holonomy_mass', 'protocol_mass')
        out.append(entry)
        out.append(spec(key.replace('holonomy_mass','protocol_mass'),'rational',
                        f'{I}.protocolMass {F}.AccountExecution.renewable '
                        f'({I}.root .{flavor} 0) {I}.protocolAB (.c,.a)',
                        I+'.actual_protocol_holonomy','TTF-05',
                        'G25 nine-state reversible internalized control / '+flavor,
                        'Evaluated forward protocol mass underlying the law-gated readout.',
                        f'rw [(pinned .{flavor} 0).1,{I}.parameters_exact.{side}]\n'
                        '  decide +kernel'))
    for key, flavor, side in [('g25_source_bias','source','1'),('g25_native_bias','native','2')]:
        out.append(spec(key,'rational',f'{I}.parameter .{flavor}',
                        I+'.parameters_exact','TTF-05',
                        'G25 nine-state reversible internalized control / '+flavor,
                        'Bias of the separate reversible control.', 'exact pinned.'+side))
    for key, fun, side in [('g23_source_forward_cycle_mass','forwardReceipts','1'),
                           ('g23_source_reverse_cycle_mass','reverseReceipts','2')]:
        out.append(spec(key,'option_rational',
                        f'({F}.Credit.sourceCycleWorld.carriers 0).map '
                        f'(fun (p : {F}.PhysicalExecution.Local) => {F}.Credit.{fun} {F}.model p.receipts)',
                        F+'.Credit.source_actual_cycle_products', 'TTF-05',
                        'FULL-NATIVE-01 G23 actual directional receipts',
                        'Actual source receipt cycle product.',
                        f'rw [pinned.{side}]\n  decide +kernel'))
    rows = f'{T}.fusionRows {T}.renewable {T}.branchesWorld {T}.mainRequest'
    out.extend([
        spec('full_native_02_fusion_outcome_count','integer',f'({rows}).length',
             T+'.main_positive_rows','TTF-04','FULL-NATIVE-02 owned canonical fusion',
             'Number of actual positive settlements of the frozen main request.',
             'rw [pinned]\n  decide +kernel'),
        spec('full_native_02_fusion_settlement_probabilities','rational_list',
             f'({rows}).map Prod.snd', T+'.main_positive_rows','TTF-04',
             'FULL-NATIVE-02 owned canonical fusion',
             'Normalized settlement probabilities in actual execution row order.',
             'rw [pinned]\n  decide +kernel'),
        spec('full_native_02_fusion_probability_sum','rational',
             f'(({rows}).map Prod.snd).sum', T+'.main_positive_rows','TTF-04',
             'FULL-NATIVE-02 owned canonical fusion',
             'Total probability mass of the actual supported fusion row.',
             'rw [pinned]\n  decide +kernel'),
        spec('full_native_02_empty_probability','rational_list',
             f'({T}.fusionRows {T}.renewable {T}.branchesWorld {T}.probeRequest).map Prod.snd',
             T+'.probe_empty_control','TTF-04','FULL-NATIVE-02 opposed-action empty control',
             'Probabilities of the supported empty settlements.',
             'have h := congrArg (List.map Prod.snd) pinned.2\n'
             '  simpa only [List.map_map,Function.comp_def,List.map_cons,List.map_nil,w4DivOne] using h'),
        spec('full_native_02_absent_supply_first_outcomes','integer',T+'.absentFirst.length',
             T+'.absent_first_preserved','TTF-05','FULL-NATIVE-02 absent-supply control',
             'Supported outcomes of the initially stored-charge step without supply.',
             'exact pinned.1'),
        spec('tts03_half_box_radius','rational',R+'.radius .predictive',
             R+'.certified_margin','TTS-03','POS-04 rational-register extension',
             'Uniform radius of the certified five-coordinate closed box.',
             'exact pinned',
             f'CSTTT.RobustnessTheory.ExactFiveMargins.PositiveCertifiedMargin '
             f'{R}.advances (fun _ => VALUE)'),
        spec('tts03_component_advances','rational_list',
             f'(([.predictive,.order,.tick,.progress,.record] : '
             f'List CSTTT.RobustnessTheory.ExactFiveMargins.Coordinate).map {R}.advances)',
             R+'.actual_advance','TTS-03','POS-04 rational-register extension',
             'Uncorrected advances in predictive, order, tick, progress and record order.',
             'rw [pinned (fun _ => 0)]\n'
             '  apply congrArg some\n  funext i\n  cases i <;> decide +kernel',
             'TTS_VIEW'),
        spec('g7_fork_system_ids','integer_list',
             f'[{N}.NativeFission.fork.source.code,{N}.NativeFission.fork.left.code,'
             f'{N}.NativeFission.fork.right.code]',
             N+'.NativeFission.native_relation_valued_temporal_fission','TTH-08',
             'G7 native symmetric fork',
             'Shared source and both relation-valued continuation targets.',
             'exact pinned',
             # This view replaces only the three identifier fields of the
             # certified fork. The rest of the original theorem type is kept
             # by Lean's definitional equality check (see dynamic_view).
             'FORK_VIEW'),
    ])
    for s in out:
        s['bridges'] = [F+'.first_profile_equation'] if s['key']=='full_native_02_c3_trajectory' else []
        if s['key'] in {'g25_source_protocol_mass','g25_native_protocol_mass'}:
            s['bridges'] = [I+'.parameters_exact']
    by_key = {s['key']: s for s in out}
    for s in out:
        if 'value_from' in s:
            origin = by_key[s['value_from']]
            s['computed_expr'] = origin['expr']
            s['bridges'] = [origin['pin'], I+'.parameters_exact']
    return out


def candidate_specs():
    # W4b pins all four originally diagnostic values on their actual definitions.
    return []


PRELUDE = r'''
open Lean Elab Command Meta
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option format.width 100000
@[noinline] def w4Memo {S : Type} [DecidableEq S] (states : List S)
    (complete : ∀ s, s∈states) (f : S → Nat) : S → Nat :=
  let values := states.map f
  fun s => values[states.idxOf s]'(by
    simpa only [values,List.length_map] using List.idxOf_lt_length_of_mem (complete s))
theorem w4Memo_eq {S : Type} [DecidableEq S] (states : List S)
    (complete : ∀ s, s∈states) (f : S → Nat) : w4Memo states complete f=f := by
  funext s
  have bound : states.idxOf s<states.length := List.idxOf_lt_length_of_mem (complete s)
  have selected : states[states.idxOf s]'bound=s := by
    have h := @List.findIdx_getElem S (fun x => x==s) states bound
    exact of_decide_eq_true h
  simp only [w4Memo,List.getElem_map,selected]
theorem w4PosComplete (s : CSTTT.Objecthood.T1Audit.KState) :
    s∈CSTTT.Objecthood.T1Audit.kernel := by cases s <;> decide +kernel
@[noinline] def w4Step {S A O : Type} [DecidableEq S]
    (d : CSTTT.TargetTheory.GenericHandoff.ProfileRules.Raw S A O) (classes : S → Nat) : S → Nat :=
  let signatures := (d.states.map (CSTTT.TargetTheory.GenericHandoff.ProfileRules.signature d classes)).eraseDups
  fun s => signatures.idxOf (CSTTT.TargetTheory.GenericHandoff.ProfileRules.signature d classes s)
theorem w4Step_eq {S A O : Type} [DecidableEq S]
    (d : CSTTT.TargetTheory.GenericHandoff.ProfileRules.Raw S A O) (classes : S → Nat) :
    w4Step d classes=CSTTT.TargetTheory.GenericHandoff.ProfileRules.step d classes := rfl
@[noinline] def w4PosStep (variant : CSTTT.POS04.ProfileVariant) (tag : CSTTT.POS04.Tag)
    (classes : CSTTT.Objecthood.T1Audit.KState → Nat) : CSTTT.Objecthood.T1Audit.KState → Nat :=
  let signatures := (CSTTT.Objecthood.T1Audit.kernel.map (CSTTT.POS04.profileSignature variant tag classes)).eraseDups
  fun s => signatures.idxOf (CSTTT.POS04.profileSignature variant tag classes s)
theorem w4PosStep_eq (variant : CSTTT.POS04.ProfileVariant) (tag : CSTTT.POS04.Tag)
    (classes : CSTTT.Objecthood.T1Audit.KState → Nat) :
    w4PosStep variant tag classes=CSTTT.POS04.profileStep variant tag classes := rfl
theorem w4DivOne (q : Rat) : q/1=q := by
  have one : (1:Rat)⁻¹=1 := by decide +kernel
  rw [Rat.div_def,one,Rat.mul_one]
def w4Nat (n : Nat) : String := toString n
def w4Rat (q : Rat) : String := toString q.num ++ "/" ++ toString q.den
def w4List (xs : List String) : String := (toJson xs).compress
def w4Required (x : Option α) (f : α → String) : IO String :=
  match x with
  | none => throw (IO.userError "W4 required readout is absent; no default")
  | some a => pure (f a)
def w4Emit (key : String) (value : String) : IO Unit :=
  do
    IO.println ("W4_VALUE|" ++ (Json.mkObj [("key",toJson key),("value",toJson value)]).compress)
    (← IO.getStdout).flush
elab "#w4_statement " name:ident : command => do
  let env ← getEnv
  let n := name.getId
  match env.find? n with
  | none => throwError "Unresolved W4 pin: {n}"
  | some info =>
    let stmt ← liftTermElabM (ppExpr info.type)
    logInfo m!"W4_STATEMENT|{(Json.mkObj [("name",toJson n.toString),("statement",toJson stmt.pretty)]).compress}"
'''


def lean_run(source, log_name):
    logs = ROOT / 'lean/.validate-logs'
    logs.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', prefix='W4-',
                                     dir=logs, encoding='utf-8', delete=False) as stream:
        scratch = Path(stream.name)
        stream.write(source)
    try:
        with (logs/log_name).open('w',encoding='utf-8') as output:
            result = subprocess.run(['lake', 'env', 'lean', str(scratch)],
                                    cwd=ROOT/'lean', text=True, timeout=1500,
                                    stdout=output, stderr=subprocess.STDOUT)
        result.stdout = (logs/log_name).read_text(encoding='utf-8')
        if result.returncode:
            errors = [line for line in result.stdout.splitlines() if re.search(r'error(?:\([^)]*\))?:',line)]
            raise RuntimeError(f'Lean probe failed ({log_name}): ' + '\n'.join(errors[:12]))
        return result.stdout
    finally:
        scratch.unlink(missing_ok=True)


def eval_command(s):
    expr, kind = '('+s['expr']+')', s['kind']
    if kind == 'integer':
        value = f'pure (w4Nat {expr})'
    elif kind == 'rational':
        value = f'pure (w4Rat {expr})'
    elif kind == 'integer_list':
        value = f'pure (w4List ({expr}.map w4Nat))'
    elif kind == 'rational_list':
        value = f'pure (w4List ({expr}.map w4Rat))'
    elif kind == 'option_rational':
        value = f'w4Required {expr} w4Rat'
    elif kind == 'option_rational_list':
        value = f'w4Required {expr} (fun xs => w4List (xs.map w4Rat))'
    else:
        raise ValueError('Unknown extraction kind '+kind)
    return (f'#eval IO.FS.writeFile ".validate-logs/W4-progress.log" "{s["key"]}"\n'
            f'#eval do let value ← {value}; w4Emit "{s["key"]}" value')


def literal(s, value):
    if s['kind'].endswith('_list'):
        xs = json.loads(value)
        if not isinstance(xs, list) or not all(isinstance(x, str) for x in xs):
            raise ValueError('Malformed exact list '+s['key'])
        result = '['+','.join('('+x+':Rat)' if '/' in x else x for x in xs)+']'
    elif 'rational' in s['kind']:
        result = '('+value+':Rat)'
    else:
        result = value
    if s['kind'].startswith('option_'):
        result = 'some '+result
    return result


def dynamic_view(s, value, statement):
    if s['view'] == 'FORK_VIEW':
        # The source theorem's type contains projections of the fixed fork.
        # Substituting only these fields must be definitionally equal to that
        # same type; no logical inference or fresh identity schema is used.
        ids = json.loads(value)
        changed = statement
        for field, number in zip(('source','left','right'), ids, strict=True):
            changed = re.sub(re.escape(N+'.NativeFission.fork.')+field+r'\b',
                             f'(⟨{number}⟩ : CSTTT.CarrierId)', changed)
        return changed
    if s['view'] == 'TTS_VIEW':
        components = json.loads(value)
        vector = '(fun i => match i with '+''.join(
            f'| .{coordinate} => ({number}:Rat) '
            for coordinate,number in zip(('predictive','order','tick','progress','record'),components,strict=True))+')'
        return (f'CSTTT.RobustnessTheory.RawRationalMargin.eventAdvance {R}.model '
                f'({R}.input (fun _ => 0)) ({R}.ready (fun _ => 0)) '
                f'{P}.RouteId.a CSTTT.TargetTheory.ComputedFIACH.LaneDisturbance.nominal '
                f'{O}.Action.cw ({P}.Ambient.inK {O}.KState.p2w1) = some {vector}')
    if s['view']:
        return s['view'].replace('VALUE',literal(s,value))
    return '('+s['expr']+') = '+literal(s,value)


def canonical_value(kind, value):
    xs = json.loads(value) if kind.endswith('_list') else [value]
    for x in xs:
        if 'rational' in kind:
            if not re.fullmatch(r'-?(?:0|[1-9]\d*)/[1-9]\d*',x):
                raise ValueError('Noncanonical rational '+x)
            q = Fraction(x)
            if x != f'{q.numerator}/{q.denominator}':
                raise ValueError('Non-reduced rational '+x)
        elif not re.fullmatch(r'0|[1-9]\d*',x):
            raise ValueError('Noncanonical nonnegative integer '+x)


def build_snapshot():
    result_specs, candidates = specs(), candidate_specs()
    all_specs = result_specs+candidates
    if len({s['key'] for s in all_specs}) != len(all_specs):
        raise ValueError('Duplicate result keys')
    with LEDGER.open(newline='',encoding='utf-8') as stream:
        claims = {r['claim_id'] for r in csv.DictReader(stream)}
    for s in result_specs:
        if s['claim'] not in claims:
            raise ValueError('Missing ledger claim '+s['claim'])
    schema_pin = 'CSTTT.RealControls.ttn12_exists_for_every_horizon'
    pins = sorted({s['pin'] for s in result_specs}|{schema_pin}|
                  {name for s in result_specs for name in s['bridges']})
    source = make_probe(pins)+'\n'+PRELUDE+'\n'
    source += '\n'.join('#w4_statement '+pin for pin in pins)+'\n'
    # Independent refinement evaluations are bounded to two extra Lean jobs.
    # Their inputs and values remain identical; joining in this fixed order
    # makes the snapshot independent of worker scheduling.
    refinements = {'pos04_c3_trajectory','full_native_02_c3_trajectory'}
    source += '\n'.join(eval_command(s) for s in all_specs
                        if 'value_from' not in s and s['key'] not in refinements)+'\n'
    jobs = [(source,'W4-extraction-and-axioms.log')]
    jobs += [('import Lean\nimport CSTTT\n'+PRELUDE+'\n'+eval_command(s)+'\n',
              'W4-'+s['key']+'.log') for s in all_specs if s['key'] in refinements]
    with ThreadPoolExecutor(max_workers=3) as pool:
        logs = list(pool.map(lambda job:lean_run(*job),jobs))
    log = logs[0]
    trusted = {line.strip() for line in (ROOT/'lean/trust_base.txt').read_text().splitlines()
               if line.strip() and not line.lstrip().startswith('#')}
    if trusted != STANDARD_AXIOMS:
        raise ValueError('Unexpected Lean trust base')
    axiom_results = parse_probe(log,pins,trusted)
    for pin, item in axiom_results.items():
        if (not item['resolved'] or item['kind']!='theorem' or not item['axiom_reported']
                or item['untrusted_axioms'] or item['errors']):
            raise ValueError(f'Unresolved/nonstandard theorem pin {pin}: {item}')
    values, statements = {}, {}
    for line in '\n'.join(logs).splitlines():
        if line.startswith('W4_VALUE|'):
            obj = json.loads(line.split('|',1)[1])
            if obj['key'] in values:
                raise ValueError('Duplicate Lean value '+obj['key'])
            values[obj['key']] = obj['value']
        elif line.startswith('W4_STATEMENT|'):
            obj = json.loads(line.split('|',1)[1])
            statements[obj['name']] = obj['statement']
    for s in result_specs:
        if 'value_from' in s:
            # Reuse the freshly #eval-computed actual protocol mass. The second
            # kernel pass proves the law-gated readout equals some of THIS value;
            # no numerical RHS is extracted from a theorem's printed statement.
            origin = s['value_from']
            if origin not in values:
                raise ValueError('Missing evaluated source '+origin)
            values[s['key']] = values[origin]
    if set(values) != {s['key'] for s in all_specs} or set(statements)!=set(pins):
        raise ValueError('Incomplete fresh Lean extraction or statement probe')
    for s in all_specs:
        canonical_value(s['kind'],values[s['key']])
    # A second kernel pass checks value-fixing projections from the ORIGINAL
    # named pins, using literals obtained only from the first Lean evaluation.
    check = 'import Lean\nimport CSTTT\n'+PRELUDE+'\n'
    views = {}
    for idx,s in enumerate(result_specs):
        value = values[s['key']]
        view = dynamic_view(s,value,statements[s['pin']])
        views[s['key']] = view
        check += ('\nnamespace W4PinChecks\n'
                  f'theorem result_{idx} : {view} := by\n'
                  f'  have pinned := {s["pin"]}\n  {s["proof"]}\n'
                  'end W4PinChecks\n'
                  f'#print axioms W4PinChecks.result_{idx}\n')
    pin_log = lean_run(check,'W4-pin-check.log')
    for axioms in re.findall(r'depends on axioms:\s*\[([^]]*)\]',pin_log):
        found = {a.strip() for a in axioms.split(',') if a.strip()}
        if not found<=STANDARD_AXIOMS:
            raise ValueError('Nonstandard projection axioms '+repr(found))
    entries = []
    for s in result_specs:
        value = values[s['key']]
        # Check exact literal occurrences in the checked statement view. For
        # lists the check preserves element order in the generated equality.
        for part in json.loads(value) if s['kind'].endswith('_list') else [value]:
            if part not in views[s['key']]:
                raise ValueError('Checked pin view omits value '+s['key'])
        entries.append(dict(key=s['key'],value=value,claim_id=s['claim'],model=s['model'],
                            computed_by=s.get('computed_expr',s['expr']),pinned_by=s['pin'],description=s['description'],
                            value_type=s['kind'].removeprefix('option_'),
                            extraction='evaluated_via_protocol' if 'value_from' in s else 'evaluated',
                            **({'evaluation_source_key': s['value_from']} if 'value_from' in s else {}),
                            pinning=dict(axioms=axiom_results[s['pin']]['axioms'],
                                         bridge_theorems={n:axiom_results[n]['axioms'] for n in s['bridges']},
                                         theorem_statement=statements[s['pin']],
                                         checked_statement=views[s['key']],
                                         method='definitional_statement_view' if s['view'] else 'kernel_checked_projection')))
    return dict(artifact='CST-TT-09 paper result snapshot',schema_version='1.0.0',
                lean_toolchain=(ROOT/'lean/lean-toolchain').read_text().strip(),
                claim_ledger_sha256=hashlib.sha256(LEDGER.read_bytes()).hexdigest(),
                entries=entries,
                candidate_findings=[dict(key=s['key'],computed_by=s['expr'],
                                         observed_value=values[s['key']],reason=s['reason'],
                                         disposition='not_exported_missing_numeric_pin') for s in candidates],
                schemas=[dict(key='ttn12_countdown_failure',claim_id='TTN-12',pinned_by=schema_pin,
                              theorem_statement=statements[schema_pin],axioms=axiom_results[schema_pin]['axioms'],
                              disposition='universal_horizon_schema_not_numeric',
                              description='Failure at the successor of each finite horizon is a theorem schema; no finite horizon is selected.')])


def render_snapshot(snapshot):
    return json.dumps(snapshot,indent=2,ensure_ascii=False)+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Fresh Lean extraction and byte drift check')
    args = parser.parse_args()
    try:
        snapshot = build_snapshot()
        text = render_snapshot(snapshot)
        target = DATA/'current_results.json'
        if args.check:
            if not target.is_file() or target.read_text(encoding='utf-8')!=text:
                print('Result snapshot drift: rerun paper/tools/export_results.py',file=sys.stderr)
                return 1
        else:
            DATA.mkdir(exist_ok=True)
            target.write_text(text,encoding='utf-8')
        print(json.dumps(dict(entries=len(snapshot['entries']),
                              pins=len({e['pinned_by'] for e in snapshot['entries']}),
                              candidate_findings=snapshot['candidate_findings'],
                              check=args.check),ensure_ascii=False))
        return 0
    except (ValueError,RuntimeError,OSError,subprocess.TimeoutExpired) as exc:
        print(str(exc),file=sys.stderr)
        return 1


if __name__=='__main__':
    raise SystemExit(main())
