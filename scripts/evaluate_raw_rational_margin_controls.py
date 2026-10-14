#!/usr/bin/env python3
"""Untuned exact evaluation of committed operational rational-margin controls.

Python interprets the old released JSON raw data independently. Lean evaluates
raw expression substitution, including partial registers, for comparison.
The theorem-valued whole gates are reserved for the following kernel bridge;
this evaluation reports their executable source/staging components and actual
receiver reset readouts rather than inventing a computable whole-gate verdict.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone
from fractions import Fraction as F
from pathlib import Path
import evaluate_fiach_pos04 as old_raw

ROOT = Path(__file__).resolve().parents[1]
DECLARATION = 'audit/proposed_models/G11-RAW-RATIONAL-MARGINS.model.json'
BASE = 'audit/proposed_models/FIACH-POS-04.model.json'
COORDINATES = ('predictive', 'order', 'tick', 'progress', 'record')
MISSING = {
    'canonical': None,
    'Assigned.put canonical (positions) none': 'positions',
    'Assigned.put canonical (rows Tag.source) none': 'rows',
    'Assigned.put canonical (writers) none': 'writers',
    'Assigned.put canonical (maintenance) none': 'maintenance',
}
CELLS = {'positions': '.positions', 'rows': '(.rows Tag.source)',
         'writers': '.writers', 'maintenance': '.maintenance'}

# Class (b): exact representations and independent raw evaluator, no verdict inputs.
def rational(value):
    return None if value is None else f'{value.numerator}/{value.denominator}'


def verify_freeze():
    data = (ROOT/DECLARATION).read_bytes()
    committed = subprocess.check_output(['git', 'show', 'HEAD:'+DECLARATION], cwd=ROOT)
    if data != committed:
        raise ValueError('declaration must be committed before evaluation and remain frozen')
    manifest = json.loads(data)
    if manifest['baseline'] != {
            'model': 'POS04FinalHandoff.raw (POS04ResourceRuntime.protocol baseline)',
            'source_assignment': 'CSTTT.POS04.Assigned.canonical',
            'history': 'RouteId.a', 'disturbance': 'LaneDisturbance.nominal',
            'action': 'Action.cw', 'outcome': 'Ambient.inK KState.p2w1'}:
        raise ValueError('unsupported declared baseline context')
    for path in (BASE, 'scripts/evaluate_fiach_pos04.py',
                 'lean/CSTTT/Robustness/RawRationalMargin.lean',
                 'lean/CSTTT/Robustness/RationalRegisters.lean',
                 'lean/CSTTT/Robustness/ExactFiveMargins.lean'):
        if (ROOT/path).read_bytes() != subprocess.check_output(
                ['git', 'show', 'HEAD:'+path], cwd=ROOT):
            raise ValueError('committed evaluator/source dependency drift: '+path)
    if len(manifest['controls']) != 24 or len({c['id'] for c in manifest['controls']}) != 24:
        raise ValueError('frozen control coverage drift')
    for case in manifest['controls']:
        if case['model'] not in ('baseline', 'POS04FinalHandoff.constant'):
            raise ValueError('unknown raw model variant')
        if case['source_assignment'] not in MISSING:
            raise ValueError('unknown raw source mutation')
        if case['correction'] is not None and set(case['correction']) != set(COORDINATES):
            raise ValueError('missing or extra correction coordinate')
    for path, sha in manifest['base_source_sha256'].items():
        if hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != sha:
            raise ValueError('declared old raw source drift: '+path)
    return manifest


def profile(base, state):
    if state not in base['t1_import']['kernel_order']:
        return ('exit', state)
    # The concrete owning target is image=exchangeAssignment: its .source
    # cells come from the original .target cells. No frozen primitive changes.
    source = base['new_data']['raw_inputs']['by_tag']['target']
    hazards = base['t1_import']['hazards']
    # Eager original profile keeps outcome order from the raw rows.
    rows = tuple(tuple(int(o[1]) in hazards and int(o[3]) == int(o[1]) % 2
                       for o in source['action_distributions'][state][act])
                 for act in base['t1_import']['actions'])
    return (base['t1_import']['public_f'][base['t1_import']['kernel_order'].index(state)], rows)


def independent_case(base, case, baseline_checks):
    missing = MISSING[case['source_assignment']]
    radius = F(case['radius_each'])
    delta = None if case['correction'] is None else {k:F(case['correction'][k]) for k in COORDINATES}
    route = next(r for r in base['new_data']['corridor']['paths'] if r['id'] == 'route_a')
    history = base['new_data']['histories'][route['source_history']]
    initial = history[0]
    destination = 'p2w1'
    source = base['new_data']['raw_inputs']['by_tag']['target']
    profiles = list(dict.fromkeys(profile(base, s) for s in base['t1_import']['kernel_order']))
    before = {'predictive':F(profiles.index(profile(base, initial))),
              'order':F(0), 'tick':F(0), 'progress':F(0), 'record':F(0)}
    ledger = base['new_data']['maintenance']
    initial_funded = base['new_data']['receiver']['latent_target']['funded_receiver']
    after_funded = initial_funded and max(0, ledger['initial_budget_tokens']-ledger['action_cost_tokens']) + ledger['recharge_tokens_per_action'] > 0
    writer = source['record_writer_available'][route['id']]
    after = {'predictive':F(profiles.index(profile(base, destination))),
             'order':F(1), 'tick':F(source['tick_increment'][initial]['cw']),
             'progress':F(1), 'record':F(int(after_funded and writer))}
    if missing == 'positions':
        before['predictive'] = after['predictive'] = None
    if missing == 'writers':
        before['record'] = after['record'] = None
    if missing == 'maintenance':
        after['record'] = None
    raw_advance = {k:None if before[k] is None or after[k] is None else after[k]-before[k] for k in COORDINATES}
    extended_after = {k:None if delta is None or after[k] is None else after[k]+delta[k] for k in COORDINATES}
    advance = None if any(v is None for v in before.values()) or any(v is None for v in extended_after.values()) else {k:extended_after[k]-before[k] for k in COORDINATES}
    rows = None if missing == 'maintenance' else [[o,F(w)] for o,w in source['action_distributions'][initial]['cw'].items()]
    if rows is not None and not (initial_funded and source['resources']['recharge_available_after_withdrawal'] and ledger['initial_budget_tokens'] >= ledger['action_cost_tokens']):
        rows=[]
    weight = None if rows is None else sum((w for o,w in rows if o == destination),F(0))
    supported = rows is not None and any(o == destination and w > 0 for o,w in rows)
    # Actual raw receiver initializer factor for the two released counterfactuals.
    receiver = ['p0w0', 'p0w0' if case['model'] == 'POS04FinalHandoff.constant' else 'p1w0']
    baseline_slack = {k:None if raw_advance[k] is None else raw_advance[k]-radius for k in COORDINATES}
    return {'before':{k:rational(v) for k,v in before.items()},
            'after':{k:rational(v) for k,v in extended_after.items()},
            'advance':None if advance is None else {k:rational(v) for k,v in advance.items()},
            'program_ready':missing != 'maintenance' and delta is not None,
            'event_ready':missing in (None, 'rows') and delta is not None,
            'row':None if rows is None else [[o,rational(w)] for o,w in rows],
            'supported':supported,'outcome_weight':rational(weight),
            'source_package_check':missing is None and baseline_checks[0],
            'staging_check':missing is None and baseline_checks[1],
            'receiver_factor_pair':receiver,
            'within_box':delta is not None and all(-radius<=v<=radius for v in delta.values()),
            'certified_slack':all(v is not None and v-radius>0 for v in raw_advance.values()),
            'all_five_positive':advance is not None and all(v>0 for v in advance.values()),
            'worst_case_slack':{k:rational(v) for k,v in baseline_slack.items()}}


LEAN_BASE = r'''
import CSTTT.Robustness.RawRationalMargin
import CSTTT.Targets.GenericHandoff.POS04FinalHandoff
import CSTTT.Targets.GenericHandoff.RegisterSubstitution
import Lean
namespace G11RawEvaluation
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.GenericHandoff CSTTT.TargetTheory.ComputedFIACH
open RegisterInterpreter RegisterInitialization RegisterSubstitution
open CSTTT.RobustnessTheory ExactFiveMargins RationalRegisters
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
private def baselineModel : POS04FinalHandoff.Model := POS04FinalHandoff.raw (POS04ResourceRuntime.protocol baseline)
private def constantModel : POS04FinalHandoff.Model := POS04FinalHandoff.constant
-- Class (b): derived receipt must equal both ACTUAL raw source/staging checks.
private structure CheckedPair (source : CSTTT.POS04.Assigned.Assignment) where
  value : Bool × Bool
  correct : value=(sourcePackageCheck {baseline with assignment := source},
    stagedPreservationCheck {baseline with assignment := source})
-- Class (b): actual canonical pair derived from released raw clause/assembly proofs.
private theorem canonical_checks_eq :
    (sourcePackageCheck baseline,stagedPreservationCheck baseline)=(true,true) := by
  apply Prod.ext
  · simp only [sourcePackageCheck,Bool.and_eq_true,decide_eq_true_eq,package_check_iff]
    exact ⟨canonical_complete _,canonical_assigned_package .source⟩
  · simp only [stagedPreservationCheck,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨⟨canonical_complete _,canonical_assigned_package .source⟩,package_lane_positive⟩
-- Class (b): every partial assignment and every deleted primitive, BOTH actual checks.
private theorem deleted_checks_eq (a : CSTTT.POS04.Assigned.Assignment) (k : Cell) :
    (sourcePackageCheck {baseline with assignment := Assigned.put a k none},
     stagedPreservationCheck {baseline with assignment := Assigned.put a k none})=(false,false) := by
  have h : ¬ CSTTT.POS04.Assigned.Complete primitiveCells (Assigned.put a k none) := by
    intro ready
    have hk := ready k (primitive_cells_complete k)
    simp [Assigned.put_same] at hk
  apply Prod.ext <;> simp [sourcePackageCheck,stagedPreservationCheck,h]
-- Class (b): cached representation is accompanied by exact kernel correspondence.
private def canonicalChecks : CheckedPair canonical := ⟨(true,true),canonical_checks_eq.symm⟩
-- Class (b): no cache fallback; proof covers every partial source and deleted primitive.
private def deletedChecks (a : CSTTT.POS04.Assigned.Assignment) (k : Cell) :
    CheckedPair (Assigned.put a k none) := ⟨(false,false),(deleted_checks_eq a k).symm⟩
private def positionsChecks := deletedChecks canonical .positions
private def rowsChecks := deletedChecks canonical (.rows Tag.source)
private def writersChecks := deletedChecks canonical .writers
private def maintenanceChecks := deletedChecks canonical .maintenance
private def coords : List ExactFiveMargins.Coordinate := [.predictive,.order,.tick,.progress,.record]
private def coordName : ExactFiveMargins.Coordinate → String
 | .predictive => "predictive" | .order => "order" | .tick => "tick" | .progress => "progress" | .record => "record"
private def obj := Json.mkObj
private def rat (r : Rat) := toJson s!"{r.num}/{r.den}"
private def optRat : Option Rat → Json | none => Json.null | some r => rat r
private def vector (v : ExactFiveMargins.Coordinate → Option Rat) := obj (coords.map fun i => (coordName i,optRat (v i)))
private def registers : List POS04RegisterDynamics.Register := [.factor,.counter,.ticks,.residue,.funded]
private def extendedRegisters : List (LiftRegister POS04RegisterDynamics.Register) :=
 registers.map .base ++ coords.map .offset
private def beforeExpr (m : POS04FinalHandoff.Model) (i : ExactFiveMargins.Coordinate) :=
 substitute (fun r => ((RawRationalMargin.initializer m) r).reenv (fun (_ : Unit) => RouteId.a))
   ((RawRationalMargin.observer m i).reenv (fun (_ : Unit) => ()))
private def afterExpr (m : POS04FinalHandoff.Model) (i : ExactFiveMargins.Coordinate) :=
 substitute (fun r => ((RawRationalMargin.initializer m) r).reenv (fun (_ : Unit) => RouteId.a))
   (substitute (fun r => ((RawRationalMargin.program m) r).reenv
      (fun (_ : Unit) => (LaneDisturbance.nominal,Action.cw,Ambient.inK KState.p2w1)))
     ((RawRationalMargin.observer m i).reenv (fun (_ : Unit) => ())))
private def stateName : Ambient → String
 | .inK s => CSTTT.POS04.stateName s | .p2w0 => "p2w0" | .p5w1 => "p5w1"
private def oldDependencies (m : POS04FinalHandoff.Model) :=
 let f := m.base.frames.sourceFrame
 f.acquisition.dependencies ++
 registers.flatMap (fun r => (f.acquisition.initializer r).dependencies) ++
 f.acquisition.execution.row.dependencies ++
 registers.flatMap (fun r => (f.acquisition.execution.program r).dependencies) ++
 registers.flatMap (fun r => (f.acquisition.receive r).dependencies) ++ f.readouts.dependencies
private def observed (m : POS04FinalHandoff.Model) (source : CSTTT.POS04.Assigned.Assignment)
    (correction : Option Vector) (radius : Rat) (checks : CheckedPair source) : Json := Id.run do
 let input : RawRationalMargin.Input Cell Value := ⟨source,correction⟩
 let target := RawRationalMargin.target m input
 let before := fun i => (beforeExpr m i).eval target noRegisters ()
 let after := fun i => (afterExpr m i).eval target noRegisters ()
 let advance : Option Vector := do
   let x ← RawRationalMargin.readVector before
   let y ← RawRationalMargin.readVector after
   pure fun i => y i-x i
 let rawBefore := fun i => (substitute (fun r => (m.base.frames.sourceFrame.acquisition.initializer r).reenv (fun (_ : Unit) => RouteId.a))
   ((RawRationalMargin.originalObserver m i).reenv (fun (_ : Unit) => ()))).eval (OwningHandoff.target m.base source) noRegisters ()
 let rawAfter := fun i => (substitute (fun r => (m.base.frames.sourceFrame.acquisition.initializer r).reenv (fun (_ : Unit) => RouteId.a))
   (substitute (fun r => (m.base.frames.sourceFrame.acquisition.execution.program r).reenv
      (fun (_ : Unit) => (LaneDisturbance.nominal,Action.cw,Ambient.inK KState.p2w1)))
     ((RawRationalMargin.originalObserver m i).reenv (fun (_ : Unit) => ())))).eval (OwningHandoff.target m.base source) noRegisters ()
 let rawAdvance := fun i => do let x ← rawBefore i; let y ← rawAfter i; pure (y-x)
 let row := (substitute (fun r => ((RawRationalMargin.initializer m) r).reenv (fun (_ : Unit) => RouteId.a))
   ((RawRationalMargin.row m).reenv (fun (_ : Unit) => (LaneDisturbance.nominal,Action.cw)))).eval target noRegisters ()
 let weight := row.map fun xs => ((xs.filter (fun e => e.1 == Ambient.inK KState.p2w1)).map Prod.snd).sum
 let receiver := [POS04ReceiverContent.inputA,POS04ReceiverContent.inputB].map fun input =>
   RegisterInitialization.evaluate m.receiver.receiver.resetProgram (OwningHandoff.target m.base source) input .factor
 return obj [
   ("before",vector before),("after",vector after),
   ("advance",match advance with | none => Json.null | some v => vector (fun i => some (v i))),
   ("program_ready",toJson (extendedRegisters.all fun r => ((RawRationalMargin.program m) r).dependencies.all fun k => (target k).isSome)),
   ("event_ready",toJson ((oldDependencies m).all (fun k => ((OwningHandoff.target m.base source) k).isSome) && correction.isSome)),
   ("row",match row with | none => Json.null | some xs => Json.arr (xs.map (fun e => Json.arr #[toJson (stateName e.1),rat e.2])).toArray),
   ("supported",toJson (row.any fun xs => xs.any fun e => e.1 == Ambient.inK KState.p2w1 && decide (0<e.2))),
   ("outcome_weight",optRat weight),
   ("source_package_check",toJson checks.value.1),("staging_check",toJson checks.value.2),
   ("receiver_factor_pair",Json.arr (receiver.map (fun v => match v with | none => Json.null | some s => toJson (stateName s))).toArray),
   ("within_box",toJson (correction.any fun v => coords.all fun i => decide (-radius<=v i ∧ v i<=radius))),
   ("certified_slack",toJson (coords.all fun i => (rawAdvance i).any fun v => decide (v-radius>0))),
   ("all_five_positive",toJson (advance.any fun v => coords.all fun i => decide (v i>0))),
   ("worst_case_slack",vector (fun i => (rawAdvance i).map (fun v => v-radius)))]
'''


def lean_rat(value):
    v=F(value)
    return f'({v.numerator} : Rat)/{v.denominator}'


def lean_probe(manifest):
    entries=[]
    for c in manifest['controls']:
        missing=MISSING[c['source_assignment']]
        source='canonical' if missing is None else f'(Assigned.put canonical {CELLS[missing]} none)'
        model='constantModel' if c['model']=='POS04FinalHandoff.constant' else 'baselineModel'
        delta='none' if c['correction'] is None else '(some (fun i => match i with '+' '.join(f'| .{k} => {lean_rat(c["correction"][k])}' for k in COORDINATES)+'))'
        checks='canonicalChecks' if missing is None else missing+'Checks'
        entries.append('('+json.dumps(c['id'])+',observed '+model+' '+source+' '+delta+' ('+lean_rat(c['radius_each'])+') '+checks+')')
    names=re.findall(r'^private (?:def|theorem|structure) (\w+)', LEAN_BASE, re.M)
    prints='\n'.join('#print axioms '+name for name in names)
    return LEAN_BASE+'\n'+prints+'\n#eval IO.println (Json.compress (obj ['+','.join(entries)+']))\nend G11RawEvaluation\n'


def run_lean(probe):
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    path=ROOT/'lean/.validate-logs'/f'g11b-raw-computed-readback-{stamp}.lean'
    path.write_text(probe)
    print('Lean raw readback probe: '+str(path.relative_to(ROOT)),flush=True)
    result=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT/'lean',capture_output=True,text=True)
    (path.with_suffix('.log')).write_text(result.stdout+result.stderr)
    if result.returncode:
        raise RuntimeError(result.stdout+result.stderr)
    allowed={'propext','Quot.sound','Classical.choice'}
    axioms={a.strip() for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]', result.stdout, re.S)
            for a in group.split(',') if a.strip()}
    if not axioms<=allowed or 'sorryAx' in result.stdout:
        raise ValueError('untrusted generated evaluator/cache axioms: '+str(sorted(axioms)))
    return json.loads(result.stdout.strip().splitlines()[-1])


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-results',action='store_true')
    args=parser.parse_args()
    manifest=verify_freeze()
    base=json.loads((ROOT/BASE).read_text())
    old=old_raw.evaluate(base)
    baseline_checks=(old['source_package'],old['staged']['pass'])
    expected={c['id']:independent_case(base,c,baseline_checks) for c in manifest['controls']}
    actual=run_lean(lean_probe(manifest))
    if expected!=actual:
        (ROOT/'lean/.validate-logs/g11b-mismatch.json').write_text(json.dumps({'python':expected,'lean':actual},indent=2)+'\n')
        raise ValueError('independent raw/readout mismatch: '+','.join(k for k in expected if expected[k]!=actual.get(k)))
    results={'schema':'csttt-g11b-raw-rational-margin-evaluation-v1',
        'declaration_sha256':hashlib.sha256((ROOT/DECLARATION).read_bytes()).hexdigest(),
        'declaration_commit':subprocess.check_output(['git','log','-1','--format=%H','--',DECLARATION],cwd=ROOT,text=True).strip(),
        'classification':'b','cases':actual,
        'whole_gate_scope':'No executable whole-gate verdict supplied. Source/staging checks and actual receiver factor collisions are evaluated; exact original F/O and receiver semantic witnesses/refutations require the following kernel bridge.',
        'coverage':'Every frozen control, exact Fraction/Rat arithmetic, actual interpreted before/after optional reads, rows/support/duplicate aggregation, consumed-cell absence; no tuning or new physical robustness claim.'}
    row_control = actual['missing_rows_Tag_source']
    if row_control['advance'] is not None and row_control['event_ready']:
        results['control_findings'] = [{
            'id': 'missing_rows_Tag_source',
            'declared_check': 'actual_missing_consumed_expression_none',
            'verdict': 'REFUTED',
            'reason': 'The owning target is exchangeAssignment. Its source row is the original target row, which remains present. The full original source package and staging checks reject, but the actual extended numeric event remains ready and positive. No raw primitive or control is changed.'}]
    else:
        results['control_findings'] = []
    path=ROOT/'audit/G11b_raw_rational_margin_results.json'
    if args.write_results:
        path.write_text(json.dumps(results,indent=2)+'\n')
    elif json.loads(path.read_text())!=results:
        raise ValueError('separately frozen evaluation result drift')
    print('PASS exact transcription comparison for all 24 frozen controls: Python equals Lean raw-expression evaluation.')
    for finding in results['control_findings']:
        print(f"Retained {finding['verdict']} frozen check: {finding['id']} / {finding['declared_check']}.")
    print('Whole theorem-valued gates require the subsequent kernel bridge; no status promotion.')


if __name__=='__main__':
    main()
