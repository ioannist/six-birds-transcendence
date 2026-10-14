#!/usr/bin/env python3
"""Compare raw supported-sequence instructions and compile exact semantic probes."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / 'audit/proposed_models/TTH07-SUPPORTED-ACQUISITION-SEQUENCE.model.json'
PROBE = r'''
import Lean
import CSTTT.Targets.GenericHandoff.SupportedAcquisitionSequenceModels
open CSTTT.TargetTheory.GenericHandoff
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence SupportedAcquisitionSequenceModels
open RawCorridorSequenceModels
example : Readout firstRaw secondRaw boundary left.schema right.schema canonical () () () () := positive
example : ¬ Readout firstRaw wrongInitial boundary left.schema right.schema canonical () () () () := wrong_initial_no_readout
example : ¬ Readout firstRaw (zeroWeight true 2) boundary left.schema right.schema canonical () () () () := zero_next_no_readout
example : ¬ Readout (zeroWeight false 0) secondRaw boundary left.schema right.schema canonical () () () () := zero_first_no_readout
example (a : Assignment Bool Value) (hm : a true = none) :
 ¬ Readout firstRaw secondRaw boundary left.schema right.schema a () () () () := missing_right_no_readout a hm
example (a : Assignment Bool Value) :
 Readout stagedFirst stagedSecond stagedBoundary left.schema right.schema (stagedSpan a) () () () () ↔
 Readout firstRaw secondRaw boundary left.schema right.schema (CellReindex.pullback select jointValue (stagedSpan a)) () () () () := staged_readout_iff a
example : Readout stagedFirst stagedSecond stagedBoundary left.schema right.schema
 (stagedSpan StagedCorridorSequenceModels.original) () () () () := staged_positive
example (a : Assignment Bool Value) : ¬ Readout stagedFirst stagedSecond stagedBoundary left.schema right.schema
 (put (stagedSpan a) (.inr true) none) () () () () := staged_missing_final a
example (hf : Ready firstRaw canonical) (hs : Ready secondRaw canonical) (hb : RegisterSubstitution.Ready boundary canonical) :
 nextEntry firstRaw secondRaw boundary canonical hf hs hb () () () () = some (run 4) := next_entry_equation 2 hf hs hb
example (o u : Bool) : ¬ Readout normalizedBranch normalizedBranch boundary left.schema right.schema canonical () () o u := normalized_branch_no_readout o u
example (a : Assignment Bool Value) (x : Registers Unit (fun _ => Nat)) :
 StrategyGame.Normalized (rows normalizedBranch a) x () () := normalized_branch_row a x
example (a : Assignment Bool Value) (h : Ready normalizedBranch a) (x : Registers Unit (fun _ => Nat)) :
 supportedFold normalizedBranch a h x [((),(),false)] = some (update normalizedBranch a h x () () false) := normalized_branch_has_alternative a h x
abbrev NRaw := Raw Bool Value Unit (fun _ => Nat) Unit Unit Unit LocalStage Bool Unit Unit
/-- Finite observation interpreter executes the same raw expressions. Kernel
probes above establish the corresponding noncomputable state equations. -/
def pureFold (raw : NRaw) (a : Assignment Bool Value) : Nat → List (Unit × Unit × Unit) → Option Nat
 | n, [] => some n
 | n, (d,act,o)::rest => do
   if stepCheck raw a (run n) d act o then
     let next ← (raw.execution.program ()).eval a (run n) (d,act,o)
     pureFold raw a next rest
   else none
def pureArrival (raw : NRaw) (a : Assignment Bool Value) (start : Nat) : Option Nat := do
 let routes ← raw.routes.read a
 let histories ← raw.histories.read a
 let source ← pureFold raw a start (histories (routes ()).history)
 (raw.receive ()).eval a (run source) ((routes ()).history,())
def pureExit (raw : NRaw) (a : Assignment Bool Value) (arrived : Nat) : Option Nat := do
 let routes ← raw.routes.read a
 let da ← raw.arrivalResponse.eval a (run arrived) ((routes ()).history,())
 if stepCheck raw a (run arrived) da.1 da.2 () then
   (raw.execution.program ()).eval a (run arrived) (da.1,da.2,()) else none
def pureFirst (raw : NRaw) (a : Assignment Bool Value) : Option Nat := do
 let n ← (raw.initializer ()).eval a RegisterInitialization.noRegisters ()
 let arrived ← pureArrival raw a n
 pureExit raw a arrived
def pureNext (first second : NRaw) (a : Assignment Bool Value) : Option Nat := do
 let actual ← pureFirst first a
 let middle ← (boundary ()).eval a (run actual) ()
 let arrived ← pureArrival second a middle
 pureExit second a arrived
def rawData (raw : NRaw) : Lean.Json := Lean.Json.mkObj [
 ("initial",Lean.toJson ((raw.initializer ()).eval canonical RegisterInitialization.noRegisters ())),
 ("historyLength",Lean.toJson ((raw.histories.read canonical).map (fun hs => (hs ()).length))),
 ("row",Lean.toJson ((raw.execution.row.eval canonical (run 7) ((),())).map (fun rs => rs.map (fun e => [e.2.num,e.2.den])))),
 ("updateAt7",Lean.toJson ((raw.execution.program ()).eval canonical (run 7) ((),(),()))),
 ("receiveAt7",Lean.toJson ((raw.receive ()).eval canonical (run 7) ((),()))),
 ("responsePresent",Lean.toJson (raw.arrivalResponse.eval canonical (run 7) ((),())).isSome),
 ("viewCell",Lean.toJson raw.events.cell),
 ("domainLengths",Lean.toJson [raw.execution.disturbances.length,raw.execution.actions.length,raw.execution.outcomes.length])]
def label : Sum Bool Bool → String | .inl k => if k then "middle.true" else "middle.false" | .inr k => if k then "final.true" else "final.false"
#eval IO.println (Lean.Json.compress (Lean.Json.mkObj [
 ("raw",Lean.Json.arr #[rawData firstRaw,rawData secondRaw]),
 ("boundaryAt7",Lean.toJson ((boundary ()).eval canonical (run 7) ())),
 ("firstArrival",Lean.toJson (pureArrival firstRaw canonical 0)),
 ("firstEntry",Lean.toJson (pureFirst firstRaw canonical)),
 ("nextArrival",Lean.toJson ((pureFirst firstRaw canonical).bind (pureArrival secondRaw canonical))),
 ("nextEntry",Lean.toJson (pureNext firstRaw secondRaw canonical)),
 ("wrongInitial",Lean.toJson ((wrongInitial.initializer ()).eval canonical RegisterInitialization.noRegisters ())),
 ("wrongComputed",Lean.toJson (pureNext firstRaw wrongInitial canonical)),
 ("wrongIndependentArrival",Lean.toJson (pureArrival wrongInitial canonical 0)),
 ("zeroWeight",Lean.toJson (((zeroWeight true 2).execution.row.eval canonical (run 7) ((),())).map (fun rs => rs.map (fun e => e.2.num)))),
 ("zeroFirst",Lean.toJson (pureFirst (zeroWeight false 0) canonical)),
 ("zeroNext",Lean.toJson (pureNext firstRaw (zeroWeight true 2) canonical)),
 ("missing",Lean.toJson (pureNext firstRaw secondRaw cut)),
 ("stageSelectors",Lean.toJson [label stagedFirst.events.cell,label stagedSecond.events.cell]),
 ("stagedBoundaryReads",Lean.toJson ((stagedBoundary ()).dependencies.map label)),
 ("normalizedRow",Lean.toJson ((normalizedBranch.execution.row.eval canonical (run 7) ((),())).map (fun rs => rs.map (fun e => (e.1,[e.2.num,e.2.den]))))),
 ("normalizedAssignedWord",Lean.toJson ((normalizedBranch.histories.read canonical).map (fun hs => (hs ()).map (fun e => e.2.2)))),
 ("normalizedTrueSupport",Lean.toJson (stepCheck normalizedBranch canonical (run 7) () () true)),
 ("normalizedFalseSupport",Lean.toJson (stepCheck normalizedBranch canonical (run 7) () () false))
]))
'''
def compare(m, observed):
    fixed={'grade':'actual supported acquisition continuation, not full Temporal-FIACH',
      'raw_cell':'Bool','register':'Unit->Nat','D_A_O_H_Route':'Unit','Stage':'Fin3','Id':'Bool',
      'updater':'register+1','receiver':'identity','boundary':'identity actual first post-exit entry',
      'raw_views':'existing RawCorridorSequenceModels canonical; independent seed0 is not runtime seed coherence',
      'stage_binding':{'primitive_contexts':'existing identity then append-prior-path raw stages',
        'selector':{'false':'middle.inl.false','true':'final.inr.true'},
        'first':'firstRaw with whole raw cell reindexing','second':'secondRaw with whole raw cell reindexing',
        'boundary':'raw identity instruction reindexed','control':'delete consumed final.inr.true cell'},
      'normalized_branch_control':{'outcome':'Bool','history':[True],'row':[[False,1],[True,0]],'initial':0,
        'updater':'register+1 independent of outcome','receive':'identity',
        'routes_events_funding':'existing canonical Bool raw views','alternative_supported_history':[False]},
    }
    for k,v in fixed.items():
        if m[k]!=v:raise ValueError(f'raw instruction/interface drift: {k}')
    if m['history_each']!=[['unit','unit','unit']] or m['row_each']!=[['unit',1]] or m['controls']['consumed_missing']!='true':
        raise ValueError('assigned word/row/missing selector drift')
    raw=[]
    for initial,cell in [(m['first_initial'],False),(m['second_initial'],True)]:
        raw.append({'initial':initial,'historyLength':len(m['history_each']), 'row':[[m['row_each'][0][1],1]],
          'updateAt7':8,'receiveAt7':7,'responsePresent':True,'viewCell':cell,'domainLengths':[1,1,1]})
    n=m['first_initial']; c=m['controls']; bc=m['normalized_branch_control']
    expected={'raw':raw,'boundaryAt7':7,'firstArrival':n+1,'firstEntry':n+2,'nextArrival':n+3,'nextEntry':n+4,
      'wrongInitial':c['wrong_second_initial'],'wrongComputed':n+4,'wrongIndependentArrival':c['wrong_second_initial']+1,
      'zeroWeight':[c['second_zero_weight']],'zeroFirst':None,'zeroNext':None,'missing':None,
      'stageSelectors':['middle.false','final.true'],'stagedBoundaryReads':[],
      'normalizedRow':[[e[0],[e[1],1]] for e in bc['row']], 'normalizedAssignedWord':bc['history'],
      'normalizedTrueSupport':False,'normalizedFalseSupport':True}
    if observed!=expected:raise ValueError(f'actual supported sequence mismatch: expected {expected}, observed {observed}')
def main():
    with tempfile.TemporaryDirectory(prefix='tth07-supported-sequence-') as directory:
        p=Path(directory)/'Probe.lean';p.write_text(PROBE)
        r=subprocess.run(['lake','env','lean',str(p)],cwd=ROOT/'lean',capture_output=True,text=True)
        if r.returncode:raise RuntimeError(r.stdout+r.stderr)
        observed=json.loads(r.stdout.strip())
    m=json.loads(MODEL.read_text());compare(m,observed)
    changes=[('next initializer',lambda x:x.__setitem__('second_initial',0)),
      ('middle boundary operation',lambda x:x.__setitem__('boundary','constant0')),
      ('selected history',lambda x:x['normalized_branch_control'].__setitem__('history',[False])),
      ('positive support weight',lambda x:x['controls'].__setitem__('second_zero_weight',1)),
      ('staged primitive selector',lambda x:x['stage_binding']['selector'].__setitem__('true','middle.inl.true'))]
    for label,mutate in changes:
        drift=copy.deepcopy(m);mutate(drift)
        try:compare(drift,observed)
        except ValueError:print(f'CAUGHT planted {label} drift')
        else:raise AssertionError(f'missed planted {label} drift')
    print('PASS actual supported acquisition instructions, computed 0->2->3->4 sequence, exact staged readout adapter and direct initializer/weight/missing/normalized-alternative controls; five planted drifts caught')
    print('Scope: supported selected histories and chosen outcomes; complete Temporal-FIACH, runtime seed/clock/funded-route/final autonomy composition remain')
if __name__=='__main__':main()
