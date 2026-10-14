#!/usr/bin/env python3
"""Check actual heterogeneous corridor chain, seam and staged-context controls."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / 'audit/proposed_models/TTH07-RAW-CORRIDOR-SEQUENCE.model.json'
PROBE = r'''
import Lean
import CSTTT.Targets.GenericHandoff.AcquisitionSupportRange
import CSTTT.Targets.GenericHandoff.StagedCorridorSequenceModels
open CSTTT.TargetTheory.GenericHandoff
open RegisterInterpreter RawCorridorSequenceModels
example : RawCorridorSequence.Readout canonical requests := positive
example : ¬ RawCorridorSequence.Readout cut requests := missing_right
example : ¬ RawCorridorSequence.Readout canonical wrongRequests := wrong_clock_no_readout
example : ¬ RawCorridorSequence.Readout unfunded requests := unfunded_no_readout
example : ¬ RawCorridorSequence.Readout canonical loopRequests := loop_no_readout
example : RawCorridorSequence.Readout (StagedCorridorSequenceModels.span StagedCorridorSequenceModels.original)
  StagedCorridorSequenceModels.requests := StagedCorridorSequenceModels.positive
example : ¬ RawCorridorSequence.Readout (StagedCorridorSequenceModels.span StagedCorridorSequenceModels.original)
  StagedCorridorSequenceModels.reusedRequests := StagedCorridorSequenceModels.reused_no_readout
example (a : Assignment Bool Value) :
  RawCorridorSequence.chain a requests =
    (RawCorridorSequence.leg (request left) a).bind (fun l =>
      (RawCorridorSequence.leg (request right) a).map (fun r => [l,r])) := by
  simp only [requests, RawCorridorSequence.chain]
  cases RawCorridorSequence.leg (request left) a <;>
    cases RawCorridorSequence.leg (request right) a <;> rfl
example (a : Assignment (Sum Bool Bool) (StagedAssignmentSpan.JointValue Value Value)) :
  RawCorridorSequence.Readout a (requests.map (CorridorCellReindex.request Sum.inr (fun _ x => x))) ↔
    RawCorridorSequence.Readout (CellReindex.pullback Sum.inr (fun _ x => x) a) requests :=
  CorridorCellReindex.chain_semantic_iff Sum.inr (fun _ x => x) requests a
def profile (qs : List (RawCorridorSequence.Request Bool Value)) (a : Assignment Bool Value) : Lean.Json :=
  Lean.toJson ((RawCorridorSequence.chain a qs).map (fun ls => ls.map (fun l =>
    (l.source,l.target,l.stages.map (fun s => (s.frontier.order,s.support,s.frontier.residue))))))
def flagList (v : Input) := [v.receiver.sourcePresent,v.receiver.targetFunded,v.receiver.funded,v.receiver.mixedRequired]
def eventData (e : AcquisitionExecution.Event LocalStage) : Lean.Json := Lean.Json.mkObj [
 ("from",Lean.toJson e.fromStage.val),("to",Lean.toJson e.toStage.val),
 ("sourceSupport",Lean.toJson e.sourceSupport),("targetSupport",Lean.toJson e.targetSupport),
 ("strict",Lean.toJson e.strictStep),("atomic",Lean.toJson e.atomic),("advance",Lean.toJson e.orderAdvance)]
def instructionData (side : Bool) : Lean.Json :=
 let raw := acquisition side
 Lean.Json.mkObj [
 ("initial",Lean.toJson ((raw.initializer ()).eval canonical RegisterInitialization.noRegisters ())),
 ("historyLength",Lean.toJson ((raw.histories.read canonical).map (fun hs => (hs ()).length))),
 ("updateAt7",Lean.toJson ((raw.execution.program ()).eval canonical (fun _ => 7) ((),(),()))),
 ("receiveAt7",Lean.toJson ((raw.receive ()).eval canonical (fun _ => 7) ((),()))),
 ("row",Lean.toJson ((raw.execution.row.eval canonical (fun _ => 7) ((),())).map (fun rs => rs.map (fun e => (e.2.num,e.2.den))))),
 ("responsePresent",Lean.toJson (raw.arrivalResponse.eval canonical (fun _ => 7) ((),())).isSome),
 ("domainLengths",Lean.toJson [raw.execution.disturbances.length,raw.execution.actions.length,raw.execution.outcomes.length])]
#eval IO.println (Lean.Json.compress (Lean.Json.mkObj [
 ("carriers", Lean.toJson [leftSource,middleCarrier,finalTarget]),
 ("offsets", Lean.toJson [0,rightOffset]), ("brokenOffset", Lean.toJson brokenOffset),
 ("viewCells", Lean.toJson [left.acquisition.events.cell,right.acquisition.events.cell]),
 ("stages", Lean.toJson (stageList.map Fin.val)),
 ("paths", Lean.toJson [leftInput.routes () |>.path,rightInput.routes () |>.path]),
 ("histories", Lean.toJson [leftInput.seeds.history (),rightInput.seeds.history ()]),
 ("seeds", Lean.toJson [leftInput.seeds.predictive (),rightInput.seeds.predictive ()]),
 ("flags", Lean.toJson [flagList leftInput,flagList rightInput]),
 ("realized",Lean.toJson [leftInput.realized.map Fin.val,rightInput.realized.map Fin.val]),
 ("events",Lean.Json.mkObj [("false",eventData (event false)),("true",eventData (event true))]),
 ("instructions",Lean.Json.arr #[instructionData false,instructionData true]),
 ("names",Lean.toJson [[left.names.entry,left.names.event false,left.names.event true],
   [right.names.entry,right.names.event false,right.names.event true]]),
 ("cover",Lean.toJson [StagedCorridorSequenceModels.cover.indices.length,(StagedCorridorSequenceModels.cover.scopes ()).length]),
 ("coverScope",Lean.toJson (StagedCorridorSequenceModels.cover.scopes ())),
 ("coverAdjacent",Lean.toJson (StagedCorridorSequenceModels.cover.adjacent () ())),
 ("profile",profile requests canonical),
 ("seam",Lean.toJson (RawCorridorSequence.seams canonical requests)),
 ("brokenSeam",Lean.toJson (RawCorridorSequence.seams canonical wrongRequests)),
 ("loopSeam",Lean.toJson (RawCorridorSequence.seams canonical loopRequests)),
 ("missing",profile requests cut),
 ("funding",Lean.toJson rightInput.receiver.targetFunded),
 ("unfunded",Lean.toJson ((unfunded true).map (fun x => x.receiver.targetFunded))),
 ("loopTarget",Lean.toJson loopRight.schema.target.code),
 ("middleHistory",Lean.toJson ((StagedCorridorSequenceModels.middle StagedCorridorSequenceModels.original true).map (fun x => x.seeds.history ()))),
 ("finalHistory",Lean.toJson ((StagedCorridorSequenceModels.finalCells StagedCorridorSequenceModels.original true).map (fun x => x.seeds.history ()))),
 ("stagedSeam",Lean.toJson (RawCorridorSequence.seams (StagedCorridorSequenceModels.span StagedCorridorSequenceModels.original) StagedCorridorSequenceModels.requests)),
 ("reuseSeam",Lean.toJson (RawCorridorSequence.seams (StagedCorridorSequenceModels.span StagedCorridorSequenceModels.original) StagedCorridorSequenceModels.reusedRequests))
]))
'''

def compare(model, observed):
    fixed = {
        'grade': 'actual raw acquisition corridor chain, not full Temporal-FIACH',
        'stage_each': 'Fin 3', 'cell_type': 'Bool', 'register_each': 'Unit -> Nat',
        'disturbance_action_outcome_history_route_each': 'Unit', 'event_each': 'Bool',
        'clock_rule': 'offset + local stage value', 'source_initializer': 0,
        'source_program': 'register unit + 1', 'source_history': [['unit','unit','unit']],
        'source_row': [['unit',1]], 'receiver_program': 'register unit', 'seed_predictive_each': 0,
        'funding_each': {'sourcePresent': True,'targetFunded': True,'funded': True,'mixedRequired': True},
        'staged_binding': {'source_raw_cells': {'false': 'leftInput','true': 'leftInput'},
          'first_instruction': 'identity',
          'second_instruction': 'append left-mix,left-exit to true cell seed history; false cell unchanged',
          'cover_each': {'indices': ['unit'],'scope': [False,True]},
          'reuse_control': 'read right request from middle branch instead of final branch'},
    }
    for k,v in fixed.items():
        if model[k] != v:
            raise ValueError(f'raw instruction/interface drift: {k}')
    if model['events'] != {'false': {'from':0,'to':1,'sourceSupport':True,'targetSupport':True,'advance':1},
                           'true': {'from':1,'to':2,'sourceSupport':False,'targetSupport':True,'advance':1}}:
        raise ValueError('event instruction drift')
    carriers, offsets, seeds, names = model['carriers'], model['clock_offsets'], model['seed_histories'], model['names']
    profile=[]
    for j,side in enumerate(['left','right']):
        src,tgt=carriers[j:j+2]
        ns=names[side]
        profile.append([src,[tgt,[[offsets[j],[[src],seeds[j]]],
          [offsets[j]+1,[[src,tgt],seeds[j]+[ns[1]]]],
          [offsets[j]+2,[[tgt],seeds[j]+[ns[1],ns[2]]]]]]])
    c=model['controls']
    if c['missing_right_cell'] is not True:
        raise ValueError('missing primitive selector drift')
    expected={
      'carriers':carriers,'offsets':offsets,'brokenOffset':c['broken_right_clock_offset'],
      'viewCells':[model['raw_view_cells']['left'],model['raw_view_cells']['right']],
      'stages':model['realized_each'],'paths':[model['paths_each']]*2,'histories':seeds,'profile':profile,
      'seam':True,'brokenSeam':False,'loopSeam':True,'missing':None,'funding':True,
      'unfunded':c['right_target_unfunded'],'loopTarget':c['loop_right_target'],
      'middleHistory':seeds[0],'finalHistory':seeds[1],'stagedSeam':True,'reuseSeam':False,
      'seeds':[model['seed_predictive_each']]*2,
      'flags':[[model['funding_each'][k] for k in ['sourcePresent','targetFunded','funded','mixedRequired']]]*2,
      'realized':[model['realized_each']]*2,
      'events':{k:dict(v,strict=True,atomic=True) for k,v in model['events'].items()},
      'names':[names['left'],names['right']], 'cover':[1,2],
      'coverScope':model['staged_binding']['cover_each']['scope'], 'coverAdjacent':True,
      'instructions':[{'initial':model['source_initializer'],
         'historyLength':len(model['source_history']), 'updateAt7':8, 'receiveAt7':7,
         'row':[[model['source_row'][0][1],1]], 'responsePresent':True,'domainLengths':[1,1,1]}]*2,
    }
    if observed != expected:
        raise ValueError(f'actual raw chain mismatch: expected {expected}, observed {observed}')

def main():
    with tempfile.TemporaryDirectory(prefix='tth07-raw-corridor-') as directory:
        p=Path(directory)/'Probe.lean';p.write_text(PROBE)
        run=subprocess.run(['lake','env','lean',str(p)],cwd=ROOT/'lean',capture_output=True,text=True)
        if run.returncode:
            raise RuntimeError(run.stdout+run.stderr)
        observed=json.loads(run.stdout.strip())
    model=json.loads(MODEL.read_text());compare(model,observed)
    mutations=[
      ('physical middle carrier', lambda m: m['carriers'].__setitem__(1,56)),
      ('middle clock',lambda m:m['clock_offsets'].__setitem__(1,3)),
      ('prior path residue',lambda m:m['seed_histories'][1].__setitem__(1,'corrupted')),
      ('staged context reuse',lambda m:m['staged_binding'].__setitem__('second_instruction','identity')),
      ('predictive seed',lambda m:m.__setitem__('seed_predictive_each',8)),
    ]
    for label,mutate in mutations:
        drift=copy.deepcopy(model);mutate(drift)
        try:compare(drift,observed)
        except ValueError:print(f'CAUGHT planted {label} drift')
        else:raise AssertionError(f'missed planted {label} drift')
    print('PASS actual heterogeneous raw corridor chain, full declared raw parameter observations, staged assignment seam, direct missing/clock/funding/loop/context-reuse controls; five planted drifts caught')
    print('Scope: corridor geometry and raw parent/adjacency construction; supported execution, runtime seed coherence, funded runtime lineage and full Temporal-FIACH remain')
if __name__=='__main__':main()
