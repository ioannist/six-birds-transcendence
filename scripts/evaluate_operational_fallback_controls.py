#!/usr/bin/env python3
"""Replay the committed G13 operational controls with exact independent Python/Lean observations (class b)."""
import argparse
from copy import deepcopy
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODEL = 'audit/proposed_models/G13-OPERATIONAL-FALLBACK.model.json'
RESULTS = 'audit/evaluations/G13-OPERATIONAL-FALLBACK.results.json'
DECLARATION_COMMIT = '718649ccfd062113b11223a6de94115766fcc3df'

def fresh(store, key):
    return key not in store['read']


def initial(source, payload):
    return dict(read={source: dict(kind='source', payload=payload)},
                active={source: True}, edges=[], clock=0, captured={})


def step(store, command, decoder, max_age):
    op, *args = command
    result = deepcopy(store)
    if op == 'snapshot':
        source, record = args
        content = store['read'].get(source)
        if content is None or content['kind'] != 'source' or not store['active'].get(source, False) or not fresh(store, record):
            return None
        stamp = store['clock'] + 1
        payload = content['payload']
        result['read'][record] = dict(kind='record', origin=source, time=stamp, payload=payload)
        result['active'][record] = False
        result['edges'].insert(0, [source, record])
        result['clock'] = stamp
        result['captured'][record] = [source, stamp, payload]
    elif op == 'erase':
        source, = args
        content = store['read'].get(source)
        if content is None or content['kind'] != 'source' or not store['active'].get(source, False):
            return None
        result['active'][source] = False
        result['clock'] += 1
    elif op == 'gap':
        duration, = args
        result['clock'] += duration
    elif op == 'activate':
        record, target = args
        content = store['read'].get(record)
        if content is None or content['kind'] != 'record':
            return None
        source = content['origin']
        original = store['read'].get(source)
        if original is None or original['kind'] != 'source' or original['payload'] != content['payload']:
            return None
        if store['captured'].get(record) != [source, content['time'], content['payload']]:
            return None
        if decoder is None or content['time'] > store['clock'] or store['clock'] - content['time'] > max_age or not fresh(store, target):
            return None
        decoded = decoder[content['payload']]
        result['read'][target] = dict(kind='target', payload=decoded)
        result['active'][target] = True
        result['edges'].insert(0, [record, target])
        result['clock'] += 1
    elif op == 'independent':
        target, payload = args
        if not fresh(store, target):
            return None
        result['read'][target] = dict(kind='target', payload=payload)
        result['active'][target] = True
        result['clock'] += 1
    else:
        raise ValueError('undeclared operation ' + op)
    return result


def execute(case, decoder):
    if case['raw_source'] is None:
        return None
    store = initial(case['initial_source'], case['raw_source'])
    for command in case['commands']:
        store = step(store, command, decoder, case['max_age'])
        if store is None:
            return None
    return store


def reachable(edges, source, target):
    # Positive-length graph walks: equal endpoints do not supply reflexivity.
    queue = [last for first, last in edges if first == source]
    visited = set()
    while queue:
        node = queue.pop()
        if node == target:
            return True
        if node in visited:
            continue
        visited.add(node)
        queue.extend(last for first, last in edges if first == node)
    return False


def signature(state, state_order, classes):
    code = classes[state_order.index(state)]
    return [int(code == classes[index]) for index in range(len(state_order))]


def target_payload(store, address):
    content = store['read'].get(address)
    return content['payload'] if content is not None and content['kind'] == 'target' else None


def seed_decision(store, source, target, state_order, classes):
    original = store['read'].get(source)
    decoded = target_payload(store, target)
    if original is None or original['kind'] != 'source' or decoded is None:
        return None
    return reachable(store['edges'], source, target) and signature(original['payload'], state_order, classes) == signature(decoded, state_order, classes)


def whole_observation(case, store, state_order, classes):
    if store is None:
        return dict(execution_present=False, source_active=None, target_payload=None,
                    twin_payload=None, target_path=None, twin_path=None,
                    finite_target_signature_matches_source=None, derived_targets=None,
                    derived_paths=None, target_seed_decision=None, twin_seed_decision=None,
                    store=None)
    source = case['initial_source']
    target = target_payload(store, 2)
    twin = target_payload(store, 3)
    original = store['read'].get(source)
    pred = None if original is None or original['kind'] != 'source' or target is None else signature(original['payload'], state_order, classes) == signature(target, state_order, classes)
    derived = sorted(address for address, content in store['read'].items()
                     if content['kind'] == 'target' and reachable(store['edges'], source, address))
    return dict(execution_present=True, source_active=store['active'].get(source, False),
                target_payload=target, twin_payload=twin,
                target_path=reachable(store['edges'], source, 2), twin_path=reachable(store['edges'], source, 3),
                finite_target_signature_matches_source=pred, derived_targets=derived,
                derived_paths=[reachable(store['edges'], source, address) for address in derived],
                target_seed_decision=seed_decision(store, source, 2, state_order, classes),
                twin_seed_decision=seed_decision(store, source, 3, state_order, classes), store=store)


def split_observation(case, decoder):
    intervention = case['record_intervention']
    stop = intervention['insert_before_command']
    prefix_case = dict(case, commands=case['commands'][:stop])
    before = execute(prefix_case, decoder)
    changed = None
    if before is not None:
        content = before['read'].get(intervention['record'])
        if content is not None and content['kind'] == 'record':
            changed = deepcopy(before)
            changed['read'][intervention['record']] = dict(kind='record', origin=intervention['origin'],
                                                       time=intervention['time'], payload=intervention['payload'])
    activated = None if changed is None else step(changed, case['commands'][stop], decoder, case['max_age'])
    return dict(prefix_present=before is not None, intervention_present=changed is not None,
                checked_activation_present=activated is not None,
                journal_preserved=None if changed is None else changed['captured'] == before['captured'],
                graph_preserved=None if changed is None else changed['edges'] == before['edges'],
                before=before, changed=changed, activated=activated)



LEAN_HELPERS = '\nopen Lean\nopen CSTTT.Objecthood.T1Audit\nopen CSTTT.FallbackTheory.OperationalTrace\nopen CSTTT.FallbackTheory.SourceCheckedTrace\nopen CSTTT.FallbackTheory.SharedOperationalSeed\nopen CSTTT.FallbackTheory.RawPredictiveQuotient\nopen CSTTT.FallbackTheory.CachedSeed\n-- Class (b): exact declared finite state names, with no fallback state.\ndef stateName : KState → String\n  | .p0w0 => "p0w0" | .p0w1 => "p0w1" | .p1w0 => "p1w0" | .p1w1 => "p1w1"\n  | .p2w1 => "p2w1" | .p3w0 => "p3w0" | .p3w1 => "p3w1"\n  | .p4w0 => "p4w0" | .p4w1 => "p4w1" | .p5w0 => "p5w0"\n-- Class (b): only typed actual target reads yield target payloads.\ndef targetPayload (store : Store KState KState) (key : Nat) : Option KState := do\n  let .target payload ← store.read key | none\n  some payload\n-- Class (b): only typed actual source reads yield historical source payloads.\ndef sourcePayload (store : Store KState KState) (key : Nat) : Option KState := do\n  let .source payload ← store.read key | none\n  some payload\n-- Class (b): finite raw type contents are encoded directly, without verdict fields.\ndef contentJSON : Content KState KState → Json\n  | .source payload => Json.mkObj [("kind",toJson "source"),("payload",toJson (stateName payload))]\n  | .target payload => Json.mkObj [("kind",toJson "target"),("payload",toJson (stateName payload))]\n  | .record origin time payload => Json.mkObj [("kind",toJson "record"),("origin",toJson origin),("time",toJson time),("payload",toJson (stateName payload))]\n-- Class (b): actual optional stores are observed on the complete address range of this frozen finite suite.\ndef storeJSON : Option (Store KState KState) → Json\n  | none => Json.null\n  | some store =>\n      Json.mkObj [\n        ("read",Json.mkObj ((List.range 5).filterMap (fun key => (store.read key).map (fun content => (toString key,contentJSON content))))),\n        ("active",Json.mkObj ((List.range 5).filterMap (fun key => (store.read key).map (fun _ => (toString key,toJson (store.active key)))))),\n        ("edges",toJson (store.edges.map (fun edge => [edge.1,edge.2]))),("clock",toJson store.clock),\n        ("captured",Json.mkObj ((List.range 5).filterMap (fun key => (store.captured key).map (fun value =>\n          (toString key,Json.arr #[toJson value.1,toJson value.2.1,toJson (stateName value.2.2)])))))]\n-- Class (b): whole observations consume actual public checked execution and actual cached Seed/path/signature readouts.\ndef wholeReadout (inputs : RawInputs KState KState) : Json :=\n  match computedStore inputs with\n  | none => Json.mkObj [\n      ("execution_present",toJson false),("source_active",Json.null),("target_payload",Json.null),("twin_payload",Json.null),\n      ("target_path",Json.null),("twin_path",Json.null),("finite_target_signature_matches_source",Json.null),\n      ("derived_targets",Json.null),("derived_paths",Json.null),("target_seed_decision",Json.null),("twin_seed_decision",Json.null),("store",Json.null)]\n  | some store =>\n      let bridge := CSTTT.POS04.pos04RawBridge .positive\n      let target := targetPayload store 2\n      let twin := targetPayload store 3\n      let prediction := (sourcePayload store inputs.initialSource).bind (fun original => target.map (fun decoded =>\n        decide (sourceSignature bridge (classQueries bridge) original=targetSignature bridge (classQueries bridge) decoded)))\n      let derived := (List.range 5).filter (fun key => (targetPayload store key).isSome && pathBit store.edges inputs.initialSource key)\n      Json.mkObj [\n        ("execution_present",toJson true),("source_active",toJson (store.active inputs.initialSource)),\n        ("target_payload",toJson (target.map stateName)),("twin_payload",toJson (twin.map stateName)),\n        ("target_path",toJson (pathBit store.edges inputs.initialSource 2)),("twin_path",toJson (pathBit store.edges inputs.initialSource 3)),\n        ("finite_target_signature_matches_source",toJson prediction),("derived_targets",toJson derived),\n        ("derived_paths",toJson (derived.map (fun key => pathBit store.edges inputs.initialSource key))),\n        ("target_seed_decision",toJson (seedDecision bridge inputs inputs.initialSource 2)),\n        ("twin_seed_decision",toJson (seedDecision bridge inputs inputs.initialSource 3)),("store",storeJSON (some store))]\n-- Class (b): adversarial records are generated only by replacing an actual executed prefix record; journal/graph are actual readouts.\ndef splitReadout (inputs : RawInputs KState KState) (stop record origin time : Nat) (payload : KState) : Json :=\n  let before := computedStore { inputs with commands := inputs.commands.take stop }\n  let changed := before.bind (fun store => replaceRecord store record origin time payload)\n  let activated := changed.bind (fun store => (inputs.commands[stop]?).bind (fun command => checkedStep inputs.decoder inputs.maxAge store command))\n  let journal := before.bind (fun previous => changed.map (fun current =>\n    decide ((List.range 5).map previous.captured=(List.range 5).map current.captured)))\n  let graph := before.bind (fun previous => changed.map (fun current => decide (previous.edges=current.edges)))\n  Json.mkObj [("prefix_present",toJson before.isSome),("intervention_present",toJson changed.isSome),\n    ("checked_activation_present",toJson activated.isSome),("journal_preserved",toJson journal),("graph_preserved",toJson graph),\n    ("before",storeJSON before),("changed",storeJSON changed),("activated",storeJSON activated)]\n'

def verify_freeze():
    data = (ROOT / MODEL).read_bytes()
    for ref in (DECLARATION_COMMIT, 'HEAD'):
        if subprocess.check_output(['git', 'show', ref + ':' + MODEL], cwd=ROOT) != data:
            raise ValueError('operational declaration must remain identical to committed G13')
    subprocess.run(['git', 'merge-base', '--is-ancestor', DECLARATION_COMMIT, 'HEAD'], cwd=ROOT, check=True)
    model = json.loads(data)
    for path, digest in model['source_sha256'].items():
        raw = (ROOT / path).read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest or raw != subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=ROOT):
            raise ValueError('pinned raw source drift: ' + path)
    order = model['state_order']
    names = ['p0w0','p0w1','p1w0','p1w1','p2w1','p3w0','p3w1','p4w0','p4w1','p5w0']
    if order != names or dict(model['identity_decoder_table']) != {name: name for name in names}:
        raise ValueError('frozen state/decoder coverage drift')
    classes = re.search(r'def mClasses : List Nat := \[([^\]]+)\]', (ROOT / 'lean/CSTTT/Objecthood/T1Audit.lean').read_text())
    if classes is None:
        raise ValueError('pinned M-class transcription absent')
    classes = [int(value) for value in classes[1].split(',')]
    if len(classes) != len(order):
        raise ValueError('complete raw state/class coverage mismatch')
    cases = model['cases']
    if len(cases) != 26 or len({c['case_id'] for c in cases}) != 26:
        raise ValueError('complete declared control coverage drift')
    for case in cases:
        if type(case['initial_source']) is not int or case['initial_source'] not in range(5):
            raise ValueError('initial address outside complete observation range')
        if case['raw_source'] is not None and case['raw_source'] not in order:
            raise ValueError('undeclared raw state')
        decoder = case['decoder']
        if decoder is not None and decoder != 'identity' and not (isinstance(decoder,dict) and set(decoder)=={'constant'} and decoder['constant'] in order):
            raise ValueError('undeclared raw decoder')
        if type(case['max_age']) is not int or case['max_age'] < 0:
            raise ValueError('invalid raw age')
        for command in case['commands']:
            op,*args=command
            if op in ('snapshot','activate'):
                addresses=args
            elif op=='erase':
                addresses=args
            elif op=='gap':
                addresses=[]
                if len(args)!=1 or type(args[0]) is not int or args[0]<0:
                    raise ValueError('invalid gap duration')
            elif op=='independent':
                if len(args)!=2 or args[1] not in order:
                    raise ValueError('invalid independent raw payload')
                addresses=args[:1]
            else:
                raise ValueError('undeclared operation')
            arity={'snapshot':2,'activate':2,'erase':1,'gap':1,'independent':2}[op]
            if len(args)!=arity or any(type(key) is not int or key not in range(5) for key in addresses):
                raise ValueError('operation outside complete five-address observation range')
        if case['phase']=='split_actual_prefix_intervention_suffix':
            intervention=case['record_intervention']
            if intervention['record'] not in range(5) or intervention['origin'] not in range(5) or intervention['payload'] not in order:
                raise ValueError('intervention outside declared address/state domain')
            if type(intervention['time']) is not int or intervention['time']<0:
                raise ValueError('invalid intervention timestamp')
            stop=intervention['insert_before_command']
            if type(stop) is not int or not 0<=stop<len(case['commands']) or case['commands'][stop][0]!='activate':
                raise ValueError('intervention must precede an actual activation command')
        elif case['phase']!='whole':
            raise ValueError('undeclared phase')
    return model,classes


def python_observations(model, classes):
    order=model['state_order']
    identity=dict(model['identity_decoder_table'])
    values=[]
    for case in model['cases']:
        raw=case['decoder']
        decoder=None if raw is None else identity if raw=='identity' else {state:raw['constant'] for state in order}
        actual=whole_observation(case,execute(case,decoder),order,classes) if case['phase']=='whole' else split_observation(case,decoder)
        values.append(dict(case_id=case['case_id'],phase=case['phase'],actual=actual))
    # JSON normalization converts actual Nat dictionary keys exactly like Lean encoding.
    return json.loads(json.dumps(values))


def lean_command(command):
    op,*args=command
    return '.'+op+' '+' '.join('.'+value if isinstance(value,str) else str(value) for value in args)


def lean_input(case):
    source='none' if case['raw_source'] is None else 'some .'+case['raw_source']
    raw=case['decoder']
    decoder='none' if raw is None else 'some id' if raw=='identity' else 'some (fun _ => .'+raw['constant']+')'
    commands=','.join(lean_command(c) for c in case['commands'])
    return '({initialSource := '+str(case['initial_source'])+',rawSource := '+source+',decoder := '+decoder+',maxAge := '+str(case['max_age'])+',commands := ['+commands+']} : RawInputs KState KState)'


def lean_observations(model):
    folder=ROOT/'lean/.validate-logs'/('operational-fallback-controls-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S-%fZ'))
    folder.mkdir(parents=True)
    calls=[]
    for case in model['cases']:
        if case['phase']=='whole':
            readout='G13OperationalReadback.wholeReadout '+lean_input(case)
        else:
            i=case['record_intervention']
            readout='G13OperationalReadback.splitReadout '+lean_input(case)+' '+' '.join(str(i[k]) for k in ('insert_before_command','record','origin','time'))+' .'+i['payload']
        calls.append('Lean.Json.mkObj [("case_id",Lean.toJson '+json.dumps(case['case_id'])+'),("phase",Lean.toJson '+json.dumps(case['phase'])+'),("actual",'+readout+')]')
    source='import Lean\nimport CSTTT.Fallback.CachedSeed\nimport CSTTT.POS04.GenericTransport\n\nnamespace G13OperationalReadback'+LEAN_HELPERS+'end G13OperationalReadback\nopen Lean CSTTT.Objecthood.T1Audit CSTTT.FallbackTheory.SharedOperationalSeed\n#eval IO.println (Lean.Json.compress (Lean.Json.arr #['+',\n'.join(calls)+']))\n'
    probe=folder/'readback.lean'
    probe.write_text(source)
    completed=subprocess.run(['lake','env','lean',str(probe.relative_to(ROOT/'lean'))],cwd=ROOT/'lean',text=True,capture_output=True)
    log=folder/'lean.log'
    log.write_text(completed.stdout+completed.stderr)
    if completed.returncode:
        raise RuntimeError('Lean readback failed; retained log: '+str(log))
    arrays=[json.loads(line) for line in completed.stdout.splitlines() if line.startswith('[{')]
    if len(arrays)!=1 or len(arrays[0])!=len(model['cases']):
        raise ValueError('expected exactly one complete26 Lean observation array')
    return arrays[0],hashlib.sha256(probe.read_bytes()).hexdigest(),str(folder.relative_to(ROOT))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-results',action='store_true',help='write exact observations and frozen prediction outcomes')
    args=parser.parse_args()
    model,classes=verify_freeze()
    python=python_observations(model,classes)
    lean,probe_sha,receipt=lean_observations(model)
    controls=[]
    for case,left,right in zip(model['cases'],python,lean,strict=True):
        if left['case_id']!=case['case_id'] or right['case_id']!=case['case_id'] or right['phase']!=case['phase']:
            raise ValueError('declared control order/phase drift')
        prediction=case['frozen_prediction']
        if not all(key in left['actual'] for key in prediction):
            raise ValueError('prediction consumes absent observation field')
        controls.append(dict(case_id=case['case_id'],phase=case['phase'],exact_match=left==right,
                             frozen_prediction=prediction,prediction_holds=all(left['actual'][key]==expected for key,expected in prediction.items()),
                             python=left['actual'],lean=right['actual']))
    report=dict(schema='CST-TT G13 exact operational fallback observations v1',classification='b',
                declaration_sha256=hashlib.sha256((ROOT/MODEL).read_bytes()).hexdigest(),declaration_commit=DECLARATION_COMMIT,
                raw_sources=model['source_sha256'],generated_lean_sha256=probe_sha,
                proof_boundary='Exact finite actual source-checked execution, record interventions, positive-length paths and tri-state Seed. Full package, native autonomy and scientific Gamma/IAPS remain kernel construction obligations.',
                controls=controls)
    failures=[c['case_id'] for c in controls if not c['exact_match'] or not c['prediction_holds']]
    if failures:
        raise SystemExit('FAIL retained frozen predictions/comparisons: '+', '.join(failures)+'; '+receipt)
    if args.write_results:
        destination=ROOT/RESULTS
        destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_text(json.dumps(report,indent=2)+'\n')
    elif report!=json.loads((ROOT/RESULTS).read_text()):
        raise ValueError('frozen exact result drift; fresh log: '+receipt)
    print('PASS all26 exact raw operational Python/Lean observations and frozen predictions; no scientific TTF promotion')


if __name__=='__main__':
    main()
