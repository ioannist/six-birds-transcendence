#!/usr/bin/env python3
"""Exact untuned G12 native control evaluation; class (b).

Independent Python interprets the frozen raw publication/mode/resource recipe.
Lean executes the actual public optional expressions, with a kernel-proved
correspondence to the original checked supported-entry implementation.
Whole package, resource closure, retention/greatestness and all-time return
are theorem obligations; numerical observations are not their proof caches.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DECLARATION = 'audit/proposed_models/G12-RAW-NATIVE-RECHARGE.model.json'
RESULTS = 'audit/evaluations/G12-RAW-NATIVE-RECHARGE.results.json'
FACTORS = list(itertools.product((False, True), repeat=3))
RECIPES = {
    'canonical': 'canonical',
    'selected_native_arm_none': 'nativeMissing',
    'selected_supplement_arm_none': 'supplementMissing',
    'other_bundle_none': 'otherMissing',
    'selected_current_recharge_zero': 'rechargeZero',
    'selected_current_owner_source': 'ownerSource',
    'selected_current_writers_false': 'writersFalse',
    'selected_current_rows_zero': 'rowsZero',
}

def rational(value):
    value = Fraction(value)
    return [value.numerator, value.denominator]


def raw_input(owner):
    # NativeComposition.Factor.factorData + AvailabilityFactor.input.
    return dict(owner=owner, recharge_available=True, initial=1, cost=1,
                recharge=1, source_copies=2, receiver_funded=True,
                writers=True, rows_zero=False)


def publish(data):
    result = deepcopy(data)
    result['owner'] = not result['owner']
    result['source_copies'] *= 2
    return result


def canonical_assignment():
    # fromArms(staged initial): actual first and second publications.
    original = raw_input(False)
    first = publish(original)
    second = publish(first)
    return {True: (deepcopy(first), deepcopy(original)),
            False: (deepcopy(second), deepcopy(first))}


def assignment(cell, recipe):
    data = canonical_assignment()
    if recipe in ('selected_native_arm_none', 'selected_supplement_arm_none'):
        # fromArms is a two-read Option bind, so either missing arm deletes bundle.
        data[cell] = None
    elif recipe == 'other_bundle_none':
        data[not cell] = None
    elif recipe != 'canonical':
        current = data[cell][0]
        if recipe == 'selected_current_recharge_zero':
            current['recharge'] = 0
        elif recipe == 'selected_current_owner_source':
            current['owner'] = not cell
        elif recipe == 'selected_current_writers_false':
            current['writers'] = False
        elif recipe == 'selected_current_rows_zero':
            current['rows_zero'] = True
        else:
            raise ValueError('undeclared primitive recipe: ' + recipe)
    return data


def initialize(source, cell, history):
    copies = source['source_copies']
    start = 0 if cell else 2
    return dict(factor=list(history), progress=start, ticks=start,
                past=[list(history) for _ in range(copies)], path=[False, True],
                funded=source['receiver_funded'] and source['recharge_available']
                and source['initial'] >= source['cost'], mode=not cell)


def active(pair, cell, state):
    return pair[0] if state['mode'] == cell else pair[1]


def rows(data, state, action):
    enabled = state['funded'] and data['recharge_available'] and data['initial'] >= data['cost']
    if not enabled or data['rows_zero'] or (action and not state['factor'][1]):
        return []
    destination = list(state['factor'])
    if action and destination[1]:
        destination[0] = not destination[0]
    return [[destination, rational(1)]]


def update(data, state, outcome):
    result = deepcopy(state)
    result['factor'] = list(outcome)
    result['progress'] += 1  # raw schema.stageAdvance
    result['ticks'] += 1  # raw data.ticks for every factor/action
    # Lean Nat subtraction in budgetAfter, rather than signed subtraction.
    budget_after = max(data['initial'] - data['cost'], 0) + data['recharge']
    result['funded'] = state['funded'] and budget_after > 0
    return result


def receive(current, state, cell):
    result = deepcopy(state)
    result['past'] += deepcopy(state['past'])
    result['funded'] = state['funded'] and current['recharge_available'] and current['initial'] >= current['cost']
    result['mode'] = cell
    return result


def writer(data, state):
    # Actual registerTuple/first route match, including whole copied history and path.
    matching_route = any(state['past'] == [list(h)] * data['source_copies']
                         and state['path'] == [False, True] for h in FACTORS)
    return matching_route and data['writers']


def record(data, state):
    return state['progress'] if state['funded'] and writer(data, state) else 0


def native_accounts(pair, cell, state):
    data = active(pair, cell, state)
    names = {False: 17, True: 55} if cell else {True: 55, False: 101}
    return [dict(resource=False, owner=None, retained=False, balance=0),
            dict(resource=True, owner=names[data['owner']], retained=state['mode'] == cell,
                 balance=data['initial'] if state['funded'] else 0)]


def native_charge(pair, cell, state):
    data = active(pair, cell, state)
    names = {False: 17, True: 55} if cell else {True: 55, False: 101}
    return dict(owner=names[data['owner']], used=[True] if state['mode'] == cell else [],
                debit=[0, data['cost']], credit=[0, data['recharge']])


def composed_initializer(pair, cell, history, require_support):
    current, source = pair
    state = initialize(source, cell, history)
    # PublicationReplay.copies - 1, fixed before evaluation.
    source_steps = (2 if cell else 4) - 1
    for _ in range(source_steps):
        data = active(pair, cell, state)
        if require_support and [list(history), rational(1)] not in rows(data, state, False):
            return None
        state = update(data, state, history)
    state = receive(current, state, cell)
    data = active(pair, cell, state)
    if require_support and [list(history), rational(1)] not in rows(data, state, False):
        return None
    return update(data, state, history)


def selected_response(pair, cell, history, action):
    initialized = composed_initializer(pair, cell, history, False)
    test = deepcopy(initialized)
    test['progress'] = test['ticks'] = 0
    data = active(pair, cell, test)
    charge = native_charge(pair, cell, test)
    before_record = record(data, test)
    branches = []
    for outcome in FACTORS:
        next_state = update(data, test, outcome)
        next_data = active(pair, cell, next_state)
        branches.append(dict(outcome=list(outcome), destination=next_state['factor'],
                             progressIncrement=max(next_state['progress'] - test['progress'], 0),
                             recordIncrement=max(record(next_data, next_state) - before_record, 0),
                             debit=rational(charge['debit'][1]), credit=rational(charge['credit'][1])))
    return dict(action=action, owner=charge['owner'], rows=rows(data, test, action), branches=branches)


def observed(case):
    cell = case['owner']
    pair = assignment(cell, case['assignment_recipe'])[cell]
    result = dict(id=case['id'], initialized=None, supportedEntry=None, decode=None,
                  response=None, writer=None, sourcePresent=None, accounts=None, charge=None)
    if pair is None:
        return result
    state = composed_initializer(pair, cell, case['history'], False)
    data = active(pair, cell, state)
    accounts = native_accounts(pair, cell, state)
    result.update(initialized=state, supportedEntry=composed_initializer(pair, cell, case['history'], True),
                  decode=dict(factor=state['factor'], progress=state['progress'], record=record(data, state),
                              balance=rational(accounts[1]['balance'])),
                  response=selected_response(pair, cell, case['history'], case['selected_action']),
                  writer=writer(data, state), sourcePresent=state['mode'] == (not cell),
                  accounts=accounts, charge=native_charge(pair, cell, state))
    return result


LEAN_HELPERS = r"""
def factorJson (h : Factor) : Lean.Json := Lean.toJson [h.1,h.2.1,h.2.2]
def ratJson (r : Rat) : Lean.Json := Lean.toJson [r.num,(r.den : Int)]
def stateJson (x : ModeExecution.State) : Lean.Json := Lean.Json.mkObj [
  ("factor",factorJson x.1.factor),("progress",Lean.toJson x.1.counter),("ticks",Lean.toJson x.1.ticks),
  ("past",Lean.Json.arr (x.1.residue.1.map factorJson).toArray),("path",Lean.toJson x.1.residue.2),
  ("funded",Lean.toJson x.1.funded),("mode",Lean.toJson x.2)]
def eventJson (x : CSTTT.AutonomyTheory.RawRechargingPolicy.EventState Factor) : Lean.Json := Lean.Json.mkObj [
  ("factor",factorJson x.factor),("progress",Lean.toJson x.progress),("record",Lean.toJson x.record),("balance",ratJson x.balance)]
def responseJson (r : CSTTT.AutonomyTheory.RawRechargingPolicy.Response Factor Bool Factor) : Lean.Json := Lean.Json.mkObj [
  ("action",Lean.toJson r.action),("owner",Lean.toJson r.owner.code),
  ("rows",Lean.Json.arr (r.rows.map (fun e => Lean.Json.arr #[factorJson e.1,ratJson e.2])).toArray),
  ("branches",Lean.Json.arr (factors.map (fun o => let b := r.branch o; Lean.Json.mkObj [
    ("outcome",factorJson o),("destination",factorJson b.destination),("progressIncrement",Lean.toJson b.progressIncrement),
    ("recordIncrement",Lean.toJson b.recordIncrement),("debit",ratJson b.debit),("credit",ratJson b.credit)])).toArray)]
def optionalJson {X : Type} (f : X → Lean.Json) : Option X → Lean.Json
  | none => .null
  | some x => f x
def observed (id : String) (cell : Owner) (h : Factor) (variant : Mutation) (act : Bool) : Lean.Json :=
  let a := assignment cell variant
  let initialized := evaluate (entryInitializer cell) a h ()
  let decoded := initialized.bind (fun x => CSTTT.AutonomyTheory.NativePolicyBridge.decodeNative (native cell) true a (ModeExecution.pack x))
  let response := ((responseView cell act).read a).map (fun f => f h ())
  let accounts := initialized.bind (fun x => (native cell).accounts.eval a (ModeExecution.pack x) ())
  let charge := initialized.bind (fun x => (native cell).charge.eval a (ModeExecution.pack x) ((),act))
  let writer := initialized.bind (fun x => (native cell).writer.eval a (ModeExecution.pack x) ())
  let absent := initialized.bind (fun x => (native cell).sourcePresent.eval a (ModeExecution.pack x) ())
  Lean.Json.mkObj [
    ("id",Lean.toJson id),("initialized",optionalJson stateJson initialized),
    ("supportedEntry",optionalJson stateJson (supportedEntry cell a h)),("decode",optionalJson eventJson decoded),
    ("response",optionalJson responseJson response),("writer",Lean.toJson writer),("sourcePresent",Lean.toJson absent),
    ("accounts",optionalJson (fun accounts => Lean.Json.arr ([false,true].map (fun res => let v := accounts res;
      Lean.Json.mkObj [("resource",Lean.toJson res),("owner",Lean.toJson (v.owner.map (fun c => c.code))),
        ("retained",Lean.toJson v.retained),("balance",Lean.toJson v.balance)])).toArray) accounts),
    ("charge",optionalJson (fun c => Lean.Json.mkObj [("owner",Lean.toJson c.owner.code),("used",Lean.toJson c.used),
      ("debit",Lean.toJson ([false,true].map c.debit)),("credit",Lean.toJson ([false,true].map c.credit))]) charge)]
"""


def verify_freeze():
    data = (ROOT / DECLARATION).read_bytes()
    if data != subprocess.check_output(['git', 'show', 'HEAD:' + DECLARATION], cwd=ROOT):
        raise ValueError('G12 declaration must be committed before evaluation and remain frozen')
    model = json.loads(data)
    for path, digest in model['raw_sources'].items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != digest:
            raise ValueError('frozen raw source drift: ' + path)
    controls = model['controls']
    if len(controls) != 32 or len({c['id'] for c in controls}) != 32:
        raise ValueError('declared control coverage drift')
    for case in controls:
        if case['assignment_recipe'] not in RECIPES or tuple(case['history']) not in FACTORS:
            raise ValueError('undeclared primitive recipe/domain')
    return model


def lean_observations(model):
    folder = ROOT / 'lean/.validate-logs' / ('native-recharge-controls-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S-%fZ'))
    folder.mkdir(parents=True)
    calls = []
    for case in model['controls']:
        owner = str(case['owner']).lower()
        hist = '(' + ','.join(str(x).lower() for x in case['history']) + ')'
        action = str(case['selected_action']).lower()
        calls.append('NativeRechargeEvaluator.observed ' + json.dumps(case['id']) + ' ' + owner + ' ' + hist + ' .' + RECIPES[case['assignment_recipe']] + ' ' + action)
    source = 'import CSTTT.Autonomy.NativeRecharge\n\nnamespace NativeRechargeEvaluator\nopen CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization\nopen NativeComposition CSTTT.AutonomyTheory.NativeRecharge CSTTT.AutonomyTheory.NativeRechargeControls\n' + LEAN_HELPERS + '\nend NativeRechargeEvaluator\n#eval IO.println (Lean.Json.compress (Lean.Json.arr #[' + ',\n'.join(calls) + ']))\n'
    probe = folder / 'readback.lean'
    probe.write_text(source)
    completed = subprocess.run(['lake', 'env', 'lean', str(probe.relative_to(ROOT / 'lean'))], cwd=ROOT / 'lean', text=True, capture_output=True)
    (folder / 'lean.log').write_text(completed.stdout + completed.stderr)
    if completed.returncode:
        raise RuntimeError('Lean readback failed; retained log: ' + str(folder / 'lean.log'))
    arrays = [json.loads(line) for line in completed.stdout.splitlines() if line.startswith('[{')]
    if len(arrays) != 1 or len(arrays[0]) != 32:
        raise ValueError('expected exactly one complete32 Lean observation array')
    return arrays[0], str(folder.relative_to(ROOT)), hashlib.sha256(probe.read_bytes()).hexdigest()


def prediction(case, value):
    recipe = case['assignment_recipe']
    if recipe in ('selected_native_arm_none', 'selected_supplement_arm_none'):
        return all(value[k] is None for k in value if k != 'id')
    if value['initialized'] is None or value['response'] is None:
        return False
    response = value['response']
    target = 55 if case['owner'] else 101
    if recipe == 'canonical' and case['selected_action']:
        return response['rows'] == [] and value['supportedEntry'] == value['initialized']
    if recipe in ('canonical', 'other_bundle_none'):
        if value['supportedEntry'] != value['initialized'] or not value['initialized']['funded']:
            return False
        if value['decode']['record'] != value['decode']['progress'] or value['decode']['balance'] != [1, 1]:
            return False
        if value['sourcePresent'] is not False or response['owner'] != target:
            return False
        if response['rows'] != [[case['history'], [1, 1]]]:
            return False
        return all(b['progressIncrement'] == b['recordIncrement'] == 1 and b['debit'] == b['credit'] == [1, 1] for b in response['branches'])
    if recipe == 'selected_current_recharge_zero':
        return not value['initialized']['funded'] and value['decode']['record'] == 0 and value['decode']['balance'] == [0, 1] and response['rows'] == []
    if recipe == 'selected_current_owner_source':
        return value['charge']['owner'] != target and value['accounts'][1]['owner'] != target and response['owner'] != target
    if recipe == 'selected_current_writers_false':
        return value['writer'] is False and value['decode']['record'] == 0 and all(b['recordIncrement'] == 0 for b in response['branches'])
    if recipe == 'selected_current_rows_zero':
        return value['supportedEntry'] is None and response['rows'] == []
    raise ValueError('unhandled frozen prediction recipe')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-results', action='store_true', help='write exact observations and frozen prediction outcomes')
    args = parser.parse_args()
    model = verify_freeze()
    python = [observed(case) for case in model['controls']]
    lean, receipt, probe_sha = lean_observations(model)
    comparisons = []
    for case, left, right in zip(model['controls'], python, lean, strict=True):
        comparisons.append(dict(id=case['id'], exact_match=left == right,
                                prediction=case['prediction'], prediction_holds=prediction(case, left),
                                python=left, lean=right))
    report = dict(schema='CST-TT G12 exact native observations v1', classification='b',
                  declaration_sha256=hashlib.sha256((ROOT / DECLARATION).read_bytes()).hexdigest(),
                  raw_sources=model['raw_sources'], generated_lean_sha256=probe_sha,
                  proof_boundary='Numerical observations only; full package/resource/greatest/infinite assertions require the exported kernel theorems.',
                  controls=comparisons)
    if args.write_results:
        destination = ROOT / RESULTS
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(report, indent=2) + '\n')
    elif report != json.loads((ROOT / RESULTS).read_text()):
        raise ValueError('frozen exact result drift; fresh log: ' + receipt)
    failures = [c['id'] for c in comparisons if not c['exact_match'] or not c['prediction_holds']]
    if failures:
        raise SystemExit('FAIL retained frozen predictions/comparisons: ' + ', '.join(failures))
    print('PASS all32 exact raw native Python/Lean observations and frozen predictions; 28responses/224branches; whole theorem claims remain kernel obligations')


if __name__ == '__main__':
    main()
