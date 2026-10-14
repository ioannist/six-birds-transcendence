#!/usr/bin/env python3
"""Replay the predeclared G14 controls using independent Python and actual public Lean execution.

Class (b). Primitive row-weight access is passed by the eventual pinned-source
transcription; this module never accepts ancestry, checked worlds, guards, or
precomputed final verdicts as raw fixture fields.
"""
from copy import deepcopy

EXECUTION_SOURCE_SHA256 = {'lean/CSTTT/Fallback/ReceiptAncestry.lean': '1efeb2e77938cf3b1e5627808a4f3e2d349d9a197b0e7949f3550b69c2b79403', 'lean/CSTTT/Fallback/GuardedFusion.lean': '5f5160240836be2d741b01f58241a879da1e9823abbb9c0aa3fd82f8e60f8d99', 'scripts/evaluate_operational_fallback_controls.py': '17d63a1df55aac3b21763fcc34fe4279d795ba4eecf5a10599dcf1c3538352bc'}

# Class (b): generated readback definitions encode computed execution only.
LEAN_HELPERS = 'import Lean\nimport CSTTT.Fallback.GuardedFusion\nimport CSTTT.POS04.GenericTransport\n\nnamespace G14GuardedReadback\n\nopen Lean\nopen CSTTT.Objecthood.T1Audit\nopen CSTTT.FallbackTheory.OperationalTrace\nopen CSTTT.FallbackTheory.SourceCheckedTrace\nopen CSTTT.FallbackTheory.SharedOperationalSeed\nopen CSTTT.FallbackTheory.RawPredictiveQuotient\nopen CSTTT.FallbackTheory.CachedSeed\n-- Class (b): exact declared finite state names, with no fallback state.\ndef stateName : KState → String\n  | .p0w0 => "p0w0" | .p0w1 => "p0w1" | .p1w0 => "p1w0" | .p1w1 => "p1w1"\n  | .p2w1 => "p2w1" | .p3w0 => "p3w0" | .p3w1 => "p3w1"\n  | .p4w0 => "p4w0" | .p4w1 => "p4w1" | .p5w0 => "p5w0"\n-- Class (b): only typed actual target reads yield target payloads.\ndef targetPayload (store : Store KState KState) (key : Nat) : Option KState := do\n  let .target payload ← store.read key | none\n  some payload\n-- Class (b): only typed actual source reads yield historical source payloads.\ndef sourcePayload (store : Store KState KState) (key : Nat) : Option KState := do\n  let .source payload ← store.read key | none\n  some payload\n-- Class (b): finite raw type contents are encoded directly, without verdict fields.\ndef contentJSON : Content KState KState → Json\n  | .source payload => Json.mkObj [("kind",toJson "source"),("payload",toJson (stateName payload))]\n  | .target payload => Json.mkObj [("kind",toJson "target"),("payload",toJson (stateName payload))]\n  | .record origin time payload => Json.mkObj [("kind",toJson "record"),("origin",toJson origin),("time",toJson time),("payload",toJson (stateName payload))]\n-- Class (b): actual optional stores are observed on the complete address range of this frozen finite suite.\ndef storeJSON : Option (Store KState KState) → Json\n  | none => Json.null\n  | some store =>\n      Json.mkObj [\n        ("read",Json.mkObj ((List.range 8).filterMap (fun key => (store.read key).map (fun content => (toString key,contentJSON content))))),\n        ("active",Json.mkObj ((List.range 8).filterMap (fun key => (store.read key).map (fun _ => (toString key,toJson (store.active key)))))),\n        ("edges",toJson (store.edges.map (fun edge => [edge.1,edge.2]))),("clock",toJson store.clock),\n        ("captured",Json.mkObj ((List.range 8).filterMap (fun key => (store.captured key).map (fun value =>\n          (toString key,Json.arr #[toJson value.1,toJson value.2.1,toJson (stateName value.2.2)])))))]\n\n-- Class (b): encode actual optional event-token worlds without a fallback allocation.\ndef worldJSON : Option (CSTTT.FallbackTheory.GuardedFusion.World KState KState) → Json\n  | none => Json.null\n  | some world => Json.mkObj [("store",storeJSON (some world.store)),\n      ("credits",toJson (world.credits.map (fun entry => [entry.1,entry.2])))]\ndef nativeCommandJSON : CSTTT.FallbackTheory.NativeDescendant.Command KState → Json\n  | .advance parent target action outcome => Json.arr #[toJson "advance",toJson parent,toJson target,toJson action,toJson (stateName outcome)]\n  | .fission parent left right => Json.arr #[toJson "fission",toJson parent,toJson left,toJson right]\ndef fusionCommandJSON (command : CSTTT.FallbackTheory.GuardedFusion.Command KState) : Json :=\n  Json.arr #[toJson command.left,toJson command.right,toJson command.target,\n    toJson command.leftAction,toJson command.rightAction,toJson (stateName command.outcome)]\ndef receiptJSON (receipt : CSTTT.FallbackTheory.ReceiptAncestry.Receipt KState KState) : Json :=\n  Json.mkObj [("before",storeJSON (some receipt.before)),("command",nativeCommandJSON receipt.command),\n    ("after",storeJSON (some receipt.after)),\n    ("edges",toJson ((CSTTT.FallbackTheory.ReceiptAncestry.receiptEdges receipt).map (fun edge => [edge.1,edge.2])))]\n-- Class (b): expose each computed guard part only after both actual typed parent reads.\ndef guardJSON (program : CSTTT.FallbackTheory.GuardedFusion.Program KState)\n    (world : CSTTT.FallbackTheory.GuardedFusion.World KState KState)\n    (command : CSTTT.FallbackTheory.GuardedFusion.Command KState) : Json :=\n  match world.store.read command.left,world.store.read command.right with\n  | some (.target left),some (.target right) =>\n    let bridge := CSTTT.POS04.pos04RawBridge .positive\n    Json.mkObj [\n      ("normalized_positive_row",toJson (CSTTT.FallbackTheory.GuardedFusion.rowValid program left right)),\n      ("joint_support",toJson (decide (0<CSTTT.FallbackTheory.GuardedFusion.jointWeight program left right command.outcome))),\n      ("left_support",toJson (decide (0<bridge.targetActionStep left command.leftAction command.outcome))),\n      ("right_support",toJson (decide (0<bridge.targetActionStep right command.rightAction command.outcome))),\n      ("distinct_parents",toJson (decide (command.left≠command.right))),\n      ("fresh_target",toJson (world.store.read command.target).isNone),\n      ("left_active",toJson (world.store.active command.left)),("right_active",toJson (world.store.active command.right)),\n      ("exclusive_tokens",toJson (decide ((world.credits.map Prod.fst).Nodup))),\n      ("housed_tokens",toJson (world.credits.all (fun entry => CSTTT.FallbackTheory.GuardedFusion.housed world.store entry.2))),\n      ("left_allocation",toJson (CSTTT.FallbackTheory.GuardedFusion.allocated world.credits command.left)),\n      ("right_allocation",toJson (CSTTT.FallbackTheory.GuardedFusion.allocated world.credits command.right))]\n  | _,_ => Json.null\n-- Class (b): record actual fusion steps and stop at the first rejection, retaining its direct readout.\ndef checkedSteps (program : CSTTT.FallbackTheory.GuardedFusion.Program KState) :\n    CSTTT.FallbackTheory.GuardedFusion.World KState KState → List (CSTTT.FallbackTheory.GuardedFusion.Command KState) → List Json\n  | _,[] => []\n  | world,command::rest =>\n    let after := CSTTT.FallbackTheory.GuardedFusion.step (CSTTT.POS04.pos04RawBridge .positive) program world command\n    let first := Json.mkObj [("before",worldJSON (some world)),("command",fusionCommandJSON command),\n      ("guard",guardJSON program world command),("after",worldJSON after)]\n    first::(match after with | none => [] | some next => checkedSteps program next rest)\n-- Class (b): whole optional observations use the actual public execution, records, guards and ancestry.\ndef wholeReadout (inputs : RawInputs KState KState)\n    (native : List (CSTTT.FallbackTheory.NativeDescendant.Command KState))\n    (rawProgram : Option (CSTTT.FallbackTheory.GuardedFusion.Program KState))\n    (rawCredits : Option CSTTT.FallbackTheory.GuardedFusion.Credits)\n    (commands : List (CSTTT.FallbackTheory.GuardedFusion.Command KState)) : Json :=\n  let bridge := CSTTT.POS04.pos04RawBridge .positive\n  let origin := computedStore inputs\n  let nativeRecorded := CSTTT.FallbackTheory.ReceiptAncestry.actualRecorded bridge inputs native\n  let nativeStore := nativeRecorded.map Prod.fst\n  let nativeReceipts := nativeRecorded.map (fun result => result.2.map receiptJSON)\n  let world := CSTTT.FallbackTheory.GuardedFusion.actualRun bridge inputs native rawProgram rawCredits commands\n  let recorded := CSTTT.FallbackTheory.GuardedFusion.actualRecordedFusion bridge inputs native rawProgram rawCredits commands\n  let ledger := recorded.map (fun result => (CSTTT.FallbackTheory.GuardedFusion.combinedLedger result.2 commands).map (fun edge => [edge.1,edge.2]))\n  let steps := do\n    let program ← rawProgram\n    let credits ← rawCredits\n    let store ← nativeStore\n    some (checkedSteps program ⟨store,credits⟩ commands)\n  let first := do\n    let program ← rawProgram\n    let credits ← rawCredits\n    let store ← nativeStore\n    let command ← commands.head?\n    some (CSTTT.FallbackTheory.GuardedFusion.step bridge program ⟨store,credits⟩ command).isSome\n  let ancestry source target := recorded.map (fun result => CSTTT.FallbackTheory.GuardedFusion.finishedAncestry bridge inputs commands result source target)\n  Json.mkObj ([\n    ("execution_present",toJson world.isSome),("native_prefix_present",toJson nativeStore.isSome),\n    ("prefix_source_seed_at2",toJson (seedDecision bridge inputs inputs.initialSource 2)),\n    ("first_fusion_present",toJson first),("prefix_store",storeJSON origin),("native_store",storeJSON nativeStore),\n    ("native_receipts",match nativeReceipts with | none => Json.null | some values => Json.arr values.toArray),\n    ("fusion_checked_steps",match steps with | none => Json.null | some values => Json.arr values.toArray),\n    ("final_world",worldJSON world),("combined_ledger",toJson ledger),\n    ("target5_payload",toJson (world.bind (fun value => (targetPayload value.store 5).map stateName))),\n    ("target5_active",toJson (world.map (fun value => value.store.active 5))),\n    ("parent3_active",toJson (world.map (fun value => value.store.active 3))),\n    ("parent4_active",toJson (world.map (fun value => value.store.active 4))),\n    ("token_allocation",toJson (world.map (fun value => value.credits.map (fun entry => [entry.1,entry.2]))))] ++\n    ([2,3,4,5,6,7] : List Nat).map (fun target => ("ancestry_0_at"++toString target,toJson (ancestry 0 target))))\nend G14GuardedReadback\n'


def native_step(store, command, row_weight):
    op, parent, *args = command
    content = store['read'].get(parent)
    if content is None or content['kind'] != 'target' or not store['active'].get(parent, False):
        return None
    result = deepcopy(store)
    if op == 'advance':
        target, action, outcome = args
        if target in store['read'] or row_weight(content['payload'], action, outcome) <= 0:
            return None
        result['read'][target] = dict(kind='target', payload=outcome)
        result['active'][target] = True
        result['edges'] = [[parent, target]] + store['edges']
    elif op == 'fission':
        left, right = args
        if left == right or left in store['read'] or right in store['read']:
            return None
        for target in (left, right):
            result['read'][target] = dict(kind='target', payload=content['payload'])
            result['active'][target] = True
        result['edges'] = [[parent, left], [parent, right]] + store['edges']
    else:
        raise ValueError('undeclared native operation: ' + op)
    result['clock'] += 1
    return result


def native_run(origin, commands, row_weight):
    if origin is None:
        return None, None
    store, receipts = origin, []
    for command in commands:
        after = native_step(store, command, row_weight)
        if after is None:
            return None, None
        op, parent, *args = command
        edges = [[parent, args[0]]] if op == 'advance' else [[parent, args[0]], [parent, args[1]]]
        receipts.append(dict(before=store, command=command, after=after, edges=edges))
        store = after
    return store, receipts


def fusion_guard(world, command, program, row_weight):
    left, right, target, left_action, right_action, outcome = command
    store, credits = world['store'], world['credits']
    left_content, right_content = store['read'].get(left), store['read'].get(right)
    if left_content is None or right_content is None or left_content['kind'] != 'target' or right_content['kind'] != 'target':
        return None
    lstate, rstate = left_content['payload'], right_content['payload']
    row = next((entries for a, b, entries in program['rows'] if (a, b) == (lstate, rstate)), [])
    token_ids = [token for token, _ in credits]
    return dict(
        normalized_positive_row=all(weight > 0 for _, weight in row)
        and sum(weight for _, weight in row) == program['scale'] and program['scale'] > 0,
        joint_support=sum(weight for state, weight in row if state == outcome) > 0,
        left_support=row_weight(lstate, left_action, outcome) > 0,
        right_support=row_weight(rstate, right_action, outcome) > 0,
        distinct_parents=left != right,
        fresh_target=target not in store['read'],
        left_active=store['active'].get(left, False),
        right_active=store['active'].get(right, False),
        exclusive_tokens=len(token_ids) == len(set(token_ids)),
        housed_tokens=all(store['read'].get(owner, {}).get('kind') == 'target'
                          and store['active'].get(owner, False) for _, owner in credits),
        left_allocation=any(owner == left for _, owner in credits),
        right_allocation=any(owner == right for _, owner in credits))


def fusion_step(world, command, program, row_weight):
    guard = fusion_guard(world, command, program, row_weight)
    if guard is None or not all(guard.values()):
        return None, guard
    left, right, target, _, _, outcome = command
    result = deepcopy(world)
    store = result['store']
    store['read'][target] = dict(kind='target', payload=outcome)
    store['active'][left] = False
    store['active'][right] = False
    store['active'][target] = True
    store['edges'] = [[left, target], [right, target]] + world['store']['edges']
    store['clock'] += 1
    result['credits'] = [[token, target if owner in (left, right) else owner]
                         for token, owner in world['credits']]
    return result, guard


def fusion_run(native_store, program, credits, commands, row_weight):
    if native_store is None or program is None or credits is None:
        return None, None
    world = dict(store=native_store, credits=credits)
    checked = []
    for command in commands:
        after, guard = fusion_step(world, command, program, row_weight)
        checked.append(dict(before=world, command=command, guard=guard, after=after))
        if after is None:
            return None, checked
        world = after
    # An empty stream does not certify the initial resource ledger.
    return world, checked


def scientific_ancestry(prefix, ledger, source, target, seed_decision, reachable):
    return any(seed_decision(prefix, source, point) is True
               and (point == target or reachable(ledger, point, target))
               for point in prefix['read'])


def observe(case, prefix, row_weight, seed_decision, reachable, target_payload):
    native_store, receipts = native_run(prefix, case['native_commands'], row_weight)
    world, checked = fusion_run(native_store, case['joint_program'], case['initial_token_allocation'],
                                case['fusion_commands'], row_weight)
    source = case['initial_source']
    output = dict(execution_present=world is not None, native_prefix_present=native_store is not None,
                  prefix_source_seed_at2=None if prefix is None else seed_decision(prefix, source, 2),
                  first_fusion_present=None if not checked else checked[0]['after'] is not None,
                  prefix_store=prefix, native_store=native_store, native_receipts=receipts,
                  fusion_checked_steps=checked, final_world=world)
    ledger = None if world is None else [edge for receipt in receipts for edge in receipt['edges']] + [
        edge for left, right, target, *_ in case['fusion_commands'] for edge in ([left, target], [right, target])]
    output['combined_ledger'] = ledger
    for target in (2, 3, 4, 5, 6, 7):
        output['ancestry_0_at' + str(target)] = None if world is None else scientific_ancestry(
            prefix, ledger, 0, target, seed_decision, reachable)
    if world is None:
        for key in ('target5_payload', 'target5_active', 'parent3_active', 'parent4_active', 'token_allocation'):
            output[key] = None
    else:
        output.update(target5_payload=target_payload(world['store'], 5),
                      target5_active=world['store']['active'].get(5, False),
                      parent3_active=world['store']['active'].get(3, False),
                      parent4_active=world['store']['active'].get(4, False),
                      token_allocation=world['credits'])
    return output


def source_row_weight(order, t1_source):
    import ast
    import re
    rows_match = re.search(r'def pRows : List \(List Nat\) :=\s*(\[\[.*?\]\])', t1_source, re.S)
    policy_match = re.search(r'def canonicalPolicy : List Action :=\s*\[([^\]]+)\]', t1_source, re.S)
    if rows_match is None or policy_match is None:
        raise ValueError('pinned canonical primitive tables absent')
    rows = ast.literal_eval(rows_match[1])
    policy = [entry.strip().removeprefix('.') for entry in policy_match[1].split(',')]
    if len(rows) != len(order) or any(len(row) != len(order) for row in rows) or len(policy) != len(order):
        raise ValueError('canonical raw native table lacks complete state coverage')
    action_order = ['stay', 'cw', 'ccw']

    def weight(state, action, outcome):
        if type(action) is not int or action < 0 or action >= len(action_order):
            return 0  # The represented total row function returns zero for an unavailable action index.
        sindex, tindex = order.index(state), order.index(outcome)
        name = action_order[action]
        if name == policy[sindex]:
            return rows[sindex][tindex]
        if state in ('p0w0', 'p0w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1'):
            return 2 if outcome in ('p1w0', 'p1w1') else 0
        if state == 'p1w0':
            return 4 if name == 'cw' and outcome == 'p2w1' else 0
        if state == 'p1w1':
            return 4 if name == 'ccw' and outcome == 'p5w0' else 0
        if state == 'p2w1':
            return (3 if outcome == 'p1w0' else 1 if outcome == 'p1w1' else 0) if name == 'stay' else 0
        if state == 'p5w0':
            return (1 if outcome == 'p1w0' else 3 if outcome == 'p1w1' else 0) if name == 'stay' else 0
        raise ValueError('noncanonical native support case uncovered')
    return weight


def lean_native_command(command):
    op, *values = command
    return '.' + op + ' ' + ' '.join('.' + value if isinstance(value, str) else str(value) for value in values)


def lean_fusion_command(command):
    left, right, target, left_action, right_action, outcome = command
    return '({left := ' + str(left) + ',right := ' + str(right) + ',target := ' + str(target) + ',leftAction := ' + str(left_action) + ',rightAction := ' + str(right_action) + ',outcome := .' + outcome + '} : CSTTT.FallbackTheory.GuardedFusion.Command KState)'


def lean_program(program):
    if program is None:
        return 'none'
    expression = '[]'
    for left, right, row in reversed(program['rows']):
        entries = ','.join('(.' + state + ',' + str(weight) + ')' for state, weight in row)
        expression = 'if left=.' + left + ' ∧ right=.' + right + ' then [' + entries + '] else ' + expression
    return '(some ({scale := ' + str(program['scale']) + ',rows := fun left right => ' + expression + '} : CSTTT.FallbackTheory.GuardedFusion.Program KState))'


def lean_credits(credits):
    if credits is None:
        return 'none'
    return '(some [' + ','.join('(' + str(token) + ',' + str(owner) + ')' for token, owner in credits) + '])'


def validate_cases(model):
    order = model['state_order']
    addresses = model['query_addresses']
    if order != ['p0w0','p0w1','p1w0','p1w1','p2w1','p3w0','p3w1','p4w0','p4w1','p5w0'] or addresses != list(range(8)):
        raise ValueError('complete declared state/address domain drift')
    if model['ancestry_queries'] != [[0, target] for target in range(2, 8)]:
        raise ValueError('declared scientific query coverage drift')
    if len(model['cases']) != 36 or len({case['case_id'] for case in model['cases']}) != 36:
        raise ValueError('complete declared36 control inventory drift')
    for case in model['cases']:
        if case['initial_source'] != 0 or type(case['max_age']) is not int or case['max_age'] < 0:
            raise ValueError('raw source/age domain drift')
        if case['raw_source'] is not None and case['raw_source'] not in order:
            raise ValueError('undeclared source payload')
        decoder = case['decoder']
        if decoder is not None and decoder != 'identity' and not (isinstance(decoder, dict) and set(decoder) == {'constant'} and decoder['constant'] in order):
            raise ValueError('undeclared raw decoder')
        for command in case['prefix_commands']:
            op, *args = command
            arity = {'snapshot':2,'erase':1,'gap':1,'activate':2,'independent':2}.get(op)
            if arity is None or len(args) != arity:
                raise ValueError('undeclared prefix operation')
            if op == 'gap':
                if type(args[0]) is not int or args[0] < 0:
                    raise ValueError('invalid raw gap duration')
                continue
            if op == 'independent':
                if args[-1] not in order:
                    raise ValueError('undeclared independent target state')
                args = args[:-1]
            if any(type(value) is not int or value not in addresses for value in args):
                raise ValueError('prefix address outside complete observation frame')
        for command in case['native_commands']:
            op, *args = command
            if op == 'fission':
                if len(args) != 3 or any(type(value) is not int or value not in addresses for value in args):
                    raise ValueError('native fission domain drift')
            elif op == 'advance':
                if len(args) != 4 or any(type(value) is not int or value not in addresses for value in args[:2]) or type(args[2]) is not int or args[2] < 0 or args[3] not in order:
                    raise ValueError('native advance domain drift')
            else:
                raise ValueError('undeclared native operation')
        for command in case['fusion_commands']:
            if len(command) != 6 or any(type(value) is not int or value not in addresses for value in command[:3]) or any(type(value) is not int or value < 0 for value in command[3:5]) or command[-1] not in order:
                raise ValueError('raw fusion domain drift')
        program = case['joint_program']
        if program is not None:
            if type(program['scale']) is not int or program['scale'] < 0:
                raise ValueError('joint scale must be a primitive Nat')
            keys = []
            for left, right, row in program['rows']:
                if left not in order or right not in order or any(state not in order or type(weight) is not int or weight < 0 for state, weight in row):
                    raise ValueError('joint row outside declared raw Nat/state domain')
                keys.append((left, right))
            if len(keys) != len(set(keys)):
                raise ValueError('ambiguous duplicate raw program key')
        credits = case['initial_token_allocation']
        if credits is not None and any(type(token) is not int or token < 0 or type(owner) is not int or owner not in addresses for token, owner in credits):
            raise ValueError('raw token identifier/owner domain drift')
    # No resource invariant, normalization or support premise is imposed here:
    # the deliberately invalid declared recipes must reach actual rejection.
    return model


def verify_freeze(root, declaration_commit, model_path):
    import hashlib
    import json
    import subprocess
    for path, digest in EXECUTION_SOURCE_SHA256.items():
        raw = (root / path).read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest or any(
            raw != subprocess.check_output(['git', 'show', ref + ':' + path], cwd=root)
            for ref in (declaration_commit, 'HEAD')
        ):
            raise ValueError('committed actual executor or independent prefix transcription drift: ' + path)
    data = (root / model_path).read_bytes()
    for ref in (declaration_commit, 'HEAD'):
        if subprocess.check_output(['git', 'show', ref + ':' + model_path], cwd=root) != data:
            raise ValueError('new36 declaration differs from frozen committed bytes')
    subprocess.run(['git', 'merge-base', '--is-ancestor', declaration_commit, 'HEAD'], cwd=root, check=True)
    model = json.loads(data)
    if subprocess.check_output(['git', 'rev-parse', declaration_commit + '^'], cwd=root, text=True).strip() != model['source_head']:
        raise ValueError('primitive-source head differs from actual declaration parent')
    if model['declared_before_new_fixture_evaluation'] is not True:
        raise ValueError('missing pre-evaluation declaration provenance')
    for path, digest in model['source_sha256'].items():
        raw = (root / path).read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest or raw != subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=root):
            raise ValueError('pinned native primitive source drift: ' + path)
    return validate_cases(model)


def python_observations(model, base, t1_source):
    import json
    import re
    order = model['state_order']
    classes_match = re.search(r'def mClasses : List Nat := \[([^\]]+)\]', t1_source)
    if classes_match is None:
        raise ValueError('pinned predictive classes absent')
    classes = [int(value) for value in classes_match[1].split(',')]
    if len(classes) != len(order):
        raise ValueError('predictive class presentation incomplete')
    weight = source_row_weight(order, t1_source)
    values = []
    for case in model['cases']:
        raw = case['decoder']
        decoder = None if raw is None else {state: state for state in order} if raw == 'identity' else {state: raw['constant'] for state in order}
        prefix = base.execute(dict(case, commands=case['prefix_commands']), decoder)
        actual = observe(case, prefix, weight,
                         lambda store, source, target: base.seed_decision(store, source, target, order, classes),
                         base.reachable, base.target_payload)
        values.append(dict(case_id=case['case_id'], actual=actual))
    return json.loads(json.dumps(values))


def lean_observations(root, model, base, helper_source, python):
    from datetime import datetime, timezone
    import hashlib
    import json
    import subprocess
    folder = root / 'lean/.validate-logs' / ('guarded-fusion-controls-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S-%fZ'))
    folder.mkdir(parents=True)
    (folder/'python.json').write_text(json.dumps(python, indent=2) + '\n')
    calls = []
    for case in model['cases']:
        inputs = base.lean_input(dict(case, commands=case['prefix_commands']))
        native = '[' + ','.join(lean_native_command(command) for command in case['native_commands']) + ']'
        commands = '[' + ','.join(lean_fusion_command(command) for command in case['fusion_commands']) + ']'
        actual = 'G14GuardedReadback.wholeReadout ' + inputs + ' ' + native + ' ' + lean_program(case['joint_program']) + ' ' + lean_credits(case['initial_token_allocation']) + ' ' + commands
        calls.append('Lean.Json.mkObj [("case_id",Lean.toJson ' + json.dumps(case['case_id']) + '),("actual",' + actual + ')]')
    source = helper_source + '\nopen Lean CSTTT.Objecthood.T1Audit CSTTT.FallbackTheory.SharedOperationalSeed\n#eval IO.println (Lean.Json.compress (Lean.Json.arr #[' + ',\n'.join(calls) + ']))\n'
    probe = folder / 'readback.lean'
    probe.write_text(source)
    completed = subprocess.run(['lake','env','lean',str(probe.relative_to(root/'lean'))], cwd=root/'lean', text=True, capture_output=True)
    log = folder / 'lean.log'
    log.write_text(completed.stdout + completed.stderr)
    if completed.returncode:
        raise RuntimeError('actual native/fusion Lean readback failed; retained ' + str(log))
    arrays = [json.loads(line) for line in completed.stdout.splitlines() if line.startswith('[{')]
    if len(arrays) != 1 or len(arrays[0]) != len(model['cases']):
        raise ValueError('expected one complete declared36 Lean observation array')
    (folder/'lean.json').write_text(json.dumps(arrays[0], indent=2) + '\n')
    return arrays[0], hashlib.sha256(probe.read_bytes()).hexdigest(), str(folder.relative_to(root))


def compare_observations(model, python, lean):
    controls = []
    for case, left, right in zip(model['cases'], python, lean, strict=True):
        if left['case_id'] != case['case_id'] or right['case_id'] != case['case_id']:
            raise ValueError('declared36 control order drift')
        prediction = case['frozen_prediction']
        if not all(key in left['actual'] for key in prediction):
            raise ValueError('frozen prediction consumes absent observation field')
        controls.append(dict(case_id=case['case_id'], exact_match=left == right,
                             frozen_prediction=prediction,
                             prediction_holds=all(left['actual'][key] == expected for key, expected in prediction.items()),
                             python=left['actual'], lean=right['actual']))
    return controls


def load_base(root):
    import importlib.util
    spec = importlib.util.spec_from_file_location('g14_committed_prefix_interpreter', root/'scripts/evaluate_operational_fallback_controls.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    import argparse
    import hashlib
    import json
    from pathlib import Path
    root = Path(__file__).resolve().parents[1]
    declaration_commit = '00eed9557111fcb18fe8604701d2ab7d8df3ee61'
    model_path = 'audit/proposed_models/G14-GUARDED-FUSION.model.json'
    result_path = 'audit/evaluations/G14-GUARDED-FUSION.results.json'
    parser = argparse.ArgumentParser(description='Replay frozen committed guarded-fusion controls with exact independent Python/public Lean observations.')
    parser.add_argument('--write-results', action='store_true')
    args = parser.parse_args()
    model = verify_freeze(root, declaration_commit, model_path)
    base = load_base(root)
    python = python_observations(model, base, (root/'lean/CSTTT/Objecthood/T1Audit.lean').read_text())
    helper_source = LEAN_HELPERS
    lean, probe_sha, receipt = lean_observations(root, model, base, helper_source, python)
    controls = compare_observations(model, python, lean)
    report = dict(schema='CST-TT G14 exact guarded fusion observations v1', classification='b',
                  declaration_sha256=hashlib.sha256((root/model_path).read_bytes()).hexdigest(),
                  declaration_commit=declaration_commit, raw_sources=model['source_sha256'],
                  execution_sources=EXECUTION_SOURCE_SHA256,
                  generated_lean_sha256=probe_sha,
                  proof_boundary='Exact finite represented source-checked prefix/native/fusion execution, full optional worlds/tokens/receipts/guards and Seed-plus-accepted-ledger scientific ancestry. Physical owner/native debit/C5 historical credit/C7 history gluing/independent packages/autonomy/full IAPS remain separate kernel obligations.',
                  controls=controls)
    (root/receipt/'comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    failures = [control['case_id'] for control in controls if not control['exact_match'] or not control['prediction_holds']]
    if failures:
        raise SystemExit('FAIL retained original frozen36 predictions/comparisons: ' + ', '.join(failures) + '; ' + receipt)
    if args.write_results:
        destination = root/result_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(json.dumps(report, indent=2) + '\n')
    elif report != json.loads((root/result_path).read_text()):
        raise ValueError('frozen exact36 result drift; fresh log: ' + receipt)
    print('PASS all36 exact raw guarded fusion Python/public Lean observations and frozen predictions; physical IAPS remains separate')

if __name__ == '__main__':
    main()
