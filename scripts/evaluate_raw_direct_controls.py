#!/usr/bin/env python3
"""Evaluate committed raw-direct controls with exact Python/Lean readback.

All verdicts derive from raw graphs, source cells and observed frontiers. The
source declaration is read without tuning; old released verdict flags are unused.
"""
from __future__ import annotations
import copy
import hashlib
import json
from pathlib import Path

SCALARS = ('predictive', 'order', 'tick', 'progress', 'record')

def advance(frontier, update):
    result = {k: frontier[k] + update[k + 'Advance'] for k in SCALARS}
    result.update(residue=frontier['residue'] + update['appendResidue'],
                  maintenance=update['nextMaintenance'], owner=update['nextOwner'])
    return result

def readout_step(source, target, update):
    return (target['frontier'] == advance(source['frontier'], update)
            and all(update[k + 'Advance'] > 0 for k in SCALARS[1:])
            and bool(update['appendResidue']) and bool(update['nextMaintenance'])
            and update['nextOwner'] in target['support'])

def event_at(model, name):
    return next((e for e in model['events'] if e['id'] == name), None)

def dependency_check(model, edge):
    source, target = event_at(model, edge['parent']), event_at(model, edge['child'])
    return source is not None and target is not None and source['stage'] < target['stage']

def assignment(model):
    result = copy.deepcopy(model.get('extraInputs', {}))
    result[model['sourceAudit']] = copy.deepcopy(model['sourceInput'])
    return result

def projection(model):
    source, target = event_at(model, model['sourceAudit']), event_at(model, model['targetAudit'])
    if source is None or target is None:
        return None
    s, t = source['stage'], target['stage']
    ids = [e['id'] for e in model['events']]
    if (s >= len(model['stages']) or t >= len(model['stages'])
        or s >= len(model['updates']) or source['owner'] != model['sourceCarrier']
        or target['owner'] != model['targetCarrier'] or len(set(ids)) != len(ids)
        or not all(dependency_check(model, e) for e in model['dependencies'])):
        return None
    return {'sourceEvent': source['id'], 'targetEvent': target['id'],
            'edges': model['dependencies'], 'receiver': model['updates'][s],
            'source': model['stages'][s], 'target': model['stages'][t],
            'sourceStage': s, 'targetStage': t,
            'sourceCarrier': model['sourceCarrier'], 'targetCarrier': model['targetCarrier']}

def incoming(raw):
    return [e for e in raw['edges'] if e['child'] == raw['targetEvent']]

def emit(raw, cells, edge):
    cell = cells.get(edge['parent'])
    if (cell is None or cell['payload'] is None or cell['token'] is None
            or not cell['present'] or cell['token']['used']):
        return None
    return {'parent': edge['parent'], 'child': edge['child'], 'kind': edge['kind'],
            'sourcePayload': copy.deepcopy(cell['payload']),
            'frontier': advance(cell['payload'], raw['receiver']),
            'stage': cell['stage'] + 1,
            'consumedToken': {'id': cell['token']['id'], 'used': True}}

def generated(raw, cells):
    return [d for e in incoming(raw) if (d := emit(raw, cells, e)) is not None]

def direct_check(raw, cells):
    edges = incoming(raw)
    if len(edges) != 1:
        return False
    edge = edges[0]
    cell = cells.get(edge['parent'])
    if emit(raw, cells, edge) is None:
        return False
    return (raw['sourceCarrier'] != raw['targetCarrier']
        and edge['parent'] == raw['sourceEvent'] and edge['child'] == raw['targetEvent']
        and edge['kind'] == 'liveTemporal' and cell['provenance'] == 'live'
        and raw['source']['realized'] and raw['target']['realized']
        and raw['source']['support'] == [raw['sourceCarrier']]
        and raw['target']['support'] == [raw['targetCarrier']]
        and raw['source']['frontier']['owner'] == raw['sourceCarrier']
        and raw['target']['frontier']['owner'] == raw['targetCarrier']
        and cell['payload'] == raw['source']['frontier']
        and cell['stage'] + 1 == raw['targetStage']
        and raw['target']['frontier'] == advance(cell['payload'], raw['receiver'])
        and readout_step(raw['source'], raw['target'], raw['receiver'])
        and cell['stage'] == raw['sourceStage']
        and raw['sourceEvent'] != raw['targetEvent'])

def consume_token(key, cells):
    next_cells = copy.deepcopy(cells)
    for cell in next_cells.values():
        if cell is not None and cell['token'] is not None and cell['token']['id'] == key:
            cell['token']['used'] = True
    return next_cells

def fire(raw, cells):
    deliveries = generated(raw, cells)
    if len(deliveries) != 1:
        return None
    delivery = deliveries[0]
    return delivery, consume_token(delivery['consumedToken']['id'], cells)

def data_reachable(model, cells):
    cell = cells.get(model['sourceAudit'])
    if cell is None or cell['payload'] is None:
        return False
    # Nonempty path: seed only actual outgoing payload-bound edges. Thus an
    # equal source/target ID needs a positive-length cycle, never an empty path.
    frontier = [e['child'] for e in model['dataGraph']
                if e['parent'] == model['sourceAudit'] and e['payload'] == cell['payload']]
    seen = set()
    while frontier:
        vertex = frontier.pop()
        if vertex == model['targetAudit']:
            return True
        if vertex in seen:
            continue
        seen.add(vertex)
        frontier.extend(e['child'] for e in model['dataGraph']
                        if e['parent'] == vertex and e['payload'] == cell['payload'])
    return False

def overlap_check(model):
    stages, updates = model['stages'], model['updates']
    source, target = model['sourceCarrier'], model['targetCarrier']
    if (source == target or len(stages) < 3 or stages[0]['support'] != [source]
        or stages[-1]['support'] != [target] or stages[0]['frontier']['owner'] != source
        or stages[-1]['frontier']['owner'] != target):
        return False
    if not all(s['realized'] and s['support'] and s['frontier']['owner'] in s['support']
               and s['frontier']['maintenance'] for s in stages):
        return False
    if not any(source in s['support'] and target in s['support'] for s in stages):
        return False
    events, dependencies = model['events'], model['dependencies']
    if not events or len({e['id'] for e in events}) != len(events):
        return False
    if not all(e['stage'] < len(stages) and e['owner'] in stages[e['stage']]['support'] for e in events):
        return False
    if not dependencies or not all(dependency_check(model, e) for e in dependencies):
        return False
    if len(updates) + 1 != len(stages) or not all(readout_step(a, b, u) for a, b, u in zip(stages, stages[1:], updates)):
        return False
    s, t, e = (event_at(model, model[k]) for k in ('sourceAudit', 'targetAudit', 'laterAudit'))
    if s is None or t is None or e is None:
        return False
    if not (s['owner'] == source and t['owner'] == target and s['stage'] == t['stage']
            and s['stage'] < e['stage'] and e['stage'] + 1 == len(stages)
            and source in stages[s['stage']]['support'] and target in stages[t['stage']]['support']
            and any(d['parent'] == s['id'] and d['child'] == e['id'] for d in dependencies)
            and any(d['parent'] == t['id'] and d['child'] == e['id'] for d in dependencies)):
        return False
    if model.get('interventionMode', 'additive') == 'mixedSupport':
        count = lambda removed: sum(st['realized'] and source in [c for c in st['support'] if c != removed]
                                   and target in [c for c in st['support'] if c != removed] for st in stages)
        if not (count(None) > 0 and count(source) == 0 and count(target) == 0):
            return False
    else:
        keys = ('predictive', 'tick', 'record')
        zero = dict.fromkeys(keys, 0)
        base, sc, tc = (model.get(k, zero) for k in ('base', 'sourceContribution', 'targetContribution'))
        whole = {k: base[k] + sc[k] + tc[k] for k in keys}
        if (base != {k: stages[0]['frontier'][k] for k in keys}
            or whole != {k: stages[-1]['frontier'][k] for k in keys}
            or whole == {k: base[k] + tc[k] for k in keys}
            or whole == {k: base[k] + sc[k] for k in keys}):
            return False
    # Exact routeStatusOf nonempty stage-by-stage event paths.
    paths = [[ev] for ev in events if ev['stage'] == 0]
    for n in range(1, len(stages)):
        paths = [p + [ev] for p in paths for ev in events if ev['stage'] == n
                 and any(d['parent'] == p[-1]['id'] and d['child'] == ev['id'] for d in dependencies)]
    return bool(paths) and bool(updates) and bool(stages[0]['frontier']['residue'])

def evaluate(model):
    cells, raw = assignment(model), projection(model)
    result = {'projection': raw is not None, 'direct': False,
              'overlap': bool(overlap_check(model)), 'dataReachable': data_reachable(model, cells)}
    if raw is None:
        result.update(generated=None, removedGenerated=None, fire=None, repeatedGenerated=None,
                      repeatedDirect=None, patterns=None, temporalGap=None, consumedIdentityGenerated=None)
        return result
    deleted = copy.deepcopy(cells)
    deleted[raw['sourceEvent']] = None
    fired = fire(raw, cells)
    selected = cells.get(raw['sourceEvent'])
    consumed = None if selected is None or selected['token'] is None else generated(raw, consume_token(selected['token']['id'],cells))
    patterns = {}
    for label, kind, provenance in [('detached', 'copy', 'detached'), ('archive', 'replay', 'archive'), ('storage', 'storage', 'store')]:
        patterns[label] = any(e['kind'] == kind or (cells.get(e['parent']) is not None
            and cells[e['parent']]['provenance'] == provenance) for e in incoming(raw))
    result.update(direct=bool(direct_check(raw, cells)), generated=generated(raw, cells),
        removedGenerated=generated(raw, deleted), fire=None if fired is None else fired[0],
        repeatedGenerated=None if fired is None else generated(raw, fired[1]),
        repeatedDirect=None if fired is None else bool(direct_check(raw, fired[1])),
        patterns=patterns, temporalGap=not raw['source']['realized'] or not raw['target']['realized']
        or raw['sourceStage'] + 1 != raw['targetStage'], consumedIdentityGenerated=consumed)
    return result

def patched(base, patches):
    result = copy.deepcopy(base)
    for patch in patches:
        parts = patch['path'].split('.')
        cell = result
        for part in parts[:-1]:
            cell = cell[int(part)] if isinstance(cell, list) else cell[part]
        final = int(parts[-1]) if isinstance(cell, list) else parts[-1]
        if not isinstance(cell, list) and final not in cell:
            raise ValueError('undeclared patch path ' + patch['path'])
        cell[final] = copy.deepcopy(patch['value'])
    return result

def frozen_cases(manifest):
    result = copy.deepcopy(manifest['primitives'])
    for name, control in manifest['controls'].items():
        result[name] = patched(manifest['primitives'][control['base']], control['patches'])
    return result

def verify_declared_sources(root, manifest):
    for name, source in manifest['sources'].items():
        source_bytes = (root / source['path']).read_bytes()
        if hashlib.sha256(source_bytes).hexdigest() != source['sha256']:
            raise ValueError('released source hash drift: ' + source['path'])
        release = json.loads(source_bytes)
        dependency = next(d for d in release['episode']['dependencies']
                          if d['dependency_id'] == release['operational_dependency_id'])
        payload = dependency['payload']
        canonical = json.dumps(payload, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
        if not (hashlib.sha256(canonical).hexdigest() == dependency['payload_sha256'] == source['releasePayloadSha256']):
            raise ValueError('released payload SHA provenance drift: ' + name)
        profile = manifest['primitives'][name]
        f = profile['stages'][-1]['frontier']
        received = {'predictive_rank': f['predictive'], 'order_rank': f['order'],
                    'tick_index': f['tick'], 'progress_rank': f['progress'],
                    'record_value': f['record'], 'route_residue': f['residue'],
                    'maintenance_state': f['maintenance']}
        if received != payload:
            raise ValueError('whole seven-field released received payload drift: ' + name)
        fields = {'predictive':'predictive_rank', 'order':'order_rank', 'tick':'tick_index',
                  'progress':'progress_rank', 'record':'record_value', 'residue':'route_residue',
                  'maintenance':'maintenance_state', 'owner':'maintenance_owner'}
        actual_stages = release['episode']['stages']
        if len(actual_stages) != len(profile['stages']):
            raise ValueError('released observed stages drift: ' + name)
        for primitive, observed in zip(profile['stages'], actual_stages, strict=True):
            if (primitive['frontier'] != {key:observed['signature'][old] for key,old in fields.items()}
                or primitive['realized'] != observed['temporal_realized']
                or primitive['support'] != [c['code'] for c in observed['active_support']]):
                raise ValueError('whole observed source/target stage drift: ' + name)
        if (profile['sourceCarrier'] != release['source_carrier']['code']
            or profile['targetCarrier'] != release['target_carrier']['code']
            or profile['sourceAudit'] != release['last_source_event_id']
            or profile['targetAudit'] != release['first_target_event_id']):
            raise ValueError('released boundary ID drift: ' + name)

def lean_string(value):
    return json.dumps(value, ensure_ascii=False)

def lean_list(values, convert):
    return '[' + ','.join(convert(v) for v in values) + ']'

def lean_frontier(f):
    return '⟨' + ','.join(str(f[k]) for k in SCALARS) + ',' + lean_list(f['residue'], lean_string) + ',' + lean_string(f['maintenance']) + ',' + str(f['owner']) + '⟩'

def lean_bool(b):
    return 'true' if b else 'false'

def lean_option(value, convert):
    return 'none' if value is None else '(some (' + convert(value) + '))'

def lean_input(cell):
    return '⟨' + str(cell['stage']) + ',' + lean_option(cell['payload'], lean_frontier) + ',' + lean_option(cell['token'], lambda t: '⟨' + str(t['id']) + ',' + lean_bool(t['used']) + '⟩') + ',' + lean_bool(cell['present']) + ',.' + cell['provenance'] + '⟩'

def lean_episode(m):
    zero = '⟨0,0,0⟩'
    stage = lambda s: '⟨' + lean_list(s['support'], str) + ',' + lean_bool(s['realized']) + ',' + lean_frontier(s['frontier']) + '⟩'
    event = lambda e: '⟨' + lean_string(e['id']) + ',' + str(e['owner']) + ',' + str(e['stage']) + '⟩'
    dep = lambda d: '⟨' + lean_string(d['parent']) + ',' + lean_string(d['child']) + '⟩'
    update = lambda u: '⟨' + ','.join(str(u[k + 'Advance']) for k in SCALARS) + ',' + lean_list(u['appendResidue'], lean_string) + ',' + lean_string(u['nextMaintenance']) + ',' + str(u['nextOwner']) + '⟩'
    proj = lambda p: '⟨' + ','.join(str(p[k]) for k in ('predictive', 'tick', 'record')) + '⟩'
    fields = ['interventionMode := .' + m.get('interventionMode', 'additive'), 'source := ' + str(m['sourceCarrier']), 'target := ' + str(m['targetCarrier']),
              'stages := ' + lean_list(m['stages'], stage), 'events := ' + lean_list(m['events'], event), 'dependencies := ' + lean_list(m['dependencies'], dep),
              'updates := ' + lean_list(m['updates'], update)]
    fields.extend(k + ' := ' + (proj(m[k]) if k in m else zero) for k in ('base', 'sourceContribution', 'targetContribution'))
    fields.extend(k + ' := ' + lean_string(m[k]) for k in ('sourceAudit', 'targetAudit', 'laterAudit'))
    return '{' + ', '.join(fields) + '}'

def lean_control(name, m):
    cells = assignment(m)
    input_expr = 'none'
    for key, value in reversed(list(cells.items())):
        input_expr = 'if id=' + lean_string(key) + ' then ' + lean_option(value, lean_input) + ' else ' + input_expr
    kind_expr = '.liveTemporal'
    for edge in reversed(m['dependencies']):
        kind_expr = 'if parent=' + lean_string(edge['parent']) + ' ∧ child=' + lean_string(edge['child']) + ' then .' + edge['kind'] + ' else ' + kind_expr
    graph = lean_list(m['dataGraph'], lambda e: '⟨' + lean_string(e['parent']) + ',' + lean_string(e['child']) + ',' + lean_frontier(e['payload']) + '⟩')
    return 'def ' + name + ' : ControlModel :=\n {episode := ' + lean_episode(m) + ', input := fun id => ' + input_expr + ', dependencyKind := fun parent child => ' + kind_expr + ', dataGraph := ' + graph + '}\n'

def native_cases(manifest, overlap):
    """The preceding actual canonical episode supplies the full shared frontier.

    This construction interprets the committed primitive extension literally;
    it does not search for or modify a successful target.
    """
    declared = manifest['nativeControls']['mixedDirect']
    if (declared['sourceFrontier'] != 'whole exit of the preceding overlapOnly actual episode'
        or declared['sourceInput'] != 'whole sourceFrontier; stage0; token id=4 used=false; present=true; provenance=live'
        or declared['targetObservation'] != 'all old scalar counters plus declared increments; old residue plus native-direct; funded; owner101'
        or declared['sourceStage'] != 0):
        raise ValueError('unrecognized native direct primitive construction rule')
    source = copy.deepcopy(overlap['stages'][-1]['frontier'])
    receiver = copy.deepcopy(declared['receiver'])
    target = advance(source, receiver)
    s, t = declared['sourceEvent'], declared['targetEvent']
    mixed = {'sourceCarrier': declared['sourceCarrier'], 'targetCarrier': declared['targetCarrier'],
        'sourceAudit': s, 'targetAudit': t, 'laterAudit': '',
        'stages': [{'support': declared['sourceSupport'], 'realized': declared['realized'][0], 'frontier': source},
                   {'support': declared['targetSupport'], 'realized': declared['realized'][1], 'frontier': target}],
        'events': [{'id': s, 'owner': declared['sourceCarrier'], 'stage': declared['sourceStage']},
                   {'id': t, 'owner': declared['targetCarrier'], 'stage': declared['targetStage']}],
        'dependencies': [{'parent': s, 'child': t, 'kind': declared['dependencyKind']}],
        'updates': [receiver], 'sourceInput': {'stage': declared['sourceStage'], 'payload': source,
        'token': {'id': 4, 'used': False}, 'present': True, 'provenance': 'live'}, 'dataGraph': []}
    return {'overlapOnly': overlap, 'mixedDirect': mixed}

def compatible(left, right):
    return (left['targetCarrier'] == right['sourceCarrier']
            and left['stages'][-1]['frontier'] == right['stages'][0]['frontier'])

def atomic_endpoint_edge_present(left, right):
    return any(edge['parent']==left['sourceAudit'] and edge['child']==right['targetAudit']
               for edge in left['dependencies']+right['dependencies'])


NATIVE_PRIMITIVE_PROBE = r'''
import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationCorridor
import Lean
open Lean CSTTT.CorridorTheory.AtomicChain
namespace G8NativePrimitiveProbe
private def obj := Json.mkObj
private def arr (xs : List Json) := Json.arr xs.toArray
private def frontier (f : Frontier) : Json := obj [
 ("predictive",toJson f.predictive),("order",toJson f.order),("tick",toJson f.tick),
 ("progress",toJson f.progress),("record",toJson f.record),("residue",toJson f.residue),
 ("maintenance",toJson f.maintenance),("owner",toJson f.owner)]
private def stage (s : RawStage) : Json := obj [
 ("support",toJson s.support),("realized",toJson s.realized),("frontier",frontier s.frontier)]
private def event (e : RawEvent) : Json := obj [
 ("id",toJson e.id),("owner",toJson e.owner),("stage",toJson e.stage)]
private def dependency (e : RawDependency) : Json := obj [
 ("parent",toJson e.parent),("child",toJson e.child),("kind",toJson "liveTemporal")]
private def update (u : ReadoutUpdate) : Json := obj [
 ("predictiveAdvance",toJson u.predictiveAdvance),("orderAdvance",toJson u.orderAdvance),
 ("tickAdvance",toJson u.tickAdvance),("progressAdvance",toJson u.progressAdvance),
 ("recordAdvance",toJson u.recordAdvance),("appendResidue",toJson u.appendResidue),
 ("nextMaintenance",toJson u.nextMaintenance),("nextOwner",toJson u.nextOwner)]
private def projection (p : Projection) : Json := obj [
 ("predictive",toJson p.predictive),("tick",toJson p.tick),("record",toJson p.record)]
private def sourceInput (l : FiniteAtomicLeg) (id : String) : Json :=
 match eventAt l id with
 | none => Json.null
 | some e => match l.stages[e.stage]? with
   | none => Json.null
   | some s => obj [("stage",toJson e.stage),("payload",frontier s.frontier),
     ("token",obj [("id",toJson e.stage),("used",toJson false)]),
     ("present",toJson s.realized),("provenance",toJson "live")]
private def episode (l : FiniteAtomicLeg) : Json := obj [
 ("sourceCarrier",toJson l.source),("targetCarrier",toJson l.target),
 ("sourceAudit",toJson l.sourceAudit),("targetAudit",toJson l.targetAudit),
 ("laterAudit",toJson l.laterAudit),
 ("interventionMode",toJson (match l.interventionMode with | .additive => "additive" | .mixedSupport => "mixedSupport")),
 ("stages",arr (l.stages.map stage)),("events",arr (l.events.map event)),
 ("dependencies",arr (l.dependencies.map dependency)),("updates",arr (l.updates.map update)),
 ("base",projection l.base),("sourceContribution",projection l.sourceContribution),
 ("targetContribution",projection l.targetContribution),
 ("sourceInput",sourceInput l l.sourceAudit),
 ("extraInputs",obj (l.events.map (fun e => (e.id,sourceInput l e.id)))),
 ("dataGraph",arr [])]
-- Run only AFTER the declaration packet is committed. No verdict is exported.
#eval IO.println (Json.compress (episode
 (CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationCorridor.canonicalLeg
 true (false,false,false) ["native-past"])))
end G8NativePrimitiveProbe

'''
READOUT_PROBE_BASE = r'''
import CSTTT.Corridor.RawDirectSuccessor
import Lean
open Lean CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor
namespace G8ReadoutProbe
private def obj := Json.mkObj
private def arr (xs : List Json) := Json.arr xs.toArray
private def frontier (f : Frontier) : Json := obj [
 ("predictive",toJson f.predictive),("order",toJson f.order),("tick",toJson f.tick),
 ("progress",toJson f.progress),("record",toJson f.record),("residue",toJson f.residue),
 ("maintenance",toJson f.maintenance),("owner",toJson f.owner)]
private def kind : Kind → String
 | .liveTemporal => "liveTemporal" | .copy => "copy" | .replay => "replay" | .storage => "storage"
private def delivery (d : Delivered) : Json := obj [
 ("parent",toJson d.parent),("child",toJson d.child),("kind",toJson (kind d.kind)),
 ("sourcePayload",frontier d.sourcePayload),("frontier",frontier d.frontier),
 ("stage",toJson d.stage),
 ("consumedToken",obj [("id",toJson d.consumedToken.id),("used",toJson d.consumedToken.used)])]
private def deliveries (xs : List Delivered) : Json := arr (xs.map delivery)
private def pattern (raw : Raw) (a : Assignment) (k : Kind) (p : Provenance) : Bool :=
 (incoming raw).any fun e => decide (e.kind=k) ||
   ((a e.parent).map (fun input => decide (input.provenance=p))).getD false
-- Search only nonempty paths in the finite payload-bound data graph. Export
-- comparison only; later Lean bridge supplies actual DataPath constructors.
private def reaches (graph : List DataEdge) (payload : Frontier) (target : String) : Nat → List String → Bool
 | 0,_ => false
 | n+1,vertices => vertices.any fun vertex => vertex==target ||
     reaches graph payload target n
       ((graph.filter (fun e => e.parent==vertex && decide (e.payload=payload))).map DataEdge.child)
private def dataReachable (m : ControlModel) : Bool :=
 match m.input m.episode.sourceAudit with
 | none => false
 | some input => match input.payload with
   | none => false
   | some payload => reaches m.dataGraph payload m.episode.targetAudit (m.dataGraph.length+1)
       ((m.dataGraph.filter (fun e => e.parent==m.episode.sourceAudit && decide (e.payload=payload))).map DataEdge.child)
private def observed (m : ControlModel) : Json :=
 let base := [("projection",toJson (directProjection m).isSome),
   ("overlap",toJson (AtomicLegCheck m.episode)),("dataReachable",toJson (dataReachable m))]
 match directProjection m with
 | none => obj (base++[("direct",toJson false),("generated",Json.null),
     ("removedGenerated",Json.null),("fire",Json.null),("repeatedGenerated",Json.null),
     ("repeatedDirect",Json.null),("patterns",Json.null),("temporalGap",Json.null),
     ("consumedIdentityGenerated",Json.null)])
 | some (raw,b) =>
   let fired := fire raw m.input
   obj (base++[("direct",toJson (directCheck raw b m.input)),
     ("generated",deliveries (generated raw m.input)),
     ("removedGenerated",deliveries (generated raw (deleteSource raw m.input))),
     ("fire",(fired.map (fun pair => delivery pair.1)).getD Json.null),
     ("repeatedGenerated",(fired.map (fun pair => deliveries (generated raw pair.2))).getD Json.null),
     ("repeatedDirect",(fired.map (fun pair => toJson (directCheck raw b pair.2))).getD Json.null),
     ("consumedIdentityGenerated",((m.input raw.sourceEvent).bind (fun input =>
       input.token.map (fun token => deliveries (generated raw (consumeToken token.id m.input))))).getD Json.null),
     ("patterns",obj [("detached",toJson (pattern raw m.input .copy .detached)),
       ("archive",toJson (pattern raw m.input .replay .archive)),
       ("storage",toJson (pattern raw m.input .storage .store))]),
     ("temporalGap",toJson (!b.source.realized || !b.target.realized || decide (b.sourceStage+1≠b.targetStage)))])
-- Insert literal controls generated from committed manifest after declaration
-- commitment; append #eval here in the separate evaluation packet.
private def compatibleEpisodes (left right : FiniteAtomicLeg) : Bool :=
 match left.stages.getLast?,right.stages.head? with
 | some a,some b => decide (left.target=right.source ∧ a.frontier=b.frontier)
 | _,_ => false
private def atomicEndpointEdge (left right : FiniteAtomicLeg) : Bool :=
 (left.dependencies++right.dependencies).any fun edge =>
   edge.parent==left.sourceAudit && edge.child==right.targetAudit

'''

import argparse
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / 'lean/.validate-logs'
DECLARATION = 'audit/proposed_models/G5-RAW-DIRECT-CONTROLS.model.json'

def native_primitive_probe(manifest):
    declared = manifest['nativeControls']['overlapOnly']
    symbol = 'CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationCorridor.canonicalLeg'
    rule = 'eventAt selected id; get actual stage; source input is full stage frontier, event local stage, token id=stage, used=false, present=stage.realized, provenance=live; missing event/stage rejects'
    if (declared['episode'] != symbol or declared['inputRule'] != rule
        or declared['dependencyKind'] != 'all liveTemporal' or declared['dataGraph'] != []
        or type(declared['cell']) is not bool or len(declared['factor']) != 3
        or not all(type(bit) is bool for bit in declared['factor'])
        or not all(isinstance(seed,str) for seed in declared['seed'])):
        raise ValueError('unrecognized native overlap primitive adapter')
    fixed = 'true (false,false,false) ["native-past"]'
    parameters = lean_bool(declared['cell']) + ' (' + ','.join(lean_bool(bit) for bit in declared['factor']) + ') ' + lean_list(declared['seed'],lean_string)
    if NATIVE_PRIMITIVE_PROBE.count(fixed) != 1:
        raise ValueError('native primitive probe template drift')
    return NATIVE_PRIMITIVE_PROBE.replace(fixed,parameters)

def compare_cases(cases, observed):
    computed = {name:evaluate(model) for name,model in cases.items()}
    if computed != observed:
        differing = [name for name in set(computed)|set(observed) if computed.get(name)!=observed.get(name)]
        raise ValueError('Python/actual Lean raw readback drift: ' + ','.join(sorted(differing)))
    return computed

def selftest_drifts(cases, observed):
    def change(case, path, value):
        def mutate(models):
            models[case] = patched(models[case],[{'path':path,'value':value}])
        return mutate
    residue = list(reversed(cases['DS-POS-02B']['sourceInput']['payload']['residue']))
    changes = [
      ('whole source payload',change('directOnly','sourceInput.payload.predictive',9)),
      ('whole observed target',change('directOnly','stages.1.frontier.tick',9)),
      ('owner',change('directOnly','stages.1.frontier.owner',17)),
      ('ordered residue',change('DS-POS-02B','sourceInput.payload.residue',residue)),
      ('receiver instruction',change('directOnly','updates.0.orderAdvance',0)),
      ('missing source',change('directOnly','sourceInput',None)),
      ('missing payload',change('directOnly','sourceInput.payload',None)),
      ('missing token',change('directOnly','sourceInput.token',None)),
      ('token reuse',change('directOnly','sourceInput.token.used',True)),
      ('provenance',change('directOnly','sourceInput.provenance','archive')),
      ('graph edge',change('directOnly','dependencies',[])),
      ('global token alias',change('ALTERNATIVE','extraInputs.ds-alternative-source.token.id',99)),
      ('whole data payload binding',change('directWithData','dataGraph.0.payload.record',99)),
      ('missing data graph',change('directWithData','dataGraph',[])),
    ]
    for label,mutate in changes:
        models = copy.deepcopy(cases)
        mutate(models)
        try:
            compare_cases(models,observed)
        except ValueError:
            print('CAUGHT planted ' + label + ' transcription drift')
        else:
            raise AssertionError('missed planted ' + label + ' transcription drift')
    return len(changes)

def checked_lean(probe):
    (LOGS / 'g8-latest-evaluation-probe.lean').write_text(probe)
    with tempfile.TemporaryDirectory(prefix='g8-raw-evaluation-') as directory:
        path = Path(directory) / 'Probe.lean'
        path.write_text(probe)
        run = subprocess.run(['lake','env','lean',str(path)],cwd=ROOT/'lean',capture_output=True,text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        return json.loads(run.stdout.strip().splitlines()[-1])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Write the exact reviewed computation artifact.')
    parser.add_argument('--check-results', type=Path, help='Require exact agreement with an existing artifact.')
    args = parser.parse_args()
    declaration_bytes = (ROOT / DECLARATION).read_bytes()
    committed = subprocess.run(['git','show','HEAD:' + DECLARATION],cwd=ROOT,capture_output=True)
    if committed.returncode or committed.stdout != declaration_bytes:
        raise RuntimeError('Exact control declaration is not committed. No new control evaluated.')
    head = subprocess.check_output(['git','log','-1','--format=%H','--',DECLARATION],cwd=ROOT,text=True).strip()
    manifest = json.loads(declaration_bytes)
    verify_declared_sources(ROOT, manifest)
    cases = frozen_cases(manifest)
    native = checked_lean(native_primitive_probe(manifest))
    cases.update(native_cases(manifest, native))
    python_results = {name:evaluate(model) for name,model in cases.items()}
    probe = READOUT_PROBE_BASE
    exports = []
    identifiers = {}
    for index,(name,model) in enumerate(cases.items()):
        identifier = 'case' + str(index)
        identifiers[name] = identifier
        probe += lean_control(identifier,model)
        exports.append('(' + json.dumps(name) + ',observed ' + identifier + ')')
    path_results = {'twoDirect':compatible(cases['DS-POS-02A'],cases['DS-POS-02B']),
        'mixed':compatible(cases['overlapOnly'],cases['mixedDirect']),
        'twoDirectAtomicEndpointEdgePresent':atomic_endpoint_edge_present(cases['DS-POS-02A'],cases['DS-POS-02B']),
        'mixedAtomicEndpointEdgePresent':atomic_endpoint_edge_present(cases['overlapOnly'],cases['mixedDirect'])}
    path_exports = []
    for label,left,right in [('twoDirect','DS-POS-02A','DS-POS-02B'),('mixed','overlapOnly','mixedDirect')]:
        arguments = '('+identifiers[left]+'.episode) ('+identifiers[right]+'.episode)'
        path_exports.extend(['("'+label+'",toJson (compatibleEpisodes '+arguments+'))',
            '("'+label+'AtomicEndpointEdgePresent",toJson (atomicEndpointEdge '+arguments+'))'])
    probe += '\n#eval IO.println (Json.compress (obj [("cases",obj [' + ','.join(exports) + ']),("paths",obj [' + ','.join(path_exports) + '])]))\nend G8ReadoutProbe\n'
    lean_results = checked_lean(probe)
    compare_cases(cases,lean_results['cases'])
    if path_results != lean_results['paths']:
        raise ValueError('whole typed frontier / actual endpoint-edge readback drift')
    drift_count = selftest_drifts(cases,lean_results['cases'])
    result = {'schema':'csttt-raw-direct-control-evaluation-v1',
        'declarationCommit':head, 'declarationSha256':hashlib.sha256(declaration_bytes).hexdigest(),
        'classification':'b', 'controlsEvaluatedWithoutPrimitiveTuning':True,
        'plantedTranscriptionDriftsCaught':drift_count,
        'scope':'Finite raw control computation only; generic laws remain separately kernel proved. No TTD promotion.',
        'cases':python_results,
        'paths':path_results,
        'review':'See audit/G8b_raw_direct_evaluation.md for independent review.', 'nonclaims':['No Lean target bridge in this evaluation packet','No full TTD promotion']}
    if args.check_results is not None and json.loads(args.check_results.read_text()) != result:
        raise ValueError('stored raw-direct evaluation artifact drift')
    if args.output is not None:
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    (LOGS / 'g8-control-evaluation-materialized-primitives.json').write_text(json.dumps(cases,indent=2)+'\n')
    (LOGS / 'G8EvaluationActualProbe.lean').write_text(probe)
    print('PASS exact Python/Lean readback of ' + str(len(cases)) + ' frozen raw cases')
    for name,r in python_results.items():
        print(name + ': direct=' + str(r['direct']) + ', overlap=' + str(r['overlap']) + ', data=' + str(r['dataReachable']))
    print('Typed frontier compatibility: ' + json.dumps(result['paths']))

if __name__=='__main__':
    main()
