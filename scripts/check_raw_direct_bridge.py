#!/usr/bin/env python3
"""Check exported Lean controls against committed raw declarations and evaluation.

The kernel theorems are built separately. This exact transcription regression
checks their primitive inputs and computed observations, including every
optional source field and the full native episode. No release verdict is used.
"""
from pathlib import Path
import json
import subprocess
import tempfile

import evaluate_raw_direct_controls as raw

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / 'lean/.validate-logs'
CONTROL_NS = 'CSTTT.TargetTheory.RawDirectSuccessorControls.'
PATH_NS = 'CSTTT.TargetTheory.RawDirectSuccessorPaths.'
NAMES = {
    'DS-POS-01': 'dsPos01', 'DS-POS-02A': 'dsPos02A', 'DS-POS-02B': 'dsPos02B',
    'GAP': 'gapPrimitive', 'ALTERNATIVE': 'alternative', 'STORE': 'store',
    'directOnly': 'directOnly', 'dataOnly': 'dataOnly', 'directWithData': 'directWithData',
    'detached': 'detached', 'archive': 'archive', 'missingSource': 'missingSource',
    'missingPayload': 'missingPayload', 'missingToken': 'missingToken', 'usedToken': 'usedToken',
    'sourceAbsent': 'sourceAbsent', 'payloadDrift': 'payloadDrift', 'duplicateEvent': 'duplicateEvent',
    'gap': 'gap', 'alternativeParent': 'alternativeParent', 'storage': 'storage',
    'overlapOnly': 'overlapOnly', 'mixedDirect': 'mixedDirect',
}

WHOLE_MODEL_PROBE = r'''
import CSTTT.Targets.RawDirectSuccessorPaths
import Lean
open Lean CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor
namespace RawDirectBridgeProbe
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
private def kind : Kind → String
 | .liveTemporal => "liveTemporal" | .copy => "copy" | .replay => "replay" | .storage => "storage"
private def dependency (m : ControlModel) (e : RawDependency) : Json := obj [
 ("parent",toJson e.parent),("child",toJson e.child),("kind",toJson (kind (m.dependencyKind e.parent e.child)))]
private def update (u : ReadoutUpdate) : Json := obj [
 ("predictiveAdvance",toJson u.predictiveAdvance),("orderAdvance",toJson u.orderAdvance),
 ("tickAdvance",toJson u.tickAdvance),("progressAdvance",toJson u.progressAdvance),
 ("recordAdvance",toJson u.recordAdvance),("appendResidue",toJson u.appendResidue),
 ("nextMaintenance",toJson u.nextMaintenance),("nextOwner",toJson u.nextOwner)]
private def projection (p : Projection) : Json := obj [
 ("predictive",toJson p.predictive),("tick",toJson p.tick),("record",toJson p.record)]
private def sourceCell : Option SourceEvent → Json
 | none => Json.null
 | some s => obj [("stage",toJson s.stage),
   ("payload",match s.payload with | none => Json.null | some p => frontier p),
   ("token",match s.token with | none => Json.null | some t => obj [("id",toJson t.id),("used",toJson t.used)]),
   ("present",toJson s.present),
   ("provenance",toJson (match s.provenance with
     | .live => "live" | .detached => "detached" | .archive => "archive" | .store => "store"))]
private def dataEdge (e : DataEdge) : Json := obj [
 ("parent",toJson e.parent),("child",toJson e.child),("payload",frontier e.payload)]
private def model (m : ControlModel) (keys : List String) : Json := obj [
 ("sourceCarrier",toJson m.episode.source),("targetCarrier",toJson m.episode.target),
 ("sourceAudit",toJson m.episode.sourceAudit),("targetAudit",toJson m.episode.targetAudit),
 ("laterAudit",toJson m.episode.laterAudit),
 ("interventionMode",toJson (match m.episode.interventionMode with
   | .additive => "additive" | .mixedSupport => "mixedSupport")),
 ("stages",arr (m.episode.stages.map stage)),("events",arr (m.episode.events.map event)),
 ("dependencies",arr (m.episode.dependencies.map (dependency m))),
 ("updates",arr (m.episode.updates.map update)),
 ("base",projection m.episode.base),("sourceContribution",projection m.episode.sourceContribution),
 ("targetContribution",projection m.episode.targetContribution),
 ("inputBindings",obj (keys.map (fun id => (id,sourceCell (m.input id))))),
 ("dataGraph",arr (m.dataGraph.map dataEdge))]
'''


def run_lean(probe, label):
    (LOGS / (label + '.lean')).write_text(probe)
    with tempfile.TemporaryDirectory(prefix='raw-direct-bridge-') as directory:
        path = Path(directory) / 'Probe.lean'
        path.write_text(probe)
        result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT/'lean', capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return json.loads(result.stdout.strip().splitlines()[-1])


def normalized(model):
    keys = sorted(set([model['sourceAudit']] + [e['id'] for e in model['events']]
        + [e[k] for e in model['dependencies'] for k in ('parent', 'child')]
        + list(model.get('extraInputs', {}))))
    result = {k: model[k] for k in ('sourceCarrier', 'targetCarrier', 'sourceAudit', 'targetAudit',
        'laterAudit', 'stages', 'events', 'dependencies', 'updates', 'dataGraph')}
    result['interventionMode'] = model.get('interventionMode', 'additive')
    for field in ('base', 'sourceContribution', 'targetContribution'):
        result[field] = model.get(field, {'predictive': 0, 'tick': 0, 'record': 0})
    inputs = raw.assignment(model)
    result['inputBindings'] = {key: inputs.get(key) for key in keys}
    return result, keys


def main():
    declaration_bytes = (ROOT/raw.DECLARATION).read_bytes()
    committed = subprocess.run(['git', 'show', 'HEAD:' + raw.DECLARATION], cwd=ROOT, capture_output=True)
    if committed.returncode or committed.stdout != declaration_bytes:
        raise RuntimeError('raw declaration differs from committed HEAD')
    evaluation_path = 'audit/G8b_raw_direct_results.json'
    evaluation_bytes = (ROOT/evaluation_path).read_bytes()
    committed = subprocess.run(['git', 'show', 'HEAD:' + evaluation_path], cwd=ROOT, capture_output=True)
    if committed.returncode or committed.stdout != evaluation_bytes:
        raise RuntimeError('separate frozen evaluation packet is not committed')
    manifest = json.loads(declaration_bytes)
    frozen = json.loads(evaluation_bytes)
    raw.verify_declared_sources(ROOT, manifest)
    cases = raw.frozen_cases(manifest)
    native = run_lean(raw.native_primitive_probe(manifest), 'g8c-parent-native-primitives')
    cases.update(raw.native_cases(manifest, native))
    if set(cases) != set(NAMES):
        raise ValueError('public control-name coverage drift')
    expected = {}
    exports = []
    for name, model in cases.items():
        expected[name], keys = normalized(model)
        exports.append('(' + json.dumps(name) + ',model ' + CONTROL_NS + NAMES[name]
            + ' ' + raw.lean_list(keys, raw.lean_string) + ')')
    probe = WHOLE_MODEL_PROBE + '\n#eval IO.println (Json.compress (obj [' + ','.join(exports) + ']))\nend RawDirectBridgeProbe\n'
    actual = run_lean(probe, 'g8c-public-whole-model-readback')
    if expected != actual:
        mismatches = [name for name in cases if expected[name] != actual.get(name)]
        raise ValueError('whole exported raw primitive drift: ' + ','.join(mismatches))
    probe = 'import CSTTT.Targets.RawDirectSuccessorPaths\n' + raw.READOUT_PROBE_BASE
    exports = ['(' + json.dumps(name) + ',observed ' + CONTROL_NS + NAMES[name] + ')' for name in cases]
    paths = []
    for label, left, right in [('twoDirect', 'dsPos02A', 'dsPos02B'), ('mixed', 'overlapOnly', 'mixedDirect')]:
        paths.append('("' + label + '",toJson (compatibleEpisodes (' + CONTROL_NS + left
            + '.episode) (' + CONTROL_NS + right + '.episode)))')
        paths.append('("' + label + 'AtomicEndpointEdgePresent",toJson (' + PATH_NS
            + 'endpointEdgePresent ' + CONTROL_NS + left + ' ' + CONTROL_NS + right + '))')
    probe += '\n#eval IO.println (Json.compress (obj [("cases",obj [' + ','.join(exports)
    probe += ']),("paths",obj [' + ','.join(paths) + '])]))\nend G8ReadoutProbe\n'
    observed = run_lean(probe, 'g8c-public-computed-readback')
    raw.compare_cases(cases, observed['cases'])
    if observed['cases'] != frozen['cases'] or observed['paths'] != frozen['paths']:
        raise ValueError('exported computation differs from separately committed evaluation')
    count = raw.selftest_drifts(cases, observed['cases'])
    print('PASS exact whole exported raw models and committed observations for23 cases')
    print('PASS four actual boundary/endpoint-edge observations and' + str(count) + ' planted drifts')
    print('Kernel witnesses, refutations and actual ModelPath values are checked by the Lean build.')


if __name__ == '__main__':
    main()
