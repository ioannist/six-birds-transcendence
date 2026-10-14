#!/usr/bin/env python3
"""Compare Lean-evaluated raw TTH-09 tables with the frozen G3a JSON.

No source/result file is changed. Labels map source-order Fin indices to JSON
IDs; operative values/references are compared, not parsed out of Lean source.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def lean_snapshot():
    with tempfile.TemporaryDirectory(prefix='tth09-lean-', dir='/tmp') as folder:
        probe = Path(folder)/'Snapshot.lean'
        probe.write_text('import CSTTT.Transport.RouteLicenseExport\n#eval CSTTT.RouteLicenses.Models.routeSnapshot.compress\n')
        completed = subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=ROOT/'lean',
                                   check=True, capture_output=True, text=True)
    return json.loads(json.loads(completed.stdout.strip()))


def declared_tables(data):
    action_names = ['identity', 'toggle']  # BitAction constructor order, not verdicts
    states = data['shared_domains']['states']
    group = data['shared_domains']['clock_group']
    if (states != [0, 1] or group['elements'] != [0, 1] or group['identity'] != 0
            or group['operation'] != 'addition modulo 2'
            or group['inverse'] != 'each element is its own inverse'):
        raise AssertionError('declaration is not the transcribed bit/Z2 interface')
    actions = data['shared_domains']['actions']
    out = {'actions': [[actions[name][str(x)] for x in states] for name in action_names], 'models': []}
    for m in data['models']:
        def index(key):
            return {row['id']: i for i, row in enumerate(m[key])}
        routes, events, boundaries = (index(k) for k in ('routes', 'events', 'boundaries'))
        vertices = {v: i for i, v in enumerate(m['vertices'])}
        out['models'].append({
            'vertex_count': len(vertices),
            'routes': [{'path': [events[e] for e in r['events']], 'boundary': boundaries[r['boundary']]}
                       for r in m['routes']],
            'events': [{'entry': vertices[e['entry']], 'exit': vertices[e['exit']],
                        'available': e['available'], 'action_id': action_names.index(e['action']),
                        'action': [actions[e['action']][str(x)] for x in states],
                        'clock_increment': e['clock_increment'],
                        'clock_forward': [(x + e['clock_increment']) % 2 for x in states],
                        'clock_backward': [(x - e['clock_increment']) % 2 for x in states]}
                       for e in m['events']],
            'boundaries': [{'entry': vertices[b['entry']], 'exit': vertices[b['exit']], 'initial': b['initial_state']}
                           for b in m['boundaries']],
            'rewrites': [[routes[u], routes[v]] for u, v in m['raw_rewrites']],
            'ranks': [m['rewrite_ranks'][r['id']] for r in m['routes']],
            'critical': [[routes[u], routes[v]] for u, v in m['critical_pairs']],
            'completions': [{'left': routes[c['left']], 'right': routes[c['right']], 'join': routes[c['join']],
                             'left_path': [routes[r] for r in c['left_rewrite_path']],
                             'right_path': [routes[r] for r in c['right_rewrite_path']]}
                            for c in m['completions']],
            'domains': [{'boundary': boundaries[d['boundary']], 'routes': [routes[r] for r in d['routes']]}
                        for d in m['comparison_domains']],
        })
    return out


def compare(got, data):
    expected = declared_tables(data)
    if got != expected:
        raise AssertionError('Lean-evaluated raw snapshot differs from declared JSON tables')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model', nargs='?', type=Path, default=ROOT/'audit/proposed_models/TTH09-ROUTES.model.json')
    args = parser.parse_args()
    data = json.loads(args.model.read_text())
    got = lean_snapshot()
    compare(got, data)
    print('PASS: evaluated Lean data matches both frozen models.')
    print('Coverage: action tables on both bits; vertex counts; all route event paths/boundary references; '
          'event entry/exit/availability/action IDs/action outputs/clock increments/forward and inverse clock outputs; '
          'boundary entry/exit/initial bits; rewrites; ranks; critical pairs; every completion field/path; every domain.')
    print('JSON IDs are source-order labels; metadata/prose are not semantic inputs.')
    for label, mutate in [
        ('event availability', lambda d: d['models'][1]['events'][0].update(available=False)),
        ('raw route path', lambda d: d['models'][1]['routes'][0].update(events=['e_n0'])),
        ('clock increment', lambda d: d['models'][0]['events'][2].update(clock_increment=0)),
    ]:
        broken = deepcopy(data)
        mutate(broken)
        try:
            compare(got, broken)
        except AssertionError:
            print('CAUGHT planted JSON drift: '+label)
        else:
            raise AssertionError('checker missed planted drift: '+label)


if __name__ == '__main__':
    main()
