#!/usr/bin/env python3
"""In-memory group-sensitivity probes for every adopted route-license gate."""
from __future__ import annotations
import argparse
from copy import deepcopy
import json
from pathlib import Path
from evaluate_tth09_routes import ROOT, evaluate_model


class BaselineUnavailable(Exception):
    pass


def run_probes(data):
    source = next((m for m in data['models'] if m['model_id'] == 'TTH09-LICENSE-01'), None)
    if source is None:
        raise BaselineUnavailable('positive model is absent')
    shared = data['shared_domains']
    positive = evaluate_model(shared, source)
    if not positive['well_formedness']['pass']:
        raise BaselineUnavailable('positive model is not well formed')
    if 'D0' not in positive['domains'] or not all(positive['domains']['D0']['licenses'].values()):
        raise BaselineUnavailable('positive D0 sensitivity baseline is not licensed')
    probes = []

    def probe(group, gate, description, mutate):
        m = deepcopy(source)
        mutate(m)
        value = evaluate_model(shared, m)
        assert value['well_formedness']['pass'], f'probe {gate} accidentally malformed raw references'
        d = value['domains']['D0']
        assert not d[group+'_checks'][gate], f'BUG: {group}.{gate} still passes'
        names = {'normalization': 'normalization', 'flatness': 'flatness', 'confluence': 'confluence'}
        if group == 'domain':
            assert not d['domain_pass'] and not any(d['licenses'].values()), f'BUG: domain not gated by every license: {gate}'
        else:
            assert not d['licenses'][names[group]], f'BUG: license does not gate {group}.{gate}'
        probes.append({'group': group, 'gate': gate, 'perturbation': description,
                       'well_formed': value['well_formedness']['pass'], 'result': 'CAUGHT'})

    def event(m, key, value):
        next(e for e in m['events'] if e['id'] == 'e_a0')[key] = value

    def drop_completion(m):
        m['completions'] = [c for c in m['completions'] if c['left'] != 'a0']

    def no_edge(m):
        m['raw_rewrites'] = [e for e in m['raw_rewrites'] if e != ['a0', 'n0']]

    def cross_rewrite(m):
        m['raw_rewrites'].append(['a0', 'a1'])

    def duplicate_pair(m):
        m['critical_pairs'][0] = ['a0', 'a0']

    domain_changes = [
        ('multiple_routes', 'D0 keeps only a0', lambda m: m['comparison_domains'][0].update(routes=['a0'])),
        ('no_duplicates', 'append repeated a0 to D0', lambda m: m['comparison_domains'][0]['routes'].append('a0')),
        ('admissible', 'make e_a0 unavailable', lambda m: event(m, 'available', False)),
        ('boundary_members', 'change a0 boundary to b1', lambda m: m['routes'][0].update(boundary='b1')),
        ('rewrite_closed', 'add raw rewrite a0 → a1 outside D0', cross_rewrite),
    ]
    for gate, desc, mutate in domain_changes:
        probe('domain', gate, desc, mutate)
    def duplicate_path(m):
        m['routes'][0]['events'] = list(m['routes'][1]['events'])

    probe('domain', 'multiple_routes', 'give a0 the identical raw event path as n0', duplicate_path)
    probe('domain', 'no_duplicates', 'give a0 the identical raw event path as n0 despite different IDs', duplicate_path)
    probe('flatness', 'critical_members_distinct', 'give a0 the identical raw event path as n0', duplicate_path)
    # Each enclosing license also has its own domain conjunct.
    for group in ('normalization', 'flatness', 'confluence'):
        probe(group, 'domain', 'make e_a0 unavailable', lambda m: event(m, 'available', False))
    probe('normalization', 'rewrite_boundary', 'add cross-domain raw rewrite a0 → a1', cross_rewrite)
    probe('normalization', 'rank_decreases', 'cap a0 rank at zero', lambda m: m['rewrite_ranks'].update(a0=0))
    probe('normalization', 'rewrite_actions', 'change e_a0 action to toggle', lambda m: event(m, 'action', 'toggle'))
    probe('normalization', 'shared_unique_normal_form', 'delete a0 → n0 rewrite', no_edge)
    probe('confluence', 'rewrite_boundary', 'add cross-domain raw rewrite a0 → a1', cross_rewrite)
    probe('confluence', 'rewrite_actions', 'change e_a0 action to toggle', lambda m: event(m, 'action', 'toggle'))
    probe('confluence', 'all_pairs_joinable', 'delete a0 → n0 rewrite', no_edge)
    probe('flatness', 'event_clock_coherence', 'change e_a0 clock increment to 1', lambda m: event(m, 'clock_increment', 1))
    probe('flatness', 'critical_nonempty', 'delete the D0 critical pair', lambda m: m['critical_pairs'].pop(0))
    probe('flatness', 'critical_members_distinct', 'replace D0 pair by a0/a0', duplicate_pair)
    probe('flatness', 'critical_covers', 'replace D0 pair by a0/a0, leaving n0 uncovered', duplicate_pair)
    probe('flatness', 'completion_covers', 'delete D0 completion', drop_completion)
    probe('flatness', 'completion_members', 'change D0 completion join to n1 outside D0',
          lambda m: m['completions'][0].update(join='n1'))
    probe('flatness', 'completion_path_ends', 'replace left completion path by [n0]',
          lambda m: m['completions'][0].update(left_rewrite_path=['n0']))
    probe('flatness', 'completion_path_steps', 'insert unsupported n0 → a0 into left completion path',
          lambda m: m['completions'][0].update(left_rewrite_path=['a0', 'n0', 'a0', 'n0']))
    probe('flatness', 'completion_path_actions', 'change e_a0 action to toggle', lambda m: event(m, 'action', 'toggle'))
    probe('flatness', 'completion_connected', 'delete D0 completion edge, disconnecting the pair', drop_completion)
    probe('flatness', 'completion_rank_decreases', 'cap a0 rank at zero', lambda m: m['rewrite_ranks'].update(a0=0))
    probe('flatness', 'completion_shared_unique_normal_form', 'delete D0 completion, leaving two terminal Q forms', drop_completion)
    probe('flatness', 'zero_completed_holonomy', 'change e_a0 clock increment to 1', lambda m: event(m, 'clock_increment', 1))

    # Focused guards supplement the gate list; they are not new registered controls.
    probe('domain', 'admissible', 'change e_a0 exit to entry, breaking declared endpoint support',
          lambda m: event(m, 'exit', 'entry'))
    probe('flatness', 'critical_members_distinct', 'change critical pair to a0/a1; do not silently filter it out',
          lambda m: m['critical_pairs'].__setitem__(0, ['a0', 'a1']))
    probe('flatness', 'completion_path_ends', 'append a second malformed completion for the existing valid pair',
          lambda m: m['completions'].append({**m['completions'][0], 'left_rewrite_path': ['n0']}))
    expected = {group: set(positive['domains']['D0'][group+'_checks'])
                for group in ('domain', 'normalization', 'flatness', 'confluence')}
    for group, gates in expected.items():
        actual = {p['gate'] for p in probes if p['group'] == group}
        assert gates <= actual, f'untested gates in {group}: {gates-actual}'
    # Method checks for unrestricted finite closure: a cycle plus an exit saturates;
    # an isolated vertex remains isolated. This is not a model prediction.
    from evaluate_tth09_routes import closure
    reach = closure(['a', 'b', 'c', 'isolated'], [('a', 'b'), ('b', 'a'), ('b', 'c')])
    assert reach['a'] == ['a', 'b', 'c'] and reach['isolated'] == ['isolated']
    # Reporting-method guards: unavailable baselines and failed ancillary tests
    # must not suppress the independently computed scientific outcomes.
    import sys
    import tempfile
    from unittest.mock import patch
    from evaluate_tth09_routes import run
    broken = deepcopy(data)
    m = next(m for m in broken['models'] if m['model_id'] == 'TTH09-LICENSE-01')
    next(e for e in m['events'] if e['id'] == 'e_a0')['available'] = False
    with tempfile.TemporaryDirectory(prefix='g3b-reporting-', dir='/tmp') as folder:
        path = Path(folder)/'unavailable-baseline.json'
        path.write_text(json.dumps(broken))
        report = run(path, ROOT/'audit/G3_predictions.md')
        assert len(report['predictions']) == 20
        assert all(r['computed'] is not None for r in report['predictions'])
        assert report['counts']['FAILED'] > 0
        assert self_test_status(broken)['status'] == 'UNAVAILABLE'
    with patch.object(sys.modules[__name__], 'run_probes', side_effect=AssertionError('planted self-test failure')):
        report = run(ROOT/'audit/proposed_models/TTH09-ROUTES.model.json', ROOT/'audit/G3_predictions.md')
        assert report['counts']['CONFIRMED'] == 20
        assert self_test_status(data)['status'] == 'FAILED'
    return probes


def self_test_status(data):
    """Tests are ancillary: failures never erase independently computed predictions."""
    try:
        probes = run_probes(data)
        return {'status': 'PASS', 'detail': f'{len(probes)}/{len(probes)} sensitivity probes caught; all license gates covered; both reporting-method guards passed.', 'probes': probes}
    except BaselineUnavailable as exc:
        return {'status': 'UNAVAILABLE', 'detail': str(exc), 'probes': []}
    except Exception as exc:
        return {'status': 'FAILED', 'detail': f'{type(exc).__name__}: {exc}', 'probes': []}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model', nargs='?', type=Path,
                        default=ROOT/'audit/proposed_models/TTH09-ROUTES.model.json')
    args = parser.parse_args()
    test = self_test_status(json.loads(args.model.read_text()))
    probes = test['probes']
    print(f"SELF-TEST {test['status']}: {test['detail']}")
    print('Group-sensitivity probes; not exhaustive isolation of individual obligations.')
    print('CHECK | RAW PERTURBATION | RESULT')
    for p in probes:
        print(f"{p['group']}.{p['gate']} | {p['perturbation']} | {p['result']}")
    if test['status'] == 'PASS':
        print(f'{len(probes)}/{len(probes)} CAUGHT; all license gates covered; fixed-point and reporting-method checks PASS')
    return 0 if test['status'] == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
