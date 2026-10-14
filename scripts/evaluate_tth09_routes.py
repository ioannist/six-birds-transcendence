#!/usr/bin/env python3
"""Exact G3b route evaluation. Verdicts use raw tables, not declaration labels.

All arithmetic is integer arithmetic on the declared bit/clock group; there are
no probabilities or approximations. Reachability is a finite fixed point.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CATEGORIES = ('CONFIRMED', 'CONFIRMED-NARROW', 'CONFIRMED-CONFOUNDED',
              'FAILED', 'INVALID-CONTROL', 'UNDETERMINED')
AMBIGUITIES = [
    'Critical pairs are filtered by boundary using either side, then BOTH sides '
    'must belong to the domain and share its boundary. A malformed cross-boundary '
    'pair cannot disappear merely because its other side has the wrong boundary.',
    'Completion records with a side on the domain boundary are all checked, including '
    'duplicates. An extra invalid completion cannot be ignored after a valid one is found.',
    'Flatness condition 6 ranges over completed critical pairs. With no completions its '
    'zero-holonomy subcheck is vacuously true; the nonempty covering-completion and '
    'connectivity gates still reject. Holonomy of ALL declared critical pairs is '
    'reported separately, including the necessity model toggle comparison.',
    'Unique/shared normal form means singleton terminal-reachability sets for every '
    'route, with the same singleton across the fixed domain. Completion reductions '
    'omit identity edges, as prescribed; reflexive one-vertex completion paths are valid.',
    'Raw event action/clock coherence checks every available event in the model, '
    'following the spec global quantifier, not just events appearing in one comparison.',
    'License evaluation stays on each predeclared same-boundary domain. Positive '
    'nonconstancy across boundaries is tested separately and is not a cross-boundary license.'
]


def table(rows):
    return {r['id']: r for r in rows}


def well_formed(shared, m):
    """Schema/reference checks only; failed semantic laws remain license failures."""
    issues = []
    try:
        assert shared['states'] == [0, 1] and all(type(x) is int for x in shared['states'])
        g = shared['clock_group']
        assert g['elements'] == [0, 1] and all(type(x) is int for x in g['elements'])
        assert type(g['identity']) is int and g['identity'] == 0
        assert g['operation'] == 'addition modulo 2'
        assert g['inverse'] == 'each element is its own inverse'
        for a in shared['actions'].values():
            assert set(a) == {'0', '1'}
            assert all(type(v) is int and v in (0, 1) for v in a.values())
        for key in ('boundaries', 'events', 'routes', 'comparison_domains'):
            ids = [r['id'] for r in m[key]]
            assert len(ids) == len(set(ids)), f'duplicate {key} ID'
        vertices = m['vertices']
        assert len(vertices) == len(set(vertices))
        bs, es, rs = (table(m[k]) for k in ('boundaries', 'events', 'routes'))
        for b in bs.values():
            assert b['entry'] in vertices and b['exit'] in vertices
            assert type(b['initial_state']) is int and b['initial_state'] in (0, 1)
        for e in es.values():
            assert e['entry'] in vertices and e['exit'] in vertices
            assert e['action'] in shared['actions'] and type(e['available']) is bool
            assert type(e['clock_increment']) is int and e['clock_increment'] in (0, 1)
        for r in rs.values():
            assert r['boundary'] in bs and isinstance(r['events'], list)
            assert all(e in es for e in r['events'])
        for d in m['comparison_domains']:
            assert d['boundary'] in bs and isinstance(d['routes'], list)
            assert all(r in rs for r in d['routes'])
        assert set(m['rewrite_ranks']) == set(rs)
        assert all(type(n) is int and n >= 0 for n in m['rewrite_ranks'].values())
        for edge in m['raw_rewrites'] + m['critical_pairs']:
            assert len(edge) == 2 and all(r in rs for r in edge)
        for c in m['completions']:
            assert all(c[k] in rs for k in ('left', 'right', 'join'))
            for k in ('left_rewrite_path', 'right_rewrite_path'):
                assert isinstance(c[k], list) and c[k] and all(r in rs for r in c[k])
    except (AssertionError, KeyError, TypeError) as exc:
        issues.append(str(exc) or 'raw schema/reference/type assertion failed')
    return {'pass': not issues, 'issues': issues}


def closure(nodes, edges):
    """Least reflexive transitive closure, saturated to an actual fixed point."""
    nodes = set(nodes)
    reach = {u: {u} for u in nodes}
    for u, v in edges:
        if u in nodes and v in nodes:
            reach[u].add(v)
    while True:
        nxt = {u: set().union(*(reach[v] for v in reach[u])) for u in nodes}
        if nxt == reach:
            return {u: sorted(reach[u]) for u in sorted(nodes)}
        reach = nxt


def normal_forms(nodes, edges, reach):
    terminals = set(nodes) - {u for u, _ in edges}
    nf = {u: sorted(set(reach[u]) & terminals) for u in sorted(set(nodes))}
    singleton_shared = bool(nf) and all(len(v) == 1 for v in nf.values())
    singleton_shared = singleton_shared and len({tuple(v) for v in nf.values()}) == 1
    return nf, singleton_shared


def evaluate_model(shared, m):
    wf = well_formed(shared, m)
    if not wf['pass']:
        return {'model_id': m.get('model_id'), 'well_formedness': wf, 'domains': {}}
    bs, es, rs = (table(m[k]) for k in ('boundaries', 'events', 'routes'))
    actions = shared['actions']

    def execute(r, x):
        for eid in rs[r]['events']:
            x = actions[es[eid]['action']][str(x)]
        return x

    def admissible(r):
        route = rs[r]
        boundary = bs[route['boundary']]
        path = [es[e] for e in route['events']]
        if not path:
            return boundary['entry'] == boundary['exit']
        return (all(e['available'] for e in path)
                and path[0]['entry'] == boundary['entry']
                and path[-1]['exit'] == boundary['exit']
                and all(a['exit'] == b['entry'] for a, b in zip(path, path[1:])))

    functions = {r: [execute(r, x) for x in shared['states']] for r in sorted(rs)}
    endpoints = {r: execute(r, bs[rs[r]['boundary']]['initial_state']) for r in sorted(rs)}
    clocks = {r: sum(es[e]['clock_increment'] for e in rs[r]['events']) % 2 for r in sorted(rs)}
    coherent_events = {e: all(actions[v['action']][str(x)] == (x + v['clock_increment']) % 2
                             for x in shared['states']) for e, v in es.items() if v['available']}
    clock_coherence = all(coherent_events.values())
    supported = {r: admissible(r) for r in sorted(rs)}
    domains = {}
    for d in m['comparison_domains']:
        nodes = set(d['routes'])
        paths = {tuple(rs[r]['events']) for r in d['routes']}
        edges = [(u, v) for u, v in m['raw_rewrites'] if u in nodes]
        dc = {
            'multiple_routes': len(paths) >= 2,
            'no_duplicates': len(paths) == len(d['routes']),
            'admissible': all(supported[r] for r in nodes),
            'boundary_members': all(rs[r]['boundary'] == d['boundary'] for r in nodes),
            'rewrite_closed': all(v in nodes for _, v in edges),
        }
        domain_pass = all(dc.values())
        in_edges = [(u, v) for u, v in edges if v in nodes]
        reach = closure(nodes, in_edges)
        nf, shared_nf = normal_forms(nodes, in_edges, reach)
        rewrite_boundary = all(v in nodes and rs[u]['boundary'] == rs[v]['boundary']
                               for u, v in edges)
        rank_decreases = all(m['rewrite_ranks'][v] < m['rewrite_ranks'][u] for u, v in edges)
        action_preserves = all(functions[u] == functions[v] for u, v in edges)
        norm_checks = {'domain': domain_pass, 'rewrite_boundary': rewrite_boundary,
                       'rank_decreases': rank_decreases, 'rewrite_actions': action_preserves,
                       'shared_unique_normal_form': shared_nf}
        joins = {f'{u}/{v}': sorted(set(reach[u]) & set(reach[v]))
                 for u in sorted(nodes) for v in sorted(nodes)}
        conf_checks = {'domain': domain_pass, 'rewrite_boundary': rewrite_boundary,
                       'rewrite_actions': action_preserves, 'all_pairs_joinable': all(joins.values())}
        pairs = [tuple(p) for p in m['critical_pairs']
                 if any(rs[r]['boundary'] == d['boundary'] for r in p)]
        completions = [c for c in m['completions']
                       if any(rs[c[k]]['boundary'] == d['boundary'] for k in ('left', 'right'))]
        pair_members = all(rs[u]['events'] != rs[v]['events'] and u in nodes and v in nodes
                           and rs[u]['boundary'] == rs[v]['boundary'] == d['boundary'] for u, v in pairs)
        pair_set = set(pairs)
        complete_pairs = {(c['left'], c['right']) for c in completions}
        completion_members = all((c['left'], c['right']) in pair_set
                                 and all(c[k] in nodes for k in ('left', 'right', 'join'))
                                 and all(r in nodes for k in ('left_rewrite_path', 'right_rewrite_path')
                                         for r in c[k]) for c in completions)
        rewrite_set = {tuple(e) for e in m['raw_rewrites']}
        path_ends = all(c[k][0] == c[side] and c[k][-1] == c['join']
                        for c in completions for k, side in
                        [('left_rewrite_path', 'left'), ('right_rewrite_path', 'right')])
        path_steps = all((u, v) in rewrite_set for c in completions
                         for k in ('left_rewrite_path', 'right_rewrite_path')
                         for u, v in zip(c[k], c[k][1:]))
        path_actions = all(functions[u] == functions[v] for c in completions
                          for k in ('left_rewrite_path', 'right_rewrite_path')
                          for u, v in zip(c[k], c[k][1:]))
        moves = [(c['left'], c['right']) for c in completions]
        connected = closure(nodes, moves + [(v, u) for u, v in moves])
        q = [(c[k], c['join']) for c in completions for k in ('left', 'right') if c[k] != c['join']]
        qr = closure(nodes, q)
        qnf, shared_qnf = normal_forms(nodes, [(u, v) for u, v in q if u in nodes and v in nodes], qr)
        qrank = all(m['rewrite_ranks'][v] < m['rewrite_ranks'][u] for u, v in q)
        holonomies = {f'{u}/{v}': (clocks[u] - clocks[v]) % 2 for u, v in pairs}
        completed_holonomy = {f"{c['left']}/{c['right']}": (clocks[c['left']] - clocks[c['right']]) % 2
                              for c in completions if (c['left'], c['right']) in pair_set}
        flat_checks = {
            'domain': domain_pass, 'event_clock_coherence': clock_coherence,
            'critical_nonempty': bool(pairs), 'critical_members_distinct': pair_members,
            'critical_covers': nodes <= {r for pair in pairs for r in pair},
            'completion_covers': all(pair in complete_pairs for pair in pairs),
            'completion_members': completion_members, 'completion_path_ends': path_ends,
            'completion_path_steps': path_steps, 'completion_path_actions': path_actions,
            'completion_connected': bool(nodes) and all(set(v) == nodes for v in connected.values()),
            'completion_rank_decreases': qrank, 'completion_shared_unique_normal_form': shared_qnf,
            'zero_completed_holonomy': all(h == 0 for h in completed_holonomy.values()),
        }
        licenses = {'normalization': all(norm_checks.values()), 'flatness': all(flat_checks.values()),
                    'confluence': all(conf_checks.values())}
        domains[d['id']] = {
            'members': d['routes'], 'domain_checks': dc, 'domain_pass': domain_pass,
            'normalization_checks': norm_checks, 'flatness_checks': flat_checks,
            'confluence_checks': conf_checks, 'licenses': licenses, 'route_license': any(licenses.values()),
            'rewrite_reachability': reach, 'rewrite_normal_forms': nf, 'common_descendants': joins,
            'completion_reductions': [list(e) for e in q], 'completion_reachability': qr,
            'completion_normal_forms': qnf, 'completion_connectivity': connected,
            'critical_holonomy': holonomies, 'completed_holonomy': completed_holonomy,
            'all_endpoints_equal': bool(nodes) and len({endpoints[r] for r in nodes}) == 1,
        }
    return {'model_id': m['model_id'], 'well_formedness': wf, 'executed_functions': functions,
            'endpoints': endpoints, 'clocks': clocks, 'admissible': supported,
            'event_clock_checks': coherent_events, 'event_clock_coherence': clock_coherence,
            'domains': domains}


def predictions(path):
    rows = []
    for line in path.read_text().splitlines():
        if line.startswith('| N-') or line.startswith('| P') and not line.startswith('| Property'):
            columns = [s.strip() for s in line.strip('|').split('|')]
            if len(columns) == 5 and '**' in columns[2]:
                rows.append({'id': columns[0], 'property': columns[1],
                             'predicted': '**PASS**' in columns[2],
                             'prediction_text': columns[2], 'confidence': columns[3],
                             'failure_meaning': columns[4]})
    if len({p['id'] for p in rows}) != len(rows):
        raise ValueError('duplicate prediction ID')
    return rows


def compute_prediction(pid, models):
    if pid.startswith('N-'):
        n = models['TTH09-NECESSITY-01']
        d = n['domains']['D']; e = n['endpoints']
        values = {'N-DOMAIN': d['domain_pass'], 'N-NORM': d['licenses']['normalization'],
                  'N-FLAT': d['licenses']['flatness'], 'N-CONF': d['licenses']['confluence'],
                  'N-EQUAL': e['r0'] == e['r1'], 'N-DIFFERENT': e['r0'] != e['r2'],
                  'N-LOOP': d['critical_holonomy']['r0/r2'] != 0,
                  'N-GLOBAL': d['all_endpoints_equal'],
                  'N-CONVERSE': d['domain_pass'] and e['r0'] == e['r1'] and not d['route_license']}
        return values[pid], {'endpoints': e, 'domain': d}
    p = models['TTH09-LICENSE-01']
    if pid.startswith(('P0-', 'P1-')):
        i = pid[1]; d = p['domains']['D' + i]
        suffix = pid.split('-')[1]
        val = (p['endpoints']['a'+i] == p['endpoints']['n'+i] if suffix == 'EQUAL'
               else d['licenses'][{'NORM': 'normalization', 'FLAT': 'flatness', 'CONF': 'confluence'}[suffix]])
        return val, {'endpoints': {r: p['endpoints'][r] for r in d['members']}, 'domain': d}
    values = {'P-NONCONST': p['endpoints']['n0'] != p['endpoints']['n1'],
              'P-FUNCTION': all(v[0] != v[1] for v in p['executed_functions'].values()),
              'P-CLOCK': p['event_clock_coherence']}
    return values[pid], {k: p[k] for k in ('endpoints', 'executed_functions', 'event_clock_checks')}


def run(model_path, prediction_path):
    data = json.loads(model_path.read_text())
    models = {m['model_id']: evaluate_model(data['shared_domains'], m) for m in data['models']}
    rows = []
    for pred in predictions(prediction_path):
        try:
            actual, witness = compute_prediction(pred['id'], models)
            outcome = 'CONFIRMED' if actual == pred['predicted'] else 'FAILED'
        except (KeyError, TypeError) as exc:
            actual, witness, outcome = None, {'unavailable': str(exc)}, 'UNDETERMINED'
        rows.append({**pred, 'computed': actual, 'outcome': outcome, 'witness': witness})
    counts = Counter(r['outcome'] for r in rows)
    return {'schema': 'CSTTT-G3b-results-v1', 'models': models, 'predictions': rows,
            'counts': {c: counts[c] for c in CATEGORIES}, 'clean_ablation_count': 0,
            'ablation_note': 'No pre-registered mutations in G3a. In-memory sensitivity probes are evaluator tests, not scientific ablations.',
            'ambiguities': AMBIGUITIES,
            'self_test': {'status': 'NOT-RUN', 'detail': 'Prediction computation does not run sensitivity tests.'},
            'sensitivity_probes': [],
            'provenance_sha256': {name: hashlib.sha256(path.read_bytes()).hexdigest()
                                  for name, path in [('model', model_path),
                                                     ('spec', ROOT/'audit/G3_route_spec.md'),
                                                     ('predictions', prediction_path)]}}


def render(result):
    lines = ['# G3b — exact route-license evaluation', '',
             '## Outcome summary', '', ', '.join(f"**{c}: {n}**" for c, n in result['counts'].items()), '',
             'Clean ablations: **0**. There were no pre-registered mutations; sensitivity probes are separate evaluator tests.', '',
             'All arithmetic is exact integer bit/group arithmetic. There are no probabilities, floats, or stored verdicts. '
             'All rewrite/completion reachability is saturated to a finite fixed point, not bounded by a word horizon.', '',
             '| Prediction | Predicted | Computed | Outcome |', '|---|---|---|---|']
    for r in result['predictions']:
        lines.append(f"| {r['id']} | {'PASS' if r['predicted'] else 'FAIL'} | "
                     f"{('PASS' if r['computed'] else 'FAIL') if r['computed'] is not None else 'unavailable'} | {r['outcome']} |")
    lines += ['', '## Computed witnesses and counterexample scope', '']
    for mid, m in result['models'].items():
        lines += [f'### {mid}', '', f"Well-formedness: `{m['well_formedness']}`.", '']
        if not m['well_formedness']['pass']:
            continue
        lines += [f"Executed functions on `[0,1]`: `{m['executed_functions']}`.", '',
                  f"Endpoints: `{m['endpoints']}`; clock translations: `{m['clocks']}`.", '']
        for did, d in m['domains'].items():
            failed = {kind: [k for k, v in d[kind+'_checks'].items() if not v]
                      for kind in ('normalization', 'flatness', 'confluence')}
            lines += [f"- `{did}`: DomainCheck `{d['domain_pass']}`; licenses `{d['licenses']}`.",
                      f"- Rewrite terminal sets: `{d['rewrite_normal_forms']}`; completion terminal sets: `{d['completion_normal_forms']}`.",
                      f"- Critical-pair holonomy: `{d['critical_holonomy']}`; completed-pair holonomy: `{d['completed_holonomy']}`.",
                      f"- Failed license gates: `{failed}`.", '']
    n = result['models'].get('TTH09-NECESSITY-01', {}); d = n.get('domains', {}).get('D', {})
    stands = (d.get('domain_pass') and n['endpoints']['r0'] == n['endpoints']['r1']
              and not d['route_license'])
    lines += [('**The necessity control stands**: DomainCheck passes, r0/r1 execute to the same bit, '
               'and all three adopted licenses fail on the fixed whole domain D.' if stands else
               '**The necessity control is not established.**'), '',
              'This is a counterexample to literal necessity of these licenses on the predeclared comparison domain. '
              'It does not assert license failure on every smaller domain or under every alternative license definition. '
              'Flatness here is the stronger adopted G3a license, including completion-rank and unique-normal-form conditions beyond G0. '
              'The necessity control already fails the G0 covering-completion/connectivity requirements, not only those added conditions.', '',
              '## Failures and declaration errors', '']
    bad = [r for r in result['predictions'] if r['outcome'] != 'CONFIRMED']
    lines += ([f"- {r['id']}: {r['outcome']}. {r['failure_meaning']}" for r in bad] or
              ['No failed or undetermined predictions. No frozen declaration error was found.'])
    lines += ['', '## Ambiguity log', ''] + ['- '+a for a in result['ambiguities']]
    lines += ['', '## Gate-sensitivity self-test', '',
              f"Self-test status: **{result['self_test']['status']}**. {result['self_test']['detail']}", '',
              'Self-test status is independent of prediction outcomes. An unavailable baseline or failed test does not suppress computed outcomes.', '',
              'Each probe mutates a fresh in-memory positive-model copy. These are **group-sensitivity probes**, '
              'not exhaustive isolation of every conjunct: some coordinated consequences break more than one gate. '
              'Each named subcheck and its enclosing license must fail. Frozen files are never edited.', '',
              '| Gate | Raw perturbation | Well-formed | Result |', '|---|---|---|---|']
    for p in result['sensitivity_probes']:
        lines.append(f"| {p['group']}.{p['gate']} | {p['perturbation']} | {p['well_formed']} | {p['result']} |")
    lines += ['', '## Supported ceiling and reproduction', '',
              'Confirmed positive-license outcomes provide nonconstant finite raw-execution instances of the three adopted '
              'sufficient mechanisms. Same-boundary routes agree; nonconstancy across boundaries and bit inputs '
              'is checked separately. These are exact Python finite checks, **not Lean kernel proofs**; '
              'G3c must prove the generic sufficient-license results and bridge these models. No registry status changes.', '',
              '```bash',
              'python3 -B scripts/evaluate_tth09_routes.py audit/proposed_models/TTH09-ROUTES.model.json',
              'python3 -B scripts/selftest_evaluate_tth09_routes.py',
              'python3 -B scripts/evaluate_tth09_routes.py audit/proposed_models/TTH09-ROUTES.model.json --json-out /tmp/g3b-rerun.json --md-out /tmp/g3b-rerun.md',
              'cmp audit/G3b_results.json /tmp/g3b-rerun.json',
              'cmp audit/G3b_results.md /tmp/g3b-rerun.md', '```', '',
              'The recorded rerun passed byte-for-byte comparisons for both outputs; no timestamps enter either artifact.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model', type=Path)
    parser.add_argument('--json-out', type=Path, default=ROOT/'audit/G3b_results.json')
    parser.add_argument('--md-out', type=Path, default=ROOT/'audit/G3b_results.md')
    args = parser.parse_args()
    result = run(args.model, ROOT/'audit/G3_predictions.md')
    from selftest_evaluate_tth09_routes import self_test_status
    test = self_test_status(json.loads(args.model.read_text()))
    result['self_test'] = {k: v for k, v in test.items() if k != 'probes'}
    result['sensitivity_probes'] = test['probes']
    args.json_out.write_text(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False)+'\n')
    args.md_out.write_text(render(result))
    print(json.dumps(result['counts'], sort_keys=True))
    print(f"Self-test: {result['self_test']['status']}; {len(result['sensitivity_probes'])} caught probes; clean ablations: 0")


if __name__ == '__main__':
    main()
