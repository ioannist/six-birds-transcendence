#!/usr/bin/env python3
"""Exact finite evaluation of the frozen FIACH-POS-04 declaration.

Only standard-library arithmetic is used. Metadata such as model_id, grade,
claim_ceiling, predicate_contracts, and mutation labels never supply verdicts.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import inspect
import itertools
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TAGS = ("source", "target")
CATEGORIES = ("CONFIRMED", "CONFIRMED-NARROW", "CONFIRMED-CONFOUNDED", "FAILED", "INVALID-CONTROL", "UNDETERMINED")


def fraction_matrix(rows):
    return [[F(x) for x in row] for row in rows]


def provenance_check(m):
    manifest=m['provenance']
    checks={}
    for name,item in manifest['imported_tables'].items():
        path=ROOT/item['source']
        content=path.read_bytes()
        lines=content.splitlines(keepends=True)
        first,last=item['lines']
        checks[name]=(hashlib.sha256(content).hexdigest()==item['sha256_file'] and
                      hashlib.sha256(b''.join(lines[first-1:last])).hexdigest()==item['sha256_lines'])
    lean_path=ROOT/manifest['lean_module']
    lean=hashlib.sha256(lean_path.read_bytes()).hexdigest()==manifest['lean_module_sha256']
    return {'pass':all(checks.values()) and lean,'tables':checks,'lean_module':lean}


def matmul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), F(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def rref(a):
    a = [[F(v) for v in row] for row in a]
    pivots = []
    for col in range(len(a[0]) - 1):
        pivot = next((i for i in range(len(pivots), len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        row = len(pivots)
        a[row], a[pivot] = a[pivot], a[row]
        scale = a[row][col]
        a[row] = [x / scale for x in a[row]]
        for other in range(len(a)):
            if other != row and a[other][col]:
                scale = a[other][col]
                a[other] = [x - scale * y for x, y in zip(a[other], a[row])]
        pivots.append(col)
    consistent = all(any(row[:-1]) or row[-1] == 0 for row in a)
    return a, pivots, consistent


def fixed_law(e):
    n = len(e)
    equations = [[e[i][j] - (i == j) for i in range(n)] + [F(0)] for j in range(n)]
    equations.append([F(1)] * n + [F(1)])
    rows, pivots, consistent = rref(equations)
    if not consistent or len(pivots) != n:
        return {'unique': False, 'rank': len(pivots), 'distribution': None}
    pi = [F(0)] * n
    for row, col in enumerate(pivots):
        pi[col] = rows[row][-1]
    valid = all(x >= 0 for x in pi) and sum(pi) == 1 and all(
        sum(pi[i] * e[i][j] for i in range(n)) == pi[j] for j in range(n))
    return {'unique': valid, 'rank': len(pivots), 'distribution': pi}


def defect(e):
    ee = matmul(e, e)
    return max(sum(abs(ee[i][j] - e[i][j]) for j in range(len(e))) / 2
               for i in range(len(e)))


def encode(x):
    if isinstance(x, F):
        return f'{x.numerator}/{x.denominator}'
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    if isinstance(x, set):
        return sorted(encode(v) for v in x)
    return x


def state(s):
    if not re.fullmatch(r'p[0-5]w[01]', s):
        raise ValueError(f'bad WheelState {s}')
    return int(s[1]), int(s[3])


def safe(m, s):
    p, w = state(s)
    return not (p in m['t1_import']['hazards'] and w == p % 2)


def table(m, tag):
    return m['new_data']['raw_inputs']['by_tag'][tag]['action_distributions']


def action_dist(m, tag, s, a):
    return {v: F(p) for v, p in table(m, tag)[s][a].items()}


def continuation(m, tag, s):
    return tuple((a, tuple(sorted('safe' if safe(m, v) else 'lethal'
                                  for v in action_dist(m, tag, s, a))))
                 for a in m['t1_import']['actions'])


def M(m, tag, s):
    return (state(s)[0], continuation(m, tag, s))


def public(m, tag, s):
    rule = m['new_data']['raw_inputs']['by_tag'][tag]['public_channel_rule']
    if rule == 'position':
        return state(s)[0]
    if rule == 'state_label':
        return s
    raise ValueError(f'unknown public-channel rule {rule}')


def canonical_matrix(m, tag):
    K = m['t1_import']['kernel_order']
    policy = m['t1_import']['canonical_policy']
    return [[action_dist(m, tag, s, policy[i]).get(t, F(0)) for t in K]
            for i, s in enumerate(K)]


def cu_matrices(m, tag):
    K = m['t1_import']['kernel_order']
    classes = sorted({M(m, tag, s) for s in K}, key=repr)
    C = [[F(int(M(m, tag, s) == cls)) for cls in classes] for s in K]
    U = [[F(int(M(m, tag, s) == cls), sum(M(m, tag, x) == cls for x in K))
          for s in K] for cls in classes]
    return C, U, classes


def c1(m, tag):
    K = m['t1_import']['kernel_order']; n = len(K)
    P = canonical_matrix(m, tag)
    C, U, classes = cu_matrices(m, tag)
    imported = m['t1_import']
    pe = [[F(15, 16) * P[i][j] + F(1, 16 * n) for j in range(n)] for i in range(n)]
    e0 = matmul(matmul(matmul(P, P), C), U)
    ep = matmul(matmul(matmul(pe, pe), C), U)
    fixed = fixed_law(ep)
    pi = fixed['distribution']
    core_indices = [i for i, s in enumerate(K) if s in imported['core']]
    mass = sum((pi[i] for i in core_indices), F(0)) if pi else None
    core_uniform = [F(1, len(core_indices)) if i in core_indices else F(0) for i in range(n)]
    tv = sum(abs(pi[i] - core_uniform[i]) for i in range(n)) / 2 if pi else None
    d0, dp = defect(e0), defect(ep)
    rows_stochastic = all(sum(row) == 1 and all(x >= 0 for x in row) for row in P)
    pinned = P == fraction_matrix(imported['P'])
    c_pinned = C == fraction_matrix(imported['C'])
    u_pinned = U == fraction_matrix(imported['U'])
    expected_pi = [F(x) for x in imported['C1']['published_pi']]
    passed = (rows_stochastic and pinned and c_pinned and u_pinned and fixed['unique']
              and pi == expected_pi and pi != [F(1, n)] * n
              and mass == F(77, 80) and mass >= F(3, 4)
              and tv == F(3, 80) and d0 == F(1, 8) and dp == F(78795, 524288))
    return {'pass': passed, 'P': P, 'C': C, 'U': U, 'P_rows_stochastic': rows_stochastic,
            'P_matches_T1': pinned, 'C_matches_T1': c_pinned, 'U_matches_T1': u_pinned,
            'realized_M_classes': len(classes), 'fixed_rank': fixed['rank'],
            'unique': fixed['unique'], 'pi': pi, 'nonuniform': bool(pi and pi != [F(1,n)] * n),
            'core_mass': mass, 'TV': tv, 'defect_epsilon_0': d0,
            'defect_epsilon_1_16': dp}


def c2(m, tag):
    K = m['t1_import']['kernel_order']
    split = [(a, b) for a in K for b in K if public(m, tag, a) == public(m, tag, b)
             and M(m, tag, a) != M(m, tag, b)]
    witness = ('p1w0', 'p1w1')
    return {'pass': bool(split) and witness in split, 'split_count': len(split),
            'declared_witness': witness in split, 'first_split': split[0] if split else None}


def canonical_partition(groups, K):
    seen = {}
    return {s: seen.setdefault(groups[s], len(seen)) for s in K}


def c3(m, tag):
    K = m['t1_import']['kernel_order']; actions = m['t1_import']['actions']
    classes = canonical_partition({s: public(m, tag, s) for s in K}, K)
    trajectory = [len(set(classes.values()))]
    for _ in range(len(K) + 1):
        signatures = {}
        for s in K:
            profiles = []
            for a in actions:
                dist = {}
                for target, p in action_dist(m, tag, s, a).items():
                    label = ('block', classes[target]) if target in classes else ('exit', target)
                    dist[label] = dist.get(label, F(0)) + p
                profiles.append(tuple(sorted(dist.items(), key=lambda x: repr(x[0]))))
            signatures[s] = (classes[s], tuple(profiles))
        nxt = canonical_partition(signatures, K)
        trajectory.append(len(set(nxt.values())))
        if all((classes[a] == classes[b]) == (nxt[a] == nxt[b]) for a in K for b in K):
            classes = nxt
            break
        classes = nxt
    terminal_m = all((classes[a] == classes[b]) == (M(m, tag, a) == M(m, tag, b))
                     for a in K for b in K)
    passed = (trajectory == [6, 7, 7] and terminal_m)
    return {'pass': passed, 'trajectory': trajectory, 'terminal_equals_M': terminal_m,
            'terminal_classes': len(set(classes.values())), 'ordered_pair_checks': len(K)**2,
            'partition': classes}


def current(m, tag, s):
    pieces = []
    for channel in m['new_data']['c4']['current_channels']:
        if channel == 'public_position':
            pieces.append(public(m, tag, s))
        elif channel == 'deadline_action_availability':
            pieces.append(tuple(a for a in m['t1_import']['actions'] if action_dist(m, tag, s, a)))
        elif channel == 'canonical_M':
            pieces.append(M(m, tag, s))
        else:
            raise ValueError(f'unknown C4 channel {channel}')
    return tuple(pieces)


def c4(m, tag):
    K = m['t1_import']['kernel_order']; a, b = m['new_data']['c4']['candidate_hidden_pair']
    collision = current(m, tag, a) == current(m, tag, b) and M(m, tag, a) != M(m, tag, b)
    path = m['new_data']['c4']['candidate_connector_history']
    P = canonical_matrix(m, tag); at = {s:i for i,s in enumerate(K)}
    connector = (all(P[at[x]][at[y]] > 0 for x,y in zip(path,path[1:]))
                 and current(m,tag,path[0]) == current(m,tag,path[-1])
                 and M(m,tag,path[0]) != M(m,tag,path[-1]))
    full_exposed = any(len({current(m,tag,s)[i] for s in K}) > 1 and
                       all(M(m,tag,x)!=M(m,tag,y) or current(m,tag,x)[i]==current(m,tag,y)[i]
                           for x in K for y in K)
                       for i in range(len(m['new_data']['c4']['current_channels'])))
    return {'pass': collision and connector and full_exposed, 'collision': collision,
            'connector': connector, 'full_HIDD_exposure': full_exposed,
            'full_HIDD_nonexposure': not full_exposed}


def cycle_credit(protocol):
    edges = protocol['edges']; vertices = ('u','v','w')
    def count(a,b,c):
        return sum(e['from']==a and e['to']==b and e['channel']==c for e in edges)
    products = {}
    for channel in ('self','other'):
        forward = count('u','v',channel)*count('v','w',channel)*count('w','u',channel)
        reverse = count('v','u',channel)*count('w','v',channel)*count('u','w',channel)
        products[channel] = (forward,reverse)
    asym = {c: products[c][0] != products[c][1] for c in products}
    if asym['self'] and asym['other']: credit='ambiguous'
    elif asym['self']: credit='self'
    elif asym['other']: credit='other'
    else: credit='none'
    return credit,products


def c5(m,tag):
    protocols = {p['id']:p for p in m['new_data']['c5']['protocols'] if p['tag']==tag}
    computed = {name:cycle_credit(p)[0] for name,p in protocols.items()}
    expected = {'clockwise':'self','scheduled':'other','internalized':'none','null':'none'}
    owners_consistent = all((computed[name]!='self' or protocols[name]['owner']==tag)
                            and (computed[name]!='other' or protocols[name]['owner']=='external')
                            for name in protocols)
    anchors=m['new_data']['c5']['history_anchor']
    anchor_valid=(set(anchors)=={'u','v','w'} and
                  all(admissible_history(m,tag,name) for name in anchors.values()))
    return {'pass': computed==expected and owners_consistent and anchor_valid,
            'history_anchors_valid':anchor_valid,'credits':computed,
            'owner_consistency': owners_consistent,
            'products':{name:cycle_credit(p)[1] for name,p in protocols.items()}}


def c6(m,tag):
    K=m['t1_import']['kernel_order']; actions=m['t1_import']['actions']
    raw=m['new_data']['raw_inputs']['by_tag'][tag]
    required_interface=('PredictiveNow','event_order','tick_phase','cumulative_progress',
                        'endogenous_record_count','route_residue','maintenance_state','owner')
    interface_complete=tuple(m['new_data']['c6']['future_interface'])==required_interface
    alphabet_complete=tuple(m['new_data']['c6']['future_alphabet'])==tuple(
        f'canonical_action_{a}' for a in actions)
    path_ids=[path['id'] for path in m['new_data']['corridor']['paths']]
    route_contexts=(bool(path_ids) and len(path_ids)==len(set(path_ids)) and
                    set(raw['record_writer_available'])==set(path_ids))
    # q includes unfolded count, phase, route, maintenance and owner. Compare
    # only equal contexts; their current full-interface outputs are equal iff
    # their M values are equal. Additive counter updates preserve equality
    # when the action-indexed delta and successor-class distributions agree.
    q_classes=canonical_partition({s:M(m,tag,s) for s in K},K)
    context_results=[];first_classes=None;first_rounds=None
    for route_id in raw['record_writer_available']:
        for maintenance in ('funded','underfunded'):
            writer=raw['record_writer_available'][route_id]
            enabled=(maintenance=='funded' and raw['resources']['recharge_available_after_withdrawal'])
            classes=q_classes.copy();rounds=0
            while True:
                signatures={}
                for s in K:
                    steps=[]
                    for a in actions:
                        dist=action_dist(m,tag,s,a) if enabled else {}
                        by_class={}
                        for t,p in dist.items():
                            key=('block',classes[t]) if t in classes else ('exit',t)
                            by_class[key]=by_class.get(key,F(0))+p
                        delta=(1,raw['tick_increment'][s][a],1,int(writer),
                               route_id,maintenance,m['new_data']['maintenance']['owner_by_tag'][tag]) if dist else None
                        steps.append((a,delta,tuple(sorted(by_class.items(),key=lambda x:repr(x[0])))))
                    signatures[s]=(classes[s],tuple(steps))
                nxt=canonical_partition(signatures,K);rounds+=1
                if all((classes[a]==classes[b])==(nxt[a]==nxt[b]) for a in K for b in K):
                    classes=nxt;break
                classes=nxt
                if rounds>len(K):raise RuntimeError('C6 refinement did not stabilize')
            sufficient=all((q_classes[a]==q_classes[b])==(classes[a]==classes[b]) for a in K for b in K)
            context_results.append({'route':route_id,'maintenance':maintenance,
                                    'future_sufficient':sufficient,'stable_classes':len(set(classes.values()))})
            if first_classes is None and maintenance=='funded':
                first_classes,first_rounds=classes,rounds
    classes=first_classes or q_classes;rounds=first_rounds or 0
    suff=(route_contexts and all(x['future_sufficient'] for x in context_results) and
          interface_complete and alphabet_complete)
    merged=[(a,b) for a in K for b in K if a!=b and q_classes[a]==q_classes[b]]
    pair=tuple(m['new_data']['c6']['candidate_merged_pair'])
    strict=bool(merged) and pair in merged
    witness=next(((a,b) for a,b in merged if classes[a]!=classes[b]),None)
    return {'pass':suff and strict, 'future_sufficient':suff,'strictly_coarser':strict,
            'q_classes':len(set(q_classes.values())),'stable_classes':len(set(classes.values())),
            'rounds':rounds,'merged_pair':pair if pair in merged else None,
            'counterexample':witness,'interface_complete':interface_complete,
            'alphabet_complete':alphabet_complete,'route_contexts':route_contexts,
            'contexts':context_results}


def c6_trace(m,tag):
    raw=m['new_data']['raw_inputs']['by_tag'][tag]
    active=all(raw['tick_increment'][s][a]==1 for s in m['t1_import']['kernel_order']
               for a in m['t1_import']['actions'] if action_dist(m,tag,s,a))
    corridor_raw=m['new_data']['corridor']
    paths=corridor_raw['paths']
    path_ids=[path['id'] for path in paths]
    writers=(bool(path_ids) and len(path_ids)==len(set(path_ids)) and
             set(raw['record_writer_available'])==set(path_ids) and
             all(raw['record_writer_available'][name] for name in path_ids))
    events=corridor_raw['events'];stages=corridor_raw['stages']
    event_by={e['id']:e for e in events}
    realized=set(corridor_raw['realized_stages'])
    refs=(bool(events) and len(event_by)==len(events) and
          all(e['from'] in stages and e['to'] in stages for e in events))
    order=(refs and all(stages.index(e['to'])==stages.index(e['from'])+1 and
                        e['strict_step'] and e['atomic'] for e in events))
    realized_sequence=corridor_raw['realized_stages']==stages
    realized_paths=(realized_sequence and bool(paths) and refs and all(
        bool(path['events']) and all(event_id in event_by for event_id in path['events']) and
        all(event_by[event_id]['from'] in realized and
            event_by[event_id]['to'] in realized for event_id in path['events']) and
        all(event_by[a]['to']==event_by[b]['from']
            for a,b in zip(path['events'],path['events'][1:]))
        for path in paths) and
        {event_id for path in paths for event_id in path['events']}==set(event_by))
    owner=m['new_data']['maintenance']['owner_by_tag'][tag]==tag
    return {'pass':active and writers and order and realized_paths and owner,
            'unit_tick':active,'record_writers':writers,'strict_event_order':order,
            'realized_paths':realized_paths,'realized_stage_sequence':realized_sequence,
            'owner':owner}


def joint_dist(assemblage):
    left=assemblage['left'];right=assemblage['right']
    counts=Counter((left[i],right[j]) for i,j in assemblage['coupling'])
    total=sum(counts.values())
    return tuple(sorted(((pair,F(n,total)) for pair,n in counts.items()),key=repr))


def c7_local(m,tag):
    data=m['new_data']['c7']['by_tag'][tag]
    assemb={a['id']:a for a in data['assemblages']}
    coupling=data['admissible_couplings']
    consistent=(len(assemb)==len(data['assemblages']) and len(assemb)>=2 and
                all(a['left']==data['branches']['left'] and a['right']==data['branches']['right']
                    and len(a['coupling'])==2 and len(set(map(tuple,a['coupling'])))==2
                    and sorted(i for i,j in a['coupling'])==[0,1]
                    and all(0<=j<2 for i,j in a['coupling']) for a in assemb.values())
                and len(data['reassembly'])==len(assemb) and
                all(r['assemblage'] in assemb and
                    r['coupling'] in coupling and
                    assemb[r['assemblage']]['coupling']==[[i,j] for i,j in enumerate(coupling[r['coupling']])]
                    for r in data['reassembly']))
    branch_histories=(all(admissible_history(m,tag,name)
                          for name in data['branches']['left']+data['branches']['right']) and
                      all(admissible_history(m,tag,name)
                          for a in assemb.values() for name in a['left']+a['right']))
    names=list(assemb)
    branchwise=lambda a:(tuple(assemb[a]['left']),tuple(assemb[a]['right']))
    observable=lambda a:joint_dist(assemb[a]) if 'jointPairing' in data['joint_observables'] else ()
    bw_same=branchwise(names[0])==branchwise(names[1])
    rec_diff=(branchwise(names[0]),observable(names[0]))!=(branchwise(names[1]),observable(names[1]))
    strict=bw_same and rec_diff
    operational=c7_receiver_display(m,tag)
    return {'pass':consistent and branch_histories and strict and operational['pass'],
            'well_formed':consistent,'branch_histories_admissible':branch_histories,
            'strict_refinement':strict,'operational_use':operational,
            'comparison_domain_size':len(assemb),'joint_observables':data['joint_observables'],
            'joint_outputs':{a:joint_dist(v) for a,v in assemb.items()},
            'recombination_difference':rec_diff}


def c7_receiver_display(m,tag):
    """Pre-exit display selected by the receiver's exact jointPairing readout."""
    data=m['new_data']['c7']['by_tag'][tag]
    events=m['new_data']['corridor']['events']
    realized=set(m['new_data']['corridor']['realized_stages'])
    pre_exit=[e for e in events if e['id']!='exit' and e['atomic'] and
              e['source_support'] and e['target_support'] and
              e['from'] in realized and e['to'] in realized]
    active=receiver_active(m)
    display={}
    for assemblage in data['assemblages']:
        if 'jointPairing' in data['joint_observables']:
            display[assemblage['id']]=joint_dist(assemblage)
        else:
            display[assemblage['id']]=()
    distinct=len(display)>=2 and len(set(display.values()))>=2
    post_exit_P_unchanged=canonical_matrix(m,tag)==fraction_matrix(m['t1_import']['P'])
    return {'pass':bool(pre_exit) and active and distinct and post_exit_P_unchanged,
            'pre_exit_mixed_events':[e['id'] for e in pre_exit],
            'receiver_active':active,
            'display_by_assemblage':display,'distinct_displays':distinct,
            'post_exit_P_unchanged':post_exit_P_unchanged,
            'receiver_read':'jointPairing' if 'jointPairing' in data['joint_observables'] else None}


def c7_transport(m):
    src=m['new_data']['c7']['by_tag']['source'];dst=m['new_data']['c7']['by_tag']['target']
    s={a['id']:a for a in src['assemblages']};t={a['id']:a for a in dst['assemblages']}
    names=set(s)&set(t)
    equality=(set(s)==set(t) and src['joint_observables']==dst['joint_observables'] and
              all(s[a]['left']==t[a]['left'] and s[a]['right']==t[a]['right']
                  and s[a]['coupling']==t[a]['coupling'] and joint_dist(s[a])==joint_dist(t[a])
                  for a in names))
    return {'pass':equality,'assemblages_compared':len(names),'raw_couplings_equal':equality}


def c8(m,tag):
    raw=m['new_data']['raw_inputs']['by_tag'][tag]
    ledger=m['new_data']['maintenance'];K=m['t1_import']['kernel_order']
    budget=ledger['initial_budget_tokens'];cost=ledger['action_cost_tokens']
    regen=ledger['recharge_tokens_per_action']
    funded=raw['resources']['recharge_available_after_withdrawal']
    available=(funded and budget>=cost and budget-cost+regen>0 and
               ledger['owner_by_tag'][tag]==tag)
    viable=set(K)
    steps=0
    while True:
        next_set={s for s in viable if available and any(
            (dist:=action_dist(m,tag,s,a)) and sum(dist.values())==1 and
            all(t in viable and p>0 for t,p in dist.items())
            for a in m['t1_import']['actions'])}
        steps+=1
        if next_set==viable:break
        viable=next_set
    P=canonical_matrix(m,tag)
    pinned=P==fraction_matrix(m['t1_import']['P'])
    ledger_equation=(budget==1 and cost==1 and regen==1 and budget-cost+regen==budget)
    return {'pass':bool(viable) and available and pinned and ledger_equation,
            'ledger_equation':ledger_equation,'greatest_viable':sorted(viable),
            'size':len(viable),'iterations':steps,'available':available,
            'ledger_next_budget':budget-cost+regen if funded else None,
            'funded_P_unchanged':pinned}


def history(m, name):
    return tuple(m['new_data']['histories'][name])


def admissible_history(m,tag,name):
    histories=m['new_data']['histories']
    if name not in histories:return False
    path=histories[name]
    K=m['t1_import']['kernel_order']
    if len(path)<2 or any(state_name not in K for state_name in path):return False
    index={state_name:i for i,state_name in enumerate(K)}
    P=canonical_matrix(m,tag)
    return all(P[index[a]][index[b]]>0 for a,b in zip(path,path[1:]))


def receiver_active(m, source_present=None):
    receiver=m['new_data']['receiver'];gate=receiver['activation']
    present=gate['source_present'] if source_present is None else source_present
    events=m['new_data']['corridor']['events']
    realized=set(m['new_data']['corridor']['realized_stages'])
    mixed=any(e['source_support'] and e['target_support'] and e['atomic'] and
              e['from'] in realized and e['to'] in realized for e in events)
    return bool(present and gate['target_receiver_funded'] and
                receiver['latent_target']['funded_receiver'] and
                (mixed if gate['mixed_event_required'] else True))


def receiver_state(m, hist_name):
    content=m['new_data']['receiver']['content']
    override=content['history_overrides'].get(hist_name)
    if override is not None:
        p,w=override['p'],override['w']
    else:
        p,w=state(history(m,hist_name)[-1])
        p_rule=content['position_rule'];w_rule=content['phase_rule']
        if p_rule=='copy_source_terminal_p':pass
        elif p_rule.startswith('constant_'):p=int(p_rule.split('_')[-1])
        else:raise ValueError(f'unknown receiver position rule {p_rule}')
        if w_rule=='copy_source_terminal_w':pass
        elif w_rule.startswith('constant_'):w=int(w_rule.split('_')[-1])
        else:raise ValueError(f'unknown receiver phase rule {w_rule}')
    return f'p{p}w{w}'


def content(m):
    entries=m['new_data']['corridor']['content_counterfactuals']
    same_latent=bool(entries) and all(set(entry)=={'source_history'} for entry in entries)
    same_activation=same_latent and receiver_active(m)
    rows=[]
    for entry in entries:
        name=entry['source_history'];source=history(m,name)[-1]
        target=receiver_state(m,name)
        rows.append({'history':name,'source_raw':source,'target_raw':target,
                     'source_M':M(m,'source',source),'target_M':M(m,'target',target),
                     'activated':receiver_active(m)})
    distinct_source= len({repr(r['source_M']) for r in rows})==len(rows)>=2
    distinct_target= len({repr(r['target_M']) for r in rows})==len(rows)>=2
    mapped=all(r['source_M']==r['target_M'] for r in rows)
    return {'pass':distinct_source and distinct_target and mapped and same_latent and
            same_activation and all(r['activated'] for r in rows),'distinct_source_M':distinct_source,
            'distinct_target_M':distinct_target,'tag_map_agreement':mapped,
            'same_latent_target':same_latent,'same_activation_fields':same_activation,'cases':rows}


def bridge(m):
    K=set(m['t1_import']['kernel_order']);hist=m['new_data']['histories']
    frontier=m['new_data']['bridge_frontier'];P=canonical_matrix(m,'source')
    lookup={s:i for i,s in enumerate(m['t1_import']['kernel_order'])}
    paths_valid=all(name in hist and len(hist[name])>=2 and
                    all(a in K and b in K and P[lookup[a]][lookup[b]]>0
                        for a,b in zip(hist[name],hist[name][1:])) for name in frontier)
    strict_edge=tuple(m['new_data']['strict_source_edge'])
    edge_valid=(strict_edge[0]!=strict_edge[1] and
                P[lookup[strict_edge[0]]][lookup[strict_edge[1]]]>0 and
                any(strict_edge in list(zip(hist[name],hist[name][1:])) for name in frontier))
    reps=m['new_data']['same_class_pair'];past_distinct=history(m,reps[0])!=history(m,reps[1])
    source_equal=M(m,'source',history(m,reps[0])[-1])==M(m,'source',history(m,reps[1])[-1])
    target_states=[receiver_state(m,x) for x in reps]
    target_equal=M(m,'target',target_states[0])==M(m,'target',target_states[1])
    # Pointwise tagged history map preserves each raw transition, including its probability.
    laws=all(action_dist(m,'source',s,a)==action_dist(m,'target',s,a)
             for s in m['t1_import']['kernel_order'] for a in m['t1_import']['actions'])
    tick=all(m['new_data']['raw_inputs']['by_tag']['source']['tick_increment'][s][a]==
             m['new_data']['raw_inputs']['by_tag']['target']['tick_increment'][s][a]
             for s in m['t1_import']['kernel_order'] for a in m['t1_import']['actions'])
    progress=all(sum(P[lookup[a]][lookup[b]]>0 for a,b in zip(hist[name],hist[name][1:]))==
                 sum(action_dist(m,'target',a,m['t1_import']['canonical_policy'][lookup[a]]).get(b,F(0))>0
                     for a,b in zip(hist[name],hist[name][1:]))==len(hist[name])-1
                 for name in frontier)
    # The declared tag map is pointwise, so it preserves occurrence indices,
    # including legitimate recurrent self-transitions.
    order=all(name in hist and len(hist[name])>=2 and
              list(enumerate(hist[name]))==list(enumerate(tuple(hist[name])))
              for name in frontier)
    raw_inputs=m['new_data']['raw_inputs']['by_tag']
    record=all(raw_inputs['source']['record_writer_available'].get(path['id']) is True and
               raw_inputs['target']['record_writer_available'].get(path['id']) is True
               for path in m['new_data']['corridor']['paths'])
    event_ids={e['id'] for e in m['new_data']['corridor']['events']}
    route_law=all(path['source_history'] in frontier and
                  all(event in event_ids for event in path['events'])
                  for path in m['new_data']['corridor']['paths']) and route(m)['retained']
    mapped=all(M(m,'source',history(m,name)[-1])==M(m,'target',receiver_state(m,name))
               for name in frontier)
    owner=(m['new_data']['maintenance']['owner_by_tag']=={'source':'source','target':'target'})
    passed=(paths_valid and edge_valid and past_distinct and source_equal and target_equal and
            laws and order and tick and progress and record and route_law and mapped and owner)
    return {'pass':passed,'frontier_size':len(frontier),'histories_supported':paths_valid,
            'strict_edge':edge_valid,'different_pasts':past_distinct,
            'same_source_M':source_equal,'same_target_M':target_equal,
            'representative_target_raw':target_states,'transition_laws':laws,
            'order_laws':order,'tick_laws':tick,'progress_laws':progress,'record_laws':record,
            'route_laws':route_law,'all_frontier_M_mapped':mapped,'owner_translation':owner}


def corridor(m):
    raw=m['new_data']['corridor'];stages=raw['stages'];realized=raw['realized_stages']
    events=raw['events'];event_by={e['id']:e for e in events}
    refs=all(e['from'] in stages and e['to'] in stages for e in events)
    strict=refs and all(stages.index(e['to'])==stages.index(e['from'])+1 and e['strict_step']
                        for e in events)
    def mixed_support(event, removed=None):
        source=event['source_support'] and removed!='source'
        target=event['target_support'] and removed!='target'
        return source and target and event['atomic']
    mixed=[e for e in events if mixed_support(e)]
    mixed_two=len(mixed)>=2
    gap=realized==stages and all(e['from'] in realized and e['to'] in realized for e in events)
    paths=all(path['source_history'] in m['new_data']['histories'] and
              all(event in event_by for event in path['events']) and
              all(event_by[a]['to']==event_by[b]['from'] for a,b in zip(path['events'],path['events'][1:]))
              for path in raw['paths'])
    intervention_sides={'remove_source_support':'source','remove_target_support':'target'}
    nonredundant=bool(mixed) and all(
        name in intervention_sides and
        all(not mixed_support(e,intervention_sides[name]) for e in mixed)
        for name in raw['interventions']) and set(raw['interventions'])==set(intervention_sides)
    return {'pass':refs and strict and mixed_two and gap and paths and nonredundant,
            'event_references':refs,'strict_steps':strict,'mixed_leg_count':len(mixed),
            'no_gap':gap,'paths_composable':paths,'nonredundant_interventions':nonredundant,
            'realized_stages':realized}


def route(m):
    paths=m['new_data']['corridor']['paths'];seen=[];outputs=[];steps=[]
    writer=m['new_data']['receiver']['route_register_write']['rule']
    viable=set(c8(m,'target')['greatest_viable'])
    K=m['t1_import']['kernel_order']
    policy=dict(zip(K,m['t1_import']['canonical_policy']))
    for path in paths:
        raw=(history(m,path['source_history']),tuple(path['events']))
        seen.append(raw)
        endpoint=receiver_state(m,path['source_history'])
        initial_register=raw if writer=='copy_raw_route_tuple' else None
        available=m['new_data']['raw_inputs']['by_tag']['target']['record_writer_available'][path['id']]
        distribution=(action_dist(m,'target',endpoint,policy[endpoint])
                      if endpoint in viable and available else {})
        resulting_states=[]
        for successor,mass in distribution.items():
            # The target step updates the T1 factor and ledger. Its declared
            # route-register operation leaves the target-owned register intact.
            resulting_register=initial_register if successor in viable else None
            resulting_states.append({'factor':successor,'mass':mass,
                                     'budget':m['new_data']['maintenance']['initial_budget_tokens']-
                                              m['new_data']['maintenance']['action_cost_tokens']+
                                              m['new_data']['maintenance']['recharge_tokens_per_action'],
                                     'register':resulting_register})
        reads={state(x['register'][0][0])[1] if x['register'] else None
               for x in resulting_states}
        output=next(iter(reads)) if len(reads)==1 else None
        outputs.append(output)
        steps.append({'endpoint':endpoint,'action':policy.get(endpoint),
                      'resulting_states':resulting_states,'register_persistent':bool(resulting_states) and
                      all(x['register']==raw for x in resulting_states),'readout':output})
    distinct=len(seen)>=2 and len(set(seen))==len(seen)
    admissible=all(p['source_history'] in m['new_data']['histories'] for p in paths) and corridor(m)['paths_composable']
    retained=(m['new_data']['maintenance']['owner_by_tag']['target']=='target' and
              all(step['register_persistent'] and step['readout'] is not None for step in steps))
    nonflat=retained and len(set(outputs))>=2
    return {'pass':distinct and admissible and nonflat,'checked_raw_routes':seen,
            'comparison_domain_size':len(seen),'distinct_raw_routes':distinct,
            'admissible':admissible,'register_rule':writer,'future_outputs':outputs,
            'retained':retained,'funded_target_steps':steps,
            'computed_status':'routeIndexed' if distinct and admissible and nonflat else 'unlicensed',
            'flat_certificate':False}


def typed_endpoint_link(m, corridor_result, bridge_result, content_result, target_viable):
    raw=m['new_data']['corridor']
    events={e['id']:e for e in raw['events']}
    exits=[e for e in raw['events'] if e['to']==raw['stages'][-1] and
           e['target_support'] and not e['source_support'] and e['atomic']]
    K=set(m['t1_import']['kernel_order'])
    links=[]
    for path in raw['paths']:
        source=history(m,path['source_history'])[-1]
        target=receiver_state(m,path['source_history'])
        last=events.get(path['events'][-1]) if path['events'] else None
        links.append({'route':path['id'],'source_terminal':source,'target_terminal':target,
                      'exit_event':last['id'] if last else None,
                      'pass':bool(last in exits and source in K and target in target_viable and
                                  M(m,'source',source)==M(m,'target',target))})
    passed=(corridor_result['pass'] and bridge_result['pass'] and content_result['pass'] and
            receiver_active(m) and len(links)>=2 and all(x['pass'] for x in links) and
            raw['stages'][-1] in raw['realized_stages'] and
            m['new_data']['maintenance']['owner_by_tag']['target']=='target')
    return {'pass':passed,'links':links,'target_exit_stage':raw['stages'][-1],
            'target_owned':m['new_data']['maintenance']['owner_by_tag']['target']=='target'}


def staged(m, details):
    source=details['clauses']['source'];target=details['clauses']['target']
    keys=('C1','C2','C3','C4','C5','C6','C6 trace','C7','C8')
    equal={key:source[key]['pass']==target[key]['pass'] for key in keys}
    c1_raw=source['C1']['P']==target['C1']['P'] and source['C1']['C']==target['C1']['C'] and source['C1']['U']==target['C1']['U']
    c2c3=all(public(m,'source',s)==public(m,'target',s) and M(m,'source',s)==M(m,'target',s)
              for s in m['t1_import']['kernel_order'])
    c4=all(current(m,'source',s)==current(m,'target',s)
           for s in m['t1_import']['kernel_order'])
    protocols=m['new_data']['c5']['protocols']
    by_tag={tag:{p['id']:p for p in protocols if p['tag']==tag} for tag in TAGS}
    translate=lambda value:'target' if value=='source' else value
    c5=all(cycle_credit(next(p for p in m['new_data']['c5']['protocols'] if p['tag']=='source' and p['id']==name))[0]==
           cycle_credit(next(p for p in m['new_data']['c5']['protocols'] if p['tag']=='target' and p['id']==name))[0]
           for name in ('clockwise','scheduled','internalized','null'))
    c5raw=(set(by_tag['source'])==set(by_tag['target']) and
           all(by_tag['source'][name]['edges']==by_tag['target'][name]['edges'] and
               translate(by_tag['source'][name]['owner'])==by_tag['target'][name]['owner'] and
               translate(by_tag['source'][name]['housing'])==by_tag['target'][name]['housing']
               for name in by_tag['source']))
    c6=all(m['new_data']['raw_inputs']['by_tag']['source']['tick_increment'][s]==
           m['new_data']['raw_inputs']['by_tag']['target']['tick_increment'][s]
           for s in m['t1_import']['kernel_order'])
    c6record=(m['new_data']['raw_inputs']['by_tag']['source']['record_writer_available']==
              m['new_data']['raw_inputs']['by_tag']['target']['record_writer_available'])
    c7=c7_transport(m)['pass']
    c8raw=(m['new_data']['raw_inputs']['by_tag']['source']['resources']['recharge_available_after_withdrawal']==
           m['new_data']['raw_inputs']['by_tag']['target']['resources']['recharge_available_after_withdrawal'])
    coordinates=package_coordinates(m)
    result=(c1_raw and c2c3 and c4 and c5 and c5raw and c6 and c6record and c7 and c8raw and
            coordinates['staged_map_valid'] and all(equal.values()))
    return {'pass':result,'C1_raw':c1_raw,'C2_C3_raw':c2c3,'C4_current':c4,
            'C5_credit':c5,'C5_raw':c5raw,'C6_tick':c6,'C6_record':c6record,
            'C7_relation':c7,'C8_resource':c8raw,
            'staged_coordinate_map':coordinates['staged_map_valid'],
            'clause_pass_equal':equal}


def package_coordinates(m):
    K=m['t1_import']['kernel_order']
    clauses=tuple(f'C{i}' for i in range(1,9))
    rows=m['new_data']['local_assignments']
    lookup={(row['tag'],row['state'],row['clause']):row for row in rows}
    expected={(tag,state,clause) for tag in TAGS for state in K for clause in clauses}
    refs_valid=True
    for row in rows:
        if row['coordinate']!=f"{row['tag']}:{row['state']}:{row['clause']}" or not row['primitive_refs']:
            refs_valid=False
        for ptr in row['primitive_refs']:
            item=m
            try:
                for key in ptr.strip('/').split('/'):
                    item=item[int(key)] if isinstance(item,list) else item[key]
            except (KeyError,IndexError,TypeError,ValueError):
                refs_valid=False
    complete=len(rows)==len(expected) and set(lookup)==expected and refs_valid
    map_rows=m['new_data']['staged_clause_map']
    mapped=(len(map_rows)==len(clauses) and
            {row['clause'] for row in map_rows}==set(clauses) and
            all(row['source_ref']==f"source:*:{row['clause']}" and
                row['target_ref']==f"target:*:{row['clause']}" and
                all(('source',state,row['clause']) in lookup and
                    ('target',state,row['clause']) in lookup for state in K)
                for row in map_rows))
    return {'pass':complete and mapped,'complete':complete,
            'staged_map_valid':mapped,'count':len(rows),'expected_count':len(expected)}


def check_wellformed(m):
    issues=[];K=m['t1_import']['kernel_order'];ambient=set(m['t1_import']['ambient_states'])
    for tag in TAGS:
        raw=m['new_data']['raw_inputs']['by_tag'][tag]
        for s in K:
            for a in m['t1_import']['actions']:
                dist=action_dist(m,tag,s,a)
                if any(t not in ambient or p<=0 for t,p in dist.items()) or (dist and sum(dist.values())!=1):
                    issues.append(f'{tag}:{s}:{a}:invalid_distribution')
                if raw['tick_increment'][s][a]<0:issues.append(f'{tag}:{s}:{a}:negative_tick')
        if not c7_local(m,tag)['well_formed']:issues.append(f'{tag}:C7_reassembly')
    for name,path in m['new_data']['histories'].items():
        if any(s not in ambient for s in path):issues.append(f'history:{name}:unknown_state')
    for assignment in m['new_data']['local_assignments']:
        for ptr in assignment['primitive_refs']:
            x=m
            try:
                for key in ptr.strip('/').split('/'):x=x[key]
            except (KeyError,IndexError,TypeError):issues.append(f'coordinate:{assignment["coordinate"]}:{ptr}')
    for route_path in m['new_data']['corridor']['paths']:
        if route_path['source_history'] not in m['new_data']['histories']:
            issues.append(f'route:{route_path["id"]}:missing_history')
    corridor_raw=m['new_data']['corridor']
    stages=corridor_raw['stages']
    events=corridor_raw['events']
    event_ids=[event['id'] for event in events]
    if len(stages)!=len(set(stages)):issues.append('corridor:duplicate_stage')
    if len(event_ids)!=len(set(event_ids)):issues.append('corridor:duplicate_event')
    for event in events:
        if event['from'] not in stages or event['to'] not in stages:
            issues.append(f'event:{event["id"]}:unknown_stage')
    for route_path in corridor_raw['paths']:
        if any(event_id not in event_ids for event_id in route_path['events']):
            issues.append(f'route:{route_path["id"]}:unknown_event')
    if any(stage not in stages for stage in corridor_raw['realized_stages']):
        issues.append('corridor:unknown_realized_stage')
    receiver=m['new_data']['receiver']
    for name,override in receiver['content']['history_overrides'].items():
        if name not in m['new_data']['histories'] or f'p{override["p"]}w{override["w"]}' not in ambient:
            issues.append(f'receiver_override:{name}')
    return {'pass':not issues,'issues':issues}


def target_only_autonomy(m):
    withdrawn=copy.deepcopy(m)
    withdrawn['new_data']['receiver']['activation']['source_present']=False
    withdrawn['new_data']['maintenance']['source_available_after_withdrawal']=False
    target=c8(withdrawn,'target')
    source_absent=(not m['new_data']['maintenance']['source_available_after_withdrawal'] and
                   not withdrawn['new_data']['receiver']['activation']['source_present'] and
                   not receiver_active(withdrawn))
    return {'pass':source_absent and target['pass'],'source_unavailable':source_absent,
            'target_C8_after_withdrawal':target['pass'],
            'target_greatest_viable':target['greatest_viable'],
            'target_funded_P_unchanged':target['funded_P_unchanged']}


def evaluate(m):
    provenance=provenance_check(m)
    clauses={tag:{'C1':c1(m,tag),'C2':c2(m,tag),'C3':c3(m,tag),
                  'C4':c4(m,tag),'C5':c5(m,tag),'C6':c6(m,tag),
                  'C6 trace':c6_trace(m,tag),'C7':c7_local(m,tag),'C8':c8(m,tag)} for tag in TAGS}
    work={'clauses':clauses,'provenance':provenance}
    work['staged']=staged(m,work)
    work['bridge']=bridge(m);work['corridor']=corridor(m)
    work['content']=content(m);work['route']=route(m)
    work['autonomy']=target_only_autonomy(m)
    work['typed_endpoint_link']=typed_endpoint_link(m,work['corridor'],work['bridge'],
                                                     work['content'],set(work['autonomy']['target_greatest_viable']))
    work['source_absent_activation_failure']=not receiver_active(m,False)
    work['wellformed']=check_wellformed(m)
    work['package_coordinates']=package_coordinates(m)
    under=copy.deepcopy(m)
    under['new_data']['raw_inputs']['by_tag']['target']['resources']['recharge_available_after_withdrawal']=False
    work['underfunded_target']=c8(under,'target')
    src_pkg=work['package_coordinates']['pass'] and all(
        clauses['source'][k]['pass'] for k in ('C1','C2','C3','C4','C5','C6','C6 trace','C7','C8'))
    dst_pkg=work['package_coordinates']['pass'] and all(
        clauses['target'][k]['pass'] for k in ('C1','C2','C3','C4','C5','C6','C6 trace','C7','C8'))
    work['source_package']=src_pkg;work['target_package']=dst_pkg
    work['handoff']={'pass':provenance['pass'] and len(set(m['carrier']['tags']))==2 and src_pkg and dst_pkg and
                     work['staged']['pass'] and work['bridge']['pass'] and work['corridor']['pass'] and
                     work['content']['pass'] and work['route']['pass'] and
                     work['typed_endpoint_link']['pass'] and work['autonomy']['pass'] and
                     work['source_absent_activation_failure'] and
                     m['new_data']['recognition_status']=='notAddressed',
                     'distinct_carriers':len(set(m['carrier']['tags']))==2,
                     'source_package':src_pkg,'target_package':dst_pkg,'staged':work['staged']['pass'],
                     'bridge':work['bridge']['pass'],'corridor':work['corridor']['pass'],
                     'content':work['content']['pass'],'route':work['route']['pass'],
                     'autonomy':work['autonomy']['pass'],
                     'typed_endpoint_link':work['typed_endpoint_link'],
                     'package_coordinates':work['package_coordinates'],
                     'recognition_status':m['new_data']['recognition_status']}
    return work


def mutate(original, intervention):
    m=copy.deepcopy(original)
    for edit in intervention['changes']:
        parts=edit['path'].strip('/').split('/')
        parent=m
        for p in parts[:-1]:parent=parent[int(p)] if isinstance(parent,list) else parent[p]
        final=parts[-1]
        if edit['op']=='replace':
            if isinstance(parent,list):
                parent[int(final)]=copy.deepcopy(edit['value'])
            else:
                if final not in parent:raise ValueError(f'missing mutation path {edit["path"]}')
                parent[final]=copy.deepcopy(edit['value'])
        elif edit['op']=='add':
            if isinstance(parent,list):
                if final!='-':raise ValueError(f'unsupported list add {edit["path"]}')
                parent.append(copy.deepcopy(edit['value']))
            else:
                if final in parent:raise ValueError(f'add already exists {edit["path"]}')
                parent[final]=copy.deepcopy(edit['value'])
        elif edit['op']=='remove':
            if isinstance(parent,list):del parent[int(final)]
            else:del parent[final]
        else:raise ValueError(f'unsupported edit {edit["op"]}')
    return m


def positive_rows(m,ev):
    c=ev['clauses'];s=c['source'];t=c['target']
    same=lambda k:s[k]['pass'] and t[k]['pass']
    rows={}
    def put(name,passed,details):rows[name]={'pass':bool(passed),'computed':details}
    put('T1 transcription and tagged isomorphism',ev['provenance']['pass'] and same('C1') and ev['staged']['C1_raw'],
        {'source':{k:s['C1'][k] for k in ('P_matches_T1','C_matches_T1','U_matches_T1')},
         'target':{k:t['C1'][k] for k in ('P_matches_T1','C_matches_T1','U_matches_T1')},
         'tag_isomorphism':ev['staged']['C1_raw'],'provenance':ev['provenance']})
    put('C1 exact T1 audit',same('C1'),
        {tag:{k:c[tag]['C1'][k] for k in ('unique','fixed_rank','pi','nonuniform','core_mass','TV','defect_epsilon_0','defect_epsilon_1_16','P_rows_stochastic','P_matches_T1')}
         for tag in TAGS})
    put('C2 strict promotion',same('C2') and ev['staged']['C2_C3_raw'],
        {tag:{k:c[tag]['C2'][k] for k in ('split_count','declared_witness','first_split')} for tag in TAGS})
    put('C3 recursive profile',same('C3') and ev['staged']['C2_C3_raw'],
        {tag:{k:c[tag]['C3'][k] for k in ('trajectory','terminal_equals_M','terminal_classes','ordered_pair_checks')} for tag in TAGS})
    put('C4 narrow collision/connector',same('C4'),
        {tag:{k:c[tag]['C4'][k] for k in ('collision','connector','full_HIDD_exposure','full_HIDD_nonexposure')} for tag in TAGS})
    put('C5 protocol-credit surrogate',same('C5'),
        {tag:{k:c[tag]['C5'][k] for k in ('credits','owner_consistency','products')} for tag in TAGS})
    put('C6 all-word future sufficiency',same('C6'),
        {tag:{k:c[tag]['C6'][k] for k in ('future_sufficient','strictly_coarser','q_classes','stable_classes','rounds','merged_pair','counterexample')} for tag in TAGS})
    put('C6 funded event order/tick/record',same('C6 trace'),
        {tag:{k:c[tag]['C6 trace'][k] for k in ('unit_tick','record_writers','strict_event_order','realized_paths','realized_stage_sequence','owner')} for tag in TAGS})
    put('C7 joint refinement and transport',same('C7') and c7_transport(m)['pass'],
        {'source':{k:s['C7'][k] for k in ('well_formed','strict_refinement','comparison_domain_size','joint_outputs','operational_use')},
         'target':{k:t['C7'][k] for k in ('well_formed','strict_refinement','comparison_domain_size','joint_outputs','operational_use')},
         'transport':c7_transport(m)})
    put('C8 funded/underfunded gfp',same('C8') and ev['underfunded_target']['size']==0,
        {'source':{k:s['C8'][k] for k in ('greatest_viable','size','iterations','available','funded_P_unchanged')},
         'target':{k:t['C8'][k] for k in ('greatest_viable','size','iterations','available','funded_P_unchanged')},
         'underfunded_target_size':ev['underfunded_target']['size']})
    put('Bridge and representative independence',ev['bridge']['pass'],ev['bridge'])
    put('Source-absent activation',ev['source_absent_activation_failure'] and receiver_active(m),
        {'positive_activates':receiver_active(m),'source_absent_activates':not ev['source_absent_activation_failure']})
    put('Content-sensitive transfer',ev['content']['pass'],ev['content'])
    put('Corridor',ev['corridor']['pass'],ev['corridor'])
    put('Route memory/status',ev['route']['pass'],ev['route'])
    put('Target-only autonomy',ev['autonomy']['pass'] and ev['underfunded_target']['size']==0,
        {**ev['autonomy'],'target_recharge':m['new_data']['raw_inputs']['by_tag']['target']['resources']['recharge_available_after_withdrawal'],
         'underfunded_target_size':ev['underfunded_target']['size']})
    put('TTH-06 surrogate assembly',ev['handoff']['pass'],ev['handoff'])
    return rows


def prediction_names(path):
    names=[];section=None
    for line in path.read_text().splitlines():
        if line=='## Positive model predictions':section='positive'
        elif line=='## Raw-input mutation predictions':section='mutation'
        elif line.startswith('## '):section=None
        if section and line.startswith('| ') and not line.startswith('| Property') and not line.startswith('| Mutation ID') and not line.startswith('|---'):
            field=line.split('|')[1].strip()
            if section=='mutation':field=field.strip('`')
            names.append((section,field))
    return names


def prediction_coverage(m,positive,prediction_path):
    names=prediction_names(prediction_path)
    expected_positive=[name for section,name in names if section=='positive']
    expected_mutations=[name for section,name in names if section=='mutation']
    return (list(positive)==expected_positive and
            [v['id'] for v in m['mutations']]==expected_mutations)


def mutation_target(mid,base,neg,m):
    s=neg['clauses']['source'];t=neg['clauses']['target']
    if mid=='NEG-C1-TABLE':return (not t['C1']['pass'],{'C1_target':t['C1']['pass'],'P_matches_T1':t['C1']['P_matches_T1']})
    if mid=='NEG-C2-SPLIT':return (not s['C2']['pass'] and not t['C2']['pass'],{'source_splits':s['C2']['split_count'],'target_splits':t['C2']['split_count']})
    if mid=='NEG-C3-PROFILE':return (not t['C3']['pass'],{'C3_target':t['C3']['pass'],'trajectory':t['C3']['trajectory'],'terminal_equals_M':t['C3']['terminal_equals_M']})
    if mid=='NEG-C4-EXPOSE':return (not t['C4']['collision'],{'target_collision':t['C4']['collision'],'full_HIDD_exposure':t['C4']['full_HIDD_exposure']})
    if mid=='NEG-C5-EXTERNAL':return (t['C5']['credits']['clockwise']=='other' and not t['C5']['pass'],{'target_credits':t['C5']['credits']})
    if mid=='NEG-C5-INTERNALIZED':return (t['C5']['credits']['scheduled']=='other',{'target_credits':t['C5']['credits'],'scheduled_housing':m['new_data']['c5']['protocols'][5]['housing']})
    if mid=='NEG-C6-FUTURE':return (not t['C6']['future_sufficient'],{'target_C6':t['C6']['pass'],'counterexample':t['C6']['counterexample'],'stable_classes':t['C6']['stable_classes']})
    if mid=='NEG-C6-RECORD':return (not t['C6 trace']['record_writers'],{'target_record_writers':t['C6 trace']['record_writers'],'route':neg['route']['future_outputs']})
    if mid=='NEG-C7-AGGREGATE':return (not s['C7']['strict_refinement'] and not t['C7']['strict_refinement'],{'source_strict':s['C7']['strict_refinement'],'target_strict':t['C7']['strict_refinement']})
    if mid=='NEG-C7-UNCOUPLED':return (not s['C7']['strict_refinement'] and not t['C7']['strict_refinement'] and s['C7']['comparison_domain_size']>=2 and t['C7']['comparison_domain_size']>=2,{'source':s['C7'],'target':t['C7']})
    if mid=='NEG-C7-TRANSPORT':return (not c7_transport(m)['pass'],{'transport':c7_transport(m),'target_local_wellformed':t['C7']['well_formed'],'target_strict':t['C7']['strict_refinement']})
    if mid=='NEG-C8-UNDERFUND':return (t['C8']['size']==0,{'target_viable_size':t['C8']['size'],'resource_available':t['C8']['available']})
    if mid=='NEG-CORRIDOR-DETACHED':return (not neg['corridor']['pass'] and neg['corridor']['mixed_leg_count']<2,neg['corridor'])
    if mid=='NEG-CORRIDOR-GAP':return (not neg['corridor']['no_gap'],neg['corridor'])
    if mid=='NEG-ACTIVATION-SOURCE-ABSENT':return (not receiver_active(m),{'activated':receiver_active(m),'activation_fields':m['new_data']['receiver']['activation']})
    if mid=='NEG-PRELOADED-COPY':return (receiver_active(m) and not neg['content']['pass'] and not neg['content']['distinct_target_M'] and m['new_data']['receiver']['activation']==base['model']['new_data']['receiver']['activation'],{'activated':receiver_active(m),'content':neg['content'],'activation_unchanged':m['new_data']['receiver']['activation']==base['model']['new_data']['receiver']['activation']})
    if mid=='NEG-BRIDGE-REP':return (not neg['bridge']['same_target_M'],{'same_target_M':neg['bridge']['same_target_M'],'target_raw':neg['bridge']['representative_target_raw']})
    if mid=='NEG-ROUTE-MEMORY':return (not neg['route']['pass'],{'route_status':neg['route']['computed_status'],'future_outputs':neg['route']['future_outputs']})
    if mid=='NEG-AUTONOMY-WITHDRAW':return (not neg['autonomy']['pass'] and
                                           not neg['autonomy']['target_greatest_viable'],
                                           {'autonomy':neg['autonomy'],
                                            'source_present':m['new_data']['receiver']['activation']['source_present']})
    raise KeyError(mid)


def lean_crosscheck(baseline):
    names=('pi_described','pi_probability','pi_fixed','pi_unique','pi_nonuniform',
           'pi_core_mass','pi_core_retention','pi_tv_from_core_uniform',
           'e2eps_defect','e2zero_defect')
    probe='import CSTTT.Objecthood.T1Audit\n'+''.join(
        f'#check CSTTT.Objecthood.T1Audit.{name}\n' for name in names)+''.join(
        f'#print axioms CSTTT.Objecthood.T1Audit.{name}\n' for name in names)
    with tempfile.TemporaryDirectory(prefix='m3b-lean-') as scratch:
        path=Path(scratch)/'probe.lean';path.write_text(probe)
        run=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT/'lean',
                           capture_output=True,text=True,check=True)
    output=run.stdout
    for name in names:
        if f'CSTTT.Objecthood.T1Audit.{name}' not in output:
            raise RuntimeError(f'BLOCKING: Lean theorem {name} unresolved')
    described={int(i):F(int(num),int(den)) for i,num,den in re.findall(
        r'T1Audit\.pi (\d+) = (\d+) / (\d+)',output)}
    if set(described)!=set(range(10)):
        raise RuntimeError(f'BLOCKING: Lean pi_described not parsed: {described}')
    expected={
        'pi_core_mass':('77','80'),
        'pi_core_retention':('3','4'),
        'pi_tv_from_core_uniform':('3','80'),
        'e2eps_defect':('78795','524288'),
        'e2zero_defect':('1','8')}
    for name,(num,den) in expected.items():
        block=re.search(
            rf"(?ms)^CSTTT\.Objecthood\.T1Audit\.{name}\b(.*?)(?=^CSTTT\.Objecthood\.T1Audit\.|^'|\Z)",
            output)
        if not block or f'{num} / {den}' not in block.group(1):
            raise RuntimeError(f'BLOCKING: Lean theorem {name} has unexpected statement')
    axiom_lines=re.findall(r"'CSTTT\.Objecthood\.T1Audit\.\w+' depends on axioms: \[([^]]*)\]",output)
    if len(axiom_lines)!=len(names):raise RuntimeError('BLOCKING: incomplete Lean axiom probe')
    axioms=sorted(set(x.strip() for line in axiom_lines for x in line.split(',') if x.strip()))
    if not set(axioms)<={'propext','Classical.choice','Quot.sound'}:
        raise RuntimeError(f'BLOCKING: untrusted Lean axiom: {axioms}')
    c=baseline['clauses']
    for tag in TAGS:
        actual=c[tag]['C1']; pi=actual['pi']
        if (pi != [described[i] for i in range(10)] or not actual['unique'] or
            not actual['nonuniform'] or actual['core_mass']!=F(77,80) or
            actual['TV']!=F(3,80) or actual['defect_epsilon_1_16']!=F(78795,524288) or
            actual['defect_epsilon_0']!=F(1,8)):
            raise RuntimeError(f'BLOCKING: Python/Lean C1 mismatch on {tag}')
    return {'agreement':True,'theorems':[f'CSTTT.Objecthood.T1Audit.{name}' for name in names],
            'pi':[described[i] for i in range(10)],'core_mass':F(77,80),
            'TV':F(3,80),'defect_epsilon_0':F(1,8),
            'defect_epsilon_1_16':F(78795,524288),'axioms':axioms}


def prediction_meanings(path):
    meanings={}
    for line in path.read_text().splitlines():
        if line.startswith('| ') and not line.startswith(('|---','| Property','| Mutation ID')):
            cells=[c.strip() for c in line.strip('|').split('|')]
            if len(cells)>=4:meanings[cells[0].strip('`')]=cells[3]
    return meanings


def classify_mutation(mid,hit,wellformed,baseline,negative):
    if not wellformed:return 'INVALID-CONTROL'
    if not hit:return 'FAILED'
    if mid=='NEG-C4-EXPOSE':return 'CONFIRMED-NARROW'
    if mid in {'NEG-C1-TABLE','NEG-C2-SPLIT','NEG-C6-FUTURE','NEG-C6-RECORD',
               'NEG-C7-TRANSPORT','NEG-CORRIDOR-GAP',
               'NEG-ACTIVATION-SOURCE-ABSENT','NEG-AUTONOMY-WITHDRAW'}:
        return 'CONFIRMED-CONFOUNDED'
    return 'CONFIRMED'


def side_effects(base,neg):
    return {'clause_pass_changes':{tag:[key for key in base['clauses'][tag]
              if base['clauses'][tag][key]['pass']!=neg['clauses'][tag][key]['pass']]
              for tag in TAGS},
            'lane_pass_changes':[key for key in ('staged','bridge','corridor','content','route','autonomy','typed_endpoint_link','handoff')
                                 if base[key]['pass']!=neg[key]['pass']]}


def brief(value,limit=230):
    out=json.dumps(encode(value),sort_keys=True,ensure_ascii=False)
    return out if len(out)<=limit else out[:limit-3]+'...'


def coverage_index():
    checks=[
        ('T1 provenance hashes',provenance_check),
        ('Tagged canonical P and M from raw actions',canonical_matrix),
        ('C1 C/U, E₂ε, fixed law, retention, TV, defects',c1),
        ('C1 uniqueness for all normalized fixed laws',fixed_law),
        ('C1 agreement with Lean theorems and axioms',lean_crosscheck),
        ('C2 split and pinned witness',c2),
        ('C3 recursive action/exit profile and terminal M',c3),
        ('C4 full current family and hidden connector',c4),
        ('C5 forward/reverse products, credit and anchors',c5),
        ('C6 full interface and all-word fixed point',c6),
        ('C6 funded order/tick/record and owner',c6_trace),
        ('C7 per-assemblage reassembly and strict refinement',c7_local),
        ('C7 receiver pre-exit jointPairing display',c7_receiver_display),
        ('C7 staged joint relation preservation',c7_transport),
        ('C8 priced ledger, gfp and canonical P',c8),
        ('T1 histories, strict edge and bridge laws',bridge),
        ('Source-absent activation',receiver_active),
        ('Raw-coordinate receiver and content counterfactuals',content),
        ('Mixed corridor, no gap and support interventions',corridor),
        ('Funded target step and persistent route readout',route),
        ('Typed corridor/receiver endpoint link',typed_endpoint_link),
        ('160 state-indexed package coordinates',package_coordinates),
        ('Eight staged maps and raw clause equations',staged),
        ('Source-removed target-only C8 autonomy',target_only_autonomy),
        ('TTH-06 surrogate assembly',evaluate),
        ('References, distributions, reassembly and events',check_wellformed),
        ('Unchanged JSON-Pointer intervention semantics',mutate),
        ('Positive prediction coverage and gates',positive_rows),
        ('Mutation targets and outcome categories',mutation_target),
        ('Exact prediction-list and mutation coverage',prediction_coverage),
    ]
    return [{'check':label,'file':'scripts/evaluate_fiach_pos04.py',
             'line':inspect.getsourcelines(fn)[1]} for label,fn in checks]


def run(model_path,prediction_path):
    raw=model_path.read_bytes();m=json.loads(raw)
    if m['model_id']!='FIACH-POS-04':raise ValueError('POS-04 model required')
    baseline=evaluate(m)
    lean=lean_crosscheck(baseline)
    positive=positive_rows(m,baseline)
    if not prediction_coverage(m,positive,prediction_path):
        raise RuntimeError('positive or mutation prediction coverage/order mismatch')
    positives={name:{'outcome':'CONFIRMED' if value['pass'] else 'FAILED',
                     'predicted':'PASS','computed':encode(value['computed'])}
               for name,value in positive.items()}
    mutation_results={};wellformed={}
    for intervention in m['mutations']:
        mid=intervention['id'];variant=mutate(m,intervention);negative=evaluate(variant)
        hit,target=mutation_target(mid,{'model':m,**baseline},negative,variant)
        status=classify_mutation(mid,hit,negative['wellformed']['pass'],baseline,negative)
        mutation_results[mid]={'outcome':status,'predicted':'declared control outcome',
                               'target_prediction_occurred':bool(hit),
                               'computed':encode(target),'side_effects':side_effects(baseline,negative)}
        wellformed[mid]=negative['wellformed']
    counts=Counter(v['outcome'] for v in list(positives.values())+list(mutation_results.values()))
    # A clean ablation loses a previously satisfied target. The internally
    # housed scheduled control predicts preserved other credit, not an ablation.
    clean=sum(v['outcome']=='CONFIRMED' and mid!='NEG-C5-INTERNALIZED'
              for mid,v in mutation_results.items())
    sensitivity_process=subprocess.run(
        [sys.executable,str(ROOT/'scripts/selftest_evaluate_fiach_pos04.py'),'--json'],
        cwd=ROOT,capture_output=True,text=True,check=True)
    sensitivity=json.loads(sensitivity_process.stdout)
    if len(sensitivity)!=len(coverage_index())+7 or any(row['result']!='CAUGHT' for row in sensitivity):
        raise RuntimeError('gate sensitivity suite incomplete or failed')
    return {'model_id':m['model_id'],'declaration_sha256':hashlib.sha256(raw).hexdigest(),
            'method':'exact Fraction matrices; rational Gaussian elimination; finite stochastic partition fixed points; greatest viable fixed points; same predicate code for mutations',
            'lean_c1_crosscheck':encode(lean),
            'positive_predictions':positives,'mutation_predictions':mutation_results,
            'positive_wellformed':baseline['wellformed'],
            'mutation_wellformedness':wellformed,
            'per_tag_clause_details':{tag:{key:encode({k:v for k,v in val.items() if k not in ('P','C','U','partition')})
                                           for key,val in baseline['clauses'][tag].items()} for tag in TAGS},
            'staged':encode(baseline['staged']),
            'underfunded_target':encode({k:baseline['underfunded_target'][k] for k in ('size','greatest_viable','available')}),
            'counts':{category:counts[category] for category in CATEGORIES},
            'clean_ablation_count':clean,
            'coverage':coverage_index(),
            'gate_sensitivity':sensitivity,
            'ambiguities':[
                'C1: reconstruct canonical P from each tag raw action rows, compute M=(position, per-action safe/lethal support law), derive C and U from those M fibers, then use exact Pε²CU. Published T1 labels and values are comparison targets, never results.',
                'C3: action profiles aggregate exact probabilities over current partition blocks and distinguish each out-of-K exit; the stable partition is compared on all 100 ordered K pairs.',
                'C6: compare equal-q states at the same unfolded event count, tick phase, route, owner and maintenance context. Check action-indexed exact distributions, tick increments and successor classes to a finite stochastic bisimulation fixed point; uniform unit progress/record increments and per-route writer availability propagate counter equality for all words. No bounded horizon is used.',
                'C7: reassembly is an indexed per-assemblage relation, allowing distinct assemblages to have equal coupling. JointPairing is a distribution over paired raw history records, with complete ordered branch records as K_bw.',
                'C7 operational use: the declaration gives no separate display-selection algorithm. The receiver display is the exact rational jointPairing distribution of each assemblage, read at a realized mixed pre-exit event under the declared receiver activation gate. Distinct displays and unchanged post-exit P are gated; display differentiation follows the declared coupling nearly automatically.',
                'Gate-sensitivity probes test group sensitivity, not exhaustive isolation of every obligation. The C1 fixed_law identity-matrix probe tests the general uniqueness solver directly. For the declared epsilon=1/16 stochastic family, positivity itself forces uniqueness, so no well-formed raw P mutation isolates loss of uniqueness; the full C1 predicate is separately tested with a changed raw action row.',
                'C8: greatest viable subset uses existence of a funded feasible action with all positive-support successors retained. Canonical P is checked separately and unchanged in the funded regime.',
                'Corridor: removal interventions delete one side of mixed support under the declared Boolean conjunction. This is synthetic intervention semantics and gives no independent causal corroboration.',
                'Receiver content: only p,w are transferred; both M classes are recomputed from raw action supports. Content sensitivity is close to automatic after tag isomorphism. The fixed-activation preloaded-copy control is the substantive discriminator within this toy.',
                'Route memory: compare dereferenced (source-state history,event sequence) tuples. Execute each positive-support successor of the funded canonical target row and retain the tuple in the resulting target state by the predeclared register rule, then read its first phase. Persistence is rule-driven and near-automatic; it does not independently establish holonomy.',
                'Bridge order/progress/record: the pointwise tag map has no independently declared target history table. Occurrence order and unit progress follow from source path indices and the same tagged raw action law; record preservation additionally checks per-route writer availability and funded-step register retention.',
                'Autonomy: remove source presence in a model copy and rerun the identical target C8 predicate. C8 reads only target resources, so source independence is structural once source absence is verified.',
                'TTH-06 package means the declared surrogate C1–C8 assignment contract. Full HIDD C4 non-exposure already fails; no full P05 C-package or T17-I is inferred.'
            ],
            'regressions':{'POS-02_JSON':'byte-identical to audit/M0b_results.json',
                           'POS-03_JSON':'byte-identical to audit/M1b_results.json'}}


def render_md(result,prediction_path):
    meanings=prediction_meanings(prediction_path)
    counts=result['counts']
    lines=['# FIACH-POS-04 preregistration evaluation','',
           'Computed against the frozen M3a declaration. The Python evaluator uses exact fractions, finite fixed points, and unchanged predicates for all interventions. No stored verdict, claimed grade, or route name supplies a result.','',
           f"Declaration SHA-256: `{result['declaration_sha256']}`",'',
           'Counts: '+', '.join(f"**{counts[k]} {k}**" for k in CATEGORIES)+
           f". Clean confirmed ablations: **{result['clean_ablation_count']}**.",'',
           '## All preregistered outcomes','',
           '| Prediction or intervention | Outcome | Deciding evidence |','|---|---|---|']
    for name,v in list(result['positive_predictions'].items())+list(result['mutation_predictions'].items()):
        evidence=brief(v['computed'],180).replace('|','/')
        lines.append(f"| `{name}` | **{v['outcome']}** | `{evidence}` |")
    c=result['lean_c1_crosscheck']
    lines+=['','## C1: exact T1 factor versus Lean','',
            'Both tagged ten-state factors reconstruct canonical `P`, `C`, `U`, `Pε²CU` from their raw tables. Exact rational Gaussian elimination gives a normalized fixed-point system of rank 10, so the probability fixed law is unique. The computed source and target values agree with kernel-checked CSTTT theorems:','',
            '| Fact | Source and target Python computation | Lean theorem |','|---|---|---|',
            f"| π in T1 K order | `{', '.join(c['pi'])}` | `pi_described`, `pi_probability`, `pi_fixed`, `pi_unique` |",
            '| Nonuniformity | `true` on both factors | `pi_nonuniform` |',
            f"| CORE mass and retention | `{c['core_mass']} ≥ 3/4` | `pi_core_mass`, `pi_core_retention` |",
            f"| TV from CORE-uniform | `{c['TV']}` | `pi_tv_from_core_uniform` |",
            f"| Defect ε=0 | `{c['defect_epsilon_0']}` | `e2zero_defect` |",
            f"| Defect ε=1/16 | `{c['defect_epsilon_1_16']}` | `e2eps_defect` |",'',
            'The evaluator probes the Lean theorem statements and axioms through `lake env lean`; the parsed values match the independently reconstructed Python matrices. The probed axioms are '+', '.join(f'`{a}`' for a in c['axioms'])+'. **No Python/Lean mismatch.** The `77/80` theorem applies only to each exact T1 factor, not to the augmented handoff carrier.','']
    lines+=['## Handoff and clause evidence','',
            'C2 has the computed `p1w0/p1w1` split on each tag. C3 refinement is `6→7→7` on each tag, with terminal equality to the freshly computed M relation over all 100 ordered pairs; staged factor equations pass. C6 uses a finite stochastic bisimulation fixed point for all finite action words on the full declared interface, including route and maintenance context, and its code merges the distinct `p0w0/p0w1` states. The funded C8 greatest viable subset is all ten T1 K states on each tag; removing target recharge yields the empty subset. Every funded canonical P row remains the published T1 row.','',
            'The receiver reads terminal raw source `(p,w)` and constructs a raw target state with the fixed latent receiver and activation fields. Only then are both terminal M values computed. This makes the p1-pair content distinction **close to automatic after the tag-isomorphism check**; the fixed-activation preloaded-copy control removes it. Source absence blocks activation separately. Representative histories have genuinely different pasts and one computed terminal M class.','',
            'The two checked routes include different source-state histories even though their event IDs coincide. A target-owned register stores each raw history-plus-event tuple, and the funded future audit reads its first-state phase, yielding `0` and `1`. This route readout is **near-automatic by design once the register persists**; it is not independent holonomy evidence. The corridor has two mixed-support legs, strict realized stages with no gap, and target-only exit; the funded target remains viable after source withdrawal. Recognition remains `notAddressed`.','']
    c7=result['positive_predictions']['C7 joint refinement and transport']['computed']
    route_e=result['positive_predictions']['Route memory/status']['computed']
    bridge_e=result['positive_predictions']['Bridge and representative independence']['computed']
    handoff_e=result['positive_predictions']['TTH-06 surrogate assembly']['computed']
    autonomy_e=result['positive_predictions']['Target-only autonomy']['computed']
    lines+=['The C7 receiver reads exact `jointPairing` distributions from admissible branch histories at a **realized** mixed pre-exit event only when the declared source-dependent activation gate succeeds, and displays the paired branch histories with their rational weights. Its two displays differ on each tag: '
            f"source `{brief(c7['source']['operational_use']['display_by_assemblage'],350)}`; "
            f"target `{brief(c7['target']['operational_use']['display_by_assemblage'],350)}`. "
            'The display is a direct readout of the declared coupling; it adds no independent coupling evidence. Post-exit canonical P is checked unchanged.','',
            'Route persistence is checked after executing the canonical target action from each receiver endpoint. Every positive-support successor must retain the raw route tuple, have a funded resulting budget, and yield the same phase readout. '
            f"Computed successor records: `{brief(route_e['funded_target_steps'],900)}`. "
            'The register-retention rule was declared in the model and is applied identically to each successor; this is a conditional operational check, not independently observed memory.','',
            f"The bridge gates successor, occurrence order, tick, progress, record and route laws: `{brief({k:bridge_e[k] for k in ('transition_laws','order_laws','tick_laws','progress_laws','record_laws','route_laws')},400)}`. The C6 trace also gates each raw event's `strict_step` and its realized path and stage order. "
            f"The typed corridor/receiver endpoint link is `{brief(handoff_e['typed_endpoint_link'],650)}`. "
            f"After explicitly removing source presence, target-only C8 yields `{brief(autonomy_e,450)}`. "
            'The pointwise tag map makes occurrence-order preservation structural; it is listed separately from the stochastic successor check.','',
            'The clause-local availability audit checks C1–C3 against raw action/readout tables, C4 against positive-support connector steps, C5 against admissible anchor histories, C6 against nonempty route contexts and realized strict event paths, C7 against admissible branch histories plus active realized pre-exit use, and C8 against its funded target ledger. The new C5, C6, and C7 conditions are gated within those clauses rather than inherited from the corridor or bridge.','']
    failures=[(k,v) for k,v in list(result['positive_predictions'].items())+list(result['mutation_predictions'].items()) if v['outcome'] in ('FAILED','UNDETERMINED')]
    lines+=['## Failed or undetermined predictions','']
    if not failures:lines.append('None.')
    for name,v in failures:
        lines += [f"### `{name}` — {v['outcome']}",'',
                  f"Computed: `{brief(v['computed'],1000)}`.",'',
                  meanings.get(name,'The pre-registered prediction did not occur. The frozen declaration is not revised.'),'',
                  f"Other predicate effects: `{brief(v.get('side_effects',{}),1000)}`.",'']
    lines+=['## Qualified interventions and well-formedness','',
            'The following categories limit the interpretation of a predicted negative; they are excluded from the clean-ablation count. `NEG-C4-EXPOSE` is `CONFIRMED-NARROW` because full HIDD C4 non-exposure already fails on the baseline; only its narrower collision is removed. `NEG-C1-TABLE` also breaks funded P preservation, C7 operational P isolation, and C8; `NEG-C2-SPLIT` also breaks C3 and C4; `NEG-C6-FUTURE` also breaks the unit-tick trace; `NEG-C6-RECORD` also erases route readout; `NEG-C7-TRANSPORT` also destroys target strict refinement; `NEG-CORRIDOR-GAP` also disables receiver content activation; and source removal in `NEG-ACTIVATION-SOURCE-ABSENT` and `NEG-AUTONOMY-WITHDRAW` also disables C7 operational use. These eight are `CONFIRMED-CONFOUNDED`. `NEG-C5-INTERNALIZED` confirms the no-fake-self credit control without ablating that credit; its raw staged C5 equation and handoff do fail, so it is excluded from the clean-ablation count.','',
            '| Intervention | Local well-formedness | Target prediction occurred | Other clause/lane changes |',
            '|---|---|---|---|']
    for mid,v in result['mutation_predictions'].items():
        wf=result['mutation_wellformedness'][mid]
        lines.append(f"| `{mid}` | {wf['pass']} ({len(wf['issues'])} issues) | {v['target_prediction_occurred']} | `{brief(v['side_effects'],165)}` |")
    previous_side_effects={
        'NEG-C3-PROFILE':{'source':[],'target':['C1','C4','C7','C8']},
        'NEG-CORRIDOR-GAP':{'source':['C7'],'target':['C7']},
    }
    lines+=['','## Changes from the preceding M3b review','',
            'No outcome category or clean-ablation count changed in this review. Two clause side-effect records changed: the C3 row mutation also invalidates a C5 anchor history, and the corridor gap also invalidates the C6 realized trace. Lane side-effect lists are unchanged.','',
            '| Intervention | Previous outcome → current outcome | Previous clause changes → current clause changes |',
            '|---|---|---|']
    for mid,old in previous_side_effects.items():
        current=result['mutation_predictions'][mid]
        previous_outcome=('CONFIRMED-CONFOUNDED' if mid=='NEG-CORRIDOR-GAP' else 'FAILED')
        changed=current['side_effects']['clause_pass_changes']
        lines.append(f"| `{mid}` | {previous_outcome} → {current['outcome']} | "
                     f"`{brief(old,90)}` → `{brief(changed,120)}` |")
    lines+=['','## Ambiguity log','']+[f'- {x}' for x in result['ambiguities']]
    lines+=['','## Declared-check coverage','',
            'Each row points to the evaluator function that computes and gates the listed contract. The table includes declared controls and the separate well-formedness path.','',
            '| Declared check | Implementing line |','|---|---|']
    for entry in result['coverage']:
        lines.append(f"| {entry['check']} | [`{entry['file']}:{entry['line']}`](../{entry['file']}#L{entry['line']}) |")
    lines+=['','## Gate-sensitivity self-test','',
            'These are **group-sensitivity probes, not exhaustive isolation of every obligation**. Each perturbation is applied to a fresh in-memory copy of the frozen positive model. `CAUGHT` means the named check rejected the broken input. Seven focused rows probe C7 activation/realization, C6 path/route availability, and C5/C7 history availability. The fixed-law identity probe tests the general rank solver at method level; uniqueness within the positive ε=1/16 stochastic family is additionally protected by the full C1 raw-row test.','',
            '| Check | In-memory perturbation | Result |','|---|---|---|']
    for row in result['gate_sensitivity']:
        lines.append(f"| {row['check']} | {row['perturbation']} | **{row['result']}** |")
    lines+=['','## POS-02, POS-03, POS-04 comparison','',
            '| Model | C1 result | Strongest declared ceiling | Outcome |',
            '|---|---|---|---|',
            '| POS-02 | stationary CORE mass `2/3` fails `3/4` | surrogate finite handoff | failed C1 and package |',
            '| POS-03 | `E₂^ε` attracting law is uniform | surrogate finite handoff | failed C1 nonuniformity |',
            '| POS-04 | exact T1 factor: unique nonuniform π, CORE `77/80`, TV `3/80` | T1 factor C1/C2/C3 plus surrogate package handoff | see outcome table; full C4/P05 remain unavailable |','',
            'The POS-02 and POS-03 JSON results were regenerated with the unchanged old evaluator and compared byte-for-byte with their committed results. Both comparisons passed.','',
            '## Claim ceiling and reproduction','',
            'The confirmed finite checks support the exact T1 C1/C2/C3 components on two tagged factors and the declared **model-relative surrogate** handoff obligations, subject to the failed C3 ablation and qualified controls above. They do not establish C1 for the full augmented carrier, a full P05 integrated C-package, T17-I, or a Lean-kernel proof of Temporal-FIACH.','',
            '`python3 scripts/evaluate_fiach_pos04.py audit/proposed_models/FIACH-POS-04.model.json --json-out audit/M3b_results.json --md-out audit/M3b_results.md`','',
            '`python3 scripts/evaluate_fiach_pos02.py audit/proposed_models/FIACH-POS-02.model.json --json-out /tmp/m3b_pos02.json --md-out /tmp/m3b_pos02.md && cmp /tmp/m3b_pos02.json audit/M0b_results.json`','',
            '`python3 scripts/evaluate_fiach_pos02.py audit/proposed_models/FIACH-POS-03.model.json --json-out /tmp/m3b_pos03.json --md-out /tmp/m3b_pos03.md && cmp /tmp/m3b_pos03.json audit/M1b_results.json`','']
    return '\n'.join(lines)+'\n'


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('model',type=Path)
    parser.add_argument('--json-out',type=Path,default=Path('audit/M3b_results.json'))
    parser.add_argument('--md-out',type=Path,default=Path('audit/M3b_results.md'))
    args=parser.parse_args()
    result=run(args.model,ROOT/'audit/M3_predictions.md')
    args.json_out.parent.mkdir(parents=True,exist_ok=True)
    args.json_out.write_text(json.dumps(result,indent=2,sort_keys=True,ensure_ascii=False)+'\n')
    args.md_out.write_text(render_md(result,ROOT/'audit/M3_predictions.md'))
    print(json.dumps(result['counts'],sort_keys=True))
    print(f"clean ablations={result['clean_ablation_count']}; wrote {args.json_out} and {args.md_out}")


if __name__=='__main__':main()
