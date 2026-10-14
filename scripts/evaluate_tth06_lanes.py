#!/usr/bin/env python3
"""G6b: exact raw assignment, atomic lineage, and F/O withdrawal evaluation.
No declared status is consumed by predicates. Predictions are compared afterwards.
The existing POS-04 library supplies exact matrix algebra only; this module owns
assignment decoding, scopes, maps, run definitions, and support-safe fixed points.
"""
import argparse
import ast
import copy
from collections import Counter
from fractions import Fraction as Q
import hashlib
import inspect
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import evaluate_fiach_pos04 as wheel

ROOT = Path(__file__).resolve().parents[1]
TAGS = ('source', 'target')
CLAUSES = tuple(f'C{i}' for i in range(1, 9))
FIELDS = ('predictive', 'order', 'tick', 'progress', 'writer', 'record',
          'residue', 'maintenance', 'owner', 'budget')
CATEGORIES = ('CONFIRMED', 'CONFIRMED-NARROW', 'CONFIRMED-CONFOUNDED', 'FAILED',
              'INVALID-CONTROL', 'UNDETERMINED')


def encode(x):
    if isinstance(x, Q): return f'{x.numerator}/{x.denominator}'
    if isinstance(x, dict): return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)): return [encode(v) for v in x]
    if isinstance(x, set): return sorted(encode(v) for v in x)
    return x


def freeze(x):
    if isinstance(x, dict): return tuple((k, freeze(v)) for k, v in sorted(x.items()))
    if isinstance(x, (tuple, list)): return tuple(map(freeze, x))
    return x


def checked(gates, **details):
    return {'pass': all(gates.values()), 'gates': gates, **details}


def scope(tag, c):
    common = [f'rows:{tag}', 'positions', 'hazards']
    return {
        'C1': common + ['policy', 'prototypes', 'publishedP', 'publishedC', 'publishedU', 'audit'],
        'C2': common + [f'lower:{tag}', 'publishedM'],
        'C3': common + [f'lower:{tag}', 'publishedM'],
        'C4': common + ['channels', 'policy', 'histories', 'publishedM'],
        'C5': [f'protocols:{tag}', f'rows:{tag}', 'policy', 'histories'],
        'C6': common + [f'ticks:{tag}', 'interface', f'resources:{tag}', 'maintenance',
                       'policy', 'publishedP', 'publishedM', 'histories', 'eventTable',
                       'realized', 'receiverInput', 'routeTable', 'writers'],
        'C7': [f'joint:{tag}', f'rows:{tag}', 'policy', 'histories', 'publishedP',
               'eventTable', 'realized', 'receiverInput'],
        'C8': [f'rows:{tag}', 'policy', f'resources:{tag}', 'maintenance'],
    }[c]


def load(path):
    declaration = json.loads(Path(path).read_text())
    base = json.loads((ROOT / declaration['base_model']['path']).read_text())
    return {'declaration': declaration, 'base': base, 'anchor_data': copy.deepcopy(base['t1_import']), 'assignment_edits': []}


def import_cells(base):
    t = base['t1_import']; n = base['new_data']; K = t['kernel_order']
    cells = {
        'positions': dict(zip(K, t['public_f'])),
        'hazards': {s: not wheel.safe(base, s) for s in t['ambient_states']},
        'policy': dict(zip(K, t['canonical_policy'])),
        # Data.c1ColumnRepresentatives is the first row of each imported C column.
        'prototypes': [next(K[i] for i in range(len(K)) if t['C'][i][j] == 1)
                       for j in range(len(t['C'][0]))],
        'publishedP': t['P'], 'publishedC': t['C'], 'publishedU': t['U'],
        'publishedM': dict(zip(K, t['M_class_labels'])),
        'audit': {k: t['C1'][k] for k in ('tau', 'epsilon', 'retention_threshold')},
        'channels': n['c4']['current_channels'], 'interface': n['c6']['future_interface'],
        'maintenance': {k: n['maintenance'][k] for k in
                        ('initial_budget_tokens', 'action_cost_tokens', 'recharge_tokens_per_action')},
        'histories': n['histories'], 'eventTable': n['corridor']['events'],
        'realized': n['corridor']['realized_stages'], 'receiverInput': n['receiver'],
        'routeTable': n['corridor']['paths'],
        'writers': {tag: n['raw_inputs']['by_tag'][tag]['record_writer_available'] for tag in TAGS},
    }
    for tag in TAGS:
        raw = n['raw_inputs']['by_tag'][tag]
        cells.update({f'rows:{tag}': raw['action_distributions'],
                      f'lower:{tag}': raw['public_channel_rule'],
                      f'ticks:{tag}': raw['tick_increment'],
                      f'protocols:{tag}': [p for p in n['c5']['protocols'] if p['tag'] == tag],
                      f'joint:{tag}': n['c7']['by_tag'][tag],
                      f'resources:{tag}': {'owner': n['maintenance']['owner_by_tag'][tag],
                                          'available': raw['resources']['recharge_available_after_withdrawal']}})
    return copy.deepcopy(cells)


def assignment(model):
    a = import_cells(model['base'])
    for edit in model['assignment_edits']:
        name = edit['cell']['constructor']
        if edit['cell'].get('tag'): name += ':' + edit['cell']['tag']
        if edit['op'] == 'remove_cell': a[name] = None
        elif edit['op'] == 'replace_cell': a[name] = copy.deepcopy(edit['value'])
        else: raise ValueError(f'unknown assignment edit {edit}')
    return a


def exchange(a):
    """PackageAssembly.swapCell/translatedValue; clause-independent raw map."""
    b = {}
    swap = {'source': 'target', 'target': 'source'}
    for k in a:
        source = k
        if ':' in k:
            family, tag = k.split(':'); source = family + ':' + swap[tag]
        v = copy.deepcopy(a[source])
        if v is not None and k.startswith('resources:'): v['owner'] = swap[v['owner']]
        if v is not None and k.startswith('protocols:'):
            for p in v:
                p['tag'] = swap[p['tag']]
                for field in ('owner', 'housing'): p[field] = swap.get(p[field], p[field])
        if v is not None and k == 'writers': v = {tag: v[swap[tag]] for tag in TAGS}
        b[k] = v
    return b


class Inputs:
    def __init__(self, model, cells):
        self.m = model; self.a = cells; self.base = model['base']
        self.K = self.base['t1_import']['kernel_order']
        self.ambient = self.base['t1_import']['ambient_states']
        self.actions = self.base['t1_import']['actions']
        self.anchors = model['anchor_data']

    def complete(self, keys): return all(self.a.get(k) is not None for k in keys)
    def row(self, tag, s, action):
        return {t: Q(p) for t, p in self.a[f'rows:{tag}'][s][action].items()}
    def pred(self, tag, s):
        if s not in self.K: return ('exit', s)
        return (self.a['positions'][s], tuple(tuple(self.a['hazards'][t]
                 for t in self.a[f'rows:{tag}'][s][a]) for a in self.actions))
    def lower(self, tag, s):
        return (self.a['positions'][s], s if self.a[f'lower:{tag}'] == 'state_label' else None)
    def P(self, tag):
        return [[self.row(tag, s, self.a['policy'][s]).get(t, Q(0)) for t in self.K] for s in self.K]
    def supported(self, tag, h):
        return bool(h) and all(s in self.K for s in h) and all(
            self.row(tag, s, self.a['policy'][s]).get(t, Q(0)) > 0 for s, t in zip(h, h[1:]))
    def valid_rows(self, tag):
        return all(not r or (sum(r.values()) == 1 and all(t in self.ambient and p > 0 and
                    (p * 4).denominator == 1 for t, p in r.items()))
                   for s in self.K for act in self.actions for r in [self.row(tag, s, act)])
    def m_link(self, tag):
        parsed = {}
        for s in self.K:
            pos, profiles = ast.literal_eval(self.a['publishedM'][s])
            parsed[s] = (pos, tuple(tuple(x == 'lethal' for x in outcomes) for _, outcomes in profiles))
        # Imported labels are comparison data only. Raw classes determine every computation.
        return (self.a['publishedM'] == dict(zip(self.K, self.anchors['M_class_labels'])) and
                all((self.pred(tag, x) == self.pred(tag, y)) == (parsed[x] == parsed[y])
                    for x in self.K for y in self.K))
    def tuple(self, path):
        return (tuple(self.a['histories'][path['source_history']]), tuple(path['events']))
    def active(self):
        rec = self.a['receiverInput']; g = rec['activation']
        return (g['source_present'] and g['target_receiver_funded'] and
                rec['latent_target']['funded_receiver'] and (not g['mixed_event_required'] or self.mixed()))
    def mixed(self):
        return any(e['id'] != 'exit' and e['atomic'] and e['source_support'] and e['target_support'] and
                   e['from'] in self.a['realized'] and e['to'] in self.a['realized'] for e in self.a['eventTable'])
    def receiver_factor(self, s, name=None):
        """The same raw coordinate map is checked at every audited occurrence.
        A history-specific override is the declared terminal override only.
        """
        rec = self.a['receiverInput']['content']
        override = rec['history_overrides'].get(name) if name is not None else None
        if override: return f"p{override['p']}w{override['w']}"
        p, w = wheel.state(s)
        for field, v in [('position_rule', p), ('phase_rule', w)]:
            rule = rec[field]
            if rule.startswith('constant_'): v = int(rule.split('_')[-1])
            elif not rule.startswith('copy_source_terminal_'): raise ValueError(rule)
            if field == 'position_rule': p = v
            else: w = v
        return f'p{p}w{w}'
    def receiver(self, name):
        return self.receiver_factor(self.a['histories'][name][-1], name)
    def ledger(self, tag):
        d = self.a['maintenance']; r = self.a[f'resources:{tag}']
        budget = Q(d['initial_budget_tokens']); cost = Q(d['action_cost_tokens'])
        recharge = Q(d['recharge_tokens_per_action']) if r['available'] else Q(0)
        return budget, cost, recharge, budget - cost + recharge


def clause(i, tag, c):
    missing = [k for k in scope(tag, c) if i.a.get(k) is None]
    if missing: return checked({'complete': False}, missing=missing)
    gates = {'complete': True, 'rows_valid': i.valid_rows(tag)}
    details = {}
    if c == 'C1':
        P = i.P(tag); preds = [i.pred(tag, s) for s in i.a['prototypes']]
        C = [[Q(int(i.pred(tag, s) == v)) for v in preds] for s in i.K]
        U = [[Q(int(i.pred(tag, s) == v), sum(i.pred(tag, t) == v for t in i.K))
              if any(i.pred(tag, t) == v for t in i.K) else Q(0) for s in i.K] for v in preds]
        audit = i.a['audit']; t1 = i.base['t1_import']
        published = lambda name: wheel.fraction_matrix(i.a[name])
        gates.update(audit_protocol=audit['tau']==2 and Q(audit['epsilon'])==Q(1,16) and Q(audit['retention_threshold'])==Q(3,4),
                     anchors=all(published(n) == wheel.fraction_matrix(i.anchors[n.removeprefix('published')])
                                 for n in ('publishedP','publishedC','publishedU')),
                     prototypes_order=len(preds)==7 and len(set(preds))==7 and all(
                         i.K[next(j for j,row in enumerate(i.a['publishedC']) if row[k]==1)]==s
                         for k,s in enumerate(i.a['prototypes'])),
                     class_coverage=all(i.pred(tag,s) in preds for s in i.K),
                     P_reconstruction=P==published('publishedP'),
                     C_reconstruction=C==published('publishedC'), U_reconstruction=U==published('publishedU'))
        pe = [[Q(15,16)*p+Q(1,160) for p in row] for row in P]
        E = wheel.matmul(wheel.matmul(wheel.matmul(pe,pe),C),U)
        E0 = wheel.matmul(wheel.matmul(wheel.matmul(P,P),C),U)
        fixed = wheel.fixed_law(E); pi=fixed['distribution']
        core = i.base['t1_import']['core']; mass = sum((pi[j] for j,s in enumerate(i.K) if s in core),Q(0)) if pi else None
        tv=sum(abs(pi[j]-(Q(1,len(core)) if s in core else 0)) for j,s in enumerate(i.K))/2 if pi else None
        d0=wheel.defect(E0); de=wheel.defect(E)
        gates.update(unique=fixed['unique'], probability=pi is not None and sum(pi)==1 and min(pi)>=0,
                     displayed_pi=pi==[Q(v) for v in t1['C1']['published_pi']],
                     nonuniform=pi is not None and pi!=[Q(1,10)]*10,
                     retention=mass==Q(77,80) and mass>=Q(audit['retention_threshold']),
                     TV=tv==Q(3,80), defect_zero=d0==Q(1,8), defect_perturbed=de==Q(78795,524288))
        details.update(pi=pi,core_mass=mass,TV=tv,defect_zero=d0,defect_perturbed=de)
    elif c in ('C2','C3'):
        gates['M_link']=i.m_link(tag)
        if c=='C2': gates['declared_split']=i.lower(tag,'p1w0')==i.lower(tag,'p1w1') and i.pred(tag,'p1w0')!=i.pred(tag,'p1w1')
        else:
            groups={s:i.lower(tag,s) for s in i.K}; classes=wheel.canonical_partition(groups,i.K); traj=[len(set(classes.values()))]
            partitions=[classes]
            while True:
                signatures={}
                for s in i.K:
                    profiles=[]
                    for act in i.actions:
                        masses={}
                        for t,p in i.row(tag,s,act).items():
                            key=('block',classes[t]) if t in classes else ('exit',t)
                            masses[key]=masses.get(key,Q(0))+p
                        profiles.append(tuple(sorted(masses.items(),key=repr)))
                    signatures[s]=(classes[s],tuple(profiles))
                nxt=wheel.canonical_partition(signatures,i.K); traj.append(len(set(nxt.values())))
                stable=all((classes[x]==classes[y])==(nxt[x]==nxt[y]) for x in i.K for y in i.K)
                partitions.append(nxt); classes=nxt
                if stable: break
            gates.update(trajectory=traj==[6,7,7], terminal_M=all((classes[x]==classes[y])==(i.pred(tag,x)==i.pred(tag,y)) for x in i.K for y in i.K))
            details['trajectory']=traj
    elif c=='C4':
        def current(s):
            return tuple(i.a['positions'][s] if ch=='public_position' else
                         tuple(a for a in i.actions if i.row(tag,s,a)) if ch=='deadline_action_availability'
                         else i.pred(tag,s) for ch in i.a['channels'])
        h=i.a['histories']['h_split']
        gates.update(M_link=i.m_link(tag), connector_refs=len(h)>=2 and h[0]=='p1w0' and h[-1]=='p1w1',
                     collision=current('p1w0')==current('p1w1') and i.pred(tag,'p1w0')!=i.pred(tag,'p1w1'),
                     connector=i.supported(tag,h))
        outputs={s:current(s) for s in i.K}
        exposed=any(len({outputs[s][j] for s in i.K})>1 and all(i.pred(tag,x)!=i.pred(tag,y) or outputs[x][j]==outputs[y][j]
                     for x in i.K for y in i.K) for j in range(len(i.a['channels'])))
        gates['full_HIDD_fails']=exposed
    elif c=='C5':
        ps={p['id']:p for p in i.a[f'protocols:{tag}']}
        credits={name:wheel.cycle_credit(p)[0] for name,p in ps.items()}
        gates.update(credits=credits=={'clockwise':'self','scheduled':'other','internalized':'none','null':'none'},
                     owners=all((credits[n]!='self' or p['owner']==tag) and (credits[n]!='other' or p['owner']=='external') for n,p in ps.items()),
                     anchors=all(i.supported(tag,i.a['histories'][name]) for name in i.base['new_data']['c5']['history_anchor'].values()))
        details['credits']=credits
    elif c=='C6':
        future=full_future(i,tag); trace=trace_check(i,tag); budget,cost,recharge,after=i.ledger(tag)
        gates.update(M_link=i.m_link(tag), P_reference=i.P(tag)==wheel.fraction_matrix(i.a['publishedP']),
                     **trace['gates'], unit_funding=budget==cost==recharge==after==1,
                     future_sufficient=future['pass'], strictly_coarser=i.pred(tag,'p0w0')==i.pred(tag,'p0w1'))
        details.update(future=future,trace=trace)
    elif c=='C7':
        d=i.a[f'joint:{tag}']; assemb=d['assemblages']; by={v['id']:v for v in assemb}
        def dist(v):
            pairs=[(freeze(i.a['histories'][v['left'][l]]),freeze(i.a['histories'][v['right'][r]])) for l,r in v['coupling']]
            return tuple(sorted(((pair,Q(n,len(pairs))) for pair,n in Counter(pairs).items()),key=repr)) if pairs else ()
        outputs={n:dist(v) if 'jointPairing' in d['joint_observables'] else () for n,v in by.items()}
        # Reassembly is a raw reference to fixed diagonal/crossed coupling constructors.
        couples={'diagonal':[[0,0],[1,1]],'crossed':[[0,1],[1,0]]}
        gates.update(local=len(by)==2 and all(len(v['coupling'])==2 and len(set(map(tuple,v['coupling'])))==2 for v in assemb) and
                     all(by[r['assemblage']]['coupling']==couples[r['coupling']] for r in d['reassembly']),
                     histories=all(i.supported(tag,h) for h in i.a['histories'].values()),
                     distinct_histories=len(set(map(freeze,i.a['histories'].values())))==len(i.a['histories']),
                     branchwise_equal=len(assemb)==2 and assemb[0]['left']==assemb[1]['left'] and assemb[0]['right']==assemb[1]['right'],
                     strict_joint=len(set(outputs.values()))==2, mixed=i.mixed(), receiver_active=i.active(),
                     operational_display=i.mixed() and i.active() and len(set(outputs.values()))==2,
                     P_reference=i.a['publishedP']==i.anchors['P'] and i.P(tag)==wheel.fraction_matrix(i.a['publishedP']))
        details['joint_distributions']=outputs
    elif c=='C8':
        resource=i.a[f'resources:{tag}']; budget,cost,recharge,after=i.ledger(tag)
        S,trace=greatest(i.K,lambda S,s: c8_available(i,tag) and bool(safe_actions(i,tag,s,S)))
        gates.update(nonempty=bool(S), available=c8_available(i,tag), ledger=resource['available'] and budget==cost==recharge==after==1,
                     P_unchanged=i.P(tag)==wheel.fraction_matrix(i.anchors['P']))
        details.update(greatest=S,pruning=trace)
    return checked(gates,**details)


def trace_check(i,tag):
    a=i.a; events=a['eventTable']; stages=i.base['new_data']['corridor']['stages']; paths=a['routeTable']; by={e['id']:e for e in events}
    g={'realization':a['realized']==stages, 'event_references':len(by)==len(events) and all(e['from'] in stages and e['to'] in stages for e in events),
       'paths_nonempty':len(paths)==2 and {p['id'] for p in paths}=={'route_a','route_b'},
       'funded':a['receiverInput']['latent_target']['funded_receiver'] and a[f'resources:{tag}']['available'],
       'owner':a[f'resources:{tag}']['owner']==tag}
    g['strict_steps']=g['event_references'] and all(e['strict_step'] and e['atomic'] and stages.index(e['to'])==stages.index(e['from'])+1 and e['from'] in a['realized'] and e['to'] in a['realized'] for e in events)
    g['paths']=all(p['events'] and i.supported(tag,a['histories'][p['source_history']]) and all(x in by for x in p['events']) and
                   all(by[x]['to']==by[y]['from'] for x,y in zip(p['events'],p['events'][1:])) for p in paths)
    g['path_coverage']={x for p in paths for x in p['events']}==set(by)
    g['unit_ticks']=all(a[f'ticks:{tag}'][s][act]==1 for s in i.K for act in i.actions if i.row(tag,s,act))
    g['writers']=bool(paths) and all(a['writers'][tag].get(p['id']) is True for p in paths)
    return checked(g)


def full_future(i,tag):
    """Finite bisimulation certificate for all runs and all finite words.
    Counts are symbolic unbounded naturals. Equal code fixes counts/phase/route/
    funding/owner; readouts and updates below are their defined algebraic laws.
    The finite check compares predictive-image masses and ticks, including exits.
    """
    a=i.a; ambient=i.ambient; pairs=[(x,y) for x in ambient for y in ambient if i.pred(tag,x)==i.pred(tag,y)]
    g={'interface':a['interface']==['PredictiveNow','event_order','tick_phase','cumulative_progress','endogenous_record_count','route_residue','maintenance_state','owner'],
       'nonempty_contexts':bool(a['routeTable'])}
    failure=None
    for x,y in pairs:
        for act in i.actions:
            def summary(s):
                row=i.row(tag,s,act) if s in i.K else {}; masses={}
                for t,p in row.items(): masses[i.pred(tag,t)]=masses.get(i.pred(tag,t),Q(0))+p
                return masses, a[f'ticks:{tag}'][s][act] if s in i.K else 0
            if summary(x)!=summary(y): failure=(x,y,act); break
        if failure: break
    g['one_step_bisimulation']=failure is None
    # Abstract only the unbounded count. All its laws are affine identities.
    # Assigned FutureClosure allows every declared outcome, even mass-zero ones.
    # Reproduce that stronger closure, rather than checking a bounded word set.
    outcomes=[]
    for s in ambient:
        if i.pred(tag,s) not in [i.pred(tag,t) for t in outcomes]:outcomes.append(s)
    roots={(s,0,bool(a['receiverInput']['latent_target']['funded_receiver']),p['id'])
           for s in i.K for p in a['routeTable']}
    closure=set(roots); _,_,_,after=i.ledger(tag)
    while True:
        nxt=closure|{(target,(phase+(a[f'ticks:{tag}'][s][act] if s in i.K else 0))%2,
                      funded and after>0,route)
                     for s,phase,funded,route in closure for act in i.actions for target in outcomes}
        if nxt==closure:break
        closure=nxt
    return checked(g, ordered_code_equal_pairs=len(pairs),counterexample=failure,
                   abstract_closure=sorted(closure),abstract_closure_size=len(closure),
                   unbounded_coordinate='count: Nat, represented symbolically; not reduced modulo a bound',
                   scope='all run states; unbounded words by one-step bisimulation and induction',
                   closure='least closure of every K/route root under all predictive-image outcomes; counters unbounded',
                   readout_laws={f:'defined from assigned row/update; symbolic identity on whole closure' for f in FIELDS})


def c8_available(i,tag):
    b,c,r,n=i.ledger(tag)
    return i.a[f'resources:{tag}']['available'] and b>=c and n>0 and i.a[f'resources:{tag}']['owner']==tag


def safe_actions(i,tag,s,S):
    return [a for a in i.actions for row in [i.row(tag,s,a)] if row and sum(row.values())==1 and
            all(t in S and p>0 and (p*4).denominator==1 for t,p in row.items())]


def greatest(K,retain):
    S=list(K); trace=[S]
    while True:
        nxt=[s for s in S if retain(set(S),s)]
        if nxt==S: break
        S=nxt; trace.append(S)
    # Exhaustive arbitrary-set check: monotonicity and greatestness, not a bounded horizon.
    subsets=[set(s for j,s in enumerate(K) if mask>>j&1) for mask in range(1<<len(K))]
    contained=all(not all(retain(T,s) for s in T) or T<=set(S) for T in subsets)
    fixed=all(retain(set(S),s) for s in S)
    if not contained or not fixed: raise AssertionError('invalid greatest fixed-point computation')
    return S,trace


def package(model, a):
    b=exchange(a); i=Inputs(model,b); primitive=list(a)
    scopes={c:primitive if c=='C1' else scope('target',c) for c in CLAUSES}
    locals_={c:{k:copy.deepcopy(b[k]) for k in scopes[c]} for c in CLAUSES}
    # Star cover, fixed parent C1, exact running intersection and dependency closure.
    cover=all(set(scope('target',c))<=set(scopes[c]) for c in CLAUSES)
    equalities=[locals_[c][k]==b[k] for c in CLAUSES for k in scopes[c]]
    overlaps=[locals_[c][k]==locals_['C1'][k] for c in CLAUSES[1:] for k in scopes[c]]
    clauses={tag:{c:clause(i,tag,c) for c in CLAUSES} for tag in TAGS}
    coordinates=wheel.package_coordinates(model['base'])
    gates={'cover':cover,'map_total':all(a[k] is not None for k in primitive),
           'value_preserving':all(equalities),'edge_compatible':all(overlaps),
           'complete_global':all(v is not None for v in b.values()),
           'restrictions':all(equalities),'coordinate_views':coordinates['pass'],
           'all_target_clauses':all(r['pass'] for r in clauses['target'].values())}
    return checked(gates,clauses=clauses,coordinates=coordinates,
                   root_scope=len(primitive),overlap_equations=len(overlaps),restriction_equations=len(equalities)), b


def route_readout(i, register):
    """Interpret the raw readout selector on the resulting target register."""
    spec=i.base['new_data']['corridor']['future_route_readout']
    rules={
        'phase of first source WheelState in retained raw route tuple after one funded target step':0,
        'phase of last source WheelState in retained raw route tuple after one funded target step':-1,
    }
    supported=spec['rule'] in rules
    owned=(spec['owner']=='target' and i.a['resources:target']['owner']==spec['owner'])
    if not supported or not owned or not register or not register[0]:return None
    return wheel.state(register[0][rules[spec['rule']]])[1]


def phase2_path_check(i, path):
    """Execution exists only on the activated, realized arrival route.
    This prerequisite is independent of post-withdrawal response availability.
    """
    stages=i.base['new_data']['corridor']['stages']
    events={event['id']:event for event in i.a['eventTable']}
    ids=path['events']; realized=set(i.a['realized'])
    return (i.active() and bool(ids) and path['source_history'] in i.a['histories'] and
            i.supported('source',i.a['histories'][path['source_history']]) and
            all(id in events for id in ids) and
            all(events[id]['atomic'] and events[id]['strict_step'] and
                events[id]['from'] in realized and events[id]['to'] in realized and
                events[id]['from'] in stages and events[id]['to'] in stages and
                stages.index(events[id]['to'])==stages.index(events[id]['from'])+1 for id in ids) and
            all(events[x]['to']==events[y]['from'] for x,y in zip(ids,ids[1:])) and
            events[ids[0]]['from']==stages[0] and events[ids[-1]]['to']==stages[-1] and
            events[ids[-1]]['target_support'] and not events[ids[-1]]['source_support'])


def routes(i):
    a=i.a; paths=a['routeTable']; contexts=[]; records=[]; entry=[]
    readout_spec=i.base['new_data']['corridor']['future_route_readout']
    supported_rules={
        'phase of first source WheelState in retained raw route tuple after one funded target step',
        'phase of last source WheelState in retained raw route tuple after one funded target step'}
    for p in paths:
        raw=i.tuple(p); contexts.append(raw); source=i.receiver(p['source_history'])
        action=a['policy'].get(source); row=i.row('target',source,action) if action is not None else {}
        write=a['receiverInput']['route_register_write']['rule']=='copy_raw_route_tuple'
        activated=i.active(); realized_path=phase2_path_check(i,p)
        row_valid=bool(row) and sum(row.values())==1 and all(
            weight>0 and (weight*4).denominator==1 and t in i.ambient for t,weight in row.items())
        available=(activated and realized_path and row_valid and c8_available(i,'target') and
                   a['writers']['target'].get(p['id']) is True)
        resulting=[]
        # Do not fabricate an entry from a merely hypothetical receiver output.
        for t,weight in (row.items() if available else []):
            register=raw if write and t in i.K else None
            step={'factor':t,'probability':weight,'register':register,
                  'counter':1,'ticks':a['ticks:target'][source][action],
                  'budget':i.ledger('target')[3]}
            resulting.append(step); entry.append(step)
        persistent=available and bool(resulting) and all(x['register']==raw for x in resulting)
        readouts={route_readout(i,x['register']) for x in resulting}
        records.append({'route':p['id'],'raw_tuple':raw,'receiver_factor':source,
                        'arrival_activated':activated,'realized_phase2_path':realized_path,
                        'phase2_execution_available':available,'row_valid':row_valid,
                        'action':action,'resulting_states':resulting,'persistent':persistent,
                        'future_readout':next(iter(readouts)) if len(readouts)==1 else None})
    outputs=[r['future_readout'] for r in records]
    g={'nonempty_comparison':len(paths)>=2,'distinct_raw_tuples':len(set(contexts))==len(paths),
       'supported_histories':all(i.supported('source',a['histories'][p['source_history']]) for p in paths),
       'shared_endpoint':bool(records) and len({r['receiver_factor'] for r in records})==1,
       'realized_activated_execution':bool(records) and all(r['phase2_execution_available'] for r in records),
       'retained_after_step':bool(records) and all(r['persistent'] for r in records),
       'readout_rule_supported':readout_spec['rule'] in supported_rules,
       'readout_owner':readout_spec['owner']=='target' and a['resources:target']['owner']==readout_spec['owner'],
       'future_readout_difference':None not in outputs and len(set(outputs))>=2,
       'target_owner':a['resources:target']['owner']=='target'}
    return checked(g,records=records,entry_states=entry,raw_contexts=contexts,
                   readout_spec=readout_spec,
                   route_status='routeIndexed' if all(g.values()) else 'unlicensed')


def lineage(model,a):
    required=list(set(scope('source','C6')+scope('target','C6')))
    missing=[k for k in required if a.get(k) is None]
    if missing: return checked({'complete':False},missing=missing)
    i=Inputs(model,a); events=a['eventTable']; stages=model['base']['new_data']['corridor']['stages']; raw=model['declaration']['raw_interface']['corridor']
    route_result=routes(i); by={e['id']:e for e in events}; atoms=[]
    # G4 source/target vertex expansion, successive-stage dependencies and exact audits.
    vertices=[('source_live','source',0)]+[(e['id']+'-'+tag,tag,stages.index(e['to']))
              for e in events if e['to'] in stages for tag in TAGS if e[tag+'_support']]
    lookup={v[0]:v for v in vertices}
    dependencies=[(x[0],y[0]) for x in vertices for y in vertices if y[2]==x[2]+1]
    def reaches(start,end,removed=None):
        seen={start} if start in lookup and lookup[start][1]!=removed else set()
        while True:
            nxt=seen|{y for x,y in dependencies if x in seen and lookup[y][1]!=removed}
            if nxt==seen:return end in seen
            seen=nxt
    source_audit=raw['source_audit']; target_audit=raw['target_audit']; later=raw['later_audit']
    audits=all(x in lookup for x in (source_audit,target_audit,later))
    audit_mixed=audits and lookup[source_audit][2]==lookup[target_audit][2] and lookup[source_audit][1]=='source' and lookup[target_audit][1]=='target'
    nonredundant=audit_mixed and reaches(source_audit,later) and reaches(target_audit,later) and all(
        not (reaches(source_audit,later,side) and reaches(target_audit,later,side)) for side in TAGS)
    traces={tag:trace_check(i,tag) for tag in TAGS}
    atomic_gates={'distinct_carriers':len(set(model['base']['carrier']['tags']))==2,
                  'no_realized_gap':a['realized']==stages,
                  'entry_exit_support':bool(stages) and any(e['id']=='exit' and e['target_support'] and not e['source_support'] for e in events),
                  'audited_mixed_support':audit_mixed,'audit_reachability':audits and reaches(source_audit,later) and reaches(target_audit,later),
                  'nonredundant_interventions':nonredundant,
                  'strict_path_updates':all(t['pass'] for t in traces.values()),
                  'computed_route_status':route_result['pass']}
    # Source history frontier and raw coordinate receiver; no supplied signature or future.
    n=model['base']['new_data']; hist=a['histories']; frontier=n['bridge_frontier']; reps=n['same_class_pair']; edge=tuple(n['strict_source_edge'])
    futures={tag:full_future(i,tag) for tag in TAGS}
    laws={
        'coverage':bool(frontier) and all(name in hist and i.supported('source',hist[name]) and len(hist[name])>=2 for name in frontier),
        'strict_edge':edge[0]!=edge[1] and i.row('source',edge[0],a['policy'][edge[0]]).get(edge[1],Q(0))>0 and any(edge in list(zip(hist[name],hist[name][1:])) for name in frontier),
        'different_pasts':hist[reps[0]]!=hist[reps[1]],
        'source_representatives':i.pred('source',hist[reps[0]][-1])==i.pred('source',hist[reps[1]][-1]),
        'target_representatives':i.pred('target',i.receiver(reps[0]))==i.pred('target',i.receiver(reps[1])),
        'coordinate_map':all(i.receiver(name)==hist[name][-1] for name in frontier),
        'successor_weights':all(i.row('source',s,act)==i.row('target',s,act) for s in i.K for act in i.actions),
        'order_progress':all(len(hist[name])-1==sum(i.row('source',s,a['policy'][s]).get(t,Q(0))>0 for s,t in zip(hist[name],hist[name][1:])) for name in frontier),
        'tick':all(a['ticks:source'][s][act]==a['ticks:target'][s][act]==1 for s in i.K for act in i.actions if i.row('source',s,act)),
        'record':all(a['writers'][tag].get(p['id']) is True for tag in TAGS for p in a['routeTable']),
        'route':route_result['pass'],
        'maintenance':all(c8_available(i,tag) and i.ledger(tag)==(Q(1),)*4 for tag in TAGS),
        'owner':a['resources:source']['owner']=='source' and a['resources:target']['owner']=='target',
        'full_future':all(f['pass'] for f in futures.values()),
        'raw_M_link':all(i.m_link(tag) for tag in TAGS),
        'snapshot_codecs':all(i.pred('source',hist[name][-1])==i.pred('target',i.receiver(name)) for name in frontier),
    }
    # Exact finite images of bridge-owned snapshots, including raw route registers.
    # Counters stay unbounded at run level; codecs cover these actual audit values.
    snapshot_pairs=[]; snapshot_domain=[]; snapshot_checks=[]
    # G1c RawRunDynamics.snapshotPositions is [afterFirst, endpoint], with
    # occurrences 1/2 and realized events mix_1/mix_2. These selectors are fixed.
    positions=[('afterFirst',1,'mix_1'),('endpoint',2,'mix_2')]
    for path in a['routeTable']:
        name=path['source_history']; h=hist[name]; residue=i.tuple(path)
        # GenericTransport.targetHistoryFor: preserve prefix, receiver constructs
        # terminal. Independently check the typed coordinate map at EACH snapshot.
        target_history=h[:-1]+[i.receiver(name)]
        for label,occurrence,event_id in positions:
            snapshot_domain.append({'route':path['id'],'position':label,
                                    'occurrence':occurrence,'event':event_id})
            valid=(occurrence<len(h) and occurrence<len(target_history) and event_id in by and
                   by[event_id]['from'] in a['realized'] and by[event_id]['to'] in a['realized'] and
                   event_id in path['events'] and by[event_id]['strict_step'] and by[event_id]['atomic'])
            if not valid:
                snapshot_checks.append(False)
                continue
            source_factor=h[occurrence]; target_factor=target_history[occurrence]
            mapped_factor=i.receiver_factor(source_factor, name if label=='endpoint' else None)
            snapshot_checks.append(target_factor==mapped_factor and source_factor in i.K and target_factor in i.K)
            frames=[]
            for tag,history_,factor in [('source',h,source_factor),('target',target_history,target_factor)]:
                prefix=history_[:occurrence+1]
                ticks=sum(a['ticks:'+tag][s][a['policy'][s]] for s in prefix[:-1])
                progress=sum(i.row(tag,s,a['policy'][s]).get(t,Q(0))>0 for s,t in zip(prefix,prefix[1:]))
                counter=occurrence; funded=c8_available(i,tag)
                frames.append((i.pred(tag,factor),counter,ticks%2,progress,
                               counter if funded and a['writers'][tag].get(path['id']) else 0,
                               residue,funded,a['resources:'+tag]['owner']))
            snapshot_pairs.append(frames)
    laws['snapshot_domain']=len(snapshot_domain)==4 and len(snapshot_pairs)==4
    laws['snapshot_coordinate_map']=bool(snapshot_checks) and all(snapshot_checks)
    alphabets={tag:[list(dict.fromkeys(pair[TAGS.index(tag)][j] for pair in snapshot_pairs))
                    for j in range(8)] for tag in TAGS}
    roundtrips=bool(snapshot_pairs) and all(
        alphabets[tag][j][alphabets[tag][j].index(pair[TAGS.index(tag)][j])]==pair[TAGS.index(tag)][j]
        for pair in snapshot_pairs for tag in TAGS for j in range(8))
    def typed_image(frame):
        return frame[:-1]+({'source':'target','target':'source'}[frame[-1]],)
    commutes=all(typed_image(pair[0])==pair[1] for pair in snapshot_pairs)
    laws['codec_roundtrips']=roundtrips
    laws['all_eight_snapshot_fields_transport']=commutes
    endpoints=bool(a['routeTable']) and all(p['events'] and p['events'][-1] in by and by[p['events'][-1]]['to']==stages[-1] and
                by[p['events'][-1]]['target_support'] and not by[p['events'][-1]]['source_support'] and
                i.receiver(p['source_history']) in i.K and i.pred('source',hist[p['source_history']][-1])==i.pred('target',i.receiver(p['source_history'])) for p in a['routeTable'])
    gates={'complete':True,'rows':all(i.valid_rows(tag) for tag in TAGS),
           'atomic_leg':all(atomic_gates.values()),'bridge':all(laws.values()),
           'receiver_activation':i.active(),'typed_endpoint_link':endpoints and i.active() and all(atomic_gates.values())}
    return checked(gates,atomic=checked(atomic_gates,vertices=vertices,dependencies=dependencies),
                   bridge=checked(laws,full_future=futures,snapshot_alphabet_sizes={tag:list(map(len,values)) for tag,values in alphabets.items()},snapshot_pairs=snapshot_pairs,snapshot_domain=snapshot_domain,snapshot_coordinate_checks=snapshot_checks),
                   route=route_result,endpoint_link=endpoints)


def withdrawn(model,b):
    bw=copy.deepcopy(b); retention=model['declaration']['raw_interface']['post_exit_retention']
    bw['resources:target']['available']=bool(bw['resources:target']['available'] and retention['resource'] in retention['retained_resources'])
    return bw


def run_laws(i,tag):
    b,c,r,n=i.ledger(tag); paths=i.a['routeTable']
    return checked({'positive_conserved_unit_budget':b==c==r==n==1,
                    'funded':i.a[f'resources:{tag}']['available'],
                    'ticks':all(i.a[f'ticks:{tag}'][s][act]==1 for s in i.K for act in i.actions if i.row(tag,s,act)),
                    'writers':bool(paths) and all(i.a['writers'][tag].get(p['id']) is True for p in paths),
                    'owner':i.a[f'resources:{tag}']['owner']==tag},
                   equations={f: {'predictive':'raw predictive class of actual supported successor',
                       'order':'counter + 1','tick':'(ticks + assigned increment) mod 2',
                       'progress':'counter + 1','writer':'same route context and writer',
                       'record':'counter + 1 iff funded and writer available',
                       'residue':'same raw route tuple','maintenance':'funded and post-budget > 0',
                       'owner':'assigned target resource owner','budget':'budget - cost + effective recharge'}[f] for f in FIELDS},
                   unbounded_argument='counter identities hold symbolically for every natural counter; invariant funding and route context preserved by induction')


def autonomy(model,b,P,version):
    required=scope('target','C8')+['ticks:target','writers','histories','routeTable','receiverInput','eventTable','realized']
    missing=[k for k in required if b.get(k) is None]
    if missing:return checked({'complete':False},missing=missing)
    bw=withdrawn(model,b); i=Inputs(model,bw); before=Inputs(model,b)
    raw=model['declaration']['raw_interface']; retention=raw['post_exit_retention']
    domains=raw['disturbance_interface']['domain']; actions=raw['response_semantics']['action_domain']
    removed=raw['withdrawal_rule']['removed_roles']
    roles={'source','migration_bridge','migration_controller','external_decoder','external_scheduler','undeclared_repair_support'}
    withdrawal=(set(removed)==roles and not retention['source_present_after_withdrawal'])
    contexts=[i.tuple(p) for p in i.a['routeTable']]
    entry_execution=routes(before); entries=entry_execution['entry_states']; laws=run_laws(i,'target')
    coordinates=wheel.package_coordinates(model['base'])
    clauses={c:clause(i,'target',c) for c in CLAUSES} if version=='F' else {}
    state_package={s: P['pass'] and coordinates['pass'] and all(r['pass'] for r in clauses.values()) and laws['pass'] for s in i.K} if version=='F' else {s:True for s in i.K}
    def responses(S,s,ctx,dist):
        b0,c,r,n=i.ledger('target')
        if dist!='nominal' or not withdrawal or not contexts or not laws['pass']:return []
        if version=='F' and not state_package[s]:return []
        return [act for act in safe_actions(i,'target',s,S)
                if i.a['writers']['target'].get(ctx[0]) is True and
                all(version!='F' or state_package[t] for t in i.row('target',s,act))]
    indexed_contexts=[(p['id'],i.tuple(p)) for p in i.a['routeTable']]
    def retain(S,s):
        if version=='O':return c8_available(i,'target') and bool(safe_actions(i,'target',s,S))
        return state_package[s] and bool(domains) and bool(indexed_contexts) and all(responses(S,s,ctx,d) for ctx in indexed_contexts for d in domains)
    S,pruning=greatest(i.K,retain)
    response_table={s:{ctx[0]:{d:responses(set(S),s,ctx,d) for d in domains} for ctx in indexed_contexts} for s in S}
    # Detect finite-algorithm errors independently by checking every subset of K.
    viable_subsets=0
    for mask in range(1<<len(i.K)):
        T={s for j,s in enumerate(i.K) if mask>>j&1}
        if all(retain(T,s) for s in T):viable_subsets+=1
    b0,c,r,n=i.ledger('target')
    gates={'complete':True,'withdrawal':withdrawal,'nominal_domain':domains==['nominal'],
           'action_domain':actions==i.actions,'nonempty_contexts':bool(indexed_contexts),
           'resource_closure':retention['resource'] in retention['retained_resources'] and i.a['resources:target']['available'] and i.a['resources:target']['owner']=='target',
           'unit_positive_conserved_ledger':b0==c==r==n==1,
           'P_unchanged':i.P('target')==wheel.fraction_matrix(i.anchors['P']),
           'nonempty_invariant':bool(S),'arrival_execution':entry_execution['gates']['realized_activated_execution'],'endpoint_inside':bool(entries) and all(x['factor'] in S and x['register'] is not None for x in entries),
           'total_responses':bool(S) and bool(domains) and bool(indexed_contexts) and all(response_table[s][ctx[0]][d] for s in S for ctx in indexed_contexts for d in domains),
           'run_advancement':laws['pass'],'greatest_fixed_point':all(retain(set(S),s) for s in S)}
    if version=='F':gates['packageInside']=all(state_package[s] for s in S)
    return checked(gates,greatest=S,pruning=pruning,viable_subset_count=viable_subsets,
                   packageAt=state_package if version=='F' else None,withdrawn_clauses=clauses,
                   responses=response_table,entry_states=entries,entry_execution=entry_execution,run_laws=laws,
                   effective_ledger={'budget':b0,'cost':c,'recharge':r,'next_budget':n},
                   generic_greatest_argument='monotone: support containment is preserved by inclusion; package/availability predicates independent of S. Descending prune from K contains every postfixed subset by induction; stabilized set is viable.')


def wellformed(model):
    result=wheel.check_wellformed(model['base'])
    issues=list(result['issues'])
    declared=model['declaration']; raw=declared['raw_interface']
    if set(raw['post_exit_retention']['retained_resources'])- {raw['post_exit_retention']['resource']}:issues.append('unknown_retained_resource')
    # None is a legal typed partial assignment, not a syntax/reference defect.
    a=assignment(model)
    if set(a)!=set(import_cells(model['base'])):issues.append('unknown_primitive_cell')
    return {'pass':not issues,'issues':issues,'missing_cells':[k for k,v in a.items() if v is None]}


def evaluate(model):
    a=assignment(model); P,b=package(model,a); L=lineage(model,a)
    F=autonomy(model,b,P,'F'); O=autonomy(model,b,P,'O')
    return {'wellformed':wellformed(model),'package':P,'lineage':L,
            'autonomy_full':F,'autonomy_operational':O,
            'lane_vectors':{'F':{'package':P['pass'],'lineage':L['pass'],'autonomy_full':F['pass']},
                            'O':{'package':P['pass'],'lineage':L['pass'],'autonomy_operational':O['pass']}},
            'AF_implies_P_instance':not F['pass'] or P['pass']}


def mutate(model,control):
    m=copy.deepcopy(model)
    for edit in control['json_edits']:
        parts=edit['path'].strip('/').split('/'); at=m['base'] if parts[0]=='base' else m['declaration']; parts=parts[1:] if parts[0]=='base' else parts
        for k in parts[:-1]:at=at[int(k)] if isinstance(at,list) else at[k]
        key=int(parts[-1]) if isinstance(at,list) else parts[-1]
        if edit.get('precondition'):
            assert all(at[k]==v for k,v in edit['precondition'].items())
        at[key]=copy.deepcopy(edit['value'])
    m['assignment_edits'].extend(copy.deepcopy(control['assignment_edits']))
    return m

AMBIGUITIES = [
    {'id':'A1','text':'StateViewsResolve/RunReadoutLawsAt are prose, not a new table. Use Substrate.viewScope: all ten state views share the clause cells. Resolve all 160 original coordinates; run readouts are the assigned C6 affine definitions, checked with positive unit ledger/writers across the unbounded closure. No state-varying verdict table is invented.'},
    {'id':'A2','text':'The G4 positive adapter used positive-only atomicPosAvailable and fixed stage support. Recompute availability from assigned trace/funding/route data; expand vertices by actual event support. Keep the mix_2 audit selectors fixed. Source/target stage support follows the declared single-leg stage-position rule; missing audited event vertices reject.'},
    {'id':'A3','text':'Run counters are unbounded; factor fixed points use K. Nominal responses have identity environment effects, and are safe across every raw positive outcome. An affine-update/bisimulation argument covers all counts and words; there is no horizon cutoff.'},
    {'id':'A4','text':'Phase-2 entry requires arrival receiver activation and each complete realized strict route path, supported source history, funded target row and writer availability. Only that executed canonical target policy row contributes successors. Without activation or realization there are no entries; both autonomy versions explicitly gate on this prerequisite independently of withdrawal. Both routes and every resulting entry are checked, with no reset to the pre-probe factor.'},
    {'id':'A5','text':'The F package is BW, with only target recharge availability changed. Arrival receiver/event/route facts remain historical evidence. Withdrawal removes current response dependencies, not the recorded acquisition history; C7 is not reactivated after withdrawal.'},
    {'id':'A6','text':'AF→P is structurally implied by the declared PackageAt conjunction, nonempty entry and packageInside. The report gives this mathematical argument and checks every family member; it does not present Python sampling as a kernel proof of the universal theorem.'},
    {'id':'A7','text':'Greatest sets are unordered subsets. Compute descending pruning to a fixed point and independently enumerate all 1024 subsets for containment; response monotonicity follows because only support containment depends on S.'},
]


def secondary_predictions(models,results):
    K=models['Baseline']['base']['t1_import']['kernel_order']; b=results['Baseline']; p=results['G6-PACKAGE-ONLY']; l=results['G6-LINEAGE-ONLY']; w=results['G6-WITHDRAWAL-ONLY']
    records=[]
    def add(id,versions,got,witness,meaning):
        records.append({'id':id,'versions':versions,'expected':True,'observed':got,
                        'status':'CONFIRMED' if got else 'FAILED','witness':witness,'failure_meaning':meaning})
    add('all-wellformed',['F','O'],all(r['wellformed']['pass'] for r in results.values()),
        {c:r['wellformed'] for c,r in results.items()},'Malformed raw model invalidates intended control; partial assignments remain allowed.')
    add('declared-disturbance-and-response-quantifier',['F','O'],all(
        models[c]['declaration']['raw_interface']['disturbance_interface']['domain']==['nominal'] and
        r['autonomy_full']['gates']['nominal_domain'] and r['autonomy_operational']['gates']['action_domain']
        for c,r in results.items()),'For every invariant state, each raw route context and nominal disturbance, search all actions and test full support.',
        'Actions cannot substitute for disturbances; existential lucky successors do not establish safety.')
    for version,name in [('F','autonomy_full'),('O','autonomy_operational')]:
        x=b[name]
        add('baseline-greatest-K-'+version,[version],x['greatest']==K and x['gates']['endpoint_inside'] and x['gates']['total_responses'],
            {'greatest':x['greatest'],'responses':x['responses'],'entries':x['entry_states']},'The new invariant/response/entry adapter is not satisfiable as predicted.')
    x=b['autonomy_full']
    add('baseline-packageInside-every-state',['F'],all(x['packageAt'].values()),x['packageAt'],'AO cannot rescue missing full package preservation.')
    # Canonical policy is a predicted witness, not merely some response existence.
    policy=import_cells(models['Baseline']['base'])['policy']
    add('baseline-canonical-response-witness',['F','O'],all(policy[s] in actions for name in ('autonomy_full','autonomy_operational')
         for s,ctxs in b[name]['responses'].items() for ds in ctxs.values() for actions in ds.values()),policy,
         'Safe alternative responses may exist, but the canonical witness prediction failed.')
    add('package-deletion-full-consequence',['F'],not p['package']['clauses']['source']['C1']['pass'] and not p['package']['clauses']['target']['C1']['pass'] and
        not p['package']['gates']['map_total'] and not any(p['autonomy_full']['packageAt'].values()) and p['autonomy_full']['greatest']==[],
        {'map_total':p['package']['gates']['map_total'],'SF':p['autonomy_full']['greatest']},'Missing shared C1/map input did not force F rejection; no physical objecthood loss is inferred.')
    add('package-deletion-operational-unchanged',['O'],p['autonomy_operational']==b['autonomy_operational'] and all(
        p['package']['clauses'][tag][c]['pass'] for tag in TAGS for c in CLAUSES[1:]),
        {'SO':p['autonomy_operational']['greatest'],'C2_C8':{t:{c:p['package']['clauses'][t][c]['pass'] for c in CLAUSES[1:]} for t in TAGS}},
        'Missing C1 metadata affects operational autonomy or another clause, confounding O isolation.')
    a0=assignment(models['Baseline']); al=assignment(models['G6-LINEAGE-ONLY'])
    changes=[k for k in a0 if a0[k]!=al[k]]
    add('lineage-only-raw-cell-and-audit',['F','O'],changes==['eventTable'] and not l['lineage']['atomic']['gates']['audited_mixed_support'] and
        al['eventTable'][0]['source_support'] and Inputs(models['G6-LINEAGE-ONLY'],al).mixed(),
        {'changed_cells':changes,'vertices':l['lineage']['atomic']['vertices']},'Mutation changed additional cells or does not reject the fixed source audit.')
    add('lineage-all-clause-and-route-side-effects',['F','O'],all(x['pass'] for cs in l['package']['clauses'].values() for x in cs.values()) and l['lineage']['route']['pass'],
        {'clauses':{t:{c:x['pass'] for c,x in cs.items()} for t,cs in l['package']['clauses'].items()},'route':l['lineage']['route']['pass']},
        'Support change confounds package/autonomy isolation or removes the funded route probe.')
    add('withdrawal-arrival-and-lineage-unchanged',['F','O'],assignment(models['G6-WITHDRAWAL-ONLY'])==a0 and w['package']==b['package'] and w['lineage']==b['lineage'],
        {'same_assignment':assignment(models['G6-WITHDRAWAL-ONLY'])==a0},'Post-exit edit leaked into immutable arrival or pre-withdrawal lineage.')
    add('withdrawal-full-collapse',['F'],w['autonomy_full']['greatest']==[] and not w['autonomy_full']['gates']['resource_closure'] and
        all(not w['autonomy_full']['withdrawn_clauses'][c]['pass'] for c in ('C6','C8')),
        {'SF':w['autonomy_full']['greatest'],'withdrawn_C6_C8':{c:w['autonomy_full']['withdrawn_clauses'][c]['pass'] for c in ('C6','C8')}},
        'Retention did not reject continuing full package/resource/response closure.')
    add('withdrawal-operational-collapse',['O'],w['autonomy_operational']['greatest']==[] and w['autonomy_operational']['effective_ledger']['recharge']==0,
        w['autonomy_operational']['effective_ledger'],'Continuing funded operational invariant survived removal of essential recharge.')
    return records


def prediction_meanings():
    text=(ROOT/'audit/G6_predictions.md').read_text(); version=None; out={}
    for line in text.splitlines():
        if line.startswith('## Version F'):version='F'
        if line.startswith('## Version O'):version='O'
        if line.startswith('| ') and version:
            row=[v.strip() for v in line.strip('|').split('|')]
            if len(row)==4 and row[0] in ('Baseline','G6-PACKAGE-ONLY','G6-LINEAGE-ONLY','G6-WITHDRAWAL-ONLY'):
                out[(version,row[0],row[1])]=row[3]
    return out


def coverage_index():
    checks={
        'P': ('package', 'total typed map, value preservation, star cover/dependencies, edge compatibility, completeness, restrictions, coordinate views'),
        'P.C1-C8': ('clause', 'assignment-scope completeness, row validity, reconstructed C1 audit, C2/C3 raw M and profiles, C4/C5/C7 surrogate checks, C6 and C8'),
        'P.C6.trace': ('trace_check', 'strict events on realized supported paths, unit ticks, funding, writer and owner'),
        'P.C6.future': ('full_future', 'defined raw-class probabilities/updater, full eight-component observation, finite one-step bisimulation and exact abstract closure with symbolic unbounded count'),
        'L.atomic': ('lineage', 'actual event support expansion, realized stages, fixed audit vertices, reachability and both intervention projections, strict readout updates'),
        'L.bridge': ('lineage', 'nonempty supported frontier and strict edge; different pasts; representative descent; raw successor, order/tick/progress/record/route/maintenance/owner equations; all four G1c snapshot pairs (afterFirst and endpoint on both routes), eight exact finite-image codecs and occurrence-wise coordinate-map checks'),
        'L.endpoint': ('lineage', 'typed source/target terminal and last realized target exit event, receiver activation, raw class map'),
        'L.route': ('routes', 'nonempty raw tuple comparison domain, shared endpoint, activated realized funded step, resulting register and interpreted raw future-readout rule/owner'),
        'AF/AO.entry': ('phase2_path_check', 'arrival activation, complete realized strict supported route; only the executed funded row yields entries'),
        'L.readout': ('route_readout', 'declared first/last phase selector and target ownership, applied to resulting register'),
        'AF/AO.response': ('autonomy', 'EVERY invariant state/route context/nominal disturbance, EXIST owned action, EVERY positive successor inside; exact positive conserved ledger and advancement'),
        'AF.packageInside': ('autonomy', 'BW withdrawn resources, recomputed assigned package, all state-view references, run laws; package-filtered greatest fixed point'),
        'AO.viability': ('autonomy', 'same withdrawn inputs, operational C8 greatest set without P/C1-C7 acceptance'),
        'AF/AO.greatest': ('greatest', 'descending fixed point and independent all-subset containment check; support monotonicity argument'),
        'AF/AO.support': ('safe_actions', 'nonempty exact stochastic row, scaled-integral positive mass and ALL successors inside'),
        'AF/AO.run': ('run_laws', 'positive conserved unit budget, writer, tick, owner; defined affine readouts and persistent register'),
        'wellformed': ('wellformed', 'raw syntax/references/stochastic rows, permitted typed absence distinct from package completeness'),
    }
    return {name: {'implementation': 'scripts/evaluate_tth06_lanes.py:'+str(inspect.getsourcelines(globals()[fn])[1]),
                   'checks': text} for name,(fn,text) in checks.items()}


def run(path,with_selftest=True):
    model=load(path); declaration=model['declaration']; original=Path(path).read_bytes()
    models={'Baseline':model}; results={'Baseline':evaluate(model)}
    for control in declaration['controls']:
        mutated=mutate(model,control);models[control['id']]=mutated;results[control['id']]=evaluate(mutated)
    meanings=prediction_meanings(); rows=[]; controls={}; counts={}; clean={}
    for version,aut in [('F','autonomy_full'),('O','autonomy_operational')]:
        for name,result in results.items():
            expected=(declaration['baseline_expected_lanes_by_version'][version] if name=='Baseline' else
                      next(c for c in declaration['controls'] if c['id']==name)['expected_lanes_by_version'][version])
            actual=result['lane_vectors'][version]
            isolation=name!='Baseline' and not(version=='F' and name=='G6-PACKAGE-ONLY')
            baseline=all(results['Baseline']['lane_vectors'][version].values())
            vector_hit=actual==expected
            if not result['wellformed']['pass']:status='INVALID-CONTROL'
            elif isolation and baseline and any(not actual[k] and not want for k,want in expected.items()) and any(want and not actual[k] for k,want in expected.items()):status='CONFIRMED-CONFOUNDED'
            elif not vector_hit:status='FAILED'
            elif name!='Baseline' and not baseline:status='CONFIRMED-NARROW'
            else:status='CONFIRMED'
            controls[(version,name)]={'status':status,'clean_isolation':isolation and baseline and vector_hit and result['wellformed']['pass'],
                                      'expected':expected,'observed':actual,'interpretation':'dependence consequence, not isolation' if version=='F' and name=='G6-PACKAGE-ONLY' else 'isolation' if isolation else 'positive satisfiability'}
            for pred,want in expected.items():
                got=actual[pred]; label={'package':'P','lineage':'L','autonomy_full':'AF','autonomy_operational':'AO'}[pred]
                scalar='CONFIRMED' if got==want else 'FAILED'
                if name!='Baseline' and got==want and not want:
                    if not result['wellformed']['pass']:scalar='INVALID-CONTROL'
                    elif not baseline:scalar='CONFIRMED-NARROW'
                    elif isolation and not vector_hit:scalar='CONFIRMED-CONFOUNDED'
                rows.append({'version':version,'case':name,'predicate':label,'expected':want,'observed':got,'status':scalar,
                             'failure_meaning':meanings[(version,name,label)]})
        counts[version]={category:sum(r['status']==category for r in rows if r['version']==version) for category in CATEGORIES}
        clean[version]=sum(v['clean_isolation'] for (ver,_),v in controls.items() if ver==version)
    implication=all(r['AF_implies_P_instance'] for r in results.values())
    theorem={'id':'AF-IMPLIES-P','status':'CONFIRMED' if implication else 'FAILED',
             'family_checks':{c:r['AF_implies_P_instance'] for c,r in results.items()},
             'generic_argument':'For arbitrary raw m: AF requires a nonempty entry set E ⊆ SF and packageInside. Choose e in E. PackageAt(m,e) includes P(m), hence P(m). This is a direct logical implication under the fixed definitions, not a finite-family inference or a Lean proof.',
             'proof_structural_disclosure':'P is independently evaluated by map/gluing and assigned clauses; it is not filled from AF.'}
    counts['F'][theorem['status']]+=1
    selftest={'status':'NOT-RUN','probes':[]}
    if with_selftest:
        try:
            from selftest_evaluate_tth06_lanes import run_selftests
            selftest=run_selftests(model)
        except Exception as error:
            selftest={'status':'ERROR','probes':[],'error':f'{type(error).__name__}: {error}'}
    assert Path(path).read_bytes()==original
    receipt={r['path']:hashlib.sha256((ROOT/r['path']).read_bytes()).hexdigest() for r in declaration['provenance']}
    return encode({'model_id':declaration['model_id'],'spec':'audit/G6_lane_spec.md','predictions':'audit/G6_predictions.md',
        'frozen_hashes':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
                         ['audit/G6_lane_spec.md','audit/G6_predictions.md',str(Path(path).relative_to(ROOT)) if Path(path).is_absolute() else str(path)]},
        'provenance_hashes_match':all(receipt[r['path']]==r['sha256'] for r in declaration['provenance']),
        'counts_primary':counts,'clean_isolation_count':clean,'predictions':rows,
        'control_vectors':{v:{c:controls[(v,c)] for c in results} for v in ('F','O')},
        'full_autonomy_satisfiable':results['Baseline']['autonomy_full']['pass'],
        'AF_implies_P':theorem,'secondary_predictions':secondary_predictions(models,results),
        'cases':results,'ambiguities':AMBIGUITIES,'selftest':selftest,
        'coverage':coverage_index(),'ceiling':declaration['claim_ceiling']} )


def render_md(r):
    lines=['# G6b — TTH-06 lane controls, F and O','',
           'Exact standard-library computation on the frozen G6a declaration. F is primary full preservation of the declared graded package; O is supplementary C8 operational autonomy (N3). C4–C7 remain surrogates; the disturbance domain is only nominal. No physical or P05/T17-I claim.','',
           '## Counts and satisfiability','',
           '| Version | CONFIRMED | CONFIRMED-NARROW | CONFIRMED-CONFOUNDED | FAILED | INVALID-CONTROL | UNDETERMINED | Clean isolations |',
           '|---|---|---|---|---|---|---|---|']
    for v in ('F','O'):
        lines.append('| '+v+' | '+' | '.join(str(r['counts_primary'][v][c]) for c in CATEGORIES)+f" | {r['clean_isolation_count'][v]} |")
    lines+=['','Primary counts: twelve individual lane predictions per version, plus the separately disclosed AF→P prediction for F. Secondary predictions are listed and counted separately below. Expected P/AF joint rejection is not an F isolation or confounding. Qualified negative statuses are excluded from clean counts.','',
            f"F positive satisfiability: **{r['full_autonomy_satisfiable']}**. AF→P: **{r['AF_implies_P']['status']}**.",'',r['AF_implies_P']['generic_argument'],'',
            '## All primary predictions','', '| Version | Case | Lane | Predicted | Computed | Outcome |','|---|---|---|---|---|---|']
    for row in r['predictions']:
        lines.append(f"| {row['version']} | {row['case']} | {row['predicate']} | {row['expected']} | {row['observed']} | {row['status']} |")
    lines+=['','## Isolation vectors','', '| Version | Control | Computed (P,L,A) | Interpretation | Status | Clean isolation |','|---|---|---|---|---|']
    for v,controls in r['control_vectors'].items():
        for name,x in controls.items():
            lines.append(f"| {v} | {name} | {tuple(x['observed'].values())} | {x['interpretation']} | {x['status']} | {x['clean_isolation']} |")
    lines+=['','## Secondary predictions','',f"Counts: {dict(Counter(x['status'] for x in r['secondary_predictions']))}.",'',
            '| Prediction | Versions | Outcome | Computed witness |','|---|---|---|---|']
    for x in r['secondary_predictions']:
        witness=json.dumps(x['witness'],sort_keys=True) if isinstance(x['witness'],(dict,list)) else str(x['witness'])
        lines.append(f"| {x['id']} | {','.join(x['versions'])} | {x['status']} | `{witness.replace('|','/').replace(chr(10),' ')}` |")
    lines+=['','## Computed invariants, packageInside, responses and entry','']
    for name,case in r['cases'].items():
        lines += [f'### {name}','',f"Well-formedness: {case['wellformed']}.", '']
        for v,aut in [('F','autonomy_full'),('O','autonomy_operational')]:
            a=case[aut]
            lines += [f"**{v}:** greatest set `{a.get('greatest')}`; pruning `{a.get('pruning')}`; exact effective ledger `{a.get('effective_ledger')}`.",
                      f"Gates: `{a['gates']}`.",
                      f"Responses (state → raw route context → nominal → admissible target-owned actions): `{a.get('responses')}`.",'']
            if v=='F':lines += [f"packageInside state checks: `{a.get('packageAt')}`.",'']
        lines += [f"Both route entries after the actual canonical target step: `{case['autonomy_full'].get('entry_states')}`.", '',
                  f"Atomic audit gates: `{case['lineage'].get('atomic',{}).get('gates')}`.",
                  f"Bridge laws: `{case['lineage'].get('bridge',{}).get('gates')}`.",'']
    lines += ['## Declared check coverage','', '| Check | Implementing function line | Conditions checked |','|---|---|---|']
    for name,cov in r['coverage'].items():lines.append(f"| {name} | `{cov['implementation']}` | {cov['checks']} |")
    lines += ['', '## Failures, qualifications and scientific meaning','']
    failures=[x for x in r['predictions']+r['secondary_predictions'] if x['status']!='CONFIRMED']
    if not failures:lines+=['No failed, narrow, confounded, invalid or undetermined prediction.','']
    for x in failures:lines += [f"- {x.get('version',x.get('versions'))} {x.get('case',x.get('id'))} {x.get('predicate','')}: {x['status']}. {x['failure_meaning']}"]
    lines+=['F package deletion is expected dependence, not isolation: missing shared publishedC rejects source/target C1 completeness and map totality. It deletes evidence, not T1 dynamics. Withdrawal leaves the arrival package and pre-exit lineage fixed; continuing conserved positive funding fails, even though one prepaid action may be possible.','',
            '## Fixed-point and unbounded-word arguments','',
            'Descending pruning from K stabilizes because K is finite. Retention is monotone: adding allowed states cannot remove a support-safe response. State package validity and resource/ledger conditions do not depend on S. Every viable subset is retained through each iteration; the stabilized set is a fixed point and the greatest viable set. The evaluator additionally checks containment of all 1024 subsets, independently of the chosen number of prune rounds.','',
            'Full future sufficiency is a finite one-step weighted bisimulation on actual predictive classes, including exit classes and assigned tick increments. Code equality fixes the unbounded counter, tick phase, raw register, funding and owner. The defined observer and affine updater preserve this equality; induction gives equality of full eight-component word laws for every finite word, on all run states (hence the closure). No bounded horizon is used. Record and budget advancement follow the positive unit ledger and available writer; every supported response has all its successors in the invariant.','',
            'The source/target raw coordinate receiver and the designed route readout retain their pre-registration near-automatic disclosure. This evaluation does not upgrade those surrogates.','',
            '## Corrected declared-domain and phase checks','',
            'All four frozen G1c snapshot pairs are checked: route_a/route_b at afterFirst (occurrence 1, mix_1) and endpoint (occurrence 2, mix_2). Intermediate receiver-map coherence is required, in addition to all eight snapshot codec/transport equations; no terminal-only snapshot restriction remains.','',
            'Phase-2 entries exist only for an activated, realized, supported arrival route and an available actual funded target step. Arrival activation is independently gated in both AF and AO. A hypothetical receiver output without activation contributes no entries. Route readouts interpret the declared raw first/last selector and owner on the resulting register; unknown selectors are rejected.','',
            '## Ambiguity log','']
    lines += [f"- **{x['id']}** {x['text']}" for x in r['ambiguities']]
    lines+=['','## Gate-sensitivity self-test','',f"Separate self-test status: **{r['selftest']['status']}**. These are group sensitivity probes, not exhaustive isolation of all obligations. Self-test failure never suppresses prediction reporting.",'',
            '| Check | In-memory perturbation | Outcome |','|---|---|---|']
    for p in r['selftest']['probes']:lines.append(f"| {p['check']} | {p['perturbation']} | {p['result']} |")
    focused=[p for p in r['selftest']['probes'] if 'witness' in p]
    if focused:
        lines+=['','Corrected-check witnesses:','']
        for p in focused:lines.append(f"- **{p['check']}**: `{p['witness']}`.")
    if r['selftest'].get('error'):lines+=['',r['selftest']['error']]
    lines+=['','## Reproduce','', '```bash',
            'python3 -B scripts/evaluate_tth06_lanes.py audit/proposed_models/TTH06-LANES.model.json',
            'python3 -B scripts/selftest_evaluate_tth06_lanes.py',
            'python3 -B scripts/evaluate_tth06_lanes.py audit/proposed_models/TTH06-LANES.model.json --check-repeat',
            '```','',
            'The repeat guard reruns the entire evaluation and self-test and compares JSON and Markdown bytes. No timestamp or process-dependent ordering is emitted. Frozen declarations and POS-04 files are read only.','',
            '## Supported ceiling','',r['ceiling'],'',
            'When confirmed, F supports satisfiability of graded packageInside and nominal-environment target-owned, probability-one-safe controlled responses, with separate package/lineage derivations and disclosed AF→P dependence. O supplies the three logical independence witnesses only for the narrower operational predicates. These are exact Python results pending G6c kernel proofs; no registry status is changed.','']
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model',nargs='?',default='audit/proposed_models/TTH06-LANES.model.json')
    parser.add_argument('--output-json',default='audit/G6b_results.json')
    parser.add_argument('--output-md',default='audit/G6b_results.md')
    parser.add_argument('--check-repeat',action='store_true')
    args=parser.parse_args(); r=run(args.model)
    js=json.dumps(r,indent=2,sort_keys=True)+'\n'; md=render_md(r)
    if args.check_repeat:
        again=run(args.model)
        assert json.dumps(again,indent=2,sort_keys=True)+'\n'==js
        assert render_md(again)==md
        for path,content in [(args.output_json,js),(args.output_md,md)]:
            if Path(path).exists():assert Path(path).read_bytes()==content.encode(),path
        print('PASS: byte-identical JSON and Markdown re-run (including independent self-test status).')
    Path(args.output_json).write_text(js);Path(args.output_md).write_text(md)
    print('Primary prediction counts:',r['counts_primary'])
    print('Clean isolations:',r['clean_isolation_count'])
    print('Secondary predictions:',dict(Counter(x['status'] for x in r['secondary_predictions'])))
    print('F satisfiable:',r['full_autonomy_satisfiable'],'AF→P:',r['AF_implies_P']['status'])
    print('Self-test:',r['selftest']['status'])

if __name__=='__main__':main()
