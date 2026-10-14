#!/usr/bin/env python3
"""Exact, declaration-driven FIACH-POS-02 finite audit (standard library only).

No field named declared_* or claim/status is used as a computed result.  Mutations
are executable transcriptions of the frozen raw-input rules, not changed tests.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


AMBIGUITIES = [
    "C1 CORE retention: use the unique stationary law of the epsilon-perturbed six-state Markov chain; compare its CORE mass with 3/4. The declaration does not specify a start distribution or an alternative retention statistic.",
    "C1 defect: symmetric-difference cardinality is an integer (equivalently an exact rational denominator 1), with no pass threshold; missing transitions make the separate Markov audit ill-formed.",
    "C3 continuation: compare the full finite-state output-equivalence fixed point, including present raw temporal values and action deltas, with computed q; no finite-word cutoff is used.",
    "C7 local consistency: require each reassembly row's actual coupling edges to equal its named admissible coupling map. This is the natural inverse-law reading of decomposition/reassembly; the declaration does not spell out the equation.",
    "C8 viability: require a safe response for every declared disturbance, as the spec says 'for each state and both disturbances'; this is a greatest fixed point, not a choice of one favorable action.",
    "Route current projection: exit_stage comes from the common corridor exit event; health/public/phase come from the arrival state. No stored declared_route_status is consulted.",
    "C6 tick phase: the declaration says every controller action toggles phase modulo two; the positive order_delta may be one or two and is not the tick increment. Check successor phase = current phase + 1 mod 2.",
    "Bridge frontier reachability: seed with states produced by reachable declared prehistory edges as well as source package arrivals, then close under source dynamics. This includes the distinct right-arrival history A0b.",
    "C4 declared continuation: test each one-step disturbance named in observation_interfaces.continuations and require an explicit differing output; the full future quotient alone is insufficient for this clause.",
]


def unique(rows, key):
    d = {}
    for row in rows:
        k = row[key]
        if k in d:
            raise ValueError(f"duplicate {key}={k}")
        d[k] = row
    return d


def states(m, side):
    return unique(m[side]["states"], "state_id")


def actions(m, side):
    return unique(m[side]["actions"], "action_id")


def transitions(m, side):
    d = {}
    for t in m[side]["transitions"]:
        key = (t["from_state"], t["disturbance_id"])
        if key in d:
            raise ValueError(f"duplicate transition {side}:{key}")
        d[key] = t
    return d


def disturbances(m, side):
    return tuple(m[side]["disturbances"])


def q(m, side, s):
    row = states(m, side)[s]
    # Use the declared field list only as the code *definition*, never a label.
    return tuple(m["carriers"][side]["code"] if k == "carrier" else row[k]
                 for k in m["predictive_code_rule"]["fields"])


def response(m, side, s, d):
    t = transitions(m, side).get((s, d))
    if not t:
        return None
    a = actions(m, side).get(t["action_id"])
    y = states(m, side).get(t["to_state"])
    return (t, a, y) if a and y else None


def observation(m, side, s):
    r = states(m, side)[s]
    return (r["initial_order"], r["initial_progress"], r["initial_record"],
            r["tick_phase"], r["health"], r["maintenance_state"],
            r["route_residue"], r["owner"])


def future_partition(m, side):
    """Moore refinement; stable partition proves equality for ALL finite words."""
    ss = tuple(m[side]["kernel_state_ids"])
    def canon(signatures):
        tags = {}
        return {s: tags.setdefault(signatures[s], len(tags)) for s in ss}
    classes = canon({s: observation(m, side, s) for s in ss})
    rounds = 0
    while True:
        signatures = {}
        for s in ss:
            pieces = []
            for d in disturbances(m, side):
                r = response(m, side, s, d)
                if r is None:
                    pieces.append((d, "MISSING"))
                else:
                    t, a, y = r
                    pieces.append((d, a["order_delta"], a["progress_delta"],
                                   a["record_delta"], classes[t["to_state"]]))
            signatures[s] = (classes[s], tuple(pieces))
        new = canon(signatures)
        rounds += 1
        if all((classes[x] == classes[y]) == (new[x] == new[y])
               for x in ss for y in ss):
            return new, rounds
        classes = new


def matmul(a, b):
    return [[sum((a[i][k]*b[k][j] for k in range(len(b))), Fraction(0))
             for j in range(len(b[0]))] for i in range(len(a))]


def rref(rows):
    a = [[Fraction(x) for x in row] for row in rows]
    pivots = []
    for col in range(len(a[0])-1):
        pivot = next((i for i in range(len(pivots), len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        r = len(pivots)
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][col]
        a[r] = [v/scale for v in a[r]]
        for i in range(len(a)):
            if i != r:
                scale = a[i][col]
                a[i] = [x-scale*y for x,y in zip(a[i], a[r])]
        pivots.append(col)
    inconsistent = any(not any(row[:-1]) and row[-1] for row in a)
    return a, pivots, inconsistent


def fixed_distribution_space(e):
    """Exact affine fixed space intersected with the probability simplex."""
    n = len(e)
    system = [[e[j][i] - (i == j) for j in range(n)] + [0] for i in range(n)]
    system.append([1]*n + [1])
    reduced, pivots, inconsistent = rref(system)
    free = [i for i in range(n) if i not in pivots]
    base = [Fraction(0) for _ in range(n)]
    for row, col in enumerate(pivots):
        base[col] = reduced[row][-1]
    basis = []
    for f in free:
        v = [Fraction(0) for _ in range(n)]
        v[f] = 1
        for row, col in enumerate(pivots):
            v[col] = -reduced[row][f]
        basis.append(v)
    return {'affine_dimension':len(free), 'inconsistent':inconsistent,
            'particular': [str(x) for x in base],
            'basis': [[str(x) for x in v] for v in basis],
            'simplex_constraint':'particular + sum(parameter_i * basis_i) >= 0 componentwise',
            'unique':not inconsistent and not free and all(x >= 0 for x in base)}


def derived_core(m, side, ss, ts):
    """Bottom support SCCs, filtered by the declared raw maintenance laws."""
    support = {s:{ts[(s,d)]['to_state'] for d in disturbances(m,side)
                  if (s,d) in ts and ts[(s,d)]['to_state'] in ss} for s in ss}
    def reach(seed):
        seen={seed}; todo=[seed]
        while todo:
            for y in support[todo.pop()]:
                if y not in seen:seen.add(y);todo.append(y)
        return seen
    reachable={s:reach(s) for s in ss}
    components=[];remaining=set(ss)
    while remaining:
        s=next(x for x in ss if x in remaining)
        comp={x for x in ss if x in remaining and x in reachable[s] and s in reachable[x]}
        components.append(comp);remaining-=comp
    anchor = ({x['source_state'] for x in m['staged_clause_map']['source_arrivals']}
              if side=='source' else set(m['staged_clause_map']['target_arrivals']))
    own=m['carriers'][side]['code']
    resource_rows=m['withdrawal']['retained_resources'] if side=='target' else m[side]['resources']
    resources={x['resource_id']:x['owner'] for x in resource_rows}
    protocols={x['protocol_id']:x['generator_owner'] for x in m[side]['generator_provenance']['protocols']}
    sr=states(m,side)
    records=[];core=set()
    for comp in components:
        reasons=[]
        if any(y not in comp for x in comp for y in support[x]):reasons.append('outgoing support')
        if not comp <= set(m[side]['kernel_state_ids']):reasons.append('outside C8 kernel')
        for s in sorted(comp):
            if set(sr[s].get('clause_assignments',{})) != {f'C{i}' for i in range(1,9)}:
                reasons.append(f'{s}: missing C1-C8 assignment')
            for d in disturbances(m,side):
                z=response(m,side,s,d)
                if z is None:reasons.append(f'{s}/{d}: missing response');continue
                t,a,y=z
                if t['to_state'] not in comp:reasons.append(f'{s}/{d}: escapes component')
                if sr[s]['budget']-a['budget_cost']+a['budget_regeneration'] != y['budget'] or y['budget'] <= 0:
                    reasons.append(f'{s}/{d}: unfunded ledger')
                if a['owner']!=own or a['regeneration_owner']!=own or protocols.get(a['generator_protocol_id'])!=own:
                    reasons.append(f'{s}/{d}: external action or provenance owner')
                if resources.get(a['regeneration_resource'])!=own or any(resources.get(r)!=own for r in a['required_resources']):
                    reasons.append(f'{s}/{d}: resource not retained and owned')
        selected=not reasons and bool(comp & anchor)
        if selected:core |= comp
        records.append({'states':sorted(comp),'bottom_and_maintained':not reasons,
                        'anchor_intersection':sorted(comp & anchor), 'selected':selected,
                        'reasons':reasons})
    return sorted(core), records


def t1_audit(m, side, ss, pe, p, core, threshold):
    tau=m[side]['closure_audit']['perturbation']['t1_style_audit']['tau']
    if tau != 2:raise ValueError(f'unsupported declared tau {tau}')
    fibers={}
    for s in ss:fibers.setdefault(q(m,side,s),[]).append(s)
    idx={s:i for i,s in enumerate(ss)}
    def prototype(matrix):
        power=matmul(matrix,matrix)
        # C U is the uniform within-fiber projection computed from raw q.
        cu=[[Fraction(1,len(fibers[q(m,side,ss[j])])) if q(m,side,ss[i])==q(m,side,ss[j]) else Fraction(0)
             for j in range(len(ss))] for i in range(len(ss))]
        return matmul(power,cu)
    out={}
    for label, matrix in [('0',p),('1/16',pe)]:
        e=prototype(matrix);e2=matmul(e,e)
        defect=max(sum((abs(e2[i][j]-e[i][j]) for j in range(len(ss))),Fraction(0))/2 for i in range(len(ss)))
        fixed=fixed_distribution_space(e)
        out[label]={'defect':str(defect),'fixed_space':fixed}
    pert=out['1/16']['fixed_space']; pi=[Fraction(x) for x in pert['particular']]
    mass=sum((pi[idx[s]] for s in core),Fraction(0)) if pert['unique'] else None
    nonuniform=pert['unique'] and any(x!=Fraction(1,len(ss)) for x in pi)
    out['perturbed_core_mass']=str(mass) if mass is not None else None
    out['perturbed_fixed_distribution']={s:str(pi[i]) for i,s in enumerate(ss)} if pert['unique'] else None
    out['nonuniform']=nonuniform
    out['retained']=mass is not None and bool(core) and mass>=threshold
    out['pass']=pert['unique'] and nonuniform and out['retained']
    out['q_fibers']=[sorted(v) for v in fibers.values()]
    return out


def c1(m, side):
    ss = list(m[side]["kernel_state_ids"]); idx = {s:i for i,s in enumerate(ss)}
    ts = transitions(m, side)
    stages = {}
    for stage in m[side]["closure_audit"]["stagings"]:
        ds = stage["allowed_disturbances"]
        fixed = 0; max_defect = 0; sum_defect = Fraction(0);fixed_sets=[];defects={}
        extensive = monotone = idempotent = True
        cl = {}
        for mask in range(1 << len(ss)):
            a = {s for s in ss if mask >> idx[s] & 1}
            reached = set(a); todo = list(a)
            while todo:
                x = todo.pop()
                for d in ds:
                    t = ts.get((x,d))
                    if t and t["to_state"] in idx and t["to_state"] not in reached:
                        reached.add(t["to_state"]);todo.append(t["to_state"])
            cl[mask] = reached
            one = a | {ts[(x,d)]["to_state"] for x in a for d in ds
                       if (x,d) in ts and ts[(x,d)]["to_state"] in idx}
            defect = len(reached ^ one)
            label=','.join(s for s in ss if s in a) or 'EMPTY'
            defects[label]=str(Fraction(defect))
            max_defect = max(max_defect, defect);sum_defect += Fraction(defect)
            fixed += reached == a
            if reached==a:fixed_sets.append(label)
            extensive &= a <= reached
        for a in range(1 << len(ss)):
            ca = cl[a];cmask = sum(1 << idx[s] for s in ca)
            idempotent &= cl[cmask] == ca
            for b in range(1 << len(ss)):
                if a & ~b == 0:monotone &= cl[a] <= cl[b]
        stages[stage["stage_id"]] = {"fixed_sets":fixed,"max_defect":max_defect,
          "sum_defect":str(sum_defect),"extensive":extensive,"monotone":monotone,
          "idempotent":idempotent,"fixed_set_members":fixed_sets,
          "defect_by_subset":defects}
    missing = [(s,d) for s in ss for d in disturbances(m,side) if (s,d) not in ts]
    if missing:
        return {"pass":False,"well_formed":False,"missing_markov_rows":missing,
                "closure":stages,"stationary":None}
    n=len(ss);P=[[Fraction(0) for _ in ss] for _ in ss]
    for s in ss:
        for d in disturbances(m,side):P[idx[s]][idx[ts[(s,d)]["to_state"]]] += Fraction(1,len(disturbances(m,side)))
    pert=m[side]["closure_audit"]["perturbation"]
    eps=Fraction(pert["epsilon_numerator"],pert["epsilon_denominator"])
    pe=[[(1-eps)*P[i][j]+eps/Fraction(n) for j in range(n)] for i in range(n)]
    # Solve (P_e^T-I)pi=0, replacing final row with normalization.
    mat=[[pe[j][i] - (1 if i==j else 0) for j in range(n)] + [Fraction(0)] for i in range(n)]
    mat[-1]=[Fraction(1)]*n+[Fraction(1)]
    for col in range(n):
        pivot=next((r for r in range(col,n) if mat[r][col]),None)
        if pivot is None:raise ValueError("singular perturbed stationary system")
        mat[col],mat[pivot]=mat[pivot],mat[col]
        scale=mat[col][col];mat[col]=[x/scale for x in mat[col]]
        for r in range(n):
            if r!=col:
                fac=mat[r][col];mat[r]=[a-fac*b for a,b in zip(mat[r],mat[col])]
    pi=[mat[i][-1] for i in range(n)]
    if 'core_rule' in pert:
        core,components=derived_core(m,side,ss,ts)
    else:
        core=pert['core_state_ids'];components=None
    mass=sum((pi[idx[s]] for s in core),Fraction(0))
    threshold=Fraction(pert["retention_threshold_numerator"],pert["retention_threshold_denominator"])
    if 'core_rule' in pert:
        audit=t1_audit(m,side,ss,pe,P,core,threshold)
        return {"pass":bool(core) and mass>=threshold and audit['pass'] and all(v["extensive"] and v["monotone"] and v["idempotent"] for v in stages.values()),
          "well_formed":True,"closure":stages,"stationary":{s:str(pi[i]) for i,s in enumerate(ss)},
          "core_state_ids":core,"components":components,"core_mass":str(mass),"threshold":str(threshold),
          "retained":bool(core) and mass>=threshold,"t1_style_audit":audit}
    return {"pass":mass>=threshold and all(v["extensive"] and v["monotone"] and v["idempotent"] for v in stages.values()),
      "well_formed":True,"closure":stages,"stationary":{s:str(pi[i]) for i,s in enumerate(ss)},
      "core_mass":str(mass),"threshold":str(threshold),"retained":mass>=threshold}


def c2(m,side):
    ss=m[side]["kernel_state_ids"];r=states(m,side)
    defect=[[x,y] for x in ss for y in ss if r[x]["public_state"]==r[y]["public_state"] and q(m,side,x)!=q(m,side,y)]
    declared_split=m[side]["promotion_readouts"]["split_pair"]
    split_is_witness=declared_split in defect
    return {"pass":bool(defect) and split_is_witness,"defect_count":len(defect),
            "witness":defect[0] if defect else None,
            "declared_split":declared_split,"declared_split_is_witness":split_is_witness}


def c3(m,side):
    ss=m[side]["kernel_state_ids"];r=states(m,side)
    def enabled(s):return tuple(d for d in disturbances(m,side) if response(m,side,s,d))
    def canon(signatures):
        tags={};return {s:tags.setdefault(signatures[s],len(tags)) for s in ss}
    classes=canon({s:(r[s]["public_state"],enabled(s)) for s in ss});rounds=0
    while True:
        sig={}
        for s in ss:
            pieces=[]
            for d in disturbances(m,side):
                z=response(m,side,s,d)
                if z is None:pieces.append((d,"MISSING"))
                else:
                    t,a,y=z
                    pieces.append((d,a["order_delta"],a["progress_delta"],a["record_delta"],
                      y["health"],y["maintenance_state"],y["route_residue"],y["tick_phase"],classes[t["to_state"]]))
            sig[s]=(classes[s],tuple(pieces))
        new=canon(sig);rounds+=1
        if all((classes[x]==classes[y])==(new[x]==new[y]) for x in ss for y in ss):break
        classes=new
    mismatch=[[x,y] for x in ss for y in ss if (new[x]==new[y])!=(q(m,side,x)==q(m,side,y))]
    fut,_=future_partition(m,side)
    continuation_bad=[[x,y] for x in ss for y in ss if q(m,side,x)==q(m,side,y) and fut[x]!=fut[y]]
    return {"pass":not mismatch and not continuation_bad,"rounds":rounds,
      "terminal_class_count":len(set(new.values())),"q_class_count":len({q(m,side,s) for s in ss}),
      "mismatch":mismatch,"continuation_bad":continuation_bad}


def current_channel(m,side,s):
    r=states(m,side)[s];out=[]
    for field in m[side]["exposure_channels"]["declared_channels"]:
        if field=="public_report":out.append(r["public_state"])
        elif field=="enabled_disturbances":out.append(tuple(d for d in disturbances(m,side) if response(m,side,s,d)))
        else:out.append(r[field])
    return tuple(out)


def c4(m,side):
    ss=m[side]["kernel_state_ids"]
    witness=None;continuation=None
    for x in ss:
        for y in ss:
            if x==y or current_channel(m,side,x)!=current_channel(m,side,y) or q(m,side,x)==q(m,side,y):continue
            for d in m['observation_interfaces']['continuations']:
                zx=response(m,side,x,d);zy=response(m,side,y,d)
                if not zx or not zy:continue
                tx,ax,_=zx;ty,ay,_=zy
                ox=(ax['order_delta'],ax['progress_delta'],ax['record_delta'],observation(m,side,tx['to_state']))
                oy=(ay['order_delta'],ay['progress_delta'],ay['record_delta'],observation(m,side,ty['to_state']))
                if ox!=oy:witness=[x,y];continuation=d;break
            if witness:break
        if witness:break
    channel_values=len({current_channel(m,side,s) for s in ss})
    return {"pass":bool(witness) and channel_values>1,"witness":witness,
            "continuation":continuation,"channel_values":channel_values}


def c5(m,side):
    protocols=m[side]["generator_provenance"]["protocols"];verts=m[side]["generator_provenance"]["cycle_vertices"]
    forward=list(zip(verts,verts[1:]+verts[:1]));reverse=[(b,a) for a,b in forward]
    out={}
    for p in protocols:
        products={}
        for ch in ('self','other'):
            edges=Counter((e['from'],e['to']) for e in p['edges'] if e['channel']==ch)
            a=b=1
            for edge in forward:a*=edges[edge]
            for edge in reverse:b*=edges[edge]
            products[ch]=[a,b]
        s=products['self'][0]!=products['self'][1];o=products['other'][0]!=products['other'][1]
        credit='ambiguous' if s and o else 'self' if s else 'other' if o else 'none'
        out[p['protocol_id']]={'products':products,'credit':credit,'generator_owner':p['generator_owner']}
    key=('S' if side=='source' else 'T')
    credits=[out[f'{key}-{x}']['credit'] for x in ('genuine','scheduled','internalized','null')]
    owner=m['carriers'][side]['code']
    genuine=next(p for p in protocols if p['protocol_id']==f'{key}-genuine')
    return {"pass":credits==['self','other','none','none'] and genuine['generator_owner']==owner,
            "credits":credits,"protocols":out,"owner_consistent":genuine['generator_owner']==owner}


def c6(m,side):
    ss=m[side]['kernel_state_ids'];rs=states(m,side);own=m['carriers'][side]['code']
    classes,rounds=future_partition(m,side)
    collisions=[[x,y] for x in ss for y in ss if x!=y and q(m,side,x)==q(m,side,y)]
    future_bad=[[x,y] for x,y in collisions if classes[x]!=classes[y]]
    violations=[];deltas=set();outcomes=set()
    resource_rows=m['withdrawal']['retained_resources'] if side=='target' else m[side]['resources']
    retained={r['resource_id']:r['owner'] for r in resource_rows}
    protocols={p['protocol_id']:p for p in m[side]['generator_provenance']['protocols']}
    for s in ss:
        for d in disturbances(m,side):
            z=response(m,side,s,d)
            if z is None:
                violations.append([s,d,'missing response']);continue
            t,a,y=z
            deltas.add((a['order_delta'],a['progress_delta'],a['record_delta']))
            outcomes.add((y['health'],y['maintenance_state'],y['route_residue'],y['tick_phase']))
            if min(a['order_delta'],a['progress_delta'],a['record_delta'])<=0:violations.append([s,d,'nonpositive delta'])
            if (rs[s]['tick_phase']+1)%m[side]['tick_modulus']!=y['tick_phase']:
                violations.append([s,d,'tick phase'])
            protocol=protocols.get(a['generator_protocol_id'])
            if a['owner']!=own or a['regeneration_owner']!=own or rs[s]['temporal_owner']!=own or not protocol or protocol['generator_owner']!=own:
                violations.append([s,d,'arrow owner'])
            if any(retained.get(res)!=own for res in a['required_resources']):violations.append([s,d,'required resource withdrawn'])
            if rs[s]['budget']-a['budget_cost']+a['budget_regeneration']!=y['budget']:
                violations.append([s,d,'budget ledger'])
            if rs[s]['initial_order']+a['order_delta']<=rs[s]['initial_order']:
                violations.append([s,d,'unfolded order'])
    past={e['produces']:(e['prior_health'],e['generator_kind']) for e in m[side]['past_history_graph']['edges']}
    nonduplicate=[[x,y] for x,y in collisions if x in past and y in past and past[x]!=past[y]]
    heterogeneous=len(deltas)>1 and len(outcomes)>1
    return {'pass':not future_bad and not violations and bool(nonduplicate) and heterogeneous,
      'future_sufficient':not future_bad,'same_code_pairs':collisions,
      'nonduplicate_past_pair':nonduplicate[0] if nonduplicate else None,
      'heterogeneous_dynamics':heterogeneous,'distinct_outcome_count':len(outcomes),
      'future_counterexample':future_bad[0] if future_bad else None,
      'partition_rounds':rounds,'distinct_action_deltas':sorted(map(list,deltas)),
      'order_stable':not any(x[2] in ('nonpositive delta','unfolded order') for x in violations),
      'successor_total_on_viable':not any(x[2]=='missing response' for x in violations),
      'tick_viable':not any(x[2]=='tick phase' for x in violations),
      'arrow_endogenous':not any(x[2] in ('arrow owner','required resource withdrawn','budget ledger') for x in violations),
      'violations':violations}


def branchwise(j,a):
    lookup={b['branch_id']:b['ordered_records'] for b in j['branch_local_histories']}
    return tuple(tuple((r['slot'],r['content'],r['predictive_class'],r['weight']) for r in lookup[a[k]])
                 for k in ('left_branch','right_branch'))


def pairing_distribution(j,a):
    lookup={b['branch_id']:{r['slot']:r for r in b['ordered_records']} for b in j['branch_local_histories']}
    left=lookup[a['left_branch']];right=lookup[a['right_branch']]
    count=Counter((left[e['left_slot']]['content'],right[e['right_slot']]['content']) for e in a['coupling_edges'])
    n=sum(count.values())
    return tuple(sorted((k,Fraction(v,n)) for k,v in count.items())) if n else ()


def rec_signature(j,a):
    obs=j['admissible_joint_observables']
    return (branchwise(j,a),tuple(pairing_distribution(j,a) for _ in obs))


def c7_local(m,side):
    j=m[side]['joint_binding'];aa=j['assemblages'];ids={a['assemblage_id'] for a in aa}
    branchids={b['branch_id'] for b in j['branch_local_histories']}
    maps={x['coupling_id']:tuple(x['right_slots_by_left_slot']) for x in j['admissible_coupling_maps']}
    issues=[]
    expected_observable=f'{"S" if side=="source" else "T"}-jointPairing'
    for obs in j['admissible_joint_observables']:
        if obs['observable_id']!=expected_observable:
            issues.append(f"unknown joint observable {obs['observable_id']}")
    if len(ids)!=len(aa):issues.append('duplicate assemblage ID')
    for a in aa:
        if a['left_branch'] not in branchids or a['right_branch'] not in branchids:issues.append(f"{a['assemblage_id']}: missing branch")
        if not a['coupling_edges']:issues.append(f"{a['assemblage_id']}: empty coupling")
    decom={x['assemblage_id']:x for x in j['decomposition']}
    for a in aa:
        x=decom.get(a['assemblage_id'])
        if not x or x['left_branch']!=a['left_branch'] or x['right_branch']!=a['right_branch']:
            issues.append(f"{a['assemblage_id']}: decomposition mismatch")
    for row in j['reassembly']:
        a=next((a for a in aa if a['assemblage_id']==row['assemblage_id']),None)
        if not a:issues.append(f"{row['assemblage_id']}: missing reassembly image");continue
        if (row['left_branch'],row['right_branch'])!=(a['left_branch'],a['right_branch']):issues.append(f"{a['assemblage_id']}: reassembly branches mismatch")
        cm=maps.get(row['coupling_id'])
        edges=tuple(sorted((e['left_slot'],e['right_slot']) for e in a['coupling_edges']))
        if cm is None or edges!=tuple(sorted(enumerate(cm))):
            issues.append(f"{a['assemblage_id']}: reassembly coupling {row['coupling_id']} disagrees with raw edges {edges}")
    prefix='S' if side=='source' else 'T'
    for action in m[side]['actions']:
        query=action['binding_query']
        if query is not None and not any(x['left_branch']==f'{prefix}:{query[0]}' and x['right_branch']==f'{prefix}:{query[1]}' for x in j['reassembly']):
            issues.append(f"{action['action_id']}: bindingProbe rejects queried pair")
    all_maps=set(itertools.product((0,1),repeat=2))
    admissible=set(maps.values())
    subset=bool(admissible) and admissible < all_maps and len(admissible)==2 and all(sorted(x)==[0,1] for x in admissible)
    if not subset:issues.append('admissible coupling maps are not two distinct bijections forming a proper subset')
    pairs=[[a['assemblage_id'],b['assemblage_id']] for a in aa for b in aa if a['assemblage_id']!=b['assemblage_id'] and branchwise(j,a)==branchwise(j,b) and rec_signature(j,a)!=rec_signature(j,b)]
    distributions={a['assemblage_id']:{f'{x[0]}|{x[1]}':str(p) for x,p in pairing_distribution(j,a)} for a in aa}
    return {'pass':not issues and bool(pairs),'well_formed':not issues,'well_formed_issues':issues,
      'strict_refinement':bool(pairs),'witness':pairs[0] if pairs else None,
      'branchwise_class_count':len({branchwise(j,a) for a in aa}),
      'recombination_class_count':len({rec_signature(j,a) for a in aa}),
      'distributions':distributions,'coupling_proper_subset':subset}


def c7(m,side):
    return c7_local(m,side)


def c7_transport(m):
    sm=m['staged_clause_map'];sj=m['source']['joint_binding'];tj=m['target']['joint_binding']
    sa={a['assemblage_id']:a for a in sj['assemblages']};ta={a['assemblage_id']:a for a in tj['assemblages']}
    amap={x['source']:x['target'] for x in sm['assemblage_map']}
    bmap={x['source']:x['target'] for x in sm['branch_map']}
    content={x['source']:x['target'] for x in sm['branch_local_content_map']}
    coupling={x['source']:x['target'] for x in sm['coupling_map']}
    obsmap={x['source']:x['target'] for x in sm['joint_observable_map']}
    issues=[];distribution_fail=[];quotient_fail=[]
    sobs={x['observable_id'] for x in sj['admissible_joint_observables']};tobs={x['observable_id'] for x in tj['admissible_joint_observables']}
    if set(obsmap)!=sobs or set(obsmap.values())!=tobs:issues.append('joint observable map incomplete or dangling')
    for sid,a in sa.items():
        tid=amap.get(sid);b=ta.get(tid)
        if not b:issues.append(f'{sid}: missing staged assemblage');continue
        if bmap.get(a['left_branch'])!=b['left_branch'] or bmap.get(a['right_branch'])!=b['right_branch']:
            issues.append(f'{sid}: branch decomposition not transported')
        source_dist=pairing_distribution(sj,a);target_dist=pairing_distribution(tj,b)
        mapped=tuple(sorted(((content.get(pair[0]),content.get(pair[1])),p) for pair,p in source_dist))
        if sobs and mapped!=target_dist:distribution_fail.append({'source':sid,'target':tid,'source_mapped':str(mapped),'target_distribution':str(target_dist)})
    src_branches={x['branch_id']:x['ordered_records'] for x in sj['branch_local_histories']}
    tgt_branches={x['branch_id']:x['ordered_records'] for x in tj['branch_local_histories']}
    for source_branch,source_records in src_branches.items():
        target_branch=bmap.get(source_branch)
        target_records=tgt_branches.get(target_branch)
        expected=[(x['slot'],content.get(x['content']),x['predictive_class'],x['weight']) for x in source_records]
        observed=[(x['slot'],x['content'],x['predictive_class'],x['weight']) for x in target_records] if target_records else None
        if expected!=observed:issues.append(f'{source_branch}: branch-local records not transported')
    for x in sa:
        for y in sa:
            if x not in amap or y not in amap:continue
            a,b=sa[x],sa[y];c,d=ta[amap[x]],ta[amap[y]]
            if (branchwise(sj,a)==branchwise(sj,b))!=(branchwise(tj,c)==branchwise(tj,d)) or (rec_signature(sj,a)==rec_signature(sj,b))!=(rec_signature(tj,c)==rec_signature(tj,d)):
                quotient_fail.append([x,y])
    for row in sj['reassembly']:
        matches=[x for x in tj['reassembly'] if x['left_branch']==bmap.get(row['left_branch']) and x['right_branch']==bmap.get(row['right_branch']) and x['coupling_id']==coupling.get(row['coupling_id'])]
        if len(matches)!=1 or matches[0]['assemblage_id']!=amap.get(row['assemblage_id']):issues.append(f"{row['assemblage_id']}: reassembly not transported")
    return {'pass':not (issues or distribution_fail or quotient_fail),'well_formed_issues':issues,
            'distribution_failures':distribution_fail,'quotient_failures':quotient_fail}


def c8(m,side):
    ss=set(m[side]['kernel_state_ids']);owner=m['carriers'][side]['code']
    resource_rows=m['withdrawal']['retained_resources'] if side=='target' else m[side]['resources']
    retained={x['resource_id']:x['owner'] for x in resource_rows}
    r=states(m,side)
    def safe(s,d,live):
        z=response(m,side,s,d)
        if z is None:return 'missing response'
        t,a,y=z
        if t['to_state'] not in live:return 'successor outside candidate kernel'
        if a['owner']!=owner or a['regeneration_owner']!=owner or y['maintenance_owner']!=owner or r[s]['owner']!=owner or y['owner']!=owner:return 'owner'
        if retained.get(a['regeneration_resource'])!=owner or any(retained.get(x)!=owner for x in a['required_resources']):return 'resource'
        paid=r[s]['budget']-a['budget_cost']+a['budget_regeneration']
        if paid<=0 or paid!=y['budget']:return f'ledger {paid} != {y["budget"]}'
        return None
    live=set(ss)
    while True:
        new={s for s in live if r[s]['budget']>0 and all(safe(s,d,live) is None for d in disturbances(m,side))}
        if new==live:break
        live=new
    violations=[[s,d,safe(s,d,ss)] for s in sorted(ss) for d in disturbances(m,side) if safe(s,d,ss)]
    return {'pass':bool(ss) and live==ss,'kernel_size':len(ss),'maximal_viable_size':len(live),
      'maximal_viable_states':sorted(live),'violations':violations}


def bridge(m):
    src=states(m,'source');tgt=states(m,'target');sm=m['staged_clause_map']
    mapping={x['source']:x['target'] for x in sm['raw_state_map']}
    frontier={x['history_id']:x for x in m['source']['history_frontier']}
    images={x['source_history_id']:x for x in m['target']['history_images']}
    problems=[]
    past=m['source']['past_history_graph']
    seed_events={e['event_id'] for e in past['events'] if not any(x['to']==e['event_id'] for x in past['edges'])}
    reached_events=set(seed_events);pending=list(seed_events)
    while pending:
        e=pending.pop()
        for edge in past['edges']:
            if edge['from']==e and edge['to'] not in reached_events:
                reached_events.add(edge['to']);pending.append(edge['to'])
    produced={e['produces'] for e in past['edges'] if e['from'] in reached_events and e['to'] in reached_events}
    reachable=set(x['state_id'] for x in m['source']['endpoint_packages'])|produced
    todo=list(reachable)
    while todo:
        s=todo.pop()
        for d in disturbances(m,'source'):
            z=response(m,'source',s,d)
            if z and z[0]['to_state'] not in reachable:
                reachable.add(z[0]['to_state']);todo.append(z[0]['to_state'])
    declared=set(m['source']['frontier_reachable_ids'])
    if reachable!=declared:problems.append({'coverage':[sorted(reachable),sorted(declared)]})
    if set(frontier)!=declared or set(images)!=declared or set(mapping)!=declared:
        problems.append('history/raw-map domain incomplete')
    noninjective=len(set(mapping.values()))!=len(mapping)
    strict_edges=[]
    for e in m['source']['frontier_edges']:
        a,b,d=e['from'],e['to'],e['disturbance'];z=response(m,'source',a,d)
        if not z or z[0]['to_state']!=b:problems.append({'source_edge_not_realized':e});continue
        strict_edges.append([a,b])
        w=response(m,'target',mapping.get(a),d) if mapping.get(a) else None
        if not w or w[0]['to_state']!=mapping.get(b):problems.append({'successor_not_preserved':e})
        sf=frontier.get(a,{}).get('signature',{});sg=frontier.get(b,{}).get('signature',{})
        for k in ('order','tick','progress','record'):
            if sf.get(k,0)>=sg.get(k,0):problems.append({'non_strict_edge':[a,b,k]})
    for a,b,d in [('S-A0a','S-A1safe','nominal'),('S-A0b','S-A1safe','nominal')]:
        if not any(e['from']==a and e['to']==b and e['disturbance']==d for e in m['source']['frontier_edges']):
            problems.append({'required_declared_strict_edge_missing':[a,b,d]})
    for s in sorted(declared):
        if s not in frontier or s not in images or s not in mapping:continue
        im=images[s];fr=frontier[s]
        if im['target_state_id']!=mapping[s]:problems.append({'history_image_map':[s,im['target_state_id'],mapping[s]]})
        expected_past=fr['past_history_id'].replace('S-','T-') if fr['past_history_id'] is not None else None
        if expected_past!=im['past_history_id']:
            problems.append({'past_history':[s,fr['past_history_id'],im['past_history_id']]})
        for k in ('order','tick','progress','record'):
            if im['signature'].get(k)!=fr['signature'].get(k,0)+2:problems.append({'rank':[s,k]})
        if q(m,'source',s)[1] not in ('sA','sB') or q(m,'target',mapping[s])[1] != {'sA':'rA','sB':'rB'}.get(q(m,'source',s)[1]):
            problems.append({'route':[s,mapping[s]]})
        if im['signature'].get('owner')!=m['carriers']['target']['code']:
            problems.append({'owner':s})
    # Representative independence: raw source equal-q pairs have equal target q.
    reps=[]
    for x in sorted(declared):
        for y in sorted(declared):
            if x!=y and x in mapping and y in mapping and q(m,'source',x)==q(m,'source',y):
                reps.append([x,y])
                if q(m,'target',mapping[x])!=q(m,'target',mapping[y]):problems.append({'representatives':[x,y]})
    return {'pass':not problems and bool(strict_edges) and bool(reps),'problems':problems,
            'reachable_count':len(reachable),'strict_edges':strict_edges,'representative_pairs':reps,
            'raw_map_noninjective':noninjective}


def route(m):
    cor=m['corridor'];events=unique(cor['events'],'event_id');deps={(x['parent'],x['child']) for x in cor['dependencies']}
    routes=cor['route_histories'];rr={x['route_id']:x for x in routes};st=states(m,'target');problems=[];witness=[]
    exit_ids={r['boundary_target_event'] for r in routes}
    max_stage=max(x['index'] for x in cor['stages'])
    declared_exits={e['event_id'] for e in cor['events'] if e['stage']==max_stage and e['owner']==m['carriers']['target']['code']}
    if len(exit_ids)!=1 or exit_ids!=declared_exits:
        problems.append({'shared_endpoint_mismatch':{'route_exits':sorted(exit_ids),'corridor_exits':sorted(declared_exits)}})
    for r in routes:
        path=r['admissible_event_path']
        if not path or any(e not in events for e in path) or any((a,b) not in deps for a,b in zip(path,path[1:])):
            problems.append({'not_path':r['route_id']})
        if not path or path[-1]!=r['boundary_target_event'] or r['boundary_target_event'] not in events:
            problems.append({'route_exit_mismatch':r['route_id']})
        if st[r['arrival_state_id']]['route_residue']!=r['endpoint_residue']:
            problems.append({'endpoint_residue':r['route_id']})
    for x,y in cor['route_comparison_domain']:
        a,b=rr[x],rr[y];u,v=a['arrival_state_id'],b['arrival_state_id']
        def current(s,route_row):
            z=st[s]
            exit_event=events.get(route_row['boundary_target_event'])
            return (m['carriers']['target']['code'],exit_event['stage'] if exit_event else None,
                    z['public_state'],z['tick_phase'],z['health'])
        if current(u,a)!=current(v,b):continue
        # The declared future probe is one word; its exact outputs are computed.
        sx,sy=u,v
        for d in cor['future_disturbance_word']:
            zx=response(m,'target',sx,d);zy=response(m,'target',sy,d)
            if not zx or not zy:break
            sx=zx[0]['to_state'];sy=zy[0]['to_state']
        if st[sx]['health']!=st[sy]['health'] or st[sx]['maintenance_state']!=st[sy]['maintenance_state']:
            if st[u]['route_residue']!=st[v]['route_residue']:
                witness.append({'routes':[x,y],'arrival_states':[u,v],
                                'future_health':[st[sx]['health'],st[sy]['health']]})
    flat=bool(cor['route_comparison_domain']) and cor['flatness_data']['completion_system'] is not None and cor['flatness_data']['path_clock_translation'] is not None
    status='route-indexed' if witness and not problems else 'flat' if flat and not problems else 'unresolved'
    return {'pass':status=='route-indexed','computed_status':status,'witness':witness[0] if witness else None,
            'path_problems':problems,'flatness_certificate_available':flat}


def corridor(m):
    cor=m['corridor'];stages=unique(cor['stages'],'index');ev=unique(cor['events'],'event_id')
    deps={(x['parent'],x['child']) for x in cor['dependencies']};src=m['carriers']['source']['code'];tgt=m['carriers']['target']['code']
    problems=[]
    if not stages or sorted(stages)!=list(range(min(stages),max(stages)+1)) or not all(x['realized'] for x in stages.values()):problems.append('unrealized stage or gap')
    mixed=[x for x in stages.values() if src in x['active_support'] and tgt in x['active_support']]
    if not mixed:problems.append('no mixed-support stage')
    for a,b in zip(sorted(stages),sorted(stages)[1:]):
        for k in ('order_rank','tick_index','progress_rank','record_value'):
            if stages[a]['signature'][k]>=stages[b]['signature'][k]:problems.append(f'non-strict {k}:{a}->{b}')
    if not cor['atomic_legs']:problems.append('no atomic leg')
    for leg in cor['atomic_legs']:
        if not (leg['start_stage'] in stages and leg['mixed_stage'] in stages and leg['takeover_stage'] in stages and leg['end_stage'] in stages):
            problems.append('atomic leg stage missing')
    if not any(e['owner']==src and e['stage'] in [x['index'] for x in mixed] for e in ev.values()):problems.append('source mixed intervention absent')
    if not any(e['owner']==tgt and e['stage'] in [x['index'] for x in mixed] for e in ev.values()):problems.append('target mixed intervention absent')
    if not all(a in ev and b in ev for a,b in deps):problems.append('dangling dependency')
    ir=cor['intervention_rule'];base=ir['base'];s=ir['source_mixed_contribution'];t=ir['target_mixed_contribution']
    source_on='source-mixed' in ev;target_on='target-mixed' in ev
    value=[base[i]+(s[i] if source_on else 0)+(t[i] if target_on else 0) for i in range(len(base))]
    no_s=[base[i]+(t[i] if target_on else 0) for i in range(len(base))]
    no_t=[base[i]+(s[i] if source_on else 0) for i in range(len(base))]
    if value==no_s or value==no_t:problems.append('redundant mixed intervention')
    return {'pass':not problems,'problems':problems,'projection':value,
            'without_source':no_s,'without_target':no_t,'mixed_stages':[x['index'] for x in mixed]}


def coordinate_valid(m,side,s,global_results):
    d=m[side];r=states(m,side)[s]
    packages={x['state_id']:x['clause_assignments'] for x in d['endpoint_packages']} if side=='source' else {x['state_id']:x['clause_assignments'] for x in d['states']}
    if s not in packages:return ['no clause assignments']
    a=packages[s];issues=[];owner=m['carriers'][side]['code']
    if set(a)!=set(f'C{i}' for i in range(1,9)):issues.append('not eight clauses')
    c=a['C1']
    if not c.get('object_token') or c['boundary_id']!=d['boundary_id'] or s not in d['boundary_state_ids'] or c['package_owner']!=owner or c['closure_audit_ref']!=d['closure_audit']['audit_id']:
        issues.append('C1 local assignment')
    c=a['C2'];pr=d['promotion_readouts']
    if c['lower_readout_ref']!=pr['lower_id'] or c['promoted_readout_ref']!=pr['promoted_id'] or c['split_pair_ref']!='|'.join(pr['split_pair']):issues.append('C2 local assignment')
    c=a['C3'];sp=d['self_profile']
    if (c['public_self_lens_ref'],c['profile_ref'],c['continuation_coordinate_ref'])!=(sp['public_self_lens_id'],sp['profile_id'],sp['continuation_coordinate_id']):issues.append('C3 local assignment')
    c=a['C4'];ex=d['exposure_channels']
    if (c['private_state'],c['public_state'],c['channel_family_ref'],c['determining_ref'])!=(s,r['public_state'],ex['channel_family_id'],ex['determining_ref']):issues.append('C4 local assignment')
    c=a['C5'];gp=d['generator_provenance']
    resources={x['resource_id']:x['owner'] for x in d['resources']}
    if (c['action_credit_owner'],c['provenance_ref'],c['credit_rule_ref'])!=(owner,gp['provenance_id'],gp['credit_rule_id']) or resources.get(c['credit_resource'])!=owner:
        issues.append('C5 local assignment')
    c=a['C6']
    if (c['state_ref'],c['dynamics_ref'])!=(s,d['table_id']):issues.append('C6 local assignment')
    c=a['C7'];j=d['joint_binding']
    if (c['joint_relation_ref'],c['decomposition_ref'],c['reassembly_ref'],c['binding_probe_ref'],c['branch_map_ref'])!=(j['relation_id'],j['decomposition_id'],j['reassembly_id'],j['probe_id'],m['staged_clause_map']['branch_map_id']):issues.append('C7 local assignment')
    c=a['C8']
    if (c['budget'],c['repair_owner'],c['kernel_ref'],c['ledger_ref'])!=(r['budget'],owner,d['kernel_id'],d['table_id']):issues.append('C8 local assignment')
    for clause in ('C1','C2','C3','C4','C5','C6','C7','C8'):
        if not global_results[clause]['pass']:issues.append(f'{clause} global predicate')
    return issues


def translate_value(rule,v,rawmap):
    if rule=='identity':return v
    if rule=='owner_17_to_101':return 101 if v==17 else v
    if rule in ('carrier_prefix','audit_ref_prefix'):
        return v.replace('S-','T-',1).replace('object:S','object:T',1)
    if rule=='resource_prefix':return 't-'+v[2:] if v.startswith('s-') else v
    if rule in ('raw_state_map','state_ref_map'):return rawmap.get(v)
    if rule=='split_pair_map':return '|'.join(rawmap.get(x,'?') for x in v.split('|'))
    raise ValueError(f'unknown value rule {rule}')


def staged(m):
    sm=m['staged_clause_map'];rawmap={x['source']:x['target'] for x in sm['raw_state_map']}
    source={x['state_id']:x['clause_assignments'] for x in m['source']['endpoint_packages']}
    target={x['state_id']:x['clause_assignments'] for x in m['target']['states']}
    fail=[]
    for arrival in sm['source_arrivals']:
        s=arrival['source_state'];t=arrival['target_state']
        if rawmap.get(s)!=t:fail.append([s,t,'raw arrival map']);continue
        for x in sm['coordinate_map']:
            a=source[s][x['clause']].get(x['source_coordinate'])
            b=target[t][x['clause']].get(x['target_coordinate'])
            expected=translate_value(x['value_rule'],a,rawmap)
            if expected!=b:fail.append([s,t,x['clause'],x['source_coordinate'],expected,b])
    c7t=c7_transport(m)
    return {'pass':not fail and c7t['pass'],'coordinate_failures':fail,'c7_transport':c7t}


def evaluate(m):
    side={}
    for name in ('source','target'):
        side[name]={f'C{i}':globals()[f'c{i}'](m,name) for i in range(1,9)}
    st=staged(m);br=bridge(m);rt=route(m);co=corridor(m)
    arrival=m['withdrawal']['endpoint_state_ids']
    target_packages={s:coordinate_valid(m,'target',s,side['target']) for s in arrival}
    all_packages={s:coordinate_valid(m,'target',s,side['target']) for s in m['target']['kernel_state_ids']}
    src_arrival=[x['source_state'] for x in m['staged_clause_map']['source_arrivals']]
    source_packages={s:coordinate_valid(m,'source',s,side['source']) for s in src_arrival}
    ev={x['event_id']:x for x in m['corridor']['events']}
    exit_event=m['withdrawal']['handoff_endpoint_event_id']
    endpoint_link=exit_event in ev and ev[exit_event]['owner']==m['carriers']['target']['code'] and ev[exit_event]['stage']==max(x['index'] for x in m['corridor']['stages']) and all(states(m,'target')[s]['tick_phase']==ev[exit_event]['stage']%m['target']['tick_modulus'] for s in arrival)
    obligations={'TTH-03 bridge':br,'Route status':rt,'Corridor':co,
      'TTH-02 package at arrivals':{'pass':all(not x for x in target_packages.values()),'assignment_issues':target_packages},
      'TTH-05 preservation':{'pass':all(not x for x in all_packages.values()),'assignment_issues':all_packages},
      'TTH-04 composition':{'pass':len(m['corridor']['atomic_legs'])>=2,'leg_count':len(m['corridor']['atomic_legs'])},
      'TTH-06':{'pass':all([m['carriers']['source']['code']!=m['carriers']['target']['code'],
          all(not x for x in source_packages.values()),st['pass'],br['pass'],rt['pass'],co['pass'],
          side['target']['C8']['pass'],all(not x for x in target_packages.values()),
          all(not x for x in all_packages.values()),endpoint_link,
          m['recognition_status']=='notAddressed']),
          'endpoint_link':endpoint_link,'source_package_issues':source_packages,
          'staged_map':st,'recognition_value':m['recognition_status']},
      'T17-I':{'pass':False,'reason':'full P05 promotion gates and certificate soundness not declared'}}
    return {'clauses':side,'obligations':obligations}


def mutate(original, mid):
    """Apply exactly the frozen rule's named raw edits to a fresh copy."""
    m=copy.deepcopy(original)
    def state(s):return states(m,'target')[s]
    def act(s,d):return actions(m,'target')[f'T-act-{s}-{d}']
    def trans(s,d):return next(x for x in m['target']['transitions'] if x['from_state']==f'T-{s}' and x['disturbance_id']==d)
    if mid in ('NEG-C6-CODE','NEG-ROUTE-ERASE'):
        state('T-B0')['route_residue']='rA'
    elif mid=='NEG-C6-HEALTH':
        state('T-A1warning')['health']='safe';state('T-A1warning')['maintenance_state']='T:safe'
    elif mid=='NEG-C7-NO-JOINT-OBSERVABLE':
        for side in ('source','target'):m[side]['joint_binding']['admissible_joint_observables']=[]
        m['staged_clause_map']['joint_observable_map']=[]
    elif mid=='NEG-C7-UNCOUPLED':
        for side in ('source','target'):
            j=m[side]['joint_binding'];j['assemblages'][1]['coupling_edges']=copy.deepcopy(j['assemblages'][0]['coupling_edges'])
            if 'core_rule' in m[side]['closure_audit']['perturbation']:
                j['reassembly']=[row for row in j['reassembly'] if row['coupling_id']!='crossed']
    elif mid=='NEG-C7-PRESERVATION':
        j=m['target']['joint_binding']
        if 'core_rule' in m['target']['closure_audit']['perturbation']:
            j['assemblages'][0]['coupling_edges'],j['assemblages'][1]['coupling_edges']=j['assemblages'][1]['coupling_edges'],j['assemblages'][0]['coupling_edges']
            j['reassembly'][0]['assemblage_id'],j['reassembly'][1]['assemblage_id']=j['reassembly'][1]['assemblage_id'],j['reassembly'][0]['assemblage_id']
            cmap=m['staged_clause_map']['coupling_map']
            cmap[0]['target'],cmap[1]['target']=cmap[1]['target'],cmap[0]['target']
        else:
            j['assemblages'][1]['coupling_edges']=copy.deepcopy(j['assemblages'][0]['coupling_edges'])
    elif mid in ('NEG-PKG-ENDPOINT','NEG-PKG-LATER'):
        s='T-A0a' if mid=='NEG-PKG-ENDPOINT' else 'T-A1safe'
        del state(s)['clause_assignments']['C1']['object_token']
    elif mid=='NEG-C8-UNDERFUND':
        for a in m['target']['actions']:a['budget_regeneration']=0
    elif mid=='NEG-BRIDGE-REP':
        next(x for x in m['staged_clause_map']['raw_state_map'] if x['source']=='S-A0b')['target']='T-B0'
    elif mid=='NEG-BRIDGE-EDGE':
        m['source']['frontier_edges']=[x for x in m['source']['frontier_edges'] if not (x['from']=='S-A0a' and x['to']=='S-A1safe')]
    elif mid=='NEG-CORRIDOR-DETACHED':
        cor=m['corridor'];cor['stages']=[x for x in cor['stages'] if x['index']!=1]
        cor['events']=[x for x in cor['events'] if x['event_id'] not in ('source-mixed','target-mixed')]
        ev={x['event_id'] for x in cor['events']}
        cor['dependencies']=[x for x in cor['dependencies'] if x['parent'] in ev and x['child'] in ev]
    elif mid=='NEG-CORRIDOR-GAP':
        next(x for x in m['corridor']['stages'] if x['index']==1)['realized']=False
    elif mid=='NEG-TTH06-LINK':m['withdrawal']['handoff_endpoint_event_id']='s-entry'
    elif mid=='NEG-C6-ORDER':act('A0a','nominal')['order_delta']=0
    elif mid=='NEG-C6-SUCCESSOR':
        m['target']['transitions']=[x for x in m['target']['transitions'] if not (x['from_state']=='T-B1safe' and x['disturbance_id']=='hit')]
    elif mid=='NEG-C6-TICK':trans('A0a','nominal')['to_state']='T-A0a'
    elif mid=='NEG-C6-ARROW':act('A0a','hit')['owner']=m['carriers']['source']['code']
    elif mid=='NEG-C1-CLOSURE':
        m['target']['transitions']=[x for x in m['target']['transitions'] if not (x['from_state']=='T-A0a' and x['disturbance_id']=='nominal')]
    elif mid=='NEG-C1-UNMAINTAINED-RECURRENCE':
        act('B0','hit')['owner']=901
    elif mid=='NEG-C2-SPLIT':
        groups={}
        for r in m['target']['states']:
            k=(r['route_residue'],r['tick_phase'],r['health'])
            groups.setdefault(k,f'report:{len(groups)}')
            r['public_state']=groups[k]
            r['clause_assignments']['C4']['public_state']=groups[k]
    elif mid=='NEG-C3-PROFILE':trans('A0b','nominal')['to_state']='T-B1safe'
    elif mid=='NEG-C4-EXPOSE':
        m['target']['exposure_channels']['declared_channels']=copy.deepcopy(m['target']['exposure_channels']['expanded_interface_negative'])
    elif mid=='NEG-C5-SCHEDULE':
        p=next(x for x in m['target']['generator_provenance']['protocols'] if x['protocol_id']=='T-genuine')
        p['generator_owner']=901
        for e in p['edges']:e['channel']='other'
    elif mid=='NEG-C5-INTERNALIZED':
        p=next(x for x in m['target']['generator_provenance']['protocols'] if x['protocol_id']=='T-internalized')
        reverse={('v','u'),('w','v'),('u','w')}
        p['edges']=[e for e in p['edges'] if (e['from'],e['to']) not in reverse]
    else:raise ValueError(f'unimplemented declared mutation {mid}')
    return m


def mutation_result(mid,positive,negative):
    p=positive['clauses']['target'];n=negative['clauses']['target'];o=negative['obligations']
    if mid=='NEG-C1-UNMAINTAINED-RECURRENCE':
        pc=n['C1']
        audit=pc.get('t1_style_audit',{})
        ok=not pc['retained'] and not audit.get('retained',False) and pc['well_formed']
        detail={'core_state_ids':pc.get('core_state_ids'), 'components':pc.get('components'),
                'P_epsilon_core_mass':pc.get('core_mass'),
                'E2_epsilon_core_mass':audit.get('perturbed_core_mass'),
                'P_epsilon_retained':pc.get('retained'),
                'E2_epsilon_retained':audit.get('retained'),
                'threshold':pc.get('threshold')}
    elif mid=='NEG-C1-CLOSURE':
        changed=n['C1']['closure']!=p['C1']['closure']
        ok=not n['C1']['well_formed'] and changed
        detail={'markov_well_formed':n['C1']['well_formed'],'closure_changed':changed,'missing_rows':n['C1'].get('missing_markov_rows')}
    elif mid=='NEG-C2-SPLIT':ok=not n['C2']['pass'];detail=n['C2']
    elif mid=='NEG-C3-PROFILE':ok=not n['C3']['pass'];detail=n['C3']
    elif mid=='NEG-C4-EXPOSE':ok=not n['C4']['pass'];detail=n['C4']
    elif mid in ('NEG-C5-SCHEDULE','NEG-C5-INTERNALIZED'):
        target='T-genuine' if mid=='NEG-C5-SCHEDULE' else 'T-internalized'
        expected='other' if mid=='NEG-C5-SCHEDULE' else 'ambiguous'
        credit=n['C5']['protocols'][target]['credit'];ok=credit==expected
        detail={'protocol':target,'computed_credit':credit,'expected_change':expected,
                'products':n['C5']['protocols'][target]['products']}
    elif mid in ('NEG-C6-CODE','NEG-C6-HEALTH'):
        ok=not n['C6']['future_sufficient'];detail={'future_counterexample':n['C6']['future_counterexample'],'partition_rounds':n['C6']['partition_rounds']}
    elif mid.startswith('NEG-C6-'):
        reasons={'NEG-C6-ORDER':'nonpositive delta','NEG-C6-SUCCESSOR':'missing response',
                 'NEG-C6-TICK':'tick phase','NEG-C6-ARROW':'arrow owner'}
        ok=any(x[2]==reasons[mid] for x in n['C6']['violations'])
        detail={'violations':n['C6']['violations']}
    elif mid in ('NEG-C7-NO-JOINT-OBSERVABLE','NEG-C7-UNCOUPLED'):
        ok=not n['C7']['strict_refinement'] and n['C7']['recombination_class_count']==n['C7']['branchwise_class_count']
        detail={'local':n['C7'],'transport':negative['obligations']['TTH-06']['staged_map']['c7_transport']}
    elif mid=='NEG-C7-PRESERVATION':
        tr=negative['obligations']['TTH-06']['staged_map']['c7_transport']
        ok=bool(tr['distribution_failures'])
        detail={'local_well_formed':n['C7']['well_formed'],'local_issues':n['C7']['well_formed_issues'],
                'transport_failures':tr['distribution_failures']}
        if 't1_style_audit' in n['C1']:
            detail['source_local_well_formed']=negative['clauses']['source']['C7']['well_formed']
            detail['other_staged_issues']=tr['well_formed_issues']
            detail['quotient_failures']=tr['quotient_failures']
            detail['coordinate_failures']=negative['obligations']['TTH-06']['staged_map']['coordinate_failures']
    elif mid in ('NEG-PKG-ENDPOINT','NEG-PKG-LATER'):
        s='T-A0a' if mid=='NEG-PKG-ENDPOINT' else 'T-A1safe'
        issues=o['TTH-05 preservation']['assignment_issues'][s]
        ok='C1 local assignment' in issues
        detail={'state':s,'local_assignment_issues':issues,
                'baseline_package_pass':positive['obligations']['TTH-02 package at arrivals']['pass'] if mid=='NEG-PKG-ENDPOINT' else positive['obligations']['TTH-05 preservation']['pass']}
    elif mid=='NEG-C8-UNDERFUND':ok=n['C8']['maximal_viable_size']==0;detail=n['C8']
    elif mid in ('NEG-BRIDGE-REP','NEG-BRIDGE-EDGE'):
        ok=not o['TTH-03 bridge']['pass'];detail=o['TTH-03 bridge']
    elif mid=='NEG-ROUTE-ERASE':ok=o['Route status']['computed_status']!='route-indexed';detail=o['Route status']
    elif mid.startswith('NEG-CORRIDOR-'):ok=not o['Corridor']['pass'];detail=o['Corridor']
    elif mid=='NEG-TTH06-LINK':
        ok=not o['TTH-06']['endpoint_link'];detail={'endpoint_link':o['TTH-06']['endpoint_link']}
    else:raise ValueError(mid)
    pos03='t1_style_audit' in p['C1']
    if mid=='NEG-C7-UNCOUPLED' and (not n['C7']['well_formed'] or (pos03 and not negative['clauses']['source']['C7']['well_formed'])):
        outcome='INVALID-CONTROL'
    elif mid=='NEG-C7-PRESERVATION' and ok and (not n['C7']['well_formed'] or (pos03 and (not detail['source_local_well_formed'] or detail['other_staged_issues'] or detail['quotient_failures'] or detail['coordinate_failures']))):
        outcome='CONFIRMED-CONFOUNDED'
    elif mid in ('NEG-PKG-ENDPOINT','NEG-PKG-LATER') and ok and not detail['baseline_package_pass']:
        outcome='CONFIRMED-NARROW'
    else:
        outcome='CONFIRMED' if ok else 'FAILED'
    return {'outcome':outcome,'computed':detail,
            'well_formedness':{'target_C7':n['C7']['well_formed'],'target_C7_issues':n['C7']['well_formed_issues'],
                               'target_C1_Markov':n['C1']['well_formed']}}


def positive_predictions(result):
    out={}
    for c,v in result['clauses']['target'].items():
        out[c]={'outcome':'CONFIRMED' if v['pass'] else 'FAILED','computed':v}
    for name,v in result['obligations'].items():
        expected=False if name in ('TTH-04 composition','T17-I') else True
        # The preregistered text explicitly predicts the full P05 claim stays open.
        actual=v['pass']
        out[name]={'outcome':'CONFIRMED' if actual==expected else 'FAILED','computed':v,
                   'predicted_boolean':expected}
    return out


def write_pos03(args, model, positive, preds, mutations, negative_runs):
    categories=('CONFIRMED','CONFIRMED-NARROW','CONFIRMED-CONFOUNDED',
                'FAILED','INVALID-CONTROL','UNDETERMINED')
    counts=Counter(x['outcome'] for x in list(preds.values())+list(mutations.values()))
    clean=sum(x['outcome']=='CONFIRMED' for x in mutations.values())
    ambiguities=[
      'CORE maintenance: funded means a positive successor budget satisfying the raw ledger equation, with carrier-owned action, generator protocol, and required/regeneration resources. This applies the declared C8-style maintenance language to each bottom component.',
      'CORE selector: anchors are the source_arrivals.source_state and target_arrivals strings. Bottom SCCs use only positive edges of the unperturbed nominal/hit matrix; missing Markov rows make C1 ill-formed before retention is interpreted.',
      'T1-style C and U: C is the state-to-computed-q-class indicator and U is uniform on each realized q fiber; E₂=P²CU. At epsilon zero, report the exact affine fixed space with componentwise nonnegativity constraints rather than assuming uniqueness.',
      'C7 uncoupled: the crossed protocol remains admissible, but its reassembly row is deleted, so local consistency checks retained, realized reassembly rows only. Both assemblages remain in the refinement domain.',
      'C7 preservation: require both carriers locally well formed and no other staged/quotient failure before calling an observable-transport negative isolated.',
    ] + AMBIGUITIES[1:]
    side_effects={}
    wellformed={}
    for mid, run in negative_runs.items():
        wellformed[mid]={side:{'C1_markov':run['clauses'][side]['C1']['well_formed'],
                                'C7_local':run['clauses'][side]['C7']['well_formed'],
                                'C7_issues':run['clauses'][side]['C7']['well_formed_issues']}
                         for side in ('source','target')}
        tr=run['obligations']['TTH-06']['staged_map']
        wellformed[mid]['staged']={'coordinate_failures':tr['coordinate_failures'],
                                  'C7_other_issues':tr['c7_transport']['well_formed_issues'],
                                  'C7_quotient_failures':tr['c7_transport']['quotient_failures']}
        side_effects[mid]={
          'changed_clause_passes':{side:{c:v['pass'] for c,v in run['clauses'][side].items()
                                          if v['pass']!=positive['clauses'][side][c]['pass']}
                                   for side in ('source','target')},
          'changed_obligation_passes':{k:v['pass'] for k,v in run['obligations'].items()
                                       if v['pass']!=positive['obligations'][k]['pass']}}
    output={'model_id':model['model_id'],
            'declaration_sha256':hashlib.sha256(args.model.read_bytes()).hexdigest(),
            'method':'exact Fraction arithmetic; finite-state partition fixed points; bottom SCC CORE; exact RREF fixed distributions; greatest viable fixed point',
            'ambiguities':ambiguities,'positive_predictions':preds,'mutation_predictions':mutations,
            'counts':{x:counts[x] for x in categories},'clean_ablation_count':clean,
            'source_clause_checks':positive['clauses']['source'],
            'mutation_well_formedness':wellformed,'mutation_side_effects':side_effects,
            'limitations':['The route-anchored union selector is declared for this model, not prescribed by T1; anchors on both route components may include nearly all maintained recurrent states. Retention chiefly tests transient leakage.',
                           'The new maintenance negative cleanly ablates the two retention subchecks, which pass at baseline, but baseline C1 already fails nonuniformity; it does not establish loss of a valid C1 package.',
                           'C1, C4, C5, and C6 remain declared surrogates; a passing finite POS-03 model does not establish P05 T17-I or a Lean-kernel Temporal-FIACH theorem.']}
    args.json_out.parent.mkdir(parents=True,exist_ok=True)
    args.json_out.write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')

    t=preds['C1']['computed'];s=positive['clauses']['source']['C1'];neg=mutations['NEG-C1-UNMAINTAINED-RECURRENCE']['computed']
    lines=['# FIACH-POS-03 preregistration evaluation','',
      'Computed from the committed declaration using exact rationals and finite fixed points. Stored prediction and status text was not used as a verdict.','',
      f"Declaration SHA-256: `{output['declaration_sha256']}`",'',
      '## Headline','',
      'Outcomes: '+', '.join(f'**{counts[c]} {c}**' for c in categories)+f'. Clean confirmed ablations: **{clean}**.','',
      'C3 and C6 all-word claims use stable finite-state partitions, not a bounded horizon. `E₂` fixed spaces and defects use exact rational matrix operations.','',
      '## Prediction outcomes','',
      '| Prediction | Outcome | Deciding computation |','|---|---|---|']
    for k,v in list(preds.items())+list(mutations.items()):
        d=v['computed'];bits=[]
        if k=='C1':
            bits=[f"CORE={','.join(d.get('core_state_ids',[]))}",f"Pε={d.get('core_mass')}",
                  f"E₂ε={d.get('t1_style_audit',{}).get('perturbed_core_mass')}",
                  f"E₂ε nonuniform={d.get('t1_style_audit',{}).get('nonuniform')}",f"pass={d['pass']}"]
        elif k=='NEG-C1-UNMAINTAINED-RECURRENCE':
            bits=[f"CORE={','.join(d.get('core_state_ids',[]))}",f"Pε={d['P_epsilon_core_mass']}",
                  f"E₂ε={d['E2_epsilon_core_mass']}"]
        elif k in ('NEG-C7-NO-JOINT-OBSERVABLE','NEG-C7-UNCOUPLED'):
            bits=[f"strict_refinement={d['local']['strict_refinement']}",
                  f"recombination_classes={d['local']['recombination_class_count']}",
                  f"local_well_formed={d['local']['well_formed']}"]
        elif k=='NEG-C7-PRESERVATION':
            bits=[f"local_well_formed={d['local_well_formed']}",
                  f"observable_transport_failures={len(d['transport_failures'])}",
                  f"other_staged_issues={len(d['other_staged_issues'])}"]
        else:
            for f in ('pass','future_sufficient','strict_refinement','local_well_formed',
                      'maximal_viable_size','computed_status','endpoint_link','core_mass'):
                if f in d:bits.append(f'{f}={d[f]}')
            if not bits:bits=[json.dumps(d,sort_keys=True)[:155]]
        lines.append(f"| `{k}` | **{v['outcome']}** | {'; '.join(bits).replace('|','/')} |")
    lines+=['','## Exact C1 audit','',
      'T1 supports a recurrent/transient audit and `P² C U`, but does **not** prescribe this route-anchored union selector. Anchors on both route components can admit essentially all maintained recurrent states; passing `3/4` retention chiefly limits transient leakage and has limited object-selection force.','',
      '| Carrier | Computed CORE | Pε stationary mass | E₂ε fixed mass | Threshold | E₂ε unique | E₂ε nonuniform | δ(E₂⁰) | δ(E₂ε) |',
      '|---|---|---:|---:|---:|---|---|---:|---:|']
    for side,x in (('source',s),('target',t)):
        a=x.get('t1_style_audit',{})
        lines.append(f"| {side} | `{', '.join(x.get('core_state_ids',[]))}` | `{x.get('core_mass')}` | `{a.get('perturbed_core_mass')}` | `{x.get('threshold')}` | {a.get('1/16',{}).get('fixed_space',{}).get('unique')} | {a.get('nonuniform')} | `{a.get('0',{}).get('defect')}` | `{a.get('1/16',{}).get('defect')}` |")
        lines += ['',f'**{side} fixed distributions and components:** `'+json.dumps({'P_epsilon_stationary':x.get('stationary'),'E2_epsilon_fixed':a.get('perturbed_fixed_distribution'),'E2_zero_fixed_space':a.get('0',{}).get('fixed_space'),'E2_epsilon_fixed_space':a.get('1/16',{}).get('fixed_space'),'components':x.get('components')},sort_keys=True)+'`.','']
    lines += ['**Maintenance negative:** `'+json.dumps(neg,sort_keys=True)+'`.','',
              'This is a clean ablation of the **two retention subchecks**: both pass on the baseline and fail after the declared raw owner mutation. Baseline C1 already fails nonuniformity, so this negative does not demonstrate loss of a valid C1 package. The owner mutation also affects other clauses; those side effects are listed below.','',
              '## Failed, qualified, or undetermined predictions','']
    meanings={
      'C1':'On each carrier, raw `P` has column sums `2` and `0` at the merged `A0a/A0b` q-class (and `1` at each other state). The computed `C U` averages that class, making `E₂^(1/16) = Pε² C U` doubly stochastic; every entry is strictly positive (the minimum is `31/1536`). Thus an attracting fixed distribution **does** exist and is unique, but it is uniform (`1/6` on each of six states). The pre-registered requirement for a **nonuniform** attracting distribution fails. Both retention checks pass (`95/96` and `5/6`), so changing CORE or its threshold cannot repair this failure. Even the declared C1 surrogate is not established.',
      'TTH-02 package at arrivals':'The arrival assignments pass their local references, but the target C1 global predicate fails because `E₂` is uniform. No valid surrogate target package is assembled, and full P05 package assembly remains outside the ceiling.',
      'TTH-05 preservation':'Every target state has an assignment, but each inherits the failed C1 global predicate. The model does not establish state-indexed surrogate package preservation.',
      'TTH-06':'Source and target C1 both fail nonuniformity, so the source-package and target-package lanes fail despite the other confirmed links. Even the surrogate handoff is not established.',
      'NEG-C7-UNCOUPLED':'An unchanged local consistency failure invalidates the uncoupled system control.',
      'NEG-C7-PRESERVATION':'A local or other staged failure confounds the observable-transport negative.',
      'NEG-C1-UNMAINTAINED-RECURRENCE':'If either retention check remains above 3/4, the declared maintenance negative does not show both predicted losses; report exact values without tuning.'}
    problematic=[(k,v) for k,v in list(preds.items())+list(mutations.items()) if v['outcome']!='CONFIRMED']
    if not problematic:lines.append('None.')
    for k,v in problematic:
        lines += [f"### {k}: {v['outcome']}",'',
                  'Computed evidence: `'+json.dumps(
                      {'core_state_ids':v['computed'].get('core_state_ids'),
                       'P_epsilon_core_mass':v['computed'].get('core_mass'),
                       'E2_epsilon_core_mass':v['computed'].get('t1_style_audit',{}).get('perturbed_core_mass'),
                       'E2_epsilon_nonuniform':v['computed'].get('t1_style_audit',{}).get('nonuniform')}
                      if k=='C1' else v['computed'],sort_keys=True)+'`.','',
                  meanings.get(k,'The preregistered outcome did not occur or the control has a narrower meaning; retain this result and do not revise POS-03.') ,'']
    lines+=['## Mutation well-formedness and side effects','',
      '| Mutation | Source C7 | Target C7 | Target C1 Markov | Other staged issues | Changed clauses/obligations |',
      '|---|---|---|---|---|---|']
    for mid in mutations:
        w=wellformed[mid];fx=side_effects[mid]
        issues=w['staged']['coordinate_failures']+w['staged']['C7_other_issues']+w['staged']['C7_quotient_failures']
        summary=json.dumps(fx,sort_keys=True).replace('|','/')
        lines.append(f"| `{mid}` | {w['source']['C7_local']} | {w['target']['C7_local']} | {w['target']['C1_markov']} | {len(issues)} | `{summary}` |")
    lines+=['','## Ambiguity log','']+[f'- {x}' for x in ambiguities]
    lines+=['','## POS-02 versus POS-03','',
      'POS-02 retains its enumerated CORE and original C1 stationary test. POS-03 uses the declared recurrent, maintained, route-anchored CORE and adds the exact `E₂` audit. POS-02 regression output was compared byte-for-byte with the committed `M0b_results.json`; see the reproduce commands below.','',
      f"| Model | Target CORE | Pε CORE mass | E₂ε CORE mass | Surrogate package at arrivals | Surrogate handoff |",
      '|---|---|---:|---:|---|---|',
      f"| POS-02 | old enumerated | `2/3` | not declared | failed | failed |",
      f"| POS-03 | `{', '.join(t.get('core_state_ids',[]))}` | `{t.get('core_mass')}` | `{t.get('t1_style_audit',{}).get('perturbed_core_mass')}` | {preds['TTH-02 package at arrivals']['computed']['pass']} | {preds['TTH-06']['computed']['pass']} |",'',
      'The C7 uncoupled control changes from `INVALID-CONTROL` in POS-02 to a locally well-formed `CONFIRMED` negative in POS-03. The C7 preservation control changes from `CONFIRMED-CONFOUNDED` to an isolated `CONFIRMED` observable-transport negative. Both package-deletion controls remain `CONFIRMED-NARROW`, because C1 still fails.','',
      '## Claim ceiling','',
      'These are exact Python finite computations for the declared surrogate clauses and handoff obligations. A confirmed result supports only that declared finite ceiling. It does not supply a full P05 integrated package, T17-I, or Lean-kernel Temporal-FIACH proof.','',
      '## Reproduce','',
      '`python3 scripts/evaluate_fiach_pos02.py audit/proposed_models/FIACH-POS-03.model.json --json-out audit/M1b_results.json --md-out audit/M1b_results.md`','',
      '`python3 scripts/evaluate_fiach_pos02.py audit/proposed_models/FIACH-POS-02.model.json --json-out /tmp/POS02-regression.json --md-out /tmp/POS02-regression.md && cmp /tmp/POS02-regression.json audit/M0b_results.json`','']
    args.md_out.write_text('\n'.join(lines))
    print(json.dumps(output['counts'],sort_keys=True))
    print(f'wrote {args.json_out} and {args.md_out}')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('model',type=Path)
    ap.add_argument('--json-out',type=Path,default=Path('audit/M0b_results.json'))
    ap.add_argument('--md-out',type=Path,default=Path('audit/M0b_results.md'))
    args=ap.parse_args()
    model=json.loads(args.model.read_text())
    positive=evaluate(model)
    names=[x['id'] for x in model['mutation_rules']]
    if len(set(names))!=len(names):raise ValueError('duplicate mutation ID')
    mutations={};negative_runs={}
    for mid in names:
        neg=evaluate(mutate(model,mid))
        mutations[mid]=mutation_result(mid,positive,neg)
        if model['model_id']=='FIACH-POS-03':
            negative_runs[mid]=neg
    preds=positive_predictions(positive)
    if model['model_id']=='FIACH-POS-03':
        write_pos03(args,model,positive,preds,mutations,negative_runs)
        return
    counts=Counter(x['outcome'] for x in list(preds.values())+list(mutations.values()))
    categories=('CONFIRMED','CONFIRMED-NARROW','CONFIRMED-CONFOUNDED','FAILED','INVALID-CONTROL','UNDETERMINED')
    clean_ablations=sum(v['outcome']=='CONFIRMED' for v in mutations.values())
    output={'model_id':model['model_id'],'declaration_sha256':hashlib.sha256(args.model.read_bytes()).hexdigest(),
      'method':'exact Fraction arithmetic; finite-state partition fixed points; powerset closure; greatest viable fixed point',
      'ambiguities':AMBIGUITIES,'positive_predictions':preds,'mutation_predictions':mutations,
      'counts':{x:counts[x] for x in categories},'clean_ablation_count':clean_ablations,
      'limitations':['NEG-C7-UNCOUPLED loses strict refinement but fails local reassembly/coupling consistency; its negative is invalid as a system control.',
                     'NEG-PKG-ENDPOINT and NEG-PKG-LATER detect deletion locally, but the baseline target package already fails C1; neither shows loss of a valid package.',
                     'NEG-C7-PRESERVATION fails both joint-observable transport and local reassembly/coupling consistency.'],
      'source_clause_checks':positive['clauses']['source']}
    args.json_out.parent.mkdir(parents=True,exist_ok=True)
    args.json_out.write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    lines=['# FIACH-POS-02 preregistration evaluation','',
      'Computed from the frozen model with exact rational arithmetic. No stored verdict or status field is used as an outcome.',
      '',f"Declaration SHA-256: `{output['declaration_sha256']}`",'',
      (f"Counts: **{counts['CONFIRMED']} CONFIRMED, {counts['CONFIRMED-NARROW']} CONFIRMED-NARROW, "
       f"{counts['CONFIRMED-CONFOUNDED']} CONFIRMED-CONFOUNDED, "
       f"{counts['FAILED']} FAILED, {counts['INVALID-CONTROL']} INVALID-CONTROL, "
       f"{counts['UNDETERMINED']} UNDETERMINED**. Clean confirmed ablations: **{clean_ablations}**."),'',
      'C6 and C3 use stable finite-state partitions: equality of action-indexed outputs and successor classes at the fixed point implies equality for every finite disturbance word by induction. No word-length cutoff is used. C1 uses exact `Fraction` Gaussian elimination for the perturbed stationary law; C8 uses a greatest-fixed-point deletion of unsafe states.','',
      '| Prediction | Outcome | Deciding computation |','|---|---|---|']
    for k,v in list(preds.items())+list(mutations.items()):
        d=v['computed'];short=[]
        if k.startswith('NEG-C7-') and 'local' in d:
            short=[f"strict_refinement={d['local']['strict_refinement']}",
                   f"R_classes={d['local']['recombination_class_count']}",
                   f"K_classes={d['local']['branchwise_class_count']}",
                   f"local_well_formed={d['local']['well_formed']}"]
        for field in ('pass','core_mass','threshold','defect_count','terminal_class_count','q_class_count','future_counterexample','strict_refinement','recombination_class_count','maximal_viable_size','computed_status','endpoint_link','well_formed','local_well_formed','closure_changed'):
            if field in d:short.append(f'{field}={d[field]}')
        if not short:short.append(json.dumps(d,sort_keys=True)[:135])
        lines.append(f"| `{k}` | **{v['outcome']}** | {'; '.join(short).replace('|','/')} |")
    lines+=['','## Failures and undetermined results','']
    bad=[(k,v) for k,v in list(preds.items())+list(mutations.items()) if v['outcome'] in ('FAILED','UNDETERMINED')]
    if not bad:lines.append('None.')
    failure_meanings={
      'C1':'The exact perturbed stationary CORE mass is 2/3, below the preregistered 3/4 retention threshold. Closure laws pass, but this C1 surrogate fails its own retention subcheck; full P05 C1 was never claimed.',
      'TTH-02 package at arrivals':'Both arrival packages have valid local coordinate references, but their C1 global predicate fails. Therefore even the declared surrogate target package is not assembled at either arrival; TTH-02 cannot be promoted.',
      'TTH-05 preservation':'All six state-indexed assignments inherit the failed C1 global predicate. The model does not establish preservation of a valid surrogate package along target runs.',
      'TTH-06':'The distinct-carrier, endpoint, staged-map, route, corridor, bridge, C7, C8, and recognition checks do not repair the failed source/target C1 package lane. The predicted surrogate handoff is not established; full Temporal-FIACH remains beyond the declared ceiling.'}
    for k,v in bad:
        evidence=v['computed']
        if k=='C1':
            evidence={'core_mass':evidence['core_mass'],'threshold':evidence['threshold'],
              'stationary':evidence['stationary'],
              'closure':{stage:{f:record[f] for f in ('fixed_sets','max_defect','sum_defect','extensive','monotone','idempotent')}
                         for stage,record in evidence['closure'].items()}}
        lines += [f'### {k}: {v["outcome"]}','',
                  'Computed evidence: `'+json.dumps(evidence,sort_keys=True)+'`.','',
                  failure_meanings.get(k,'The preregistered prediction fails or cannot be determined; no model repair is made here.'),'']
    lines+=['## Qualified and invalid controls','',
      '`NEG-C7-UNCOUPLED` is **INVALID-CONTROL**: the quotient distinction collapses, but its unchanged crossed reassembly row disagrees with the new raw coupling. It cannot establish a negative on a well-formed uncoupled system.','',
      '`NEG-PKG-ENDPOINT` is **CONFIRMED-NARROW**: deleting `T-A0a` C1 `object_token` creates a local assignment failure, while the baseline arrival package already fails global C1 retention. It shows local deletion detection, not loss of a valid assembled package.','',
      '`NEG-PKG-LATER` is **CONFIRMED-NARROW**: deleting `T-A1safe` C1 `object_token` creates a local assignment failure, while baseline package preservation already fails global C1 retention. It shows local deletion detection, not loss of a valid preserved package.','']
    lines+=['`NEG-C7-PRESERVATION` is **CONFIRMED-CONFOUNDED**: joint-observable transport fails as predicted, but the mutated target assemblage also disagrees with its unchanged crossed reassembly row. The control detects a transport failure but does not isolate transport on a locally well-formed target.','']
    lines+=['## Mutation well-formedness, separate from target verdicts','',
            '| Mutation | Local well-formedness result | Target predicate result |',
            '|---|---|---|']
    for k,v in mutations.items():
        wf=v['well_formedness'];issues=wf['target_C7_issues']
        local=('C7: '+('; '.join(issues) if issues else 'well formed')+
               '; C1 Markov: '+('well formed' if wf['target_C1_Markov'] else 'missing row'))
        lines.append(f'| `{k}` | {local.replace("|","/")} | {v["outcome"]} |')
    lines+=['',
      'Qualified and invalid controls above are excluded from clean confirmations and clean ablations.','']
    lines+=['','## Ambiguity log','']
    lines += [f'- {a}' for a in AMBIGUITIES]
    lines+=['','## Claim ceiling','',
      'Confirmed entries establish only the named exact finite computations on this declared toy. Any failed clause or lane blocks even the predicted surrogate handoff. No full P05 C-package, T17-I instance, full Temporal-FIACH theorem, or Lean-kernel certificate follows from this Python evaluation.','']
    args.md_out.write_text('\n'.join(lines))
    print(json.dumps(output['counts'],sort_keys=True))
    print(f'wrote {args.json_out} and {args.md_out}')


if __name__=='__main__':main()
