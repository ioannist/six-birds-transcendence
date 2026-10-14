#!/usr/bin/env python3
"""G31b independent epoch, all-block, account and contextual readout checks.

Finite comparisons supplement the universal Lean history/future/lift proofs.
Numeric dynamics come from the unchanged G17/G30 freeze, never evaluated Lean.
"""
from __future__ import annotations
from copy import deepcopy as copy
from fractions import Fraction as F
from itertools import product
import hashlib
import json
from pathlib import Path
import subprocess
import check_full_native_02_fusion_transcription as raw

ROOT = Path(__file__).resolve().parents[1]


def owner_count(events, owner):
    return sum(e[0] == 'native' and e[2]['owner'] == owner for e in events)


def node_count(events, node):
    tag, n = node
    if tag == 'birth':
        return 0
    if tag == 'version' and n < len(events) and events[n][0] == 'native':
        return owner_count(events[:n+1], events[n][2]['owner'])
    return None


def decode_birth(events, owner, ordinal):
    if not 0 <= ordinal < len(events):
        return None
    e = events[ordinal]
    if e[0] == 'boot' and e[1] == owner:
        return e[2],raw.ZERO,e[3],[],e[4]
    if e[0] == 'activation' and e[2] == owner:
        snapshot = events[e[1][1]]
        assert snapshot[0] == 'snapshot'
        return e[3],e[6],e[4],[[snapshot[1],snapshot[5]]],e[5]
    if e[0] == 'partition' and e[2] == owner and e[4]:
        count = node_count(events,e[1])
        return None if count is None else (e[3],e[5],min(e[4]),[[e[1],count]],None)
    if e[0] == 'fusion' and e[3] == owner and e[7]['after'] == e[8]['after']:
        lc,rc = node_count(events,e[1]),node_count(events,e[2])
        return None if lc is None or rc is None else (
            e[4],e[7]['after'],min(e[5]+e[6]),[[e[1],lc],[e[2],rc]],None)
    return None


def epoch_valid(w,a,r,rom,key):
    if r['birth'][0] != 'birth':
        return False
    ordinal = r['birth'][1]
    birth = decode_birth(w['events'][:ordinal+1],a,ordinal)
    if birth is None:
        return False
    br,state,bk,roots,recorded_cursor = birth
    earlier = [e[2] for e in w['events'][:ordinal] if e[0] == 'native' and e[2]['token'] == key]
    cursor = len(earlier)
    initial_cursor = cursor
    charge = earlier[-1]['packet'] if earlier else True
    version = ['birth',ordinal]
    records = []
    valid = True
    for index,e in enumerate(w['events'][ordinal+1:],ordinal+1):
        if e[0] != 'native' or e[2]['owner'] != a:
            continue
        receipt = e[2]
        valid = valid and charge and (
            e[1] == version and receipt['before'] == state and receipt['rom'] == br and
            receipt['issuer'] == ['local',a] and receipt['token'] == bk and receipt['cursor'] == cursor and
            receipt['serial'] == 4*cursor+bk and e[3] is None and
            [receipt['after'],receipt['weight']] in raw.row(br,receipt['before'],receipt['action']))
        state,version,cursor = receipt['after'],['version',index],cursor+1
        records.append(receipt)
        charge = receipt['packet']
    return valid and ordinal < len(w['events']) and (br,bk) == (rom,key) and (
        r['birthCursor'],r['roots'],r['state'],r['version'],r['receipts'],w['cursor'][key],w['charge'][key]) == (
        initial_cursor,roots,state,version,records,cursor,charge) and (
        recorded_cursor is None or recorded_cursor == initial_cursor)


def edge(rom,s,t):
    return sum((F(n,16) for state,n in raw.row(rom,s,False) if state == t),F(0))


def qualifying(rom,a,rs):
    if not rs or rs[0]['before'] != rs[-1]['after'] or any(
            l['after'] != r['before'] for l,r in zip(rs,rs[1:])):
        return None
    if not all(r['owner'] == a and r['issuer'] == ['local',a] and r['rom'] == rom and
               not r['action'] and r['packet'] and [r['after'],r['weight']] in raw.row(rom,r['before'],False) for r in rs):
        return None
    forward,reverse = F(1),F(1)
    for r in rs:
        forward *= edge(rom,r['before'],r['after'])
        reverse *= edge(rom,r['after'],r['before'])
    return [len(rs),rs[0]['cursor'],str(forward),str(reverse)] if forward and reverse and forward != reverse else None


def blocks(rom,a,rs):
    return [block for start in range(len(rs)+1) for count in range(len(rs)-start+1)
            if (block := qualifying(rom,a,rs[start:start+count])) is not None]


def classes(rom):
    states = [list(s) for s in product((False,True),repeat=5)]
    colors = [0 if not s[0] else 1+2*(2*int(s[1])+int(s[2]))+int(s[4]) for s in states]
    signatures = []
    for index,s in enumerate(states):
        signatures.append((colors[index],tuple(tuple(sum(n for t,n in raw.row(rom,s,a)
            if colors[states.index(t)] == color) for color in range(32)) for a in (False,True))))
    distinct = list(dict.fromkeys(signatures))
    return {tuple(s):distinct.index(signature) for s,signature in zip(states,signatures)}


CLASSES = {rom:classes(rom) for rom in ('canonical32','flat32')}


def view(w,a):
    data = raw.binding(w,a)
    available = raw.binding(w,a,True) is not None
    if data is None:
        return dict(available=available,accepted=False,data=None)
    r,rom,key = data
    found = blocks(rom,a,r['receipts'])
    audited = epoch_valid(w,a,r,rom,key)
    count = len(r['receipts'])
    residue = [rom,r['birth'],r['birthCursor'],r['roots']]
    observation = [CLASSES[rom][tuple(r['state'])],count,r['state'][4],count,count,residue,w['charge'][key],a]
    return dict(available=available,accepted=available and rom == 'canonical32' and not r['state'][0] and audited and bool(found),
        data=dict(state=r['state'],key=key,audited=audited,blocks=found,cursor=w['cursor'][key],observation=observation))


def factor_table():
    def pre(rom,renew,state,charge,V):
        return not state[0] and any(charge and bool(rows := raw.row(rom,state,a)) and
            all(V(t,renew) for t,_ in rows) for a in (False,True))
    core = lambda s,c:not s[0] and c
    return [[[pre(rom,renew,list(s),c,lambda s,c:True),
              pre(rom,renew,list(s),c,core),core(list(s),c)]
             for s in product((False,True),repeat=5) for c in (False,True)]
            for rom in ('canonical32','flat32') for renew in (False,True)]


def reference():
    base = raw.reference()
    source,branches = base['worlds'][:2]
    endpoints = [[source,0],[branches,1],[branches,2]]+[[entry[0],3] for entry in base['mature']]
    checked = [view(w,a) for w,a in endpoints]
    assert all(v['accepted'] for v in checked)
    successors = [[[view(v,a),n] for v,n in raw.native(w,a)] for w,a in endpoints]
    assert all(entry[0]['accepted'] for rows in successors for entry in rows)
    probes = [[[view(v,a),n] for v,n in raw.native(w,a,True)] for w,a in endpoints]
    assert all(not entry[0]['accepted'] for rows in probes for entry in rows)
    absent = [[[view(v,a),n,len(raw.native(v,a,packet=False))] for v,n in raw.native(w,a,packet=False)] for w,a in endpoints]
    assert all(not e[0]['accepted'] and e[2] == 0 for rows in absent for e in rows)
    interleaved = [[view(v,1),n] for action in (False,True) for v,n in raw.native(branches,2,action)]
    assert all(e[0] == view(branches,1) for e in interleaved)
    # Account commutation; global event ordinals/versions are intentionally not identified.
    for l,_ in raw.native(branches,1):
        for lr,_ in raw.native(l,2,True):
            matching = [rl for r,_ in raw.native(branches,2,True) for rl,_ in raw.native(r,1)
                        if view(rl,1) == view(lr,1) and view(rl,2) == view(lr,2)]
            assert matching and matching[0]['cursor'] == lr['cursor'] and matching[0]['charge'] == lr['charge']
    tampered = copy(branches);tampered['residents'][1]['receipts'][0]['serial'] += 1
    mixed = copy(branches);mixed['residents'][1]['receipts'][0]['issuer']=['external']
    flat = raw.cycle(raw.initial('flat32'),0)
    controls = [view(raw.initial(),0),view(flat,0),view(tampered,1),view(mixed,1),view(base['worlds'][5],1)]
    assert [v['accepted'] for v in controls] == [False,False,False,False,True]
    cold = [view(e[0],3) for e in base['fusion']]
    assert all(v['available'] and not v['accepted'] for v in cold)
    fork = [[view(e[0],6) for e in entry[1]] for entry in base['mature']]
    assert all(v['available'] and not v['accepted'] for rows in fork for v in rows)
    # Actual supported three-key fusion, followed by differently ordered
    # raw selectors. Neither execution nor decoding may demand sorted input.
    uncut = raw.cycle(raw.cycle(raw.bootstrap(source),1),2)
    first = raw.fusion(uncut,raw.request(uncut,0,1,3))[0][0]
    aligned = raw.native(first,3)[0][0]
    three = raw.fusion(aligned,raw.request(aligned,3,2,4))[0][0]
    assert raw.keys(three,4) == [0,1,2]
    permutation_worlds = []
    for selector in ([2,0],[0,2]):
        w = raw.partition(three,4,5,6,selector,[1])
        phase = w['residents'][5]['state'][4]
        cycle = [[False,False,True,False,not phase],
                 [False,True,True,False,phase],
                 [False,False,False,False,not phase],
                 [False,False,True,False,phase],
                 [False,True,True,False,not phase],
                 [False,False,False,False,phase]]
        for state in cycle:
            w = next(v for v,_ in raw.native(w,5) if v['residents'][5]['state'] == state)
        assert raw.binding(w,5,True)[2] == 0 and view(w,5)['accepted']
        permutation_worlds.append(w)
    permutations = [view(w,5) for w in permutation_worlds]
    assert permutations[0] == permutations[1]
    permutation_successors = [[[view(v,5),n] for v,n in raw.native(w,5)] for w in permutation_worlds]
    assert permutation_successors[0] == permutation_successors[1]
    assert all(e[0]['accepted'] for rows in permutation_successors for e in rows)
    table = factor_table()
    assert all(entry[0] == entry[2] for rows in table for entry in rows)
    assert all(entry[1] == (entry[2] if index%2 else False) for index,rows in enumerate(table) for entry in rows)
    return dict(endpoints=checked,successors=successors,probes=probes,absent=absent,interleaved=interleaved,
        controls=controls,cold=cold,fork=fork,factors=table,permutations=permutations,permutation_successors=permutation_successors)


PROBE = raw.PROBE.split('def jw')[0].replace('import CSTTT.FullNative02.WarmupSupport',
    'import CSTTT.FullNative02.SelectorRegression') + r'''
def jobs (o : Temporal.Observation) : Lean.Json := Lean.Json.arr #[
  Lean.toJson o.predictive,Lean.toJson o.order,Lean.toJson o.tick,Lean.toJson o.progress,Lean.toJson o.record,
  Lean.Json.arr #[jrom o.residue.installed,jn o.residue.birth,Lean.toJson o.residue.birthCursor,
    Lean.toJson (o.residue.roots.map fun e => Lean.Json.arr #[jn e.1,Lean.toJson e.2])],
  Lean.toJson o.maintenance,Lean.toJson o.owner]
def jblock (rom : ROM) (rs : List Receipt) : Lean.Json := Lean.Json.arr #[
  Lean.toJson rs.length,Lean.toJson (rs.head?.map Receipt.cursor),
  Lean.toJson (Blocks.forward (Blocks.edge rom) Receipt.before Receipt.after rs),
  Lean.toJson (Blocks.backward (Blocks.edge rom) Receipt.before Receipt.after rs)]
def jdata (w : World) (a : Nat) (data : Resident × ROM × Token) : Lean.Json :=
  let r := data.1
  let rom := data.2.1
  let key := data.2.2
  Lean.Json.mkObj [("state",js r.current),("key",Lean.toJson key.val),
    ("audited",Lean.toJson (Epoch.valid w a r rom key)),
    ("cursor",Lean.toJson (w.accounts.cursor key)),
    ("observation",jobs (Temporal.observe (Temporal.frameROM w r rom key))),
    ("blocks",Lean.toJson (((Blocks.blocks r.receipts).filter (Blocks.qualifies rom a)).map (jblock rom)))]
def jview (w : World) (a : Nat) : Lean.Json := Lean.Json.mkObj [
  ("available",Lean.toJson (access w a).isSome),("accepted",Lean.toJson (Epoch.accept w a)),
  ("data",Lean.toJson ((binding w a).map (jdata w a)))]
def endpoints : List (World × Nat) := [(sourceWorld,0),(branchesWorld,1),(branchesWorld,2)]++
  (fusionRows renewable branchesWorld mainRequest).flatMap fun e =>
    (outputWarmup e.1.world).toList.map fun w => (w,3)
def jrows (supply : Supply) (action : Bool) (w : World) (owner : Nat) : Lean.Json :=
  Lean.toJson ((nativeRows supply w owner action).map fun e => Lean.Json.arr #[jview e.1 owner,Lean.toJson e.2])
def jabsent (w : World) (a : Nat) : Lean.Json :=
  Lean.toJson ((nativeRows absent w a false).map fun v =>
    Lean.Json.arr #[jview v.1 a,Lean.toJson v.2,Lean.toJson (nativeRows absent v.1 a false).length])
def result : Lean.Json := Lean.Json.mkObj [
  ("endpoints",Lean.toJson (endpoints.map fun e => jview e.1 e.2)),
  ("successors",Lean.toJson (endpoints.map fun e => jrows renewable false e.1 e.2)),
  ("probes",Lean.toJson (endpoints.map fun e => jrows renewable true e.1 e.2)),
  ("absent",Lean.toJson (endpoints.map fun e => jabsent e.1 e.2)),
  ("interleaved",Lean.toJson (bits.flatMap fun a => (nativeRows renewable branchesWorld 2 a).map fun e =>
    Lean.Json.arr #[jview e.1 1,Lean.toJson e.2])),
  ("controls",Lean.toJson [jview (initial 8) 0,jview flatWorld 0,jview (tamperedTail branchesWorld 1) 1,
    jview (mixedEpoch branchesWorld 1) 1,jview twinWorld 1]),
  ("cold",Lean.toJson ((fusionRows renewable branchesWorld mainRequest).map fun e => jview e.1.world 3)),
  ("fork",Lean.toJson ((fusionRows renewable branchesWorld mainRequest).flatMap fun e =>
    (outputWarmup e.1.world).toList.flatMap fun w => (strongerFork w).toList.map fun rows =>
      Lean.toJson (rows.map fun v => jview v.1.world 6))),
  ("permutations",Lean.toJson ([SelectorRegression.unsortedWorld,SelectorRegression.sortedWorld].map fun w => jview w 5)),
  ("permutation_successors",Lean.toJson ([SelectorRegression.unsortedWorld,SelectorRegression.sortedWorld].map fun w => jrows renewable false w 5)),
  ("factors",Lean.toJson ([ROM.canonical32,ROM.flat32].flatMap fun rom => bits.map fun renew =>
    Lean.toJson (CSTTT.FullNative.Viability.carrier.map fun q => [
      CSTTT.FullNative02.Viability.pre rom renew (fun _ => true) q,
      CSTTT.FullNative02.Viability.pre rom renew CSTTT.FullNative02.Viability.core q,
      CSTTT.FullNative02.Viability.core q])))]
#eval result.compress
'''


def main():
    freeze=json.loads((ROOT/'audit/proposed_models/G30-full-native-02.model.json').read_text())
    pins=freeze['baseline']['source_sha256']
    old=json.loads((ROOT/'audit/G31a_full_native_fusion_declarations.json').read_text())
    for name,digest in {**pins,**old['source_sha256']}.items():
        if name != 'cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv':
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name+' baseline drift'
    logs=ROOT/'lean/.validate-logs'
    probe=logs/'G31bAutonomyTranscriptionProbe.lean';probe.write_text(PROBE)
    run=subprocess.run(['lake','env','lean',str(probe)],cwd=ROOT/'lean',capture_output=True,text=True)
    (logs/'G31b-transcription.log').write_text(run.stdout+run.stderr)
    if run.returncode:
        raise RuntimeError('Lean readout failed: lean/.validate-logs/G31b-transcription.log')
    actual=json.loads(json.loads(run.stdout.strip()))
    raw.compare(actual,reference())
    print('G31b transcription passed: 11 credited endpoints; 88 maintenance, 11 probe and 88 absent successors;')
    print('Selector permutation regression passed: both three-key acquisitions + all16 positive maintenance successors.')
    print('9 interleaved foreign responses; 8 cold + 64 stronger-fork newborns; 256 ROM/supply/charge factors; frozen pins unchanged.')


if __name__ == '__main__':
    main()
