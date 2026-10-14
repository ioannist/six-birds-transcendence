#!/usr/bin/env python3
"""G31a: independent frozen-ROM, owned-protocol and rational-meeting readouts.

Finite transcription supplements (does not replace) the universal kernel
history, ownership, normalization and least-ancestry proofs. No certificate,
issuer, normalizer, relation or package verdict is supplied to either runtime.
"""
from copy import deepcopy as copy
from fractions import Fraction as F
from itertools import product
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FREEZE = ROOT/'audit/proposed_models/G30-full-native-02.model.json'
G17 = json.loads((ROOT/'audit/proposed_models/G17-full-native-package.model.json').read_text())
MATRIX = G17['primitive_dynamics']['inside_maintenance_weights']
ZERO = [False]*5
CYCLE = [[False,False,True,False,True], [False,True,True,False,False],
         [False,False,False,False,True], [False,False,True,False,False],
         [False,True,True,False,True], ZERO]


def node(tag, n):
    return [tag, n]


def row(rom, state, action):
    outside,u,v,replica,phase = state
    if action:
        return [[[True,u,v,replica,not phase],16]]
    weights = [2]*4 if outside or rom == 'flat32' else MATRIX[2*int(u)+int(v)]
    return [[[False,x,y,r,not phase],weights[2*int(x)+int(y)]]
            for x,y in product((False,True), repeat=2) for r in (False,True)]


def resident(a, rom, state, born, cursor, roots):
    return dict(owner=a,rom=rom,state=copy(state),birth=born,version=born,
                birthCursor=cursor,roots=roots,receipts=[])


def initial(rom='canonical32'):
    return dict(inventory=8,residents=[resident(0,rom,ZERO,node('birth',0),0,[])]+[None]*7,
                fresh=[False]+[True]*7,custody=[['local',0],['unallocated'],['unallocated'],['external']],
                charge=[True]*4,cursor=[0]*4,slots=[None]*8,
                events=[['boot',0,rom,0,0]],acquisition=True)


def keys(w,a):
    return [t for t,c in enumerate(w['custody']) if c == ['local',a]]


def authenticated(w,a,r):
    tag,n = r['version'] if r['version'][0] != 'prospective' else ('prospective',-1)
    if not 0 <= n < len(w['events']):
        return False
    e = w['events'][n]
    if tag == 'version':
        return e[0] == 'native' and bool(r['receipts']) and e[2] == r['receipts'][-1] and (
            e[2]['owner'], e[2]['rom'], e[2]['after']) == (a,r['rom'],r['state'])
    if tag != 'birth' or r['birth'] != r['version'] or r['receipts']:
        return False
    if e[0] == 'boot':
        return (e[1],e[2],ZERO) == (a,r['rom'],r['state'])
    if e[0] == 'activation':
        return (e[2],e[3],e[6]) == (a,r['rom'],r['state'])
    if e[0] == 'partition':
        return (e[2],e[3],e[5]) == (a,r['rom'],r['state'])
    if e[0] == 'fusion':
        return (e[3],e[4],e[7]['after']) == (a,r['rom'],r['state']) and e[7]['after'] == e[8]['after']
    return False


def binding(w,a,charged=False):
    if not 0 <= a < w['inventory']:
        return None
    r = w['residents'][a]
    owned = keys(w,a)
    if r is None or r['rom'] is None or not owned or r['owner'] != a or not authenticated(w,a,r):
        return None
    return (r,r['rom'],owned[0]) if not charged or w['charge'][owned[0]] else None


def fresh(w,a):
    return 0 <= a < w['inventory'] and w['fresh'][a] and w['residents'][a] is None and w['slots'][a] is None


def advance(w,a,r,rom,key,action,edge,prob=None,packet=True):
    v=copy(w)
    state,weight=edge
    cursor=w['cursor'][key]
    receipt=dict(issuer=copy(w['custody'][key]),owner=a,token=key,cursor=cursor,
                 serial=4*cursor+key,rom=rom,before=copy(r['state']),after=copy(state),
                 action=action,weight=weight,packet=packet)
    nxt=copy(r); nxt['state']=copy(state); nxt['version']=node('version',len(w['events']))
    nxt['receipts'].append(receipt); v['residents'][a]=nxt
    v['cursor'][key]+=1; v['charge'][key]=packet
    v['events'].append(['native',r['version'],receipt,prob])
    return v


def native(w,a,action=False,packet=True):
    data=binding(w,a,True)
    if data is None:
        return []
    r,rom,key=data
    return [[advance(w,a,r,rom,key,action,e,packet=packet),e[1]] for e in row(rom,r['state'],action)]


def cycle(w,a):
    for state in CYCLE:
        matches=[v for v,_ in native(w,a) if v['residents'][a]['state'] == state]
        assert matches, 'missing actual native support'
        w=matches[0]
    return w


def capture(w,a):
    data=binding(w,a,True)
    if data is None:
        return None
    r,rom,key=data
    if not r['receipts'] or r['version'][0] != 'version':
        return None
    receipt=r['receipts'][-1]; e=w['events'][r['version'][1]]
    if e[0] != 'native' or e[2] != receipt or e[3] is not None or receipt['issuer'] != ['local',a] or (
            receipt['token'],receipt['rom'],receipt['after'],receipt['cursor']+1,receipt['serial']) != (
            key,rom,r['state'],w['cursor'][key],4*receipt['cursor']+key) or [receipt['after'],receipt['weight']] not in row(rom,receipt['before'],receipt['action']):
        return None
    return dict(program=rom,state=copy(r['state']),sourceVersion=r['version'],order=len(r['receipts']),
                count=len(r['receipts']),serial=receipt['serial'],receipt=copy(receipt),event=node('event',len(w['events'])))


def snapshot(w,source=0,left=1,right=2):
    c=capture(w,source)
    if c is None or not w['acquisition'] or not fresh(w,left) or not fresh(w,right) or left == right or (
        w['custody'][1:] [:2] != [['unallocated'],['unallocated']]) or not w['charge'][1] or not w['charge'][2]:
        return None
    v=copy(w)
    for a,t in ((left,1),(right,2)):
        v['slots'][a]=dict(recipient=a,key=t,capture=copy(c));v['custody'][t]=['reserved',a]
    v['events'].append(['snapshot',c['sourceVersion'],c['receipt'],left,right,c['count']])
    return v


def activate(w,a):
    if not 0 <= a < w['inventory']:
        return None
    s=w['slots'][a]
    if s is None or s['recipient'] != a or w['custody'][s['key']] != ['reserved',a] or not w['fresh'][a] or w['residents'][a] is not None:
        return None
    c=s['capture'];tag,n=c['event']
    if tag != 'event' or not 0 <= n < len(w['events']):
        return None
    e=w['events'][n]
    if e[0] != 'snapshot' or (e[1],e[2],e[5],e[5]) != (c['sourceVersion'],c['receipt'],c['order'],c['count']) or a not in e[3:5] or (
        c['receipt']['after'],c['receipt']['rom'],c['receipt']['serial']) != (c['state'],c['program'],c['serial']):
        return None
    v=copy(w);t=s['key'];v['residents'][a]=resident(a,c['program'],c['state'],node('birth',len(w['events'])),w['cursor'][t],[[c['sourceVersion'],c['count']]])
    v['slots'][a]=None;v['fresh'][a]=False;v['custody'][t]=['local',a]
    v['events'].append(['activation',c['event'],a,c['program'],t,w['cursor'][t],c['state']]);return v


def bootstrap(w):
    v=snapshot(w)
    if v is None:
        return None
    v=activate(v,1)
    return None if v is None else activate(v,2)


def retire(w,withdraw=False):
    v=copy(w);v['residents'][0]=None
    v['custody']=[['retired'] if c == ['local',0] or (withdraw and c == ['external']) else c for c in v['custody']]
    if withdraw:
        v['slots']=[None]*v['inventory'];v['acquisition']=False
    return v


def boot(w,a,t,rom):
    if not w['acquisition'] or not fresh(w,a) or w['custody'][t] != ['unallocated'] or not w['charge'][t]:
        return None
    v=copy(w);v['residents'][a]=resident(a,rom,ZERO,node('birth',len(w['events'])),w['cursor'][t],[])
    v['fresh'][a]=False;v['custody'][t]=['local',a];v['events'].append(['boot',a,rom,t,w['cursor'][t]]);return v


def partition(w,parent,left,right,xs,ys):
    data=binding(w,parent)
    if data is None or not xs or not ys or len(set(xs)) != len(xs) or len(set(ys)) != len(ys) or set(xs)&set(ys) or set(xs)|set(ys) != set(keys(w,parent)) or left == right or not fresh(w,left) or not fresh(w,right):
        return None
    r,rom,_=data;v=copy(w);v['residents'][parent]=None
    for n,(a,ts) in enumerate(((left,xs),(right,ys))):
        v['residents'][a]=resident(a,rom,r['state'],node('birth',len(w['events'])+n),w['cursor'][min(ts)],[[r['version'],len(r['receipts'])]])
        v['fresh'][a]=False
        for t in ts:v['custody'][t]=['local',a]
        v['events'].append(['partition',r['version'],a,rom,ts,r['state']])
    return v


def request(w,left=1,right=2,output=3,a=False,b=False):
    return dict(left=left,right=right,output=output,a=a,b=b,lv=w['residents'][left]['version'],rv=w['residents'][right]['version'])


def parents(w,q):
    l=binding(w,q['left'],True);r=binding(w,q['right'],True)
    if l is None or r is None or q['left'] == q['right'] or l[1] != r[1] or l[2] == r[2] or l[0]['version'] != q['lv'] or r[0]['version'] != q['rv'] or not fresh(w,q['output']):
        return None
    return l,r,min(keys(w,q['left'])+keys(w,q['right']))


def prospective(q):
    return ['prospective',q['lv'],q['rv'],q['a'],q['b'],q['output']]


def fusion(w,q):
    p=parents(w,q)
    if p is None:return []
    (l,rom,lk),(r,_,rk),outkey=p
    lr=row(rom,l['state'],q['a']);rr=row(rom,r['state'],q['b'])
    pairs=[(x,y) for x in lr for y in rr if x[0] == y[0]]
    mass=sum(x[1]*y[1] for x,y in pairs)
    if not mass:
        diagnostic=[q,prospective(q),rom,[[x[0],x[1],i] for i,x in enumerate(lr)],[[x[0],x[1],i] for i,x in enumerate(rr)],0]
        return [[copy(w),['empty',prospective(q)],F(1),diagnostic,None]]
    outcomes=[]
    for x,y in pairs:
        probability=F(x[1]*y[1],mass)
        first=advance(w,q['left'],l,rom,lk,q['a'],x,probability)
        paid=advance(first,q['right'],r,rom,rk,q['b'],y,probability)
        leftReceipt=first['events'][-1][2];rightReceipt=paid['events'][-1][2]
        n=len(paid['events']);v=copy(paid)
        v['residents'][q['left']]=None;v['residents'][q['right']]=None
        v['residents'][q['output']]=resident(q['output'],rom,x[0],node('birth',n),paid['cursor'][outkey],
            [[node('version',len(w['events'])),len(l['receipts'])+1],[node('version',len(w['events'])+1),len(r['receipts'])+1]])
        v['fresh'][q['output']]=False
        v['custody']=[['local',q['output']] if c in (['local',q['left']],['local',q['right']]) else c for c in paid['custody']]
        v['events'].append(['fusion',node('version',len(w['events'])),node('version',len(w['events'])+1),q['output'],rom,
                            keys(w,q['left']),keys(w,q['right']),leftReceipt,rightReceipt,probability])
        receipt=[q,l['birth'],r['birth'],l['roots'],r['roots'],len(l['receipts']),len(r['receipts']),lr.index(x),rr.index(y),mass,probability,leftReceipt,rightReceipt,node('birth',n),keys(w,q['left']),keys(w,q['right'])]
        outcomes.append([v,['created',node('birth',n)],probability,None,receipt])
    assert sum(e[2] for e in outcomes) == 1
    return outcomes


def reference():
    source=cycle(initial(),0);copied=bootstrap(source)
    beforeCut=cycle(cycle(copied,1),2);branches=retire(beforeCut,True)
    q=request(branches);outputs=fusion(branches,q);fused=outputs[0][0]
    pool=partition(fused,3,4,5,[1],[2]);refusion=fusion(pool,request(pool,4,5,6))
    staged=snapshot(source);gap=activate(activate(retire(staged),1),2)
    phase=native(branches,1)[0][0]
    assert phase['residents'][1]['state'] == [False,False,False,False,True]
    twin=cycle(boot(source,1,1,'canonical32'),1)
    zero=retire(fusion(beforeCut,request(beforeCut,0,1,3))[0][0],True)
    unequal=boot(boot(initial(),1,1,'canonical32'),2,2,'flat32')
    empty=[fusion(branches,request(branches,b=True)),fusion(phase,request(phase))]
    missing=copy(branches);missing['residents'][1]['rom']=None
    wrong=copy(branches);wrong['custody'][1]=['external']
    alias=copy(branches);alias['custody'][2]=['local',1]
    disabled=copy(branches);disabled['charge'][1]=False
    forged=copy(branches);forged['residents'][1]['version']=node('version',999)
    fq=copy(q);fq['lv']=node('version',999)
    malformed=copy(staged);malformed['slots'][1]['capture']['count']=99
    aliased=copy(staged);aliased['slots'][2]['key']=1
    checks=[parents(missing,q) is None,parents(wrong,q) is None,parents(alias,q) is None,
            parents(disabled,q) is None,parents(forged,fq) is None,
            parents(unequal,request(unequal)) is None,activate(malformed,1) is None,
            activate(aliased,2) is None,partition(fused,3,4,5,[],[1,2]) is None,
            partition(fused,3,4,5,[1],[1,2]) is None,partition(fused,3,4,4,[1],[2]) is None,
            boot(staged,3,1,'canonical32') is None,boot(branches,4,0,'canonical32') is None]
    assert all(checks)
    mature=[]
    for out in outputs:
        entrance=native(out[0],3)[0][0]
        assert entrance['residents'][3]['state'] == ZERO
        warmed=cycle(entrance,3)
        divided=partition(warmed,3,4,5,[1],[2])
        forked=fusion(divided,request(divided,4,5,6))
        mature.append([warmed,[[e[0],e[1],e[2]] for e in forked]])
    tables=[[[row(rom,list(s),a) for a in (False,True)] for s in product((False,True),repeat=5)] for rom in ('canonical32','flat32')]
    return dict(rows=tables,worlds=[source,branches,fused,pool,gap,twin,zero,unequal],
                fusion=outputs,refusion=refusion,empty=empty,absent=native(initial(),0,packet=False),checks=checks,mature=mature)


PROBE = r'''import CSTTT.FullNative02.WarmupSupport
import CSTTT.FullNative02.HousedAccounts
open CSTTT.FullNative02
open CSTTT.FullNative
instance : Lean.ToJson Rat where
  toJson r := Lean.toJson (if r.den=1 then toString r.num else toString r.num ++ "/" ++ toString r.den)
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
def js (s : State) : Lean.Json := Lean.toJson [s.outside,s.u,s.v,s.replica,s.phase]
def jrom (r : ROM) : Lean.Json := Lean.toJson (match r with | .canonical32 => "canonical32" | .flat32 => "flat32")
def jc : Custody → Lean.Json
  | .local a => Lean.Json.arr #[Lean.toJson "local",Lean.toJson a]
  | .reserved a => Lean.Json.arr #[Lean.toJson "reserved",Lean.toJson a]
  | .unallocated => Lean.toJson ["unallocated"]
  | .external => Lean.toJson ["external"]
  | .retired => Lean.toJson ["retired"]
def jn : Node → Lean.Json
  | .birth n => Lean.Json.arr #[Lean.toJson "birth",Lean.toJson n]
  | .event n => Lean.Json.arr #[Lean.toJson "event",Lean.toJson n]
  | .version n => Lean.Json.arr #[Lean.toJson "version",Lean.toJson n]
  | .hardware n => Lean.Json.arr #[Lean.toJson "hardware",Lean.toJson n]
  | .prospective l r a b out => Lean.Json.arr #[Lean.toJson "prospective",jn l,jn r,Lean.toJson a,Lean.toJson b,Lean.toJson out]
def jr (r : Receipt) : Lean.Json := Lean.Json.mkObj [
  ("issuer",jc r.issuer),("owner",Lean.toJson r.owner),("token",Lean.toJson r.token.val),
  ("cursor",Lean.toJson r.cursor),("serial",Lean.toJson r.serial),("rom",jrom r.rom),
  ("before",js r.before),("after",js r.after),("action",Lean.toJson r.action),
  ("weight",Lean.toJson r.weight),("packet",Lean.toJson r.packet.isSome)]
def jresident (r : Resident) : Lean.Json := Lean.Json.mkObj [
  ("owner",Lean.toJson r.owner),("rom",Lean.toJson (r.installed.map jrom)),("state",js r.current),
  ("birth",jn r.birth),("version",jn r.version),("birthCursor",Lean.toJson r.birthCursor),
  ("roots",Lean.toJson (r.roots.map fun e => Lean.Json.arr #[jn e.1,Lean.toJson e.2])),
  ("receipts",Lean.toJson (r.receipts.map jr))]
def jcapture (c : Capture) : Lean.Json := Lean.Json.mkObj [
  ("program",jrom c.program),("state",js c.current),("sourceVersion",jn c.sourceVersion),
  ("order",Lean.toJson c.order),("count",Lean.toJson c.count),("serial",Lean.toJson c.serial),
  ("receipt",jr c.receipt),("event",jn c.event)]
def jslot (s : Slot) : Lean.Json := Lean.Json.mkObj [
  ("recipient",Lean.toJson s.recipient),("key",Lean.toJson s.key.val),("capture",jcapture s.capture)]
def je : Event → Lean.Json
  | .boot a rom t c => Lean.Json.arr #[Lean.toJson "boot",Lean.toJson a,jrom rom,Lean.toJson t.val,Lean.toJson c]
  | .native before r p => Lean.Json.arr #[Lean.toJson "native",jn before,jr r,Lean.toJson p]
  | .snapshot source r l right c => Lean.Json.arr #[Lean.toJson "snapshot",jn source,jr r,Lean.toJson l,Lean.toJson right,Lean.toJson c]
  | .activation source a rom t c s => Lean.Json.arr #[Lean.toJson "activation",jn source,Lean.toJson a,jrom rom,Lean.toJson t.val,Lean.toJson c,js s]
  | .partition parent a rom ts s => Lean.Json.arr #[Lean.toJson "partition",jn parent,Lean.toJson a,jrom rom,Lean.toJson (ts.map Fin.val),js s]
  | .fusion l r a rom xs ys lr rr p => Lean.Json.arr #[Lean.toJson "fusion",jn l,jn r,Lean.toJson a,jrom rom,Lean.toJson (xs.map Fin.val),Lean.toJson (ys.map Fin.val),jr lr,jr rr,Lean.toJson p]
def jw (w : World) : Lean.Json := Lean.Json.mkObj [
  ("inventory",Lean.toJson w.inventory),
  ("residents",Lean.toJson ((List.range w.inventory).map fun a => (w.residents a).map jresident)),
  ("fresh",Lean.toJson ((List.range w.inventory).map w.fresh)),
  ("custody",Lean.toJson (tokens.map fun t => jc (w.accounts.custody t))),
  ("charge",Lean.toJson (tokens.map w.accounts.charge)),("cursor",Lean.toJson (tokens.map w.accounts.cursor)),
  ("slots",Lean.toJson ((List.range w.inventory).map fun a => (w.slots a).map jslot)),
  ("events",Lean.toJson (w.events.map je)),("acquisition",Lean.toJson w.acquisition)]
def jq (q : FusionRequest) : Lean.Json := Lean.Json.mkObj [
  ("left",Lean.toJson q.left),("right",Lean.toJson q.right),("output",Lean.toJson q.output),
  ("a",Lean.toJson q.leftAction),("b",Lean.toJson q.rightAction),("lv",jn q.leftVersion),("rv",jn q.rightVersion)]
def jedge (e : Edge) : Lean.Json := Lean.Json.arr #[js e.state,Lean.toJson e.weight,Lean.toJson e.index]
def jd (d : EmptyReceipt) : Lean.Json := Lean.Json.arr #[jq d.request,jn d.reference,jrom d.rom,
  Lean.toJson (d.leftRows.map jedge),Lean.toJson (d.rightRows.map jedge),Lean.toJson d.mass]
def jpaid (p : PaidFusionReceipt) : Lean.Json := Lean.Json.arr #[
  jq p.request,jn p.leftBirth,jn p.rightBirth,
  Lean.toJson (p.leftRoots.map fun e => Lean.Json.arr #[jn e.1,Lean.toJson e.2]),
  Lean.toJson (p.rightRoots.map fun e => Lean.Json.arr #[jn e.1,Lean.toJson e.2]),
  Lean.toJson p.leftOrder,Lean.toJson p.rightOrder,Lean.toJson p.leftIndex,Lean.toJson p.rightIndex,
  Lean.toJson p.mass,Lean.toJson p.probability,jr p.leftReceipt,jr p.rightReceipt,jn p.outputBirth,
  Lean.toJson (p.leftKeys.map Fin.val),Lean.toJson (p.rightKeys.map Fin.val)]
def jk : OutcomeKind → Lean.Json
  | .created n => Lean.Json.arr #[Lean.toJson "created",jn n]
  | .empty n => Lean.Json.arr #[Lean.toJson "empty",jn n]
def jo (supply : Supply) (w : World) (q : FusionRequest) : Lean.Json :=
  Lean.toJson ((fusionExecution supply w q).map fun e => Lean.Json.arr #[jw e.1.settlement.world,
    jk e.1.settlement.kind,
    Lean.toJson e.2,Lean.toJson (e.1.empty.map jd),Lean.toJson (e.1.paid.map jpaid)])
def tables : Lean.Json := Lean.toJson ([ROM.canonical32,ROM.flat32].map fun rom =>
  Lean.toJson (states.map fun s => Lean.toJson (bits.map fun a =>
    Lean.toJson ((rom.program.rows s a).map fun e => Lean.Json.arr #[js e.1,Lean.toJson e.2]))))
def checks : List Bool := [
  (parentView missingProgram mainRequest).isNone,(parentView wrongCustody mainRequest).isNone,
  (parentView aliasedCustody mainRequest).isNone,(parentView disabledKey mainRequest).isNone,
  (parentView forgedVersion {mainRequest with leftVersion := .version 999}).isNone,
  (parentView unequalBootWorld unequalBootRequest).isNone,(activate malformedCapture 1).isNone,
  (activate aliasedSlot 2).isNone,(partition fused 3 4 5 [] [1,2]).isNone,
  (partition fused 3 4 5 [1] [1,2]).isNone,(partition fused 3 4 4 [1] [2]).isNone,
  (boot stageWorld 3 1 .canonical32).isNone,(boot branchesWorld 4 0 .canonical32).isNone]
def mature : Lean.Json := Lean.toJson ((fusionRows renewable branchesWorld mainRequest).map fun e =>
  Lean.toJson ((outputWarmup e.1.world).toList.map fun v => Lean.Json.arr #[jw v,
    Lean.toJson ((strongerFork v).toList.map fun rows => Lean.toJson (rows.map fun next =>
      Lean.Json.arr #[jw next.1.world,jk next.1.kind,Lean.toJson next.2]))]))
def snapshot : Lean.Json := Lean.Json.mkObj [
  ("rows",tables),("worlds",Lean.toJson ([sourceWorld,branchesWorld,fused,poolWorld,
    gapRun.get destructive_gap_available,twinWorld,withdraw tokenZeroFused,unequalBootWorld].map jw)),
  ("fusion",jo renewable branchesWorld mainRequest),("refusion",jo renewable poolWorld poolRequest),
  ("empty",Lean.toJson [jo renewable branchesWorld probeRequest,jo renewable phaseWorld phaseRequest]),
  ("absent",Lean.toJson (absentFirst.map fun e => Lean.Json.arr #[jw e.1,Lean.toJson e.2])),
  ("checks",Lean.toJson checks),("mature",mature)]
#eval snapshot.compress
'''


def compare(got,want,path='root'):
    if type(got) != type(want):
        raise AssertionError(f'{path}: type mismatch {type(got).__name__}/{type(want).__name__}')
    if isinstance(got,dict):
        assert got.keys() == want.keys(), path+' keys'
        for k in got:compare(got[k],want[k],path+'.'+k)
    elif isinstance(got,list):
        assert len(got) == len(want), f'{path}: lengths {len(got)}/{len(want)}'
        for i,(a,b) in enumerate(zip(got,want)):compare(a,b,f'{path}[{i}]')
    else:
        assert got == want, f'{path}: {got!r} != {want!r}'


def main():
    freeze=json.loads(FREEZE.read_text())
    pins=freeze['baseline']['source_sha256']
    # Registry adjudication is an authorized metadata change, never a raw-model change.
    for name,digest in pins.items():
        if name != 'cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv':
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name+' baseline drift'
    logs=ROOT/'lean/.validate-logs';probe=logs/'G31aFusionTranscriptionProbe.lean';probe.write_text(PROBE)
    run=subprocess.run(['lake','env','lean',str(probe)],cwd=ROOT/'lean',capture_output=True,text=True)
    (logs/'G31a-fusion-transcription.log').write_text(run.stdout+run.stderr)
    if run.returncode:raise RuntimeError('Lean probe failed: lean/.validate-logs/G31a-fusion-transcription.log')
    got=json.loads(json.loads(run.stdout.strip()))
    got['mature']=[[entry[0][0],entry[0][1][0]] for entry in got['mature']]
    expected=json.loads(json.dumps(reference(),default=lambda n:str(n) if isinstance(n,F) else (_ for _ in ()).throw(TypeError(type(n)))))
    compare(got,expected)
    print('G31a transcription passed: 128 ROM/action rows, 8 complete worlds, all 8 fusion + 8 refusion outputs,')
    print('2 unchanged-world empty diagnostics, 8 initially stored absent steps, 13 rejection controls; 48 frozen source pins match.')
    print('All 8 outputs complete the frozen own 7-step warmup; all 64 subsequent stronger-fork fusion worlds match.')


if __name__ == '__main__':
    main()
