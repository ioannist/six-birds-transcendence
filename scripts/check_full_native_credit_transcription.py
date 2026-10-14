#!/usr/bin/env python3
"""Rebuild actual six-edge receipts, copy provenance, credit and funding controls."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def references():
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    matrix = frozen["primitive_dynamics"]["inside_maintenance_weights"]
    states = list(product((False, True), repeat=5))
    cycle = [(False,False,False,False,False),(False,False,True,False,True),
             (False,True,True,False,False),(False,False,False,False,True),
             (False,False,True,False,False),(False,True,True,False,True)]

    def rows(s, action, flat=False):
        out,u,v,replica,phase=s
        if action:
            return [((True,u,v,replica,not phase),16)]
        weights=[2]*4 if flat or out else matrix[2*int(u)+int(v)]
        return [((False,x,y,r,not phase),weights[k])
                for k,(x,y) in enumerate(product((False,True),repeat=2)) for r in (False,True)]

    def carrier(owner, flip=False, root_serial=None, flat=False, mode="native"):
        physical=[(s[0],s[1],s[2],s[3],not s[4]) if flip else s for s in cycle]
        following=physical[1:]+physical[:1]
        receipts=[]
        cursors={owner:0,3:0}
        forward=F(1);reverse=F(1)
        for index,(s,t) in enumerate(zip(physical,following)):
            bridge=mode=="bridge" or mode=="mixed" and index>0
            token=3 if bridge else owner
            actor=["bridge",None] if bridge else ["local",owner]
            n=next(n for q,n in rows(s,False,flat) if q==t)
            back=next(n for q,n in rows(t,False,flat) if q==s)
            forward*=F(n,16);reverse*=F(back,16)
            receipts.insert(0,[actor,token,4*cursors[token]+token,list(s),list(t),False,n,True])
            cursors[token]+=1
        local_credit="rejected" if mode in ("bridge","mixed") else "neutral" if flat else "self"
        bridge_credit="other" if mode=="bridge" else "rejected"
        root_states=[] if root_serial is None else [list(physical[0])]
        roots=[] if root_serial is None else [root_serial]
        program=None if mode=="bridge" else [
            [[list(t),n] for t,n in rows(s,a,flat)] for s in states for a in (False,True)]
        return [list(physical[0]),owner,owner,6,6,root_states,roots,True,cursors[owner],
                receipts,local_credit,bridge_credit,forward,reverse,program]

    values=[carrier(0),carrier(1,True,0),carrier(2,True,0),carrier(1,False,20),
            carrier(2,False,20),carrier(0,flat=True),carrier(1,True,0,mode="bridge"),
            carrier(1,True,0,mode="mixed")]
    transfer=[[False,False,False,False,False],20,0,0,True,True,6,0,0]
    controls=[8,0,False,False]
    return [values,transfer,controls]


def evaluate():
    folder=ROOT / "lean/.validate-logs"
    probe=folder / "G23CreditTranscriptionProbe.lean"
    probe.write_text("""import CSTTT.FullNative.DriveClock
open CSTTT.FullNative CSTTT.FullNative.Credit
open CSTTT.FullNative.PhysicalExecution CSTTT.FullNative.SnapshotExecution CSTTT.FullNative.AccountExecution
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def rat (r : Rat) : Lean.Json := Lean.toJson (toString r)
def actor (a : Actor) : Lean.Json := match a with
  | .bridge => Lean.Json.arr #[Lean.toJson "bridge",Lean.Json.null]
  | .localGenerator o => Lean.Json.arr #[Lean.toJson "local",Lean.toJson o.val]
def credit (v : CreditVerdict) : String := match v with
  | .self => "self" | .other => "other" | .neutral => "neutral" | .rejected => "rejected"
def receipt (r : Receipt) : Lean.Json := Lean.Json.arr #[actor r.issuer,Lean.toJson r.token.val,
  Lean.toJson r.serial,Lean.toJson (encode r.before),Lean.toJson (encode r.after),
  Lean.toJson r.action,Lean.toJson r.weight,Lean.toJson r.energy.isSome]
def data (w : World) (o : Owner) (useBridge : Bool) : Lean.Json := match w.carriers o with
  | none => Lean.Json.null
  | some p =>
    let program := if useBridge then w.bridge else p.installed
    Lean.Json.arr #[Lean.toJson (encode p.current),Lean.toJson p.owner.val,Lean.toJson p.token.val,
      Lean.toJson (p.orderBase+p.receipts.length),Lean.toJson p.receipts.length,
      Lean.toJson (p.rootedRoute.1.map encode),Lean.toJson p.rootedRoute.2,
      Lean.toJson (w.accounts.charge p.token),Lean.toJson (w.accounts.portCursor p.token),
      Lean.toJson (p.receipts.map receipt),Lean.toJson ((localCredit w o).map credit),
      Lean.toJson ((bridgeCredit w o).map credit),
      Lean.toJson (program.map fun d => rat (forwardReceipts d p.receipts)),
      Lean.toJson (program.map fun d => rat (reverseReceipts d p.receipts)),
      Lean.toJson (p.installed.map fun d => states.flatMap fun s => bits.map fun a =>
        (d.rows s a).map fun e => (encode e.1,e.2))]
def transferData : Lean.Json := Lean.Json.arr #[
  Lean.toJson ((creditedTransferWorld.carriers 1).map Local.current |>.map encode),
  Lean.toJson ((creditedTransferWorld.carriers 1).map Local.rootedRoute |>.map (fun r => r.2.head?)),
  Lean.toJson ((creditedTransferWorld.carriers 1).map (fun p => p.receipts.length)),
  Lean.toJson ((creditedTransferWorld.carriers 2).map (fun p => p.receipts.length)),
  Lean.toJson (creditedTransferWorld.carriers 0).isNone,Lean.toJson creditedTransferWorld.bridge.isNone,
  Lean.toJson (creditedTransferWorld.accounts.portCursor 0),
  Lean.toJson (creditedTransferWorld.accounts.portCursor 1),Lean.toJson (creditedTransferWorld.accounts.portCursor 2)]
def disabled : World := {initialWorld with carriers := (putOwner initialWorld.carriers 0
  (some {source.resident with installed:=none}))}
def snapshot : Lean.Json := Lean.Json.arr #[Lean.toJson [
  data sourceCycleWorld 0 false,data sequentialCyclesWorld 1 false,data sequentialCyclesWorld 2 false,
  data creditedBothWorld 1 false,data creditedBothWorld 2 false,data flatCycleWorld 0 false,
  data scheduledCycleWorld 1 true,data mixedCycleWorld 1 false],transferData,
  Lean.Json.arr #[Lean.toJson (nativeRows absentSupply initialWorld 0 false).length,
    Lean.toJson (nativeRows absentSupply (mount initialWorld 0
      (advance absentSupply source false FullInterface.replicaLeft 1)) 0 false).length,
    Lean.toJson (runWith absentSupply initialWorld 0 sourcePlan).isSome,
    Lean.toJson (runWith renewable disabled 0 sourcePlan).isSome]]
#eval snapshot.compress
""")
    run=subprocess.run(["lake","env","lean",str(probe)],cwd=ROOT / "lean",
                       capture_output=True,text=True,check=True)
    (folder / "G23CreditTranscriptionProbe.log").write_text(run.stdout+run.stderr)
    value=json.loads(json.loads(run.stdout.strip()))

    def decode(x):
        if isinstance(x,str) and (x.isdigit() or "/" in x):
            return F(x)
        if isinstance(x,list):
            return [decode(y) for y in x]
        return x
    return decode(value)


def main():
    expected=references();actual=evaluate()
    assert actual==expected,"actual cycle/credit/copied-program/provenance/funding drift"
    print("PASS: eight actual native/flat/bridge/mixed histories, all 48 complete receipts and exact path products")
    print("PASS: actual source receipt20 copy/consume, both autonomous issuer/port histories, complete installed program rows")
    print("PASS: absent energy permits the initially charged step then stops; missing generator stops immediately")
    mutations=[]
    wrong=deepcopy(expected);wrong[0][6][10]="self";mutations.append(("housing credited as issuer",wrong))
    wrong=deepcopy(expected);wrong[0][7][10]="other";mutations.append(("mixed issuer accepted",wrong))
    wrong=deepcopy(expected);wrong[0][3][9][0][0]=["local",0];mutations.append(("source issuer inherited by target",wrong))
    wrong=deepcopy(expected);wrong[1][1]=0;mutations.append(("copied receipt replaced by fresh default",wrong))
    wrong=deepcopy(expected);wrong[2][0]=0;mutations.append(("absence erases initial stored charge",wrong))
    for label,wrong in mutations:
        assert actual!=wrong,f"failed planted drift: {label}"
        print(f"PASS: caught planted drift: {label}")


if __name__=="__main__":
    main()
