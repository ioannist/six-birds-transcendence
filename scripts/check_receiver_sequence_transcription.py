#!/usr/bin/env python3
"""Check raw delivery instructions and compile actual receiver conclusions."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/TTH07-RECEIVER-SEQUENCE.model.json"
PROBE = r"""
import Lean
import CSTTT.Targets.GenericHandoff.POS04ReceiverSequence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TargetTheory.GenericHandoff
open POS04ResourceRuntime POS04ReceiverSequence
example (p q : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ReceiverSequence.rightCells (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) a = a := right_cells p q a
example (p q : Protocol) : ReceiverSequence.ContentReadout (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
    POS04ReceiverContent.instructions POS04ReceiverContent.instructions transport canonical := public_content p q
example (p q : Protocol) : ¬ ReceiverSequence.ContentFaithful
    (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) POS04ReceiverContent.instructions POS04ReceiverContent.instructions
    constantTransport canonical canonical initialReady (targetReady p) initialReady (targetReady q) := constant_not_faithful p q
example (p q : Protocol) : ¬ ReceiverSequence.ContentFaithful
    (POS04RawHandoff.raw p) (POS04RawHandoff.raw q) POS04ReceiverContent.instructions POS04ReceiverContent.instructions
    transport (POS04ReceiverIntervention.withoutSource canonical) canonical cutInitial (cutTarget p) initialReady (targetReady q) :=
  source_cut_not_faithful p q
example (p q : Protocol) (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverSequence.classAt (POS04RawHandoff.raw p) (POS04RawHandoff.raw q)
      POS04ReceiverContent.instructions POS04ReceiverContent.instructions transport
      (POS04ReceiverIntervention.withoutSource canonical) canonical cutInitial (cutTarget p) initialReady (targetReady q) input = none :=
  (source_cut p q input).2
#eval IO.println (Lean.Json.compress (Lean.Json.mkObj [
  ("state", Lean.toJson (kernel.all (fun s => middleMaps.state s == s))),
  ("action", Lean.toJson (actions.all (fun a => middleMaps.action a == a))),
  ("coordinate", Lean.toJson ((List.range 8).all (fun n => middleMaps.coordinate n == n))),
  ("predictive", Lean.toJson (middleMaps.predictive (3,[[true,false]]) == (3,[[true,false]]))),
  ("maintenance", Lean.toJson (middleMaps.maintenance false == false && middleMaps.maintenance true == true)),
  ("owner", Lean.toJson (middleMaps.owner .source == Tag.target && middleMaps.owner .target == Tag.source)),
  ("event", Lean.toJson (eventIds.all (fun e => transport.event e == e))),
  ("history", Lean.toJson (transport.history .a == RouteId.a && transport.history .b == RouteId.b)),
  ("route", Lean.toJson (transport.route .a == RouteId.a && transport.route .b == RouteId.b)),
  ("constantState", Lean.toJson (kernel.all (fun s => constantMaps.state s == KState.p0w0))),
  ("erasedSource", Lean.toJson ((POS04ReceiverIntervention.erase (canonicalValue .receiverInput)).sourcePresent)),
  ("sourcePairDistinct", Lean.toJson (decide (
    FactorTransport.classOf (POS04TemporalFactor.schema .source) (POS04FactorTransport.data canonical .source) POS04ReceiverContent.inputA.1 ≠
    FactorTransport.classOf (POS04TemporalFactor.schema .source) (POS04FactorTransport.data canonical .source) POS04ReceiverContent.inputB.1))) ]))
"""


def compare(model: dict, observed: dict) -> None:
    delivery = model["delivery"]
    expected_names = {k: "identity" for k in ("state", "action", "coordinate", "predictive", "maintenance", "event", "history", "route")}
    expected_names["owner"] = "Assigned.swapTag"
    if delivery != expected_names:
        raise ValueError("raw delivery instruction mismatch")
    if model["source_class_test_inputs"] != ["POS04ReceiverContent.inputA", "POS04ReceiverContent.inputB"]:
        raise ValueError("raw source-class input mismatch")
    if model["controls"]["constant_middle_state"] != "p0w0; all other map and primitive fields retained":
        raise ValueError("raw constant state control mismatch")
    if model["controls"]["source_erasure"] != "apply POS04ReceiverIntervention.erase to only the left receiver primitive; right cells unchanged":
        raise ValueError("raw source erasure control mismatch")
    expected = {k: True for k in expected_names}
    expected.update(constantState=True, erasedSource=False, sourcePairDistinct=True)
    if expected != observed:
        raise ValueError(f"interpreted instruction mismatch: {observed}")


def main() -> None:
    model = json.loads(MODEL.read_text())
    with tempfile.TemporaryDirectory(prefix="receiver-sequence-") as directory:
        path = Path(directory) / "Receiver.lean"
        path.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean", capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        observed = json.loads(run.stdout.strip())
    compare(model, observed)
    for label in ("state", "owner", "route", "constant control"):
        drift = copy.deepcopy(model)
        if label == "constant control":
            drift["controls"]["constant_middle_state"] = "p1w0"
        else:
            drift["delivery"][label] = "constant"
        try:
            compare(drift, observed)
        except ValueError:
            print(f"CAUGHT planted {label} drift")
        else:
            raise AssertionError(f"missed planted {label} drift")
    print("PASS raw delivery instructions/source pair and kernel actual receiver content, collision and source-erasure controls")
    print("Scope: immediate common-coordinate receiver operation; physical middle interface, supported acquisition and full two-hop Temporal-FIACH remain open")


if __name__ == "__main__":
    main()
