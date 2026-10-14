#!/usr/bin/env python3
"""Read-only exact comparison of Lean's computed G6 controls with frozen G6b.

Probes live under /tmp. No Python lane evaluation or stored Lean verdict is used.
Expensive GF/F/O exports use Lean-checked computation equalities, not trusted
candidate outputs; the data reduction is kernel-certified before evaluation.
Existing POS-04 raw transcription is independently checked by its L5 checker.
"""
from __future__ import annotations
import copy
import json
import subprocess
import tempfile
from fractions import Fraction
from math import lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "audit/G6b_results.json"
MODEL = ROOT / "audit/proposed_models/FIACH-POS-04.model.json"
PROBE = r'''
import CSTTT.Targets.ComputedFIACH.Assembly
import CSTTT.Targets.GenericHandoff.POS04RouteReadout
import CSTTT.Targets.GenericHandoff.POS04DispatchedStage
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory
local instance : DecidableEq (BridgeRunObservation pos04SnapshotBridge) :=
  bridgeRunObservationDecEq pos04SnapshotBridge
set_option maxRecDepth 8192
private def obj := Json.mkObj
private def arr (xs : List Json) : Json := Json.arr xs.toArray
private def str := Json.str
private def nat (n : Nat) : Json := toJson n
private def jsonBool (b : Bool) : Json := toJson b
private def rational (n d : Nat) : Json := str (toString n ++ "/" ++ toString d)
private def names (xs : List KState) : Json := toJson (xs.map stateName)
private def reg (r : List KState × List EventId) : Json :=
  arr [names r.1,toJson (r.2.map eventName)]
private def entry (m : RawLaneModel) (e : WithdrawalEntry) : Json := obj [
  ("factor",str (ambientName e.factor)),("probability",rational e.numerator 4),
  ("counter",nat e.counter),("ticks",nat e.ticks),("register",reg e.register),
  ("budget",rational (budget6 (arrivalInputs m)) 1)]
private def ledger (m : RawLaneModel) : Json :=
  let d := runInputs6 (withdrawnAssignment m) .target
  let recharge := if d.resource.rechargeAvailable then d.ledger.rechargePerAction else 0
  obj [("budget",rational (budget6 d) 1),("cost",rational d.ledger.actionCost 1),
    ("recharge",rational recharge 1),
    ("next_budget",rational (budget6 d - d.ledger.actionCost + recharge) 1)]
/-- Export a reduced value ONLY after its equation to the actual computation
has been checked by Lean. These equations are the kernel-checked controls. -/
private def reduced {α : Type} (actual value : α) (_h : actual = value) : α := value
private def falseOfNotTrue (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> first | rfl | exact False.elim (h rfl)
/-- Values from the new actual-support source/receiver/target interpreter,
whose row/update/arrival/result equations are proved for partial assignments.
This exports computations, not a stored successful route verdict. -/
private def executedRoutes (m : RawLaneModel) : Json :=
  let a := CSTTT.TargetTheory.GenericHandoff.DispatchedPackage.global
    CSTTT.TargetTheory.GenericHandoff.POS04DispatchedStage.raw m.assignment
  arr (routeIds.map fun r =>
    let x := CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution.arrivalRun a r
    let act := CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution.responseAction a x
    let d := runInputs6 a .target
    let row := actualRows6 d x act
    obj [("receiver_factor",str (ambientName x.factor)),("action",str (actionName act)),
      ("raw_tuple",reg x.residue),
      ("supported_history",jsonBool (CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution.supportedWord a .source
        (acquisitionInitialRun a .source r)
        (CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution.wordFor a r))),
      ("resulting_states",arr (row.filterMap fun e => if e.2 > (0 : Rat) then
        let next := actualUpdate6 d x act e.1
        some (obj [("factor",str (ambientName next.factor)),("probability",str (toString e.2)),
          ("counter",nat next.counter),("ticks",nat next.ticks),("register",reg next.residue),
          ("budget",rational (budget6 d) 1)]) else none)),
      ("result_readouts",arr (row.filterMap fun e => if e.2 > (0 : Rat) then
        let next := actualUpdate6 d x act e.1
        some (match CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution.routeRaw.readout.eval a
          (CSTTT.TargetTheory.GenericHandoff.POS04RouteExecution.frame .target next) () with
          | some (some n) => nat n | _ => Json.null) else none))])
private def sample (m : RawLaneModel) (gf go : List KState) (p l f o : Bool)
    (hP : packageLaneCheck m.assignment = p) (hL : lineageLaneCheck m = l)
    (hf : greatestF m = gf) (ho : greatestO m = go)
    (hF : fullAutonomyCheck m = f) (hO : operationalAutonomyCheck m = o) : Json := obj [
  ("package",jsonBool (reduced (packageLaneCheck m.assignment) p hP)),("lineage",jsonBool (reduced (lineageLaneCheck m) l hL)),
  ("AF",jsonBool (reduced (fullAutonomyCheck m) f hF)),("AO",jsonBool (reduced (operationalAutonomyCheck m) o hO)),
  ("greatestF",names (reduced (greatestF m) gf hf)),("greatestO",names (reduced (greatestO m) go ho)),
  ("entries",arr ((entries m).map (entry m))),
  ("route_readouts",arr (routeIds.map fun r => match acquisitionRouteOutput m r with
     | some n => nat n | none => Json.null)),
  ("ledger",ledger m),
  ("executed_route_component",executedRoutes m),
  ("snapshot_coordinate_checks",toJson (acquisitionSnapshotIndices.map fun i =>
     decide (mapSnapshotReadout acquisitionSnapshotMaps (acquisitionSnapshotReadout (image m.assignment) .source i) =
       acquisitionSnapshotReadout (image m.assignment) .target i))),
  ("snapshot_occurrences",toJson (acquisitionSnapshotIndices.map (fun i => snapshotOccurrence i.2)))]
#eval (obj [("Baseline",sample baseline kernel kernel true true true true package_lane_positive baseline_lineage_lane baseline_greatestF baseline_greatestO baseline_AF baseline_AO),("G6-PACKAGE-ONLY",sample packageDeletion [] kernel false true false true
    (falseOfNotTrue _ package_deletion_package) package_deletion_lineage_lane
    package_deletion_greatestF package_deletion_greatestO
    (falseOfNotTrue _ package_deletion_not_AF) package_deletion_AO),
  ("G6-LINEAGE-ONLY",sample lineageDeletion kernel kernel true false true true
    lineage_deletion_package (falseOfNotTrue _ lineage_deletion_not_lineage_lane)
    lineage_deletion_greatestF lineage_deletion_greatestO lineage_deletion_AF lineage_deletion_AO),("G6-WITHDRAWAL-ONLY",sample withdrawalDeletion [] [] true true false false
    withdrawal_deletion_package withdrawal_deletion_lineage_lane
    withdrawal_deletion_greatestF withdrawal_deletion_greatestO
    (falseOfNotTrue _ withdrawal_deletion_not_AF) (falseOfNotTrue _ withdrawal_deletion_not_AO))]).compress
'''


def lean_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-lean-") as directory:
        path = Path(directory) / "G6.lean"
        path.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


HISTORICAL_PROBE = r'''
import CSTTT.Targets.GenericHandoff.POS04HistoricalFIACH
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TargetTheory.GenericHandoff
set_option maxRecDepth 8192
private def entriesJson (m : RawLaneModel) : Json :=
  Json.arr ((POS04HistoricalAutonomy.executionEntries m).map fun e =>
    Json.mkObj [("factor",toJson (ambientName e.2.factor)),
      ("probability",toJson (toString e.1 ++ "/4")),
      ("counter",toJson e.2.counter),("ticks",toJson e.2.ticks),
      ("register",Json.arr #[toJson (e.2.residue.1.map stateName),toJson (e.2.residue.2.map eventName)]),
      ("budget",toJson (toString (budget6 (arrivalInputs m)) ++ "/1"))]).toArray
private def reduced (actual value : Bool) (_h : actual = value) : Bool := value
private def falseOfNotTrue (b : Bool) (h : b ≠ true) : b = false := by
  cases b <;> first | rfl | exact False.elim (h rfl)
private def caseJson (m : RawLaneModel) (f o : Bool)
    (hf : fullAutonomyCheck m = f) (ho : operationalAutonomyCheck m = o) : Json := Json.mkObj [
  ("entries",entriesJson m),
  ("funded",toJson ((POS04HistoricalAutonomy.executionEntries m).map fun e => e.2.funded)),
  -- These are raw computed CHECKS, connected to the historical GAME READOUTS
  -- by the arbitrary-partial full_game_iff_af/operational_game_iff_ao theorems.
  ("AF",toJson (reduced (fullAutonomyCheck m) f hf)),
  ("AO",toJson (reduced (operationalAutonomyCheck m) o ho))]
#eval (Json.mkObj [
  ("Baseline",caseJson baseline true true baseline_AF baseline_AO),
  ("G6-PACKAGE-ONLY",caseJson packageDeletion false true
    (falseOfNotTrue _ package_deletion_not_AF) package_deletion_AO),
  ("G6-LINEAGE-ONLY",caseJson lineageDeletion true true lineage_deletion_AF lineage_deletion_AO),
  ("G6-WITHDRAWAL-ONLY",caseJson withdrawalDeletion false false
    (falseOfNotTrue _ withdrawal_deletion_not_AF) (falseOfNotTrue _ withdrawal_deletion_not_AO)),
  ("missingPastTicks",caseJson POS04RuntimeEquivalenceBoundary.missingPastTicks false true
    (falseOfNotTrue _ POS04RuntimeEquivalenceBoundary.legacy_full_rejects)
    POS04RuntimeEquivalenceBoundary.legacy_operational_accepts),
  ("sourceRechargeUnavailable",caseJson POS04ReceiverResetProjection.sourceRechargeUnavailable true true
    ((POS04HistoricalAutonomy.full_game_iff_af _).mp
      POS04HistoricalAutonomy.source_recharge_unavailable_historical_full)
    POS04ReceiverResetProjection.diagnostic_legacy_operational_accepts)]).compress
'''


def historical_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-historical-") as directory:
        path = Path(directory) / "Historical.lean"
        path.write_text(HISTORICAL_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_historical(got: dict, results: dict) -> None:
    registered = set(results["cases"])
    assert set(got) == registered | {"missingPastTicks", "sourceRechargeUnavailable"}, "historical case domain"
    for name in sorted(registered):
        g, c = got[name], results["cases"][name]
        for version, key, lane in [("F", "AF", "autonomy_full"), ("O", "AO", "autonomy_operational")]:
            assert g[key] == c["lane_vectors"][version][lane], f"{name}: historical {key}"
            assert normalize_entries(g["entries"]) == normalize_entries(c[lane]["entry_states"]), f"{name}: historical every-branch entries"
        assert g["funded"] == [True] * len(g["entries"]), f"{name}: actual target funding"
    # New diagnostics are NOT frozen predictions. Their mutation rules and
    # precise outcomes are kernel-proved in POS04HistoricalAutonomy; compare
    # computed entries with the unchanged registered baseline, not a Python
    # reconstruction of any transition table.
    for name, full in [("missingPastTicks", False), ("sourceRechargeUnavailable", True)]:
        g = got[name]
        assert g["AO"] is True and g["AF"] is full, f"{name}: historical diagnostic games"
        assert g["entries"] == got["Baseline"]["entries"], f"{name}: reset receiver/target entries"
        assert g["funded"] == got["Baseline"]["funded"], f"{name}: retained target funding"


SEMANTIC_PROBE = r'''
import CSTTT.Targets.GenericHandoff.POS04CompleteFIACH
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
open CSTTT.TargetTheory.GenericHandoff
private def weights (tag : Tag) : Json :=
  let a := image POS04LineageFutureBoundary.proposal.assignment
  Json.mkObj (ambientStates.map fun o =>
    (ambientName o, toJson (toString (actualWeight6 (runInputs6 a tag)
      POS04LineageFutureBoundary.afterFirst .cw o))))
#eval (Json.mkObj [
  ("source", weights .source), ("target", weights .target),
  ("first_step", toJson (toString (actualWeight6
    (runInputs6 (image POS04LineageFutureBoundary.proposal.assignment) .source)
    POS04LineageFutureBoundary.start .cw (.inK .p2w1))))]).compress
'''


def semantic_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-semantic-") as directory:
        path = Path(directory) / "Semantic.lean"
        path.write_text(SEMANTIC_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_semantic(got: dict, model: dict) -> None:
    # This new sensitivity intervention is NOT a frozen G6b prediction. Its
    # stated rule relabels only p2w1/cw's lethal outcome, keeping its numerator.
    # Compare ALL ambient outcomes; do not repeat the K-only legacy blind spot.
    imported = model["t1_import"]
    outcomes = imported["ambient_states"]
    source = {o: Fraction(imported["all_action_distributions"]["p2w1"]["cw"].get(o, "0"))
              for o in outcomes}
    target = dict(source)
    target["p5w1"] += target["p2w0"]
    target["p2w0"] = Fraction(0)
    assert {k: Fraction(v) for k, v in got["source"].items()} == source, "semantic source row"
    assert {k: Fraction(v) for k, v in got["target"].items()} == target, "semantic relabeled target row"
    first = Fraction(imported["all_action_distributions"]["p1w0"]["cw"]["p2w1"])
    assert Fraction(got["first_step"]) == first, "semantic supported first step"


TEMPORAL_PROBE = r'''
import CSTTT.Targets.GenericHandoff.POS04TemporalCoherence
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
open CSTTT.TargetTheory.GenericHandoff
private def rows (tag : Tag) (funded : Bool) : Json :=
  Json.mkObj (ambientStates.map fun state =>
    (ambientName state, Json.mkObj (actions.map fun action =>
      (actionName action, match (POS04TemporalCoherence.runtime tag).row.eval canonical
        (POS04RegisterDynamics.encode (show Run6 from ⟨state,0,0,([],[]),funded⟩)) (.nominal,action) with
      | none => Json.null
      | some row => Json.arr (row.map (fun e => Json.arr #[toJson (ambientName e.1),toJson (toString e.2)])).toArray))))
#eval (Json.mkObj [
  ("source-funded",rows .source true), ("target-funded",rows .target true),
  ("source-unfunded",rows .source false), ("target-unfunded",rows .target false)]).compress
'''


def temporal_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-temporal-") as directory:
        path = Path(directory) / "Temporal.lean"
        path.write_text(TEMPORAL_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_temporal(got: dict, model: dict) -> None:
    raw = model["t1_import"]
    outcomes = raw["ambient_states"]
    actions = raw["actions"]
    assert set(raw["all_action_distributions"]) == set(raw["kernel_order"]), "declared kernel row coverage"
    for state, rows in raw["all_action_distributions"].items():
        assert set(rows) == set(actions), f"{state}: declared action coverage"
    assert set(got) == {f"{tag}-{regime}" for tag in ["source", "target"]
                        for regime in ["funded", "unfunded"]}, "temporal row regimes"
    for regime, table in got.items():
        assert set(table) == set(outcomes), f"{regime}: ambient coverage"
        for state, action_rows in table.items():
            assert set(action_rows) == set(actions), f"{regime}/{state}: action coverage"
            for action, row in action_rows.items():
                assert row is not None, f"{regime}/{state}/{action}: missing interpreted inputs"
                actual = {o: Fraction(0) for o in outcomes}
                for dest, weight in row:
                    assert dest in actual, f"{regime}/{state}/{action}: unknown outcome"
                    actual[dest] += Fraction(weight)
                # The two external ambient outcomes have no outgoing row by
                # the declared semantics; every active row/action is mandatory.
                declared = raw["all_action_distributions"][state][action] if state in raw["kernel_order"] else {}
                expected = {o: Fraction(declared.get(o, "0")) if regime.endswith("-funded")
                            else Fraction(0) for o in outcomes}
                assert actual == expected, f"{regime}/{state}/{action}: actual temporal row"


RESOURCE_PROBE = r'''
import CSTTT.Targets.GenericHandoff.POS04MultiResourceGames
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TargetTheory.GenericHandoff
open RegisterInterpreter POS04RouteExecution POS04ResourceRuntime
private def resourceName : Resource → String
  | .recharge => "target_recharge"
  | .removed .source => "source"
  | .removed .migrationBridge => "migration_bridge"
  | .removed .migrationController => "migration_controller"
  | .removed .externalDecoder => "external_decoder"
  | .removed .externalScheduler => "external_scheduler"
  | .removed .undeclaredRepair => "undeclared_repair_support"
private def ownerJson (v : Option CSTTT.CarrierId) : Json :=
  match v with | none => Json.null | some x => toJson x.code
private def natString (v : Nat) : Json := toJson (toString v)
private def sample (m : RawLaneModel) : Json :=
  let a := PackageRuntime.target (model (protocol m)) m.assignment
  let raw := resourceRaw (protocol m)
  let x : Run6 := ⟨.inK .p2w1,1,1,routeRegister .a,true⟩
  let r := frame .target x
  let accounts := match raw.accounts.eval a r () with
    | none => Json.null
    | some ac => Json.mkObj (resources.map fun res =>
        (resourceName res,Json.mkObj [("owner",ownerJson (ac res).owner),
          ("retained",toJson (ac res).retained),("balance",natString (ac res).balance)]))
  let charge (tag : Tag) := match raw.charge.eval a (frame tag x) (.nominal,.cw) with
    | none => Json.null
    | some ch => Json.mkObj [("owner",toJson ch.owner.code),
        ("used",toJson (ch.used.map resourceName)),
        ("debit",natString (ch.debit .recharge)),("credit",natString (ch.credit .recharge))]
  let wd := match raw.withdrawal.read a with
    | none => Json.null
    | some w => Json.mkObj [("removed",toJson (w.removed.map resourceName)),
        ("retained",toJson (w.retained.map resourceName))]
  Json.mkObj [("accounts",accounts),("target_charge",charge .target),
    ("source_charge",charge .source),("withdrawal",wd),
    ("source_present",toJson (raw.sourcePresent.eval a r ())),
    ("required",match raw.required.eval a r () with
      | none => Json.null | some rs => toJson (rs.map resourceName))]
#eval (Json.mkObj [("Baseline",sample baseline),
  ("G6-PACKAGE-ONLY",sample packageDeletion),
  ("G6-LINEAGE-ONLY",sample lineageDeletion),
  ("G6-WITHDRAWAL-ONLY",sample withdrawalDeletion)]).compress
'''


def resource_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-resources-") as directory:
        path = Path(directory) / "Resources.lean"
        path.write_text(RESOURCE_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_resources(got: dict, results: dict, model: dict, lanes: dict) -> None:
    # Accounts and charges are read directly from the Lean instruction evaluator.
    # The six absent acquisition accounts follow the declared withdrawal rule,
    # not a Python copy of the interpreter. Exact ledger values come from G6b.
    interface = lanes["raw_interface"]
    removed = interface["withdrawal_rule"]["removed_roles"]
    retention = interface["post_exit_retention"]
    resource = retention["resource"]
    target_code = model["carrier"]["tags"].index("target")
    assert set(got) == set(results["cases"]), "resource case domain"
    controls = {c["id"]: c for c in lanes["controls"]}
    for name, case in results["cases"].items():
        actual = got[name]
        # Apply the declaration's raw metadata edit, not its expected verdict.
        retained = retention["retained_resources"]
        for edit in controls.get(name, {}).get("json_edits", []):
            if edit["path"] == "/raw_interface/post_exit_retention/retained_resources":
                assert edit["op"] == "replace", "retention intervention operation"
                retained = edit["value"]
        ledger = {k: Fraction(v) for k, v in case["autonomy_full"]["effective_ledger"].items()}
        assert set(actual["accounts"]) == set(removed + [resource]), f"{name}: resource accounts"
        for role in removed:
            assert actual["accounts"][role] == {"owner": None, "retained": False, "balance": "0"}, f"{name}: removed {role} account"
        account = actual["accounts"][resource]
        assert account["owner"] == target_code, f"{name}: recharge ownership"
        assert account["retained"] == (resource in retained), f"{name}: recharge retention"
        assert Fraction(account["balance"]) == ledger["budget"], f"{name}: recharge balance"
        assert actual["withdrawal"] == {"removed": removed, "retained": retained}, f"{name}: six-role withdrawal"
        assert actual["source_present"] == retention["source_present_after_withdrawal"], f"{name}: source presence"
        assert actual["required"] == [resource], f"{name}: required maintenance resource"
        for tag in ["target", "source"]:
            charge = actual[f"{tag}_charge"]
            assert charge is not None, f"{name}: missing {tag} charge input"
            assert charge["owner"] == target_code, f"{name}: charge owner"
            # Source-mode execution belongs to acquisition, not maintenance.
            assert charge["used"] == ([resource] if tag == "target" else []), f"{name}: {tag} used resource boundary"
            assert Fraction(charge["debit"]) == ledger["cost"], f"{name}: debit"
            assert Fraction(charge["credit"]) == ledger["recharge"], f"{name}: effective credit"
        assert (Fraction(account["balance"]) - Fraction(actual["target_charge"]["debit"])
                + Fraction(actual["target_charge"]["credit"])) == ledger["next_budget"], f"{name}: balance update"

def normalize_entries(entries: list[dict]) -> list[dict]:
    return [{**entry, "probability": Fraction(entry["probability"]),
             "budget": Fraction(entry["budget"])} for entry in entries]


def compare(got: dict, results: dict) -> None:
    expected_names = set(results["cases"])
    assert set(got) == expected_names, "case domain drift"
    for name in sorted(expected_names):
        g, c = got[name], results["cases"][name]
        vector = c["lane_vectors"]
        expected = {"package": vector["F"]["package"], "lineage": vector["F"]["lineage"],
                    "AF": vector["F"]["autonomy_full"], "AO": vector["O"]["autonomy_operational"]}
        assert {k: g[k] for k in expected} == expected, f"{name}: lane vectors"
        assert g["greatestF"] == c["autonomy_full"]["greatest"], f"{name}: greatestF"
        assert g["greatestO"] == c["autonomy_operational"]["greatest"], f"{name}: greatestO"
        for lane in ["autonomy_full", "autonomy_operational"]:
            assert normalize_entries(g["entries"]) == normalize_entries(c[lane]["entry_states"]), f"{name}: {lane} entries"
            assert {k: Fraction(v) for k, v in g["ledger"].items()} == {
                k: Fraction(v) for k, v in c[lane]["effective_ledger"].items()}, f"{name}: {lane} ledger"
        route = c["lineage"]["route"]
        assert g["route_readouts"] == [x["future_readout"] for x in route["records"]], f"{name}: route readouts"
        executed = g["executed_route_component"]
        assert len(executed) == len(route["records"]), f"{name}: executed comparison domain"
        for actual, expected_route in zip(executed, route["records"], strict=True):
            for key in ["receiver_factor", "action", "raw_tuple"]:
                assert actual[key] == expected_route[key], f"{name}: executed {key}"
            assert actual["supported_history"] == route["gates"]["supported_histories"], f"{name}: actual source support"
            assert normalize_entries(actual["resulting_states"]) == normalize_entries(expected_route["resulting_states"]), f"{name}: actual target support and updates"
            assert actual["result_readouts"] == [expected_route["future_readout"]] * len(expected_route["resulting_states"]), f"{name}: every-branch retained probe"
        bridge = c["lineage"]["bridge"]
        assert g["snapshot_coordinate_checks"] == bridge["snapshot_coordinate_checks"], f"{name}: four snapshots"
        assert g["snapshot_occurrences"] == [x["occurrence"] for x in bridge["snapshot_domain"]], f"{name}: snapshot domain"



RUNTIME_LINEAGE_PROBE = r'''
import CSTTT.Targets.GenericHandoff.POS04RuntimeLineage
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.GenericHandoff RegisterInterpreter
private def model := POS04RuntimeLineage.raw (POS04ResourceRuntime.protocol baseline)
private def input := DispatchedPackage.global POS04DispatchedStage.raw baseline.assignment
private def interpreted (tag : Tag) : ResourceRuntime.Execution Cell Value
    POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue LaneDisturbance Action Ambient :=
  if tag = .source then (RuntimeLineage.sourceLink model).source
  else (RuntimeLineage.targetLink model).source
private def rows (tag : Tag) (funded : Bool) : Json :=
  Json.mkObj (ambientStates.map fun state =>
    (ambientName state, Json.mkObj (actions.map fun action =>
      (actionName action, match (interpreted tag).row.eval input
        (POS04RegisterDynamics.encode (show Run6 from ⟨state,0,0,([],[]),funded⟩)) (.nominal,action) with
      | none => Json.null
      | some row => Json.arr (row.map (fun e => Json.arr #[toJson (ambientName e.1),toJson (toString e.2)])).toArray))))
private def domain (tag : Tag) : Json := Json.mkObj [
  ("outcomes",toJson ((interpreted tag).outcomes.map ambientName)),
  ("actions",toJson ((interpreted tag).actions.map actionName))]
-- The universal semantic adapter is kernel-checked; not exported as a stored Boolean.
example (m : RawLaneModel) :
    (RuntimeLineage.CoreReadout (POS04RuntimeLineage.raw (POS04ResourceRuntime.protocol m))
      (image m.assignment) ∧ TypedAcquisitionEndpointPass m) ↔
      POS04CompleteLineage.StrictTemporalLineage m := POS04RuntimeLineage.complete_iff m
#eval (Json.mkObj [
  ("rows", Json.mkObj [("source-funded",rows .source true), ("target-funded",rows .target true),
    ("source-unfunded",rows .source false), ("target-unfunded",rows .target false)]),
  ("domains", Json.mkObj [("source",domain .source),("target",domain .target)])]).compress
'''


def runtime_lineage_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-runtime-lineage-") as directory:
        path = Path(directory) / "RuntimeLineage.lean"
        path.write_text(RUNTIME_LINEAGE_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_runtime_lineage(got: dict, model: dict) -> None:
    assert set(got) == {"rows", "domains"}, "runtime lineage export domain"
    compare_temporal(got["rows"], model)
    assert set(got["domains"]) == {"source", "target"}, "runtime lineage tag domain"
    raw = model["t1_import"]
    for tag, domain in got["domains"].items():
        assert set(domain) == {"outcomes", "actions"}, f"{tag}: raw execution domain fields"
        assert domain["outcomes"] == raw["ambient_states"], f"{tag}: complete actual outcome domain"
        assert domain["actions"] == raw["actions"], f"{tag}: raw action domain"


PUBLIC_RUNTIME_PROBE = r"""
import CSTTT.Targets.GenericHandoff.POS04PublicRuntime
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TargetTheory.GenericHandoff
open RegisterInterpreter POS04RouteExecution
private def input := PublicRuntime.target (POS04PublicRuntime.raw (POS04ResourceRuntime.protocol baseline)) canonical
private def rows (funded : Bool) : Json := Json.mkObj (ambientStates.map fun state =>
  (ambientName state,Json.mkObj (actions.map fun action =>
    (actionName action,match POS04HistoricalRuntime.execution.row.eval input
      (frame .target (show Run6 from ⟨state,0,0,([],[]),funded⟩)) (.nominal,action) with
    | none => Json.null
    | some row => Json.arr (row.map (fun e => Json.arr #[toJson (ambientName e.1),toJson (toString e.2)])).toArray))))
-- Universal equations/biconditionals; never exported as stored verdicts.
example (p : POS04ResourceRuntime.Protocol) :
    PublicRuntime.autonomy (POS04PublicRuntime.raw p) = POS04HistoricalRuntime.model p :=
  POS04PublicRuntime.autonomy_eq p
example (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment) :
    PublicRuntime.target (POS04PublicRuntime.raw p) a = image a := POS04PublicRuntime.target_eq p a
example (m : RawLaneModel) : POS04PublicRuntime.FullAutonomy m ↔ AF m := POS04PublicRuntime.full_iff_af m
example (m : RawLaneModel) : POS04PublicRuntime.OperationalAutonomy m ↔ AO m := POS04PublicRuntime.operational_iff_ao m
example (m : RawLaneModel) : POS04PublicRuntime.Lineage m ↔ POS04CompleteLineage.StrictTemporalLineage m :=
  POS04PublicRuntime.lineage_named_iff m
example : ¬ PublicRuntime.TargetExecutionCoherent POS04PublicRuntime.emptyHistoricalRows canonical :=
  POS04PublicRuntime.empty_rows_rejected
example : ¬ PublicRuntime.TargetExecutionCoherent POS04PublicRuntime.identityHistorical canonical :=
  POS04PublicRuntime.identity_successor_rejected
#eval (Json.mkObj [("target-funded",rows true),("target-unfunded",rows false)]).compress
"""


def public_runtime_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-public-runtime-") as directory:
        path = Path(directory) / "PublicRuntime.lean"
        path.write_text(PUBLIC_RUNTIME_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_public_runtime(got: dict, runtime: dict) -> None:
    assert set(got) == {"target-funded", "target-unfunded"}, "public target row domain"
    for mode, rows in got.items():
        assert rows == runtime["rows"][mode], f"{mode}: exact historical/actual target rows"



PRESENTATION_PROBE = r"""
import CSTTT.Targets.GenericHandoff.POS04PresentationCoherence
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.GenericHandoff CSTTT.TargetTheory.ComputedFIACH
private def arr (xs : List Json) : Json := Json.arr xs.toArray
private def factorRows (tag : Tag) : Json :=
  match (PresentationCoherence.factorBindings
    (FramePresentation.presentation POS04PresentationCoherence.frames)).source.read canonical with
  | none => Json.null
  | some _ =>
    match (PresentationCoherence.factorView (POS04TemporalFactor.bindings tag)).read canonical with
    | none => Json.null
    | some d => Json.mkObj (kernel.map fun state => (stateName state,
      Json.mkObj (actions.map fun action => (actionName action,
        arr (d.rows state action |>.map fun e =>
          Json.arr #[toJson (ambientName e.1),toJson (toString e.2 ++ "/4")])))))
private def recordData : Json :=
  match POS04PresentationCoherence.raw.record.read canonical with
  | none => Json.null
  | some r => Json.mkObj [
    ("realized",toJson (r.realized.map stageName)),
    ("events",arr (eventIds.map fun i =>
      match r.events i with
      | none => Json.null
      | some e => Json.mkObj [("id",toJson (eventName i)),
        ("from",toJson (stageName e.fromStage)),("to",toJson (stageName e.toStage)),
        ("source_support",toJson e.sourceSupport),("target_support",toJson e.targetSupport),
        ("atomic",toJson e.atomic),("strict_step",toJson e.strictStep),
        ("order_advance",toJson e.orderAdvance)])),
    ("clock",arr (stages.map fun s => toJson (r.clock s))),
    ("writers",arr (routeIds.map fun i => Json.arr #[toJson (r.sourceWriter i),toJson (r.targetWriter i)]))]
-- Universal interface equations, not stored verdict Booleans.
example (a : Assigned.Assignment) (t : Tag) :
    (PresentationCoherence.factorView (POS04TemporalFactor.bindings t)).read a =
      (POS04FactorTransport.view t).read a := POS04PresentationCoherence.factor_decoder a t
example : FramePresentation.presentation POS04PresentationCoherence.frames =
    POS04PresentationCoherence.raw := POS04PresentationCoherence.constructed_presentation
example (m : RawLaneModel) (h : POS04CompleteLineage.StrictTemporalLineage m) :
    FramePresentation.SchemaCheck POS04PresentationCoherence.frames ∧
      PresentationCoherence.Pass (FramePresentation.presentation POS04PresentationCoherence.frames)
        (PublicRuntime.target (POS04PublicRuntime.raw (POS04ResourceRuntime.protocol m)) m.assignment) :=
  POS04PresentationCoherence.public_coherence m h
example (a : Assigned.Assignment) :
    PresentationCoherence.RecordLaws (POS04AcquisitionEndpoint.data a)
      (POS04RecordComponent.data a) stages.idxOf := POS04PresentationCoherence.record_laws a
example : ¬ PresentationCoherence.RecordLaws (POS04AcquisitionEndpoint.data canonical)
    {(POS04RecordComponent.data canonical) with events := fun _ => none} stages.idxOf :=
  POS04PresentationCoherence.record_event_guard
example (a : Assigned.Assignment) (k : Cell) (hk : k ∈ acquisitionDependencies) (hm : a k = none) :
    ¬ PresentationCoherence.Pass POS04PresentationCoherence.raw a :=
  POS04PresentationCoherence.missing_endpoint a k hk hm
#eval (Json.mkObj [("source",factorRows .source),("target",factorRows .target),("record",recordData)]).compress
"""


def presentation_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-presentation-") as directory:
        path = Path(directory) / "Presentation.lean"
        path.write_text(PRESENTATION_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_presentation(got: dict, model: dict) -> None:
    assert set(got) == {"source", "target", "record"}, "presentation export domain"
    raw = model["t1_import"]
    for tag in ("source", "target"):
        assert set(got[tag]) == set(raw["kernel_order"]), f"{tag}: factor state coverage"
        for state in raw["kernel_order"]:
            assert set(got[tag][state]) == set(raw["actions"]), f"{tag}: factor action coverage"
            for action in raw["actions"]:
                actual = [(o, Fraction(w)) for o, w in got[tag][state][action]]
                expected = {o: Fraction(w) for o, w in model["new_data"]["raw_inputs"]["by_tag"][tag]["action_distributions"][state][action].items()}
                assert len(actual) == len(expected) and dict(actual) == expected, f"{tag}/{state}/{action}: projected exact raw rows"
    corridor = model["new_data"]["corridor"]
    record = got["record"]
    assert set(record) == {"realized", "events", "clock", "writers"}, "record presentation fields"
    assert record["realized"] == corridor["realized_stages"], "record realization"
    assert record["events"] == [dict(e, order_advance=1) for e in corridor["events"]], "record event shapes/increments"
    assert record["clock"] == list(range(len(corridor["stages"]))), "record declared stage clock"
    # POS-04 declares both route writers internally on each tag.
    writers = {tag: model["new_data"]["raw_inputs"]["by_tag"][tag]["record_writer_available"]
               for tag in ("source", "target")}
    assert record["writers"] == [[writers["source"][r["id"]], writers["target"][r["id"]]]
                                  for r in corridor["paths"]], "record assigned writers"



# Owning boundary: evaluated values come from the constructed RawHandoff,
# not an independent Python table or a supplied semantic verdict.
def replace_probe_once(probe: str, old: str, new: str) -> str:
    count = probe.count(old)
    if count != 1:
        raise ValueError(f"expected one owning-probe extraction site, found {count}: {old!r}")
    return probe.replace(old, new, 1)


OWNING_PROBE = replace_probe_once(PRESENTATION_PROBE,
    "import CSTTT.Targets.GenericHandoff.POS04PresentationCoherence",
    "import CSTTT.Targets.GenericHandoff.POS04FinalReversal"
)
OWNING_PROBE = replace_probe_once(OWNING_PROBE,
    "(PresentationCoherence.factorBindings\n    (FramePresentation.presentation POS04PresentationCoherence.frames)).source.read canonical",
    "(OwningHandoff.factor (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline))).instructions.source.read canonical"
)
OWNING_PROBE = replace_probe_once(OWNING_PROBE,
    "(PresentationCoherence.factorView (POS04TemporalFactor.bindings tag)).read canonical",
    "(if tag == Tag.source then (OwningHandoff.factor (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline))).instructions.source else (OwningHandoff.factor (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline))).instructions.target).read canonical"
)
OWNING_PROBE = replace_probe_once(OWNING_PROBE,
    "POS04PresentationCoherence.raw.record.read canonical",
    "(OwningHandoff.lineage (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline))).record.read canonical"
)
OWNING_PROBE += r"""
-- All-partial adapters and direct semantic controls are kernel theorems.
example (m : RawLaneModel) :
    OwningHandoff.StrictTemporalLineage (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔
      POS04CompleteLineage.StrictTemporalLineage m := POS04RawHandoff.lineage_iff m
example (m : RawLaneModel) :
    OwningHandoff.IntegratedTargetRealization (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔
      IntegratedTargetRealization m := POS04RawHandoff.package_iff m
example (m : RawLaneModel) : POS04RawHandoff.FullAutonomy m ↔ AF m := POS04RawHandoff.full_iff_af m
example (m : RawLaneModel) : POS04RawHandoff.OperationalAutonomy m ↔ AO m := POS04RawHandoff.operational_iff_ao m
example : OwningHandoff.HandoffPass_F (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical :=
  POS04RawHandoff.positive_F
example : OwningHandoff.HandoffPass_O (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical :=
  POS04RawHandoff.positive_O
example : (¬ POS04RawHandoff.Package packageDeletion ∧ POS04RawHandoff.Lineage packageDeletion ∧ POS04RawHandoff.OperationalGame packageDeletion) ∧
  (POS04RawHandoff.Package lineageDeletion ∧ ¬ POS04RawHandoff.Lineage lineageDeletion ∧ POS04RawHandoff.OperationalGame lineageDeletion) ∧
  (POS04RawHandoff.Package withdrawalDeletion ∧ POS04RawHandoff.Lineage withdrawalDeletion ∧ ¬ POS04RawHandoff.OperationalGame withdrawalDeletion) :=
  POS04RawHandoff.O_control_vectors
example : POS04RawHandoff.OperationalGame POS04HistoricalDuplicateEvents.diagnostic := POS04RawHandoff.duplicate_event_operational
example : POS04RawHandoff.OperationalGame POS04RuntimeEquivalenceBoundary.missingPastTicks := POS04RawHandoff.missing_past_ticks_operational
example : ¬ POS04RawHandoff.FullGame POS04RuntimeEquivalenceBoundary.missingPastTicks := POS04RawHandoff.missing_past_ticks_full_rejected
example (m : RawLaneModel) :
    ¬ OwningHandoff.StrictTemporalLineage (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m)) (Assigned.put m.assignment .eventTable none) :=
  POS04RawHandoff.endpoint_deletion_no_lineage m
example : ¬ OwningHandoff.HandoffPass_F POS04RawHandoff.wrongOwner canonical ∧
    ¬ OwningHandoff.HandoffPass_O POS04RawHandoff.wrongOwner canonical := POS04RawHandoff.wrong_owner_rejected
-- All-coordinate receiver laws on every complete consumed-input projection.
example (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment) (hc : Assigned.Complete acquisitionDependencies a) :
    ReceiverContent.Laws (POS04RawHandoff.raw p) POS04ReceiverContent.instructions a
      (POS04ReceiverContent.ready a hc) (POS04ReceiverContent.historical_ready p a hc)
      (POS04ReceiverContent.target_ready p a hc) (POS04ReceiverContent.embedding_ready p a hc)
      (POS04AcquisitionEndpoint.data a) POS04FactorTransport.maps :=
  POS04ReceiverContent.checked_from_inputs p a hc
example (p : POS04ResourceRuntime.Protocol) :
    ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions canonical
      (POS04ReceiverContent.ready canonical (canonical_complete _))
      (POS04ReceiverContent.target_ready p canonical (canonical_complete _)) :=
  POS04ReceiverContent.positive_content_faithful p
example (p : POS04ResourceRuntime.Protocol) :
    ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.constant canonical
      (POS04ReceiverContent.constant_ready canonical (canonical_complete _))
      (POS04ReceiverContent.target_ready p canonical (canonical_complete _)) :=
  POS04ReceiverContent.constant_not_faithful p
example (p : POS04ResourceRuntime.Protocol) :
    ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions POS04ReceiverContent.sourceAbsent
      (POS04ReceiverContent.ready _ POS04ReceiverContent.source_absent_complete)
      (POS04ReceiverContent.target_ready p _ POS04ReceiverContent.source_absent_complete) :=
  POS04ReceiverContent.source_absent_not_faithful p
example (p : POS04ResourceRuntime.Protocol) :
    ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions POS04ReceiverContent.missingSourceTicks
      POS04ReceiverContent.missing_ticks_initial_ready (POS04ReceiverContent.missing_ticks_target_ready p) :=
  POS04ReceiverContent.missing_ticks_not_faithful p
-- Counterfactual intervention changes the primitive, then reruns the SAME receiver.
example (a : Assigned.Assignment) (tag : Tag) :
    TemporalFactorCells.decoded (POS04TemporalFactor.bindings tag) (POS04ReceiverIntervention.withoutSource a) =
      TemporalFactorCells.decoded (POS04TemporalFactor.bindings tag) a :=
  POS04ReceiverIntervention.latent_factor a tag
example (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment) :
    TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (POS04ReceiverIntervention.withoutSource a) ↔
      TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target a :=
  POS04ReceiverIntervention.target_ready_iff p a
example (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment)
    (hi : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (POS04ReceiverIntervention.withoutSource a))
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (POS04ReceiverIntervention.withoutSource a))
    (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
    ReceiverContent.receive (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (POS04ReceiverIntervention.withoutSource a) hi ht input = none ∧
    ReceiverContent.receivedClass (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (POS04ReceiverIntervention.withoutSource a) hi ht input = none :=
  POS04ReceiverIntervention.no_reception p a hi ht input
example (p : POS04ResourceRuntime.Protocol) :
    ∃ hi : RegisterInitialization.Ready POS04ReceiverContent.instructions.resetProgram (POS04ReceiverIntervention.withoutSource canonical),
      ∃ ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation (POS04RawHandoff.raw p)).target (POS04ReceiverIntervention.withoutSource canonical),
        ¬ ReceiverContent.ContentFaithful (POS04RawHandoff.raw p) POS04ReceiverContent.instructions (POS04ReceiverIntervention.withoutSource canonical) hi ht :=
  POS04ReceiverIntervention.baseline_rerun_rejected p
-- The protocol is derived from primitive views, then bound to the owning model.
example (m : RawLaneModel) :
    NominalProtocol.Pass POS04NominalProtocol.specification (POS04NominalProtocol.withdrawalData m)
      POS04NominalProtocol.tableViews (image m.assignment) ↔ POS04OperationalGame.Protocol m :=
  POS04NominalProtocol.pass_iff m
example (m : RawLaneModel) :
    NominalHandoff.Pass (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m))
      (POS04NominalHandoff.instructions (POS04ResourceRuntime.protocol m))
      (OwningHandoff.target (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment) ↔ POS04OperationalGame.Protocol m :=
  POS04NominalHandoff.protocol_iff m
example (m : RawLaneModel) :
    NominalHandoff.FullAutonomy (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m))
      (POS04NominalHandoff.instructions (POS04ResourceRuntime.protocol m)) m.assignment ↔ AF m :=
  POS04NominalHandoff.full_iff_af m
example (m : RawLaneModel) :
    NominalHandoff.OperationalAutonomy (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m))
      (POS04NominalHandoff.instructions (POS04ResourceRuntime.protocol m)) m.assignment ↔ AO m :=
  POS04NominalHandoff.operational_iff_ao m
example (p : POS04ResourceRuntime.Protocol) (a : Assigned.Assignment) :
    NominalHandoff.Laws (POS04RawHandoff.raw p) (POS04NominalHandoff.instructions p) a :=
  POS04NominalHandoff.laws p a
example (m : RawLaneModel) (k : Cell) (hk : k ∈ phase2Dependencies) (hm : image m.assignment k = none) :
    ¬ NominalProtocol.Pass POS04NominalProtocol.specification (POS04NominalProtocol.withdrawalData m)
      POS04NominalProtocol.tableViews (image m.assignment) := POS04NominalProtocol.missing_primitive_rejected m k hk hm
example : NominalProtocol.Pass POS04NominalProtocol.specification
    (POS04NominalProtocol.withdrawalData POS04HistoricalDuplicateEvents.diagnostic)
    POS04NominalProtocol.tableViews (image POS04HistoricalDuplicateEvents.diagnostic.assignment) :=
  POS04NominalProtocol.duplicate_event_pass
example : NominalProtocol.Pass POS04NominalProtocol.specification
    (POS04NominalProtocol.withdrawalData POS04RuntimeEquivalenceBoundary.missingPastTicks)
    POS04NominalProtocol.tableViews (image POS04RuntimeEquivalenceBoundary.missingPastTicks.assignment) :=
  POS04NominalProtocol.missing_past_ticks_pass
example : ¬ NominalProtocol.Pass POS04NominalProtocol.specification
    (POS04NominalProtocol.withdrawalData POS04HistoricalRuntimeProtocol.zeroLedger)
    POS04NominalProtocol.tableViews (image POS04HistoricalRuntimeProtocol.zeroLedger.assignment) :=
  POS04NominalProtocol.zero_ledger_rejected

-- Final receiver/nominal raw recipes and component gate correspondence.
example (m : RawLaneModel) : FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔
    NominalHandoff.HandoffPass_F (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m))
      (POS04NominalHandoff.instructions (POS04ResourceRuntime.protocol m)) m.assignment :=
  POS04FinalHandoff.full_gate_iff_nominal m
example (m : RawLaneModel) : FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔
    NominalHandoff.HandoffPass_O (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m))
      (POS04NominalHandoff.instructions (POS04ResourceRuntime.protocol m)) m.assignment :=
  POS04FinalHandoff.operational_gate_iff_nominal m
example (m : RawLaneModel)
    (hp : DispatchedPackage.Valid (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m)).package m.assignment)
    (hl : OwningHandoff.StrictTemporalLineage (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment) :
    ReceiverGate.Subcheck (POS04RawHandoff.raw (POS04ResourceRuntime.protocol m))
      (POS04ReceiverGate.instructions (POS04ResourceRuntime.protocol m)) (image m.assignment) :=
  POS04ReceiverGate.checked_of_package_lineage m hp hl
example : FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol baseline)) baseline.assignment :=
  POS04FinalHandoff.positive_F
example : FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol baseline)) baseline.assignment :=
  POS04FinalHandoff.positive_O
example : FinalHandoff.ReceiverReadout (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol baseline)) baseline.assignment :=
  POS04FinalHandoff.positive_receiver
example : ¬ FinalHandoff.ReceiverReadout POS04FinalHandoff.constant canonical := POS04FinalHandoff.constant_no_receiver_readout
example : ¬ FinalHandoff.HandoffPass_F POS04FinalHandoff.constant canonical ∧
    ¬ FinalHandoff.HandoffPass_O POS04FinalHandoff.constant canonical := POS04FinalHandoff.constant_no_handoff

example (m : RawLaneModel) :
    FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔
      POS04CompleteFIACH.HandoffPassF ⟨m⟩ := POS04FinalCorrespondence.final_full_iff_complete m
example (m : RawLaneModel) :
    FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔
      POS04CompleteFIACH.HandoffPassO ⟨m⟩ := POS04FinalCorrespondence.final_operational_iff_complete m
example : ¬ (∀ m : RawLaneModel,
    FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔ validF ⟨m⟩ = true) :=
  POS04FinalCorrespondence.legacy_full_gate_not_equivalent
example : ¬ (∀ m : RawLaneModel,
    FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol m)) m.assignment ↔ validO ⟨m⟩ = true) :=
  POS04FinalCorrespondence.legacy_operational_gate_not_equivalent
example : acquisitionRouteOutput reversedHistories .a = some 1 ∧
    acquisitionRouteOutput reversedHistories .b = some 0 ∧
    FinalHandoff.HandoffPass_F (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment ∧
    FinalHandoff.HandoffPass_O (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment :=
  POS04FinalReversal.outputs_and_certificates
example : FinalHandoff.ReceiverReadout (POS04FinalHandoff.raw (POS04ResourceRuntime.protocol reversedHistories)) reversedHistories.assignment :=
  POS04FinalReversal.receiver_readout

"""


def owning_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-owning-") as directory:
        path = Path(directory) / "Owning.lean"
        path.write_text(OWNING_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))

ENDPOINT_PROBE = r"""
import CSTTT.Targets.GenericHandoff.POS04RuntimeLineage
import Lean
open Lean CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TargetTheory.GenericHandoff
open POS04AcquisitionEndpoint
private def check (a : Assigned.Assignment) : Bool :=
  match AcquisitionEndpoint.decoded bindings a with
  | none => false
  | some d => !cfg.source.routes.isEmpty && cfg.source.routes.all (AcquisitionEndpoint.atRoute cfg d)
private def receiver (a : Assigned.Assignment) (r : RouteId) : Json :=
  match AcquisitionEndpoint.decoded bindings a with
  | none => Json.null
  | some d => match TemporalFactorRules.route d.source r with
    | none => Json.null
    | some route => Json.mkObj [
      ("history",toJson (d.source.histories route.history |>.map stateName)),
      ("path",toJson (route.eventPath.map eventName)),
      ("received",match AcquisitionEndpoint.received cfg d route.history with
        | none => Json.null | some s => toJson (stateName s)),
      ("target_history",toJson ((AcquisitionEndpoint.targetHistory cfg d route.history).map stateName))]
private def sample (m : RawLaneModel) :=
  let a := DispatchedPackage.global POS04DispatchedStage.raw m.assignment
  Json.mkObj [("endpoint_check",toJson (check a)),
    ("routes",Json.arr (routeIds.map (receiver a)).toArray)]
example (m : RawLaneModel) :
    RuntimeLineage.StrictTemporalLineage (POS04RuntimeLineage.raw (POS04ResourceRuntime.protocol m))
      (image m.assignment) ↔ POS04CompleteLineage.StrictTemporalLineage m :=
  POS04RuntimeLineage.generic_complete_iff m
#eval (Json.mkObj [
  ("cases",Json.mkObj [("Baseline",sample baseline),("G6-PACKAGE-ONLY",sample packageDeletion),
    ("G6-LINEAGE-ONLY",sample lineageDeletion),("G6-WITHDRAWAL-ONLY",sample withdrawalDeletion)]),
  ("row_scale",toJson cfg.rowScale),
  ("fallback",toJson (stateName cfg.fallback)),
  ("transfer",toJson (kernel.map fun s => stateName (cfg.transfer s))),
  ("missing_event_cell",toJson (check (Assigned.put canonical .eventTable none))),
  ("exit_deleted_complete",toJson (decide (Assigned.Complete acquisitionDependencies deleteExit))),
  ("exit_deleted_check",toJson (check deleteExit))]).compress
"""


def endpoint_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="tth06-endpoint-") as directory:
        path = Path(directory) / "Endpoint.lean"
        path.write_text(ENDPOINT_PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
                             capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare_endpoint(got: dict, results: dict, model: dict) -> None:
    assert set(got) == {"cases", "row_scale", "fallback", "transfer", "missing_event_cell",
                        "exit_deleted_complete", "exit_deleted_check"}, "endpoint export fields"
    assert set(got["cases"]) == set(results["cases"]), "endpoint comparison domain"
    # The integer-row scale is the least common denominator of published P.
    denominator = lcm(*(Fraction(w).denominator for row in model["t1_import"]["P"] for w in row))
    assert got["row_scale"] == denominator, "endpoint raw row scale"
    assert got["fallback"] == model["new_data"]["receiver"]["latent_target"]["factor_state"], "endpoint coordinate fallback"
    assert got["transfer"] == model["t1_import"]["kernel_order"], "raw coordinate-copy instruction"
    routes = model["new_data"]["corridor"]["paths"]
    histories = model["new_data"]["histories"]
    for name, case in got["cases"].items():
        assert set(case) == {"endpoint_check", "routes"}, f"{name}: endpoint fields"
        assert case["endpoint_check"] == results["cases"][name]["lineage"]["endpoint_link"], f"{name}: G6b endpoint"
        expected = [{"history": histories[r["source_history"]], "path": r["events"],
                     "received": histories[r["source_history"]][-1],
                     "target_history": histories[r["source_history"]]} for r in routes]
        assert case["routes"] == expected, f"{name}: raw receiver/route coordinates"
    assert got["missing_event_cell"] is False, "missing endpoint dependency"
    assert got["exit_deleted_complete"] is True, "exit deletion keeps primitive cells present"
    assert got["exit_deleted_check"] is False, "referenced exit deletion"


def main() -> None:
    results = json.loads(RESULTS.read_text())
    got = lean_snapshot()
    compare(got, results)
    print("PASS exact Lean/G6b comparison: route execution now reads the constructed closed-dispatcher staged global; all four controls; F/O lane vectors; both greatest sets; every positive-support phase-2 entry (factor, probability, budget, counter, tick, register); effective ledger; funded route readouts; all four snapshot coordinate checks and occurrences; new route execution's actual source support, receiver factors, actions, raw tuples, every target support branch and retained probe")
    for field, mutate in [
        ("lane", lambda x: x["Baseline"].__setitem__("package", False)),
        ("probability 1 -> 3/8", lambda x: x["Baseline"]["entries"][0].__setitem__("probability", "3/8")),
        ("invariant", lambda x: x["Baseline"]["greatestF"].pop()),
        ("route readout", lambda x: x["Baseline"]["route_readouts"].reverse()),
        ("intermediate snapshot", lambda x: x["Baseline"]["snapshot_coordinate_checks"].__setitem__(0, False)),
        ("executed receiver endpoint", lambda x: x["Baseline"]["executed_route_component"][0].__setitem__("receiver_factor", "p1w1")),
        ("actual target branch", lambda x: x["Baseline"]["executed_route_component"][0]["resulting_states"][0].__setitem__("factor", "p1w1")),
        ("retained branch probe", lambda x: x["Baseline"]["executed_route_component"][0]["result_readouts"].__setitem__(0, 1)),
    ]:
        broken = copy.deepcopy(got)
        mutate(broken)
        try:
            compare(broken, results)
        except AssertionError as error:
            print(f"CAUGHT planted {field} drift: {error}")
        else:
            raise AssertionError(f"escaped drift: {field}")
    semantic = semantic_snapshot()
    model = json.loads(MODEL.read_text())
    compare_semantic(semantic, model)
    print("PASS complete-execution regression: all 12 actual ambient outcome weights against frozen raw row plus declared relabeling; supported first step; source p2w0=" + semantic["source"]["p2w0"] + ", target p2w0=" + semantic["target"]["p2w0"])
    broken = copy.deepcopy(semantic)
    broken["target"]["p2w0"] = broken["source"]["p2w0"]
    try:
        compare_semantic(broken, model)
    except AssertionError as error:
        print(f"CAUGHT planted complete-execution branch drift: {error}")
    else:
        raise AssertionError("escaped complete-execution branch drift")
    temporal = temporal_snapshot()
    compare_temporal(temporal, model)
    print("PASS clause/runtime transcription: both tags, funded and unfunded, all 12 ambient states, all declared actions, every exact branch weight from Lean's raw instruction evaluator")
    broken = copy.deepcopy(temporal)
    tag = "target-funded"
    state = next(s for s, rows in broken[tag].items() if any(rows.values()))
    action = next(a for a, row in broken[tag][state].items() if row)
    broken[tag][state][action][0][1] = "3/8"  # Exact in-memory result drift.
    try:
        compare_temporal(broken, model)
    except AssertionError as error:
        print(f"CAUGHT planted interpreted temporal probability drift: {error}")
    else:
        raise AssertionError("escaped interpreted temporal probability drift")
    broken = copy.deepcopy(temporal)
    broken[tag][state][action] = None
    try:
        compare_temporal(broken, model)
    except AssertionError as error:
        print(f"CAUGHT planted missing temporal input drift: {error}")
    else:
        raise AssertionError("escaped missing temporal input drift")
    resource_values = resource_snapshot()
    lanes = json.loads((ROOT / "audit/proposed_models/TTH06-LANES.model.json").read_text())
    compare_resources(resource_values, results, model, lanes)
    print("PASS multi-resource interpreter transcription: all four controls; seven account identities, balances, owners and retention; six-role withdrawal; target and source-mode charges; exact effective ledger; required recharge and source presence")
    for field, mutate in [
        ("resource balance", lambda x: x["Baseline"]["accounts"]["target_recharge"].__setitem__("balance", "3/8")),
        ("resource ownership", lambda x: x["Baseline"]["accounts"]["target_recharge"].__setitem__("owner", 0)),
        ("withdrawal retention", lambda x: x["G6-WITHDRAWAL-ONLY"]["accounts"]["target_recharge"].__setitem__("retained", True)),
        ("missing charge", lambda x: x["Baseline"].__setitem__("target_charge", None)),
        ("acquisition as response", lambda x: x["Baseline"]["source_charge"].__setitem__("used", ["target_recharge"])),
    ]:
        broken = copy.deepcopy(resource_values)
        mutate(broken)
        try:
            compare_resources(broken, results, model, lanes)
        except AssertionError as error:
            print(f"CAUGHT planted {field} drift: {error}")
        else:
            raise AssertionError(f"escaped resource drift: {field}")
    historical = historical_snapshot()
    compare_historical(historical, results)
    print("PASS historical-support autonomy: actual folded-history/receiver/target entries for all four registered controls, exact probabilities and funding, AF/AO checks linked by arbitrary-partial game equivalences; both dependency diagnostics preserve baseline target entries")
    for field, mutate in [
        ("historical probability", lambda x: x["Baseline"]["entries"][0].__setitem__("probability", "3/8")),
        ("historical actual factor", lambda x: x["Baseline"]["entries"][0].__setitem__("factor", "p5w1")),
        ("historical funding", lambda x: x["Baseline"]["funded"].__setitem__(0, False)),
        ("historical branch deletion", lambda x: x["G6-PACKAGE-ONLY"]["entries"].pop()),
        ("historical dead tick", lambda x: x["missingPastTicks"].__setitem__("AO", False)),
        ("historical source availability", lambda x: x["sourceRechargeUnavailable"].__setitem__("AF", False)),
    ]:
        broken = copy.deepcopy(historical)
        mutate(broken)
        try:
            compare_historical(broken, results)
        except AssertionError as error:
            print(f"CAUGHT planted {field} drift: {error}")
        else:
            raise AssertionError(f"escaped historical drift: {field}")
    runtime_lineage = runtime_lineage_snapshot()
    compare_runtime_lineage(runtime_lineage, model)
    print("PASS polymorphic lineage-core instance transcription: defined source/receiver execution links, complete ordered action/outcome domains, every exact raw branch on both tags and funding regimes; whole arbitrary-partial extracted-endpoint adapter kernel-checked")
    for field, mutate in [
        ("omitted runtime outcome", lambda x: x["domains"]["source"]["outcomes"].pop()),
        ("omitted runtime action", lambda x: x["domains"]["target"]["actions"].pop()),
        ("runtime branch weight", lambda x: x["rows"]["source-funded"]["p1w0"]["cw"][0].__setitem__(1, "3/8")),
        ("runtime actual branch", lambda x: x["rows"]["target-funded"]["p1w0"]["cw"].pop()),
    ]:
        broken = copy.deepcopy(runtime_lineage)
        mutate(broken)
        try:
            compare_runtime_lineage(broken, model)
        except AssertionError as error:
            print(f"CAUGHT planted {field} drift: {error}")
        else:
            raise AssertionError(f"escaped runtime-lineage drift: {field}")
    public_runtime = public_runtime_snapshot()
    compare_public_runtime(public_runtime, runtime_lineage)
    print("PASS public constructed-target span: historical target rows agree exactly with raw runtime rows in both funding regimes on all 12 ambient states and 3 actions; arbitrary-partial target and F/O/complete-lineage adapters kernel-checked; broken empty row directly rejected")
    for mode in ("target-funded", "target-unfunded"):
        broken = copy.deepcopy(public_runtime)
        broken[mode]["p1w0"]["cw"] = [["p0w0", "3/8"]]
        try:
            compare_public_runtime(broken, runtime_lineage)
        except AssertionError as error:
            print(f"CAUGHT planted public {mode} row drift: {error}")
        else:
            raise AssertionError(f"escaped public-runtime row drift: {mode}")
    endpoint = endpoint_snapshot()
    compare_endpoint(endpoint, results, model)
    print("PASS generic endpoint extraction: every G6b endpoint outcome, raw receiver terminals, route tuples and mapped histories; scale and coordinate instruction; direct missing-cell and present-cell exit-deletion checks; universal complete-lineage adapter kernel-checked")
    for field, mutate in [
        ("endpoint outcome", lambda x: x["cases"]["Baseline"].__setitem__("endpoint_check", False)),
        ("endpoint receiver", lambda x: x["cases"]["Baseline"]["routes"][0].__setitem__("received", "p1w1")),
        ("endpoint coordinate instruction", lambda x: x["transfer"].__setitem__(0, "p1w0")),
        ("endpoint deletion", lambda x: x.__setitem__("exit_deleted_check", True)),
    ]:
        broken = copy.deepcopy(endpoint)
        mutate(broken)
        try:
            compare_endpoint(broken, results, model)
        except AssertionError as error:
            print(f"CAUGHT planted {field} drift: {error}")
        else:
            raise AssertionError(f"escaped endpoint drift: {field}")
    presentation = presentation_snapshot()
    compare_presentation(presentation, model)
    print("PASS endpoint/factor/record presentation: all factor rows on both tags exactly match JSON; raw event fields, unit increments, realization, assigned writers and stage clock; universal partial decoder/frame/primitive equations and missing-input/event guards kernel-checked")
    for field, mutate in [
        ("presentation factor probability", lambda x: x["target"]["p1w0"]["cw"][0].__setitem__(1, "3/8")),
        ("presentation record event", lambda x: x["record"]["events"][0].__setitem__("source_support", False)),
        ("presentation record clock", lambda x: x["record"]["clock"].__setitem__(3, 0)),
        ("presentation record writer", lambda x: x["record"]["writers"][0].__setitem__(1, False)),
    ]:
        broken = copy.deepcopy(presentation)
        mutate(broken)
        try:
            compare_presentation(broken, model)
        except AssertionError as error:
            print(f"CAUGHT planted {field} drift: {error}")
        else:
            raise AssertionError(f"escaped presentation drift: {field}")
    owning = owning_snapshot()
    compare_presentation(owning, model)
    print("PASS owning RawHandoff boundary: evaluated constructed factor rows and record tables against frozen JSON; all-partial P and complete lineage adapters, nominal-protocol-qualified AF/AO adapters, positive F/O certificates and direct named control/diagnostic regressions kernel-checked; universal receiver reset equations, total content preservation and direct constant/source-absent/missing-input controls kernel-checked; raw source-absence rerun, all-partial latent-factor preservation and readiness equivalence kernel-checked; exact every-partial final-to-complete whole-gate adapters, direct legacy-gate counterexample and complete reversed-history F/O/receiver certificates with computed outputs 1/0 kernel-checked")
    for field, mutate in [
        ("owning factor probability", lambda x: x["source"]["p1w0"]["cw"][0].__setitem__(1, "3/8")),
        ("owning record realization", lambda x: x["record"]["realized"].pop()),
    ]:
        broken = copy.deepcopy(owning)
        mutate(broken)
        try:
            compare_presentation(broken, model)
        except AssertionError as error:
            print(f"CAUGHT planted {field} drift: {error}")
        else:
            raise AssertionError(f"escaped owning drift: {field}")
    print("Polymorphic scope: staged target/resource instructions and the target-execution span are publicly bound. The raw frame-to-presentation constructor and exact partial POS-04 presentation equations are checked; the owning raw-interface component boundary, generic F/O soundness and common-coordinate receiver square are checked. The generic nominal protocol and its exact arbitrary-partial AF/AO owning adapters are checked. Receiver/counterfactual coherence is incorporated into the owning final gate, whose exact all-partial POS04 adapters to the nominal gate are checked. The complete whole-gate correspondence is exact for every partial assignment, preserving the frozen source/staging/package/nominal autonomy checks with complete actual lineage. The weaker legacy whole-gate identification is kernel-refuted. Reversed raw histories pass both final gates with computed outputs 1/0. Independent ACCEPT / FAITHFUL adjudication is recorded in audit/G6d_final_correspondence.md; TTH-06 is proved at the explicitly disclosed structural grades and F/O interpretation, with the frozen row text unchanged.")
    print("Legacy G6b vectors above certify their unchanged weaker lineage. Complete named lineage, its family vectors, and F/O soundness are separately kernel-proved in POS04CompleteLineage/POS04CompleteFIACH; they are not inferred from those legacy booleans.")
    print("Coverage limit: finite observations are compared here; unbounded word laws, generic fixed-point greatest-ness, and TTH-05 soundness are theorems, not Python transcription results. Raw POS-04 cells remain covered by check_pos04_transcription.py.")

if __name__ == "__main__":
    main()
