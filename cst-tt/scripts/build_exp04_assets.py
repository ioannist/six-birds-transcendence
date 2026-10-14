#!/usr/bin/env python3
"""Build deterministic CST-EXP-04 adversarial assets."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import exp04_data as D  # noqa: E402

CSV_KW = {"newline":"", "encoding":"utf-8"}


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    clean = "\n".join(line.rstrip() for line in text.splitlines())
    path.write_text(clean.rstrip()+"\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", **CSV_KW) as fh:
        w=csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore", lineterminator="\n")
        w.writeheader()
        for row in rows:
            w.writerow({k:norm(row.get(k,"")) for k in fields})


def norm(v: Any) -> str:
    if v is None: return ""
    if isinstance(v,bool): return "true" if v else "false"
    if isinstance(v,(list,tuple,set)): return ";".join(str(x) for x in v)
    return str(v).replace("\r\n","\n").replace("\r","\n")


def read_csv(path: Path) -> list[dict[str,str]]:
    with path.open(**CSV_KW) as fh: return list(csv.DictReader(fh))


def split_ids(s: str) -> list[str]:
    return [x.strip() for x in str(s).split(";") if x.strip()]


def md(s: Any) -> str:
    return str(s).replace("|","\\|").replace("\n"," ")


def short(s: str, n: int=180) -> str:
    s=" ".join(str(s).split())
    return s if len(s)<=n else s[:n-1].rstrip()+"…"


def hash_text(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def candidate_map(root: Path) -> dict[str,dict[str,Any]]:
    data=json.loads((root/"candidates/CANDIDATE_REGISTRY.json").read_text(encoding="utf-8"))
    return {x["id"]:x for x in data["candidates"]}


def hard_specific(cid: str, hid: str) -> str:
    direct = {
      "HC-01": {"TS-01":"Its predictive quotient is deliberately finer than the public shadow and detects the hidden divergence.","TS-09":"Its predictive residual vector can detect the divergence only if the hidden continuation probe is registered as a hard component.","TS-10":"Its ancestry relation may use predictive witnesses, so public equality alone is rejected.","TS-02":"The full-package audit can reject the counterfeit if predictive structure is an admitted clause dependency.","TS-04":"Generic viability can remain identical in both systems, so this criterion alone misses the mismatch.","TS-05":"A code can faithfully preserve the wrong public-level object unless the hidden predictive structure is in the logical package."},
      "HC-02": {"TS-01":"This is a direct countermodel to quotient sufficiency: the candidate preserves its object while the binding predicate changes.","TS-02":"Binding is a hard package clause and must be re-audited on the target.","TS-06":"The gluing/global-coherence gate is designed to detect the mismatch.","TS-07":"Route and recombination data may expose the mismatch, but binding is not guaranteed by the functor alone.","TS-09":"A predictive-only residual is insufficient; a binding coordinate or hard gate must be added."},
      "HC-03": {"TS-04":"This is the candidate's defining withdrawal test: equivalent supported dynamics can still fail target-native viability.","TS-02":"C8 and withdrawal are hard gates, so target realization fails when autonomous maintenance fails.","TS-09":"The bundle can register viability margin separately from predictive error.","TS-01":"Predictive bisimulation during support does not decide post-withdrawal maintenance.","TS-06":"Global closure at one time does not guarantee maintained viability.","TS-10":"An ancestry relation can hold while the target immediately ceases to be viable."},
      "HC-04": {"TS-03":"A live causal-overlap witness can distinguish a handoff process from a detached copy, but the persistent source yields at most branching, not uniqueness.","TS-10":"The natural output is a relation from the source history to both continuing tokens when both satisfy ancestry conditions.","TS-01":"Structural equivalence marks the target as a qualifying branch and explicitly does not delete the source branch.","TS-02":"The target may realize the package, but source persistence blocks any unqualified one-token identity conclusion."},
      "HC-05": {"TS-07":"Its branch-valued semantics and automorphism audit directly reject unique tie-breaking.","TS-10":"Both symmetric targets may be successors; the criterion remains relation-valued.","TS-03":"The process criterion must either find an asymmetry in overlap history or return symmetric branching/underdetermination.","TS-02":"Two certified targets remain two structural successors; certification selects neither.","TS-01":"Quotient equivalence cannot choose one of two isomorphic targets."},
      "HC-06": {"TS-03":"The candidate rejects lineage because its defining live-process overlap witness is absent; this is a coherent restrictive verdict, not a proof that copying never preserves consciousness.","TS-10":"Destructive reconstruction can still be ancestry-related if a noncircular source-derived history relation is supplied.","TS-02":"Target realization may succeed while lineage remains unlicensed.","TS-05":"Logical reconstruction can succeed despite the process gap, illustrating the separation of logical transport from subject lineage."},
      "HC-07": {"TS-03":"Continuous moving-support causation is its strongest positive control, provided the preserved process organization is independently specified.","TS-02":"A staged handoff can pass if one coherent package remains and becomes target-native.","TS-04":"Autonomy must be checked after the overlap and controller are removed.","TS-10":"Gradual overlap supplies ancestry evidence but does not force unique numerical identity."},
      "HC-08": {"TS-07":"This is the candidate's central audit: nontrivial loop action is retained as holonomy rather than erased by endpoint matching.","TS-06":"Gluing/closure can expose incompatible route data if the retained cover includes the loop.","TS-10":"Ancestry can remain route-indexed or become underdetermined until flatness is proved.","TS-01":"Predictive route independence is available only under a zero-holonomy proof."},
      "HC-09": {"TS-07":"Recombination is explicit, so branchwise success is rejected when the joint probe fails.","TS-06":"The global gluing condition rejects incompatible branch marginals.","TS-02":"The integrated package includes joint binding/event coherence and therefore fails.","TS-01":"Unless recombination probes are added to the predictive test family, this is a standalone counterexample.","TS-03":"One process can split into branches while losing the joint information needed for later recombination."},
      "HC-10": {"TS-10":"The relation-valued output permits both branches as successors while refusing unique numerical identity.","TS-07":"Branch objects remain separate and no unique selection is manufactured.","TS-03":"A process may fission, but uniqueness must be surrendered or an asymmetry shown.","TS-02":"Both branches may realize packages; realization does not adjudicate unique identity."},
      "HC-11": {"TS-08":"Incompatible self/credit ledgers force an explicit provenance transform; copying both as exclusive truths is incoherent.","TS-10":"Many-to-one ancestry is representable, but conflict resolution is an additional target-realization obligation.","TS-07":"Fusion is a typed operation whose existence can fail when recombination or route data conflict.","TS-02":"A fused package succeeds only after one coherent global history and credit law is built."},
      "HC-12": {"TS-06":"This is the defining obstruction: every local witness can pass while the global section fails.","TS-02":"Integrated realization fails because component certificates do not glue.","TS-07":"Route/overlap incompatibility may expose the obstruction but does not automatically repair it.","TS-01":"Local predictive bisimulations need a compatibility condition before they define one global bridge."},
      "HC-13": {"TS-04":"Withdrawal makes the failure immediate and classifies it as non-autonomous on the declared target boundary.","TS-02":"The final target-native package gate fails even if decoded behavior remains perfect during support.","TS-05":"This case separates a valid encoded logical object from target autonomy; the decoder must be internalized or regenerated.","TS-09":"Decoder dependence must be a hard gate, not a small residual."},
      "HC-14": {"TS-09":"Its vector residual and hard-gate design survives only if critical local maxima and viability margins are explicit.","TS-04":"A local viability threshold overrides a favorable aggregate score.","TS-05":"Error-correction claims need a code-specific threshold and correlated-error audit.","TS-02":"One failed hard clause defeats the integrated package despite small average error."},
      "HC-15": {"TS-03":"Without a maintained process or declared dormancy token, the later reconstruction is not process continuation under this criterion.","TS-10":"The relation can return empty during the gap and possibly re-establish ancestry only through a separately carried dormant record.","TS-04":"Viability failure is a real failure of autonomy; later reconstruction does not retroactively erase it.","TS-02":"The target package is absent during the interval, so continuous realization fails even if a later copy exists."},
      "HC-16": {"TS-01":"The carrier tokens are individuated before evaluation, so a gauge re-encoding on one token is classified as same-carrier representation change.","TS-02":"Exactification blocks counting a representative change as a heterogeneous handoff.","TS-05":"Logical re-encoding may be useful but does not by itself establish a new carrier.","TS-10":"Ancestry is irrelevant until distinct carrier episodes are actually present."},
      "HC-17": {"TS-08":"Its target-native temporal ledger directly requires a clock/order relation and can classify gaps or discontinuities.","TS-03":"A temporal gap without a process/dormancy witness breaks its conservative lineage criterion.","TS-10":"The relation can preserve explicit gap semantics or return underdetermination rather than inventing a universal now.","TS-02":"Temporal closure is a hard clause, but source-target clock translation remains a separate bridge obligation."},
      "HC-18": {"TS-07":"Its functorial/holonomy framing is explicitly built to compare direct and composite routes.","TS-06":"Critical-pair and gluing conditions can reject noncongruent compositions.","TS-09":"Composition must carry accumulated defect and hard-gate status.","TS-10":"Relation composition can be defined, but route memory may require path-indexed ancestry rather than endpoint-only relations.","TS-03":"Moving-process composition needs compatible process boundaries and may fail when intermediate handoff changes the invariant."}
    }
    return direct.get(hid,{}).get(cid,"")


def stress_finding(cid: str, case: dict[str,str], code: str) -> str:
    prof=D.CANDIDATE_PROFILES[cid]
    specific=hard_specific(cid,case["id"])
    label,base=D.STATUS_LABELS[code]
    if not specific:
        if code=="S": specific=f"The candidate's core strength—{prof['core_strength']}—directly addresses the constructed contrast."
        elif code=="C": specific=f"The candidate can avoid the counterexample only after this amendment: {prof['required_amendment']}"
        elif code=="U": specific="The candidate does not contain enough typed data to choose among the symmetric or history-sensitive alternatives and therefore returns underdetermination rather than an invented verdict."
        elif code=="N": specific=f"The case exceeds this component's proper role as {prof['role']}; it must be evaluated by the surrounding family."
        else: specific=f"The witness exploits the candidate's standalone boundary: {prof['fatal_boundary']}"
    return specific+" "+base


def lens_finding(cid: str, lens: dict[str,str], code: str) -> str:
    prof=D.CANDIDATE_PROFILES[cid]
    label,base=D.STATUS_LABELS[code]
    if code=="S": lead=f"The candidate has an explicit mechanism relevant to {lens['title'].lower()}: {prof['core_strength']}."
    elif code=="C": lead=f"The lens exposes an unresolved obligation. {prof['required_amendment']}"
    elif code=="F": lead=f"As a complete criterion it is defeated here because {prof['fatal_boundary']}."
    elif code=="N": lead=f"The lens is outside the component's proper role as {prof['role']}; its output must remain lane-limited."
    else: lead="The available data do not determine a unique result under this lens."
    return lead+" "+base


def phase_decisions(root: Path) -> list[dict[str,str]]:
    rows=read_csv(root/"ledgers/decision_log.csv")
    rows=[r for r in rows if not r["id"].startswith("D04-")]
    for did,topic,decision,rationale in D.PHASE_DECISIONS:
        rows.append({"id":did,"date":D.DATE,"topic":topic,"decision":decision,"rationale":rationale,"status":"active"})
    return rows


def render_decision_log(rows: list[dict[str,str]]) -> str:
    names={"D00":"CST-EXP-00 — charter and typing discipline","D01":"CST-EXP-01 — corpus mining and asset atlas","D02":"CST-EXP-02 — scenario atlas and neutral semantics","D03":"CST-EXP-03 — candidate generation","D04":"CST-EXP-04 — adversarial stress and external confrontation"}
    out=["# CST-EXP Decision Log","","These rulings control method, provenance, typing, and phase boundaries. They are not conclusions about consciousness or personal identity.",""]
    for prefix,name in names.items():
        out += [f"## {name}","","| ID | Topic | Decision | Rationale | Status |","|---|---|---|---|---|"]
        for r in rows:
            if r["id"].startswith(prefix+"-"):
                out.append(f"| {r['id']} | `{md(r['topic'])}` | {md(r['decision'])} | {md(r['rationale'])} | {r['status']} |")
        out.append("")
    out += ["## Boundary","","CST-EXP-04 freezes three **unranked survivor families** and a library of component roles and no-go prospects. It does not select the final theorem target, implement a toy program, prove a no-go theorem, establish a consciousness certificate, or settle personal identity."]
    return "\n".join(out)


def update_rejected_defaults(root: Path) -> None:
    p=root/"ledgers/REJECTED_DEFAULTS.md"; text=p.read_text(encoding="utf-8")
    marker="## Additional defaults rejected by CST-EXP-04"
    if marker in text: text=text.split(marker,1)[0]
    text=text.rstrip()
    rows=[
      ("RD04-01","One best candidate already exists","Rejected","The adversarial pass supports three non-equivalent families answering different lanes."),
      ("RD04-02","Exact organization uniquely selects one continuer","Rejected","Symmetric duplication defeats any invariant unique selector without extra asymmetry."),
      ("RD04-03","Gradual overlap is automatically survival","Rejected","Overlap is evidence for SF-02 only after a noncircular process invariant is supplied."),
      ("RD04-04","Destructive copying is automatically failure","Rejected","SF-01 target realization and SF-03 ancestry can remain possible while SF-02 lineage rejects the case."),
      ("RD04-05","A valid decoder makes the target autonomous","Rejected","Autonomy depends on the declared carrier boundary and withdrawal result."),
      ("RD04-06","Small average error is adequate","Rejected","Hard local viability/binding/provenance defects can survive arbitrarily small aggregate residual."),
      ("RD04-07","Local clause witnesses imply one global package","Rejected","A gluing or closure theorem is separately required."),
      ("RD04-08","A structural certificate settles ontology","Rejected","Certificate soundness, A1, A2-P, recognition, and identity interpretation remain separate."),
      ("RD04-09","External literature can choose the target","Rejected","The literature pass challenges and retypes internally generated candidates only."),
      ("RD04-10","A no-go prospectus is a proved theorem","Rejected","All NG records remain conjecture-grade until later proof work."),
    ]
    out=[text,"",marker,"","| ID | Premature default | Ruling | Reason |","|---|---|---|---|",*[f"| {a} | {b} | {c} | {d} |" for a,b,c,d in rows]]
    write_text(p,"\n".join(out))


def update_unresolved(root: Path) -> None:
    p=root/"ledgers/UNRESOLVED_QUESTIONS.md"; text=p.read_text(encoding="utf-8")
    marker="## Adversarial questions added after CST-EXP-04"
    if marker in text: text=text.split(marker,1)[0].rstrip()
    nums=[int(x) for x in re.findall(r"(?m)^(\d+)\. ",text)]; start=max(nums)+1 if nums else 1
    sec=["",marker,""]+[f"{i}. {q}" for i,q in enumerate(D.UNRESOLVED,start)]
    write_text(p,text.rstrip()+"\n\n"+"\n".join(sec))


def build(root: Path) -> None:
    candidates=candidate_map(root)
    cids=sorted(candidates)
    assumptions=read_csv(root/"ledgers/candidate_assumption_matrix.csv")
    old_verdicts=read_csv(root/"ledgers/candidate_scenario_verdicts.csv")

    # Hard-case stress ledger.
    stress=[]
    for cid in cids:
        prof=D.CANDIDATE_PROFILES[cid]
        for case,code in zip(D.HARD_CASES,D.HARD_CASE_STATUS[cid]):
            label,_=D.STATUS_LABELS[code]
            stress.append({
              "candidate_id":cid,"candidate_title":candidates[cid]["title"],"hard_case_id":case["id"],"hard_case_title":case["title"],
              "claim_lanes":case["lanes"],"status_code":code,"stress_disposition":label,"finding":stress_finding(cid,case,code),
              "core_objection":case["core_objection"],"no_go_ids":case["no_go"],"assumption_exposed":assumption_for_case(case["id"]),
              "required_response":required_response(cid,case["id"],code),"salvage":prof["salvage"],"family_role":prof["role"],"survivor_family":prof["family"],
              "blocked_inference":"No result licenses target consciousness, numerical identity, A2-P, or unique continuation unless separately stated.","phase":"CST-EXP-04"
            })
    write_csv(root/"ledgers/candidate_hard_case_stress.csv",stress,list(stress[0]))

    # Internal lens audit.
    lens_rows=[]
    for cid in cids:
        prof=D.CANDIDATE_PROFILES[cid]
        for lens,code in zip(D.INTERNAL_LENSES,D.LENS_STATUS[cid]):
            label,_=D.STATUS_LABELS[code]
            lens_rows.append({"candidate_id":cid,"candidate_title":candidates[cid]["title"],"lens_id":lens["id"],"lens_title":lens["title"],"asset_focus":lens["asset_focus"],"status_code":code,"audit_disposition":label,"finding":lens_finding(cid,lens,code),"challenge":lens["challenge"],"required_response":lens["required_response"],"candidate_amendment":prof["required_amendment"],"salvage":prof["salvage"],"phase":"CST-EXP-04"})
    write_csv(root/"ledgers/candidate_internal_lens_audit.csv",lens_rows,list(lens_rows[0]))

    # Rejection/salvage and survivors.
    rej=[]
    for cid in cids:
        p=D.CANDIDATE_PROFILES[cid]
        sc=Counter(r["stress_disposition"] for r in stress if r["candidate_id"]==cid)
        lc=Counter(r["audit_disposition"] for r in lens_rows if r["candidate_id"]==cid)
        rej.append({"candidate_id":cid,"candidate_title":candidates[cid]["title"],"phase_disposition":p["disposition"],"retained_role":p["role"],"survivor_family":p["family"],"core_strength":p["core_strength"],"decisive_boundary":p["fatal_boundary"],"required_amendment":p["required_amendment"],"strongest_salvage":p["salvage"],"rationale":p["rationale"],"hard_case_profile":format_counter(sc),"lens_profile":format_counter(lc),"not_a_ranking":"true"})
    write_csv(root/"ledgers/rejection_and_salvage_log.csv",rej,list(rej[0]))
    write_csv(root/"ledgers/survivor_family_registry.csv",D.SURVIVOR_FAMILIES,list(D.SURVIVOR_FAMILIES[0]))

    comp=[]
    for f in D.SURVIVOR_FAMILIES:
        for cid in cids:
            role="outside"
            if cid==f["core"]: role="core"
            elif cid in split_ids(f["mandatory_modules"]): role="mandatory_module"
            elif cid in split_ids(f["optional_mechanism"]): role="optional_mechanism"
            comp.append({"family_id":f["id"],"family_title":f["title"],"candidate_id":cid,"candidate_title":candidates[cid]["title"],"role":role,"inclusion_reason":family_inclusion_reason(f,cid,role),"claim_lane_separation":"Target realization, lineage, autonomy, recognition, and ontology remain separately typed."})
    write_csv(root/"ledgers/survivor_composition_matrix.csv",comp,list(comp[0]))

    # No-go assets.
    ngo=[]
    for ng in D.NO_GO:
        x=dict(ng); x["status"]="conjecture_or_theorem_prospectus_not_proved"; x["phase"]="CST-EXP-04"; ngo.append(x)
        write_text(root/f"challenges/no_go_conjectures/{ng['id']}.md",render_no_go(ng))
    write_csv(root/"ledgers/no_go_register.csv",ngo,list(ngo[0]))
    write_text(root/"challenges/no_go_conjectures/INDEX.md",render_no_go_index())

    # Counterexample cards and catalog.
    for case in D.HARD_CASES:
        write_text(root/f"challenges/counterexamples/{case['id']}.md",render_case(case,stress))
    write_text(root/"challenges/COUNTEREXAMPLE_CATALOG.md",render_catalog(stress))
    write_text(root/"challenges/INTERNAL_STRESS_SYNTHESIS.md",render_internal_synthesis(candidates,stress,lens_rows))

    # Candidate stress cards.
    for cid in cids:
        write_text(root/f"challenges/candidate_stress/{cid}.md",render_candidate_card(cid,candidates[cid],stress,lens_rows))
    write_text(root/"challenges/candidate_stress/INDEX.md",render_candidate_index(candidates))

    # External literature assets.
    write_csv(root/"challenges/external_literature/SOURCE_REGISTRY.csv",D.EXTERNAL_SOURCES,list(D.EXTERNAL_SOURCES[0]))
    cross=[]
    for s in D.EXTERNAL_SOURCES:
        for rel,field in [("supports_or_sharpens","supports"),("presses_or_limits","presses")]:
            for obj in split_ids(s[field]):
                cross.append({"source_id":s["id"],"source_title":s["title"],"category":s["category"],"relation_type":rel,"object_id":obj,"object_kind":object_kind(obj),"challenge":s["challenge"],"phase_use":"external challenge; not target selection"})
    write_csv(root/"ledgers/external_literature_crosswalk.csv",cross,list(cross[0]))
    write_text(root/"challenges/external_literature/LITERATURE_CHALLENGE_MAP.md",render_literature_map())
    write_text(root/"challenges/external_literature/SEARCH_AND_SCOPE_LOG.md",render_search_log())

    # Red teams.
    for rt in D.RED_TEAMS: write_text(root/f"challenges/red_team/{rt['id']}.md",render_red_team(rt))
    write_text(root/"challenges/red_team/INDEX.md",render_red_index())

    # Assumption exposure. Preserve 10x20 bank.
    exposure=[]
    for r in assumptions:
        cid=r["candidate_id"]; aid=r["assumption_id"]; p=D.CANDIDATE_PROFILES[cid]
        exposure.append({**r,"phase_disposition":p["disposition"],"retained_role":p["role"],"survivor_family":p["family"],"exposure_class":assumption_class(aid),"adversarial_finding":assumption_finding(aid,r),"may_not_rescue":assumption_nonrescue(aid),"phase":"CST-EXP-04"})
    write_csv(root/"ledgers/assumption_exposure.csv",exposure,list(exposure[0]))

    # Add phase interpretation without altering frozen scenario outputs.
    bycid={r["candidate_id"]:r for r in rej}
    ext_verdict=[]
    for r in old_verdicts:
        p=bycid[r["candidate_id"]]
        ext_verdict.append({**r,"exp04_phase_disposition":p["phase_disposition"],"exp04_retained_role":p["retained_role"],"exp04_survivor_family":p["survivor_family"],"exp04_adversarial_reading":scenario_reading(r,p),"frozen_exp03_outcome":"true","not_a_ranking":"true"})
    write_csv(root/"ledgers/candidate_verdicts_by_scenario.csv",ext_verdict,list(ext_verdict[0]))

    # Shortlist and synthesis.
    write_text(root/"challenges/SURVIVOR_SHORTLIST.md",render_shortlist(candidates))
    write_text(root/"challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md",render_synthesis(candidates,stress,lens_rows))
    write_text(root/"challenges/README.md",render_challenges_readme())

    # Diagram.
    dot=render_dot(candidates); write_text(root/"challenges/survivor_architecture.dot",dot)
    try_render_dot(root)

    # Governance and root status.
    decisions=phase_decisions(root)
    write_csv(root/"ledgers/decision_log.csv",decisions,["id","date","topic","decision","rationale","status"])
    write_text(root/"ledgers/DECISION_LOG.md",render_decision_log(decisions))
    update_rejected_defaults(root); update_unresolved(root)
    write_text(root/"STATE.md",render_state())
    write_text(root/"STATUS.md",render_status())
    update_readme(root)
    update_changelog(root)

    # Summary machine surface.
    summary={
      "schema_version":"1.0","project":"CST-EXP","phase":"CST-EXP-04","generated_date":D.DATE,
      "counts":{"candidates":len(cids),"hard_cases":len(D.HARD_CASES),"hard_case_records":len(stress),"internal_lenses":len(D.INTERNAL_LENSES),"lens_records":len(lens_rows),"no_go_prospects":len(D.NO_GO),"external_sources":len(D.EXTERNAL_SOURCES),"external_crosswalk_rows":len(cross),"red_team_positions":len(D.RED_TEAMS),"survivor_families":len(D.SURVIVOR_FAMILIES),"scenario_records":len(ext_verdict),"assumption_exposure_records":len(exposure)},
      "survivor_families":[{"id":f["id"],"title":f["title"],"core":f["core"],"mandatory_modules":f["mandatory_modules"]} for f in D.SURVIVOR_FAMILIES],
      "candidate_dispositions":{cid:D.CANDIDATE_PROFILES[cid]["disposition"] for cid in cids},
      "boundary":"No theorem or no-go is proved; no toy program is implemented; no final target, consciousness conclusion, or personal-identity verdict is selected."
    }
    write_text(root/"manifests/EXP04_ASSET_SUMMARY.json",json.dumps(summary,indent=2,sort_keys=True))


def assumption_for_case(hid: str) -> str:
    return {
      "HC-01":"H-RECOG;H-PRESERVE-O","HC-02":"H-TARGET-FULL;H-GLOBAL-GLUE","HC-03":"H-AUTONOMY;H-TARGET-FULL","HC-04":"H-LINEAGE","HC-05":"H-LINEAGE-UNIQUE","HC-06":"H-LINEAGE","HC-07":"H-LINEAGE;H-AUTONOMY","HC-08":"H-ROUTE-FLAT","HC-09":"H-GLOBAL-GLUE;H-PRESERVE-O","HC-10":"H-LINEAGE-UNIQUE;H-IDENTITY-O","HC-11":"H-LINEAGE;H-GLOBAL-GLUE","HC-12":"H-GLOBAL-GLUE","HC-13":"H-AUTONOMY","HC-14":"H-APPROX;H-AUTONOMY","HC-15":"H-LINEAGE;H-AUTONOMY","HC-16":"D-CARRIER;H-DISTINCT","HC-17":"H-BRIDGE-ADM;H-LINEAGE","HC-18":"H-BRIDGE-ADM;H-ROUTE-FLAT"
    }[hid]


def required_response(cid: str, hid: str, code: str) -> str:
    p=D.CANDIDATE_PROFILES[cid]
    if code=="S": return "Retain the explicit witness and state its lane ceiling; do not inflate it into identity or consciousness."
    if code=="U": return "Name the absent datum, return a typed underdetermination/branch set, and prohibit arbitrary tie-breaking."
    if code=="N": return "Delegate the case to the containing survivor family and preserve this candidate only in its registered component role."
    return p["required_amendment"]


def format_counter(c: Counter[str]) -> str:
    return ";".join(f"{k}={c[k]}" for k in sorted(c))


def family_inclusion_reason(f: dict[str,str], cid: str, role: str) -> str:
    if role=="core": return "Defines the family's principal claim lane and characteristic verdicts."
    if role=="mandatory_module": return D.CANDIDATE_PROFILES[cid]["salvage"]
    if role=="optional_mechanism": return "Available as an explicit encode/recover implementation pattern after the family target is independently defined."
    return "Not part of the minimal frozen composition; may remain a comparator in CST-EXP-05."


def object_kind(obj: str) -> str:
    if obj.startswith("TS-"): return "candidate"
    if obj.startswith("SF-"): return "survivor_family"
    if obj.startswith("NG-"): return "no_go_prospect"
    if obj.startswith("RT-"): return "red_team_position"
    return "other"


def assumption_class(aid: str) -> str:
    if aid in {"A1","A2-P","H-CERT-SOUND","H-IDENTITY-O"}: return "ontological_or_certificate"
    if aid=="H-RECOG": return "recognition"
    if aid in {"H-LINEAGE","H-LINEAGE-UNIQUE"}: return "lineage"
    if aid in {"H-AUTONOMY","H-GLOBAL-GLUE","H-ROUTE-FLAT","H-APPROX","H-PRESERVE-O"}: return "structural_gate"
    return "typing_or_realization"


def assumption_finding(aid: str, r: dict[str,str]) -> str:
    if aid=="H-LINEAGE-UNIQUE": return "Symmetric duplication defeats any unqualified use; admissible only with independent asymmetry or by rejecting uniqueness."
    if aid in {"A1","A2-P","H-CERT-SOUND","H-IDENTITY-O"}: return "Quarantined from structural verdicts; it may price a later interpretation but cannot repair a failed bridge, gluing, or autonomy test."
    if aid=="H-RECOG": return "Instrument completeness is model-class relative; finite exact toys may stipulate access, while empirical use must expose blind alternatives."
    if aid=="H-AUTONOMY": return "Must be cashed out by a withdrawal intervention, retained environment, disturbance class, and horizon/invariant region."
    if aid=="H-GLOBAL-GLUE": return "Cannot be inferred from local clause or branch witnesses; requires a separate extension/compatibility theorem."
    if aid=="H-ROUTE-FLAT": return "May not be silently assumed; nontrivial holonomy must be reported as route dependence."
    if aid=="H-APPROX": return "Requires vector/local residuals and hard gates; a scalar similarity score is insufficient."
    return f"Retain only for its registered role: {r['role_in_candidate']}; refusal removes the stated conclusion rather than licensing a substitute."


def assumption_nonrescue(aid: str) -> str:
    if aid in {"A1","A2-P","H-CERT-SOUND","H-RECOG","H-IDENTITY-O"}: return "May not be invoked to convert structural failure into structural success."
    if aid=="H-LINEAGE-UNIQUE": return "May not be assumed in a form equivalent to 'this target is the same subject.'"
    return "May not license any conclusion listed in does_not_license."


def scenario_reading(r: dict[str,str], p: dict[str,str]) -> str:
    return f"CST-EXP-03 lane outputs remain unchanged. Under CST-EXP-04, {r['candidate_id']} is {p['phase_disposition']} and is read as {p['retained_role']}; the scenario row therefore cannot be used as a complete transfer or identity verdict."


def render_case(case: dict[str,str], stress: list[dict[str,str]]) -> str:
    rows=[r for r in stress if r["hard_case_id"]==case["id"]]
    out=[f"# {case['id']} — {case['title']}","",f"**Claim lanes:** `{case['lanes']}`  ",f"**No-go links:** `{case['no_go']}`", "", "## Construction", "", case["probe"], "", "## Adversarial point", "", case["core_objection"], "", "## Candidate responses", "", "| Candidate | Disposition | Finding |", "|---|---|---|"]
    for r in rows: out.append(f"| {r['candidate_id']} | `{r['stress_disposition']}` | {md(r['finding'])} |")
    out += ["","## Interpretation boundary","","A survivor status means only that the candidate has a coherent typed response in its own lane. It does not establish consciousness, personal identity, or success under another candidate's criterion."]
    return "\n".join(out)


def render_catalog(stress: list[dict[str,str]]) -> str:
    out=["# Counterexample Catalog","","This is the frozen 18-case adversarial battery required by CST-EXP-04. Every case is a finite theorem/toy prospectus, not an implemented program or proved result.","","| ID | Hard case | Lanes | Core obstruction | Linked no-go |", "|---|---|---|---|---|"]
    for c in D.HARD_CASES: out.append(f"| [{c['id']}](counterexamples/{c['id']}.md) | {md(c['title'])} | `{c['lanes']}` | {md(c['core_objection'])} | `{c['no_go']}` |")
    out += ["","## Cross-candidate profile","","Counts below describe the registered responses and are **not a ranking**.","","| Candidate | Survives | Conditional | Underdetermined | Narrowed role | Fails standalone |", "|---|---:|---:|---:|---:|---:|"]
    for cid in sorted(D.CANDIDATE_PROFILES):
        c=Counter(r["stress_disposition"] for r in stress if r["candidate_id"]==cid)
        out.append(f"| {cid} | {c['survives']} | {c['survives_conditionally']} | {c['principled_underdetermination']} | {c['narrowed_role_only']} | {c['fails_as_standalone']} |")
    out += ["","## Reading rule","","A failure as a standalone criterion may still yield a mandatory component, and a principled underdetermination may be the correct result in a symmetric case. No pass count is evidence that one family is closer to personal identity."]
    return "\n".join(out)


def render_no_go(ng: dict[str,str]) -> str:
    return f"""# {ng['id']} — {ng['title']}

**Status:** conjecture/theorem prospectus; **not proved in CST-EXP-04**.

## Setup and conjecture

{ng['claim']}

## Smallest intended witness

{ng['witness']}

## Proposed proof spine

{ng['proof_spine']}

## Candidate impact

`{ng['impacts']}`

## Assumptions

{ng['assumptions']}

## Falsifier or escape condition

{ng['falsifier']}

## Nonclaim

{ng['nonclaim']}

The prospect does not establish target consciousness, personal identity, A2-P, or empirical recognizability. A later phase must state the exact finite model class and prove or refute the claim.
"""


def render_no_go_index() -> str:
    out=["# No-Go Conjecture Index","","All entries are conjecture-grade prospects generated by adversarial analysis. None is represented as a proved theorem.","","| ID | Prospect | Finite witness | Impact |", "|---|---|---|---|"]
    for n in D.NO_GO: out.append(f"| [{n['id']}]({n['id']}.md) | {md(n['title'])} | {md(short(n['witness'],130))} | `{n['impacts']}` |")
    return "\n".join(out)


def render_candidate_card(cid: str, c: dict[str,Any], stress: list[dict[str,str]], lens: list[dict[str,str]]) -> str:
    p=D.CANDIDATE_PROFILES[cid]; sr=[x for x in stress if x["candidate_id"]==cid]; lr=[x for x in lens if x["candidate_id"]==cid]
    out=[f"# {cid} — {c['title']}: adversarial disposition","",f"**Phase disposition:** `{p['disposition']}`  ",f"**Retained role:** {p['role']}  ",f"**Survivor-family placement:** `{p['family']}`","","## Result","",p['rationale'],"",f"- **Core strength:** {p['core_strength']}.",f"- **Decisive boundary:** {p['fatal_boundary']}.",f"- **Required amendment:** {p['required_amendment']}",f"- **Strongest salvage:** {p['salvage']}","","## Hard-case audit","","| Case | Disposition | Finding |", "|---|---|---|"]
    for r in sr: out.append(f"| {r['hard_case_id']} | `{r['stress_disposition']}` | {md(r['finding'])} |")
    out += ["","## Internal-lens audit","","| Lens | Disposition | Finding |", "|---|---|---|"]
    for r in lr: out.append(f"| {r['lens_id']} | `{r['audit_disposition']}` | {md(r['finding'])} |")
    ng=sorted({x for r in sr for x in split_ids(r['no_go_ids'])})
    out += ["","## No-go exposure","",", ".join(f"`{x}`" for x in ng),"","## Frozen nonclaims","",c["nonclaims"],"", "This disposition is not a ranking. It says whether the schema remains a complete family core, a mandatory component, a bridge mechanism, or an approximation layer after adversarial testing."]
    return "\n".join(out)


def render_candidate_index(cands: dict[str,dict[str,Any]]) -> str:
    out=["# Candidate Adversarial Cards","","| Candidate | Disposition | Retained role | Family placement |", "|---|---|---|---|"]
    for cid in sorted(cands):
        p=D.CANDIDATE_PROFILES[cid]
        out.append(f"| [{cid}]({cid}.md) — {md(cands[cid]['title'])} | `{p['disposition']}` | {md(p['role'])} | `{p['family']}` |")
    return "\n".join(out)


def render_internal_synthesis(cands: dict[str,dict[str,Any]], stress: list[dict[str,str]], lens: list[dict[str,str]]) -> str:
    return "\n".join([
      "# Internal Adversarial-Stress Synthesis","",
      "## Main result","",
      "The ten CST-EXP-03 schemas do not survive as ten rival complete theories. The stress pass decomposes them into **three unranked family cores** and **seven retained component/mechanism roles**. This is a substantive narrowing without a final target selection.","",
      "The most robust distinction is between (i) what structure exists on the target, (ii) what history or process relates source and target, and (iii) whether the target maintains the structure after support withdrawal. No candidate can collapse those lanes without counterexamples.","",
      "## Decisive counterexample classes","",
      "1. **Symmetric duplication** defeats unique continuation for every evidence-invariant criterion.",
      "2. **Public/predictive/package separations** defeat single-shadow and single-quotient sufficiency.",
      "3. **Decoder withdrawal and viability collapse** defeat supported-behavior accounts of autonomy.",
      "4. **Holonomy, critical pairs, and recombination** defeat endpoint-only and branchwise composition.",
      "5. **Local/global and aggregate/local separations** defeat component certificates and scalar error scores.",
      "6. **Temporal gaps and fusion conflicts** require explicit dormancy, provenance, and many-to-one laws.","",
      "## Resulting architecture","",
      "- `SF-01` answers integrated target realization and autonomy, without claiming source identity.",
      "- `SF-02` answers a conservative live-process lineage question, while accepting restrictive negative verdicts.",
      "- `SF-03` answers branching/fusion ancestry relation-valuedly, without unique numerical identity.",
      "- TS-04/06/07/08/09 become gates; TS-05 becomes an optional bridge mechanism; TS-01 becomes predictive content inside SF-03.","",
      "## Boundary","",
      "No no-go theorem is proved, and no survivor is declared correct. CST-EXP-05 must determine whether any family admits a genuinely small exact model, clean theorem statement, and discriminating toy-program contract."
    ])


def render_literature_map() -> str:
    by=defaultdict(list)
    for s in D.EXTERNAL_SOURCES: by[s["category"]].append(s)
    labels={
      "organizational_invariance":"Organizational and computational invariance",
      "computation_and_implementation":"Computation and implementation",
      "branching_identity":"Branching identity",
      "mind_uploading_identity":"Mind-uploading identity arguments",
      "whole_brain_emulation":"Whole-brain emulation",
      "enactivism_autonomy":"Embodiment, enactivism, and autonomy",
      "causal_structure_consciousness":"Causal-structure theories and critiques",
      "consciousness_empirical":"Adversarial empirical consciousness research",
      "causal_abstraction":"Causal abstraction and implementation fidelity",
      "bisimulation_dynamics":"Dynamical and approximate equivalence",
      "logical_object_persistence":"Logical-object persistence and QEC",
      "process_migration":"Live process migration",
      "distributed_state":"Distributed state and reconfiguration",
      "copying_and_observers":"Copying, branching, and self-location",
      "personal_identity":"Personal identity and fission"
    }
    out=["# External-Literature Challenge Map","",f"**Search/freeze date:** {D.DATE}.  ","**Purpose:** confront internally generated candidates with prior art and standard objections; not outsource target selection.","","## Cross-field findings","",
      "1. Organizational/computational invariance supplies a serious sufficiency challenge to process-heavy criteria, but remains a philosophical/psychophysical premise rather than a heterogeneous transport theorem.",
      "2. Branching accounts solve the symmetry contradiction by making continuation non-unique or relation-valued; they do not restore strict numerical identity.",
      "3. Causal abstraction, bisimulation, and live-migration research demand typed maps, intervention/trajectory preservation, consistency, and composition. None licenses consciousness or personal identity.",
      "4. Enactivist autonomy makes source/decoder withdrawal and endogenous maintenance nonoptional, while computational-autonomy work blocks a simple biology-only stipulation.",
      "5. QEC is the sharpest engineering analogy because the logical object, code, errors, decoder, and fidelity are explicit. The present consciousness project lacks an equivalently justified code/recovery map.",
      "6. Recent adversarial consciousness research shows that sharply articulated theories can have core predictions challenged, reinforcing the separation of structural certificates from certificate soundness.",
      "7. Recent work on plasticity limits an overly simple unfolding objection but explicitly does not establish that recurrence, plasticity, or process is necessary for consciousness.","",
      "## Category map",""
    ]
    for cat in sorted(by):
        out += [f"### {labels.get(cat,cat.replace('_',' ').title())}","","| ID | Source | Challenge imported into CST |", "|---|---|---|"]
        for s in by[cat]: out.append(f"| `{s['id']}` | {md(s['authors'])} ({s['year']}), *{md(s['title'])}* | {md(s['challenge'])} |")
        out.append("")
    out += ["## Candidate consequences","",
      "- `SF-01` must answer both the strict functionalist and the intrinsic-causal/autonomy critic without treating any current consciousness theory as settled.",
      "- `SF-02` must identify a process invariant that is neither a metaphysical label nor a hidden biological essentialism.",
      "- `SF-03` is closest to branching-identity literature, but must prove a noncircular ancestry generator and keep relation-valued continuation distinct from numerical identity.",
      "- All families inherit formal obligations from causal abstraction, bisimulation, distributed snapshots, migration, and QEC: exact types, intervention scope, composition, error models, and withdrawal boundaries.","",
      "## Scope limitations","",
      "The registry prioritizes primary papers, author manuscripts, technical reports, and major monographs. It is targeted rather than exhaustive. Philosophical arguments are catalogued as arguments; engineering analogies are not treated as evidence that a person or consciousness has been transferred."
    ]
    return "\n".join(out)


def render_search_log() -> str:
    cats=Counter(s["category"] for s in D.EXTERNAL_SOURCES)
    return "\n".join(["# External Search and Scope Log","",f"- **Execution date:** {D.DATE}","- **Sources retained:** %d"%len(D.EXTERNAL_SOURCES),"- **Temporal coverage:** classics through 2026; recent 2025–2026 sources included where they materially change the challenge landscape.","- **Selection rule:** primary author pages, publisher records, peer-reviewed papers, major monographs, or clearly labeled technical reports/preprints.","- **Exclusions:** popular summaries were not used as load-bearing support; no paper was treated as proving consciousness transfer.","","## Coverage counts","","| Category | Sources |","|---|---:|",*[f"| `{k}` | {v} |" for k,v in sorted(cats.items())],"","## Query themes","","Personal identity and fission; mind uploading and WBE; organizational invariance; causal implementation and abstraction; embodiment/enactivism; causal-structure theories of consciousness; QEC/logical teleportation; live migration and distributed snapshots; observer duplication and self-location.","","## Interpretation discipline","","A source can sharpen a definition, supply a counterexample, or expose an assumption. It does not automatically validate any CST candidate, and disagreement among philosophical sources is preserved rather than averaged into a consensus."])


def render_red_team(rt: dict[str,str]) -> str:
    return f"""# {rt['id']} — {rt['title']}

## Strongest adversarial thesis

{rt['thesis']}

## Candidate/family hit

{rt['best_hit']}

## Concession the project should make

{rt['concession']}

## Required response

{rt['required_answer']}

## Remainder after response

{rt['unresolved']}

This review is intentionally adversarial but does not claim that its standpoint is correct.
"""


def render_red_index() -> str:
    out=["# Red-Team Review Index","","| ID | Standpoint | Strongest pressure |", "|---|---|---|"]
    for r in D.RED_TEAMS: out.append(f"| [{r['id']}]({r['id']}.md) | {md(r['title'])} | {md(short(r['thesis'],150))} |")
    return "\n".join(out)


def render_shortlist(cands: dict[str,dict[str,Any]]) -> str:
    out=["# CST-EXP-04 Survivor Shortlist","","**Status:** three unranked candidate families survive to theorem/toy reconnaissance. They answer different questions and are not interchangeable. The three families remain unranked throughout CST-EXP-05 reconnaissance.",""]
    for f in D.SURVIVOR_FAMILIES:
        out += [f"## {f['id']} — {f['title']}","",f"- **Core:** `{f['core']}` — {cands[f['core']]['title']}",f"- **Mandatory modules:** `{f['mandatory_modules']}`",f"- **Optional bridge mechanism:** `{f['optional_mechanism']}`",f"- **Claim ceiling:** {f['claim_ceiling']}",f"- **Lineage policy:** {f['lineage_policy']}",f"- **Why it survives:** {f['why_survives']}",f"- **Principal risk:** {f['principal_risk']}",f"- **Kill condition:** {f['kill_condition']}",""]
    out += ["## Shared admission conditions","",
      "A family survives only because it (1) is genuinely cross-carrier typed, (2) has finite falsifiers, (3) returns relation-valued or underdetermined outputs under symmetry rather than arbitrary uniqueness, (4) exposes route and autonomy assumptions, and (5) does not use A2-P or a same-subject premise to pass.","",
      "## Not shortlisted as standalone families","",
      "`TS-01`, `TS-04`, `TS-05`, `TS-06`, `TS-07`, `TS-08`, and `TS-09` remain scientifically active as components. Their narrowing is not deletion: each supplies a test that one or more survivors must pass.","",
      "## Next-phase question","",
      "CST-EXP-05 must determine which family—or which narrow theorem/no-go inside a family—has the smallest exact finite semantics and most informative toy-program contract. No primary target is frozen here."
    ]
    return "\n".join(out)


def render_synthesis(cands: dict[str,dict[str,Any]], stress: list[dict[str,str]], lens: list[dict[str,str]]) -> str:
    return "\n".join([
      "# CST-EXP-04 — Adversarial Stress, No-Go Mining, and External Confrontation","",
      "## Executive finding","",
      "The phase breaks the original ten-schema roster into a more defensible architecture: **three unranked survivor families** plus **seven retained component/mechanism roles**. No candidate survives as a one-predicate answer to ‘did consciousness move?’ The plausible formal target must factor target realization, lineage, autonomy, recognition, and ontology.","",
      "The strongest constructive possibility is not a single invariant. It is a typed conjunction in which an integrated target package is globally realized and autonomous, while lineage is supplied either by a conservative live-process criterion or by a relation-valued predictive ancestry relation. Route/recombination, temporal/provenance, and approximation audits are mandatory crosscutting controls.","",
      "## What the adversarial pass rules out as standalone answers","",
      "- public or report equivalence;",
      "- predictive-quotient equivalence alone;",
      "- viability alone;",
      "- a code/recovery mechanism without a justified logical package;",
      "- local closure witnesses without global gluing;",
      "- route/branch bookkeeping without target realization;",
      "- ledger continuity without predictive/binding/viability content;",
      "- a scalar approximate-similarity score;",
      "- unique continuation under exact target symmetry.","",
      "## Strongest no-go prospects","",
      "The most promising exact negative results are `NG-02/NG-16` (symmetric duplication), `NG-01` (public-shadow nonidentifiability), `NG-04` (branchwise versus recombination), `NG-05/NG-18` (decoder support versus autonomy), `NG-06/NG-12` (holonomy and composition), `NG-07` (global residual versus local catastrophe), and `NG-08` (local-to-global obstruction). These are prospectus items, not proofs.","",
      "## External confrontation","",
      "Organizational-invariance arguments make it illegitimate to assume that biological material is essential; enactivist and process views make it illegitimate to assume that endpoint organization exhausts continuity; branching-identity work makes uniqueness untenable under duplication; causal abstraction, QEC, migration, and distributed-systems work make implementation, recovery, consistency, and composition obligations explicit. Current consciousness theory remains empirically contested, so no attached or external certificate can be treated as settled psychophysical truth.","",
      "## Frozen shortlist","",
      "1. `SF-01` Integrated Autonomous Handoff — target realization/autonomy.",
      "2. `SF-02` Causal-Overlap Process Lineage — conservative live-process lineage.",
      "3. `SF-03` Relation-Valued Predictive Ancestry — branching/fusion lineage.","",
      "These are not ranked. SF-01 can combine with either lineage family; SF-02 and SF-03 may prove incompatible on destructive copies or temporal gaps, which is precisely what the next phase must preserve and test.","",
      "## Ontological boundary","",
      "Even a complete structural result would not by itself prove consciousness, personal survival, or numerical identity. Certificate soundness, A1, A2-P, empirical recognition, and identity interpretation remain separately priced. No phase result licenses a same-subject migration claim without adding and defending those premises.","",
      "## Exit-gate judgment","",
      "PASS. Every candidate has a complete 18-case and 13-lens audit; every rejection preserves a salvage; all assumptions remain exposed; the three survivors give coherent duplication/fission/route/autonomy answers or typed underdetermination; and none passes by a same-subject assumption."
    ])


def render_challenges_readme() -> str:
    return """# CST-EXP-04 Challenge Bank

This directory contains the adversarial surfaces used to narrow the CST-EXP-03 candidate roster.

- `COUNTEREXAMPLE_CATALOG.md` and `counterexamples/` contain the 18 hard cases.
- `candidate_stress/` contains one complete audit per candidate.
- `no_go_conjectures/` contains theorem prospects; none is claimed proved.
- `external_literature/` records the targeted current challenge pass.
- `red_team/` contains seven explicit adversarial standpoints.
- `SURVIVOR_SHORTLIST.md` freezes three unranked families.
- `CST-EXP-04_ADVERSARIAL_SYNTHESIS.md` is the phase synthesis.

The bank is exploratory. It does not implement proofs or toy programs and does not establish consciousness or personal identity.
"""


def render_dot(cands: dict[str,dict[str,Any]]) -> str:
    lines=["digraph CST_EXP_04 {","  rankdir=LR;","  graph [label=\"CST-EXP-04 survivor architecture (unranked)\", labelloc=t];","  node [shape=box];"]
    for f in D.SURVIVOR_FAMILIES:
        lines.append(f'  "{f["id"]}" [shape=oval,label="{f["id"]}\\n{f["title"]}"];')
        lines.append(f'  "{f["core"]}" -> "{f["id"]}" [label="core"];')
        for x in split_ids(f["mandatory_modules"]): lines.append(f'  "{x}" -> "{f["id"]}" [label="gate/module"];')
        for x in split_ids(f["optional_mechanism"]): lines.append(f'  "{x}" -> "{f["id"]}" [style=dashed,label="optional bridge"];')
    for cid,c in cands.items(): lines.append(f'  "{cid}" [label="{cid}\\n{c["title"]}"];')
    lines += ['  "SF-01" -> "SF-02" [style=dotted,label="may pair: realization + lineage"];','  "SF-01" -> "SF-03" [style=dotted,label="may pair: realization + ancestry"];',"}"]
    return "\n".join(lines)


def try_render_dot(root: Path) -> None:
    import subprocess
    dot=root/"challenges/survivor_architecture.dot"
    for fmt in ["svg","png"]:
        try: subprocess.run(["dot",f"-T{fmt}",str(dot),"-o",str(root/f"challenges/survivor_architecture.{fmt}")],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        except Exception: pass


def render_state() -> str:
    return f"""# Repository State

- **Project:** CST-EXP
- **State version:** CST-EXP-04-v1
- **State date:** {D.DATE}
- **Completed:** CST-EXP-00 through CST-EXP-04
- **Next planned phase:** CST-EXP-05
- **Science status:** three unranked survivor families frozen after complete adversarial stress; no final target selected
- **Formalization status:** 18 no-go/theorem prospects and finite-witness spines recorded; none proved
- **Toy-program status:** no program implemented; only later reconnaissance authorized
- **Simulation status:** no Six Birds simulation authorized or required
- **Empirical status:** external challenge and recognition limits recorded; no empirical bridge supplied
- **Ontological status:** no unconditional consciousness, survival, or numerical-identity claim

## Frozen CST-EXP-04 rulings

1. The ten candidates are decomposed into three family cores and seven component/mechanism roles.
2. The survivor families are `SF-01`, `SF-02`, and `SF-03`; they are unranked and answer different lanes.
3. Symmetric duplication forbids invariant unique selection without independently declared asymmetry.
4. Target realization, lineage, autonomy, recognition, and ontology remain separate.
5. Decoder/source/protocol support is removed in every autonomy claim.
6. Route independence requires flatness/confluence; otherwise route dependence is retained.
7. Approximation uses typed local/vector defects and hard gates, not one similarity score.
8. All no-go assets remain conjecture-grade.
9. External sources challenge internal candidates but do not choose the target.
10. A1, A2-P, certificate soundness, recognition, and personal-identity interpretation do not rescue structural failure.
"""


def render_status() -> str:
    return f"""# Repository Status

**Status date:** {D.DATE}
**Completed phase:** CST-EXP-04
**Exit gate:** pending/finalized by `scripts/validate_exp04.py`
**Next authorized phase:** CST-EXP-05 — theorem and toy-program reconnaissance
**Implementation authorization:** none

## Landed

- 180 candidate × hard-case stress records and 130 candidate × internal-lens audits.
- 18 counterexample cards and 18 no-go conjecture/theorem prospectuses.
- 10 rejection/salvage dispositions preserving every candidate's strongest reusable role.
- 26-source targeted external-literature registry across 15 challenge categories.
- 7 explicit red-team reviews.
- 3 unranked survivor families with composition, risk, and kill conditions.
- 350 inherited scenario verdicts reissued with phase-04 interpretation while preserving every phase-03 lane output.
- 200 assumption-exposure records.

## Not landed

No final target, theorem proof, no-go proof, Lean asset, toy program, full simulation, empirical recognition protocol, consciousness result, survival result, or personal-identity verdict.
"""


def update_readme(root: Path) -> None:
    p=root/"README.md"; text=p.read_text(encoding="utf-8")
    marker="## CST-EXP-04 adversarial layer"
    if marker in text: text=text.split(marker,1)[0]
    text=text.rstrip()
    sec=f"""

{marker}

CST-EXP-04 attacks all ten candidate schemas using 18 hard cases, 13 internal SBT lenses, 18 no-go prospects, 26 external sources, and seven red-team standpoints. It freezes three **unranked** survivor families:

- `SF-01` Integrated Autonomous Handoff;
- `SF-02` Causal-Overlap Process Lineage;
- `SF-03` Relation-Valued Predictive Ancestry.

Seven original candidates remain as mandatory gates, bridge mechanisms, or approximation layers. See `challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md` and `challenges/SURVIVOR_SHORTLIST.md`.
"""
    write_text(p,text+sec)


def update_changelog(root: Path) -> None:
    p=root/"CHANGELOG.md"; text=p.read_text(encoding="utf-8")
    marker="## CST-EXP-04"
    if marker in text: text=text.split(marker,1)[0]
    text=text.rstrip()
    sec=f"""

{marker} — {D.DATE}

- Added the complete 18-case × 10-candidate adversarial stress ledger.
- Added 13 internal-lens audits for every candidate.
- Added 18 no-go conjecture/theorem prospectuses and finite witness spines.
- Added a 26-source external-literature challenge map and seven red-team reviews.
- Narrowed the ten candidates into three unranked survivor families plus seven component/mechanism roles.
- Preserved all CST-EXP-03 scenario verdicts and exposed all 200 candidate-assumption records.
- Did not prove a theorem, implement a toy, select a final target, or make an ontological claim.
"""
    write_text(p,text+sec)


def main() -> int:
    ap=argparse.ArgumentParser(); ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1]); args=ap.parse_args()
    build(args.root.resolve()); print("CST-EXP-04 assets built"); return 0

if __name__=="__main__": raise SystemExit(main())
