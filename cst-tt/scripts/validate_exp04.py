#!/usr/bin/env python3
"""Validate CST-EXP-04 repository invariants and phase exit gate."""
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


class V:
    def __init__(self, root: Path, skip_manifest: bool=False):
        self.r=root; self.skip_manifest=skip_manifest; self.checks=[]
    def add(self,name:str,ok:bool,detail:Any=""):
        self.checks.append({"name":name,"status":"pass" if ok else "fail","detail":detail})
    def rows(self,rel:str):
        with (self.r/rel).open(newline="",encoding="utf-8") as f: return list(csv.DictReader(f))
    def j(self,rel:str): return json.loads((self.r/rel).read_text(encoding="utf-8"))
    def text(self,rel:str): return (self.r/rel).read_text(encoding="utf-8")
    def sha(self,p:Path):
        h=hashlib.sha256()
        with p.open("rb") as f:
            for b in iter(lambda:f.read(1024*1024),b""): h.update(b)
        return h.hexdigest()
    @staticmethod
    def ids(s:str): return [x.strip() for x in str(s).split(";") if x.strip()]

    def run(self):
        r=self.r
        candidate_ids={f"TS-{i:02d}" for i in range(1,11)}
        hard_ids={f"HC-{i:02d}" for i in range(1,19)}
        lens_ids={f"IL-{i:02d}" for i in range(1,14)}
        ng_ids={f"NG-{i:02d}" for i in range(1,19)}
        rt_ids={f"RT-{i:02d}" for i in range(1,8)}
        family_ids={f"SF-{i:02d}" for i in range(1,4)}

        # 1. Baseline parse and inherited controls.
        required=[
          "candidates/CANDIDATE_REGISTRY.json","ledgers/candidate_scenario_verdicts.csv","ledgers/candidate_assumption_matrix.csv",
          "manifests/CST-EXP-03_MANIFEST.json","manifests/EXP04_ASSET_SUMMARY.json",
          "challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md","challenges/SURVIVOR_SHORTLIST.md",
          "ledgers/candidate_hard_case_stress.csv","ledgers/candidate_internal_lens_audit.csv",
          "ledgers/rejection_and_salvage_log.csv","ledgers/assumption_exposure.csv",
        ]
        self.add("All core inherited and phase-04 files exist",all((r/x).is_file() for x in required),[x for x in required if not (r/x).is_file()])
        parse_bad=[]
        for p in r.rglob("*.json"):
            if ".git" in p.parts: continue
            try: json.loads(p.read_text(encoding="utf-8"))
            except Exception as e: parse_bad.append(f"{p.relative_to(r)}:{e}")
        self.add("All repository JSON files parse",not parse_bad,parse_bad or "all parse")
        csv_bad=[]
        for p in r.rglob("*.csv"):
            if ".git" in p.parts: continue
            try:
                with p.open(newline="",encoding="utf-8") as f:
                    rr=csv.reader(f); next(rr,None); list(rr)
            except Exception as e: csv_bad.append(f"{p.relative_to(r)}:{e}")
        self.add("All repository CSV files parse",not csv_bad,csv_bad or "all parse")

        oldm=self.j("manifests/CST-EXP-03_MANIFEST.json")
        oldhash={x["path"]:x["sha256"] for x in oldm["files"]}
        frozen=[
          "candidates/CANDIDATE_REGISTRY.json","candidates/transported_object_registry.csv","candidates/invariant_registry.csv","candidates/bridge_registry.csv",
          "ledgers/candidate_scenario_verdicts.csv","ledgers/candidate_assumption_matrix.csv","ledgers/candidate_question_responses.csv","ledgers/candidate_anti_conflation_audit.csv",
          "ledgers/new_primitive_register.csv","scenarios/SCENARIO_REGISTRY.json","corpus/machine_index/all_statement_index.csv"
        ]
        for rel in frozen:
            self.add(f"Inherited CST-EXP-03 surface remains byte-frozen: {rel}",(r/rel).is_file() and oldhash.get(rel)==self.sha(r/rel),{"expected":oldhash.get(rel),"actual":self.sha(r/rel) if (r/rel).is_file() else "missing"})
        prev=self.j("manifests/VALIDATION_RESULTS.json") if (r/"manifests/VALIDATION_RESULTS.json").is_file() else {}
        # Existing file will later be overwritten by this validator, so prior record is captured separately in CST-EXP-03 completion/report.
        exp03report=self.text("manifests/CST-EXP-03_COMPLETION_REPORT.md").lower()
        self.add("Inherited CST-EXP-03 completion record reports pass", "255/255" in exp03report and "pass" in exp03report,"completion report")
        paper=self.rows("corpus/machine_index/paper_inventory.csv")
        machine=self.rows("corpus/machine_index/all_statement_index.csv")
        prov=self.rows("ledgers/statement_provenance.csv")
        self.add("Corpus inventory remains 60 papers and 1,359 nonquarantined statements",len(paper)==60 and len(machine)==1359,{"papers":len(paper),"statements":len(machine)})
        self.add("P46 remains excluded from machine statement bank",not any(x.get("paper_id")=="P46" for x in machine),sum(1 for x in machine if x.get("paper_id")=="P46"))
        self.add("P46 retains one exclusion provenance record",sum(1 for x in prov if x.get("paper_id")=="P46" and x.get("selection_status")=="excluded")==1,"expected one")
        vlog=self.text("ledgers/version_and_exclusion_log.md").lower()
        self.add("P42/P60 revision control remains explicit",all(x in vlog for x in ["p42","p60","normative","zero independent"]),"version log")

        # 2. Registry and source data parity.
        creg=self.j("candidates/CANDIDATE_REGISTRY.json")
        cands={x["id"]:x for x in creg["candidates"]}
        self.add("Candidate registry remains exactly TS-01 through TS-10",set(cands)==candidate_ids,set(cands))
        self.add("Phase-04 data profiles cover every candidate",set(D.CANDIDATE_PROFILES)==candidate_ids,set(D.CANDIDATE_PROFILES))
        self.add("Hard-case definition bank contains HC-01 through HC-18",{x["id"] for x in D.HARD_CASES}==hard_ids,len(D.HARD_CASES))
        self.add("Internal-lens definition bank contains IL-01 through IL-13",{x["id"] for x in D.INTERNAL_LENSES}==lens_ids,len(D.INTERNAL_LENSES))
        self.add("No-go data bank contains NG-01 through NG-18",{x["id"] for x in D.NO_GO}==ng_ids,len(D.NO_GO))
        self.add("Red-team data bank contains RT-01 through RT-07",{x["id"] for x in D.RED_TEAMS}==rt_ids,len(D.RED_TEAMS))
        self.add("Survivor bank contains SF-01 through SF-03",{x["id"] for x in D.SURVIVOR_FAMILIES}==family_ids,len(D.SURVIVOR_FAMILIES))
        self.add("Every hard-case status matrix has 18 entries",all(len(D.HARD_CASE_STATUS[c])==18 for c in candidate_ids),{c:len(D.HARD_CASE_STATUS[c]) for c in candidate_ids})
        self.add("Every internal-lens matrix has 13 entries",all(len(D.LENS_STATUS[c])==13 for c in candidate_ids),{c:len(D.LENS_STATUS[c]) for c in candidate_ids})
        self.add("All status codes are registered",all(x in D.STATUS_LABELS for vals in list(D.HARD_CASE_STATUS.values())+list(D.LENS_STATUS.values()) for x in vals),"S/C/U/N/F only")

        # 3. Hard-case stress bank.
        stress=self.rows("ledgers/candidate_hard_case_stress.csv")
        self.add("Hard-case stress ledger has exactly 180 records",len(stress)==180,len(stress))
        self.add("Stress ledger covers complete candidate × case product",{(x["candidate_id"],x["hard_case_id"]) for x in stress}=={(c,h) for c in candidate_ids for h in hard_ids},len({(x['candidate_id'],x['hard_case_id']) for x in stress}))
        self.add("Every stress record names a disposition and substantive finding",all(x["stress_disposition"] and len(x["finding"])>90 for x in stress),[f"{x['candidate_id']}/{x['hard_case_id']}" for x in stress if not x["stress_disposition"] or len(x["finding"])<=90])
        self.add("Every stress record exposes assumptions and a required response",all(x["assumption_exposed"] and x["required_response"] for x in stress),[f"{x['candidate_id']}/{x['hard_case_id']}" for x in stress if not x["assumption_exposed"] or not x["required_response"]])
        self.add("Every stress record preserves a salvage",all(len(x["salvage"])>30 for x in stress),[f"{x['candidate_id']}/{x['hard_case_id']}" for x in stress if len(x["salvage"])<=30])
        bad_ng=sorted({n for x in stress for n in self.ids(x["no_go_ids"]) if n not in ng_ids})
        self.add("All stress-ledger no-go references resolve",not bad_ng,bad_ng or "all resolve")
        for cid in sorted(candidate_ids):
            rows=[x for x in stress if x["candidate_id"]==cid]
            self.add(f"{cid} has all 18 hard-case responses",len(rows)==18 and {x["hard_case_id"] for x in rows}==hard_ids,len(rows))
            self.add(f"{cid} hard-case profile includes at least two response types",len({x["stress_disposition"] for x in rows})>=2,sorted({x["stress_disposition"] for x in rows}))
        for hid in sorted(hard_ids):
            rows=[x for x in stress if x["hard_case_id"]==hid]
            self.add(f"{hid} is evaluated for all ten candidates",len(rows)==10 and {x["candidate_id"] for x in rows}==candidate_ids,len(rows))
        symmetric=[x for x in stress if x["hard_case_id"] in {"HC-05","HC-10"}]
        forbidden=[x for x in symmetric if x["stress_disposition"]=="survives" and "relation" not in x["finding"].lower() and "branch" not in x["finding"].lower() and "unique" not in x["finding"].lower()]
        self.add("Symmetric duplication has no unexplained unique-success verdict",not forbidden,[f"{x['candidate_id']}/{x['hard_case_id']}" for x in forbidden] or "none")
        hc13=[x for x in stress if x["hard_case_id"]=="HC-13"]
        self.add("External-decoder case classifies every direct survivor as a detector of non-autonomy",all(x["stress_disposition"]!="survives" or any(k in x["finding"].lower() for k in ["fails","non-autonomous","failure"]) for x in hc13),[(x['candidate_id'],x['stress_disposition'],x['finding']) for x in hc13 if x["stress_disposition"]=="survives"])
        hc16=[x for x in stress if x["hard_case_id"]=="HC-16"]
        self.add("Gauge-change case is treated as a carrier-individuation control",all("carrier" in x["finding"].lower() or x["stress_disposition"] in {"survives_conditionally","survives"} for x in hc16),"HC-16 findings")

        # 4. Lens bank.
        lens=self.rows("ledgers/candidate_internal_lens_audit.csv")
        self.add("Internal-lens audit has exactly 130 records",len(lens)==130,len(lens))
        self.add("Lens audit covers complete candidate × lens product",{(x["candidate_id"],x["lens_id"]) for x in lens}=={(c,l) for c in candidate_ids for l in lens_ids},len({(x['candidate_id'],x['lens_id']) for x in lens}))
        self.add("Every lens audit records challenge, response, and amendment",all(x["challenge"] and x["required_response"] and x["candidate_amendment"] for x in lens),"complete")
        for cid in sorted(candidate_ids):
            rows=[x for x in lens if x["candidate_id"]==cid]
            self.add(f"{cid} has all 13 internal-lens audits",len(rows)==13 and {x["lens_id"] for x in rows}==lens_ids,len(rows))
        for lid in sorted(lens_ids):
            rows=[x for x in lens if x["lens_id"]==lid]
            self.add(f"{lid} is applied to all ten candidates",len(rows)==10,len(rows))
        em=[x for x in lens if x["lens_id"]=="IL-13"]
        self.add("Audited-emergence lens never upgrades structure to ontology",all(x["audit_disposition"] in {"narrowed_role_only","survives_conditionally"} for x in em),[(x['candidate_id'],x['audit_disposition']) for x in em])

        # 5. Disposition and salvage.
        rej=self.rows("ledgers/rejection_and_salvage_log.csv")
        self.add("Rejection/salvage log has one record per candidate",len(rej)==10 and {x["candidate_id"] for x in rej}==candidate_ids,len(rej))
        self.add("Every disposition preserves role, amendment, salvage, and boundary",all(all(x[k] for k in ["phase_disposition","retained_role","decisive_boundary","required_amendment","strongest_salvage","rationale"]) for x in rej),"complete")
        core={x["candidate_id"] for x in rej if x["phase_disposition"]=="survives_as_family_core"}
        self.add("Exactly TS-02, TS-03, and TS-10 survive as family cores",core=={"TS-02","TS-03","TS-10"},sorted(core))
        component={x["candidate_id"] for x in rej if x["phase_disposition"]!="survives_as_family_core"}
        self.add("Seven noncore candidates are retained rather than silently deleted",component==candidate_ids-core,sorted(component))
        self.add("No disposition presents its profile as a ranking",all(x["not_a_ranking"]=="true" for x in rej),"all true")

        # 6. Survivor architecture.
        fam=self.rows("ledgers/survivor_family_registry.csv")
        self.add("Survivor registry contains exactly three families",len(fam)==3 and {x["id"] for x in fam}==family_ids,len(fam))
        cores={x["id"]:x["core"] for x in fam}
        self.add("Survivor cores are frozen as TS-02/TS-03/TS-10",cores=={"SF-01":"TS-02","SF-02":"TS-03","SF-03":"TS-10"},cores)
        self.add("Every survivor states claim ceiling, lineage policy, risk, and kill condition",all(all(x[k] for k in ["claim_ceiling","lineage_policy","principal_risk","kill_condition"]) for x in fam),"complete")
        same_subject=[x["id"] for x in fam if re.search(r"\bsame subject\b",x["claim_ceiling"],re.I)]
        self.add("No survivor claim ceiling assumes 'same subject'",not same_subject,same_subject or "none")
        self.add("No survivor claim ceiling asserts consciousness or personal identity",all(not re.search(r"establish(?:es)? (?:target )?consciousness|proves? personal identity",x["claim_ceiling"],re.I) for x in fam),"none")
        comp=self.rows("ledgers/survivor_composition_matrix.csv")
        self.add("Composition matrix is complete 3 × 10",len(comp)==30 and {(x["family_id"],x["candidate_id"]) for x in comp}=={(f,c) for f in family_ids for c in candidate_ids},len(comp))
        for f in fam:
            rows=[x for x in comp if x["family_id"]==f["id"]]
            self.add(f"{f['id']} has exactly one core in composition matrix",sum(x["role"]=="core" for x in rows)==1,[x['candidate_id'] for x in rows if x['role']=='core'])
            self.add(f"{f['id']} has at least three explicit modules/mechanisms",sum(x["role"] in {"mandatory_module","optional_mechanism"} for x in rows)>=3,sum(x["role"] in {"mandatory_module","optional_mechanism"} for x in rows))
        shortlist=self.text("challenges/SURVIVOR_SHORTLIST.md").lower()
        self.add("Shortlist explicitly states unranked status",shortlist.count("unranked")>=2,shortlist.count("unranked"))
        self.add("Shortlist explicitly preserves component candidates",all(x.lower() in shortlist for x in ["ts-01","ts-04","ts-05","ts-06","ts-07","ts-08","ts-09"]),"all seven")

        # 7. No-go bank.
        ng=self.rows("ledgers/no_go_register.csv")
        self.add("No-go register has exactly 18 entries",len(ng)==18 and {x["id"] for x in ng}==ng_ids,len(ng))
        self.add("Every no-go has claim, witness, proof spine, falsifier, and nonclaim",all(all(len(x[k])>20 for k in ["claim","witness","proof_spine","falsifier","nonclaim"]) for x in ng),"complete")
        self.add("Every no-go is explicitly marked unproved",all("not_proved" in x["status"] for x in ng),[x['id'] for x in ng if 'not_proved' not in x['status']])
        for x in ng:
            p=r/f"challenges/no_go_conjectures/{x['id']}.md"
            self.add(f"{x['id']} prospectus exists and says not proved",p.is_file() and "not proved" in p.read_text(encoding="utf-8").lower(),str(p.relative_to(r)))
            bad=[z for z in self.ids(x["impacts"]) if z not in candidate_ids]
            self.add(f"{x['id']} candidate-impact references resolve",not bad,bad or "all resolve")
        ngblob=" ".join(x["title"].lower()+" "+x["claim"].lower() for x in ng)
        for term in ["public-shadow","symmetric","predictive-quotient","recombination","decoder","route independence","global residual","global gluing","endpoint equality","temporal-gap","carrier-individuation","bridge-composition","finite-instrument","certificate","personal identity","trilemma","fusion","external support"]:
            self.add(f"No-go bank covers required theme: {term}",term in ngblob,term)

        # 8. Counterexample and candidate-card files.
        case_files=list((r/"challenges/counterexamples").glob("HC-*.md"))
        self.add("Exactly 18 hard-case cards exist",len(case_files)==18 and {p.stem for p in case_files}==hard_ids,len(case_files))
        for p in case_files:
            text=p.read_text(encoding="utf-8")
            self.add(f"{p.stem} card lists all ten candidates",all(c in text for c in candidate_ids),sum(c in text for c in candidate_ids))
        cfiles=list((r/"challenges/candidate_stress").glob("TS-*.md"))
        self.add("Exactly ten candidate stress cards exist",len(cfiles)==10 and {p.stem for p in cfiles}==candidate_ids,len(cfiles))
        for p in cfiles:
            text=p.read_text(encoding="utf-8")
            self.add(f"{p.stem} card includes all 18 hard cases",sum(h in text for h in hard_ids)==18,sum(h in text for h in hard_ids))
            self.add(f"{p.stem} card includes all 13 internal lenses",sum(l in text for l in lens_ids)==13,sum(l in text for l in lens_ids))
            self.add(f"{p.stem} card preserves frozen nonclaims","frozen nonclaims" in text.lower(),"heading")

        # 9. External literature.
        src=self.rows("challenges/external_literature/SOURCE_REGISTRY.csv")
        self.add("External source registry has exactly 26 records",len(src)==26,len(src))
        self.add("External registry IDs are EXT-001 through EXT-026",{x["id"] for x in src}=={f"EXT-{i:03d}" for i in range(1,27)},len({x['id'] for x in src}))
        cats={x["category"] for x in src}
        self.add("External registry spans at least 12 categories",len(cats)>=12,sorted(cats))
        recent=[x for x in src if int(x["year"])>=2025]
        self.add("External pass includes at least five 2025–2026 sources",len(recent)>=5,[(x['id'],x['year']) for x in recent])
        self.add("Every external source has bibliographic identity and challenge",all(all(x[k] for k in ["authors","title","venue","identifier","source_type","challenge"]) for x in src),"complete")
        self.add("Every external source has a stable-looking source locator",all(x["url"].startswith("https://") for x in src),[x['id'] for x in src if not x['url'].startswith('https://')])
        self.add("No popular-news source is retained as load-bearing evidence",all("popular" not in x["source_type"].lower() and "news" not in x["source_type"].lower() for x in src),[x['id'] for x in src if 'popular' in x['source_type'].lower() or 'news' in x['source_type'].lower()])
        years={int(x["year"]) for x in src}
        self.add("External registry covers classics and current work",min(years)<=1995 and max(years)>=2026,{"min":min(years),"max":max(years)})
        xwalk=self.rows("ledgers/external_literature_crosswalk.csv")
        self.add("External crosswalk has at least 90 source-object links",len(xwalk)>=90,len(xwalk))
        self.add("All external crosswalk source IDs resolve",all(x["source_id"] in {s['id'] for s in src} for x in xwalk),"resolve")
        valid_objs=candidate_ids|family_ids|ng_ids|rt_ids
        self.add("All external crosswalk object IDs resolve",all(x["object_id"] in valid_objs for x in xwalk),sorted({x['object_id'] for x in xwalk if x['object_id'] not in valid_objs}))
        lmap=self.text("challenges/external_literature/LITERATURE_CHALLENGE_MAP.md").lower()
        self.add("Literature map contains all 26 source IDs",all(x["id"].lower() in lmap for x in src),sum(x['id'].lower() in lmap for x in src))
        self.add("Literature map states engineering analogies are not identity evidence","none licenses consciousness or personal identity" in lmap or "not treated as evidence" in lmap,"boundary")
        slog=self.text("challenges/external_literature/SEARCH_AND_SCOPE_LOG.md").lower()
        self.add("Search log records execution date and targeted-not-exhaustive scope",D.DATE in slog and all(marker in slog for marker in ["selection rule", "exclusions", "query themes", "does not automatically validate"]),"scope and interpretation fields")

        # 10. Red teams.
        rtfiles=list((r/"challenges/red_team").glob("RT-*.md"))
        self.add("Exactly seven red-team memos exist",len(rtfiles)==7 and {p.stem for p in rtfiles}==rt_ids,len(rtfiles))
        required_heads=["strongest adversarial thesis","candidate/family hit","concession","required response","remainder"]
        for p in rtfiles:
            t=p.read_text(encoding="utf-8").lower()
            self.add(f"{p.stem} memo has all adversarial-review fields",all(h in t for h in required_heads),[h for h in required_heads if h not in t])
        rtblob=" ".join(p.read_text(encoding="utf-8").lower() for p in rtfiles)
        for term in ["functionalist","biological","duplication","sbt audit","empirical","formal-methods","ontological"]:
            self.add(f"Red-team bank includes standpoint: {term}",term in rtblob,term)

        # 11. Assumption exposure and ontology separation.
        exp=self.rows("ledgers/assumption_exposure.csv")
        self.add("Assumption exposure ledger has 200 records",len(exp)==200,len(exp))
        self.add("Assumption exposure covers 10 candidates × 20 assumptions",len({x["assumption_id"] for x in exp})==20 and {(x["candidate_id"],x["assumption_id"]) for x in exp}=={(c,a) for c in candidate_ids for a in {x['assumption_id'] for x in exp}},len({x['assumption_id'] for x in exp}))
        protected={"A1","A2-P","H-CERT-SOUND","H-RECOG","H-IDENTITY-O"}
        for aid in sorted(protected):
            rows=[x for x in exp if x["assumption_id"]==aid]
            self.add(f"{aid} is exposed for all ten candidates",len(rows)==10,len(rows))
            self.add(f"{aid} may not rescue structural failure",all("may not" in x["may_not_rescue"].lower() for x in rows),[x['candidate_id'] for x in rows if 'may not' not in x['may_not_rescue'].lower()])
        unique=[x for x in exp if x["assumption_id"]=="H-LINEAGE-UNIQUE"]
        self.add("Unique-lineage assumption explicitly faces symmetric duplication",all("symmetric" in x["adversarial_finding"].lower() for x in unique),"all ten")
        auto=[x for x in exp if x["assumption_id"]=="H-AUTONOMY"]
        self.add("Autonomy assumption is cashed out by withdrawal",all("withdrawal" in x["adversarial_finding"].lower() for x in auto),"all ten")

        # 12. Scenario inheritance.
        old=self.rows("ledgers/candidate_scenario_verdicts.csv")
        new=self.rows("ledgers/candidate_verdicts_by_scenario.csv")
        self.add("Phase-04 scenario ledger preserves all 350 rows",len(old)==350 and len(new)==350,{"old":len(old),"new":len(new)})
        key=lambda x:(x["candidate_id"],x["scenario_id"])
        oldmap={key(x):x for x in old}; newmap={key(x):x for x in new}
        self.add("Phase-04 scenario ledger preserves the exact key set",set(oldmap)==set(newmap),len(newmap))
        frozen_fields=list(old[0].keys())
        diffs=[]
        for k,o in oldmap.items():
            n=newmap[k]
            for f in frozen_fields:
                if o[f]!=n[f]: diffs.append((k,f,o[f],n[f]))
        self.add("Every CST-EXP-03 scenario field is byte-for-byte preserved",not diffs,diffs[:5] or "all preserved")
        self.add("Every phase-04 scenario row is marked frozen and nonranking",all(x["frozen_exp03_outcome"]=="true" and x["not_a_ranking"]=="true" for x in new),"all 350")
        self.add("Every phase-04 scenario row adds a disposition and retained role",all(x["exp04_phase_disposition"] and x["exp04_retained_role"] for x in new),"all 350")

        # 13. Governance, phase boundary, and links.
        dlog=self.rows("ledgers/decision_log.csv")
        self.add("Decision log contains exactly eight active D04 rulings",sum(x["id"].startswith("D04-") and x["status"]=="active" for x in dlog)==8,[x['id'] for x in dlog if x['id'].startswith('D04-')])
        self.add("Rejected-defaults log contains ten RD04 entries",len(re.findall(r"\| RD04-\d+",self.text("ledgers/REJECTED_DEFAULTS.md")))==10,"10")
        self.add("Unresolved-question log contains CST-EXP-04 section","Adversarial questions added after CST-EXP-04" in self.text("ledgers/UNRESOLVED_QUESTIONS.md"),"section")
        state=self.text("STATE.md"); status=self.text("STATUS.md")
        self.add("STATE advances to CST-EXP-04-v1 and names CST-EXP-05", "CST-EXP-04-v1" in state and "CST-EXP-05" in state,"state")
        self.add("STATUS records no implementation authorization", "Implementation authorization:** none" in status,"status")
        synth=self.text("challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md").lower()
        for phrase in ["three unranked survivor families","no candidate survives as a one-predicate answer","not proofs","ontological boundary","exit-gate judgment"]:
            self.add(f"Phase synthesis contains boundary: {phrase}",phrase in synth,phrase)
        prohibited=[]
        for rel in ["challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md","challenges/SURVIVOR_SHORTLIST.md","STATE.md","STATUS.md"]:
            t=self.text(rel).lower()
            for pat in [r"we proved consciousness",r"the same subject moved",r"a2 is proved",r"personal identity is established"]:
                if re.search(pat,t): prohibited.append((rel,pat))
        self.add("Core phase surfaces contain no prohibited ontological overclaim",not prohibited,prohibited or "none")
        # Markdown local links.
        broken=[]
        link_re=re.compile(r"\[[^\]]+\]\(([^)]+)\)")
        for p in list((r/"challenges").rglob("*.md")):
            for target in link_re.findall(p.read_text(encoding="utf-8")):
                if target.startswith(("http://","https://","#","mailto:")): continue
                target=target.split("#",1)[0]
                if target and not (p.parent/target).resolve().exists(): broken.append(f"{p.relative_to(r)} -> {target}")
        self.add("All local Markdown links in challenge bank resolve",not broken,broken[:20] or "all resolve")
        self.add("Survivor architecture DOT and SVG exist",(r/"challenges/survivor_architecture.dot").is_file() and (r/"challenges/survivor_architecture.svg").is_file(),"diagram")
        # No implementation artefacts.
        new_code=[p for p in r.rglob("*") if p.is_file() and p.suffix in {".lean",".ipynb"} and "inputs" not in p.parts and "corpus" not in p.parts]
        self.add("CST-EXP-04 adds no Lean or notebook implementation",not new_code,[str(p.relative_to(r)) for p in new_code])
        self.add("Challenge synthesis states no toy program is implemented","no toy program" in self.text("challenges/README.md").lower() or "does not implement" in self.text("challenges/README.md").lower(),"boundary")

        # 14. Summary counts and manifest.
        summ=self.j("manifests/EXP04_ASSET_SUMMARY.json")
        expected={"candidates":10,"hard_cases":18,"hard_case_records":180,"internal_lenses":13,"lens_records":130,"no_go_prospects":18,"external_sources":26,"red_team_positions":7,"survivor_families":3,"scenario_records":350,"assumption_exposure_records":200}
        for k,v in expected.items(): self.add(f"EXP04 summary count matches {k}",summ["counts"].get(k)==v,summ["counts"].get(k))
        self.add("EXP04 summary records all three survivors",{x["id"] for x in summ["survivor_families"]}==family_ids,summ["survivor_families"])
        self.add("EXP04 summary boundary denies proof/implementation/ontology",all(x in summ["boundary"].lower() for x in ["no theorem","no toy program","no final target","personal-identity"]),summ["boundary"])

        if not self.skip_manifest:
            man=self.j("manifests/MANIFEST.json")
            self.add("Manifest is labeled CST-EXP-04",man.get("phase")=="CST-EXP-04",man.get("phase"))
            entries={x["path"]:x for x in man["files"]}
            bad=[]
            for rel,e in entries.items():
                p=r/rel
                if not p.is_file() or self.sha(p)!=e["sha256"] or p.stat().st_size!=e["bytes"]: bad.append(rel)
            self.add("Every manifest file exists with matching size and SHA-256",not bad,{"entries":len(entries),"bad":bad[:20]})
            excluded=set(man.get("excluded",[]))
            self.add("Dynamic validation/manifest surfaces are excluded",all(x in excluded for x in ["manifests/MANIFEST.json","manifests/SHA256SUMS","manifests/REPO_TREE.txt","manifests/VALIDATION_REPORT.md","manifests/VALIDATION_RESULTS.json"]),sorted(excluded))
            sums={}
            for line in self.text("manifests/SHA256SUMS").splitlines():
                m=re.match(r"^([0-9a-f]{64})\s+\*?(.+)$",line.strip())
                if m: sums[m.group(2)]=m.group(1)
            sum_bad=[rel for rel,h in sums.items() if not (r/rel).is_file() or self.sha(r/rel)!=h]
            self.add("SHA256SUMS verifies every listed file",not sum_bad,{"listed":len(sums),"bad":sum_bad[:20]})
            tree=self.text("manifests/REPO_TREE.txt")
            self.add("Repository tree includes challenge, ledger, and script surfaces",all(x in tree for x in ["challenges/CST-EXP-04_ADVERSARIAL_SYNTHESIS.md","ledgers/candidate_hard_case_stress.csv","scripts/validate_exp04.py"]),"tree")

        return self.checks


def render_report(checks:list[dict[str,Any]],skip:bool)->str:
    passed=sum(x["status"]=="pass" for x in checks); failed=len(checks)-passed
    out=["# CST-EXP-04 Validation Report","",f"**Mode:** {'pre-manifest' if skip else 'full frozen repository'}",f"**Result:** {'PASS' if failed==0 else 'FAIL'} — {passed}/{len(checks)} checks passed.","", "| # | Check | Status | Detail |","|---:|---|---|---|"]
    for i,x in enumerate(checks,1):
        d=str(x["detail"]).replace("|","\\|").replace("\n"," ")
        if len(d)>220: d=d[:219]+"…"
        out.append(f"| {i} | {x['name']} | **{x['status'].upper()}** | {d} |")
    return "\n".join(out)+"\n"


def main()->int:
    ap=argparse.ArgumentParser(); ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1]); ap.add_argument("--skip-manifest",action="store_true"); ap.add_argument("--no-write",action="store_true"); args=ap.parse_args()
    v=V(args.root.resolve(),args.skip_manifest); checks=v.run(); failed=[x for x in checks if x["status"]=="fail"]
    result={"schema_version":"1.0","project":"CST-EXP","phase":"CST-EXP-04","mode":"pre_manifest" if args.skip_manifest else "full","date":D.DATE,"status":"pass" if not failed else "fail","checks_total":len(checks),"checks_passed":len(checks)-len(failed),"checks_failed":len(failed),"checks":checks}
    if not args.no_write:
        name="CST-EXP-04_PREVALIDATION" if args.skip_manifest else "VALIDATION"
        (args.root/"manifests").mkdir(exist_ok=True)
        (args.root/f"manifests/{name}_RESULTS.json").write_text(json.dumps(result,indent=2,sort_keys=True,default=lambda o: sorted(o) if isinstance(o,set) else str(o))+"\n",encoding="utf-8")
        (args.root/f"manifests/{name}_REPORT.md").write_text(render_report(checks,args.skip_manifest),encoding="utf-8")
        if not args.skip_manifest:
            (args.root/"manifests/VALIDATION_RESULTS.json").write_text(json.dumps(result,indent=2,sort_keys=True,default=lambda o: sorted(o) if isinstance(o,set) else str(o))+"\n",encoding="utf-8")
            (args.root/"manifests/VALIDATION_REPORT.md").write_text(render_report(checks,args.skip_manifest),encoding="utf-8")
    print(f"{'PASS' if not failed else 'FAIL'} {len(checks)-len(failed)}/{len(checks)}")
    if failed:
        for x in failed: print("FAIL:",x["name"],x["detail"])
    return 0 if not failed else 1

if __name__=="__main__": raise SystemExit(main())
