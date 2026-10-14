# CST-EXP-04 Validation Report

**Mode:** pre-manifest
**Result:** PASS — 305/305 checks passed.

| # | Check | Status | Detail |
|---:|---|---|---|
| 1 | All core inherited and phase-04 files exist | **PASS** | [] |
| 2 | All repository JSON files parse | **PASS** | all parse |
| 3 | All repository CSV files parse | **PASS** | all parse |
| 4 | Inherited CST-EXP-03 surface remains byte-frozen: candidates/CANDIDATE_REGISTRY.json | **PASS** | {'expected': '03d484ead5b69a6400b117db580613cc42d04de957796391f96a8cfe8fe2411e', 'actual': '03d484ead5b69a6400b117db580613cc42d04de957796391f96a8cfe8fe2411e'} |
| 5 | Inherited CST-EXP-03 surface remains byte-frozen: candidates/transported_object_registry.csv | **PASS** | {'expected': '02b71e158df21014f824f07a7791d507be5f1dad26cece606b30f6da5e0d6bb3', 'actual': '02b71e158df21014f824f07a7791d507be5f1dad26cece606b30f6da5e0d6bb3'} |
| 6 | Inherited CST-EXP-03 surface remains byte-frozen: candidates/invariant_registry.csv | **PASS** | {'expected': '7427d89cc5b67e5116de13da03ef59eee03ed42ba13afa4bc1af728b860ab25e', 'actual': '7427d89cc5b67e5116de13da03ef59eee03ed42ba13afa4bc1af728b860ab25e'} |
| 7 | Inherited CST-EXP-03 surface remains byte-frozen: candidates/bridge_registry.csv | **PASS** | {'expected': '1cbae2480478a3fbf4d037107e88dfe34d743c4a933b2f47136535c1068a6fde', 'actual': '1cbae2480478a3fbf4d037107e88dfe34d743c4a933b2f47136535c1068a6fde'} |
| 8 | Inherited CST-EXP-03 surface remains byte-frozen: ledgers/candidate_scenario_verdicts.csv | **PASS** | {'expected': 'f010b92dc3fe1bf5dc2905a6f7806f2e0eb06461631991855158988e2d8a7123', 'actual': 'f010b92dc3fe1bf5dc2905a6f7806f2e0eb06461631991855158988e2d8a7123'} |
| 9 | Inherited CST-EXP-03 surface remains byte-frozen: ledgers/candidate_assumption_matrix.csv | **PASS** | {'expected': 'a8455be01e95ca2c699ba41870d6880aeef111e6747eaef05cf790b2a2e708fa', 'actual': 'a8455be01e95ca2c699ba41870d6880aeef111e6747eaef05cf790b2a2e708fa'} |
| 10 | Inherited CST-EXP-03 surface remains byte-frozen: ledgers/candidate_question_responses.csv | **PASS** | {'expected': 'b4a3146675fd69193b5a2d1c7f62fbf959a441b48b95277e50e4da4e4dd769f4', 'actual': 'b4a3146675fd69193b5a2d1c7f62fbf959a441b48b95277e50e4da4e4dd769f4'} |
| 11 | Inherited CST-EXP-03 surface remains byte-frozen: ledgers/candidate_anti_conflation_audit.csv | **PASS** | {'expected': '8814335cb11c11669f07ebc21b6e8b1b781bfa5181396f70a9767381a71bac4e', 'actual': '8814335cb11c11669f07ebc21b6e8b1b781bfa5181396f70a9767381a71bac4e'} |
| 12 | Inherited CST-EXP-03 surface remains byte-frozen: ledgers/new_primitive_register.csv | **PASS** | {'expected': 'bb8f1b4ad725060a4eb3c5233e73b4d894604b81095f056cc423c6cf34697993', 'actual': 'bb8f1b4ad725060a4eb3c5233e73b4d894604b81095f056cc423c6cf34697993'} |
| 13 | Inherited CST-EXP-03 surface remains byte-frozen: scenarios/SCENARIO_REGISTRY.json | **PASS** | {'expected': 'd0d6b56dd25e98338f40816c4e0e9f45e185c073fb6e9ffd043d18332443eb8e', 'actual': 'd0d6b56dd25e98338f40816c4e0e9f45e185c073fb6e9ffd043d18332443eb8e'} |
| 14 | Inherited CST-EXP-03 surface remains byte-frozen: corpus/machine_index/all_statement_index.csv | **PASS** | {'expected': '89bcdb48eebdf6006cb38c482bfa1b8e887769460f7421b7191bc6250b9ec0c3', 'actual': '89bcdb48eebdf6006cb38c482bfa1b8e887769460f7421b7191bc6250b9ec0c3'} |
| 15 | Inherited CST-EXP-03 completion record reports pass | **PASS** | completion report |
| 16 | Corpus inventory remains 60 papers and 1,359 nonquarantined statements | **PASS** | {'papers': 60, 'statements': 1359} |
| 17 | P46 remains excluded from machine statement bank | **PASS** | 0 |
| 18 | P46 retains one exclusion provenance record | **PASS** | expected one |
| 19 | P42/P60 revision control remains explicit | **PASS** | version log |
| 20 | Candidate registry remains exactly TS-01 through TS-10 | **PASS** | {'TS-09', 'TS-03', 'TS-07', 'TS-01', 'TS-04', 'TS-06', 'TS-08', 'TS-05', 'TS-02', 'TS-10'} |
| 21 | Phase-04 data profiles cover every candidate | **PASS** | {'TS-09', 'TS-03', 'TS-07', 'TS-01', 'TS-04', 'TS-06', 'TS-08', 'TS-05', 'TS-02', 'TS-10'} |
| 22 | Hard-case definition bank contains HC-01 through HC-18 | **PASS** | 18 |
| 23 | Internal-lens definition bank contains IL-01 through IL-13 | **PASS** | 13 |
| 24 | No-go data bank contains NG-01 through NG-18 | **PASS** | 18 |
| 25 | Red-team data bank contains RT-01 through RT-07 | **PASS** | 7 |
| 26 | Survivor bank contains SF-01 through SF-03 | **PASS** | 3 |
| 27 | Every hard-case status matrix has 18 entries | **PASS** | {'TS-09': 18, 'TS-03': 18, 'TS-07': 18, 'TS-01': 18, 'TS-04': 18, 'TS-06': 18, 'TS-08': 18, 'TS-05': 18, 'TS-02': 18, 'TS-10': 18} |
| 28 | Every internal-lens matrix has 13 entries | **PASS** | {'TS-09': 13, 'TS-03': 13, 'TS-07': 13, 'TS-01': 13, 'TS-04': 13, 'TS-06': 13, 'TS-08': 13, 'TS-05': 13, 'TS-02': 13, 'TS-10': 13} |
| 29 | All status codes are registered | **PASS** | S/C/U/N/F only |
| 30 | Hard-case stress ledger has exactly 180 records | **PASS** | 180 |
| 31 | Stress ledger covers complete candidate × case product | **PASS** | 180 |
| 32 | Every stress record names a disposition and substantive finding | **PASS** | [] |
| 33 | Every stress record exposes assumptions and a required response | **PASS** | [] |
| 34 | Every stress record preserves a salvage | **PASS** | [] |
| 35 | All stress-ledger no-go references resolve | **PASS** | all resolve |
| 36 | TS-01 has all 18 hard-case responses | **PASS** | 18 |
| 37 | TS-01 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 38 | TS-02 has all 18 hard-case responses | **PASS** | 18 |
| 39 | TS-02 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 40 | TS-03 has all 18 hard-case responses | **PASS** | 18 |
| 41 | TS-03 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 42 | TS-04 has all 18 hard-case responses | **PASS** | 18 |
| 43 | TS-04 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 44 | TS-05 has all 18 hard-case responses | **PASS** | 18 |
| 45 | TS-05 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 46 | TS-06 has all 18 hard-case responses | **PASS** | 18 |
| 47 | TS-06 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 48 | TS-07 has all 18 hard-case responses | **PASS** | 18 |
| 49 | TS-07 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 50 | TS-08 has all 18 hard-case responses | **PASS** | 18 |
| 51 | TS-08 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 52 | TS-09 has all 18 hard-case responses | **PASS** | 18 |
| 53 | TS-09 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 54 | TS-10 has all 18 hard-case responses | **PASS** | 18 |
| 55 | TS-10 hard-case profile includes at least two response types | **PASS** | ['fails_as_standalone', 'principled_underdetermination', 'survives', 'survives_conditionally'] |
| 56 | HC-01 is evaluated for all ten candidates | **PASS** | 10 |
| 57 | HC-02 is evaluated for all ten candidates | **PASS** | 10 |
| 58 | HC-03 is evaluated for all ten candidates | **PASS** | 10 |
| 59 | HC-04 is evaluated for all ten candidates | **PASS** | 10 |
| 60 | HC-05 is evaluated for all ten candidates | **PASS** | 10 |
| 61 | HC-06 is evaluated for all ten candidates | **PASS** | 10 |
| 62 | HC-07 is evaluated for all ten candidates | **PASS** | 10 |
| 63 | HC-08 is evaluated for all ten candidates | **PASS** | 10 |
| 64 | HC-09 is evaluated for all ten candidates | **PASS** | 10 |
| 65 | HC-10 is evaluated for all ten candidates | **PASS** | 10 |
| 66 | HC-11 is evaluated for all ten candidates | **PASS** | 10 |
| 67 | HC-12 is evaluated for all ten candidates | **PASS** | 10 |
| 68 | HC-13 is evaluated for all ten candidates | **PASS** | 10 |
| 69 | HC-14 is evaluated for all ten candidates | **PASS** | 10 |
| 70 | HC-15 is evaluated for all ten candidates | **PASS** | 10 |
| 71 | HC-16 is evaluated for all ten candidates | **PASS** | 10 |
| 72 | HC-17 is evaluated for all ten candidates | **PASS** | 10 |
| 73 | HC-18 is evaluated for all ten candidates | **PASS** | 10 |
| 74 | Symmetric duplication has no unexplained unique-success verdict | **PASS** | none |
| 75 | External-decoder case classifies every direct survivor as a detector of non-autonomy | **PASS** | [('TS-02', 'survives', 'The final target-native package gate fails even if decoded behavior remains perfect during support. The candidate directly contains a nontrivial response to this challenge, subject to its stated … |
| 76 | Gauge-change case is treated as a carrier-individuation control | **PASS** | HC-16 findings |
| 77 | Internal-lens audit has exactly 130 records | **PASS** | 130 |
| 78 | Lens audit covers complete candidate × lens product | **PASS** | 130 |
| 79 | Every lens audit records challenge, response, and amendment | **PASS** | complete |
| 80 | TS-01 has all 13 internal-lens audits | **PASS** | 13 |
| 81 | TS-02 has all 13 internal-lens audits | **PASS** | 13 |
| 82 | TS-03 has all 13 internal-lens audits | **PASS** | 13 |
| 83 | TS-04 has all 13 internal-lens audits | **PASS** | 13 |
| 84 | TS-05 has all 13 internal-lens audits | **PASS** | 13 |
| 85 | TS-06 has all 13 internal-lens audits | **PASS** | 13 |
| 86 | TS-07 has all 13 internal-lens audits | **PASS** | 13 |
| 87 | TS-08 has all 13 internal-lens audits | **PASS** | 13 |
| 88 | TS-09 has all 13 internal-lens audits | **PASS** | 13 |
| 89 | TS-10 has all 13 internal-lens audits | **PASS** | 13 |
| 90 | IL-01 is applied to all ten candidates | **PASS** | 10 |
| 91 | IL-02 is applied to all ten candidates | **PASS** | 10 |
| 92 | IL-03 is applied to all ten candidates | **PASS** | 10 |
| 93 | IL-04 is applied to all ten candidates | **PASS** | 10 |
| 94 | IL-05 is applied to all ten candidates | **PASS** | 10 |
| 95 | IL-06 is applied to all ten candidates | **PASS** | 10 |
| 96 | IL-07 is applied to all ten candidates | **PASS** | 10 |
| 97 | IL-08 is applied to all ten candidates | **PASS** | 10 |
| 98 | IL-09 is applied to all ten candidates | **PASS** | 10 |
| 99 | IL-10 is applied to all ten candidates | **PASS** | 10 |
| 100 | IL-11 is applied to all ten candidates | **PASS** | 10 |
| 101 | IL-12 is applied to all ten candidates | **PASS** | 10 |
| 102 | IL-13 is applied to all ten candidates | **PASS** | 10 |
| 103 | Audited-emergence lens never upgrades structure to ontology | **PASS** | [('TS-01', 'narrowed_role_only'), ('TS-02', 'survives_conditionally'), ('TS-03', 'narrowed_role_only'), ('TS-04', 'narrowed_role_only'), ('TS-05', 'narrowed_role_only'), ('TS-06', 'survives_conditionally'), ('TS-07', 'n… |
| 104 | Rejection/salvage log has one record per candidate | **PASS** | 10 |
| 105 | Every disposition preserves role, amendment, salvage, and boundary | **PASS** | complete |
| 106 | Exactly TS-02, TS-03, and TS-10 survive as family cores | **PASS** | ['TS-02', 'TS-03', 'TS-10'] |
| 107 | Seven noncore candidates are retained rather than silently deleted | **PASS** | ['TS-01', 'TS-04', 'TS-05', 'TS-06', 'TS-07', 'TS-08', 'TS-09'] |
| 108 | No disposition presents its profile as a ranking | **PASS** | all true |
| 109 | Survivor registry contains exactly three families | **PASS** | 3 |
| 110 | Survivor cores are frozen as TS-02/TS-03/TS-10 | **PASS** | {'SF-01': 'TS-02', 'SF-02': 'TS-03', 'SF-03': 'TS-10'} |
| 111 | Every survivor states claim ceiling, lineage policy, risk, and kill condition | **PASS** | complete |
| 112 | No survivor claim ceiling assumes 'same subject' | **PASS** | none |
| 113 | No survivor claim ceiling asserts consciousness or personal identity | **PASS** | none |
| 114 | Composition matrix is complete 3 × 10 | **PASS** | 30 |
| 115 | SF-01 has exactly one core in composition matrix | **PASS** | ['TS-02'] |
| 116 | SF-01 has at least three explicit modules/mechanisms | **PASS** | 6 |
| 117 | SF-02 has exactly one core in composition matrix | **PASS** | ['TS-03'] |
| 118 | SF-02 has at least three explicit modules/mechanisms | **PASS** | 4 |
| 119 | SF-03 has exactly one core in composition matrix | **PASS** | ['TS-10'] |
| 120 | SF-03 has at least three explicit modules/mechanisms | **PASS** | 4 |
| 121 | Shortlist explicitly states unranked status | **PASS** | 2 |
| 122 | Shortlist explicitly preserves component candidates | **PASS** | all seven |
| 123 | No-go register has exactly 18 entries | **PASS** | 18 |
| 124 | Every no-go has claim, witness, proof spine, falsifier, and nonclaim | **PASS** | complete |
| 125 | Every no-go is explicitly marked unproved | **PASS** | [] |
| 126 | NG-01 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-01.md |
| 127 | NG-01 candidate-impact references resolve | **PASS** | all resolve |
| 128 | NG-02 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-02.md |
| 129 | NG-02 candidate-impact references resolve | **PASS** | all resolve |
| 130 | NG-03 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-03.md |
| 131 | NG-03 candidate-impact references resolve | **PASS** | all resolve |
| 132 | NG-04 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-04.md |
| 133 | NG-04 candidate-impact references resolve | **PASS** | all resolve |
| 134 | NG-05 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-05.md |
| 135 | NG-05 candidate-impact references resolve | **PASS** | all resolve |
| 136 | NG-06 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-06.md |
| 137 | NG-06 candidate-impact references resolve | **PASS** | all resolve |
| 138 | NG-07 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-07.md |
| 139 | NG-07 candidate-impact references resolve | **PASS** | all resolve |
| 140 | NG-08 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-08.md |
| 141 | NG-08 candidate-impact references resolve | **PASS** | all resolve |
| 142 | NG-09 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-09.md |
| 143 | NG-09 candidate-impact references resolve | **PASS** | all resolve |
| 144 | NG-10 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-10.md |
| 145 | NG-10 candidate-impact references resolve | **PASS** | all resolve |
| 146 | NG-11 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-11.md |
| 147 | NG-11 candidate-impact references resolve | **PASS** | all resolve |
| 148 | NG-12 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-12.md |
| 149 | NG-12 candidate-impact references resolve | **PASS** | all resolve |
| 150 | NG-13 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-13.md |
| 151 | NG-13 candidate-impact references resolve | **PASS** | all resolve |
| 152 | NG-14 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-14.md |
| 153 | NG-14 candidate-impact references resolve | **PASS** | all resolve |
| 154 | NG-15 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-15.md |
| 155 | NG-15 candidate-impact references resolve | **PASS** | all resolve |
| 156 | NG-16 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-16.md |
| 157 | NG-16 candidate-impact references resolve | **PASS** | all resolve |
| 158 | NG-17 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-17.md |
| 159 | NG-17 candidate-impact references resolve | **PASS** | all resolve |
| 160 | NG-18 prospectus exists and says not proved | **PASS** | challenges/no_go_conjectures/NG-18.md |
| 161 | NG-18 candidate-impact references resolve | **PASS** | all resolve |
| 162 | No-go bank covers required theme: public-shadow | **PASS** | public-shadow |
| 163 | No-go bank covers required theme: symmetric | **PASS** | symmetric |
| 164 | No-go bank covers required theme: predictive-quotient | **PASS** | predictive-quotient |
| 165 | No-go bank covers required theme: recombination | **PASS** | recombination |
| 166 | No-go bank covers required theme: decoder | **PASS** | decoder |
| 167 | No-go bank covers required theme: route independence | **PASS** | route independence |
| 168 | No-go bank covers required theme: global residual | **PASS** | global residual |
| 169 | No-go bank covers required theme: global gluing | **PASS** | global gluing |
| 170 | No-go bank covers required theme: endpoint equality | **PASS** | endpoint equality |
| 171 | No-go bank covers required theme: temporal-gap | **PASS** | temporal-gap |
| 172 | No-go bank covers required theme: carrier-individuation | **PASS** | carrier-individuation |
| 173 | No-go bank covers required theme: bridge-composition | **PASS** | bridge-composition |
| 174 | No-go bank covers required theme: finite-instrument | **PASS** | finite-instrument |
| 175 | No-go bank covers required theme: certificate | **PASS** | certificate |
| 176 | No-go bank covers required theme: personal identity | **PASS** | personal identity |
| 177 | No-go bank covers required theme: trilemma | **PASS** | trilemma |
| 178 | No-go bank covers required theme: fusion | **PASS** | fusion |
| 179 | No-go bank covers required theme: external support | **PASS** | external support |
| 180 | Exactly 18 hard-case cards exist | **PASS** | 18 |
| 181 | HC-14 card lists all ten candidates | **PASS** | 10 |
| 182 | HC-06 card lists all ten candidates | **PASS** | 10 |
| 183 | HC-04 card lists all ten candidates | **PASS** | 10 |
| 184 | HC-11 card lists all ten candidates | **PASS** | 10 |
| 185 | HC-12 card lists all ten candidates | **PASS** | 10 |
| 186 | HC-03 card lists all ten candidates | **PASS** | 10 |
| 187 | HC-02 card lists all ten candidates | **PASS** | 10 |
| 188 | HC-10 card lists all ten candidates | **PASS** | 10 |
| 189 | HC-05 card lists all ten candidates | **PASS** | 10 |
| 190 | HC-17 card lists all ten candidates | **PASS** | 10 |
| 191 | HC-15 card lists all ten candidates | **PASS** | 10 |
| 192 | HC-18 card lists all ten candidates | **PASS** | 10 |
| 193 | HC-09 card lists all ten candidates | **PASS** | 10 |
| 194 | HC-08 card lists all ten candidates | **PASS** | 10 |
| 195 | HC-01 card lists all ten candidates | **PASS** | 10 |
| 196 | HC-13 card lists all ten candidates | **PASS** | 10 |
| 197 | HC-16 card lists all ten candidates | **PASS** | 10 |
| 198 | HC-07 card lists all ten candidates | **PASS** | 10 |
| 199 | Exactly ten candidate stress cards exist | **PASS** | 10 |
| 200 | TS-02 card includes all 18 hard cases | **PASS** | 18 |
| 201 | TS-02 card includes all 13 internal lenses | **PASS** | 13 |
| 202 | TS-02 card preserves frozen nonclaims | **PASS** | heading |
| 203 | TS-03 card includes all 18 hard cases | **PASS** | 18 |
| 204 | TS-03 card includes all 13 internal lenses | **PASS** | 13 |
| 205 | TS-03 card preserves frozen nonclaims | **PASS** | heading |
| 206 | TS-09 card includes all 18 hard cases | **PASS** | 18 |
| 207 | TS-09 card includes all 13 internal lenses | **PASS** | 13 |
| 208 | TS-09 card preserves frozen nonclaims | **PASS** | heading |
| 209 | TS-07 card includes all 18 hard cases | **PASS** | 18 |
| 210 | TS-07 card includes all 13 internal lenses | **PASS** | 13 |
| 211 | TS-07 card preserves frozen nonclaims | **PASS** | heading |
| 212 | TS-08 card includes all 18 hard cases | **PASS** | 18 |
| 213 | TS-08 card includes all 13 internal lenses | **PASS** | 13 |
| 214 | TS-08 card preserves frozen nonclaims | **PASS** | heading |
| 215 | TS-10 card includes all 18 hard cases | **PASS** | 18 |
| 216 | TS-10 card includes all 13 internal lenses | **PASS** | 13 |
| 217 | TS-10 card preserves frozen nonclaims | **PASS** | heading |
| 218 | TS-04 card includes all 18 hard cases | **PASS** | 18 |
| 219 | TS-04 card includes all 13 internal lenses | **PASS** | 13 |
| 220 | TS-04 card preserves frozen nonclaims | **PASS** | heading |
| 221 | TS-06 card includes all 18 hard cases | **PASS** | 18 |
| 222 | TS-06 card includes all 13 internal lenses | **PASS** | 13 |
| 223 | TS-06 card preserves frozen nonclaims | **PASS** | heading |
| 224 | TS-01 card includes all 18 hard cases | **PASS** | 18 |
| 225 | TS-01 card includes all 13 internal lenses | **PASS** | 13 |
| 226 | TS-01 card preserves frozen nonclaims | **PASS** | heading |
| 227 | TS-05 card includes all 18 hard cases | **PASS** | 18 |
| 228 | TS-05 card includes all 13 internal lenses | **PASS** | 13 |
| 229 | TS-05 card preserves frozen nonclaims | **PASS** | heading |
| 230 | External source registry has exactly 26 records | **PASS** | 26 |
| 231 | External registry IDs are EXT-001 through EXT-026 | **PASS** | 26 |
| 232 | External registry spans at least 12 categories | **PASS** | ['bisimulation_dynamics', 'branching_identity', 'causal_abstraction', 'causal_structure_consciousness', 'computation_and_implementation', 'consciousness_empirical', 'copying_and_observers', 'distributed_state', 'enactiv… |
| 233 | External pass includes at least five 2025–2026 sources | **PASS** | [('EXT-007', '2025'), ('EXT-011', '2025'), ('EXT-013', '2026'), ('EXT-016', '2025'), ('EXT-020', '2025')] |
| 234 | Every external source has bibliographic identity and challenge | **PASS** | complete |
| 235 | Every external source has a stable-looking source locator | **PASS** | [] |
| 236 | No popular-news source is retained as load-bearing evidence | **PASS** | [] |
| 237 | External registry covers classics and current work | **PASS** | {'min': 1984, 'max': 2026} |
| 238 | External crosswalk has at least 90 source-object links | **PASS** | 103 |
| 239 | All external crosswalk source IDs resolve | **PASS** | resolve |
| 240 | All external crosswalk object IDs resolve | **PASS** | [] |
| 241 | Literature map contains all 26 source IDs | **PASS** | 26 |
| 242 | Literature map states engineering analogies are not identity evidence | **PASS** | boundary |
| 243 | Search log records execution date and targeted-not-exhaustive scope | **PASS** | scope and interpretation fields |
| 244 | Exactly seven red-team memos exist | **PASS** | 7 |
| 245 | RT-04 memo has all adversarial-review fields | **PASS** | [] |
| 246 | RT-03 memo has all adversarial-review fields | **PASS** | [] |
| 247 | RT-05 memo has all adversarial-review fields | **PASS** | [] |
| 248 | RT-06 memo has all adversarial-review fields | **PASS** | [] |
| 249 | RT-02 memo has all adversarial-review fields | **PASS** | [] |
| 250 | RT-01 memo has all adversarial-review fields | **PASS** | [] |
| 251 | RT-07 memo has all adversarial-review fields | **PASS** | [] |
| 252 | Red-team bank includes standpoint: functionalist | **PASS** | functionalist |
| 253 | Red-team bank includes standpoint: biological | **PASS** | biological |
| 254 | Red-team bank includes standpoint: duplication | **PASS** | duplication |
| 255 | Red-team bank includes standpoint: sbt audit | **PASS** | sbt audit |
| 256 | Red-team bank includes standpoint: empirical | **PASS** | empirical |
| 257 | Red-team bank includes standpoint: formal-methods | **PASS** | formal-methods |
| 258 | Red-team bank includes standpoint: ontological | **PASS** | ontological |
| 259 | Assumption exposure ledger has 200 records | **PASS** | 200 |
| 260 | Assumption exposure covers 10 candidates × 20 assumptions | **PASS** | 20 |
| 261 | A1 is exposed for all ten candidates | **PASS** | 10 |
| 262 | A1 may not rescue structural failure | **PASS** | [] |
| 263 | A2-P is exposed for all ten candidates | **PASS** | 10 |
| 264 | A2-P may not rescue structural failure | **PASS** | [] |
| 265 | H-CERT-SOUND is exposed for all ten candidates | **PASS** | 10 |
| 266 | H-CERT-SOUND may not rescue structural failure | **PASS** | [] |
| 267 | H-IDENTITY-O is exposed for all ten candidates | **PASS** | 10 |
| 268 | H-IDENTITY-O may not rescue structural failure | **PASS** | [] |
| 269 | H-RECOG is exposed for all ten candidates | **PASS** | 10 |
| 270 | H-RECOG may not rescue structural failure | **PASS** | [] |
| 271 | Unique-lineage assumption explicitly faces symmetric duplication | **PASS** | all ten |
| 272 | Autonomy assumption is cashed out by withdrawal | **PASS** | all ten |
| 273 | Phase-04 scenario ledger preserves all 350 rows | **PASS** | {'old': 350, 'new': 350} |
| 274 | Phase-04 scenario ledger preserves the exact key set | **PASS** | 350 |
| 275 | Every CST-EXP-03 scenario field is byte-for-byte preserved | **PASS** | all preserved |
| 276 | Every phase-04 scenario row is marked frozen and nonranking | **PASS** | all 350 |
| 277 | Every phase-04 scenario row adds a disposition and retained role | **PASS** | all 350 |
| 278 | Decision log contains exactly eight active D04 rulings | **PASS** | ['D04-001', 'D04-002', 'D04-003', 'D04-004', 'D04-005', 'D04-006', 'D04-007', 'D04-008'] |
| 279 | Rejected-defaults log contains ten RD04 entries | **PASS** | 10 |
| 280 | Unresolved-question log contains CST-EXP-04 section | **PASS** | section |
| 281 | STATE advances to CST-EXP-04-v1 and names CST-EXP-05 | **PASS** | state |
| 282 | STATUS records no implementation authorization | **PASS** | status |
| 283 | Phase synthesis contains boundary: three unranked survivor families | **PASS** | three unranked survivor families |
| 284 | Phase synthesis contains boundary: no candidate survives as a one-predicate answer | **PASS** | no candidate survives as a one-predicate answer |
| 285 | Phase synthesis contains boundary: not proofs | **PASS** | not proofs |
| 286 | Phase synthesis contains boundary: ontological boundary | **PASS** | ontological boundary |
| 287 | Phase synthesis contains boundary: exit-gate judgment | **PASS** | exit-gate judgment |
| 288 | Core phase surfaces contain no prohibited ontological overclaim | **PASS** | none |
| 289 | All local Markdown links in challenge bank resolve | **PASS** | all resolve |
| 290 | Survivor architecture DOT and SVG exist | **PASS** | diagram |
| 291 | CST-EXP-04 adds no Lean or notebook implementation | **PASS** | [] |
| 292 | Challenge synthesis states no toy program is implemented | **PASS** | boundary |
| 293 | EXP04 summary count matches candidates | **PASS** | 10 |
| 294 | EXP04 summary count matches hard_cases | **PASS** | 18 |
| 295 | EXP04 summary count matches hard_case_records | **PASS** | 180 |
| 296 | EXP04 summary count matches internal_lenses | **PASS** | 13 |
| 297 | EXP04 summary count matches lens_records | **PASS** | 130 |
| 298 | EXP04 summary count matches no_go_prospects | **PASS** | 18 |
| 299 | EXP04 summary count matches external_sources | **PASS** | 26 |
| 300 | EXP04 summary count matches red_team_positions | **PASS** | 7 |
| 301 | EXP04 summary count matches survivor_families | **PASS** | 3 |
| 302 | EXP04 summary count matches scenario_records | **PASS** | 350 |
| 303 | EXP04 summary count matches assumption_exposure_records | **PASS** | 200 |
| 304 | EXP04 summary records all three survivors | **PASS** | [{'core': 'TS-02', 'id': 'SF-01', 'mandatory_modules': 'TS-04;TS-06;TS-07;TS-08;TS-09', 'title': 'Integrated Autonomous Handoff'}, {'core': 'TS-03', 'id': 'SF-02', 'mandatory_modules': 'TS-04;TS-07;TS-08', 'title': 'Cau… |
| 305 | EXP04 summary boundary denies proof/implementation/ontology | **PASS** | No theorem or no-go is proved; no toy program is implemented; no final target, consciousness conclusion, or personal-identity verdict is selected. |
