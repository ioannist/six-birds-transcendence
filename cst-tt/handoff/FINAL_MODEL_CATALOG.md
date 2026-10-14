# Final toy and model catalog

The catalog separates exact positive witnesses, exact countermodels, and the unexecuted fallback toys. Model files and certificates are hash-bound in the repository manifest.

| ID | Name | Evidence grade | Canonical evidence | Purpose |
|---|---|---|---|---|
| TTM-01 | live temporal handoff | checked exact finite witness | formal/certificates/fiach/FIACH-POS-01.certificate.json;formal/certificates/composition/FIACH-COMP-01.certificate.json | TTH-02;TTH-04;TTH-05;TTH-06 |
| TTM-02 | detached exact temporal copy | checked finite countermodel | formal/certificates/countermodels/CM-01.certificate.json;formal/certificates/countermodels/CM-02.certificate.json | TTN-01 |
| TTM-03 | direct-successor temporal handoff | checked exact finite witness | formal/certificates/direct_successor/DS-POS-01.certificate.json;formal/certificates/direct_successor/DS-PATH-POS-01.certificate.json | TTD-01;TTD-03 |
| TTM-04 | external scheduler or decoder shadow | checked finite countermodel | formal/certificates/countermodels/CM-04.certificate.json;formal/certificates/autonomy/controls/AUT-C01.certificate.json | TTN-06 |
| TTM-05 | replacement-order holonomy | checked finite countermodel | formal/certificates/countermodels/CM-07.certificate.json;formal/certificates/routes/ROUTE-NEG-01.certificate.json | TTN-04;TTN-05 |
| TTM-06 | confluent completion | checked exact finite witness | formal/certificates/routes/ROUTE-POS-01.certificate.json | TTH-09 |
| TTM-07 | temporal fission | checked exact finite witness | formal/certificates/fission/FISSION-POS-01.certificate.json;formal/certificates/countermodels/CM-11.certificate.json | TTH-08;TTN-11 |
| TTM-08 | gap and resume | checked finite countermodel | formal/certificates/countermodels/CM-12.certificate.json | TTN-09 |
| TTM-09 | anti-stall target | checked finite countermodel | formal/certificates/autonomy/controls/AUT-C05.certificate.json | TTH-05;TTN-07 |
| TTM-10 | long-run budget failure | checked finite countermodel | formal/certificates/countermodels/CM-13.certificate.json;formal/certificates/autonomy/controls/AUT-C06.certificate.json | TTN-12 |
| TTM-11 | local/global package obstruction | checked finite countermodel | formal/certificates/countermodels/CM-08.certificate.json | TTN-08 |
| TTM-12 | public-shadow collision | checked finite countermodel | formal/certificates/countermodels/CM-09.certificate.json | TTN-02 |
| TTM-13 | scalar hard-gate failure | checked finite countermodel | formal/certificates/countermodels/CM-10.certificate.json | TTN-10 |
| TTM-14 | stable tick without progress | checked finite countermodel | formal/certificates/countermodels/CM-05.certificate.json | TTN-07 |
| TTM-15 | same-carrier re-encoding | checked finite countermodel | formal/certificates/countermodels/CM-14.certificate.json | TTN-13 |
| TTM-16 | holonomy without arrow | checked finite countermodel | formal/certificates/countermodels/CM-03.certificate.json | TTN-03 |
| TTM-17 | current-equal predictive-route mismatch | checked finite countermodel | formal/certificates/countermodels/CM-06.certificate.json;formal/certificates/memory/MEM-POS-01.certificate.json | TTN-04 |
| TFM-01 | source-derived destructive successor | open | — | TTF-02;TTF-05;TTF-06 |
| TFM-02 | independent structural twin | open | — | TTF-03;TTF-06 |
| TFM-03 | source-derived symmetric duplication | open | — | TTF-04;TTF-07 |
| TFM-04 | fusion with recombination conflict | checked finite countermodel | formal/certificates/countermodels/CM-15.certificate.json;formal/certificates/fusion/FUSION-BOUNDARY-01.certificate.json | TTF-04;TTF-08;TTN-14 |
| TTM-18 | integrated target C-package | checked exact finite witness | formal/certificates/packages/PKG-POS-01-TARGET.certificate.json | TTH-01;TTN-08;TTN-14 |
| TTM-19 | staged heterogeneous package assembly | checked exact finite witness | formal/certificates/packages/STG-POS-01.certificate.json | TTH-02 |
| TTM-20 | mixed overlap/direct continuity path | checked exact finite witness | formal/certificates/strengthenings/continuity/GCP-MIXED-01.certificate.json | TTS-01 |
| TTM-21 | exact vector defect profile | checked finite countermodel | formal/certificates/strengthenings/defects/DEF-POS-01.certificate.json;formal/certificates/strengthenings/defects/DEF-EQUAL-SCALAR-01.certificate.json | TTS-02;TTN-10 |
| TTM-22 | hard-gate-preserving robustness box | checked exact finite witness | formal/certificates/strengthenings/robustness/ROB-POS-01.certificate.json | TTS-03 |
| TTM-23 | total invariant autonomy policy | checked exact finite witness | formal/certificates/strengthenings/unbounded/UNB-POS-01.certificate.json | TTS-04 |
| TTM-24 | arbitrarily long finite-prefix countdown family | checked finite countermodel | formal/certificates/search/ARBITRARILY_LONG_FINITE_PREFIX_FAMILY.json | TTN-12;TTS-04 |
