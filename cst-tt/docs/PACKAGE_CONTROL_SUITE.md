# CST-TT-02 Package Control Suite

| Control | Kind | Removed obligation | Observed failures |
|---|---|---|---|
| PC-01 | package | PKG-O01-exact-C1-C8-coverage | PKG-O01-exact-C1-C8-coverage;PKG-O02-local-scope-and-clause-acceptance;PKG-O03-nonnegotiable-hard-gates;PKG-O07-global-gluing-and-restriction |
| PC-02 | package | PKG-O02-local-scope-and-clause-acceptance | PKG-O02-local-scope-and-clause-acceptance |
| PC-03 | package | PKG-O02-local-scope-and-clause-acceptance | PKG-O02-local-scope-and-clause-acceptance |
| PC-04 | package | PKG-O02-local-scope-and-clause-acceptance | PKG-O02-local-scope-and-clause-acceptance |
| PC-05 | package | PKG-O02-local-scope-and-clause-acceptance | PKG-O02-local-scope-and-clause-acceptance |
| PC-06 | package | PKG-O02-local-scope-and-clause-acceptance | PKG-O02-local-scope-and-clause-acceptance |
| PC-07 | package | PKG-O08-substantive-C6-temporal-closure | PKG-O03-nonnegotiable-hard-gates;PKG-O08-substantive-C6-temporal-closure |
| PC-08 | package | PKG-O03-nonnegotiable-hard-gates | PKG-O03-nonnegotiable-hard-gates |
| PC-09 | package | PKG-O02-local-scope-and-clause-acceptance | PKG-O02-local-scope-and-clause-acceptance |
| PC-10 | package | PKG-O06-edge-overlap-compatibility | PKG-O06-edge-overlap-compatibility;PKG-O07-global-gluing-and-restriction |
| PC-11 | package | PKG-O04-rooted-join-tree-shape | PKG-O04-rooted-join-tree-shape;PKG-O05-running-intersection |
| PC-12 | package | PKG-O05-running-intersection | PKG-O05-running-intersection;PKG-O07-global-gluing-and-restriction |
| PC-13 | package | PKG-O07-global-gluing-and-restriction | PKG-O07-global-gluing-and-restriction |
| PC-14 | package | PKG-O08-substantive-C6-temporal-closure | PKG-O03-nonnegotiable-hard-gates;PKG-O08-substantive-C6-temporal-closure |
| PC-15 | package | PKG-O09-target-local-package-ownership | PKG-O09-target-local-package-ownership |
| PC-16 | package | PKG-O08-substantive-C6-temporal-closure | PKG-O03-nonnegotiable-hard-gates;PKG-O08-substantive-C6-temporal-closure;PKG-O09-target-local-package-ownership |
| PC-17 | package | PKG-O10-verdict-field-separation | PKG-O10-verdict-field-separation |
| SC-01 | staged-assembly | STG-O07-value-translation-soundness | STG-O07-value-translation-soundness |

Every package obligation PKG-O01 through PKG-O10 has at least one exact one-obligation-removed control. C1 through C8 each also has a direct clause-specific failure. Cascading failures are retained rather than concealed; for example, breaking running intersection may also make a global assignment impossible.
