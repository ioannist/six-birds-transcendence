# G6d-2 continuation 4: C1 protocol equivalence and C5 schema

## Proved boundary

### C1: arbitrary partial assignments, both directions

`POS04ObjecthoodProtocol.generic_c1_iff a tag` proves

```lean
POS04ObjecthoodProtocol.Accept a tag ↔ CSTTT.POS04.Assigned.C1Accept a tag
```

for **every** partial assignment and both tags. This is not the earlier
canonical-truth equivalence. The polymorphic `ObjecthoodRules` and
`ObjecthoodCells` remain unchanged and continue to admit arbitrary finite
carriers and protocols.

The checked POS-04 specialization adds the explicit raw `Protocol`:

- audit parameters and published P/C/U equal the exact T1 protocol (`T1Anchors`);
- positive row weights, references and scaled row totals satisfy `RowsValid`;
- the raw prototypes are in the published first-occurrence column order.

It then requires the actual generic decoder and generic C1 acceptance.
There is no reconstruction, uniqueness, or acceptance verdict in `Protocol`.
A consumed missing cell fails the Option decoder even if an old input decoder
would have a default.

**Forward direction:** legacy raw equations imply the exact prototype order,
kernel validity, quotient validity and all-action support. The preceding seam's
symbolically transported row-operation trace proves the normalized-system
check and uniqueness. Its derived audit quantities prove generic acceptance.

**Converse:** generic rational P/C/U reconstruction, combined with the fixed
protocol, yields legacy scaled-integer reconstruction. The C columns force
the predictive partition. Its fibers have sizes one or two, which justifies
U's integer scaling without assuming it. `reconstructed_from_generic` proves
all legacy table checks, including the CU equation. The existing proved
`c1_accept_iff_gate` finishes the legacy numerical audit.

Locality, missing-input rejection, protocol/order/reference rejection,
canonical instances and all C1–C3 control transfers are proved. C3-PROFILE's
C1 failure remains attributed to P, not a changed predictive partition.

### C5: generic protocol-credit surrogate

`ProtocolCreditRules` imports only the generic substrate. State, action,
outcome, vertex, edge, channel, protocol, history, owner and cell types are
polymorphic. Cycles may have arbitrary length. The schema declares finite
complete domains, the raw directed cycle, edge projections, self/other
channels, owner ids, history anchors and the expected credit audit.

The evaluator **computes** forward/reverse generator products, self/other/
none/ambiguous credit, provenance ownership and supported history anchors.
`DomainCheck` requires complete duplicate-free domains. `CreditCoverage`
requires self, other and none audit roles, preventing an empty/no-generator
audit from passing. Rows are checked for positive weights, references and
scale. This is the existing **protocol-credit surrogate**, not full T5.
Housing is transported as raw provenance; it never determines credit.

Four typed primitive views (protocol tables, action rows, policy and histories)
are decoded without defaults. Decoder, gate and acceptance locality and
missing-input rejection are generic. The raw table transport permits different
source/target protocol, edge and owner types.

`POS04ProtocolCredit.generic_c5_iff` and `generic_c5_gate_iff` give exact
acceptance/gate equivalences for **all partial assignments**, on both tags.
`generic_transport_iff` identifies the computed transport with assigned
`C5Transport`. Product, credit and supported-history equations are established
before using acceptance equivalence.

Canonical acceptance and transport are proved. `controls_equivalence`
transfers every existing C5 variant. Specifically:

| Control | Source C5 | Target C5 | Transport |
|---|---|---|---|
| external generator | pass | fail | not claimed by this outcome theorem |
| internally housed scheduled generator | pass | pass | fail |

Internal housing is not internal credit; the control retains its other credit.

## Arguments and guards

| Argument | Classification |
|---|---|
| finite domains, cycle, edge/reference projections, owner ids, expected credit roles | raw schema/audit data |
| typed primitive views | raw binding instructions onto shared cells |
| immutable assignment, tag | raw data and namespace selection |
| raw equation, completeness and locality proofs | evidence on raw data |
| decoded records, M/fibers, rational operators/candidate, products/credits and acceptance | defined objects; never supplied |

| Field family | Check/link | Guard theorem |
|---|---|---|
| every consumed C1 cell | exact decoder and protocol specialization | C1 `missing_rejected` |
| C1 rows/positions/hazards/policy/prototypes/P/C/U | actual rational reconstruction and raw protocol checks | C1 `field_guards` (one edit per family) |
| C1 tau/epsilon/retention | exact raw protocol equality | C1 `field_guards`, `changed_protocol_rejected` |
| C1 column order | exact first-occurrence prototypes | `changed_column_order_rejected` |
| four C5 primitive cells | Option decoding; exact scope equality | generic `missing_rejected`; POS-04 `missing_rejected` |
| C5 generator edges | computed forward/reverse products | generic `empty_generator_rejected`; POS-04 `edges_guard` |
| C5 owner | computed credit's own provenance check | generic `wrong_self_owner_rejected`; POS-04 `owners_guard` |
| C5 housing | staged raw ownership/housing transport | POS-04 `housing_guard` (transport, not local acceptance) |
| C5 rows/policy | actual canonical action support along anchors | POS-04 `rows_guard`, `policy_guard` |
| C5 histories | nonempty supported raw paths | generic `unsupported_anchor_rejected`; POS-04 `histories_guard` |
| C5 edge projection instructions | exact computed counts | POS-04 `edge_from_guard`, `edge_to_guard`, `edge_channel_guard` |
| C5 cycle/domain/credit targets | length, distinct channels, domain coverage and credit coverage | `empty_cycle_rejected`, `equal_channels_rejected`, `missing_state_rejected`, `missing_self_role_rejected`, `wrong_credit_rejected` |

## Not proved here

C4 and C7 generic schemas/equivalences remain. Temporal/C8 extraction and the
**proved** run-to-factor lift remain. No finite-factor lifting claim or new
finite-context premise is introduced. The §7.4 stop rule applies before any
such premise is added. No TTH-06 promotion or status/inventory change occurs.

All new statements are **(b) mathematical additions**, with no existing
statement changes, renames or narrowing. Frozen science/model files remain
unchanged.

## Checks

- `cd lean && lake build`: exit 0, 369 jobs; no new-module warnings.
- `scripts/validate_lean.sh`: exit 0; inventory matches, zero placeholders,
  zero high-confidence vacuity findings, no untrusted axioms.
- `#print axioms` on all 65 new public theorems: standard three or fewer.
- New-source forbidden scan and `git diff --check`: clean.
- Frozen `cst-tt/`, vendor, registry and inventory files: unchanged.

All edits remain uncommitted.
