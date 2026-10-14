#!/usr/bin/env python3
"""Build CST-EXP-01 corpus cards, ledgers, and asset atlas.

The builder is deterministic over the extracted statement index and source tree.
It performs research inventory construction only; it selects no transfer target.
"""
from __future__ import annotations
from pathlib import Path
import argparse, csv, hashlib, json, re, shutil, textwrap, zipfile
from collections import defaultdict, Counter

WAVES = {
  1:['P05','P28','P29','P33'],
  2:['P14','P18','P24','P30','P50','P53'],
  3:['P08','P16','P23','P03','P09','P39','P06','P04'],
  4:['P32','P56','P57','P31','P22'],
  5:['P13','P12','P44','P02','P34','P35','P17'],
  6:['P07','P52','P40','P45','P59'],
  7:['P58'],
}
WAVE_OF = {p:w for w,ps in WAVES.items() for p in ps}
FIXED_SUPPORT = {'P03','P08','P09','P14','P16','P18','P23','P24','P39'}
QUARANTINED = {'P46'}
VERSION_NORMATIVE = {'P42'}
VERSION_SUPERSEDED = {'P60'}

TRIAGE_USE_OVERRIDE = {
 'P46':'No substantive content is imported in CST-EXP-01. The metadata-only card exists solely to prove corpus coverage while preserving the owner-inherited quarantine.',
}
TRIAGE_BOUNDARY_OVERRIDE = {
 'P46':'Quarantine is fail-closed: no theorem, definition, map, witness, formal asset, or application lesson from P46 may enter the project bank unless the owner explicitly revokes the exclusion.',
 'P60':'P60 is an older revision of the same Strict Audited Utility line as P42, not independent evidence. Use P42 as normative and retain P60 only for provenance or statement-level delta checks. Profile transfer still does not establish cross-domain object identity.',
}

CLAIM_TAGS_BY_ASSET = {
 'carrier':'S-T;S-R','transport':'S-T','predictive':'S-L;S-T','identity':'S-L',
 'recombination':'S-L;S-R','promotion':'S-R;S-T','admissibility':'S-R;R',
 'autonomy':'A;S-R','viability':'A;S-R','hiddenness':'R;S-R','holonomy':'S-T;S-L',
 'temporal':'S-L;A','consciousness':'S-R','audit':'M;R','finite':'M','record':'R;S-R'
}

# Manual source passages for manuscripts without theorem-like environments, and
# a few source-critical boundary passages. They are compacted from exact lines.
MANUAL_PASSAGES = {
 'P05':[
   ('C-package component-evidence table and no integrated instance',627,643,'S-R;M','C-package;component-level;nonclaim'),
   ('T18 temporal consequence cluster and no canonical now-transport',1422,1463,'A;S-L;M','temporal;holonomy;nonclaim'),
   ('T17 seven-claim separation, simplified/full nonordering, and absent integrated target',1630,1687,'S-R;O;M','certificate;nonordering;open-target'),
 ],
 'P03':[
   ('Layer-local old/new carrier grammar and nonfactorization boundary',323,416,'S-T;S-R','promotion;carrier;fixed-support'),
   ('PICA promotion–internalization–exactification route',489,519,'S-T;S-R','promotion;exactification;route'),
   ('Native state, transport/readout laws, and exactification certificate',646,683,'S-T;S-R','carrier;transport;readout'),
   ('Result and inherited nonclaim boundary',1575,1684,'M;S-T;S-R','nonclaim;fixed-support'),
 ],
 'P07':[
   ('Predictive quotient primitive and transport explicitly not tested',184,204,'S-L;S-T;M','predictive;transport;nonclaim'),
   ('QEC instantiation map and scope fences',211,258,'S-R;M','qec;carrier;scope'),
   ('Registered failure, diagnosis, corrected witness, and recalibration loop',389,495,'M;A;S-R','audit;repair;control'),
   ('What the QEC instantiation does and does not establish',504,526,'M;O','nonclaim;engineering-analogue'),
 ],
 'P12':[
   ('Declared quotient, lens, protocol, and exact-finite objects',209,260,'S-L;R;M','predictive;record;finite'),
   ('Current-equal/future-different Kovacs split and scalar buyback',457,529,'S-L;S-T','split-pair;memory;refinement'),
   ('Lens-definable predicate foreclosure and control panel',530,625,'R;M','hiddenness;counterfeit;controls'),
   ('Strict extension certificate and explicit non-autonomy boundary',628,729,'S-R;A;M','promotion;nonclaim'),
 ],
 'P28':[
   ('Core finite audited interaction-calculus result map',203,282,'M;S-R;S-T','interaction;admissibility;promotion'),
   ('Explicit no-universality, no-activation-equivalence, and no-self-certification boundaries',303,338,'M','nonclaim;scope'),
   ('Finite host, primitive, level, and status discipline',376,736,'M;S-R','finite;typing;status'),
   ('Theory-package and morphism grammar',1003,1108,'S-T;S-R','package;morphism;admissibility'),
 ],
 'P35':[
   ('Scheduled counterexample: holonomy without thermodynamic arrow',151,200,'M;A;S-L','protocol-trap;holonomy;control'),
   ('Autonomous phase lift separating external schedule from internal protocol state',201,246,'A;S-T','autonomy;lift;temporal'),
   ('Driven clock: where genuine arrow audit enters',247,295,'A;M','temporal;currency;audit'),
 ],
 'P38':[
   ('Common-staging and lens-swap audit discipline',239,351,'M;R','lens;staging;control'),
   ('Limits and non-novelty boundary',528,564,'M','nonclaim;peripheral'),
 ],
 'P39':[
   ('Three admissibility rungs and identity-lane taxonomy',288,341,'S-R;S-L','admissibility;identity;event'),
   ('Protocol-indexed event bridge and missing bridge-level law basis',390,447,'S-R;S-L;M','event;identity;missing-subobject'),
   ('Accepted same-role edges and event-package obstruction',511,672,'S-L;S-R;M','identity;event;obstruction'),
   ('Final gate and exact claim boundary',816,859,'M;S-R','nonclaim;fixed-support'),
 ],
 'P41':[
   ('Abstract-level cosmological-constant application boundary',104,132,'M','not-primary;application'),
 ],
 'P43':[
   ('Layer, closure, audit, and route-mismatch dictionary',103,268,'M;S-T;S-R','closure;route;record'),
   ('Scope, modeling, failure, and limitation boundary',735,792,'M','nonclaim;supporting'),
 ],
 'P47':[
   ('Primitive-activation layer-birth classification',1,260,'M;S-R','classification;promotion;control'),
 ],
 'P49':[
   ('Finite stochastic substrate and ablation method',1,260,'M;S-R','finite;ablation;toy-method'),
 ],
 'P51':[
   ('Common-refinement versus hierarchy grammar and anti-contamination boundary',250,416,'M;S-T','refinement;route;not-primary'),
 ],
 'P53':[
   ('Time decomposed into order, measure, and arrow',159,229,'S-L;A;M','temporal;closure'),
   ('Finite Markov clock/ledger laboratory and audit suite',230,315,'A;M','finite;clock;ledger'),
   ('Budgeted clock viability and anti-stall progress',348,406,'A;S-R','viability;temporal;currency'),
   ('Protocol holonomy as obstruction to global time',461,530,'S-L;S-T','holonomy;temporal;route'),
   ('Local records and protocol-dependent time translation',579,587,'S-L;R','record;temporal'),
 ],
 'P54':[
   ('Points as quotient classes and distances as optimized protocol costs',140,269,'S-R;M','geometry;quotient;route'),
   ('Geometry-birth diagnostics and limits',270,351,'M','audit;supporting'),
 ],
 'P56':[
   ('Strict layer-relative definition of currency',142,213,'A;M','currency;constraint;route'),
   ('Currency–constraint principle and shadow-price emergence',214,252,'A;S-R','currency;viability;promotion'),
   ('Finite Markov measurement pipeline',258,335,'M','finite;audit;dual'),
   ('Budget buys object stability; proxy currencies can fail',336,417,'A;S-R;M','currency;objecthood;control'),
   ('Explicit empirical and ontological nonclaims',418,455,'M;O','nonclaim'),
 ],
 'P57':[
   ('Agenthood versus agency and theory-object typing',75,133,'A;S-R;M','agenthood;agency;typing'),
   ('Controlled kernel, ledger feasibility, viability greatest fixed point, and empowerment channel',189,315,'A;S-R','viability;controlled-kernel;channel'),
   ('Repair-enabled packaging and objecthood proxy',338,379,'A;S-R','repair;packaging'),
   ('Single-action and external-schedule null controls',380,425,'A;M','protocol-trap;controls'),
   ('Protocol holonomy and horizon-dependent control',426,481,'A;S-L','holonomy;agency'),
 ],
 'P58':[
   ('Free versus purchased metaphysical claims',144,196,'O;M','ontology;assumption-pricing'),
   ('Object as audited closure survivor, not public shadow',197,213,'O;S-R','objecthood;shadow'),
   ('A1 Ontic Closure Completeness and A2 Substrate Indifference price box',295,326,'O;M','A1;A2;non-theorem'),
   ('Ghosts and simulation-versus-instance boundary',327,358,'O;R','counterfeit;recognition'),
 ],
}

# Preferred statement-name/label fragments. These are not theorem-target choices;
# they prioritize source material for the inventory.
PREFERRED = {
 'P02':['record','Leibniz','context','closure'],
 'P04':['audit energy','legal quotient','residual','adequacy','chain rule','bridge'],
 'P05':['Carrier, actions, lens','Quotient, refinement','Predictive and observational','Closure operator','Viability kernel','Full C-package','Exact forcing','non-exposure','No-shortcut','Report descent','Leibniz quotient','Certificate demarcation','authorship','Same-level','Meta-problem composition','Binding witness','Purchased clock','Exact dual prices','valence bridge','Induced-kernel','gauge','Existence boundary','Lineage','Combination','A1','A2','Conditional realization'],
 'P06':['PreSB carrier','Scope record','PreSB morphism','AOR subcategory','Closure-completion','Universal property','adjunction','Eight-stratum','Thirteen residual','cascade confluence','Cross-cascade','asymptotic','No strong-realism'],
 'P08':['Carrier candidate','Reduction','Criterion implication'],
 'P09':['Event bridge','Event admissibility','Test family','Shared-event identity','Final-gate'],
 'P13':['Current quotient','Predictive quotient','Forget-witness','Autonomous lift','loop-action asymmetry','Visibility coupling','core','dissolution','preservation','hiddenness'],
 'P14':['Route transport package','Current equivalence','Predictive equivalence','Predictive witness','Future refines current','Predictive transport','Future sufficient','reachable','strict refinement','Loop asymmetry'],
 'P16':['surviving','package','carrier','readout','reduction','criterion'],
 'P17':['Finite stable record context','Event package','Frozen support','global realization','obstruction'],
 'P18':['refinement under detectability','Quotient-lift','No-interference','Strict refinement','positive instance'],
 'P22':['legality','feasibility','channel','persistence','kernel'],
 'P23':['promotion','criterion','surviving','package','fixed support'],
 'P24':['branchwise','recombination','control','anchor','witness'],
 'P29':['admissibility','meta-theory','exact six','status','morphism','completion'],
 'P30':['Closure formation','Current and predictive','Split pair','Quotientality','No-overread','No-free-distinction','Hiddenness','No needles','Sufficiency','Strict extension','Unstatused','Target repair','route residue','Holonomy-memory','Local-global','Bridge composition','Object Persistence','Composability','Presentation invariance','record monotonicity'],
 'P31':['dynamical','persistence','repair','viability','closure','transport','history'],
 'P32':['E-system','Self-Maintaining','Repair Compilation','Control-Price','Offline Reclosure','Adaptability','Audit capture'],
 'P33':['Finite theory package','Interface lens','Ports, causal bridge','Self-generated primitives','protocol holonomy','Protocol trap','accounting'],
 'P34':['NG_ARROW','NG_LADDER','protocol','Closed-walk','Exactness','Extension escape'],
 'P40':['shell','Cantor','closure','boundary','finite'],
 'P42':['Promotion bridge','Strict Audited Utility certificate','Finite promoted-use trace','Accepted promoted-use trace','Strict and essentially promoted','Audit-equivalent','Basic audit grammar','Canonical witness vector','profile skeleton','substrate erasure','Profile equivalence does not imply object identity','transfer plan','profile-transfer soundness','failure modes'],
 'P44':['closure deficit','Exact decomposition','Expected KL','closed packaging','vanishing deficit','Route mismatch'],
 'P45':['phase','regime','classifier','control','transition'],
 'P50':['Reduction 2-complex','Elementary holonomy','Local confluence','flatness iff','unique normal','Completion as holonomy','remaining gap'],
 'P52':['Substrate','No smuggling','Lens','Packaging endomap','packaging-respecting','Audit monotonicity','Canonical minimal','Realizability','Compilation','No-smuggling separations','Status and scope'],
 'P55':['assumption','purchased','lift','extension'],
 'P59':['Boolean','logic','XOR','closure'],
 'P60':['profile not object identity','profile transfer','substrate erasure','portability without collapse','transfer plan'],
}

# Compact typed-map ledger. "Imported status" distinguishes actual paper objects
# from project-side abstractions of prose.
MAPS = {
 'P02':[
  ('record lens / packaging','X → R or X → X','micro/global state','packaged record state','paper-defined','Context- and interface-relative; matching records need not identify underlying states.'),
  ('context transition','R_c → R_d','record algebra in context c','record algebra in context d','paper-defined','Route mismatch may obstruct a global context-independent record object.'),
 ],
 'P03':[
  ('old/new readouts','C → Y₀ and C → Y₁','exactified carrier','old-layer and new-layer records','paper-defined','Both live on one fixed support; no X_s → X_t migration map.'),
  ('native update/readout','C × U → C; C → Y₁','new-layer carrier state/action','next carrier state/new readout','paper-defined','Layer-local strictness is one-way compatible with descent.'),
 ],
 'P04':[
  ('probe embeddings / projections','V_native,V_dest ↪ H','probe spans','common audited Hilbert space','paper-defined','Residual is computed only after a declared common comparison space.'),
  ('exact/defective bridge','H_s → H_t','source audit space','target audit space','paper-defined','Exact bridges transport adequacy identities; defective bridges carry a priced defect.'),
 ],
 'P05':[
  ('closure family','E_τ: X → X','carrier state','closed/exposed carrier state','paper-defined','C1 is staging- and retention-relative.'),
  ('public and predictive lenses','Q: H → Q; M: H → M','histories or reachable states','current/public and future-sufficient classes','paper-defined','C3/C4/T14 need the predictive object, not only Q.'),
  ('lower/promoted readouts','π₀: X → Y₀; π₁: X → Y₁','carrier','declared layer records','paper-defined','C2 strictness is a nonfactorization relation between these maps.'),
  ('branchwise/recombination quotients','q_bw: H → K_bw; q_rec: H → R_rec','joint branch histories','branchwise/joint-content classes','paper-defined','C7 requires R_rec strictly refine K_bw.'),
  ('conditional bridge','Cert_simp(X,pkg) → ClosureComplete(X,pkg) → Realized(X,pkg)','simplified certificate','ontological predicate','assumption-composed','Both arrows are assumptions; this is not transport.'),
 ],
 'P06':[
  ('PreSB morphism','F: C → D','pre-audited carrier record','pre-audited carrier record','paper-defined','Requires identical scope and commuting structure fields.'),
  ('closure completion','Cl_SB: PreSB → AOR','pre-audited carrier','audit-closed completion','paper-defined/reflection','A completion on typed carrier records, not personal continuation.'),
  ('unit of reflection','η_C: C → U Cl_SB(C)','original carrier record','underlying completed record','paper-defined','Universal property supports canonical repair relative to the category.'),
 ],
 'P07':[
  ('syndrome/decoder pipeline','error history → syndrome record → recovery/logical readout','physical error process','logical record','engineering instantiation','Transport between physical substrates is explicitly outside the experiment.'),
 ],
 'P08':[
  ('public compression/readout','π: C → Y','exactified carrier','public signature','paper-defined','Nonfaithful public shadow is a control, not a carrier identity map.'),
  ('autonomous carrier update','F: C × U → C','carrier state/action','next carrier state','paper-defined','Exactification is on the same native support.'),
  ('reduction','ρ: C_exact → S_declared','exactified carrier','designated lower surface','paper-defined','Reduction certifies public compatibility, not invertibility.'),
 ],
 'P09':[
  ('instrument/readout','I: C → O','carrier','event observation','paper-defined','Event admissibility is instrument- and threshold-relative.'),
  ('selected lift/forget map','ℓ or f between carrier and event surfaces','carrier/event records','event/carrier records','paper-defined','The record stores visibility and suppression; no shared identity object follows.'),
 ],
 'P12':[
  ('current lens','Q: H → Q','prepared histories','current macrostate class','paper-defined','Kovacs pair collides here.'),
  ('predictive/memory refinement','M: H → M','prepared histories','future-response class','paper-defined','Separates current-equal/future-different histories.'),
 ],
 'P13':[
  ('current/predictive quotients','q: H → Q; m: H → M','history space','current and future-sufficient classes','paper-defined','Hiddenness is relative to a declared exposure family.'),
  ('forget-witness map','φ: M → Q','predictive class','current class','paper-defined','Witness refinement makes Q a quotient of M on the declared support.'),
  ('autonomous lift','L: lower process → enlarged process','visible process','internally seeded/coupled process','paper-defined','Lift family controls whether determining variables become exposed.'),
 ],
 'P14':[
  ('route continuation','C_{i→j}: H_i → H_j','histories at interface i','histories at interface j','paper-defined','All interfaces sit on a declared fixed support.'),
  ('predictive transport','T_{i→j}: M_i → M_j','predictive quotient at i','predictive quotient at j','paper-defined','Well-defined only after future-sufficiency/factorization conditions.'),
  ('observation','obs_i: H_i → O_i','interface history','current record','paper-defined','Current equivalence can be strictly coarser than predictive equivalence.'),
 ],
 'P16':[
  ('promoted package inclusion/reduction','P ↪ C; ρ: C → S','surviving package/native carrier','declared lower surface','paper-defined','One fixed support; internal structure is not yet cross-carrier transport.'),
 ],
 'P17':[
  ('restriction maps','r_{UV}: E(U) → E(V)','local event package on U','package on overlap V','paper-defined','Compatibility on overlaps is required for gluing.'),
  ('global realization/gluing','{local records} ⇀ E_global','compatible local package family','global event package','paper-defined/partial','Local admissibility can coexist with a global obstruction.'),
 ],
 'P18':[
  ('marking/erasure','m: H → H_mark; e: H_mark → H','unmarked histories','marked/restored histories','paper-defined','Erasure need not recover recombination information lost by factorization.'),
  ('branch/recombination quotients','q_bw: H → K_bw; q_rec: H → R_rec','joint histories','branchwise and joint classes','paper-defined','Strict refinement is a witness of non-factorizable joint content.'),
 ],
 'P22':[
  ('channelized feasibility update','F: 2^X → 2^X','candidate legal set','one-step viable legal set','paper-defined','Persistence is relative to declared channels, controls, and budgets.'),
 ],
 'P23':[
  ('promotion/readout pair','π_old,π_new: C → Y_old,Y_new','fixed-support carrier','old/promoted records','paper-defined','Promotion criteria do not create a cross-carrier map.'),
  ('package survival update','T|_P: P → P','promoted package','next package state','paper-defined','Survival is internal invariance on one support.'),
 ],
 'P24':[
  ('branchwise/recombination maps','H → K_bw and H → R_rec','histories','branchwise/joint quotient','paper-defined','Control-stable anchors witness strictness; no token identity is selected.'),
 ],
 'P28':[
  ('theory-package morphism','f: T → T′','finite typed theory package','finite typed theory package','paper-defined','Must preserve typing, statuses, and designated audit/descent data.'),
  ('instrument','I: content → observed status/record','typed content','instrument-relative judgment','paper-defined','Admissibility and visibility are instrument-relative.'),
 ],
 'P29':[
  ('admissibility/completion maps','candidate record ⇀ admitted record','typed candidate','statused admissible object','paper-defined','Partiality and five-status discipline block silent promotion.'),
 ],
 'P30':[
  ('closure and quotient maps','E_τ: X → X; q_Q,q_M: H → Q,M','carrier/history','closed state and quotients','catalog law','Mostly layer-agnostic; each use must declare support.'),
  ('repair map','R: defective target → repaired target','defective package','statused repaired package','catalog law','Repair preserves the declared continuing members, not personal identity.'),
  ('bridge composition','B_st;B_tu ⇒ B_su','typed bridge chain','composite bridge','catalog law','Composition requires compatibility; route residue/holonomy can obstruct path independence.'),
  ('persistence relation','Rel ⊆ Obj_t × Obj_{t+1}','objects at adjacent stages','relation-valued successors','catalog law','F19 does not force function-valued identity.'),
 ],
 'P31':[
  ('induced dynamics','T_X → T_Y under lens/packaging','micro dynamics','macro/package dynamics','catalog law','Requires closure and admissibility; may be history-dependent.'),
  ('repair/maintenance update','R: package × ledger → package','current maintained package','reclosed package','catalog law','Autonomy must be tested after external support withdrawal.'),
 ],
 'P32':[
  ('E-system transition','F: X × U × L → X','state, endogenous control, ledger','next state','paper-defined','Endogenous closure is ledger- and environment-relative.'),
  ('repair compilation','repair specification → executable reclosure policy','declared defects','maintenance policy','paper-defined','Compilation does not prove consciousness or source lineage.'),
 ],
 'P33':[
  ('lens/refinement','π: X → Y; r: Y′ → Y','carrier and refined record','record and coarser record','toolkit-defined','No-smuggling and typed status are required.'),
  ('packaging/closure','E: X → X','carrier','packaged carrier state','toolkit-defined','Idempotence/defect is an objecthood audit, not ontology.'),
  ('causal bridge ports','B: Port_s ⇀ Port_t','typed source port','typed target port','toolkit-defined','Accounting and admissibility must be explicit.'),
 ],
 'P34':[
  ('coarse lens','π: X → Y','micro process','observed process','no-go setup','Data processing bounds observed arrow/complexity.'),
  ('schedule embedding','s: time index → protocol state','external schedule','staged process','no-go/control','Can manufacture apparent order or holonomy without endogenous arrow.'),
 ],
 'P35':[
  ('autonomous phase lift','Z=X×Φ; F_Z: Z → Z','base state plus phase','next lifted state','paper-defined','Separates internal protocol state from analyst scheduling.'),
  ('projection','p: Z → X','lifted process','base process','paper-defined','Projection can hide clock state; holonomy alone need not imply entropy production.'),
 ],
 'P39':[
  ('same-role event edges','R_role ⊆ E_i × E_j','protocol-indexed events','candidate same-role events','paper-defined','Accepted edges do not assemble into a global identity object.'),
  ('bridge law basis','B_role (missing)','carrier/event bridge records','composable event package law','named absent object','This missing subobject blocks the package candidate.'),
 ],
 'P42':[
  ('promotion bridge','B: L → U','lower problem/interface','promoted object/interface','paper-defined','Strict non-descent plus audited boundary use; not object identity.'),
  ('profile erasure','ε: detailed witness → profile skeleton','domain-specific witness','audited profile','paper-defined','Portability is at profile level; substrate erasure deliberately loses token identity.'),
  ('profile transfer plan','P_A → P_B','validated source profile','target profile obligations','paper-defined','Soundness transfers certificate fields, not the underlying object.'),
 ],
 'P44':[
  ('packaging','τ: X → Y','micro state','packaged state','paper-defined','Closure deficit measures predictive information lost relative to τ.'),
  ('route comparison','two conditional routes → mismatch scalar','micro and packaged update routes','audit value','paper-defined','Lower bound diagnoses noncommutation, not identity.'),
 ],
 'P45':[
  ('parameter-to-phase classifier','Θ → Phase','control/budget parameter grid','diagnostic phase label','paper-defined','Organizes experiment regimes; no phase is thereby conscious.'),
 ],
 'P50':[
  ('reduction relation','→ ⊆ X×X','rewrite object','rewrite successor','paper-defined','Paths, not only endpoints, are retained.'),
  ('filler/2-cell','p ⇒ q','parallel reduction paths','identified path pair','paper-defined','Elementary flatness corresponds to fillable critical pairs.'),
  ('normal-form map','nf: X → N','rewrite object','unique normal form','conditional','Exists canonically only under termination/normalization plus confluence.'),
 ],
 'P52':[
  ('lens','π: X → Y','finite substrate state','packaged observation','paper-defined','Deterministic and declared; no hidden read access.'),
  ('packaging endomap','E: Y → Y','packaged state','repackaged state','paper-defined','Idempotence defect audits objecthood.'),
  ('packaging-respecting morphism','f: S → S′','finite packaged machine','finite packaged machine','paper-defined','Must commute with declared packaging and interfaces.'),
  ('compiler','Compile: S → S_min/≈','finite semantics','canonical minimal machine class','paper-defined','Normal form is only up to packaging equivalence.'),
 ],
 'P53':[
  ('phase projection','φ: Z=X×Φ×R → Φ','world/phase/ledger state','clock phase','paper-defined','A clock is maintained, not a free external index.'),
  ('time-translation 1-form','a: route edges → increments','protocol route','local clock translation','paper-defined','Nonzero loop sum is temporal holonomy and blocks global synchronization.'),
 ],
 'P56':[
  ('currency','c: admissible paths → ℝ^k','protocol path','resource/accounting vector','paper-defined','Must be additive or composition-compatible and tied to feasibility.'),
  ('coarse-graining','π: X → Y','lower carrier','higher package','paper-defined','Lower currencies become constraints after packaging.'),
  ('dual/shadow-price map','budget/slack → λ','higher-layer constraint','marginal price vector','paper-defined','Proxy currencies can fail; duality is relative to declared optimization.'),
 ],
 'P57':[
  ('controlled kernel','P(x′|x,a)','state/action','successor distribution','paper-defined','Actions are ledger-gated; external schedule is not an action.'),
  ('viability operator','F: 2^X → 2^X','candidate safe set','states with feasible safe successor','paper-defined','Greatest fixed point defines maintained viability.'),
  ('action-output channel','A_H → Y_H','feasible action sequences','horizon-H outputs','paper-defined','Capacity is agency evidence, not consciousness.'),
  ('packaging endomap','E: Y → Y','coarse state','repackaged state','paper-defined','Repair can reduce idempotence defect.'),
 ],
 'P58':[
  ('cross-carrier closure identity','not structurally typed','closure profile on one carrier','closure profile on another','philosophical interpretation','The manuscript purchases this through A2; no transport/invariance theorem supplies the map.'),
 ],
 'P59':[
  ('bit lens','π: X → {0,1}^n','microstate','logical record','paper-defined','Metastability and retained-information audits are required.'),
  ('gate action','g: {0,1}^k → {0,1}^m','logical inputs','logical outputs','paper-defined','Functional preservation is only a subsystem audit.'),
 ],
 'P60':[
  ('profile erasure/transfer','detailed witness → SAU profile → target obligations','older SAU witness','profile-level transfer','older version','Retained only for version deltas; not independent support.'),
 ],
}

GENERALIZATIONS = {
 'P05':'Type source and target carriers separately; define a bridge preserving whichever C-clauses are claimed; prove composition and branch behavior; add withdrawal-based autonomy; keep certificate soundness and A1/A2 outside the structural theorem.',
 'P06':'Define a heterogeneous completion/reflection whose objects may change carrier type, prove a universal property for cross-carrier bridges, and show that completion does not silently import source internals or external maintenance.',
 'P08':'Replace fixed-support exactification with X_s/X_t-typed realization maps; prove target-native closure after bridge removal; separate public reduction from faithful package transport.',
 'P09':'Add a composable cross-carrier event law basis and a global package criterion; prove how local event records glue, and preserve explicit nonidentity under mere role matching.',
 'P14':'Retype route interfaces over distinct carriers, prove predictive transport is well-defined across heterogeneous histories, and state whether lineage is relation-, branch-, or function-valued under duplication.',
 'P18':'Define marking/erasure and recombination across changing supports; prove which joint-history information is invariant and how it composes through multiple handoffs.',
 'P23':'Generalize strict promotion/survival from invariant subsets of one carrier to a bridge between independently typed carrier dynamics.',
 'P24':'Give a heterogeneous recombination quotient and controls that distinguish preserved joint content from two independently rebuilt copies.',
 'P30':'Instantiate catalog laws with explicit X_s/X_t types and prove a cross-carrier persistence law; do not infer a unique identity token from relation-valued persistence.',
 'P50':'Model alternative migration orders as a reduction 2-complex; prove local generators cover all route differences and state termination/normalization assumptions before claiming route-independent endpoints.',
 'P53':'Define local clocks on source, bridge, and target; provide transport/translation data and flatness conditions; test continuity through gaps, rescaling, and bridge removal.',
 'P03':'Retype the accepted strict-test family on a target-native carrier and prove it is not merely inherited through an always-on source protocol.',
 'P16':'Specify how a surviving promoted package is transported rather than merely invariant on one support, including internal-state and history preservation.',
 'P39':'Construct the missing bridge-level law basis or prove its obstruction persists cross-carrier; accepted pairwise identity edges must not be promoted to a global continuer without composition.',
 'P04':'Choose consciousness-relevant probe spaces and a typed source-target comparison space; prove bridge-defect composition and relate thresholds to clause failure without making residual zero an identity claim.',
 'P32':'Define source withdrawal and target-environment retention; prove target reclosure is endogenous and that repair compilation does not hide a remote controller.',
 'P56':'Specify currencies and constraints for each C-clause on both carriers; prove budget translation and stability under bridge composition; separate resource sufficiency from lineage.',
 'P57':'Couple target viability/agency to the transferred package, define the handoff intervention, and prove post-handoff maintenance without equating empowerment with consciousness.',
 'P31':'Retype dynamical closure/repair laws across changing state spaces and prove stability under composition and approximation.',
 'P22':'Translate source legal/viable sets into target channels and prove legality persists under target-native dynamics after source removal.',
 'P13':'State exposure channels on both sides and prove hidden predictive structure is preserved without relying on inaccessible source variables; include expanded-interface and counterfeit controls.',
 'P12':'Identify a consciousness-relevant future test family and prove that target matching preserves predictive—not merely current—equivalence across histories.',
 'P44':'Define cross-carrier predictive distributions and a common comparison measure; prove how closure deficit and route mismatch compose and what threshold is meaningful.',
 'P02':'Define record-algebra equivalence across carriers while retaining context and route data; show which hidden global-state differences are intentionally ignored and which are continuity-critical.',
 'P34':'Lift no-go hypotheses to heterogeneous carriers and use them as kill criteria for snapshot-only, schedule-driven, or bounded-interface proposals.',
 'P35':'Embed the bridge protocol as an explicit state only when it remains target-endogenous; distinguish removable synchronization from permanent external scheduling.',
 'P17':'Define a cross-carrier cover and overlap/restriction system; prove local certificates glue or expose the exact obstruction to a global event package.',
 'P07':'Construct an explicit code/recovery analogue for a selected structural package, then test decoder removal and logical-identity branching; do not import QEC identity as consciousness identity.',
 'P52':'Add separately typed source/target machines and an explicit packaging equivalence; prove no-smuggling, composition, and which invariants survive compilation.',
 'P40':'Use only as a finite boundary/refinement toy after a transfer-relevant invariant has been chosen.',
 'P45':'Use as a parameter-search organization tool after candidate semantics are fixed; phase labels cannot determine continuity.',
 'P59':'Embed logic preservation as one subsystem check inside a broader package and lineage audit.',
 'P58':'No structural generalization can be obtained by restating A2. A formal cross-carrier invariance/transport theorem and an independent recognition bridge must be supplied before ontological use.',
}

EVIDENCE_OVERRIDE = {
 'P03':'Exact fixed-support construction and audit tables; layer-local PICA/exactification argument; no general cross-carrier theorem.',
 'P05':'Exact finite studies, selected Lean kernels, Python witnesses, and schema-level conditional logic; component witnesses live on separate declared carriers; no integrated C1–C8 instance.',
 'P06':'Category/reflection-style structural development with finite/asymptotic status ledgers; operational closure only.',
 'P07':'Deterministic exactly reproducible QEC simulation with preregistered predictions, failures, controls, and repairs; transport primitive explicitly untested.',
 'P08':'Fixed-support flagship construction with public-shadow, same-branch, and autonomous-lift controls; exactification is construction-specific.',
 'P09':'Fixed-support finite event-record construction with explicit thresholds and missing-package boundary.',
 'P12':'Exact-finite glass-model witnesses plus deterministic numeric artifacts; current/future split is exact on the declared class.',
 'P13':'Finite computational substrates, exact structural propositions, lift families, and exposure controls.',
 'P14':'Exact finite route package on one fixed support; quotient/factorization laws and explicit holonomy witness.',
 'P17':'Finite stable-record context with exact local/global gluing conditions and obstruction.',
 'P18':'Exact finite fixed-support marking/erasure/recombination witnesses and controls.',
 'P28':'Finite audited interaction calculus and theorem/status catalog; schema-level host restrictions.',
 'P30':'Layer-agnostic structural law catalog with finite witnesses and selected formal kernels; each law remains scope-relative.',
 'P32':'Finite endogenous-closure systems, repair/control laws, and maintenance ledgers.',
 'P33':'Finite emergence-calculus toolkit with definitions, theorem schemas, controls, and interoperability cautions.',
 'P35':'Minimal finite scheduled/autonomous/driven-clock countermodels.',
 'P39':'Fixed-support protocol-indexed event analysis; nine accepted same-role edges but a named missing bridge-level law basis.',
 'P42':'Newer Strict Audited Utility revision; exact finite/algebraic examples and profile-level transfer only.',
 'P50':'Exact finite rewriting/ARS studies plus local-confluence/flatness theorem core and completion examples.',
 'P52':'Finite-state semantics, realizability/compilation theorems, and no-smuggling separations.',
 'P53':'Finite Markov clock/ledger laboratory, exact audit outputs, and informal theorem-level synthesis with formal anchors.',
 'P56':'Finite Markov laboratories, path/cycle audits, constrained optimization duals, and proxy-failure controls.',
 'P57':'Finite controlled Markov kernels, exact viability fixed points, empowerment channels, packaging defects, and null controls.',
 'P58':'Philosophical synthesis and explicit assumption pricing; not structural evidence for A1 or A2.',
}

FORMAL_STATUS_OVERRIDE = {
 'P05':'Existing consciousness repository contains one Lean file, a Python package, 20 theorem-specific test modules, claim registries, and paper traceability ledgers. CST-EXP-01 inventories these separately; it does not treat their presence as an integrated-instance proof.',
 'P07':'Executable deterministic simulation and registered experiment artifacts are reported by the manuscript; this phase records the analogue and its failures, not a new run of the full QEC study.',
 'P12':'Manuscript reports exact-rational artifacts, deterministic numeric artifacts, and a Lean-checked core with a stated scope boundary.',
 'P14':'Manuscript reports exact finite witnesses and formal support for quotient/transport laws; cross-carrier typing is absent.',
 'P50':'Manuscript reports a Lean formal core and exhaustive finite ARS stress tests; the remaining scientific gap is coverage of migration-relevant generators.',
 'P52':'Finite semantics and theorem statements are directly reusable for later toy specifications; no toy is implemented in CST-EXP-01.',
 'P58':'No structural formalization imported as evidence; A1/A2 remain assumptions.',
}

ASSET_FAMILIES = [
 ('A-CT-01','Full C-package target','P05:C1–C8; clause cards','S-R;A;R','mixed/component-level','Defines the destination contract and its open integrated target.','No bridge, soundness theorem, or instance.'),
 ('A-PQ-01','Current/predictive quotient separation','P05,T1/T14; P12; P13; P14','S-L;S-T;R','finite, often fixed-support','Blocks snapshot/public-state matching from standing in for future-equivalent continuation.','Needs heterogeneous histories and target-relevant future tests.'),
 ('A-PQ-02','Reachable-image factorization / future sufficiency','P14; P30','S-L;S-T','fixed-support/catalog','Makes predictive transport well-defined on reachable histories.','No distinct-carrier factorization theorem.'),
 ('A-RT-01','Route continuation and predictive transport','P14','S-T;S-L','fixed-support','Provides identity/composition laws and transport on predictive quotients.','Carrier support is frozen; personal identity is not selected.'),
 ('A-HO-01','Route residue and holonomy','P14; P30; P35; P50; P53','S-T;S-L;M','finite/catalog','Detects path dependence and memory around loops.','Nonzero holonomy is a warning, not automatically failure or arrow.'),
 ('A-RE-01','Marking, erasure, branchwise and recombination quotients','P18; P24; P05 T7/T15','S-L;S-R','fixed-support','Tests whether joint content survives decomposition/reassembly.','Needs cross-carrier joint-history semantics.'),
 ('A-OP-01','Object Persistence / relation-valued identity','P30 F19; P05 T14','S-L','catalog/finite witness','Permits branch- and relation-valued continuation rather than forcing a function.','Does not establish personal/token identity.'),
 ('A-PR-01','Strict promotion and surviving packages','P23; P16; P03','S-R;S-T','fixed-support','Distinguishes a genuine new-layer package from re-description.','Promotion is not migration.'),
 ('A-EX-01','Carrier exactification and public-shadow controls','P08','S-R;S-T;R','fixed-support construction','Separates target-native internal carrier structure from public signature matching.','No heterogeneous carrier theorem.'),
 ('A-ST-01','Accepted new-layer strict tests','P03','S-R;R','fixed-support','Specifies destination-native tests unavailable in the old vocabulary.','No event package or shared identity object.'),
 ('A-EV-01','Carrier-to-event admissibility and bridge records','P09; P39','S-R;S-L;R','fixed-support','Binds carrier, instrument, visibility, role, thresholds, and audit.','Pairwise accepted edges do not compose into an event package.'),
 ('A-LG-01','Local/global event-package obstruction','P17; P30 F4','S-R;M','finite/catalog','Prevents local certificates from being silently promoted to a global package.','Requires a cross-carrier cover/gluing setup.'),
 ('A-AOR-01','Audited Operational Realisability completion/reflection','P06','S-R;M','schema/category','Organizes open obligations, repair, statuses, and universal completion.','Operational completion is not phenomenal realization or lineage.'),
 ('A-VI-01','Viability kernels and maintained legal sets','P05 C8/T1/T11; P22; P57','A;S-R','finite','Supplies a hard post-handoff survival gate.','Resource-supported persistence does not identify the continuer.'),
 ('A-CU-01','Currencies, constraints, dual prices, and ledgers','P56; P05 T11; P32','A;M','finite/schema','Prices maintenance, repair, clocking, and binding obligations.','Needs carrier-to-carrier budget translation.'),
 ('A-AG-01','Agenthood, agency, and withdrawal-sensitive autonomy','P57; P32','A;S-R','finite','Separates maintained package existence from causal action and external schedule.','No consciousness or source-lineage implication.'),
 ('A-TM-01','Temporal closure, local clocks, and no unified now','P05 C6/T8/T18; P53','A;S-L','finite','Makes handoff continuity a temporal/process claim rather than endpoint matching.','No canonical cross-carrier clock transport.'),
 ('A-HID-01','Exposure-relative hiddenness','P13; P05 C4/T2','R;S-R','finite','Distinguishes determining predictive state from exposed public shadow.','Hiddenness can dissolve under an expanded interface.'),
 ('A-NO-01','No-overreading and report descent','P05 T9; P30 F11/F12; P52','R;M','catalog/finite','Blocks inference from a report channel to unmeasured internal structure.','Does not prevent complete-state access by a stronger instrument.'),
 ('A-PT-01','Protocol/schedule trap','P35; P34; P33; P57','A;M','finite/no-go','Detects apparent drive, arrow, or continuity injected by external staging.','Need explicit withdrawal intervention and retained environment.'),
 ('A-CF-01','Critical pairs, flatness, confluence, and completion','P50; P30','S-T;S-L','finite/rewrite theorem','Tests whether multiple handoff orders produce path-independent packages.','Requires proof that critical pairs generate all relevant route differences.'),
 ('A-AR-01','Adequacy residual and blind-spot currency','P04','S-T;R;M','exact/defect-bounded','Quantifies destination distinctions absent from source probes and bridge defect.','Needs consciousness-specific probe families and stability thresholds.'),
 ('A-CD-01','Closure deficit and route mismatch lower bounds','P44','S-R;M','exact information-theoretic','Quantifies predictive nonclosure under packaging.','Zero deficit is sufficiency relative to a declared process, not identity.'),
 ('A-FS-01','Finite semantics, packaging equivalence, no-smuggling','P52; P33','M;S-T;S-R','finite','Provides exact toy grammar and implementation-comparison discipline.','Packaging equivalence alone is too weak for lineage.'),
 ('A-QEC-01','QEC logical-object engineering analogue','P07','S-R;A;M','simulation/engineering','Demonstrates recovery-supported higher-layer persistence amid physical noise/change.','Code/recovery are sharper than the consciousness certificate; analogy only.'),
 ('A-ON-01','A1/A2 and conditional realization boundary','P05 T17; P58','O;M','axiom-relative/philosophical','Makes ontological purchases explicit and separable.','A2 is not a transport theorem; certificate soundness and recognition remain open.'),
]

GAPS = [
 ('G01','No A2 carrier-invariance theorem','A-PQ-02;A-RT-01;A-ON-01','A2-P is philosophical; no H-XCI theorem; no implementation/substrate classifier','A heterogeneous carrier invariance/transport theorem with explicit bridge types and preserved predicates','theorem-sized + philosophical boundary','A countermodel with identical formal schema but different bridge-preservation verdicts.'),
 ('G02','No integrated full C1–C8 instance','A-CT-01;A-VI-01;A-TM-01;A-RE-01;A-HID-01','Cross-clause coherence and one carrier satisfying all full clauses; certificate soundness','A finite integrated package witness or an incompatibility/no-go theorem','model-sized + theorem-sized','Exhaustive finite search or proof shows required clauses cannot jointly hold under proposed bounds.'),
 ('G03','No cross-carrier lineage theorem','A-PQ-01;A-RT-01;A-OP-01','Separate source/target history types; bridge factorization; branch semantics','A relation-valued heterogeneous predictive-lineage theorem with composition and empty-target cases','theorem-sized','Two bridge-related targets satisfy endpoint invariants but predictive transport is ill-defined or noncompositional.'),
 ('G04','Fixed-support dominance','A-RT-01;A-RE-01;A-PR-01;A-EX-01;A-EV-01','All key constructions share one support; no X_s/X_t bridge','Retyped heterogeneous versions or a reduction showing when fixed-support models faithfully represent support change','theorem/model-sized','A relabeling passes the criterion despite no implementation change, or a true carrier change cannot be typed.'),
 ('G05','Matched public shadow is insufficient','A-HID-01;A-NO-01;A-PQ-01;A-EX-01;A-CD-01','Recognition bridge and declared future tests; hidden-state access discipline','A counterfeit-separation theorem or exact finite witness family','theorem/model-sized','Public-perfect copies with divergent predictive/viability/recombination behavior are classified as equivalent.'),
 ('G06','Duplication and symmetric-continuation ambiguity','A-OP-01;A-PQ-01;A-RE-01','No uniqueness-breaking premise; token identity not structurally defined','A symmetry/no-unique-continuer theorem or branch-valued classification law','theorem-sized','Criterion arbitrarily chooses one of two isomorphic, equally causally connected targets.'),
 ('G07','No empirical recognition bridge','A-CT-01;A-HID-01;A-AR-01;A-ON-01','Observable mapping from biological/engineered measurements to C-clause predicates','A preregistered recognition protocol with measurement error and falsification conditions','empirical','Candidate structural predicates cannot be estimated without unobservable complete state or analyst-only labels.'),
 ('G08','Incomplete protocol unification','A-EV-01;A-CF-01;A-TM-01;A-AG-01','Shared event law basis, clock translation, handoff/withdrawal contract, route coverage','A unified finite bridge record and composition law','model/theorem-sized','Pairwise bridge records pass but their composition has undefined role, time, or audit semantics.'),
 ('G09','Post-handoff autonomy not coupled to lineage','A-AG-01;A-VI-01;A-CU-01;A-PT-01','Withdrawal intervention, retained environment, horizon, source-disconnection proof','An autonomous-handoff theorem or explicit bridge-dependent classification','model/theorem-sized','Target fails immediately when decoder/source/bridge is removed, while proposal still calls it transferred.'),
 ('G10','No approximate/noisy stability theorem','A-AR-01;A-CD-01;A-QEC-01;A-VI-01','Metric/order on packages, defect budget, horizon, thresholds, composition law','A perturbation/stability theorem with error accumulation and viability margins','theorem-sized','Arbitrarily small local bridge error causes discontinuous lineage or viability failure.'),
 ('G11','No route-independent temporal synchronization','A-TM-01;A-HO-01;A-CF-01','Clock-translation connection and flatness/confluence assumptions','A local-to-global time-transport theorem or holonomy obstruction theorem','theorem-sized','Two allowed replacement orders yield different target phase/continuation coordinates.'),
 ('G12','No ordering between full package and simplified certificate','A-CT-01;A-ON-01','Missing implication in both directions','A comparison theorem, counterexamples, or explicit incomparability result','theorem/model-sized','Finite models satisfy one schema but not the other in both directions.'),
 ('G13','Carrier versus substrate/medium not independently classified','A-FS-01;A-ON-01','Implementation maps and medium equivalence/distinctness criterion','A typed realization layer below formal carriers','model/philosophical','Same implementation is relabeled as a new substrate or different media collapse to one unexamined carrier label.'),
 ('G14','Object persistence does not select personal identity','A-OP-01;A-ON-01','A personal-identity interpretation premise or a purely structural replacement for it','A demarcation theorem stating exactly what structural lineage does and does not entail','theorem + philosophical','Structurally identical lineage relations support incompatible personal-identity verdicts.'),
]

THEOREM_CARD_DATA = {
 'T01':('Exact forcing and minimal restoration; T1','P05-S008','P05','S-R;A','Exact finite twelve-state deadline carrier; target viability restored by a unique minimal predictive refinement.','Forces a self-coordinate only on the declared carrier and policy class; not cross-carrier or ontological.'),
 'T02':('Interface-relative non-exposure; T2','P05-S009','P05','R;S-R','Connector loop moves the predictive quotient while fixing the current quotient; dissolution control expands the interface.','Hiddenness is channel-relative and can disappear.'),
 'T03':('No-shortcut / nonfactorization corollary; T3','P05-S010','P05','S-R;R','Strict promoted content does not factor through the declared lower interface; a factoring control is supplied.','Fixed-interface nonfactorization is not a universal explanatory gap or a cross-carrier transport theorem.'),
 'T04':('Public duplicate and certificate contrast; T4a/T4b','P05-S012;P05-S013','P05','R;S-R','Public-equivalent states can remain distinct under a declared certificate battery, with a public discernibility control.','The battery is interface-relative and the full certificate/soundness theorem remains open.'),
 'T05':('Priced residue and audited action credit; T5','P05-S014','P05','A;S-R','Finite provenance ledgers distinguish self-, other-, and none-credited action under bounded audits.','No metaphysical freedom claim and no cross-carrier authorship theorem.'),
 'T06':('Same-level audit failure and rotating towers; T6','P05-S015','P05','R;M','Finite self-audit limits and rotating higher-level checks.','Does not establish absolute unknowability or privileged introspection.'),
 'T09':('Report descent and no-overreading; T9','P05-S011','P05','R;M','Reports license only descended boundary content; a noninjective report and stronger no-report interface witness the boundary.','No absolute unknowability and no inference from reports to unmeasured internal structure.'),
 'T10':('Existence boundary schema; T10','P05-S023','P05','S-R;M','Finite maintenance sweeps separate parameter regions in which the declared package proxy appears or fails.','A toy boundary is not a universal consciousness phase transition or a cross-carrier criterion.'),
 'T11':('Exact dual prices and funded viability; T11','P05-S019;P05-S020','P05','A;S-R;M','Exact finite LP dual prices expose binding maintenance constraints; the valence interpretation is recognition-grade only.','Shadow prices and viability do not establish lineage, consciousness, or personal survival.'),
 'T12':('Induced-kernel similarity geometry; T12','P05-S021','P05','S-R;R','A declared lens induces comparison geometry with exact finite separation and defect controls.','No phenomenal-quality identification or carrier-invariant quality transport follows.'),
 'T16':('Meta-problem composition; T16','P05-S016','P05','M;O','A declared completion convention composes certified flags into a hard-problem report, with a control convention.','The result is convention-relative and does not independently realize or recognize consciousness.'),
 'T07':('Binding witness with marking and erasure; T7','P05-S017','P05','S-R;S-L','Strict recombination refinement with marking-collapse and erasure controls.','Component witness only; no phenomenal-unity theorem.'),
 'T08':('Purchased clock and no unified now; T8','P05-S018','P05','A;S-L','Funded phase/clock trace and route-holonomy contrast.','No canonical cross-carrier “now” transport.'),
 'T13':('Descent-fixing gauge and rigidification; T13','P05-S022','P05','S-R;S-T','Quality-comparison gauge shrinks after declared descents/rigidifier.','Does not identify phenomenal qualities or transport them across carriers.'),
 'T14':('Lineage, trauma, fission/fusion, empty target; T14','P05-S024','P05','S-L','Predictive lineage on a declared route; future-sufficient summaries factor to M; fiber splitting/merging models fission/fusion; underfunded empty target.','Finite declared-route machinery, not a complete metaphysics or cross-carrier personal-identity theorem.'),
 'T15':('Combination gate; T15','P05-S025','P05','S-R;S-L','One joint carrier satisfies strict recombination plus joint reflexive refinement; aggregation control removes the forced coordinate.','No general combination theorem, no cross-carrier fusion rule, and no source-target lineage theorem.'),
 'T17':('T17 realization umbrella and conditional bridge','P05-M003;P05-S026;P05-S027;P05-S028','P05','O;S-R;M','Seven separately graded objects; T17-O composes assumed certificate soundness with A1; A2 has no theorem; integrated instance absent.','No package is unconditionally certified or realized; no A2 transport/invariance theorem.'),
 'T18':('Temporal consequence cluster; T18','P05-M002','P05','A;S-L','Cluster linking strictness, closure defects, entrainment, and transport counts on declared finite carriers.','Cluster constants do not supply a general cross-carrier temporal continuity theorem.'),
 'P14-PT':('Predictive transport and reachable-image factorization','P14 formal statements','P14','S-T;S-L','Route continuation descends to predictive quotient under future-sufficiency; reachable-image factorization and loop asymmetry are explicit.','Fixed support; endpoint token identity is not implied.'),
 'P18-RE':('Recombination refinement laws','P18 formal statements','P18','S-L;S-R','Detectability, quotient-lift sufficiency, no-interference factorization, and strict-refinement obstruction.','Fixed support and declared branch family.'),
 'P06-AOR':('AOR closure-completion reflection','P06-S006;P06-S009;P06-S010','P06','S-R;M','Canonical completion from PreSB records to AOR with universal property/adjunction.','Operational status only; carrier-changing completion not supplied.'),
 'P30-F19':('Object Persistence law F19','P30 source law','P30','S-L','Persistence is organized as a typed relation across stages, compatible with branch/fusion cases rather than a forced bijection.','Layer-agnostic structural law; not personal identity.'),
 'P50-CF':('Elementary flatness iff local confluence; completion eliminates holonomy','P50 formal statements','P50','S-T;S-L','Critical pairs generate elementary curvature; flatness/local confluence equivalence and completion examples.','Global unique normal form also needs normalization/termination and generator coverage.'),
 'P52-NS':('Finite compilation and no-smuggling separations','P52-S020;P52-S021','P52','M;S-T;S-R','Finite semantics compile to a canonical machine class up to packaging equivalence; separations prevent analyst-only information from entering.','Packaging equivalence is not lineage or consciousness.'),
 'P44-CD':('Closure deficit decomposition and vanishing criterion','P44-S001..S006','P44','S-R;M','Exact decomposition, KL form, closure/sufficiency equivalence, and route mismatch lower bound.','Relative to declared process and packaging; zero deficit is not identity.'),
}


def compact_ws(s: str) -> str:
    return re.sub(r'\s+', ' ', s).strip()

def md_escape(s: str) -> str:
    return s.replace('|','\\|').replace('\n',' ')

def shorten(s: str, n: int=420) -> str:
    s=compact_ws(s)
    return s if len(s)<=n else s[:n-1].rstrip()+'…'

def clean_tex(s: str) -> str:
    s=re.sub(r'(?m)%.*$','',s)
    s=s.replace('\\\\',' — ')
    s=re.sub(r'\\begin\{[^}]+\}|\\end\{[^}]+\}',' ',s)
    s=re.sub(r'\\item(?:\[[^]]*\])?',' • ',s)
    for _ in range(6):
        ns=re.sub(r'\\[A-Za-z@]+\*?(?:\[[^]]*\])?\{([^{}]*)\}',r'\1',s)
        if ns==s: break
        s=ns
    s=re.sub(r'\\[A-Za-z@]+\*?',' ',s)
    s=s.replace('{','').replace('}','').replace('$','`').replace('~',' ')
    return compact_ws(s)

def source_excerpt(path: Path, lo: int, hi: int) -> str:
    lines=path.read_text(errors='replace').splitlines()
    lo=max(1,lo); hi=min(len(lines),hi)
    return clean_tex('\n'.join(lines[lo-1:hi]))

def detect_abstract_lines(path: Path):
    text=path.read_text(errors='replace')
    m=re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}',text,re.S)
    if not m: return (1,min(30,text.count('\n')+1))
    return (text.count('\n',0,m.start())+1,text.count('\n',0,m.end())+1)

def infer_evidence(p: dict) -> str:
    if p['paper_id'] in EVIDENCE_OVERRIDE: return EVIDENCE_OVERRIDE[p['paper_id']]
    a=(p.get('abstract') or '').lower()
    bits=[]
    if 'exact finite' in a or 'exact-finite' in a: bits.append('exact finite')
    if 'simulation' in a or 'computational' in a: bits.append('computational')
    if 'lean' in a or 'machine-checked' in a: bits.append('formal anchor reported')
    if 'finite' in a and 'exact finite' not in a: bits.append('finite')
    if not bits: bits.append('paper-local structural or application analysis')
    return ', '.join(dict.fromkeys(bits)).capitalize()+'. Imported only at its declared scope.'

def support_scope(pid: str, p: dict) -> tuple[str,str]:
    if pid in FIXED_SUPPORT:
        return ('yes','One declared fixed support/carrier; any apparent interface change remains internal to that support.')
    if pid=='P05': return ('mixed','Full target is carrier-indexed; landed component witnesses are on separate declared finite carriers; T17 is parametric but not a transport theorem.')
    if pid in {'P30','P31','P33','P34'}: return ('mixed/schema','Layer-agnostic or typed schema instantiated only after a support and interfaces are declared.')
    if pid in {'P58'}: return ('not structural','Cross-carrier reading is philosophical and purchased by A2, not supplied by a support-typed theorem.')
    if pid in {'P42','P60'}: return ('case-relative','Promotion bridges compare layers/domains; profile portability does not preserve object identity.')
    if pid in {'P07'}: return ('physical support changes inside one QEC experiment class','Logical object is recovered over noisy physical configurations; explicit transport primitive is not tested.')
    return ('no explicit cross-carrier theorem','Uses a declared finite/application carrier or schema; distinct source/target carrier typing is absent unless stated in the selected source passage.')

def phase_role(pid: str, p: dict) -> str:
    if pid in QUARANTINED: return 'quarantined metadata/exclusion card only'
    if pid=='P42': return 'version-reconciled normative SAU line'
    if pid=='P60': return 'superseded SAU revision; delta/provenance only'
    if pid in WAVE_OF: return f'primary dependency-order read, wave {WAVE_OF[pid]}'
    if p['verdict']=='Supporting': return 'supporting-on-demand'
    if p['verdict']=='Peripheral': return 'peripheral diagnostic/control'
    if p['verdict']=='Not selected': return 'explicit non-primary/excluded from working core'
    return 'supplementary'

def version_status(pid: str) -> str:
    if pid=='P42': return 'normative-newer-revision'
    if pid=='P60': return 'superseded-older-revision-no-independent-weight'
    if pid=='P46': return 'quarantined'
    return 'standalone-corpus-item'

def select_statements(pid: str, p: dict, statements: list[dict]) -> list[dict]:
    arr=[s for s in statements if s['paper_id']==pid]
    if pid in QUARANTINED: return []
    target = 12 if p['verdict']=='Essential' else 9 if p['verdict']=='High' else 5 if p['verdict']=='Supporting' else 3
    if pid in {'P42'}: target=14
    if pid in {'P60'}: target=5
    selected=[]; used=set()
    prefs=[x.lower() for x in PREFERRED.get(pid,[])]
    for pref in prefs:
        matches=[s for s in arr if pref in (s['name']+' '+s['label']).lower()]
        for s in sorted(matches,key=lambda z:(-z['relevance_score'],z['line_start'])):
            if s['statement_id'] not in used:
                selected.append(s);used.add(s['statement_id']);break
    # Favor relevant definitions/theorems, then score.
    for s in sorted(arr,key=lambda z:(-z['relevance_score'], 0 if z['kind'] in {'theorem','proposition','corollary','definition','postulate','nonclaim'} else 1, z['line_start'])):
        if len(selected)>=target: break
        if s['statement_id'] in used: continue
        selected.append(s);used.add(s['statement_id'])
    return sorted(selected,key=lambda z:z['line_start'])

def claim_lanes(tags: str, pid: str='') -> str:
    out=[]
    for t in (tags or '').split(';'):
        for lane in CLAIM_TAGS_BY_ASSET.get(t, '').split(';'):
            if lane and lane not in out: out.append(lane)
    if pid=='P58' and 'O' not in out: out.append('O')
    if not out: out=['M']
    return ';'.join(out)

def infer_formal_status(pid: str, p: dict, source_text: str) -> str:
    if pid in FORMAL_STATUS_OVERRIDE: return FORMAL_STATUS_OVERRIDE[pid]
    bits=[]
    lo=source_text.lower()
    if 'lean' in lo: bits.append('Lean/formal anchor reported in source')
    if 'python' in lo or 'code' in lo or 'repository' in lo: bits.append('code or executable artifact reported')
    if 'exact finite' in lo or 'exact-finite' in lo: bits.append('exact-finite witness regime')
    if not bits: bits.append('TeX theorem/prose asset only in this archive')
    return '; '.join(bits)+'. CST-EXP-01 indexes claims but does not re-prove them.'

def cross_generalization(pid: str, p: dict) -> str:
    if pid in GENERALIZATIONS: return GENERALIZATIONS[pid]
    if pid in FIXED_SUPPORT:
        return 'Introduce separately typed source and target carriers, an explicit bridge, preserved invariants, composition/identity laws, and a bridge-removal autonomy test.'
    if p['verdict']=='Not selected':
        return 'No project-facing generalization is presently justified; retain only the named methodological control unless a later live subproblem reopens it.'
    if p['verdict']=='Peripheral':
        return 'Use only as a diagnostic/control pattern after a transfer-relevant object is declared; do not promote application-specific quantities into continuity criteria.'
    return 'Retype any reused object against explicit source/target carriers and state what the paper-local result does not preserve; no cross-carrier implication is inherited automatically.'

def control_summary(pid: str, p: dict) -> str:
    use=(p.get('triage_use') or '').lower()
    controls=[]
    for key,label in [
      ('control','matched/zero/ablation controls'),('shadow','public-shadow control'),('failure','registered failure modes'),
      ('nonclaim','explicit nonclaim boundary'),('holonomy','route/holonomy contrast'),('erasure','marking/erasure control'),
      ('empty','empty-target or collapse case'),('protocol trap','schedule/protocol trap'),('no-overreading','no-overreading control'),
      ('counter','counterexample/control')]:
        if key in use and label not in controls: controls.append(label)
    if not controls: controls.append('Use the paper-specific negative result or boundary as a control; no positive transfer inference is licensed.')
    return '; '.join(controls)

def primitive_summary(selected: list[dict], manual: list[dict]) -> list[str]:
    defs=[s['name'] for s in selected if s.get('kind') in {'definition','construction','schema','postulate'} and s.get('name')]
    names=[]
    for x in defs:
        if x not in names: names.append(x)
    for x in manual:
        if len(names)>=8: break
        names.append(x.get('name') or x.get('statement_name') or 'source passage')
    return names[:10] or ['No project-facing primitive imported; card retained for explicit coverage and boundary control.']

def write_csv(path: Path, fields: list[str], rows: list[dict]):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('w',newline='',encoding='utf-8') as fh:
        w=csv.DictWriter(fh,fieldnames=fields,extrasaction='ignore');w.writeheader();w.writerows(rows)

def write_text(path: Path, text: str):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text.rstrip()+'\n',encoding='utf-8')

def inventory_consciousness(con_dir: Path, repo: Path):
    rows=[]
    for f in sorted(x for x in con_dir.rglob('*') if x.is_file() and '.git/' not in x.as_posix()):
        rel=f.relative_to(con_dir).as_posix();ext=f.suffix.lower()
        if rel.startswith('lean/') or ext=='.lean': cat='formalization'
        elif rel.startswith('lab/tests/'): cat='python-test'
        elif rel.startswith('lab/'): cat='python-toy'
        elif rel.startswith('paper/sections/') or rel.startswith('paper/appendices/'): cat='paper-source'
        elif rel.startswith('paper/prewriting/'): cat='traceability-ledger'
        elif rel.startswith('formalization/'): cat='formalization-metadata'
        elif rel.startswith('papers/'): cat='embedded-paper-copy'
        elif rel.startswith('review_requests/'): cat='review-history'
        elif rel.startswith('design/'): cat='design-history'
        else: cat='other'
        rows.append({'path':rel,'category':cat,'extension':ext,'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
    write_csv(repo/'corpus/consciousness_repo/consciousness_repo_inventory.csv',['path','category','extension','bytes','sha256'],rows)
    counts=Counter(r['category'] for r in rows)
    tests=[r for r in rows if r['category']=='python-test']
    formal=[r for r in rows if r['category'] in {'formalization','formalization-metadata'}]
    md=f"""# Consciousness repository asset map

This inventory treats the attached consciousness repository as an evidence and traceability surface, not as proof of an integrated C1–C8 instance.

## Counts

| Category | Files |
|---|---:|
"""+''.join(f"| {k} | {counts[k]} |\n" for k in sorted(counts))+f"""

Total inventoried files: **{len(rows)}**. Python test modules: **{len(tests)}**. Formalization/formalization-metadata files: **{len(formal)}**.

## High-value surfaces

- `paper/sections/sec_03_closure_architecture.tex`: full C-package contract and clause boundaries.
- `paper/sections/sec_05_consequence_clusters.tex`: T14/T15 and other structural consequence clusters.
- `paper/sections/sec_06_conditional_realization.tex`: T17, A1/A2, certificate-soundness price, and absent integrated instance.
- `lean/SixBirdsConsciousness.lean`: the repository's declared formal kernel; its carrier polymorphism is not evidence for A2.
- `formalization/inventory/t17_claim_registry.yml`: seven-way T17 grading/registry.
- `lab/sixbirds_consciousness/`: finite witness utilities.
- `lab/tests/`: theorem-specific executable checks, including T14, T15, T17, and T18.
- `paper/prewriting/lean_declaration_map.csv`, `lean_traceability.md`, and claim/evidence ledgers: provenance surfaces.

## Critical boundary

The repository contains component witnesses, tests, and formal declarations, but its own manuscript states that no full integrated C1–C8 instance and no proved certificate-soundness theorem are landed. File presence and test success cannot upgrade that status.
"""
    write_text(repo/'corpus/consciousness_repo/ASSET_MAP.md',md)
    # Test/formal concise inventories.
    write_csv(repo/'corpus/consciousness_repo/test_inventory.csv',['path','bytes','sha256'],tests)
    write_csv(repo/'corpus/consciousness_repo/formal_inventory.csv',['path','category','bytes','sha256'],formal)
    return rows

def duplicate_map(papers: list[dict], papers_dir: Path, con_dir: Path, repo: Path):
    byhash={p['sha256']:p for p in papers}
    rows=[]
    for f in sorted((con_dir/'papers').rglob('*.tex')) if (con_dir/'papers').exists() else []:
        h=hashlib.sha256(f.read_bytes()).hexdigest()
        match=byhash.get(h)
        rows.append({'consciousness_repo_path':f.relative_to(con_dir).as_posix(),'sha256':h,'top_level_paper_id':match['paper_id'] if match else '', 'byte_identical':bool(match),'handling':'duplicate-evidence-not-double-counted' if match else 'embedded-only'})
    write_csv(repo/'ledgers/corpus_duplicate_map.csv',['consciousness_repo_path','sha256','top_level_paper_id','byte_identical','handling'],rows)
    return rows

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--papers-dir',type=Path,required=True)
    ap.add_argument('--consciousness-dir',type=Path,required=True)
    ap.add_argument('--parsed-dir',type=Path,required=True)
    ap.add_argument('--source-zip',type=Path,required=False)
    args=ap.parse_args();repo=args.repo
    papers=json.loads((args.parsed_dir/'papers.json').read_text())
    statements=json.loads((args.parsed_dir/'statements.json').read_text())
    pby={p['paper_id']:p for p in papers}; sby={s['statement_id']:s for s in statements}
    source_by_pid={p['paper_id']:args.papers_dir/p['filename'] for p in papers}

    # Output directories.
    for d in ['corpus/paper_cards','corpus/clause_cards','corpus/theorem_cards','corpus/asset_atlas','corpus/machine_index','corpus/consciousness_repo']:
        (repo/d).mkdir(parents=True,exist_ok=True)

    # Full machine index, with P46 content fail-closed.
    inv_rows=[]
    for p in papers:
        inv_rows.append({**{k:p.get(k,'') for k in ['paper_id','index','filename','embedded_title','triage_title','verdict','useful','sha256','bytes','lines','statement_count']},'phase_role':phase_role(p['paper_id'],p),'version_status':version_status(p['paper_id']),'quarantine':p['paper_id'] in QUARANTINED})
    write_csv(repo/'corpus/machine_index/paper_inventory.csv',list(inv_rows[0].keys()),inv_rows)
    full_fields=['statement_id','paper_id','paper_title','filename','kind','name','label','line_start','line_end','tags','relevance_score','compact','version_status']
    full_rows=[]
    for s in statements:
        if s['paper_id']=='P46':
            continue
        r={k:s.get(k,'') for k in full_fields};r['version_status']=version_status(s['paper_id']);full_rows.append(r)
    write_csv(repo/'corpus/machine_index/all_statement_index.csv',full_fields,full_rows)
    write_text(repo/'corpus/machine_index/README.md',f"""# Machine corpus index

- Paper inventory: 60 top-level manuscripts.
- Extracted theorem-like environments: {len(statements)} total in the source archive.
- Indexed statement rows in `all_statement_index.csv`: {len(full_rows)}.
- P46's {pby['P46']['statement_count']} theorem-like environments are deliberately omitted from statement content because the paper is quarantined; its metadata card and exclusion log remain.
- P42 and P60 are both indexed for version comparison but carry one evidence line; P42 is normative and P60 has no independent evidential weight.

The extraction is lexical and provenance-oriented. It does not validate TeX, proofs, theorem truth, or semantic equivalence across manuscript versions.
""")

    # Curated statement provenance and paper cards.
    provenance=[]; paper_assumptions=[]
    card_index=[]
    for p in papers:
        pid=p['paper_id']; src=source_by_pid[pid]; source_text=src.read_text(errors='replace')
        selected=select_statements(pid,p,statements)
        manual=[]
        if pid in MANUAL_PASSAGES and pid not in QUARANTINED:
            for j,(name,lo,hi,lanes,tags) in enumerate(MANUAL_PASSAGES[pid],1):
                manual.append({'statement_id':f'{pid}-M{j:03d}','paper_id':pid,'kind':'source-passage','name':name,'label':'','line_start':lo,'line_end':hi,'compact':source_excerpt(src,lo,hi),'tags':tags,'relevance_score':0,'filename':p['filename'],'paper_title':p['embedded_title']})
        if not selected and not manual and pid not in QUARANTINED:
            lo,hi=detect_abstract_lines(src)
            manual=[{'statement_id':f'{pid}-M001','paper_id':pid,'kind':'abstract-scope','name':'Abstract-level project relevance and boundary','label':'','line_start':lo,'line_end':hi,'compact':source_excerpt(src,lo,hi),'tags':'audit;record','relevance_score':0,'filename':p['filename'],'paper_title':p['embedded_title']}]
        curated=selected+manual
        fixed_flag,carrier_note=support_scope(pid,p)
        formal=infer_formal_status(pid,p,source_text)
        ver=version_status(pid)
        for s in curated:
            provenance.append({
              'record_id':f"PR-{len(provenance)+1:04d}",'statement_id':s['statement_id'],'paper_id':pid,
              'canonical_title':p['triage_title'],'source_file':p['filename'],'source_sha256':p['sha256'],
              'source_lines':f"{s['line_start']}-{s['line_end']}",'source_label':s.get('label',''),
              'statement_kind':s['kind'],'statement_name':s.get('name',''),'compact_statement':shorten(s.get('compact',''),650),
              'claim_lanes':claim_lanes(s.get('tags',''),pid),'asset_tags':s.get('tags',''),
              'evidence_regime':infer_evidence(p),'fixed_support':fixed_flag,'carrier_scope':carrier_note,
              'interface_relative':'yes unless the source statement explicitly declares otherwise',
              'imported_assumptions':'paper-local declared carrier, lens/instrument, protocol, thresholds, and status discipline',
              'formalization_status':formal,'selection_status':'curated-transfer-relevant','version_status':ver,
              'nonclaim_or_limit':p['triage_boundary'],'notes':'Inventory selection, not project target selection.'
            })
        if pid in QUARANTINED:
            provenance.append({
              'record_id':f"PR-{len(provenance)+1:04d}",'statement_id':f'{pid}-EXCLUSION','paper_id':pid,
              'canonical_title':p['triage_title'],'source_file':p['filename'],'source_sha256':p['sha256'],'source_lines':'metadata only',
              'source_label':'','statement_kind':'quarantine-record','statement_name':'Owner-inherited exclusion; no statement content imported',
              'compact_statement':'Paper retained only so it is not silently skipped. No theorem, definition, or engineering pattern from this source is imported in CST-EXP-01.',
              'claim_lanes':'M','asset_tags':'quarantine;exclusion','evidence_regime':'not read for substantive extraction',
              'fixed_support':'not assessed','carrier_scope':'quarantined','interface_relative':'not assessed','imported_assumptions':'none',
              'formalization_status':'not assessed','selection_status':'excluded','version_status':'quarantined',
              'nonclaim_or_limit':'No substantive use unless the owner explicitly revokes the exclusion.','notes':'Satisfies no-silent-skip rule without contaminating the asset bank.'
            })
        paper_assumptions.append({
          'record_id':f'SC-{pid}','paper_id':pid,'asset_id':'paper-level','title':p['triage_title'],
          'support_scope':carrier_note,'fixed_support_flag':fixed_flag,'carrier_relation':'no source-target carrier relation is inherited by default',
          'finite_or_schema':infer_evidence(p),'interface_relative':'yes/mixed; see card','route_declared':'only where paper explicitly defines routes/protocols',
          'composition_status':'see card; absent is not inferred','identity_status':'no personal-identity implication',
          'autonomy_status':'requires an explicit withdrawal test; not inherited','imported_assumptions':'declared paper-local carrier, interfaces, protocols, thresholds, and evidence grade',
          'retyping_needed':cross_generalization(pid,p),'source_lines':'see curated provenance','notes':phase_role(pid,p)
        })

        primitives=primitive_summary(selected,manual)
        maps=MAPS.get(pid,[])
        # If no map is imported, state that explicitly.
        map_md='| Object/map | Type | Source | Target | Imported status | Cross-carrier caution |\n|---|---|---|---|---|---|\n'
        if maps:
            for obj,typ,so,ta,st,ca in maps:
                map_md+=f'| {md_escape(obj)} | `{md_escape(typ)}` | {md_escape(so)} | {md_escape(ta)} | {md_escape(st)} | {md_escape(ca)} |\n'
        else:
            map_md+='| None imported as a transfer map | — | — | — | explicit negative record | Any maps in the paper remain application-local until a later live subproblem types them against X_s and X_t. |\n'
        stmt_md='| ID | Kind | Name | Source | Compact statement / role |\n|---|---|---|---|---|\n'
        if pid in QUARANTINED:
            stmt_md+='| P46-EXCLUSION | quarantine record | no content imported | metadata only | Owner-inherited exclusion retained. |\n'
        else:
            for s in curated:
                stmt_md+=f"| {s['statement_id']} | {md_escape(s['kind'])} | {md_escape(s.get('name','') or 'unnamed')} | `{p['filename']}:{s['line_start']}-{s['line_end']}` | {md_escape(shorten(s.get('compact',''),330))} |\n"
        status=phase_role(pid,p)
        lanes=[]
        for s in curated:
            for lane in claim_lanes(s.get('tags',''),pid).split(';'):
                if lane and lane not in lanes:lanes.append(lane)
        if not lanes:lanes=['M']
        card=f"""# {pid} — {p['triage_title']}

> **Corpus verdict:** {p['verdict']}  
> **Phase role:** {status}  
> **Claim lanes touched:** {', '.join(lanes)}  
> **Version handling:** {ver}

## Source identity

| Field | Value |
|---|---|
| Corpus ID | `{pid}` |
| Source file | `{p['filename']}` |
| Embedded title | {p['embedded_title'] or '(title macro did not resolve lexically)'} |
| SHA-256 | `{p['sha256']}` |
| Source size | {p['bytes']} bytes; {p['lines']} lines |
| Theorem-like environments lexically indexed | {p['statement_count']} |
| Dependency-order wave | {WAVE_OF.get(pid,'not in primary waves')} |

## Evidence and scope

- **Evidence regime:** {infer_evidence(p)}
- **Fixed-support flag:** **{fixed_flag}**.
- **Carrier/support reading:** {carrier_note}
- **Interface dependence:** all imported claims remain relative to their declared lenses, instruments, protocols, histories, budgets, and thresholds unless the source explicitly proves invariance.
- **Result form:** exact, finite, asymptotic, computational, or schema status is preserved statement by statement in the provenance ledger; no status upgrade is made here.

## Transfer-relevant primitives and definitions

"""+'\n'.join(f'- **{x}**' for x in primitives)+f"""

## Curated statements

{stmt_md}
{('P46 is deliberately absent from the machine statement bank; only its source metadata and exclusion record are retained.' if pid in QUARANTINED else 'The complete lexical index is in `../machine_index/all_statement_index.csv`; curation is for navigation and does not erase unselected source statements.')}

## Typed map ledger

{map_md}
## Assumptions and dependencies

- The paper-local carrier, lens/instrument family, admissible protocols, thresholds, and status discipline are imported whenever one of its assets is cited.
- Fixed-support or same-carrier hypotheses are never silently reinterpreted as distinct-carrier transport.
- Any claim involving public records is kept separate from predictive state, package realization, lineage, autonomy, recognition, and ontology.
- Formal or executable assets are evidence only for the exact statement they implement; they do not establish a stronger cross-carrier claim.

## Composition, identity, and route status

- **Composition:** {('addressed only for the paper-defined maps/routes; heterogeneous composition remains open' if any(k in (p.get('triage_use','')+p.get('abstract','')).lower() for k in ['composition','morphism','route','holonomy','confluence']) else 'not a landed project-facing result; must be supplied if this asset is used in a bridge chain')}.
- **Identity:** no selected statement is read as personal or token identity unless a later candidate adds and prices that interpretation. Relation-, profile-, event-, record-, or quotient-equivalence remain typed as such.
- **Route dependence:** {('material and must be preserved in later use' if any(k in (p.get('triage_use','')+p.get('abstract','')).lower() for k in ['route','holonomy','protocol']) else 'not resolved by this paper for cross-carrier use')}.
- **Autonomy:** bridge-supported or scheduled behavior is not target autonomy without the phase-00 withdrawal contract.

## Reusable witnesses, controls, and failure modes

{('None imported; the quarantine record itself is the only control.' if pid in QUARANTINED else control_summary(pid,p))}

## Formalization and toy status

{('Not assessed or imported under the active quarantine.' if pid in QUARANTINED else formal)}

## Likely contribution to CST exploration

{TRIAGE_USE_OVERRIDE.get(pid,p['triage_use'])}

## Explicit boundary / what it cannot establish

{TRIAGE_BOUNDARY_OVERRIDE.get(pid,p['triage_boundary'])}

## Distinct-carrier generalization required

{cross_generalization(pid,p)}

## Phase disposition

This card contributes source-traceable assets and boundaries only. It neither selects a transported object nor endorses a transfer, survival, identity, recognition, or ontological verdict.
"""
        write_text(repo/f'corpus/paper_cards/{pid}.md',card)
        card_index.append({'paper_id':pid,'title':p['triage_title'],'verdict':p['verdict'],'phase_role':status,'fixed_support':fixed_flag,'curated_records':len(curated) if pid not in QUARANTINED else 1,'card':f'corpus/paper_cards/{pid}.md'})

    prov_fields=list(provenance[0].keys())
    write_csv(repo/'ledgers/statement_provenance.csv',prov_fields,provenance)
    write_csv(repo/'ledgers/support_and_carrier_assumptions.csv',list(paper_assumptions[0].keys()),paper_assumptions)
    write_csv(repo/'corpus/paper_cards/INDEX.csv',list(card_index[0].keys()),card_index)
    idx_md='# Paper-card index\n\n| ID | Title | Verdict | Phase role | Fixed support | Curated records |\n|---|---|---|---|---|---:|\n'
    for r in card_index: idx_md+=f"| [{r['paper_id']}]({r['paper_id']}.md) | {md_escape(r['title'])} | {r['verdict']} | {r['phase_role']} | {r['fixed_support']} | {r['curated_records']} |\n"
    write_text(repo/'corpus/paper_cards/INDEX.md',idx_md)

    # Clause cards C1-C8.
    clause_data={
     'C1':('Objecthood','closure operators `E_τ: X → X`, fixed points, defects, perturbation/retention audits','carrier state and declared staging family','maintained/dynamical; interface- and threshold-relative','P05:567–605; P05 table 627–643; T1 exact ten-state-kernel audit','Intertwine closure families across the bridge, transport fixed-point/defect data, and preserve retention margins after withdrawal.','Public behavior can match while target packaging is non-idempotent, fragile, or maintained only by the bridge.','No cross-carrier objecthood-preservation or stability theorem.'),
     'C2':('Strict promotion','lower/promoted readouts `π₀,π₁` and factorization defect with split pair','one declared carrier with layer interfaces','relational between layers; interface-relative','P05:580–582; T1/T3; P03/P23 promotion series','Preserve a nonfactorizing promoted distinction on the target-native carrier and prove it survives source/bridge removal.','A public clone can reproduce the lower readout while lacking the promoted distinction or using an analyst-injected decoder.','Fixed-support promotion is not migration; no heterogeneous strictness theorem.'),
     'C3':('Reflexive self-coordinate','profile refinement terminating at predictive quotient carrying continuation coordinate','history/reachable-state space and self-lens family','predictive, historical, recursively stabilized','P05:583–585; T1 kernel refinement 6→7→7; T14/P14 predictive machinery','Define heterogeneous source/target histories, a well-defined predictive transport, terminality on target support, and branch behavior.','Current/public self-reports can match while future policy/continuation profiles diverge; a copied coordinate can be externally supplied.','No cross-carrier terminal-self-coordinate preservation theorem.'),
     'C4':('Non-exposure','predictive determining state versus declared current/public channel family','realized support plus exposure channels','relational/interface-relative; can dissolve under expanded interface','P05:586–589; T2; P13 hiddenness laws','Transport the predictive distinction while declaring target exposure channels; include expanded-interface and joint-decoder controls.','Public-perfect target may expose or omit the determining variable, changing the package despite matched reports.','No absolute privacy and no empirical access theorem.'),
     'C5':('Drive / action credit','generator provenance and credit partition self/other/none','action generators, environment, ledger, audit record','historical/causal and protocol-relative','P05:590–593; T5; P57 agency/null controls','Preserve provenance through handoff, distinguish target-endogenous actions from source/bridge schedules, and re-audit after withdrawal.','A remote controller or replay can yield identical actions while all directionality should be credited to other/none.','No cross-carrier authorship theorem and no free-will conclusion.'),
     'C6':('Temporal closure','funded order/tick/arrow on staged phase carrier','package state × phase × maintenance ledger','maintained, historical, route-sensitive','P05:594–597; T8/T18; P53 clocks/holonomy','Supply local clock translation through bridge, prove progress and arrow are target-endogenous, and state flatness/holonomy conditions.','An external schedule can manufacture smooth continuity, phase, or arrow while target has no autonomous clock.','No canonical unified-now or cross-carrier synchronization theorem.'),
     'C7':('Binding','strict recombination quotient refinement `R_rec ≻ K_bw`','joint branch histories and declared decomposition','relational/joint-history; decomposition-relative','P05:598–600; T7/T15; P18/P24','Preserve joint recombination information across decomposition/reassembly and distinguish it from independent branch copies.','Branchwise public records can match while cross-branch counterfactual/recombination structure is absent.','No phenomenal-unity or heterogeneous recombination theorem.'),
     'C8':('Viability','nonempty maintained viability kernel under declared ledger; underfunding collapse','controlled dynamics, safe set, action feasibility, ledger','maintained, dynamical, budget-relative','P05:601–603; T1/T11; P22/P32/P56/P57','Translate constraints/budgets, prove a target-native nonempty kernel after withdrawal, and establish robustness under bridge error.','Target can match outputs transiently while outside any self-maintained viability kernel or dependent on source power/control.','Viability is not identity or consciousness; no general cross-carrier kernel theorem.'),
    }
    for cid,(name,primitive,carrier,kind,evidence,survive,counterfeit,gap) in clause_data.items():
        text=f"""# {cid} — {name}

> **Status:** clause of the full C-package design contract; not an exhibited integrated instance.  
> **Primary source:** `P05`, definition `def:cpackage`, lines 567–605.

## Primitive and type

- **Primitive:** {primitive}.
- **Carrier/support:** {carrier}.
- **Temporal/structural character:** {kind}.
- **Claim lanes:** `S-R`{', `A`' if cid in {'C5','C6','C8'} else ''}{', `S-L`' if cid in {'C3','C6','C7'} else ''}{', `R`' if cid in {'C4'} else ''}.

## Landed component evidence

{evidence}.

The strongest evidence is component-level and lives on a declared carrier. P05:642–643 states that component witnesses live on separately declared carriers and that no integrated instance exists.

## What must survive a carrier change

{survive}

## Intrinsic versus interface-relative

No clause is imported as absolutely intrinsic. Even closure, viability, and temporal maintenance are relative to declared dynamics, staging, perturbations, environments, ledgers, or horizons; strictness, hiddenness, credit, and binding additionally depend on declared interfaces or decompositions.

## Bridge composition status

No clause currently has a landed heterogeneous composition theorem. A later bridge must state identity/composition laws, route dependence, and error accumulation for this clause rather than relying on carrier-polymorphic notation.

## Public-match failure mode

{counterfeit}

## Open gap

{gap}

## Nonclaim

Passing {cid} alone does not establish the full C-package, source-target lineage, post-handoff autonomy unless that is part of the clause-specific audit, empirical recognition, consciousness, or personal survival.
"""
        write_text(repo/f'corpus/clause_cards/{cid}.md',text)

    # Theorem cards.
    for tid,(title,srcid,pid,lanes,statement,boundary) in THEOREM_CARD_DATA.items():
        refs=[]
        for sid in srcid.split(';'):
            sid=sid.strip()
            if sid in sby:
                s=sby[sid];refs.append(f"`{sid}` — `{s['filename']}:{s['line_start']}-{s['line_end']}`")
            else: refs.append(sid)
        scope=support_scope(pid,pby[pid])
        t=f"""# {tid} — {title}

> **Claim lanes:** `{lanes.replace(';','`, `')}`  
> **Source paper:** [{pid}](../paper_cards/{pid}.md)  
> **Source record(s):** {', '.join(refs)}

## Compact imported statement

{statement}

## Scope and evidence grade

- **Carrier/support:** {scope[1]}
- **Fixed-support flag:** {scope[0]}.
- **Evidence:** {infer_evidence(pby[pid])}
- **Imported assumptions:** all paper-declared carriers, interfaces, protocols, reachable sets, thresholds, and status conditions.

## Project-facing use

This theorem family is retained as a composable asset or boundary for later candidate generation. It is not selected as the project target in CST-EXP-01.

## Composition / route / branch audit

Any later use must explicitly state whether the source theorem supplies identity, composition, route independence, branch/fusion behavior, and approximation. Missing fields remain open rather than inferred.

## Boundary

{boundary}

## Distinct-carrier obligation

{cross_generalization(pid,pby[pid])}
"""
        write_text(repo/f'corpus/theorem_cards/{tid}.md',t)

    # Asset atlas.
    atlas=f"""# Canonical asset atlas

## Purpose and reading rule

This atlas converts the corpus into a composable research inventory without choosing a transfer theory. Every asset remains attached to its exact source scope. In particular, fixed-support promotion, route transport, or persistence is never renamed “substrate transfer,” and profile or public equivalence is never renamed identity.

## Corpus-level synthesis

The corpus is rich in **local ingredients** and poor in the one theorem the project ultimately needs. It contains exact machinery for predictive quotients, relation-valued persistence, route transport, holonomy, recombination, promotion, carrier exactification, event admissibility, closure completion, viability, endogenous repair, temporal closure, hiddenness, no-overreading, confluence, residuals, and finite no-smuggling semantics. Most of the strongest continuity-adjacent assets are either fixed-support, carrier-relative, interface-relative, or component-level. No paper supplies a heterogeneous source-carrier/target-carrier theorem that simultaneously establishes target C-package realization, source-target lineage, and post-handoff autonomy.

The most promising **compositional seam**—without ranking it as a target—is: predictive quotient/future sufficiency → typed route transport → relation-valued object persistence → recombination and confluence audits → target exactification/strict tests/event admissibility → viability/endogenous repair/temporal closure after withdrawal. The corpus also supplies decisive controls against snapshot copying, public-shadow matching, external schedules, local-but-not-global packaging, and route-dependent reconstruction. Whether those pieces can be made mutually compatible is an open exploration question for later phases.

Ontology remains separate. P05/T17 and P58 price certificate soundness, A1, and A2 explicitly. A2 is not a carrier-transport theorem, and the absence of an integrated full C-package instance remains a hard gap.

## Asset families

| ID | Asset | Primary sources | Lanes | Scope | Likely use | Hard boundary |
|---|---|---|---|---|---|---|
"""
    for row in ASSET_FAMILIES:
        atlas+='| '+' | '.join(md_escape(x) for x in row)+' |\n'
    atlas+="""

## Cross-asset dependency observations

1. **Predictive transport depends on more than a current-state match.** The quotient must be future-sufficient on a declared reachable image, and bridge continuation must respect that quotient.
2. **Lineage cannot be reduced to a function without extra premises.** T14 and F19 make branch/fusion and relation-valued persistence natural; symmetric duplication is therefore a first-class stress case.
3. **Target realization is downstream of target-native closure.** Public reduction/readout is compatible with counterfeit shadows. Exactification, strict tests, event admissibility, and AOR status help, but none alone gives the full C-package.
4. **Autonomy is intervention-relative.** Viability, repair, currencies, and clocks must be re-audited after a declared bridge/source withdrawal.
5. **Route independence is purchased by confluence/flatness conditions, not by endpoint similarity.** Holonomy and critical pairs expose protocol dependence.
6. **Local certificates need a global package law.** Event and clause witnesses on separate supports cannot be concatenated into one subject by prose.
7. **Approximation is a separate program.** Residuals and QEC provide tools, but no general stability/composition theorem connects small bridge error to preserved lineage or viability.
8. **Recognition and ontology remain external seams.** Structural certificates require a measurement bridge; phenomenal/personal readings require separately declared assumptions.

## Fail-closed import rule

A later candidate may cite an asset only by its asset ID plus a row in `ledgers/statement_provenance.csv` or by marking the primitive as genuinely new. The citation must carry the fixed-support flag from `ledgers/support_and_carrier_assumptions.csv`.
"""
    write_text(repo/'corpus/asset_atlas/ASSET_ATLAS.md',atlas)

    composition="""# Cross-asset composition notes

These are **unranked exploratory assemblies**, not target proposals. No target is selected and no assembly is a selected candidate.

## Predictive-lineage assembly

`A-PQ-01 → A-PQ-02 → A-RT-01 → A-OP-01`, stress-tested by `A-HO-01`, `A-RE-01`, and duplication symmetry. Missing: heterogeneous carrier types, global composition, and a demarcation between structural lineage and personal identity.

## Target-native realization assembly

`A-PR-01 → A-EX-01 → A-ST-01 → A-EV-01 → A-AOR-01`, constrained by `A-LG-01` and `A-FS-01`. Missing: a full integrated C1–C8 instance and proof that bridge removal leaves the target closed.

## Autonomous handoff assembly

`A-VI-01 + A-CU-01 + A-AG-01 + A-TM-01`, with `A-PT-01` as the null/control family. Missing: a single withdrawal intervention binding source disconnection, environment retention, horizon, and target repair.

## Counterfeit-resistance assembly

`A-HID-01 + A-NO-01 + A-PQ-01 + A-AR-01 + A-CD-01`, with public-perfect but future-different or bridge-dependent copies as controls. Missing: a recognition instrument that can test the relevant distinctions without complete-state access.

## Route-independent migration assembly

`A-HO-01 + A-CF-01 + A-TM-01 + A-RE-01`. Missing: proof that the chosen critical pairs generate all admissible migration-order differences and that normal forms preserve the target package rather than only a coarse record.

## Ontological reading

`A-ON-01` is not part of any structural assembly. It can only be applied after certificate soundness and the desired structural theorem are separately supplied; A2 cannot fill a missing bridge.
"""
    write_text(repo/'corpus/asset_atlas/COMPOSITION_NOTES.md',composition)

    # Dependency graph.
    nodes=[
      ('N01','Declared carrier/support','primitive'),('N02','Lens / public record','primitive'),('N03','History / reachable image','primitive'),
      ('N04','Current quotient Q','quotient'),('N05','Predictive quotient M','quotient'),('N06','Future sufficiency / factorization','law'),
      ('N07','Route continuation','bridge'),('N08','Predictive transport','bridge'),('N09','Holonomy / route residue','obstruction'),
      ('N10','Marking / erasure','operation'),('N11','Recombination quotient','quotient'),('N12','Relation-valued persistence','lineage'),
      ('N13','Strict promotion','realization'),('N14','Carrier exactification','realization'),('N15','Accepted strict tests','recognition'),
      ('N16','Carrier-event record','recognition'),('N17','Global event package','realization'),('N18','Local/global obstruction','obstruction'),
      ('N19','AOR completion/reflection','realization'),('N20','Viability kernel','autonomy'),('N21','Currency / maintenance ledger','autonomy'),
      ('N22','Endogenous repair','autonomy'),('N23','Temporal closure / local clock','autonomy'),('N24','Protocol trap','obstruction'),
      ('N25','Hiddenness / non-exposure','recognition'),('N26','No-overreading','obstruction'),('N27','Confluence / flatness','law'),
      ('N28','Adequacy residual','metric'),('N29','Closure deficit','metric'),('N30','No-smuggling finite semantics','method'),
      ('N31','Full C1–C8 package','target-contract'),('N32','Simplified certificate','certificate'),('N33','Certificate soundness H1','assumption'),
      ('N34','ClosureComplete','predicate'),('N35','A1 Ontic Closure Completeness','assumption'),('N36','Realized','ontology'),
      ('N37','A2 Substrate Indifference','assumption'),('N38','Cross-carrier invariance H-XCI','missing-theorem'),
      ('N39','Recognition bridge','missing-empirical'),('N40','Post-handoff autonomy','target-property'),
    ]
    edges=[
      ('N01','N02','typed-by'),('N03','N04','quotiented-by'),('N03','N05','quotiented-by'),('N05','N04','refines'),
      ('N06','N08','makes-well-defined'),('N07','N08','induces'),('N08','N09','may-generate'),('N27','N09','eliminates-under-conditions'),
      ('N10','N11','stress-tests'),('N11','N12','informs'),('N05','N12','supports'),('N08','N12','supports'),
      ('N13','N14','precedes'),('N14','N15','supports'),('N15','N16','supports'),('N16','N17','candidate-input'),('N18','N17','obstructs'),
      ('N19','N17','can-complete-operationally'),('N20','N40','required-for'),('N21','N20','funds'),('N22','N20','maintains'),
      ('N23','N40','required-for'),('N24','N40','can-counterfeit'),('N25','N31','is-C4-component'),('N26','N39','limits'),
      ('N28','N08','measures-defect-of'),('N29','N14','audits'),('N30','N08','constrains'),('N30','N14','constrains'),
      ('N13','N31','is-C2-component'),('N11','N31','is-C7-component'),('N20','N31','is-C8-component'),('N23','N31','is-C6-component'),
      ('N31','N32','no-ordering-theorem'),('N32','N33','requires-for-closure'),('N33','N34','licenses'),('N34','N35','requires-for-ontology'),
      ('N35','N36','licenses'),('N37','N38','does-not-prove'),('N38','N08','would-support'),('N39','N31','would-recognize'),
      ('N40','N31','separate-audit'),('N12','N36','does-not-imply'),('N31','N36','does-not-imply-unconditionally'),
    ]
    write_csv(repo/'corpus/asset_atlas/dependency_graph_nodes.csv',['node_id','label','kind'],[{'node_id':a,'label':b,'kind':c} for a,b,c in nodes])
    write_csv(repo/'corpus/asset_atlas/dependency_graph_edges.csv',['source','target','relation'],[{'source':a,'target':b,'relation':c} for a,b,c in edges])
    dot=['digraph CST_EXP01 {','  rankdir=LR;','  node [shape=box, fontsize=9];']
    for n,l,k in nodes: dot.append(f'  {n} [label="{l}\\n[{k}]"];')
    for a,b,r in edges: dot.append(f'  {a} -> {b} [label="{r}", fontsize=8];')
    dot.append('}')
    write_text(repo/'corpus/asset_atlas/dependency_graph.dot','\n'.join(dot))
    mer=['flowchart LR']
    for n,l,k in nodes: mer.append(f'  {n}["{l}<br/>({k})"]')
    for a,b,r in edges: mer.append(f'  {a} -->|{r}| {b}')
    write_text(repo/'corpus/asset_atlas/dependency_graph.mmd','\n'.join(mer))
    graph_md="# Dependency graph reading guide\n\nThe `.dot`, `.mmd`, node, and edge files encode the same graph. Edges are typed and do not all denote implication. In particular, `does-not-imply`, `no-ordering-theorem`, and `does-not-prove` are negative boundaries. A1, A2, certificate soundness, recognition, and the missing cross-carrier theorem are outside the landed structural path.\n"
    write_text(repo/'corpus/asset_atlas/DEPENDENCY_GRAPH_GUIDE.md',graph_md)

    # Gap-to-asset matrix.
    gap_rows=[{'gap_id':g,'gap':name,'partial_assets':assets,'missing_assumptions_or_data':missing,'new_result_needed':needed,'gap_type':typ,'falsifier_or_kill_test':kill,'status':'open; not target-ranked'} for g,name,assets,missing,needed,typ,kill in GAPS]
    write_csv(repo/'ledgers/gap_to_asset_matrix.csv',list(gap_rows[0].keys()),gap_rows)

    # Version and exclusion log with archive timestamps when available.
    zi={}
    if args.source_zip and args.source_zip.exists():
        with zipfile.ZipFile(args.source_zip) as z:
            for info in z.infolist(): zi[Path(info.filename).name]=info
    p42,p60,p46=pby['P42'],pby['P60'],pby['P46']
    def zdate(p):
        inf=zi.get(p['filename']);return f"{inf.date_time[0]:04d}-{inf.date_time[1]:02d}-{inf.date_time[2]:02d} {inf.date_time[3]:02d}:{inf.date_time[4]:02d}" if inf else 'not recovered'
    labs42={s['label'] for s in statements if s['paper_id']=='P42' and s['label']}
    labs60={s['label'] for s in statements if s['paper_id']=='P60' and s['label']}
    version=f"""# Version and exclusion log

## P42 / P60 — one Strict Audited Utility evidence line

| Field | P42 (normative newer revision) | P60 (older revision) |
|---|---|---|
| Stored filename | `{p42['filename']}` | `{p60['filename']}` |
| Embedded title | {p42['embedded_title']} | {p60['embedded_title']} |
| Archive timestamp | {zdate(p42)} | {zdate(p60)} |
| SHA-256 | `{p42['sha256']}` | `{p60['sha256']}` |
| Bytes | {p42['bytes']} | {p60['bytes']} |
| Theorem-like environments | {p42['statement_count']} | {p60['statement_count']} |
| Evidential weight | primary for this line | zero independent weight; provenance/deltas only |

The filenames and embedded titles are crossed: the file named for *The Usefulness of Non-Descending Objects* contains the embedded title *Why Mathematics Even Works*, while the file named *Why Mathematics Even Works* contains the embedded title *The Usefulness of Non-Descending Objects*. Archive timestamps and the expanded statement catalog make P42 the normative revision.

Label-set comparison: {len(labs42)} labeled environments in P42, {len(labs60)} in P60; {len(labs42-labs60)} labels appear only in P42 and {len(labs60-labs42)} only in P60. The full lexical indexes are retained for audit, but citations should ordinarily point to P42. Profile transfer remains profile/certificate transport and explicitly does not establish object identity.

## P46 quarantine

- Paper: `{p46['filename']}`
- SHA-256: `{p46['sha256']}`
- Source contains {p46['statement_count']} theorem-like environments, but none are imported into the machine statement bank or curated provenance.
- The paper card is metadata/exclusion only. The owner-inherited exclusion remains active unless explicitly revoked.

## Embedded duplicates in the consciousness repository

See `corpus_duplicate_map.csv`. Byte-identical copies are not counted as additional evidence. The modular consciousness manuscript and compiled PDF are separate presentation/build surfaces for P05, not independent research lines.
"""
    write_text(repo/'ledgers/version_and_exclusion_log.md',version)

    # Consciousness repository inventory and duplicate map.
    conrows=inventory_consciousness(args.consciousness_dir,repo)
    dups=duplicate_map(papers,args.papers_dir,args.consciousness_dir,repo)

    # Source-read protocol and wave ledger.
    wave_rows=[]
    for w,ps in WAVES.items():
        for order,pid in enumerate(ps,1):
            wave_rows.append({'wave':w,'order':order,'paper_id':pid,'title':pby[pid]['triage_title'],'card':f'corpus/paper_cards/{pid}.md','status':'extracted'})
    write_csv(repo/'ledgers/dependency_read_wave_log.csv',['wave','order','paper_id','title','card','status'],wave_rows)

    # Phase README.
    readme=f"""# CST-EXP-01 corpus inventory

This directory set is the statement-level corpus extraction required by CST-EXP-01.

## Counts

- 60 paper cards, including explicit non-primary and quarantined cards.
- {len(full_rows)} nonquarantined theorem-like source environments in the complete lexical index; {len(statements)} in the original source archive including P46.
- {len(provenance)} curated provenance records.
- 8 C-clause cards.
- {len(THEOREM_CARD_DATA)} theorem/family cards.
- {len(ASSET_FAMILIES)} canonical asset families.
- {len(GAPS)} open gap rows.
- {len(conrows)} consciousness-repository files inventoried.
- {sum(1 for r in dups if r['byte_identical'])} byte-identical embedded paper copies mapped and not double counted.

## Entry points

1. `asset_atlas/ASSET_ATLAS.md`
2. `paper_cards/INDEX.md`
3. `clause_cards/C1.md` through `C8.md`
4. `theorem_cards/`
5. `../ledgers/statement_provenance.csv`
6. `../ledgers/support_and_carrier_assumptions.csv`
7. `../ledgers/gap_to_asset_matrix.csv`
8. `consciousness_repo/ASSET_MAP.md`

## Scope fence

No transported object, bridge, lineage criterion, theorem target, toy program, simulation, empirical recognition rule, or ontological conclusion is selected here.
"""
    write_text(repo/'corpus/README.md',readme)

    print(json.dumps({'paper_cards':60,'full_index_rows':len(full_rows),'curated_provenance':len(provenance),'clause_cards':8,'theorem_cards':len(THEOREM_CARD_DATA),'assets':len(ASSET_FAMILIES),'gaps':len(GAPS),'consciousness_files':len(conrows),'duplicate_matches':sum(1 for r in dups if r['byte_identical'])},indent=2))

if __name__=='__main__': main()
