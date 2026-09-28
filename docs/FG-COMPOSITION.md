# FG composition registry (v2, 2026-09-28)

_Owner: the async-resilience session (research). ethereum-f1 keeps this file
consistent with FRAMEWORK-DESIGN.md §7._

## 0. Registry policy (audit W08)

- Each entry PINS its statement and its hypotheses. The pinned text is an
  exact copy of the cited source lines. It does not change when the source
  changes. Links inside pinned text are relative to `tsc/`.
- Each entry names its module variant: `nj` (`SimplexFG.nj`, DC's NJ rule),
  `fj` (`SimplexFG.fj`, the FJ root rule), or `both`. An AP-side entry names
  the variant whose frame its premises use.
- Each entry names its source file, section and line range, and the SHA-256
  of that source file at registration (§0.1).
- A change of statement or hypotheses gets a new id. The old id stays, with
  the status WITHDRAWN. Ids with an unchanged statement stay.
- The status is a dated line. A later status change adds a new dated line
  below the old one. It does not change the pinned statement.
- Status values: LEAN (a Lean certificate); PROVED (a paper proof from the
  pinned hypotheses); PROVED* (a paper proof, conditional on the listed
  unproved entries); SKETCH (a proof with an identified missing step); OPEN
  (no proof and no refutation); REFUTED (a counterexample); RULE (true by
  the honest code, not a theorem); def (a definition); WITHDRAWN (no
  composite may cite the entry); SUPERSEDED (the entry stays as a pointer;
  its pinned text does not change; a composite cites the named successor
  ids, whose conjunction states the same fact).
- Two edits of a hypotheses list keep the id, with a dated note: (a) the
  replacement of a SUPERSEDED id by its successor ids; (b) a new reference
  by id to a fact that the pinned text already uses (for example "F4" or
  "finalized crossing"). Any other change of hypotheses gets a new id.
- "FG-SA" in a status means a proof for the FG-SA client, that is, the
  Simplex policy with honest non-equivocating signers. As a certificate
  FAMILY over every policy σ, an AP-side entry still needs a proof that uses
  only frame conditions and AP facts (FRAMEWORK-DESIGN.md §7.3, audit W02).
  [async] An entry that states FG height progress is never a family entry;
  it holds for the Simplex policy only.
- AP-side ids (`ap.*`) state only AP SERVICE facts: repair, common fresh
  sources, row service, block retention and source safety
  (FRAMEWORK-DESIGN.md §7.3, audit W02). A height rise, an FG entry law or
  a record permission is a `comp.*` or `fg.*` entry, derived after
  specialization to the Simplex policy.

### 0.1 Sources

`tsc/` = `research/async-resilient-committees/tip-stability/codex/`. [async]
`r146` = `fgsa-adj` of v1. Section numbers and line ranges replace the v1
line numbers. `r144o` is the Opus variant of r144. `r151` is `fj-theorem-h.md`.

```text
┌───────┬───────────────────────────┬──────────────────────────────────┬──────────────────────────────────┐
│ Key   │ File (tsc/)               │ SHA-256, first half              │ SHA-256, second half             │
├───────┼───────────────────────────┼──────────────────────────────────┼──────────────────────────────────┤
│ r143  │ fgsa-fast.md              │ 8907540c5c71fe06703bc8d2ec2d30bc │ 6cbc752a5f7577219a69196e2fd8ef37 │
│ r144  │ fgsa-no-nj.md             │ 1eaf728ffc4d56cc54fbccf581a8dffe │ 457da02b96bd59cedb012bbf5ee1e03a │
│ r144o │ fgsa-no-nj-opus.md        │ 7df2a540134deddede78ea711754bb32 │ 2911fced62271868f8b5034164db9f4e │
│ r146  │ fgsa-adjudicate.md        │ 0fe1717f6abbf0d708cada05a8a4d3e3 │ 431a530d3d5c3a65e86bf755f5642017 │
│ r147  │ fgsa-conditional.md       │ 940e481501f8c52f57bd7110faa442b5 │ 4ce4aa3bb512769a07c9b769037ea0f5 │
│ r148  │ fj-redteam.md             │ 934fe2927f047a11e37dbe52aba9d754 │ d5c461927f24b91902077f17459d47d2 │
│ r149  │ fgsa-conditional-close.md │ 1ea1ccc5c944335b7e7793afe2c6675a │ 056762e35eeaeee13ec1f6066460a902 │
│ r150  │ fgsa-theorem-h.md         │ 8211361a618814fa4d5f4b1a3c593943 │ 380c9ccb99235e8b9c413d633876adc3 │
│ r151  │ fj-theorem-h.md           │ 16b69dba55d889b9ae20dd55b228cfd8 │ 3ad22037d796c6219cdb65831718bba3 │
│ bp    │ fgsa-healing-blueprint.md │ 4d643d7a6285705ef8bcef6b408b46a4 │ 5d64641f0d92828b3539f8f938074318 │
│ sa    │ slow-arming.md            │ c1d1a4e343c6910a1072cc7e6e8816b6 │ ab6ac94b4940f204573f3a39c500db0b │
└───────┴───────────────────────────┴──────────────────────────────────┴──────────────────────────────────┘
```

Sources outside `tsc/` (registered 2026-09-28). `spec/` =
`research/async-resilient-committees/tip-stability/spec/`. `dc/` =
`research/healing/rewrite/`. `vc/` =
`lean/decoupled-consensus/verified-consensus/` at commit `b97b902`. `ac/` =
`lean/available-chain/` at commit `ae2a9d3` (the SA Lean model; the file is
unchanged since `588d666`).

```text
┌───────┬──────────────────────────────────────────────────────────────────┬──────────────────────────────────┬──────────────────────────────────┐
│ Key   │ File                                                             │ SHA-256, first half              │ SHA-256, second half             │
├───────┼──────────────────────────────────────────────────────────────────┼──────────────────────────────────┼──────────────────────────────────┤
│ spec  │ spec/fgsa-protocol.tex                                           │ ae4497abc7c5b3a6f73697f341bf730a │ 63c7d34bd2f7546154bd022bc95af223 │
│ dc    │ dc/consensus.tex                                                 │ dc471b47a46896fe0a3df300c188fef1 │ 512f475615ce0fc0df18dbea6d2e5517 │
│ vcE   │ vc/DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean │ 92fb0e64c1288afea98b53212cb3ad5c │ 843c9c720187367eea578d17a9d53454 │
│ vcF   │ vc/DecoupledConsensusProofs/Protocol/ChainState/                 │ aa0ed92740eb1ec8ee69e90fd2ae75f0 │ 3179a27c05accf5f631e7a254589b94c │
│       │   FinalityComparison.lean                                        │                                  │                                  │
│ vcW   │ vc/DecoupledConsensusProofs/Protocol/ValidatorClient/            │ f0d45fa7fd93a0a1c9f4dfccaf6c3f7c │ 63c43245c5deee7182a25f3963c22b5d │
│       │   WeakHeightBounds.lean                                          │                                  │                                  │
│ acG   │ ac/AvailableChainGridCO/Model/Protocol.lean                      │ 2cb079fd72fb7cb6901d8a8cfd59c650 │ ad6561377b226b3240b68c852b59755c │
└───────┴──────────────────────────────────────────────────────────────────┴──────────────────────────────────┴──────────────────────────────────┘
```

### 0.2 Pinned premise sets

Entries cite these sets as hypotheses. Each set is an exact copy.

**`env.r147`** — r147 §1, lines 36–101. File `fgsa-conditional.md`, sha256
`940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.

> _fgsa-conditional.md, lines 36–101:_
>
> Use a valid, reachable FG-SA execution, starting with the specified
> initial state. An arbitrary pre-GST execution is permitted. Arbitrary
> independently assigned S records, leases, or Λ records are not permitted.
> There are n base seats per label and n unit-weight FG identities, as in
> the two rule documents. The same static faulty set has size a. Counts
> at different base labels are never added.
>
> ```text
> h = n−a;             f = (n−1) div 3;
> τ = (n+1) div 2;     q_F = (2n+2) div 3;
> a ≤ f;              h ≥ q_F ≥ τ;       h > 2a;
> 2q_F−n > a;         τ > a.
>
> Δ > 0; k ≥ 2;       L = (4k−1)Δ;
> t_s = 4sΔ;          v_s = t_s+Δ;
> e_s = t_s+2Δ;       z_s = t_s+3Δ;
> q_s = t_s+5Δ;       d_s = t_s+6Δ;
> P = 4RΔ; R ≥ 3;     T_r = rP; a_r = T_r+6Δ = d_(rR);
> δ_t = 2R slots;     ρ = 2L+G+8Δ;
> σ = (g+3)P+G+6Δ;   B_static = ρ+2σ.
> ```
>
> The following premises apply through every time used in a conclusion.
>
> 1. All honest validators participate after GST. Each has one HEAD per
>    scheduled label and one FG action per scheduled round. They process
>    clocks and receipts as specified. Honest identities do not equivocate.
> 2. Post-GST messages and accepted complete dependencies have strict Δ
>    delivery and relay. The return-relay condition covers objects already
>    accepted at GST. An emission is not a receipt, even at the sender.
> 3. Blocks and signatures are authentic. Parents have smaller slots.
>    Roots identify blocks uniquely. Views have the specified ancestor
>    closure. Original declared support subsets remain unchanged. A later
>    path receipt does not convert a raw-only declaration into support.
> 4. For (L), an awake honest proposal occurs strictly after each relevant
>    trigger and within G. Also use Rec(g): every inclusive round window
>    `[r,r+g]` contains an honest opening whose next two **slot** proposers
>    are honest. Use the rule documents' `g≥3`. The full window and every
>    gate used must fit in the horizon. Strong recurrence for first finality
>    is not used here. Neither K nor the debt parameter D enters (L).
> 5. Honest proposals include the specified current-window rows from the
>    pool and from held current-window blocks, except rows already on the
>    parent chain. Use `w_F≥1`, full-row deduplication, and distinct FG
>    identities. A faulty carrier may use old authentic rows. Stored
>    progress bits persist until that chain advances height.
> 6. The source at action r is exactly the deepest member of
>    `FastWrite_i[rR] ∩ D_action` with a live deadline. An empty latest gate
>    does not fall back to an earlier gate. Targets, repeats, and timeouts
>    all use this source. The finality pair instead uses the actual full-view
>    finality head. Its own finality pair overrides the lock at the same
>    height before the height-pair branch is evaluated. Λ persists.
> 7. R1 is used at every duty. Gates, saved raw results, resolution, and
>    release remain unfiltered. The whole-result S guard tests all live
>    leases, including excluded leases. Only a successful guarded gate
>    writes S and leases. Finality does not assign to S.
>
> For (S), a synchronous source label means that its complete SA delivery,
> return-relay, and late-test premises hold. `t_s≥GST` is a sufficient
> condition. The claim is not based on `a_r≥GST` alone. The proof needs the
> same receipt properties at each later label it uses. The SA definition
> `SynchronousLabel` explicitly includes execution, delivery, relay, honest
> majority, and horizon conditions [SA1].
>
> Full participation and `a≤f` are retained throughout this document to
> match the recovery job. The source-to-HEAD part of (S) can use weaker
> majority premises. No such weakening is needed for this interface.

**`env.r149`** — r149 §1, lines 49–79. File `fgsa-conditional-close.md`,
sha256 `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
It uses `env.r147` by reference.

> _fgsa-conditional-close.md, lines 49–79:_
>
> Use [fgsa-fast §§2–4](fgsa-fast.md) and
> [fgsa-fast-opus §2](fgsa-fast-opus.md) as the FG-SA rules. Use the reachable
> execution and recovery premises of [r147 §1](fgsa-conditional.md):
> authentic objects, strict parent-slot order, full honest participation
> after GST, strict Δ delivery and accepted-object return relay, original
> declared support subsets, R1 duty views, unfiltered raw gates and release,
> the whole-result guard, persistent DC records, and the actual fresh-source
> rule at every height action. No independently assigned initial lease or S
> record is allowed.
>
> For liveness, retain the honest-proposer bound G, Rec(g), current-window
> row inclusion with `w_F ≥ 1`, and every required horizon. For safety, only
> the relevant synchronous labels and delivery horizons are needed. In
> particular, the existence of a fast write at `d_s` requires an execution
> through `d_s`, even when the safety endpoint is the earlier time `q_s`.
>
> ```text
> h = n−a;             f = (n−1) div 3;
> τ = (n+1) div 2;     q_F = (2n+2) div 3;
> a ≤ f;              h ≥ q_F ≥ τ > a;     h > 2a;
>
> t_s = 4sΔ;          v_s = t_s+Δ;          e_s = t_s+2Δ;
> z_s = t_s+3Δ;        q_s = t_s+5Δ;        d_s = t_s+6Δ;
> k ≥ 2;              L = (4k−1)Δ;
> R ≥ 3;              P = 4RΔ;             a_r = d_(rR);
> ρ = 2L+G+8Δ;        σ = (g+3)P+G+6Δ;     θ = 4Δ.
> ```
>
> Here and below, “ordinary walk” means the same duty's walk from its FG
> root Z, with the lease start removed. It retains the domain, scores,
> eligibility test, and tie order. It does not mean an unfiltered walk.

**`env.bp`** — bp §1.2, lines 118–145. File `fgsa-healing-blueprint.md`,
sha256 `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.

> _fgsa-healing-blueprint.md, lines 118–145:_
>
> Use the equal-size C* profile: n base seats at each label and n fixed
> unit-weight FG identities, with the same static faulty set of size a.
>
> ```text
> τ = (n+1) div 2;  q_F = (2n+2) div 3;  f = (n−1) div 3;
> k ≥ 2;  L = (4k−1)Δ;  ρ = 2L+G+8Δ;  R ≥ 3;  P = 4RΔ;  θ = 4Δ;
> t_s = 4sΔ; v_s = t_s+Δ; e_s = t_s+2Δ; z_s = t_s+3Δ;
> q_s = t_s+5Δ = v_(s+1);  d_s = t_s+6Δ;
> T_r = rP;  a_r = T_r+6Δ = d_(rR);  δ_t = 2R slots;  D ≥ 2;  K ≥ g+2.
>
> a ≤ f  ⇒  h = n−a ≥ q_F ≥ τ;  τ > a;  q_F > a;  h > 2a;  2q_F−n > a.
> ```
>
> The recovery environment (E-env) is: `a≤f`; full participation from GST;
> strict Δ delivery and accepted-object relay from GST; an awake honest
> proposer strictly after each trigger and within G; DC's multi-proposer
> recurrence Rec(g); every proof window in the horizon. Readers process
> receipts while asleep. A private faulty object has no relay deadline until
> an honest reader accepts it.
>
> Let r_G be the first action round with `a_(r_G) ≥ GST`. The DC cut is the
> inclusive event prefix at `u_0 = a_(r_G+2)`. Then `GST+2P ≤ u_0 < GST+3P`.
> Let M be the honest archival frontier at u_0. As in DC,
>
> ```text
> H = the first multiple of K strictly above M+D+2;
> M+D+3 ≤ H ≤ M+D+K+2;  H+3 ≤ M+D+K+5.
> ```

**`env.r150`** — r150 §1, lines 43–112. File `fgsa-theorem-h.md`, sha256
`8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.

> _fgsa-theorem-h.md, lines 43–112:_
>
> The exact recovery premises are:
>
> 1. The equal-size C* profile has n base seats per label and n fixed,
>    unit-weight FG identities. The same static faulty set has size
>    `a ≤ f = (n−1) div 3`. All h=`n−a` honest identities participate
>    after GST.
> 2. Objects and paths are authentic; roots are injective; parent slots
>    strictly increase. Executions start from the specified initial
>    state. S values, saved results, leases, and persistent DC records
>    have actual event origins. Completed gates do not replay.
> 3. After GST, delivery and accepted-object return relay take strictly
>    less than Δ. Honest proposal delivery and proposal-view relay
>    readiness hold. Receipts and clock events are processed also while
>    asleep. Private faulty objects acquire a relay duty only when an
>    honest reader accepts them. Every proof window fits in the horizon.
> 4. Each duty computes its frame from its own R1 view. Signed proposal
>    merges retain the original declared support subset. Raw tests,
>    saved raw results, and release are unfiltered. The S guard tests
>    all live leases, including excluded leases. Only a successful
>    guarded gate changes S or writes a lease. Finality does not assign S.
> 5. An awake honest proposer occurs strictly after every trigger and
>    within G. For the arrival bounds, retain Rec(g): an honest opening
>    and its next two slot proposers within g rounds. Honest proposals
>    include current-window rows, with `w_F ≥ 1`. Use the DC causal cap,
>    exact-entry quorum rules, finality lock, and persistent client rules.
>
> The local Theorem H needs the actual reset specified below, but does
> not need a height-progress bound. Rec(g) and row inclusion are used to
> obtain that reset within a deadline. No stronger recurrence for first
> finality is assumed or concluded.
>
> ```text
> τ = (n+1) div 2;      q_F = (2n+2) div 3;
> h ≥ q_F ≥ τ > a;     h > 2a;             2q_F−n > a;
> Δ > 0;              k ≥ 2;              L = (4k−1)Δ;
> R ≥ 3;              P = 4RΔ;            g ≥ 3;
> D ≥ 2;              K ≥ g+2;            δ_t = 2R slots;
>
> t_s = 4sΔ;          v_s = t_s+Δ;        e_s = t_s+2Δ;
> z_s = t_s+3Δ;        q_s = t_s+5Δ;       d_s = t_s+6Δ;
> T_r = rP;           a_r = d_(rR);
> ρ = 2L+G+8Δ;        σ = (g+3)P+G+6Δ;
> λ = ρ+2σ;           θ = 4Δ;             N = D+K+5.
> ```
>
> Write `ht(B)` for the DC height of a block. Prefix order is `⪯`.
> At duty d, use the blueprint's frame `(F_d,H_d,J_d,j_d,Z_d,D_d)`.
> A block B is kept when `B ⪯ Z_d` or `B ∈ D_d`. The ordinary walk is
> the same domain walk from Z_d, with the lease start removed. It retains
> the scores, eligibility rule, and tie order.
>
> Let `u_0=a_(r_G+2)`, where r_G is the first action round at or after
> GST. Let M be the honest archival frontier at that inclusive cut. Set
> H to the first multiple of K strictly above `M+D+2`. Thus
>
> ```text
> GST+2P ≤ u_0 < GST+3P;
> M+D+3 ≤ H ≤ M+D+K+2;       H+3 ≤ M+N.
> ```
>
> Use the actual DC consumer, with both outcomes. In the NJ outcome,
> `x=H` and the retained prefix has no honest target or lock at H. In
> the finalized outcome, x is its actual finalized height, `M<x≤H+1`,
> and F* is the named checkpoint at x. Every block of height greater
> than x extends F*. Do not replace this outcome by an assumed NJ bit.
>
> Let r* be the least round of an honest height-(x+1) row, let `s*=r*R`,
> and let C* be its fresh fast source body. The causal cap gives a wholly
> post-GST source label s*. Every honest row at height at least x+1 has
> label at least s*. These are the reset facts in blueprint §6.

**`env.r148`** — r148 §1, lines 76–119. File `fj-redteam.md`, sha256
`934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.

> _fj-redteam.md, lines 76–119:_
>
> Use the equal-size C* profile: n seats at each base label and n fixed
> unit-weight FG identities; static corruption; one awake predicate;
> complete authenticated paths; injective roots; increasing parent
> slots; strict receipt cutoffs; and accepted-object relay. This does
> not prove a result for a smaller sampled committee.
>
> ```text
> τ = ceil(n/2); q = ceil(2n/3); f = floor((n−1)/3).
> L = (4k−1)Δ, k≥2; Π=min(η,L); ρ=2L+G+8Δ.
> P=4RΔ, R≥3; δ_t=2R slots; w_F≥1.
> t_s=4sΔ; v_s=t_s+Δ; e_s=t_s+2Δ; z_s=t_s+3Δ;
> q_s=t_s+5Δ; d_s=t_s+6Δ; a_r=rP+6Δ=d_(rR).
>
> Base claims: a<h≤n−a; thus a<τ and a<q.
> Recovery: a≤f; full participation; strict Δ delivery and relay;
>           honest proposal recurrence G and DC multi-proposer recurrence g.
> Then h=n−a≥q≥τ, h>2a, and 2q−n>a.
> ```
>
> First-finality bounds need the actual DC strong recurrence: three
> consecutive honest openings, with the last opening's next two slot
> proposers honest. See [Conditions.lean][conditions]. It has g≥3 in
> continuous time. Removing NJ removes the restriction K≥g+2; it does
> not remove proposer recurrence.
>
> Write h(B) for state height, not block depth or slot. Let j be the
> justified height of J, and H the maximum in the current duty view.
> An entry at one height can have many descendants at that same height.
> Two different entries at the same height conflict.
>
> Use two causal caps:
>
> ```text
> M  = maximum height of an honest height row whose source label has
>      v_s<GST, or 1 if there is no such row.
> rG = first action round at or after GST.
> u0 = a_(rG+2), with its inclusive event prefix.
> M0 = honest archival maximum at u0. Thus M≤M0.
> ```
>
> A synchronous source C at label s is retained from its transfer HEAD
> q_s=v_(s+1). It need not be in every HEAD at v_s, and need not be in
> every S at a_r=d_s. This timing correction applies to “stays canonical”
> throughout this report.

**`env.r151`** — r151 §1, lines 41–98. File `fj-theorem-h.md`, sha256
`16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
It restates the FJ frame of `fj.frame.v1` and the premises of `env.r150`.

> _fj-theorem-h.md, lines 41–98:_
>
> Use exactly [r148 §2](fj-redteam.md): plain SA, the DC exact-entry
> client, R1 duty views, fresh fast height sources, and `nj=false`.
> There is no SG or PC rule. In each duty's own view V, compute F, H,
> and the highest justified pair (j,J) compatible with F. Use:
>
> ```text
> H=j+1, all height-H blocks extend J: Z=J, lo=H−1;
> H=j+1, some height-H block conflicts with J: Z=F, lo=H;
> otherwise: Z=F, lo=H−1.
>
> D = {B∈V : F⪯B, Z⪯B, ∃W∈V, B⪯W and ht(W)≥lo};
> Kept_d(B) := B⪯Z_d or B∈D_d.
> ```
>
> The below-band eligibility test is `ht(parent)<lo`. Both viability
> and eligibility use the changed threshold in a contest. Paths add
> no support keys. Raw tests, release, saved raw results, and the S
> guard remain unfiltered. The guard tests every live lease. Finality
> does not assign S. The finality acceptance helper retains the r148
> rule; do not replace it with the new choice-band predicate.
>
> The proof uses the same recovery premises as [r150 §1](fgsa-theorem-h.md):
>
> 1. There are n base seats at each label and n fixed, unit-weight FG
>    identities, with one static faulty set of size `a≤f=(n−1) div 3`.
>    All `h=n−a` honest identities participate after GST.
> 2. Paths and signatures are authentic, roots are injective, and parent
>    slots strictly increase. Runs start from the specified initial state.
>    S, leases, saved results, and client records have actual event origins.
>    A completed gate cannot replay.
> 3. After GST, delivery and accepted-object relay take strictly less
>    than Δ. Honest proposal delivery and proposal-view relay readiness
>    hold. Receipts and clocks also run while asleep. Private faulty
>    objects acquire relay duties when an honest reader accepts them.
>    All required windows lie in the execution horizon.
> 4. Each duty uses its own R1 frame. Declared support remains the original
>    declared subset when a proposal is merged. Whole-result guards and
>    persistent exact-entry records follow the executable event order.
> 5. An honest awake proposal occurs strictly after each trigger within G.
>    For arrival, use Rec(g): an honest opening with its next two slot
>    proposers honest, within g rounds. Current-window FG rows are included,
>    `w_F≥1`, and timeout maturity is `2R` slots.
>
> The local healing theorem needs an actual reset but does not need a
> bound for reaching it. The arrival theorems additionally use item 5's
> opening recurrence and the supplied producer. No first-finality
> recurrence theorem is inferred from these premises.
>
> ```text
> τ=(n+1) div 2;          q_F=(2n+2) div 3;
> h≥q_F≥τ>a;             h>2a;             2q_F−n>a;
> Δ>0; k≥2; L=(4k−1)Δ;  R≥3; P=4RΔ;      g≥3;
> t_s=4sΔ; v_s=t_s+Δ; e_s=t_s+2Δ; z_s=t_s+3Δ;
> q_s=t_s+5Δ=v_(s+1);    d_s=t_s+6Δ;       a_r=d_(rR);
> ρ=2L+G+8Δ;             σ=(g+3)P+G+6Δ;
> λ=ρ+2σ;                θ=4Δ;             W=λ+θ;
> δ_H=2L+G−2Δ=ρ−10Δ.
> ```

### 0.3 Glossary: F-numbers (added 2026-09-28)

Two sources use the labels F1, F2, … for different facts.

- The blueprint F-table (bp §3, lines 290–311) numbers DC and SA facts:
  F1 honest row in each QC, F2 causal cap, F3 one justified entry per
  height, F4 finality lock, F5–F10 further DC facts.
- r148 (`fj-redteam.md`) numbers its own claims: F2 = a conflicting
  crossing of j proves that J cannot finalize (PROVED, lines 234–258);
  F3 = the converse, "retain J iff J can still finalize", is REFUTED (lines
  290–309); F4 = "no timeout at H−1" as a proxy for "J can finalize" is
  REFUTED and unsafe for liveness (lines 311–338); F6–F18 are its later
  claims.

In a pinned quote, an F-number belongs to the file of that quote. Every
"F3" or "F4" in the entries of v2 means the blueprint fact: F3 is
`fg.uniqueJust.v1` and F4 is `fg.finalLock.v1`. The r148 phrase
"finalized-crossing law" (line 226) and "finalized crossing" are also
`fg.finalLock.v1`. The FJ entry titles in §4 (F7, F9, F10, F12, F14, F17)
use the r148 numbers. r148 F2 is `fj.crossingNoFinal.v1`.

## Index

`§` is the section of this file. New ids in v2 are listed in §7; the
ids of the f1 splits (2026-09-28) are listed in §8.

"Lean plan" is the scope of the Lean FG module (user decision
2026-09-28, §8). The module is DC-fj: DC's FG without SG and grades, with
the FJ root rule in place of NJ (FRAMEWORK-DESIGN.md §7.1). `DC-fj` = planned
in the DC-fj module (plan `docs/plans/2026-09-28-fg-module.md`);
`none (nj)` = nj research entry, not planned for Lean now; `none` = not
needed by the DC-fj module; `—` = not an entry of the current FG-module
plan (AP-side, composite, or not scheduled).

```text
┌───────────────────────┬──────┬─────────────────────┬───┬───────────┐
│ Id                    │ Var  │ Status 2026-09-28   │ § │ Lean plan │
├───────────────────────┼──────┼─────────────────────┼───┼───────────┤
│ fg.frame.v1           │ nj   │ SUPERSEDED (def)    │ 1 │ none (nj) │
│ fg.frame.v2           │ nj   │ def                 │ 1 │ none (nj) │
│ fg.frameCompat.v1     │ both │ PROVED              │ 1 │ none      │
│ fg.Ret.v1             │ nj   │ def                 │ 1 │ none (nj) │
│ fg.N1.v1              │ nj   │ def                 │ 1 │ none (nj) │
│ fg.N1eff.v1           │ nj   │ def                 │ 1 │ none (nj) │
│ fg.N2.v1              │ nj   │ def                 │ 1 │ none (nj) │
│ fg.N2.v2              │ nj   │ def                 │ 1 │ none (nj) │
│ fg.HNI.v1             │ nj   │ def                 │ 1 │ none (nj) │
│ ap.S.v1               │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.S.v2               │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.Sslow.v1           │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.repair.fixedF.v1   │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.repair.movingF.v1  │ nj   │ OPEN                │ 2 │ —         │
│ ap.L.fixedF.v1        │ nj   │ WITHDRAWN (PROVED)  │ 2 │ —         │
│ ap.L.movingF.v1       │ nj   │ WITHDRAWN (OPEN)    │ 2 │ —         │
│ ap.reach.v1           │ nj   │ OPEN                │ 2 │ —         │
│ ap.source.v1          │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.X.v1               │ nj   │ REFUTED; WITHDRAWN  │ 2 │ —         │
│ ap.Xplus.v1           │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.rowService.v1      │ both │ RULE                │ 2 │ —         │
│ ap.carrierKeep.v1     │ nj   │ WITHDRAWN (PROVED)  │ 2 │ —         │
│ ap.carrierKeep.v2     │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.honestSourced.v1   │ both │ WITHDRAWN (PROVED)  │ 2 │ —         │
│ ap.honestSourced.v2   │ both │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.armedSafe.v1       │ nj   │ PROVED (FG-SA)      │ 2 │ —         │
│ ap.outputRecovered.v1 │ nj   │ WITHDRAWN (PROVED)  │ 2 │ —         │
│ ap.finalityHead.v1    │ nj   │ WITHDRAWN (SKETCH)  │ 2 │ —         │
│ ap.finalityHead.v2    │ nj   │ SKETCH              │ 2 │ —         │
│ ap.fastSupport.v1     │ both │ PROVED (RULE, τ>a)  │ 2 │ —         │
│ fg.provenance.v1      │ both │ SUPERSEDED (PROVED) │ 3 │ —         │
│ fg.provenance.v2      │ both │ PROVED              │ 3 │ DC-fj     │
│ fg.causalCap.v1       │ both │ SUPERSEDED (PROVED) │ 3 │ —         │
│ fg.causalCap.core.v1  │ both │ PROVED; LEAN (DC)   │ 3 │ DC-fj     │
│ fg.uniqueJust.v1      │ both │ LEAN (DC, Lemma U)  │ 3 │ DC-fj     │
│ fg.finalLock.v1       │ both │ LEAN (DC)           │ 3 │ DC-fj     │
│ fg.trunk.v1           │ nj   │ PROVED (a≤f)        │ 3 │ none (nj) │
│ fg.oneBullet.v1       │ nj   │ SUPERSEDED (PROVED) │ 3 │ none (nj) │
│ fg.oneBullet.core.v1  │ nj   │ PROVED (a≤f)        │ 3 │ none (nj) │
│ fg.H19.v1             │ nj   │ PROVED              │ 3 │ none (nj) │
│ fg.HNIb.v1            │ nj   │ PROVED              │ 3 │ none (nj) │
│ fg.base.finalized.v1  │ nj   │ PROVED              │ 3 │ none (nj) │
│ fg.base.nj.v1         │ nj   │ PROVED (FG-SA)      │ 3 │ none (nj) │
│ fg.baseSel.nj.v1      │ nj   │ PROVED (FG-SA)      │ 3 │ none (nj) │
│ fg.accountable.v1     │ both │ PROVED; LEAN (DC)   │ 3 │ DC-fj     │
│ fj.frame.v1           │ fj   │ def                 │ 4 │ DC-fj     │
│ fj.crossingNoFinal.v1 │ fj   │ PROVED              │ 4 │ DC-fj     │
│ fj.descent.v1         │ fj   │ PROVED              │ 4 │ —         │
│ fj.canonical.v1       │ fj   │ PROVED              │ 4 │ —         │
│ fj.inBandLock.v1      │ fj   │ PROVED              │ 4 │ DC-fj     │
│ fj.twoChanges.v1      │ fj   │ SUPERSEDED (PROVED) │ 4 │ —         │
│ fj.twoChanges.core.v1 │ fj   │ PROVED (a≤f)        │ 4 │ DC-fj     │
│ fj.armedSafe.v1       │ fj   │ PROVED              │ 4 │ —         │
│ fg.base.fj.v1         │ fj   │ PROVED              │ 4 │ —         │
│ fj.firstFinality.v1   │ fj   │ SKETCH              │ 4 │ —         │
│ fj.reset.v1           │ fj   │ PROVED              │ 4 │ —         │
│ fj.theoremN.v1        │ fj   │ PROVED              │ 4 │ —         │
│ fj.rise.fixedF.v1     │ fj   │ PROVED              │ 4 │ —         │
│ fj.rise.movingF.v1    │ fj   │ OPEN (impl. PROVED) │ 4 │ —         │
│ fj.Xplus.v1           │ fj   │ PROVED              │ 4 │ —         │
│ fj.healed.v1          │ fj   │ PROVED              │ 4 │ —         │
│ fj.healedUnif.v1      │ fj   │ OPEN (impl. PROVED) │ 4 │ —         │
│ fj.healedAtQ.v1       │ fj   │ OPEN                │ 4 │ —         │
│ comp.provenance.v1    │ both │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.settle.v1        │ both │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.cut.v1           │ both │ PROVED              │ 5 │ —         │
│ comp.rise.fixedF.v1   │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.rise.movingF.v1  │ nj   │ OPEN                │ 5 │ —         │
│ comp.theoremN.v1      │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.fgHealed.v1      │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.healed.v1        │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.healedLit.v1     │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.arrivalNJ.v1     │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.handoffBase.v1   │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
│ comp.healedUnif.v1    │ nj   │ OPEN (impl. PROVED) │ 5 │ —         │
│ comp.healedAtQ.v1     │ nj   │ OPEN                │ 5 │ —         │
│ comp.finality.v1      │ nj   │ SKETCH              │ 5 │ —         │
│ comp.clean.v1         │ nj   │ PROVED (FG-SA)      │ 5 │ —         │
└───────────────────────┴──────┴─────────────────────┴───┴───────────┘
```

## 1. Definitions (`SimplexFG.nj` frame)

These definitions use the NJ frame. FJ has its own frame (`fj.frame.v1`,
§4); these definitions do not apply to it.

### `fg.frame.v1` — duty frame

- Variant `nj`. Source r147 §2, lines 105–119. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional.md, lines 105–119:_
>
> For each honest duty d, take its own R1 view V_d. Compute its controls
> together, as in the rule documents:
>
> ```text
> F_d = current accepted F, with its retained acceptance basis;
> H_d = max({1} ∪ {h(W) : W∈V_d});
> (j_d,J_d) = greatest justified pair in V_d compatible with F_d;
> Z_d = J_d if H_d=j_d+1, else F_d;
>
> D_d = {B∈V_d : F_d⪯B, Z_d⪯B,
>                   ∃W∈V_d, B⪯W and h(W)≥H_d−1}.
>
> Ret_d(B) := B⪯Z_d
>             or (Z_d⪯B and B∈D_d).
> ```

- Status: 2026-09-28 — def. This is the frame of FRAMEWORK-DESIGN.md §7.2.
  bp §1.3 (lines 153–161) has the same frame; there the F test follows from
  the Z test.
- Status: 2026-09-28 — SUPERSEDED by `fg.frame.v2`. The J line of v1 says
  "compatible with F_d"; DC and the spec select with `F_d ⪯ J`.
  `fg.frameCompat.v1` proves that the two rules select the same pair at
  every honest duty view. Thus every entry that uses this frame keeps its
  meaning.

### `fg.frame.v2` — duty frame (J selected with `F_d ⪯ J_d`)

- Variant `nj`. Source spec, section "Duties and handlers", `fg_frame`,
  lines 854–859, and appendix "NJ variant", lines 1408–1417 (the frame
  without a contest). The store rule `update_finality` has the same J
  guard: spec lines 731–752 and DC `update_finality`, dc lines 937–948.
  Files `spec/fgsa-protocol.tex` (sha256
  `ae4497abc7c5b3a6f73697f341bf730a63c7d34bd2f7546154bd022bc95af223`) and
  `dc/consensus.tex` (sha256
  `dc471b47a46896fe0a3df300c188fef1512f475615ce0fc0df18dbea6d2e5517`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Frame (registry form; it is `fg.frame.v1` with the J line changed):

```text
F_d = current accepted F, with its retained acceptance basis;
H_d = max({1} ∪ {h(W) : W∈V_d});
(j_d,J_d) = the lex-greatest (h_j, J.root) justified pair in V_d
            with F_d ⪯ J_d;
Z_d = J_d if H_d=j_d+1, else F_d;

D_d = {B∈V_d : F_d⪯B, Z_d⪯B,
                  ∃W∈V_d, B⪯W and h(W)≥H_d−1}.

Ret_d(B) := B⪯Z_d
            or (Z_d⪯B and B∈D_d).
```

- Statement (pinned):

> _fgsa-protocol.tex, lines 854–859:_
>
> ```latex
>   \State $F\gets\Sigma.F$
>   \Comment{the current accepted $F$}
>   \State $H\gets\max(\{1\}\cup\{\Sigma.\sigma[W].h:W\in V\})$
>   \Comment{this view's own maximum}
>   \State $(j,J)\gets$ the lex-greatest $(\Sigma.\sigma[W].h_j,
>     \Sigma.\sigma[W].J.\rootf)$ over $W\in V$ with $F\preceq\Sigma.\sigma[W].J$
> ```

> _fgsa-protocol.tex, lines 1408–1417:_
>
> ```latex
> \item \fname{fg\_frame} has no contest:
>   \[
>    (Z,\lo)\gets
>    \begin{cases}
>     (J,H-1), & H=j+1,\\
>     (F,H-1), & \text{otherwise}.
>    \end{cases}
>   \]
>   This is the frame \textsf{FRAME} of~\ADJ{2}: the root rule of~\DC{5}
>   and the band $\{H-1,H\}$, computed from the duty's own view.
> ```

> _fgsa-protocol.tex, lines 731–752:_
>
> ```latex
> \Function{update\_finality}{$\Sigma,B$}
>   \Comment{\DC{7}, extended by \ADJ{2}: F basis}
>   \State $\sigma\gets\Sigma.\sigma[B]$
>   \State $\Sigma.\hmax\gets\max(\Sigma.\hmax,\sigma.h)$
>   \Comment{archival; no duty frame reads it}
>   \If{$\Sigma.F\preceq\sigma.J$ \textbf{and}
>       $(\sigma.h_j,\sigma.J.\rootf)>(\Sigma.h_j,\Sigma.J.\rootf)$}
>     \State $(\Sigma.J,\Sigma.h_j)\gets(\sigma.J,\sigma.h_j)$;
>       $\Sigma.\jCarrier\gets B$
>     \Comment{lex order}
>   \EndIf
>   \If{$\Sigma.F\prec\sigma.F$ \textbf{and} $\sigma.F\preceq\Sigma.J$
>       \textbf{and} $\sigma.F\in\Call{viable\_tree}{\Sigma}$}
>     \State $\Sigma.F\gets\sigma.F$
>     \Comment{does not change $S$ or leases}
>     \State $W\gets$ the $W\in\Sigma.\TF$ with $\sigma.F\preceq W$ of
>       greatest $\Sigma.\sigma[W].h$
>     \Comment{ties by root}
>     \State $\Sigma.\fBasis\gets\{B,\Sigma.\jCarrier,W\}$
>     \Comment{carrier, J carrier, witness}
>   \EndIf
> \EndFunction
> ```

> _consensus.tex, lines 937–948:_
>
> ```latex
> \Function{update\_finality}{$\Sigma,\sigma$}
>   \State $\Sigma.\hmax\gets\max(\Sigma.\hmax,\sigma.h)$
>   \If{$\Sigma.F\preceq\sigma.J$ \textbf{and}
>       $(\sigma.h_j,\sigma.J.\rootf)>(\Sigma.h_j,\Sigma.J.\rootf)$}
>     \Comment{lex order}
>     \State $(\Sigma.J,\Sigma.h_j)\gets(\sigma.J,\sigma.h_j)$
>   \EndIf
>   \If{$\Sigma.F\prec\sigma.F$ \textbf{and} $\sigma.F\preceq\Sigma.J$
>       \textbf{and} $\sigma.F\in\Call{viable\_tree}{\Sigma}$}
>     \State $\Sigma.F\gets\sigma.F$
>   \EndIf
> \EndFunction
> ```

- Status: 2026-09-28 — def. It replaces `fg.frame.v1`; `fg.frameCompat.v1`
  proves that both select the same pair.
- Note: the fj counterpart is `fj.frame.v1`. It already selects J with
  `F ⪯ σ[W].J` (r148 `FJ_FRAME`, lines 151–152). `fg.frameCompat.v1`
  applies to both frames. The pinned `fg_frame` lines also
  compute the FJ frame; the NJ variant (lines 1408–1417) removes only the
  contest.
- Note: spec line 357 says "compatible", but the code of lines 736–737 and
  858–859 tests `F ⪯ J`:

> _fgsa-protocol.tex, lines 356–357:_
>
> ```latex
> $(\Sigma.F,\Sigma.J,\Sigma.h_j)$ are the accepted finalization and the
> lex-greatest justification compatible with it, as in~\DC{5}.
> ```

### `fg.frameCompat.v1` — "compatible with F" and "`F ⪯ J`" select the same pair

- Variant `both`. Source: registry, 2026-09-28. No source file states this
  lemma; the argument is below. Rule sources: dc lines 747–748, 762–767,
  820, 824 and 838 (checkpoint heights); spec lines 361–365 and 494 (F
  basis in every duty view); spec lines 736–750 (J guard and F basis).
  Hashes as in `fg.frame.v2`.
- Lean plan: none (user 2026-09-28). The DC-fj module states the frame
  with `F ⪯ J` (`fj.frame.v1`), so it does not need this lemma.
- Hypotheses: R1 duty views (`env.r150` item 4; spec lines 483–495); the
  F-basis rule of spec lines 742–750; the DC chain state (bp F5: one
  height per block; the entry `T_h` is the block that entered h). It does
  not use `a≤f`.
- Statement (registry): let d be an honest duty with view V_d and current
  accepted F = F_d. Let P1 be the greatest `(h_j, J.root)` justified pair
  in V_d whose J is compatible with F (the `fg.frame.v1` rule). Let P2 be
  the lex-greatest such pair with `F ⪯ J` (the `fg.frame.v2` rule). Then
  P1 = P2. The same holds for the FJ frame: the wording "compatible with
  F" of `env.r151` (r151 line 44) and the `F ⪯ σ[W].J` test of
  `fj.frame.v1` select the same pair.
- Proof (registry, 2026-09-28).
  1. Checkpoint heights. A justified pair is `(h, T_h)` of a chain state
     (dc line 824). `T_h` is the block that brought its chain into height
     h (dc lines 747–748, 838), so `σ[T_h].h = h`. A finalized pair is a
     former justified pair (dc line 820). The only exception is the
     initial pair `(0, genesis)`, with `σ[genesis].h = 1` (dc lines
     762–767). Thus each pair `(h,C)` has `h ≤ σ[C].h`, with equality when
     C ≠ genesis. Heights do not decrease along a chain, and a non-genesis
     entry T is the first block of its height on its chain. So every
     strict ancestor of T has state height at most `σ[T].h − 1`.
  2. Part (i): if `h_J ≥ h_F`, then "J is compatible with F" ⇔ `F ⪯ J`.
     The direction ⇐ is immediate. For ⇒, suppose `J ≺ F` strictly. Then
     F ≠ genesis, so `h_F = σ[F].h`, and step 1 gives
     `h_J ≤ σ[J].h ≤ h_F − 1`. This contradicts `h_J ≥ h_F`.
  3. Part (ii): V_d holds a pair with `F ⪯ J` and `h_J ≥ h_F`. If F is
     genesis, every pair has `F ⪯ J` and `h_J ≥ 0 = h_F`. Otherwise
     `update_finality` accepted F only with `σ.F ⪯ Σ.J` (spec line 742).
     The F basis saved the J carrier W0, with `σ[W0].J = Σ.J` (spec lines
     736–739, 749). R1 puts the F basis in every duty view (spec lines
     363–365; HEAD view item 5, line 494; a full view holds every admitted
     block). If `Σ.J = F` as blocks, then `h_J = h_F` (step 1, F ≠
     genesis). If `F ≺ Σ.J`, then `h_J = σ[Σ.J].h ≥ σ[F].h = h_F`.
  4. Each candidate of P2 is a candidate of P1, so P2 ≤ P1. Step 3 gives
     `h(P2) ≥ h_F`, so `h(P1) ≥ h_F`. Step 2 gives `F ⪯ J` for P1, so P1
     is a candidate of P2 and P1 ≤ P2. Thus P1 = P2. ∎
- Status: 2026-09-28 — PROVED (registry argument; no Lean certificate).
- Note: part (ii) needs the F basis in the view. A view without it can
  select a different pair; R1 excludes such a view at an honest duty. The
  argument reads "greatest" in `fg.frame.v1` as the lex order
  `(h_j, J.root)` of DC §5.

### `fg.Ret.v1` — keep predicate

- Variant `nj`. Source r147 §2, lines 117–125. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned; lines 117–118 are inside the frame block above):

> _fgsa-conditional.md, lines 117–118:_
>
> ```text
> Ret_d(B) := B⪯Z_d
>             or (Z_d⪯B and B∈D_d).
> ```

> _fgsa-conditional.md, lines 121–125:_
>
> The first arm of Ret allows the root to move past B along B's chain.
> It is therefore weaker than requiring B to remain a member of D_d.
> The second arm requires a band witness in **this** view. Compatibility
> with F and Z alone is insufficient. Ancestor closure supplies the path
> from Z_d to B in this arm.

- Status: 2026-09-28 — def. It is equivalent to
  `Kept_d(B) ⇔ B ⪯ Z_d or B ∈ D_d` (bp §1.3, lines 163–167; r149 §1, line
  85), because `B ∈ D_d ⇒ Z_d ⪯ B` (bp §10, lines 1065–1067). Lemma K of bp
  §7.3 (the one-duty keep lemma) proves Kept at every honest duty after the
  reset.

### `fg.N1.v1` — literal static controls

- Variant `nj`. Source r147 §2, lines 127–138. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional.md, lines 127–138:_
>
> **N1(u,v;m,F,Z): static controls.** At every honest proposal, HEAD, and
> FG choice duty in `[u,v]`, `H_d=m`, `F_d=F`, and `Z_d=Z`. R1 and the
> retained-F-basis rule continue to hold. Each duty computes D_d from its
> own view. The full archival honest frontier is m until the stopping
> event under consideration. Views, block sets, scores, leases, and raw
> results need not be equal. New blocks and band witnesses may arrive.
> The unused lower justified pair need not be fixed when Z=F.
>
> N1 concerns the selection rule, not literal equality of D_d. This matters:
> the honest proposal itself must enter later views. A static filter may
> also exclude an old lease target below the band. No claim that all old
> protected blocks remain eligible is part of N1.

- Status: 2026-09-28 — def.

### `fg.N1eff.v1` — effective static filter

- Variant `nj`. Source bp §1.3 and §2.1, lines 169–172 and 178–187. File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`. The
  same condition is r149 §1, lines 94–97 (in `env.r149`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 169–172:_
>
> **Definition (effective filter).** For a duty d put
> `Ẑ_d = J_d` if `H_d = j_d+1` (J-mode), and `Ẑ_d = ◇` otherwise (F-mode).
> The effective filter is `Φ_d = (H_d, Ẑ_d)`. In F-mode, F_d is not part of
> Φ_d. Section 4 shows that this omission is harmless.

> _fgsa-healing-blueprint.md, lines 178–187:_
>
> **(N1) Static effective filter.** For times u≤v, a frontier m≥1, and
> `Ẑ ∈ {◇} ∪ Blocks`, (N1)(u,v;m,Ẑ) holds iff every honest duty d with
> t_d∈[u,v] satisfies: the honest frontier at t_d exceeds m, or
> `Φ_d = (m,Ẑ)`.
>
> (N1) permits these changes: arbitrary view growth, lease paths that enter
> or leave a HEAD view, F advances in F-mode (they are below the band, §4.1),
> lower J changes, and a finalization of J_(m−1) in J-mode. It forbids a
> change of the band threshold at a frontier that has not risen, and a
> change between the two modes.

- Status: 2026-09-28 — def.

### `fg.N2.v1` — source-closed preservation (Ret form)

- Variant `nj`. Source r147 §2, lines 140–158. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional.md, lines 140–158:_
>
> **N2(C,s;a_r,t): preservation for one source.** Let `s=rR` and
> `a_r=d_s`. Require Ret_d(C) at every honest transfer HEAD at q_s, and
> at every subsequent honest choice duty through t. Equivalently this is
> preservation on `[q_s,t]`, with the first transfer HEAD included. This
> condition refers only to F_d, Z_d, H_d, V_d, and their domain predicate;
> it does not assert that any actual HEAD or S already contains C.
>
> For a family of rows, **N2(u,t)** means N2(C,s;a_r,t) for each honest
> nonempty height row with `a_r∈[u,t]` and its selected fresh source C.
> This definition includes the source boundary of each row. In particular,
> the first row's q_s can be one Δ before u.
>
> This boundary is essential to the statement being proved. A condition
> only on duties whose wall-clock times are in `[a_r,t]` does not supply a
> premise about the already completed HEAD at `q_s=a_r−Δ`. When this file
> says “N2 on `[a_r,t]`”, it means the explicit source-closed definition
> above. It does not silently infer that earlier HEAD from future controls.
> An alternative interface is Ret at q_s as a separate premise, followed
> by ordinary forward preservation on `[a_r,t]`.

- Status: 2026-09-28 — def. Used by `ap.S.v1`.

### `fg.N2.v2` — preservation of one body or a set (Kept form)

- Variant `nj`. Source r149 §1, lines 90–92; set form bp §2.1, lines
  189–192. Files `fgsa-conditional-close.md` (sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`) and
  `fgsa-healing-blueprint.md` (sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 90–92:_
>
> `N2(B;q_s,t)` requires Kept at every honest HEAD, proposal, FG source
> choice, and finality-head read in `[q_s,t]`. It includes the first HEAD
> at `q_s`. It imposes no condition on a later duty outside this interval.

> _fgsa-healing-blueprint.md, lines 189–192:_
>
> **(N2) Protected blocks are kept.** Let 𝒫 be a set of blocks, each with a
> start time q(B). (N2)(𝒫;t) holds iff every B∈𝒫 is kept at every honest
> duty d (HEAD, proposal, FG action, or finality head) with
> `q(B) ≤ t_d ≤ t`.

- Status: 2026-09-28 — def. Used by `ap.S.v2`, `ap.Sslow.v1` and
  `comp.theoremN.v1`. It differs from `fg.N2.v1`: it names every honest
  HEAD, proposal, FG source choice and finality-head read, it applies to any
  body, and its interval starts at `q_s` for every `t ≥ q_s`.

### `fg.HNI.v1` — height-m noninterference

- Variant `nj`. Source bp §7.9, lines 790–801. File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 790–801:_
>
> **Definition (HNI).** For a height m ≥ 1, *height-m noninterference*,
> HNI(m), holds iff, over the whole run:
>
> - (h1) every justified entry at height m−1 precedes every valid block of
>   height ≥ m; and
> - (h2) every finalized checkpoint of height ≤ m−1 precedes every valid
>   block of height ≥ m.
>
> HNI(m) speaks only about FG objects **below** m. It says that they never
> separate blocks at height ≥ m. It does not say when an honest node learns
> of such an object. A justified entry at a height < m−1 needs no clause:
> it is never the root at a view with `H_d ≥ m`.

- Status: 2026-09-28 — def.

`HeightRetains(m)` (v5) is REFUTED once the frontier passes m (bp §7.9, H22,
lines 865–878) and is withdrawn.

## 2. AP-side entries

These entries use the NJ frame of §1 in their premises. The FJ analogues are
in §4. Every status below is for the FG-SA client (§0).

### `ap.S.v1` — (S) for row sources, r147 form

- Variant `nj`. Source r147 §3, lines 170–181. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N2.v1` for C on `[q_s,t]`; `t ≥ a_r`.
- Statement (pinned):

> _fgsa-conditional.md, lines 170–181:_
>
> **Exact statement (S).** Under §1, let an honest nonempty height row at
> `a_r=d_s≥GST`, `s=rR`, use fresh fast source C from a synchronous label s.
> Let `t≥a_r`, and assume N2(C,s;a_r,t). Every honest HEAD emitted at a
> scheduled HEAD duty in `[q_s,t]` contains C. Every honest S that contains
> C immediately after d_s retains C through t. If `t≥d_(s+1)`, every
> honest S contains C at every time in `[d_(s+1),t]`, where
> `d_(s+1)=t_s+10Δ`. These conclusions hold for both a target row and a
> timeout row. Its named entry `T=σ[C].T_h⪯C` inherits them.
>
> “HEAD from q_s” refers to emitted HEAD duties. It does not assert that
> an arbitrary full-view recomputation between duties is an emission.
> “By +10Δ” is subject to the horizon and `t≥+10Δ` guards just stated.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §3 and its claim table).
- Scope: row sources only, at FG action labels. It does not cover every fast
  body, slow bodies, or proposal parents. `comp.fgHealed.v1` does not use it
  (audit W05); it uses `ap.S.v2` and `ap.Sslow.v1`.

### `ap.S.v2` — (S) at every fast-write label

- Variant `nj`. Source r149 §2.1, lines 130–141. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: `env.r149`; `fg.N2.v2` for B on `[q_s,t]`; `t_s ≥ GST`;
  `t ≥ q_s`; a fast write at `d_s` (so the execution reaches `d_s`).
- Statement (pinned):

> _fgsa-conditional-close.md, lines 130–141:_
>
> **(S) — PROVED.** Let B be a successful fast body at any label s with
> `t_s ≥ GST`: `B ∈ FastWrite_i[s]` for an honest i. Assume the recovery
> execution premises through the times used, and let `t ≥ q_s`. If
> `N2(B;q_s,t)` holds, then:
>
> 1. **S1:** every honest emitted HEAD in `[q_s,t]` contains B.
> 2. **S2:** every honest proposal P at slot u with `u ≥ s+2` and
>    `t_u ≤ t` has `B ⪯ parent(P)`.
> 3. **S3:** every honest S at each time in `[d_(s+1),t]` contains B.
>
> An interval with its lower endpoint above t contributes no conclusion.
> No requirement that s be a multiple of R occurs in this statement.

- Status: 2026-09-28 — PROVED (FG-SA; r149 §2, claim table line 28).
- Notes: the proof (r149 §2.2–§2.8) uses only the Kept premise, the release
  at τ, raw same-label compatibility and the S guard. It holds at labels
  without an FG action. It implies `ap.S.v1` for row sources (r149 lines
  152–154).

### `ap.Sslow.v1` — (S_slow) for a wholly synchronous slow window

- Variant `nj`. Source r149 §2.1, lines 143–150. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: as `ap.S.v2`, with a successful slow write at s and every
  label in `[s−k+1,s]` synchronous.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 143–150:_
>
> **(S_slow) — PROVED.** The same three conclusions hold when B has a
> successful slow write at label s and every label in `[s−k+1,s]` is
> synchronous. Later used labels are synchronous as well. The N2 interval
> still starts at `q_s`, not at the beginning of the slow window.
>
> For the blueprint's protected set, require `s−k+1 ≥ s*` and
> `t_(s*) ≥ GST`. Thus a window contained in `[s*,∞)` suffices. If “wholly
> after s*” is read strictly, `s−k+1 > s*` is a sufficient stronger premise.

- Status: 2026-09-28 — PROVED (FG-SA; r149 §2.4, claim table line 29).

### `ap.repair.fixedF.v1` — base repair by u+ρ under literal N1

- Variant `nj`. Source r147 §4, lines 285–287, 339–345 and 400–405. File
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N1.v1` from `u ≥ GST` on the interval used;
  stop at the first rise of the honest frontier.
- Service statement: the first honest proposal p strictly after T* has
  exact honest HEAD service and a fresh fast write at every honest reader
  by `p+6Δ ≤ u+ρ`; every later honest proposal whose service interval
  stays under N1 has the same service.
- Statement (pinned):

> _fgsa-conditional.md, lines 285–287:_
>
> Assume N1 from `u≥GST` on a sufficiently long interval, and stop the
> argument if the honest frontier rises. Do not require every old lease
> to be inside D_d.

> _fgsa-conditional.md, lines 339–345:_
>
> Choose the first honest proposal at time p strictly after T*, within G.
> Both proposal times lie on the 4Δ grid, so `p≥T*+4Δ>E_old`.
> Consequently
>
> ```text
> p+6Δ ≤ T*+G+6Δ ≤ u+2L+G+8Δ = u+ρ.
> ```

> _fgsa-conditional.md, lines 400–405:_
>
> Repeat the same comparison for later honest proposals while N1 lasts.
> It gives exact service, fresh fast writes, and the usual safe S suffix
> inside the domain. A later genuine result covers the last supported
> honest proposal; its guard passes because every live target has such
> support or precedes Z. This is local repair and continuation, not a
> claim about a later change of filter.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §4 "Base repair under N1 —
  PROVED").
- Kind: AP service fact (audit W02). It states no height rise.

### `ap.repair.movingF.v1` — base repair by u+ρ under effective N1

- Variant `nj`. Sources: r149 §4.4, lines 444–446 (file
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`); r150
  §5, lines 441–443 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Hypotheses: `env.r149`; `fg.N1eff.v1` from `u ≥ GST` until the first
  rise; the initial reachable base state at u is arbitrary.
- Service statement: as `ap.repair.fixedF.v1`, with `fg.N1eff.v1` in place
  of `fg.N1.v1` (F may advance below the band).
- Statement (pinned):

> _fgsa-conditional-close.md, lines 444–446 (excerpt; line breaks reflowed):_
>
> Once exact service under effective N1 is available, r147's height
> production proof has no further F-constancy use

> _fgsa-theorem-h.md, lines 441–443 (excerpt; line breaks reflowed):_
>
> If Reach(m) is proved with the quantifiers above, r149 §4.2 supplies the
> remaining lease and ordinary-parent facts, and (X+) supplies repair by
> `w+ρ`.

- Status: 2026-09-28 — OPEN (r149 claim table lines 32–33: effective (L)
  OPEN, the proposed M1 exact-service argument SKETCH; r150 §5).
- Notes: r149 §4.1 (source support under effective N1) and §4.2 (lease
  and ordinary-parent facts after the two-lease boundary) are PROVED. The
  missing step is x3 at the service reads, that is, `ap.reach.v1`.
  `ap.reach.v1` ⇒ this entry, by `ap.Xplus.v1` (r150 lines 441–443).
- Kind: AP service fact (audit W02).

### `ap.L.fixedF.v1` — (L) under literal N1

- Variant `nj`. Source r147 §5, lines 409–429. File `fgsa-conditional.md`,
  sha256 `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147` (with premises 4 and 5); `fg.N1.v1` with F and Z
  fixed on `[u,min(t_up,u+B_static))`; `u ≥ GST`.
- Statement (pinned):

> _fgsa-conditional.md, lines 409–429:_
>
> **Exact statement (L).** Under §1, let `u≥GST` and let the honest
> archival frontier at u be m. Let t_up be the first later time at which
> that frontier exceeds m, or infinity if there is none. Suppose fixed
> F and Z make N1 hold on `[u,min(t_up,u+B_static))`, and suppose the
> execution premises and horizon are available through `u+B_static`.
> Then `t_up≤u+B_static`; that is, a rise above m occurs by
>
> ```text
> u+B_static = u+ρ+2σ,
> ρ = 2L+G+8Δ,     σ = (g+3)P+G+6Δ.
> ```
>
> If no earlier rise ends the interval, base repair completes by u+ρ.
> Every later honest proposal whose full service interval remains in
> that interval receives exact honest HEAD service and a fresh fast
> write at all honest readers at its +6Δ gate. A selected honest
> opening supplies `C_fg` and a nonempty matching target or timeout row
> at every honest validator. Its next two honest slot proposers carry
> the branch and fold the rows. At most two such production steps are
> needed to exceed m. Statements about duties after the first rise are
> not part of (L).

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5). r149 §4.4 (lines 443–445)
  confirms that the literal-N1 form stays PROVED.
- Scope: this entry states FG height progress. It is not a family entry
  (§0); it holds for the Simplex policy only.
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED but
  is misfiled: it states a height rise. It is refiled as
  `comp.rise.fixedF.v1`; its service parts are `ap.repair.fixedF.v1`,
  `ap.source.v1`, `ap.rowService.v1` and `ap.carrierKeep.v2`.

### `ap.L.movingF.v1` — (L) under effective N1

- Variant `nj`. Source r149 §4.4, lines 436–441. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: `env.r149` (all liveness premises); `fg.N1eff.v1` on
  `[u,u+λ]`; `u ≥ GST`.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 436–441:_
>
> > **(L), OPEN under effective N1.** Set `u_L=GST` and
> > `λ=ρ+2σ`, where `σ=(g+3)P+G+6Δ`. For every `u≥u_L`, m, and Zhat,
> > if the honest archival frontier at u is m and
> > `N1(u,u+λ;m,Zhat)` holds, then the frontier at `u+λ` exceeds m.
> > All execution, proposer, row-inclusion, and horizon premises in §1
> > apply. The initial reachable base state at u is arbitrary.

- Status: 2026-09-28 — OPEN (r149 claim table line 32; r150 claim table line
  25). The proposed M1 argument is SKETCH (r149 line 33).
- Notes: r149 §4.1 PROVES source support under effective N1 and lower F
  advances. The missing step is transport of the viable tree between the
  proposal view and an R1 HEAD view with a new F basis (r149 §4.3, lines
  417–424). `ap.reach.v1` is a sufficient lemma. bp marks the same claim H16
  SKETCH (bp §10, lines 1086–1101); r149 §4.3 shows that the bp argument
  misses one case. Scope as `ap.L.fixedF.v1`.
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays OPEN but is
  misfiled: it states a height rise. It is refiled as
  `comp.rise.movingF.v1`; its missing service part is
  `ap.repair.movingF.v1`.

### `ap.reach.v1` — common supported band prefix before the reset

- Variant `nj`. Source r150 §5, lines 400–414. File `fgsa-theorem-h.md`,
  sha256 `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.
- Hypotheses: `env.r150`; `fg.N1eff.v1` until the first rise or the service
  deadline; frontier m at `w ≥ GST`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 400–414:_
>
> Let the frontier at `w≥GST` be m, and suppose effective N1 holds
> until the first rise or the required service deadline. Let b be the
> first proposal label strictly after w and put `ℓ=b+2k−1`. For each
> honest proposal Q at `t_j>t_ℓ` used in the local repair and production
> argument, with its service interval before the rise, the missing
> sufficient lemma is:
>
> > **Reach(m).** There exists a block T that precedes the proposal
> > parent, is present and kept at the proposal and every same-slot
> > HEAD read, has `ht(T)≥m−1`, and is contained in every honest
> > label-(j−1) HEAD.
>
> This is x3 at the service reads. It must hold for every reachable
> initial state at w, without a previous reset, without an earlier
> successful honest repair, and without literal F constancy.

- Status: 2026-09-28 — OPEN (r150 claim table line 24).
- Implication, pinned from r150 §5, lines 441–450, PROVED:

> _fgsa-theorem-h.md, lines 441–450:_
>
> If Reach(m) is proved with the quantifiers above, r149 §4.2 supplies
> the remaining lease and ordinary-parent facts, and (X+) supplies
> repair by `w+ρ`. The r147 production argument then costs at most σ
> per promotion. Two promotions exceed m. Thus the precise conditional
> claim is
>
> ```text
> Reach(m) for every required service use
>   ⇒ effective (L) with u_L=GST and λ=ρ+2σ.
> ```

### `ap.source.v1` — each honest opening is a common fresh fast source

- Variant `nj`. Source r147 §5 "Common fresh source", lines 435–449. File
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; a completed repair (`ap.repair.fixedF.v1`; under
  effective N1, `ap.repair.movingF.v1`, OPEN); the opening's service
  interval stays under N1.
- Service statement: from the repair on, for each honest opening at
  `p = T_r`, every honest validator has a fresh fast write of the opening
  block B at `a_r = p+6Δ`, and its source choice is B: `C_fg(i,r) = B` for
  every honest i.
- Statement (pinned):

> _fgsa-conditional.md, lines 435–440 (excerpt; line breaks reflowed):_
>
> After the repair in §4, choose a Rec(g) opening at `p=T_r`.

> _fgsa-conditional.md, lines 437–440 (excerpt; line breaks reflowed):_
>
> Section 4 gives every reader the raw result B and a fresh fast write at
> `a_r=p+6Δ`. B is in the action domain. Its fresh deadline is strictly
> greater than a_r. Every fast-written block at this label is a prefix of B,
> so the deepest candidate is exactly B:

> _fgsa-conditional.md, line 443:_
>
> ```text
> For all honest i: C_fg(i,r)=B.
> ```

> _fgsa-conditional.md, lines 447–449:_
>
> This is a source at **every** honest validator, not one reader's raw
> quorum relabelled as a public certificate. No FG source is required
> at earlier actions during the repair interval.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5) under literal N1. Under
  effective N1 it holds once `ap.repair.movingF.v1` holds (r149 lines
  444–446).
- Kind: AP service fact (audit W02). The height of B and the row that
  the Simplex client emits from it are not part of this entry; they are
  used in `comp.rise.fixedF.v1`.

### `ap.X.v1` — exact service from (x1) and (x2) only

- Variant `nj`. Source r149 §5.1, lines 463–467 (the bp claim of bp §2.4,
  lines 248–256). File `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 463–467:_
>
> > **(X), REFUTED.** Let P be an honest proposal at slot u after GST with
> > parent A. If (x1) every honest live lease target at `v_u` is a prefix
> > of A, and (x2) at the proposal read and every honest HEAD at `v_u`,
> > `Z_d ⪯ A` and `h(A) ≥ H_d−1`, then every honest HEAD at `v_u` names P
> > and every honest S contains P at `d_u`.

- Status: 2026-09-28 — REFUTED (r149 §5.2–§5.3, a reachable integer
  execution with `n=4, a=1, Δ=16`; rechecked in r150 §8, lines 625–633).
- Status: 2026-09-28 — WITHDRAWN (audit W03). No composite may cite it. The
  replacement is `ap.Xplus.v1`.

### `ap.Xplus.v1` — exact service with x0 and x3

- Variant `nj`. Source r149 §6, lines 632–644. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: synchronous proposal delivery; proposal-view relay readiness;
  (x1) and (x2) as in `ap.X.v1`; (x0) and (x3) as pinned.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 632–644:_
>
> **(X+) — PROVED.** Let P be an honest proposal at slot u, with parent A.
> Assume synchronous proposal delivery and proposal-view relay readiness,
> (x1), (x2), and these two extra conditions:
>
> - **(x0)** A is the ordinary proposal walk result, with its lease start
>   removed.
> - **(x3)** There is a prefix T of A, present in the compared views, with
>   `h(T) ≥ max_d H_d−1`, where d ranges over the proposal and same-slot
>   HEAD reads. Every honest label-(u−1) HEAD contains T. At the proposal
>   read and each HEAD root, T is kept.
>
> Then every honest HEAD at `v_u` names P, and every honest S contains P
> at `d_u`.

- Status: 2026-09-28 — PROVED (FG-SA; proof r149 lines 646–677; r150 claim
  table line 18).
- Use rule (audit W03): a composite that uses this entry must prove x0, x1,
  x2 and x3 at each call. `comp.healed.v1` does this after the reset (r150
  §3). Before the reset, x3 is `ap.reach.v1` (OPEN); r149 §6 (lines 692–695)
  does not prove it.

### `ap.rowService.v1` — honest row inclusion

- Variant `both` (a proposer rule; FJ keeps it, r148 §2). Source r147 §1,
  premise 5, lines 76–80. File `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Statement (pinned):

> _fgsa-conditional.md, lines 76–80:_
>
> 5. Honest proposals include the specified current-window rows from the
>    pool and from held current-window blocks, except rows already on the
>    parent chain. Use `w_F≥1`, full-row deduplication, and distinct FG
>    identities. A faulty carrier may use old authentic rows. Stored
>    progress bits persist until that chain advances height.

- Status: 2026-09-28 — RULE. [async] RULE means true by the honest
  proposer's code, not a theorem. Its timed form is a premise of
  `comp.rise.fixedF.v1`.

### `ap.carrierKeep.v1` — carriers and maturity under N1

- Variant `nj`. Source r147 §5 "Carriers and maturity", lines 485–501. File
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N1.v1`; exact service after the r147 §4
  repair.
- Statement (pinned):

> _fgsa-conditional.md, lines 485–501:_
>
> **Carriers and maturity.** Let B1 and B2 be the honest proposals at
> p+4Δ and p+8Δ. Exact service keeps their parent chains above B. The
> round-r rows arrive before p+7Δ. B2 includes them unless its parent
> already includes them. If the chain still has height j, its entry
> remains T, so it folds at least q_F distinct matching identities.
> If it has already left j, the desired one-height promotion has occurred
> on this selected chain. Rows at different entries are never added.
>
> A target quorum can be consumed immediately. Otherwise the stored
> progress quorum is consumed once the chain's slot reaches
> `T.slot+2R`. Since `T⪯B`, this deadline is no later than p+2P.
> Select an honest proposal Q strictly after p+2P, within G. The branch
> from B2 remains selected: B2 itself had exact service and fresh fast
> support, and N1 retains its in-band path. If that branch is still at j,
> Q consumes its stored quorum. Otherwise it is already at least j+1.
> Q's +6Δ service establishes a common fast-supported block of height
> at least j+1 for the next step.

- Status: 2026-09-28 — PROVED (FG-SA; part of the r147 §5 proof of (L)).
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED but
  mixes block retention with FG entries, maturity and a rise. The block
  retention part is `ap.carrierKeep.v2`; the rest is in
  `comp.rise.fixedF.v1`.

### `ap.carrierKeep.v2` — the selected chain keeps the honest carrier blocks

- Variant `nj`. Source r147 §5 "Carriers and maturity", lines 485–486 and
  496–498. File `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses: `env.r147`; `fg.N1.v1`; `ap.repair.fixedF.v1`;
  `ap.source.v1` for the opening B at p.
- Service statement: let B1 and B2 be the honest proposals at `p+4Δ` and
  `p+8Δ`, and Q an honest proposal strictly after `p+2P`, within G. By
  exact service, the parent chains of B1 and B2 stay above B. At Q, the
  branch from B2 is still selected while N1 holds.
- Statement (pinned):

> _fgsa-conditional.md, lines 485–486 (excerpt; line breaks reflowed):_
>
> Let B1 and B2 be the honest proposals at p+4Δ and p+8Δ. Exact service
> keeps their parent chains above B.

> _fgsa-conditional.md, lines 496–498 (excerpt; line breaks reflowed):_
>
> Select an honest proposal Q strictly after p+2P, within G. The branch from
> B2 remains selected: B2 itself had exact service and fresh fast support,
> and N1 retains its in-band path.

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5).
- Kind: AP service fact (audit W02): block retention only. Row folding
  is `ap.rowService.v1`; entries, maturity and consumption are Simplex
  transition facts, used in `comp.rise.fixedF.v1`.

### `ap.honestSourced.v1` — one fresh source per action

- Variant `both` (FJ keeps the `C_fg` rule, r148 §2). Sources: r143 §3.1,
  lines 226–244 (the rule), and r143 §10.1, lines 846–851 (compatibility).
  File `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`.
- Statement (pinned):

> _fgsa-fast.md, lines 226–244:_
>
> At the FG action a_r, after the scheduled gate, put s=rR. This is the
> latest scheduled SA gate, including a gate that returned no result. Use:
>
> ```text
> Candidates = {B∈D_action : B∈FastWrite_i[s] and E_i(B)>a_r};
> C_fg = deepest candidate, or none if Candidates is empty.
> ```
>
> No older set may replace an empty `FastWrite_i[s]`. Sleeping does not make
> an old gate the latest gate. The candidates lie on the local raw result's
> ancestor path, so the deepest choice is unique. A deterministic root tie
> rule can be retained but is not needed on a valid local path.
>
> B need not have slot s. In particular, the source can be an old block with
> a fresh fast renewal. Its immutable entry `T=σ[B].T_h` can be older still.
> The height pair uses `(σ[B].h,T,σ[B].nj)`, not the source's slot and not
> the cache maximum. The source qualification applies before every client
> branch. A repeat still needs a current fresh source, but **the named entry
> does not need a new lease or a new slot**.

> _fgsa-fast.md, lines 846–851:_
>
> Two same-round fresh sources are prefixes of synchronous same-label
> genuine results. They are compatible. If their source heights are H+1,
> immutable entry equality on a plateau gives the same T. No G2/genuine
> comparison remains. The proof also covers a present source whose pair is
> empty; at this first new height an incompatible lock cannot precede all
> honest rows, since its QC would contain an earlier honest target.

- Status: 2026-09-28 — PROVED (FG-SA; r143 §10.1 "PROVED locally"; r146
  claim 4, freshness equivalence, PROVED).
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED
  but includes Simplex client and transition facts. The service part is
  `ap.honestSourced.v2`.

### `ap.honestSourced.v2` — one fresh source per action (service form)

- Variant `both` (FJ keeps the `C_fg` rule, r148 §2). Source r143 §3.1,
  lines 226–237, and §10.1, lines 846–847. File `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`.
- Statement (pinned):

> _fgsa-fast.md, lines 226–237:_
>
> At the FG action a_r, after the scheduled gate, put s=rR. This is the
> latest scheduled SA gate, including a gate that returned no result. Use:
>
> ```text
> Candidates = {B∈D_action : B∈FastWrite_i[s] and E_i(B)>a_r};
> C_fg = deepest candidate, or none if Candidates is empty.
> ```
>
> No older set may replace an empty `FastWrite_i[s]`. Sleeping does not make
> an old gate the latest gate. The candidates lie on the local raw result's
> ancestor path, so the deepest choice is unique. A deterministic root tie
> rule can be retained but is not needed on a valid local path.

> _fgsa-fast.md, lines 846–847 (excerpt; line breaks reflowed):_
>
> Two same-round fresh sources are prefixes of synchronous same-label
> genuine results. They are compatible.

- Status: 2026-09-28 — PROVED (FG-SA; r143 §10.1 "PROVED locally"; r146
  claim 4).
- Kind: AP service fact (audit W02). v1 also pinned the height-pair fields
  and the equality of entries on a plateau; those are Simplex client and
  transition facts (`fg.provenance.v1`, bp §7.5).
- Note (2026-09-28): `fg.provenance.v1` is SUPERSEDED. The client and
  entry facts are `fg.provenance.v2` and `comp.provenance.v1`.

### `ap.armedSafe.v1` — clean safety and P1 with the FG

- Variant `nj`. Source r146 §3, claims 1a–1c, lines 26–28 (claim table),
  359–364 and 389–392. File `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 26–28:_
>
> ```text
> │ 1a │ Clean safety and monotonicity, all a<h          │ PROVED  │
> │ 1b │ Clean honest-proposal inclusion in 6Δ, all a<h  │ PROVED  │
> │ 1c │ Fast and slow P1, with their original premises  │ PROVED  │
> ```

> _fgsa-adjudicate.md, lines 359–364:_
>
> This induction uses `a<h`, not `a≤f` and not FG quorum turnout. It
> proves clean safety, monotonicity, and 6Δ service. F and S remain on
> the same chain. The accessor is their greater prefix and is monotone.
> The changed proof follows the origin/root/parent/HEAD/guard order in
> `CleanInclusion.lean`; it does not instantiate that theorem on a
> different executable `Run`.

> _fgsa-adjudicate.md, lines 389–392:_
>
> Release has at most a conflicts, below τ. Expiry is after b₁. A new
> conflicting S write fails the guard; an ancestor result keeps S. Finality
> has a compatible target origin and cannot remove B at the accessor.
> Both P1 claims follow with `Π=min(η,L)` and the original lags.

- Status: 2026-09-28 — PROVED (FG-SA; r146 1a–1c).

### `ap.outputRecovered.v1` — ordinary outputs recover after the reset

- Variant `nj`. Source r150 §4.5, lines 374–387. File `fgsa-theorem-h.md`,
  sha256 `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.
- Hypotheses: `env.r150`; the actual reset of `fg.baseSel.nj.v1`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 374–387:_
>
> **Theorem H — PROVED.** Under §1 and the actual reset of §1, the run
> is FG-healed from q_s*. There is a repair gate `t_h=d_u` such that,
> for all times from t_h onward, all honest S values lie on one chain,
> each honest S is monotone, every accepted honest F is a prefix of
> every honest S, and every honest proposal emitted from t_h onward
> is in every honest S within 6Δ.
>
> The bound is
>
> ```text
> t_h ≤ t_(s*) + 2L+G+4Δ
>     = q_(s*) + 2L+G−Δ
>     = a_(r*) + 2L+G−2Δ.
> ```

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table line 23).
- Note: this is the local part of `comp.healed.v1`. It uses
  `comp.theoremN.v1`, so it is not a policy-uniform service fact
  (FRAMEWORK-DESIGN.md §7.3).
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays PROVED
  but depends on `comp.theoremN.v1`, so it is not an AP service fact.
  The local Theorem H clause of `comp.healed.v1` covers it.

### `ap.finalityHead.v1` — current-slot finality head

- Variant `nj`. Source r146 §5.4, item 1, lines 676–678. File
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 676–678:_
>
> 1. At the selected honest opening-plus-two-slots window, the separate
>    **current-slot finality head** is the slot-1 proposal, with the
>    required latest justification and permitted finality record.

- Status: 2026-09-28 — SKETCH (r146 claim 3g, environment-only first
  finality). It is used for finality liveness only.
- Status: 2026-09-28 — WITHDRAWN (audit W02). The statement stays SKETCH but
  includes the finality record permission, a Simplex client fact. The
  base-walk part is `ap.finalityHead.v2`; the record part is an
  obligation of `comp.finality.v1`.

### `ap.finalityHead.v2` — current-slot finality head (base walk only)

- Variant `nj`. Source r143 §11.2, interface I item 3, lines 996–999. File
  `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`.
- Statement (pinned):

> _fgsa-fast.md, lines 996–999 (excerpt; line breaks reflowed):_
>
> In an honest opening-plus-two-slots window, the action's separate finality
> head is the slot-1 proposal. Current honest HEADs cover it; the actual R1
> root and effective leases permit that walk. Slot bounds then give
> equality.

- Status: 2026-09-28 — SKETCH (r146 claim 3g; r143 §11.2 "First-finality
  assembly: SKETCH"). It is used for finality liveness only.
- Kind: AP service fact (audit W02). The permitted finality record
  ("Its finality records are absent or aligned") is a Simplex client
  fact and is an obligation of `comp.finality.v1`.

### `ap.fastSupport.v1` — a fast write has an honest supporter

- Variant `both` (no frame premise). Sources: r143 §3.1, lines 208–218
  (file `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`); the
  SA rule, sa lines 83–91, 157–161 and 219 (file `slow-arming.md`, sha256
  `c1d1a4e343c6910a1072cc7e6e8816b6ab6ac94b4940f204573f3a39c500db0b`); the
  SA Lean model, acG lines 381–383, 431–435 and 456–461 (file
  `AvailableChainGridCO/Model/Protocol.lean`, sha256
  `2cb079fd72fb7cb6901d8a8cfd59c650ad6561377b226b3240b68c852b59755c`); bp
  F-table row B3, line 314.
- Hypotheses: the static faulty set has size a with `h > a` and
  `h + a ≤ n` (so `a < τ`; under `a≤f` also `τ > a`); authentic HEADs.
- Service statement: let B ∈ `FastWrite_i[s]` at an honest reader i. Then
  B has at least τ distinct supporting seats at label s that survive the
  late equivocation test at i. Since `τ > a`, at least one of them is
  honest, and its label-s HEAD extends B.
- Statement (pinned):

> _fgsa-fast.md, lines 208–218:_
>
> Keep an immutable gate result and a local set `FastWrite_i[s]` at each
> completed gate. A block is in this set exactly when all of the following
> held at d_s:
>
> ```text
> B ≠ genesis;
> C_i[s] exists and B⪯C_i[s];
> 2*p_i(s,B) > |D_i[s]| and p_i(s,B) ≥ τ;
> the whole-result SA lease guard passed;
> the gate executed its lease write or renewal for B by the fast test.
> ```

> _slow-arming.md, lines 83–91:_
>
> Keep saved early support, the late participant pool, equivocation
> removal, full proposal-view merge, declared support subsets, block-slot
> guards, and old-block eligibility. For a raw genuine result `C_i[r]`
> and its non-genesis prefix B, write `p_i(r,B)` for B's surviving early
> support. It is an integer count from label r alone. In particular,
>
> ```text
> 2 p_i(r,B) > |D_i[r]|.
> ```

> _slow-arming.md, lines 157–161:_
>
> There is a useful absolute bound, but it comes from the regime:
>
> ```text
> h>a and h+a≤n  ⇒  a≤floor((n−1)/2)<τ=ceil(n/2).
> ```

> _slow-arming.md, line 219:_
>
> ```text
> fast_i(r,B) ⇔ B ⪯ C_i[r] and p_i(r,B)≥τ.
> ```

> _AvailableChainGridCO/Model/Protocol.lean, lines 381–383, 431–435 and
> 456–461:_
>
> ```lean
> def cleanSupport (p : Params) {n : Nat} (st : State n) (r : Slot) : List (Wire n) :=
>   (earlyVotes p st r).filter (fun o =>
>     !(lateVotes p st r).any (fun u => sameSeat u o && u != o))
> def prefixSupport (p : Params) {n : Nat} (st : State n) (r : Slot) (b : Block) : Nat :=
>   goldfishScore st.blocks (cleanSupport p st r) (cleanSupport p st r) b
>
> /-- The single SA release threshold is the ceiling of half the seats. -/
> def releaseThreshold (p : Params) : Nat := (p.n + 1) / 2
> def admissionLevels [LeasePolicy] (p : Params) {n : Nat} (st : State n)
>     (r : Slot) (b : Block) : List Nat :=
>   if LeasePolicy.slowArming then
>     if releaseThreshold p ≤ prefixSupport p st r b || slowEligible p st r b then
>       [releaseThreshold p] else []
>   else
> ```

- Status: 2026-09-28 — PROVED. The support count is RULE (the fast
  admission test); the honest supporter follows from `τ > a`. bp B3 states
  the same fact.
- Kind: AP service fact (audit W02): source safety. It is the SA half of
  the v1 provenance sentence "Each such C has an honest supporter since
  `τ>a`" (`fg.provenance.v1`).
- Note: the Lean model has no separate `FastWrite` record. The fast test is
  the first disjunct of `admissionLevels` (acG line 459). A Lean statement
  of this entry must name that disjunct, not the slow one.

## 3. `SimplexFG.nj` lemmas (`Kit.FG`)

### `fg.provenance.v1` — row, entry and finality provenance

- Variant `both`. Source r146 §3.1, lines 244–247. File
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`. Rule
  sources: r143 §3.1 and §3.3. FJ: r148 §5 F7, lines 400–403 (same facts).
- Statement (pinned):

> _fgsa-adjudicate.md, lines 244–247:_
>
> Every progress or target QC contains an honest height row since `q_F>a`.
> Its entry T is a prefix of its successful fast source C. Each such C
> has an honest supporter since `τ>a`. Finality names an already justified
> entry and thus has this earlier target origin.

- Status: 2026-09-28 — PROVED.
- Status: 2026-09-28 — SUPERSEDED (audit W02 split, agreed with
  ethereum-f1). The statement mixes a pure FG fact, an SA fact and the
  Simplex source rule. Successors: `fg.provenance.v2` (pure FG),
  `ap.fastSupport.v1` (SA: a fast write has an honest supporter) and
  `comp.provenance.v1` (the source C is the signer's `C_fg`). Their
  conjunction is this statement.

### `fg.provenance.v2` — honest row, entry and finality provenance (pure FG)

- Variant `both`. Sources: r146 §3.1, lines 244–247 (file
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`); r143
  §3.3, lines 275–283 (file `fgsa-fast.md`, sha256
  `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`); bp
  F-table row F1, lines 294–295 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`). FJ:
  r148 §5 F7, lines 400–403 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `q_F > a` (from `a≤f`); honest identities do not
  equivocate; the DC height-pair and finality-pair rules of r143 §3.3.
- Statement (registry): (1) every target, progress or finality QC has an
  honest row, since `q_F > a`. (2) An honest height row names the entry
  `T = σ[C].T_h` of the signer's source C, so `T ⪯ C`. (3) A finality row
  names the justified pair `(h_j, J)` of the signer's head state; hence a
  finality QC names an already justified entry, with an earlier target
  QC. The statement does not say how C is chosen or supported.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 244–247 (excerpt; the first, second and
> fourth sentences; line breaks reflowed):_
>
> Every progress or target QC contains an honest height row since `q_F>a`.
> Its entry T is a prefix of its successful fast source C. Finality names
> an already justified entry and thus has this earlier target origin.

> _fgsa-fast.md, lines 275–283:_
>
> ```text
> finality_pair(Λ,hj,J,hF):
>     if hj>hF and Λ.target[hj]∈{none,J}
>        and not Λ.timeout[hj] and Λ.lock[hj]∈{none,J}:
>         return (hj,J)
>     return empty
>
> height_pair(Λ,C_fg,fp):
>     if C_fg absent: return empty
>     (h,T,nj) := (σ[C_fg].h, σ[C_fg].T_h, σ[C_fg].nj)
> ```

> _fgsa-healing-blueprint.md, lines 294–295:_
>
> ```text
> │ F1  │ Each target, progress, or finality QC   │ q_F>a                               │
> │     │ has an honest row.                      │                                     │
> ```

> _fj-redteam.md, lines 400–403:_
>
> Every target or progress QC contains an honest row because q>a. Each
> honest height row has a successful fresh fast source, with τ>a surviving
> supporters. Its named entry is an ancestor of that source. Finality has
> an earlier justified target origin.

- Status: 2026-09-28 — PROVED.
- Note: the word "successful fast" in the r146 excerpt and the second
  sentence of the r148 lines are not part of this entry. They are
  `ap.fastSupport.v1` and `comp.provenance.v1`.

### `fg.causalCap.v1` — causal cap at the cut

- Variant `both`. Sources: r147 §6, lines 642–651 (file
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`); r144
  §2.2, lines 168–193 (file `fgsa-no-nj.md`, sha256
  `1eaf728ffc4d56cc54fbccf581a8dffe457da02b96bd59cedb012bbf5ee1e03a`).
- Statement (pinned):

> _fgsa-conditional.md, lines 642–651:_
>
> **The causal cap used by the other job.** At an actual event-prefix cut
> with honest archival frontier M, each previously emitted honest height
> row has height at most M [DC6]. A crossing uses q_F distinct matching
> identities and hence an honest row. A carrier made only from pre-cut
> rows therefore has height at most M+1 and justified height at most M
> [DC7]. This includes later assembly from old signatures. The cap does
> not bound carriers that use new honest rows. It affects an R1 HEAD
> only when its own view contains the required height witness. These
> facts are consistent with N2's explicit first-q_s boundary; they do
> not replace its proof at NJ+1.

> _fgsa-no-nj.md, lines 168–193:_
>
> Use exactly the requested cut:
>
> ```text
> r_G = first action round at or after GST;
> u0  = a_(r_G+2), inclusive event prefix;
> M   = honest archival frontier at u0.
> ```
>
> Every honest height row in that prefix has height at most M, because its
> source was already in its signer's store. Every crossing has an honest
> row, since `q_F>a`. Hence a carrier whose height evidence uses only such
> old honest rows has height at most M+1, and its justified height is at
> most M. Faulty rows can be new; without a new honest row they cannot
> cross the next height. This includes a newly constructed carrier with
> old target rows. See [fg-frame-recovery §§2.3–2.4](fg-frame-recovery.md)
> and [WeakHeightBounds][height-bound].
>
> At a duty with `H_V≥M+2`, an old-only justification satisfies
>
> ```text
> j_old≤M < H_V−1,
> ```
>
> so it cannot be the active root. This is a duty-view statement. An
> archival rise must first reach the frozen HEAD view. Allow the R1 relay
> and freeze margin; do not substitute an unseen archival maximum.

- Status: 2026-09-28 — PROVED (r147 §6; r144 claims N1 and N2).
- Note: r144 claim N3 ("thus all later justifications are permanent") is
  REFUTED. The cap does not bound carriers that use new honest rows.
- Status: 2026-09-28 — SUPERSEDED (split agreed with ethereum-f1).
  Successors: `fg.causalCap.core.v1` (the cap for any bound M) and
  `comp.cut.v1` (the DC cut r_G, `u_0 = a_(r_G+2)` and M at `u_0`, with
  the duty-view clause, which also uses `comp.settle.v1`).

### `fg.causalCap.core.v1` — causal cap for a bound M

- Variant `both`. Sources: r147 §6, lines 642–651 (file
  `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`); bp
  F-table row F2, lines 296–297 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); DC
  Lean, vcW lines 42–48 (file
  `DecoupledConsensusProofs/Protocol/ValidatorClient/WeakHeightBounds.lean`,
  sha256 `f0d45fa7fd93a0a1c9f4dfccaf6c3f7c63c43245c5deee7182a25f3963c22b5d`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `fg.provenance.v2` (each crossing and each target QC has an
  honest row); the honest DC client (a row names its source's own height).
- Statement (registry): (a) an honest row of height h, emitted by v at
  time t, has `h ≤` the archival maximum of v's store before t. (b) Let M
  be a height. A carrier whose honest rows all have height at most M has
  height at most M+1 and justified height at most M: a crossing of M+1
  and a target QC at M+1 each need an honest row at M+1. Faulty rows can
  be new; they cannot cross a height alone. The cap does not bound a
  carrier that uses a new honest row above M.
- Statement (pinned):

> _fgsa-conditional.md, lines 642–651:_
>
> **The causal cap used by the other job.** At an actual event-prefix cut
> with honest archival frontier M, each previously emitted honest height
> row has height at most M [DC6]. A crossing uses q_F distinct matching
> identities and hence an honest row. A carrier made only from pre-cut
> rows therefore has height at most M+1 and justified height at most M
> [DC7]. This includes later assembly from old signatures. The cap does
> not bound carriers that use new honest rows. It affects an R1 HEAD
> only when its own view contains the required height witness. These
> facts are consistent with N2's explicit first-q_s boundary; they do
> not replace its proof at NJ+1.

> _fgsa-healing-blueprint.md, lines 296–297:_
>
> ```text
> │ F2  │ Causal cap: an honest row at height h   │ WeakHeightBounds.lean:42            │
> │     │ has h ≤ the signer's archival maximum.  │ honestEmittedHeight_le_localHMax... │
> ```

> _WeakHeightBounds.lean, lines 42–48:_
>
> ```lean
> theorem honestEmittedHeight_le_localHMaxBeforeTime
>     (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
>     {v : V} {a : NamedAttestation V}
>     {t : Time} {h : Height}
>     (hemit : rho.emits S v (Object.attest a) t)
>     (hh : a.height_pair.erase.height? = some h) :
>     h ≤ (rho.storeBeforeTime S v t).h_max := by
> ```

- Status: 2026-09-28 — PROVED. Part (a) is LEAN for DC
  (`honestEmittedHeight_le_localHMaxBeforeTime`); there is no FG-SA Lean
  instance. Part (b) is the paper step of r147 §6 and r144 §2.2.
- Note: the pinned r147 text states the cap at a cut. This entry states
  it for any M; `comp.cut.v1` sets M to the DC cut maximum.

### `fg.uniqueJust.v1` — one justified entry per height (blueprint F3)

- Variant `both` (FJ keeps the certificate syntax and E1/E2, r148 F8).
  Sources: bp F-table row F3, line 298 (file `fgsa-healing-blueprint.md`,
  sha256 `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`);
  DC Lean L7 (Lemma U), vcE lines 229–249 (file
  `DecoupledConsensusProofs/Protocol/ValidatorClient/Engine.lean`, sha256
  `92fb0e64c1288afea98b53212cb3ad5c843c9c720187367eea578d17a9d53454`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `a≤f`, so `2q_F−n > a`; honest identities follow E2 (at most
  one target per height).
- Statement (registry): at each height h, at most one entry is justified
  in the whole run (on any chain, in any store).
- Statement (pinned):

> _fgsa-healing-blueprint.md, line 298:_
>
> ```text
> │ F3  │ One justified entry per height (L7).    │ ValidatorClient/Engine.lean, a≤f    │
> ```

> _Engine.lean, lines 229–249:_
>
> ```lean
> /-- **Lemma U** (rev. 3 §1.3; PROTOCOL.md#the-complete-protocol): two target quorums at one
> height for **different** roots expose `2q − W` of E2 weight, at that height,
> against those two roots.
>
> Hence *"absent `2q − W` of E2-slashable weight, at most one target is justified
> at any height, on any chain, anywhere in the run"* — and hence the lex tiebreak
> on `(h_j, J.root)` never arbitrates between two real certificates
> (`Finality.lean:52–70`, rev. 3 §1.3): the root component separates only events
> at the same height, and by this lemma two real justifications never share one.
>
> Nothing about chains, stores or reachability enters. The quorums are abstract
> sets with per-member witnesses drawn one from each attestation pool, which is the
> same evidence discipline `SlashableBetween` uses — the pool a witness comes
> from is named, never existentially closed. -/
> theorem justification_unique_per_height (E : Env V)
>     {A₁ A₂ : Finset (CombinedAttestation V)} {Q₁ Q₂ : Finset V} {h : Height}
>     {T₁ T₂ : BlockId}
>     (hQ₁ : E.electorate.IsQuorum Q₁) (hQ₂ : E.electorate.IsQuorum Q₂)
>     (hw₁ : ∀ i ∈ Q₁, ∃ a ∈ A₁, a.val_index = i ∧ a.height_pair = .target h T₁)
>     (hw₂ : ∀ i ∈ Q₂, ∃ b ∈ A₂, b.val_index = i ∧ b.height_pair = .target h T₂) :
>     HasE2WeightAt E h T₁ T₂ A₁ A₂ := by
> ```

- Status: 2026-09-28 — LEAN (DC). The Lean theorem is the certificate
  form: two target quorums for different entries at one height give
  `2q−W` of E2 weight. The step to "at most one entry" uses
  `2q_F−n > a` and honest E2 compliance; it is one line of paper proof. The
  companion `justification_unique_per_height_slashable` is at vcE line
  261. There is no FG-SA Lean instance.

### `fg.finalLock.v1` — finality lock (blueprint F4)

- Variant `both`. Sources: bp F-table row F4, lines 299–300 (file
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); DC
  Lean L8, vcF lines 50–56 (file
  `DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean`,
  sha256 `aa0ed92740eb1ec8ee69e90fd2ae75f03179a27c05accf5f631e7a254589b94c`).
  r148 calls the same fact the "finalized-crossing law" (line 226; file
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`).
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: the run satisfies the DC slashable bound (`a≤f`); roots are
  collision-free; the honest DC client (E1).
- Statement (registry): if D is a block of the run with finalized
  checkpoint `F(D)` at height `h_F(D)`, then every block C of the run with
  `h(C) > h_F(D)` extends `F(D)`.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 299–300:_
>
> ```text
> │ F4  │ Finality lock: every block of height    │ FinalityComparison.lean:50          │
> │     │ > h_F(D) extends F(D) (L8).             │ finalized_preceq_of_height_lt       │
> ```

> _FinalityComparison.lean, lines 50–56:_
>
> ```lean
> theorem finalized_preceq_of_height_lt
>     (S : Setup V) (rho : NamedRun V) (C D : NamedBlock V)
>     (hsb : Internal.NamedOutageEntry.SlashableBound S rho)
>     (hroot : NamedRootCollisionFree S rho)
>     (hC : NamedRun.blockInRun S rho C) (hD : NamedRun.blockInRun S rho D)
>     (hlt : (derive_named S.E S.cfg D).h_F < (derive_named S.E S.cfg C).h) :
>     Block.Preceq (derive_named S.E S.cfg D).F C.erase := by
> ```

> _fj-redteam.md, lines 224–226:_
>
> Every frontier block has height above the height of accepted F: a
> finalization at y has a justification carrier at height at least y+1.
> The finalized-crossing law puts every such frontier block above F.

- Status: 2026-09-28 — LEAN (DC). There is no FG-SA Lean instance. bp
  §7.9, lines 831–843 (pinned in `fg.base.finalized.v1`), explains why
  the proof also covers crossings signed before the finality pairs.

### `fg.trunk.v1` — F advance below the band

- Variant `nj`. Source bp §4.1, lines 352–375 (H2). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`. r149
  §4.1, lines 324–334, proves it again.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses (named 2026-09-28; §0 rule (b)): `fg.finalLock.v1` (the "F4"
  of item 1); B2 of bp §3 (live leases at one reader form a chain);
  `a≤f`.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 352–375:_
>
> Let d be a duty in F-mode with `H_d = m ≥ 2`. Then `h(F_d) ≤ m−2`: an F at
> m−1 is a justified checkpoint at m−1, its J carrier is in V_d (the F
> basis), and `F_d⪯F_d`, so j_d ≥ m−1 and d is in J-mode. Let F′ be a finalized block with `F_d⪯F′` and `h(F′) ≤ m−2`.
> Compare the frame of V_d with root F_d and with root F′.
>
> 1. Every W∈V_d with `h(W) ≥ m−1` extends F′, by F4. Hence every block of
>    D(F_d) is comparable with F′, and `D(F′) = D(F_d) ∩ desc(F′)`. F′ is in
>    D(F_d), since the maximizing carrier of height m extends F′.
> 2. Let M_d be the deepest live lease target in D(F_d), or F_d. By B2
>    the leases are a chain. If F′⪯M_d, M_d is also the start with root F′.
>    If M_d≺F′, no live lease lies in D(F′), since it would be deeper than
>    M_d in D(F_d). The start with root F′ is F′. The walk from M_d has
>    exactly one child on each step below F′, since every block of D(F_d)
>    is comparable with F′. Each such child has a parent of height
>    ≤ m−2 < m−1, so it is eligible. The walk from M_d therefore reaches F′.
> 3. Above F′ the two domains, scores, and eligibility tests are equal. The
>    score reads votes, not the domain. Hence both walks return the same
>    block. This applies to proposal, HEAD, and finality-head walks.
> 4. A fresh candidate of height ≥ m−1 is in both domains, by item 1. Thus
>    C_fg is the same whenever either choice has height ≥ m−1. A candidate
>    below that height gives a row at height ≤ m−2; such a row produces
>    carriers of height ≤ m−1 and cannot change the frontier m.
>
> So an F advance in F-mode changes no walk result and no band source.

- Status: 2026-09-28 — PROVED (a≤f).
- Note: the lemma compares one view with two roots. It does not transport a
  comparison between two views (r149 §4.3).

### `fg.oneBullet.v1` — at most one effective filter change

- Variant `nj`. Source bp §4.2, lines 383–409 (H3). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 383–409:_
>
> Fix m. Let t_m be the time at which the honest frontier first equals m.
>
> 1. **Settling.** Every object that an honest store holds at t is in every
>    honest full view from t+Δ, and in every honest HEAD view at a time
>    ≥ t+θ. Proof: relay gives receipt by t+Δ at every honest reader. A HEAD
>    at `v_s ≥ t+4Δ` has freeze `t_s−Δ ≥ t+2Δ`. Since views are subsets of
>    stores, `H_d ≤ m` while the frontier is m. Thus `H_d = m` at every
>    honest duty in `[t_m+θ, ·)` until the frontier rises.
> 2. **Modes.** At `H_d = m`, J-mode means `j_d = m−1`. A justified entry at
>    m−1 is unique (F3). F_d has height ≤ m−1, and an F at m−1 equals
>    J_(m−1). An F at a lower height precedes J_(m−1) by F4. Thus J-mode at
>    d means `Ẑ_d = J_(m−1)`, for one fixed block. No justification above
>    m−1 exists at frontier m, because `h_j < h` on every chain.
> 3. **One change.** Let t_J be the first time at which an honest store
>    holds a carrier of J_(m−1), or ∞. Views are subsets of stores, so every
>    duty before t_J is in F-mode. By item 1, every duty at a time ≥
>    `max(t_m, t_J)+θ` is in J-mode, since stores only grow. Hence Φ_d
>    takes at most two values at frontier m, first (m,◇) and then
>    (m,J_(m−1)).
> 4. **No other change.** Lower J values do not act: `H_d = m ≠ j+1` for
>    `j ≤ m−2`. F advances in F-mode do not act (§4.1). A finalization of
>    J_(m−1) in J-mode leaves Ẑ_d unchanged. New blocks only add witnesses.
>
> Count: at a fixed frontier there is **at most one effective filter change**
> (the arrival of J_(m−1)). The adversary needs a higher frontier for a new
> change. This agrees with the one-exclusion count of
> [fgsa-fast §9.1](fgsa-fast.md) and [fgsa-fast-opus §6.5](fgsa-fast-opus.md).

- Status: 2026-09-28 — PROVED (a≤f).
- Notes: [async] r147 §6 counts control EVENTS (`m−1−f0+ε_J`, F advances
  included); bp counts EFFECTIVE filter values after the trunk lemma. θ is
  4Δ in bp and 3Δ in r147. [async] r149 §3 (lines 305–315) fixes θ = 4Δ.
- Status: 2026-09-28 — SUPERSEDED (split agreed with ethereum-f1). Item 1
  (settling) and the step "By item 1" of item 3 are run facts:
  `comp.settle.v1`. Items 2–4 without that step are the pure core:
  `fg.oneBullet.core.v1`. Their conjunction is this statement.

### `fg.oneBullet.core.v1` — effective filter at a fixed frontier (pure core)

- Variant `nj`. Source bp §4.2, items 2–4 and the count, lines 391–409
  (H3). File `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `fg.frame.v2` (with `fg.frameCompat.v1`); `fg.uniqueJust.v1`
  (F3); `fg.finalLock.v1` (F4); `fg.trunk.v1` (F advances in F-mode do not
  act); `h_j < h` on every chain (DC transition, bp F5).
- Statement (registry): fix a frontier m. Let J_(m−1) be the justified
  entry at m−1, if one exists (unique by `fg.uniqueJust.v1`). For an
  honest duty d with `H_d = m`, let `E_J(d)` mean "V_d holds a carrier of
  J_(m−1)". Then:
  1. `Ẑ_d = J_(m−1)` if `E_J(d)`, and `Ẑ_d = ◇` otherwise. So
     `Φ_d ∈ {(m,◇), (m,J_(m−1))}`.
  2. If `E_J(d)` is false at every such duty before a time t1 and true at
     every such duty from a time t2 ≥ t1, then `Φ_d = (m,◇)` before t1 and
     `Φ_d = (m,J_(m−1))` from t2. Lower J values, F advances in F-mode, a
     finalization of J_(m−1) in J-mode and new blocks do not change Φ_d.
  Thus the effective filter changes at most once per frontier: one event
  (the arrival of J_(m−1)), with the interval `[t1,t2)` as its settling
  interval. The core does not say when t1 and t2 occur.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 391–409:_
>
> 2. **Modes.** At `H_d = m`, J-mode means `j_d = m−1`. A justified entry at
>    m−1 is unique (F3). F_d has height ≤ m−1, and an F at m−1 equals
>    J_(m−1). An F at a lower height precedes J_(m−1) by F4. Thus J-mode at
>    d means `Ẑ_d = J_(m−1)`, for one fixed block. No justification above
>    m−1 exists at frontier m, because `h_j < h` on every chain.
> 3. **One change.** Let t_J be the first time at which an honest store
>    holds a carrier of J_(m−1), or ∞. Views are subsets of stores, so every
>    duty before t_J is in F-mode. By item 1, every duty at a time ≥
>    `max(t_m, t_J)+θ` is in J-mode, since stores only grow. Hence Φ_d
>    takes at most two values at frontier m, first (m,◇) and then
>    (m,J_(m−1)).
> 4. **No other change.** Lower J values do not act: `H_d = m ≠ j+1` for
>    `j ≤ m−2`. F advances in F-mode do not act (§4.1). A finalization of
>    J_(m−1) in J-mode leaves Ẑ_d unchanged. New blocks only add witnesses.
>
> Count: at a fixed frontier there is **at most one effective filter change**
> (the arrival of J_(m−1)). The adversary needs a higher frontier for a new
> change. This agrees with the one-exclusion count of
> [fgsa-fast §9.1](fgsa-fast.md) and [fgsa-fast-opus §6.5](fgsa-fast-opus.md).

- Status: 2026-09-28 — PROVED (a≤f; bp H3 without its item 1).
- Composition: with `comp.settle.v1`, take `t1 = t_J` (views are subsets
  of stores) and `t2 = max(t_m, t_J)+θ`, and restrict to duties in
  `[t_m+θ, t_up)`, where `H_d = m`. This gives the full bp §4.2 count.

### `fg.H19.v1` — HNI-a

- Variant `nj`. Source bp §7.9, lines 803–809 (H19). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `fg.HNI.v1` for m.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 803–809:_
>
> **Lemma HNI-a — PROVED.** Assume HNI(m). At every honest duty d with
> `H_d = m`, every block B∈V_d with `h(B) ≥ m` is kept. This holds whatever
> F_d is and whether J at m−1 is known.
>
> Proof. At H_d = m, Z_d is J_d at m−1 or F_d with `h(F_d) ≤ m−1`. By (h1)
> or (h2), `Z_d ⪯ B`. The band threshold is m−1 ≤ h(B), so B is its own
> witness. Hence B∈D_d. ∎

- Status: 2026-09-28 — PROVED.

### `fg.HNIb.v1` — HNI-b

- Variant `nj`. Source bp §7.9, lines 815–827. File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `fg.HNI.v1` for m.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 815–827:_
>
> **Lemma HNI-b — PROVED.** Assume HNI(m). At every honest duty d with
> `H_d ≥ m`, either `h(Z_d) ≥ m`, or Z_d precedes every block of V_d of
> height ≥ m. In the first case Z_d is a justified entry at a height ≥ m.
>
> Proof. If `h(Z_d) ≤ m−1`, then Z_d is F_d (with h ≤ m−1) or a J at
> `H_d−1`. The second option forces `H_d = m` and J at m−1. Apply (h2) or
> (h1). ∎
>
> So the only FG objects that can remove a block of height ≥ m are
> justified entries at heights ≥ m, and band thresholds above m. Both are
> made from honest rows at heights ≥ m (F1, F11). This is the split that
> Lemma K uses. In Lemma K, (K2) with F3 and F4 is exactly HNI(x+1), and
> (K1) controls the objects at heights ≥ x+1.

- Status: 2026-09-28 — PROVED.

### `fg.base.finalized.v1` — finalized arm gives HNI(x+1) run-wide

- Variant `nj`. Source bp §7.9, lines 831–843 (H20). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: the finalized arm of `fg.baseSel.nj.v1` (x = hF0 and the
  actual checkpoint F*); `a≤f`; `fg.uniqueJust.v1` (F3) and
  `fg.finalLock.v1` (F4), named 2026-09-28 (§0 rule (b)).
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 831–843:_
>
> - *Finalized arm — PROVED.* x = hF0 and F* is finalized at x. (h1): every
>   justified entry at x equals F* (F3), and F* precedes every block of
>   height > x (F4). (h2): a finalized checkpoint of height ≤ x precedes
>   every block of height > its own height (F4). F4 is
>   [finalized_preceq_of_height_lt][dc-finality]. Its proof uses only the
>   existence of the finality quorum in the run and the honest record
>   order: a height crossing at x with another entry and the finality
>   quorum share an honest identity, and that identity's first signature
>   forbids the second, in either order. So HNI(x+1) holds for the whole
>   run, including crossings signed **before** the finality pairs, and
>   including honest nodes that sign rows at x+1 without knowing F*. The
>   revelation of F* at a view with H_d = x+1 moves the root to F*; by
>   HNI-a it prunes only blocks that never reach x+1.

- Status: 2026-09-28 — PROVED.
- Note (audit W09): this is a lemma. The base-selection output is the
  witness record of `fg.baseSel.nj.v1`.

### `fg.base.nj.v1` — NJ arm gives HNI(H+1) run-wide

- Variant `nj`. Source bp §7.9, lines 844–847 (H21). File
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`.
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: the NJ arm of `fg.baseSel.nj.v1`; `ap.S.v2`; `ap.Sslow.v1`;
  `fg.finalLock.v1` (F4, for (h2)), named 2026-09-28 (§0 rule (b)).
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 844–847:_
>
> - *NJ arm — PROVED from (S).* x = H. (h2) is F4. (h1) holds vacuously
>   because no justified entry at H ever exists. In the DC prefix this is
>   F7. For the whole run it is Theorem N clause (ii) with F1 (N-b). The NJ
>   arm therefore needs an induction, and the finalized arm does not.

- Status: 2026-09-28 — PROVED (FG-SA). bp has PROVED* from (S) (H21). Its
  hypothesis (S) is `ap.S.v2` (PROVED, r149), and r150 §2 (lines 131–133)
  states Theorem N clause (ii) as PROVED.
- Note (audit W09): run-wide HNI(H+1) is DERIVED inside the joint induction
  of `comp.theoremN.v1` (clause (ii) with F1). It is not a base-selection
  input. The base returns only the prefix NJ facts.

### `fg.baseSel.nj.v1` — base-selection witness record (NJ or finalized)

- Variant `nj`. Sources: bp §1.2 and §6, lines 138–145, 483–492 and 500–514
  (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); bp
  §7.1, lines 524–531; r150 §1, lines 94–112 (file `fgsa-theorem-h.md`,
  sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`); r146
  §4, lines 406–415 (file `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`).
- Lean plan: none (nj research entry; user 2026-09-28). Not planned
  for Lean now; the entry stays as a research entry.
- Hypotheses: `env.bp` (or `env.r150`); the honest frontier reaches H+3 (the
  deadline is in `comp.healedLit.v1` or `comp.arrivalNJ.v1`); for the
  finalized arm `fg.uniqueJust.v1` (F3) and `fg.finalLock.v1` (F4, also
  "DC's finalized-crossing law" in the r146 quote); `comp.cut.v1` and
  `fg.causalCap.core.v1` (F2, item 4). Named 2026-09-28 (§0 rule (b)).
- Returned witness (audit W09; FRAMEWORK-DESIGN.md §7.4). The base does not
  return HNI.
  1. Cut: `u_0 = a_(r_G+2)`, its inclusive event prefix, and M = the honest
     archival frontier at `u_0`; `GST+2P ≤ u_0 < GST+3P`. H is the first
     multiple of K above `M+D+2`; `H+3 ≤ M+D+K+5`.
  2. Height x > M, from the DC consumer: NJ arm `x = H`; finalized arm
     `x = hF0` with `M < x ≤ H+1`.
  3. Arm witness. NJ arm: the prefix NJ record facts F6 and F7 (nj = true at
     H before `first`; no honest lock, target record or target row at H in
     that prefix). Finalized arm: the actual finalized checkpoint F* at x in
     an honest store, with F3 (`fg.uniqueJust.v1`) and F4
     (`fg.finalLock.v1`).
  4. First row above x: r* = the least round of an honest row at height x+1,
     `s* = r*R`, its fresh fast source body C* and its entry T*.
     `r* > r_G+2`, `t_(s*) ≥ GST+2P`, s* and every later label are
     synchronous, and every honest row at height ≥ x+1 has round ≥ r*.
  5. First-transfer view facts of C*: C* is in every honest store before
     `z_(s*)` and in every honest view from its first freeze; each `q_(s*)`
     view has maximum exactly x+1; the root is below C*; every `q_(s*)` HEAD
     covers C*; `H_d ≥ x+1` at every honest duty from `q_(s*)`.
- Statements (pinned):

> _fgsa-healing-blueprint.md, lines 138–145:_
>
> Let r_G be the first action round with `a_(r_G) ≥ GST`. The DC cut is the
> inclusive event prefix at `u_0 = a_(r_G+2)`. Then `GST+2P ≤ u_0 < GST+3P`.
> Let M be the honest archival frontier at u_0. As in DC,
>
> ```text
> H = the first multiple of K strictly above M+D+2;
> M+D+3 ≤ H ≤ M+D+K+2;  H+3 ≤ M+D+K+5.
> ```

> _fgsa-healing-blueprint.md, lines 483–492:_
>
> **Consumer — PROVED port.** Apply F9 unchanged. Let `first` be the first
> event index at which the frontier is H+2, and let hF0 be the greatest h_F
> in honest stores before it.
>
> - **NJ arm:** `K | H` and `D < H−hF0`. Put `x = H`. Every chain state at H
>   in an honest store before `first` has nj = true (F6). F7 gives no honest
>   lock, target record, or target row at H in that prefix.
> - **Finalized arm:** otherwise `M < hF0 ≤ H+1`, and a finalized checkpoint
>   F* at height hF0 exists in an honest store. Put `x = hF0`. By F3, every
>   justified entry at x is F*. By F4, every block of height > x extends F*.

> _fgsa-healing-blueprint.md, lines 500–514:_
>
> **Reset round.** Let r* be the least round of an honest row at height x+1.
> Put `s* = r*R`, let C* be that row's source body, and T* its entry.
>
> - r* exists before the frontier reaches x+2, because that crossing folds
>   a quorum at x+1 with an honest row (F1). In both arms `x+2 ≤ H+3`, so
>   `a_(r*) < u_0 + (D+K+5)Λ_lvl`.
> - `x+1 > M`, so by F2 the signer's archival maximum exceeds M at a_(r*).
>   Hence `r* > r_G+2` and `t_(s*) = T_(r*) ≥ GST+2P`. The label s* and all
>   later labels are synchronous. This is the blueprint's causal cap.
> - Rows emitted before u_0 have heights ≤ M. A carrier that uses only them
>   has height ≤ M+1 and a justification ≤ M, since each crossing needs an
>   honest row. Since `x ≥ M+3` in the NJ arm and `x ≥ M+1` in the finalized
>   arm, such objects never set `H_d ≥ x+1` and never supply a root at x.
> - Every honest row at a height ≥ x+2 is later than some honest row at x+1.
>   Hence every honest row at a height ≥ x+1 has round ≥ r* and label ≥ s*.

> _fgsa-healing-blueprint.md, lines 524–531:_
>
> Every B∈𝒫 at label s is in every honest store before z_s, hence in every
> honest view from its first freeze on. Proof: a fast body has an honest
> supporter (B3) whose HEAD at v_s extends B. A slow body lies in the
> label-s genuine result, which has more than |D_s|/2 > a surviving
> supporters, one of them honest. That HEAD's path relays to every honest
> reader by `v_s+Δ = e_s < z_s`.
>
> At every honest duty d with `t_d ≥ q_(s*)`, `C*∈V_d` and so `H_d ≥ x+1`.

> _fgsa-theorem-h.md, lines 103–112:_
>
> Use the actual DC consumer, with both outcomes. In the NJ outcome,
> `x=H` and the retained prefix has no honest target or lock at H. In
> the finalized outcome, x is its actual finalized height, `M<x≤H+1`,
> and F* is the named checkpoint at x. Every block of height greater
> than x extends F*. Do not replace this outcome by an assumed NJ bit.
>
> Let r* be the least round of an honest height-(x+1) row, let `s*=r*R`,
> and let C* be its fresh fast source body. The causal cap gives a wholly
> post-GST source label s*. Every honest row at height at least x+1 has
> label at least s*. These are the reset facts in blueprint §6.

> _fgsa-adjudicate.md, lines 406–415:_
>
> **First transfer.** An honest surviving supporter held the complete C*
> path at v_s*. Relay puts that path in every freeze z_s*. No earlier
> honest row at x+1 exists, so no earlier carrier at x+2 can exist.
> Each q_s* view has maximum exactly x+1. The NJ record induction excludes
> J at x in this prefix. In the finalized arm, any J at x equals F*;
> every block above height x extends F* by DC's finalized-crossing law.
> In either case the root is below C*. The path is viable. The τ release
> removes every conflicting lease, and the strict score transfer makes
> every q_s* HEAD cover C*. Same-label genuine compatibility excludes a
> conflicting pending write at d_s*.

- Status: 2026-09-28 — PROVED (FG-SA). bp §6 "Consumer — PROVED port"; r146
  claims 2a and 2b; r143 claim C12 (first transfer).
- Note: a Lean port of the consumer must re-derive the DC chain-state facts
  for a mixed instance (bp lines 494–498).

### `fg.accountable.v1` — accountable FG safety

- Variant `both`. Sources: r143 §6, lines 474–485 (file `fgsa-fast.md`,
  sha256 `8907540c5c71fe06703bc8d2ec2d30bc6cbc752a5f7577219a69196e2fd8ef37`)
  for `nj`; r148 §5 F8, lines 452–462 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`) for
  `fj`.
- Lean plan: DC-fj module (user 2026-09-28).
- Statement (pinned):

> _fgsa-fast.md, lines 474–485:_
>
> Each justification has q_F distinct matching targets. Each height crossing
> has q_F distinct matching progress identities. Each finalization has q_F
> matching finality identities. DC's crossed-height certificate argument
> therefore extracts at least `2q_F−n` identities with E1/E2 evidence from
> two conflicting finalizations. It uses full fixed identities, not base
> seats. Under `a≤f`, `2q_F−n>a`, so conflicting finalizations are impossible.
> Above that cap the accountable statement still holds. It is not an
> unconditional agreement claim.
>
> The live finality update advances F only to a proper descendant; local F
> never retreats. The accessor in §4 gives `finalized⪯available` at every
> read. These results do not depend on the missing base-history proof.

> _fj-redteam.md, lines 452–462:_
>
> F8 — PROVED. The certificate syntax, exact-entry transition, E1/E2,
> and signing client are unchanged. The pure DC accountable-finality
> proof still extracts at least 2q−n slashable identities from conflicting
> finalizations. A finite no-NJ prefix can be checked with a finite K
> larger than every height in it; no NJ bit is then set. Alternatively,
> repeat the certificate argument, which does not require scheduled NJ
> heights. With a≤f, conflicting finalizations are impossible.
>
> Pointwise finalized ⪯ available follows directly from the two accessor
> cases, even outside the fault bound. It does not imply F⪯S in every
> damaged local state.

- Status: 2026-09-28 — PROVED (r143 C7, C8; r148 F8). LEAN for DC only (the
  DC accountable-finality theorem); there is no FG-SA Lean instance.

## 4. `SimplexFG.fj` — FJ root rule, own frame and interface (audit W06)

FJ changes the frame rule: a frontier test, root F and band `{H}` in a
contest. It is a module variant, not a base selector. HNI is NOT the FJ
interface. FJ can keep a height-(M+1) source that does not extend an old
justified entry at M; this is a failure of HNI(M+1).(h1), while FJ's filter
still protects the source:

> _fgsa-no-nj-opus.md, lines 612–620:_
>
> **N14: NJ-free reset — PROVED.** Under FJ every step of a descent chain
> has `x ≥ σ[C].h`. So every abandoned post-GST source has height at most
> M (§3.3). Every honest row at height ≥ M+1 has a synchronous label, so
> its source is extended by every honest HEAD from its label on. The next
> unanimous batch then puts it in every S by `t_s+10Δ` (fgsa-fast-opus
> §5.1 step 7). This is Lemma R with `x=M` and no NJ. It also follows the
> proof in fgsa-adjudicate §4: the only change is its "old J at x" clause.
> Under FJ an old J at M cannot pass a source C* at M+1, because C* is a
> frontier block that does not extend it.

Thus `fg.HNI.v1`, `fg.H19.v1`, `fg.HNIb.v1`, `fg.trunk.v1`,
`fg.oneBullet.v1` (now `fg.oneBullet.core.v1`), `fg.base.finalized.v1`,
`fg.base.nj.v1` and `fg.baseSel.nj.v1` do not apply to FJ. The FJ
noninterference interface is `fj.descent.v1`, `fj.canonical.v1` (F9),
`fj.inBandLock.v1` (F10) and `fj.twoChanges.v1` (F12; now
`fj.twoChanges.core.v1` with `comp.settle.v1`); its reset witness is
`fj.reset.v1`. The `both` entries `fg.provenance.v2`,
`fg.causalCap.core.v1`, `fg.uniqueJust.v1`, `fg.finalLock.v1`,
`fg.frameCompat.v1`, `comp.provenance.v1`, `comp.settle.v1` and
`comp.cut.v1` apply to FJ. The FJ cap M
is the cap on old honest rows (`env.r148`); it is at most DC's archival
M0. r151 calls this cap μ and calls M0 simply M.

### `fj.frame.v1` — FJ frame and walk

- Variant `fj`. Source r148 §2, lines 148–185 and 188–192. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`. Rule
  origin: r144o §5.3, lines 565–583 (file `fgsa-no-nj-opus.md`, sha256
  `7df2a540134deddede78ea711754bb322911fced62271868f8b5034164db9f4e`).
- Lean plan: DC-fj module (user 2026-09-28).
- Statement (pinned):

> _fj-redteam.md, lines 148–185:_
>
> ```text
> FJ_FRAME(V):
>     F := current accepted F
>     H := max({1} ∪ {h(W): W∈V})
>     (j,J) := lex-greatest (σ[W].h_j, root(σ[W].J)) witnessed in V
>              with F ⪯ σ[W].J
>     front := {W∈V: h(W)=H}
>     contest := (H=j+1 and exists W∈front with not J⪯W)
>
>     if H=j+1 and not contest:
>         Z := J
>         lo := H−1
>     else if contest:
>         Z := F
>         lo := H
>     else:
>         Z := F
>         lo := H−1
>
>     viable := {B∈V: F⪯B and
>                     exists W∈V with B⪯W and h(W)≥lo}
>     D := {B∈viable: Z⪯B}
>     return (F,H,j,J,Z,lo,D,contest)
>
> get_fg_root(V):
>     return FJ_FRAME(V).Z
>
> get_filtered_block_tree_from(V):
>     return FJ_FRAME(V).D
>
> fgsa_head(V, raw, declared, currentSlot):
>     frame := FJ_FRAME(V)
>     A := deepest live lease target in frame.D, else frame.Z
>     score(B) := raw equivocators
>                 + clean declared supporters whose HEAD extends B
>     eligible(B) := h(B.parent)<frame.lo
>                    or 2*score(B)>number_of_raw_participants
>                    or B.slot=currentSlot
>     return GHOST(A, frame.D, score, eligible)
> ```

> _fj-redteam.md, lines 188–192:_
>
> Full proposal and finality-head reads use OTHER_VIEW. HEADs use
> HEAD_VIEW. A lease outside D stays in the raw guard and release test.
> The code must change both viability and below-band eligibility in a
> contest. Changing only one does not supply the proof that the walk
> reaches H.

- Status: 2026-09-28 — def (r148 claim F1, exact FJ delta, PROVED).
- Note (2026-09-28): the contest test is the local witness of r148 lines
  260–270: an admitted W in the view with `h(W) = j+1` and `J ⋠ W`. By
  ancestor closure this is a conflicting crossing of j in the view, so
  `fj.crossingNoFinal.v1` shows that J cannot finalize. The converse is
  false (r148 F3, REFUTED): J can be unable to finalize without a contest.
  `fg.frameCompat.v1` shows that the `F ⪯ σ[W].J` test selects the same
  pair as "compatible with F" (`env.r151`, line 44).

> _fj-redteam.md, lines 260–270:_
>
> The exact local geometric witness used by FJ at H=j+1 is:
>
> ```text
> exists admitted W in this duty view:
>     h(W)=j+1 and not J⪯W.
> ```
>
> Ancestor closure makes this equivalent to a conflicting crossing of j
> materialized in this view. All frontier blocks extending J is exactly
> the absence of this geometric witness. It is not exactly the absence
> of every possible proof that J cannot finalize.

### `fj.crossingNoFinal.v1` — r148 F2: a conflicting crossing of j proves that J cannot finalize

- Variant `fj`. Source r148 §3 F2, lines 234–258. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `a≤f`, so `2q−n > a`; honest identities follow E1 and E2;
  the uniform timeout maturity of the DC transition.
- Statement (pinned):

> _fj-redteam.md, lines 234–258:_
>
> F2 — PROVED. Suppose J is justified at j and a valid block W has
> h(W)>j with J not a prefix of W. On W's path, take the first crossing
> of j. It consumes q progress identities naming an entry T≠J at j.
> A target QC for T would conflict with J's target QC. Their intersection
> has at least 2q−n>a identities, so an honest identity would violate E2.
> Thus this crossing cannot be an all-target crossing. It needs the
> timeout branch, at the uniform maturity slot.
>
> More precisely, intersect J's target QC with the progress QC for T.
> At least one honest member of the intersection has already targeted J.
> Its row for T cannot be a target; it is a timeout. “Through timeouts”
> therefore means a mixed or all-timeout progress QC with at least one
> honest timeout. It does not mean that every progress row is a timeout.
>
> Now suppose a finality QC for J exists, before or after that crossing.
> Intersect it with the progress QC for T. Again an honest member must
> occur. If its progress row is a target for T, E1 forbids its finality
> pair for J. If it is a timeout, E1 also forbids that pair, regardless
> of the entry named by the timeout. This argument is independent of the
> order of emission. Therefore J has not finalized and cannot finalize
> in any continuation that retains the fault bound and honest client.
>
> This is the argument in [finalized_preceq_of_height_lt][crossing],
> with its direction reversed. It applies to a privately finalized J,
> and to a crossing held only by the adversary.

- Status: 2026-09-28 — PROVED (r148 F2).
- Note: this is the contrapositive form of `fg.finalLock.v1` for one
  justified J: a block above j that does not extend J excludes a
  finalization of J. It is registered for `fj` because FJ uses it in the
  contested phase (`fj.twoChanges.core.v1`); the argument uses only the DC
  certificate rules, so it also holds for `nj`.

### `fj.descent.v1` — descent lemma under FJ

- Variant `fj`. Source r144o §3.1 and §5.3, lines 162–182 and 601–610. File
  `fgsa-no-nj-opus.md`, sha256
  `7df2a540134deddede78ea711754bb322911fced62271868f8b5034164db9f4e`. r148
  §6 (lines 479–527) proves the same descent per actual duty view, with R1
  split cases.
- Hypotheses: `env.r148`; old row, M and first abandonment as defined in
  r144o §1 (lines 108–121).
- Statement (pinned):

> _fgsa-no-nj-opus.md, lines 108–121:_
>
> ```text
> synchronous label s:  v_s ≥ GST (its HEADs reach every reader before e_s).
> old row:              an honest height pair whose source label has v_s < GST.
> M:                    the highest height of an old row (M=1 if none).
> post-GST source:      a fresh fast source C at a synchronous label s.
> abandonment of C:     an honest HEAD at a label s' > s that does not extend C.
> first abandonment:    the earliest abandonment of that C.
> flip:                 a duty frame whose root or band excludes the branch
>                       that the previous honest HEADs extended.
> frontier, level:      H_V of the duty view.
> ```
>
> M is the Opus r143 definition. It is at most DC's archival frontier at
> `r_GST+2`. Every honest row at a height above M has a synchronous label.

> _fgsa-no-nj-opus.md, lines 162–182:_
>
> **Lemma D.** Let (C, v) be the first abandonment of a post-GST source C
> with label s. Then the HEAD view V at v holds a QC with an honest row ρ.
> The row ρ names an entry that conflicts with C, at a height x. Exactly one
> of these holds:
>
> 1. ρ is old, so `x ≤ M`;
> 2. ρ has a post-GST source C′ with label `s′<s`, and the first
>    abandonment of C′ is at or before `v_s < v`.
>
> The height x depends on the cause:
>
> ```text
> ┌──────────────────────────┬──────────────────────────────┬──────────────┐
> │ Cause at v               │ Condition                    │ x            │
> ├──────────────────────────┼──────────────────────────────┼──────────────┤
> │ F root or F floor        │ F_V conflicts with C         │ ≥ σ[C].h     │
> │ band {H−1,H}             │ C's branch in V is below H−1 │ ≥ σ[C].h+1   │
> │ DC J root (Z=J at H=j+1) │ J_V conflicts with C         │ ≥ σ[C].h−1   │
> │ lease or score           │ —                            │ not possible │
> └──────────────────────────┴──────────────────────────────┴──────────────┘
> ```

> _fgsa-no-nj-opus.md, lines 601–610:_
>
> **Lemma D under FJ — PROVED.** Two cases change:
>
> - Uncontested J root: every frontier block of V extends J_V, and C ∈ V
>   conflicts with J_V, so `σ[C].h ≤ H_V−1 = j_V = x`.
> - Strict band: C's branch in V has no block at H_V, so `σ[C].h ≤ H_V−1`.
>   Both QC entries E at `H_V−1` have a frontier descendant. If
>   `σ[C].h=H_V−1`, at least one E differs from C's entry at `H_V−1`, and
>   two different entries at one height conflict. If `σ[C].h<H_V−1`, then
>   `C ⋠ E` (else C has a witness at H_V) and `E ⋠ C` (height). So a row
>   on a conflicting entry exists at `x=H_V−1 ≥ σ[C].h`.

- Status: 2026-09-28 — PROVED (r144o N3 and "Lemma D under FJ — PROVED";
  r148 F9 proof).

### `fj.canonical.v1` — F9: sources above M stay canonical

- Variant `fj`. Source r148 §6 F9, lines 479–486, 518–528 and 549–561. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Hypotheses: `env.r148` (recovery regime); M as in `env.r148`.
- Statement (pinned):

> _fj-redteam.md, lines 479–486:_
>
> F9 — PROVED under the recovery regime.
>
> Let C be a synchronous selected source at label s. Consider its first
> honest HEAD failure after that label. This includes a failure of its
> first transfer at q_s. Its complete path is in the failing view:
> at the first transfer, a surviving honest supporter relays it before
> z_s; at later transfers, the previous honest batch supplies it.
> Accepted F above C already protects C.

> _fj-redteam.md, lines 518–528:_
>
> The source C' of this row extends its conflicting entry and hence
> conflicts with C. If it is old, y≤M. If it is synchronous, its label
> s' must be earlier than s. Equality contradicts same-label genuine
> compatibility. A later label would have an honest supporter departing
> C before the proposed first failure. The supporter of C at v_s
> already witnesses a failure of C' after C's earlier source label s'.
>
> Repeat this step on C'. The labels strictly decrease, so the descent
> terminates at an old row. At each step the new source height is y,
> at least the previous source height. Therefore a lost C has h(C)≤M.
> No selected source above M can be lost.

> _fj-redteam.md, lines 549–561:_
>
> After each retained source transfers, the next all-honest batch covers
> it. Its gate has a genuine result above it and no conflicting live
> lease. Every S therefore covers that source by t_s+10Δ. As in the
> adjudication, retain all source bodies in the induction, not only one
> named entry. Two retained sources at the same state height have the
> same immutable entry. Their later target and timeout rows cannot name
> another entry.
>
> In fact, with nj=false all honest rows at a height y>M are targets.
> There is no old honest height row or old lock at y. An old lock would
> require an old target QC and hence an old honest row at y. Later
> honest sources at y have one entry; the client therefore adopts or
> repeats it, and never creates the first timeout there.

- Status: 2026-09-28 — PROVED (r148 F9). r144o N14 states the same reset
  result, PROVED.
- Note: retention starts at the transfer HEAD `q_s`, not at `v_s`
  (`env.r148`, lines 116–119). r144o N14 (line 615) says "from its label
  on"; r148 corrects this timing.

### `fj.inBandLock.v1` — F10: no lock stall for an in-band source

- Variant `fj`. Source r148 §7 F10, lines 577–597. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Lean plan: DC-fj module (user 2026-09-28).
- Statement (pinned):

> _fj-redteam.md, lines 577–597:_
>
> F10 — PROVED for an in-band selected source. Let C_fg have height m≥lo
> in its full action view. Suppose a lock on J'≠T_c at m suppresses its
> height row. Its finality pair required a justification carrier at
> height at least m+1. This carrier is retained in the full store.
> A same-action finality pair has the same property.
>
> Since m≤H and lo≥H−1, this gives H=m+1 and lo=m. A strict contest would
> give lo=m+1, a contradiction. The lock's J' is compatible with F;
> otherwise finalized crossing or source descent from F already excludes
> this case. Same-height justification uniqueness gives j=m and J=J'.
> The remaining FJ case is uncontested, with root J'. C_fg at height m
> must then have entry J'. This contradicts the mismatched lock.
>
> In a contest, an actual head reaches H. A lock at H would require an
> already known carrier at H+1, contrary to the fixed frontier. Locks at
> H−1 do not block rows at H. Old different targets cause timeouts there,
> which still contribute progress.
>
> This does not say every action has a source, or that every selected
> prefix of a raw result is in band. The no-source and below-band cases
> are handled by the producer in §9. F10 alone is not a liveness theorem.

- Status: 2026-09-28 — PROVED (r148 F10; r144o N15).
- Note (2026-09-28; §0 rule (b)): "finalized crossing" in the pinned text
  is `fg.finalLock.v1`, and "same-height justification uniqueness" is
  `fg.uniqueJust.v1`.
- Note: the old-band variant (FJ root test, band `{H−1,H}`) stalls (r148
  F11, REFUTED by the exact N12 execution, lines 599–711).

### `fj.twoChanges.v1` — F12: at most two effective changes per frontier

- Variant `fj`. Source r148 §8 F12, lines 762–789. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Statement (pinned):

> _fj-redteam.md, lines 762–789:_
>
> F12 — PROVED for effective changes after relay settling. Fix an honest
> archival frontier m during a no-rise interval. After one P margin,
> a maximizing witness is in every duty view. Under a≤f there is at
> most one justified entry at m−1. There are at most these phases:
>
> ```text
> gap: no top J
>     -> uncontested top J
>     -> contested top J
>
> or gap -> contested top J.
> ```
>
> The first top-J evidence and the first contest evidence can each
> interrupt an attempt once. Within P of each event, accepted-object
> relay and a later freeze put the relevant evidence in every view.
> Repeated copies do not start a new phase. Later frontier blocks only
> add witnesses once the phase is settled.
>
> A finalization below m−1 is below every band witness and cannot cause
> an independent exclusion. A finalization at m−1 is the same unique
> top J. It is impossible in the contested phase by F2; in the
> uncontested phase the root already enforces it. A finalization at m
> requires a carrier above m, which ends the no-rise interval.
>
> Hence k_eff≤2, with at most three complete attempts. This count is
> independent of SA's slow-window parameter k. It is not a strictly
> increasing potential on each full/HEAD call.

- Status: 2026-09-28 — PROVED (r148 F12; r144o N16).
- Note: the count is for effective changes after relay settling. For raw
  successive R1 duty frames it is false (r148 F13, REFUTED, lines 737–760).
- Note (r151): r151 confirms F13 as REFUTED (claim table line 24) and
  replays the receipt schedule (r151 §9, lines 801–805). The frame cycle
  occurs below the cap μ, so it does not refute `fj.theoremN.v1`:

> _fj-theorem-h.md, line 24:_
>
> ```text
> │ At most two changes of successive R1 duty frames          │ REFUTED │
> ```

- Status: 2026-09-28 — SUPERSEDED (split agreed with ethereum-f1). The
  settling sentences (lines 763–764 "After one P margin, a maximizing
  witness is in every duty view" and lines 775–777) are run facts:
  `comp.settle.v1`. The phase count is the pure core:
  `fj.twoChanges.core.v1`. Their conjunction is this statement.

### `fj.twoChanges.core.v1` — FJ phases at a fixed frontier (pure core)

- Variant `fj`. Source r148 §8 F12, lines 764–773 and 778–789. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Lean plan: DC-fj module (user 2026-09-28).
- Hypotheses: `fj.frame.v1`; `fg.uniqueJust.v1` (at most one justified
  entry at m−1); `fg.finalLock.v1`; `fj.crossingNoFinal.v1` (the "F2" of
  line 783, r148 numbering).
- Statement (registry): fix a frontier m in a no-rise interval. Let
  J_(m−1) be the justified entry at m−1, if one exists. For an honest duty
  d with `H_d = m`, let `E_J(d)` mean "V_d holds a carrier of J_(m−1)",
  and `E_C(d)` mean "V_d holds a block of height m that does not extend
  J_(m−1)". Then:
  1. The effective FJ frame `(H_d, lo_d, Ẑ_d)` is a function of the phase
     of d: gap (not `E_J(d)`): `(m, m−1, ◇)`; uncontested (`E_J(d)` and not
     `E_C(d)`): `(m, m−1, J_(m−1))`; contested (`E_J(d)` and `E_C(d)`):
     `(m, m, ◇)`.
  2. Each evidence bit is false at every duty before the first time an
     honest store holds that evidence (views are subsets of stores). If
     each bit, once true at every duty from some time, stays true, then
     the phases occur in the order gap → uncontested → contested, or gap
     → contested. So there are at most two effective changes per frontier,
     one for each evidence event.
  3. Finalizations add no change: below m−1 they are below every band
     witness; at m−1 it is the same J_(m−1), impossible in the contested
     phase (`fj.crossingNoFinal.v1`) and enforced by the root in the
     uncontested phase; at m it needs a carrier above m, which ends the
     no-rise interval.
  The core does not say when the bits become true at every duty.
- Statement (pinned):

> _fj-redteam.md, lines 764–773 (excerpt; from "Under a≤f"):_
>
> Under a≤f there is at most one justified entry at m−1. There are at
> most these phases:
>
> ```text
> gap: no top J
>     -> uncontested top J
>     -> contested top J
>
> or gap -> contested top J.
> ```

> _fj-redteam.md, lines 778–789:_
>
> Repeated copies do not start a new phase. Later frontier blocks only
> add witnesses once the phase is settled.
>
> A finalization below m−1 is below every band witness and cannot cause
> an independent exclusion. A finalization at m−1 is the same unique
> top J. It is impossible in the contested phase by F2; in the
> uncontested phase the root already enforces it. A finalization at m
> requires a carrier above m, which ends the no-rise interval.
>
> Hence k_eff≤2, with at most three complete attempts. This count is
> independent of SA's slow-window parameter k. It is not a strictly
> increasing potential on each full/HEAD call.

- Status: 2026-09-28 — PROVED (a≤f; r148 F12 without its settling
  sentences; r144o N16).
- Note: the count is for settled phases, not for raw successive R1 duty
  frames (r148 F13, REFUTED; r151 line 24). Between an evidence event and
  its settling, duties can disagree on the phase.
- Composition: with `comp.settle.v1`, each evidence bit is true at every
  duty from (first store time)+θ, or +P in r148's margin. This gives the
  full r148 F12 count.

### `fj.armedSafe.v1` — F7: clean safety and P1 under FJ

- Variant `fj`. Source r148 §5 F7, lines 398–413 and 431–443. File
  `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Statement (pinned):

> _fj-redteam.md, lines 398–413:_
>
> F7 — PROVED under the original base premises.
>
> Every target or progress QC contains an honest row because q>a. Each
> honest height row has a successful fresh fast source, with τ>a surviving
> supporters. Its named entry is an ancestor of that source. Finality has
> an earlier justified target origin.
>
> In a clean run the adjudicated induction retains all genuine source
> bodies, including a raw result whose write was vetoed. Their controlling
> entries lie on one retained chain. Two different entries at the same
> height cannot both have those honest origins. Hence no FJ contest can
> occur in the clean induction. FJ has the same choice as the adjudicated
> rule, including its exact proposal/HEAD comparison and pending-gate step.
> Clean safety, monotonicity, and honest-proposal inclusion in 6Δ follow
> for all a<h. This uses [fgsa-adjudicate §3.2](fgsa-adjudicate.md), not
> the incorrect whole-view inclusion shortcut in fgsa-fast-opus §3.2.

> _fj-redteam.md, lines 431–443:_
>
> Consequently the strict band retains B. F and J are comparable with B.
> A root above B already covers it; otherwise its live lease is an
> effective anchor. FJ cannot create the first departure. Conflicting
> release support is at most a<τ. Pending renewal, expiry, and the raw
> whole-result guard are exactly the adjudicated outage proof.
>
> The constants remain:
>
> ```text
> fast P1:  lag 4Δ, with h_t≥τ throughout the required healthy prefix;
> slow P1:  lag L−3Δ, with its original healthy-prefix premises;
> outage budget: Π=min(η,L).
> ```

- Status: 2026-09-28 — PROVED (r148 F7; r144o N13).

### `fg.base.fj.v1` — FJ reset and base handoff witness

- Variant `fj` (moved from §3 of v1). Source r148 §9 F14, lines 852–900.
  File `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Hypotheses: `env.r148`; `fj.canonical.v1`; `fj.inBandLock.v1`;
  `fj.twoChanges.core.v1`; `comp.settle.v1`.
- Note (2026-09-28; §0 rule (a)): `fj.twoChanges.v1` was replaced by
  `fj.twoChanges.core.v1` and `comp.settle.v1`. The cut `u0` and M0 of the
  witness are `comp.cut.v1`.
- Returned witness (audit W09): the caps M ≤ M0 and the cut `u0`
  (`env.r148`); an honest row at height ≥ M0+1 > M by `B_R`; its fresh
  source, permanent by `fj.canonical.v1` from its transfer HEAD; the repair
  start and `B_base`. FJ has no NJ arm. An actual finalized checkpoint F*
  above the cut can serve as an earlier reset (r148 §5, lines 471–475).
- Statement (pinned):

> _fj-redteam.md, lines 852–900:_
>
> Thus the old conservative (3g+6)P producer budget covers both cases.
> Non-opening consumption can only finish the required rise earlier.
> One attempt, including settling and alignment, costs at most
>
> ```text
> c       = ceil(ρ/P)
> w       = c+3g+8
> P+ρ+P+(3g+6)P ≤ wP.
> ```
>
> At most two phase events interrupt an attempt. If an event arrives
> after an attempt would have completed, the frontier has already
> risen. Otherwise charge that event once and restart with its own
> settling margin and local repair. Therefore
>
> ```text
> β_FJ = 3w = 3ceil(ρ/P)+9g+24
> ```
>
> is a sufficient number of rounds per frontier rise. No common global
> SA handoff was assumed to obtain those rises. In particular, a
> permanent lock or record stall is impossible under these recovery
> premises, including when every action initially has an empty source.
>
> At u0 the honest archival maximum is M0. A crossing to M0+2 requires
> an honest row at M0+1 or higher, because every progress QC contains
> an honest signer and advances only one height. Its height exceeds
> M, so §6 makes its source permanent. Two frontier rises suffice to
> force such a row. Since u0<GST+3P,
>
> ```text
> B_R = P[3+2β_FJ]
> ```
>
> bounds the existence of this reset row, and also the public height
> rise used to force it. A statement that *all duty views already see
> the high witness* needs the extra settling margin. Do not silently
> replace the event bound by that duty-view claim.
>
> From the reset, retain all selected source bodies. Allow P for a
> common start and then run the new SA source-window calculation for
> raw fast and slow sources, including older leases on divergent
> descendants of the retained prefix. The exact repair proposal
> replaces old S tips and starts the safe, monotone suffix with 6Δ
> service. This is fgsa-adjudicate §5.3 with FJ's descent result:
>
> ```text
> B_base = B_R+P+ρ.
> ```

- Status: 2026-09-28 — PROVED (r148 F14, paper bounds at the level of the
  adjudicated r143 producer). Example (`R=3, k=2, G=8Δ, g=3`):
  `B_R = 1476Δ`, `B_base = 1518Δ` (r148 §11, lines 988–989).
- Note: r144o N17 (lines 645–677) marks the same bounds SKETCH, because the
  contested-band producer port was missing. r148 §9 supplies that port. This
  entry does not discharge HNI (§4 introduction).
- Note (r151): the reset witness is now pinned as `fj.reset.v1`. This
  entry keeps the supplied arrival `B_R` and handoff `B_base`; r151
  §5.4 uses `B_R` as the supplied uniform producer.

### `fj.firstFinality.v1` — F17: first finality after damage

- Variant `fj`. Source r148 §10 F17, lines 941–945. File `fj-redteam.md`,
  sha256 `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`.
- Statement (pinned):

> _fj-redteam.md, lines 941–945:_
>
> F17 — SKETCH for the post-damage numerical expression
>
> ```text
> B_first = B_base+(g+2)P+9Δ.
> ```

- Status: 2026-09-28 — SKETCH (r148 F17; three timed steps are missing,
  lines 947–966).

**FJ composite entries (`Kit.Compose`, from r151).** r151 renames the
caps. Its μ is the old-source cap that r148 and r144o call M. Its M is
the DC cut maximum at `u_0` that r148 calls M0. The entries below use the
r151 names; `μ ≤ M`.

### `fj.reset.v1` — reset at the first honest row of height M+1

- Variant `fj`. Source r151 §2, lines 106–143. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; `fj.frame.v1`; `fg.causalCap.core.v1`;
  `comp.cut.v1`; `fg.finalLock.v1`.
- Note (2026-09-28; §0 rules (a) and (b)): `fg.causalCap.v1` was replaced
  by `fg.causalCap.core.v1` and `comp.cut.v1`. `fg.finalLock.v1` is the
  "finalized crossing" of the pinned text.
- Returned witness (audit W09): the cut `u_0`, its maximum M and the
  old-source cap μ ≤ M; r* = the least round with an honest row at
  height M+1, `b = s* = r*R`, and its fresh fast source C* with
  `ht(C*) = M+1`; every honest row at height ≥ M+1 has source label ≥ b;
  first-transfer view facts at `q_b`: every freeze `z_b` has the C* path,
  each transfer frame has H = M+1, and C* is kept. FJ has no NJ or
  finalized case split; an actual finalized reset F* can replace the cut
  only with its source-label boundary (r151 §7.2, lines 639–645).
- Statement (pinned):

> _fj-theorem-h.md, lines 106–143:_
>
> There are two related maxima. Keep them distinct:
>
> ```text
> μ = max({1} ∪ {height of an honest row with source v_s<GST});
> r_G = first action round at or after GST;
> u_0 = a_(r_G+2), with its inclusive event prefix;
> M = honest archival maximum at u_0.
>
> μ≤M;       GST+2P≤u_0<GST+3P.
> ```
>
> Here M is the DC cut maximum, called M0 in r148. The old-source cap
> called M in r148 and in the descent lemma is μ here. This distinction
> is needed for the two-rise arrival proof.
>
> Let r* be the least round containing an honest row at height M+1.
> Set `s*=r*R`, `b=s*`, and let C* be a selected fresh fast source of
> such a row. Then `ht(C*)=M+1`. A higher row cannot precede this row:
> its source path must first cross M+1, and that crossing needs an
> honest row at M+1. Thus every honest row at height at least M+1
> has source label at least b. The cut and causal cap make b a wholly
> synchronous label.
>
> This is the required reset. “Above M+1” must not mean that one must
> wait for a row of height M+2. The first row at M+1 already suffices.
> Equivalently, this is Lemma R with predecessor x=M. One can use the
> earlier cap μ for a local reset; the cut maximum M gives the stated
> arrival accounting without an additional search.
>
> The transfer boundary is `q_b=a_(r*)−Δ`, not the action time a_(r*).
> A surviving honest supporter of C* sends its complete path at v_b.
> Relay places that path in every freeze z_b. At q_b no carrier above
> M+1 can already exist: such a carrier would require an earlier
> honest row at M+1. Thus each transfer frame has H=M+1. If it roots
> at J of height M, the absence of a contest means `J⪯C*`. If C*
> conflicts with J, C* itself forces the contest and witnesses lo=M+1.
> The F case follows from finalized crossing. Therefore C* is kept at
> its first transfer, including when readers see different old J evidence.

- Status: 2026-09-28 — PROVED (r151 claim table line 21).

### `fj.theoremN.v1` — Theorem N for all protected fast and slow bodies

- Variant `fj`. Source r151 §3.2 and §4, lines 204–214, 246–249, 267–269 and
  290–291. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; `fj.reset.v1`; `fj.canonical.v1` (r151 §3.1
  re-proves F9 with the source boundary explicit and the cap μ);
  `ap.S.v2`; `ap.Sslow.v1`; `fg.provenance.v2`; `ap.fastSupport.v1`;
  `comp.provenance.v1`. No service entry is used.
- Note (2026-09-28; §0 rule (a)): `fg.provenance.v1` was replaced by
  `fg.provenance.v2`, `ap.fastSupport.v1` and `comp.provenance.v1`.
- Protected set: 𝒫 = all fast bodies at labels ≥ b and all slow bodies
  whose window lies in `[b,∞)` (blueprint §7.1), as for
  `comp.fgHealed.v1`.
- Statement (pinned):

> _fj-theorem-h.md, lines 204–214:_
>
> **High contest exclusion — PROVED.** A contest at H=j+1 with j≥M+1
> would give a justified J at j and a conflicting crossing of j. Each
> QC contains an honest row. Those rows would name different entries
> at j, contrary to the preceding result. This also excludes a private
> conflicting carrier. Consequently every post-reset duty satisfies
>
> ```text
> H_d≥M+1;
> contest_d ⇒ H_d=M+1;
> lo_d ≤ max(M+1,H_d−1).
> ```

> _fj-theorem-h.md, lines 246–249:_
>
> Let 𝒫 be exactly the protected family in blueprint §7.1: all successful
> fast bodies at labels s≥b and all successful slow bodies whose complete
> k-label windows lie in `[b,∞)`. Include qualifying prefixes, not only
> the deepest FG-selected source. Put `q(B)=q_s` for a body of label s.

> _fj-theorem-h.md, lines 267–269:_
>
> **Lemma K_FJ — PROVED.** Fix an honest duty d after q_b and a present
> body B with q(B)≤t_d. Suppose B is compatible with C* and with every
> earlier controlling high source, of height at least M+1. Then B is kept.

> _fj-theorem-h.md, lines 290–291:_
>
> **Theorem N_FJ — PROVED.** For every B∈𝒫 and every honest choice duty
> d with `t_d≥q(B)`, B is kept. S1, S2, and S3 therefore hold forever.

- Status: 2026-09-28 — PROVED (r151 claim table lines 20 and 22).
- Note: this is the FJ counterpart of `comp.theoremN.v1` and
  `comp.fgHealed.v1`. It does not use HNI: an active J at M precedes C*
  by the frontier test (r151 lines 273–275).

### `fj.rise.fixedF.v1` — literal-N1 split and M-dependent arrival

- Variant `fj`. Source r151 §5.1–§5.3, lines 328–332, 371–374 and 384–398.
  File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses (audit W02): the FJ port of `comp.rise.fixedF.v1`, with lo
  fixed and the contested threshold m (r151 §5.2, lines 342–355);
  `fj.twoChanges.core.v1`; `fj.inBandLock.v1`; `comp.settle.v1` (the
  settling constant θ = 4Δ); `fj.reset.v1` (a crossing to M+2 needs the
  reset row). It is a comp-level rise, not an AP service fact.
- Note (2026-09-28; §0 rule (a)): `fj.twoChanges.v1` was replaced by
  `fj.twoChanges.core.v1` and `comp.settle.v1`.
- Statement (pinned):

> _fj-theorem-h.md, lines 328–332:_
>
> For FJ, literal N1 must fix `(H,F,Z,lo)`, not only `(H,F,Z)`.
> Effective N1 fixes `(H,lo,Zhat)`, where Zhat records the active top-J
> restriction or the absence of that restriction; lower common-trunk F
> advances are allowed. This explicit lo coordinate is necessary even
> if a root name happens to stay equal during a phase change.

> _fj-theorem-h.md, lines 371–374:_
>
> With literal N1, additionally charge lower F advances. If n_F(m) is
> their count at frontier m, the bound is `(3+n_F(m))W`. Evidence
> delivered to different readers is one event with one settling interval,
> not n events for n readers.

> _fj-theorem-h.md, lines 384–398:_
>
> Let f_0 be the least honest finalized height at u_0. Before the first
> arrival at M+2, every accepted F has height at most M: its evidence
> contains a carrier of height at least `ht(F)+1`. Thus distinct lower
> F advances total at most M−f_0. A finalization which itself gives a
> carrier at M+2 ends the search and needs no new attempt. Literal
> composition gives the **PROVED**, M-dependent bound
>
> ```text
> a_(r*) < GST+A_lit;
> A_lit = 3P+[6+M−f_0](λ+4Δ).
> ```
>
> Allowing one extra terminal F event gives the weaker expression with
> `7+M−f_0`; it is also valid. Neither expression is a uniform bound
> independent of the damaged prefix.

- Status: 2026-09-28 — PROVED (r151 claim table line 25). Example
  (`Δ=1, R=3, k=2, G=8, g=3`, `M=1, f_0=0`):
  `B_lit = A_lit + δ_H = 1498Δ` (r151 line 720).

### `fj.rise.movingF.v1` — effective-N1 split and arrival

- Variant `fj`. Source r151 §5.2–§5.3, lines 357–364 and 400–412. File
  `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: effective (L) for the FJ frame, with effective N1 fixing
  `(H,lo,Zhat)` (r151 lines 329–331); `fj.twoChanges.core.v1`;
  `comp.settle.v1` (θ = 4Δ).
- Note (2026-09-28; §0 rule (a)): `fj.twoChanges.v1` was replaced by
  `fj.twoChanges.core.v1` and `comp.settle.v1`.
- Statement (pinned):

> _fj-theorem-h.md, lines 357–364:_
>
> If effective (L) holds with a uniform λ, split at the first top-J and
> contest events. If an event has not occurred by the end of a complete
> settled attempt, (L) already gives a rise. Otherwise settle its evidence
> and restart. With two interruptions the bound is
>
> ```text
> one height rise: at most 3(λ+4Δ).
> ```

> _fj-theorem-h.md, lines 400–412:_
>
> With effective (L) the **PROVED conditional implication** is
>
> ```text
> a_(r*) < GST+A_eff(λ);
> A_eff(λ) = 3P+6(λ+4Δ).
> ```
>
> Effective (L), for every reachable pre-reset start with the candidate
> `λ=ρ+2σ`, remains OPEN. r149/r150's missing common supported band
> prefix can occur as an obligation in an ordinary FJ phase too. The
> trunk lemma compares two roots within one view; it does not supply
> that prefix across different views. Neither the stricter contested
> band nor the count of two events proves this missing service premise.

- Status: 2026-09-28 — OPEN as a result from the execution premises
  alone (r151 claim table line 27). The split and arrival implication
  from effective (L) is PROVED (r151 claim table line 26).
- Note: the missing premise is the same common supported band prefix as
  `ap.reach.v1` (r151 lines 408–412).

### `fj.Xplus.v1` — FJ (X+), band stated with lo

- Variant `fj`. Source r151 §6.2, lines 464–485. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; x0–x3 as pinned, with the threshold `lo_d` of
  each compared read.
- Statement (pinned):

> _fj-theorem-h.md, lines 464–485:_
>
> Use r149's (X+) proof with the actual threshold lo_d. Specifically,
> for an honest proposal P with parent A require:
>
> ```text
> x0: A is the ordinary proposal walk result, with no lease start.
> x1: every live lease at each same-slot honest HEAD precedes A.
> x2: every compared FG root precedes A, and ht(A)≥lo_d.
> x3: some T⪯A is present and kept at all compared reads,
>     every honest preceding-label HEAD contains T,
>     and ht(T)≥max_d lo_d.
> ```
>
> Then every honest HEAD names exactly P and every honest S contains P
> at d_u. This is **PROVED** by the r149 transport argument. Below T,
> all h honest supporters give strict score dominance. At or above T,
> the below-band clause is off in every compared view. Any old majority
> competitor has an honest supporter whose path reached the proposer;
> it was already available to the ordinary parent comparison. A new
> unsupported F-basis edge has no such majority. The unique current-slot
> child P is eligible and available. These comparisons give exact P.
> At q_u its h≥τ clean votes release every conflict, and its d_u raw
> result is exactly P.

- Status: 2026-09-28 — PROVED (r151 claim table line 28).
- Use rule (audit W03): a composite must prove x0–x3 at each call. The
  form `ht(T) ≥ max H_d−1` of `ap.Xplus.v1` alone does not suffice in a
  contest (r151 lines 487–489).

### `fj.healed.v1` — Theorem H for FJ and the proved bound

- Variant `fj`. Source r151 §7.3 and §8, lines 649–663 and 722–736. File
  `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `env.r151`; `fj.reset.v1`; `fj.theoremN.v1`; `ap.S.v2`;
  `ap.Sslow.v1`; `fj.Xplus.v1`; for the global clause also
  `fj.rise.fixedF.v1` (literal route) and the supplied r148 F14 arrival
  `B_R` (`fg.base.fj.v1`). It does not use `fj.rise.movingF.v1`.
- (X+) discharge (audit W03): at each honest proposal with `u ≥ ℓ+1`,
  `ℓ = b+2k−1`, r151 proves x0 and x1 (§6.3, lines 493–508) and x2 and
  x3 with `ht(T) = max(M+1, m_u−1) ≥ lo_d` (§6.4, lines 512–547),
  including views that disagree on the contest bit.
- Clauses: (local) `t_h ≤ q_(s*)+2L+G−Δ` (§7.3), with no arrival input.
  (global) `t_h < GST+B_proved` (§8), uniform choice
  `B_FJ,H = B_R+δ_H`.
- Statement (pinned):

> _fj-theorem-h.md, lines 649–663:_
>
> Under §1 and the actual reset in §2, all protected bodies have permanent
> FG non-interference from their own transfer times. There is a repair
> gate t_h such that, from t_h onward, all honest S values form one
> chain, each S is monotone, each accepted honest F precedes every
> honest S, and every honest proposal emitted from t_h onward is included
> in every honest S within 6Δ. The available accessor is then S.
>
> The bound is
>
> ```text
> t_h=d_u≤t_ℓ+G+6Δ
>           =t_b+2L+G+4Δ
>           =q_(s*)+2L+G−Δ
>           =a_(r*)+2L+G−2Δ.
> ```

> _fj-theorem-h.md, lines 722–736:_
>
> **Final healing theorem for FJ — PROVED.** Under §1, with r148 F14
> as a supplied proved arrival result, define
>
> ```text
> B_proved=min(3P+[6+M−f_0](ρ+2σ+4Δ),
>              P[3+2(3ceil(ρ/P)+9g+24)])+2L+G−2Δ.
> ```
>
> There exists `t_h<GST+B_proved` from which all honest S values lie
> on one chain, each honest S is monotone, every accepted honest F
> satisfies `F⪯S_i` at every honest reader i, and every honest proposal
> emitted in this suffix is included in all honest S values within 6Δ.
> Thus `available=S` throughout this suffix. The uniform proved choice
> is **B_FJ,H**, which is **1496Δ** for the first example. Independently
> of the arrival route, `t_h≤q_(s*)+2L+G−Δ` at the actual reset.

- Status: 2026-09-28 — PROVED (r151 claim table lines 29–32). Example
  (`Δ=1, R=3, k=2, G=8, g=3`): `B_FJ,H = 1496Δ`, 22Δ below r148's
  `B_base = 1518Δ` (r151 lines 705–716).

### `fj.healedUnif.v1` — uniform bound under effective N1

- Variant `fj`. Source r151 §8, lines 692–698. File `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Hypotheses: `fj.rise.movingF.v1` (OPEN); the local clause of
  `fj.healed.v1`.
- Statement (pinned):

> _fj-theorem-h.md, lines 692–698:_
>
> The **PROVED conditional** uniform expression is
>
> ```text
> effective (L) with λ ⇒ B_eff(λ)=3P+6(λ+4Δ)+δ_H.
> ```
>
> Its use with `λ=ρ+2σ` as a bound from execution premises alone is OPEN.

- Status: 2026-09-28 — OPEN as a bound from the execution premises
  alone; the implication is PROVED (r151 claim table lines 26–27).
  Example with `λ = ρ+2σ`: 1292Δ, conditional (r151 line 708).

### `fj.healedAtQ.v1` — full healing already at `q_(s*)`

- Variant `fj`. Source r151 §3.3 and §7.3, lines 241–242 and 668–669. File
  `fj-theorem-h.md`, sha256
  `16b69dba55d889b9ae20dd55b228cfd83ad22037d796c6219cdb65831718bba3`.
- Statement (pinned):

> _fj-theorem-h.md, lines 241–242 (excerpt; line breaks reflowed):_
>
> Full healing of arbitrary S tips exactly at q_b is still OPEN.

> _fj-theorem-h.md, lines 668–669 (excerpt; line breaks reflowed):_
>
> Immediate full healing at q_b is not established by this argument.

- Status: 2026-09-28 — OPEN (r151 claim table line 33).

## 5. Composite entries (`Kit.Compose`, `SimplexFG.nj`)

The first three entries (added 2026-09-28) are variant `both`. They are
the run parts of the f1 splits (§8).

### `comp.provenance.v1` — each honest-containing QC has an honest-supported source

- Variant `both`. Sources: r146 §3.1, lines 244–247 (file
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`); r148
  §5 F7, lines 400–403 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`). Rule
  source: r143 §3.1, lines 226–237 (pinned in `ap.honestSourced.v2`).
- Hypotheses: `fg.provenance.v2`; `ap.honestSourced.v2` (the Simplex
  source rule: the row source is the signer's `C_fg`, a member of
  `FastWrite_i[s]`); `ap.fastSupport.v1`.
- Statement (registry): every target, progress or finality QC contains an
  honest row (`fg.provenance.v2`; for a finality QC, through its earlier
  justified target). The source C of an honest height row is the signer's
  `C_fg`, so C is a successful fast write at the signer, and C has an
  honest supporter (`ap.fastSupport.v1`). The row's entry T satisfies
  `T ⪯ C`. Thus every QC with an honest row has an honest-supported
  source.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 244–247:_
>
> Every progress or target QC contains an honest height row since `q_F>a`.
> Its entry T is a prefix of its successful fast source C. Each such C
> has an honest supporter since `τ>a`. Finality names an already justified
> entry and thus has this earlier target origin.

> _fj-redteam.md, lines 400–403:_
>
> Every target or progress QC contains an honest row because q>a. Each
> honest height row has a successful fresh fast source, with τ>a surviving
> supporters. Its named entry is an ancestor of that source. Finality has
> an earlier justified target origin.

- Status: 2026-09-28 — PROVED (FG-SA; r146 §3.1; r148 F7).
- Note: this is the Simplex-policy part of the SUPERSEDED
  `fg.provenance.v1`. It holds for the Simplex source rule only, not for
  every policy σ (§0).

### `comp.settle.v1` — relay and freeze settle store objects into duty views

- Variant `both`. Sources: bp §4.2 item 1, lines 385–390 (file
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r149
  §3, lines 305–315 (file `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`); r148
  §8 F12, lines 763–764 and 776–777 (file `fj-redteam.md`, sha256
  `934fe2927f047a11e37dbe52aba9d754d5c461927f24b91902077f17459d47d2`).
- Hypotheses: `env.r149` (strict Δ delivery and accepted-object return
  relay after GST); R1 duty views (the HEAD at `v_s` freezes at
  `z_(s−1) = t_s − Δ = v_s − 2Δ`); the object is held by an honest store at
  a time `w ≥ GST`.
- Statement (registry): let an honest store hold an object at `w ≥ GST`.
  The object is in every honest full view from `w+Δ` and in every honest
  HEAD view at a HEAD time `≥ w+θ`, θ = 4Δ. Views are subsets of stores,
  and stores only grow. Consequences: (1) if the honest frontier first
  equals m at t_m and rises at t_up, then `H_d = m` at every honest duty in
  `[t_m+θ, t_up)`; (2) an evidence object first held by an honest store at
  t_e is in no duty view before t_e and in every duty view from
  `max(t_e, GST)+θ`. r148 uses the larger margin P ≥ θ.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 385–390:_
>
> 1. **Settling.** Every object that an honest store holds at t is in every
>    honest full view from t+Δ, and in every honest HEAD view at a time
>    ≥ t+θ. Proof: relay gives receipt by t+Δ at every honest reader. A HEAD
>    at `v_s ≥ t+4Δ` has freeze `t_s−Δ ≥ t+2Δ`. Since views are subsets of
>    stores, `H_d ≤ m` while the frontier is m. Thus `H_d = m` at every
>    honest duty in `[t_m+θ, ·)` until the frontier rises.

> _fgsa-conditional-close.md, lines 305–315:_
>
> Suppose a controlling object is accepted by an honest reader at time w.
> Strict relay delivers it to every honest full view before `w+Δ`. A HEAD
> at time v freezes at `v−2Δ`. If `v ≥ w+4Δ`, that freeze is at least
> `w+2Δ`, after delivery. Its frozen view contains the complete object.
> The retained F basis supplies the required accepted-control evidence.
>
> This proves settling at every duty after `w+4Δ`. Under the strict cutoff
> convention, `3Δ` also suffices: a freeze at `w+Δ` is after all strict
> receipts. This file uses only **4Δ** in bounds. It avoids a change of
> constant when a statement is read with a non-strict delivery endpoint.
> It is a sufficient constant, not a lower bound.

> _fj-redteam.md, lines 763–764 (excerpt; line breaks reflowed):_
>
> After one P margin, a maximizing witness is in every duty view.

> _fj-redteam.md, lines 776–777 (excerpt; line breaks reflowed):_
>
> Within P of each event, accepted-object relay and a later freeze put the
> relevant evidence in every view.

- Status: 2026-09-28 — PROVED (FG-SA; bp §4.2 item 1; r149 §3, M4).
- Note: this is the run part of the SUPERSEDED `fg.oneBullet.v1` and
  `fj.twoChanges.v1`. It is a statement about delivery and R1 views, not
  about FG rules. For an object held only before GST, the return-relay
  premise gives the same bound from GST.

### `comp.cut.v1` — the DC cut `u_0` and its maximum M

- Variant `both`. Sources: r144 §2.2, lines 168–193 (file `fgsa-no-nj.md`,
  sha256 `1eaf728ffc4d56cc54fbccf581a8dffe457da02b96bd59cedb012bbf5ee1e03a`);
  bp §1.2, lines 138–140 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Hypotheses: `fg.causalCap.core.v1`; the action schedule
  `a_r = T_r+6Δ`, `T_r = rP`; for clause 4, `comp.settle.v1`.
- Statement (registry):
  1. Definition: r_G = the first action round with `a_(r_G) ≥ GST`;
     `u_0 = a_(r_G+2)`, with its inclusive event prefix; M = the honest
     archival frontier at `u_0`.
  2. `GST+2P ≤ u_0 < GST+3P`.
  3. Every honest height row emitted in the prefix has height at most M.
     A carrier whose honest rows all come from the prefix has height at
     most M+1 and justified height at most M (`fg.causalCap.core.v1` with
     this M).
  4. At a duty with `H_V ≥ M+2`, an old-only justification has
     `j ≤ M < H_V−1`, so it is not the active root. H_V is the duty view's
     own maximum: an archival rise acts only after it reaches the view
     (`comp.settle.v1`).
- Statement (pinned):

> _fgsa-no-nj.md, lines 168–193:_
>
> Use exactly the requested cut:
>
> ```text
> r_G = first action round at or after GST;
> u0  = a_(r_G+2), inclusive event prefix;
> M   = honest archival frontier at u0.
> ```
>
> Every honest height row in that prefix has height at most M, because its
> source was already in its signer's store. Every crossing has an honest
> row, since `q_F>a`. Hence a carrier whose height evidence uses only such
> old honest rows has height at most M+1, and its justified height is at
> most M. Faulty rows can be new; without a new honest row they cannot
> cross the next height. This includes a newly constructed carrier with
> old target rows. See [fg-frame-recovery §§2.3–2.4](fg-frame-recovery.md)
> and [WeakHeightBounds][height-bound].
>
> At a duty with `H_V≥M+2`, an old-only justification satisfies
>
> ```text
> j_old≤M < H_V−1,
> ```
>
> so it cannot be the active root. This is a duty-view statement. An
> archival rise must first reach the frozen HEAD view. Allow the R1 relay
> and freeze margin; do not substitute an unseen archival maximum.

> _fgsa-healing-blueprint.md, lines 138–140:_
>
> Let r_G be the first action round with `a_(r_G) ≥ GST`. The DC cut is the
> inclusive event prefix at `u_0 = a_(r_G+2)`. Then `GST+2P ≤ u_0 < GST+3P`.
> Let M be the honest archival frontier at u_0. As in DC,

- Status: 2026-09-28 — PROVED (r144 claims N1 and N2; r147 §6; bp §1.2).
- Note: this is the run part of the SUPERSEDED `fg.causalCap.v1`. The FJ
  entries call this M "M0" (r148) or "M" (r151). The old-source cap of
  `env.r148` (μ in `fj.reset.v1`) is at most this M.

### `comp.rise.fixedF.v1` — height rise under literal N1

- Variant `nj`. Source r147 §5, lines 409–429 (statement); proof lines
  435–523. File `fgsa-conditional.md`, sha256
  `940e481501f8c52f57bd7110faa442b54ce4aa3bb512769a07c9b769037ea0f5`.
- Hypotheses (audit W02): the AP service facts `ap.repair.fixedF.v1`,
  `ap.source.v1`, `ap.rowService.v1` and `ap.carrierKeep.v2`, specialized
  to the Simplex policy; the Simplex client and transition: the lock
  cases (r147 lines 451–483), `fg.provenance.v2`, `ap.fastSupport.v1`,
  `comp.provenance.v1`, row folding at the exact entry, maturity and
  consumption (r147 lines 485–507); `env.r147` (premises 4 and 5);
  `fg.N1.v1` with F and Z fixed on `[u,min(t_up,u+B_static))`; `u ≥ GST`.
- Note (2026-09-28; §0 rule (a)): `fg.provenance.v1` was replaced by
  `fg.provenance.v2`, `ap.fastSupport.v1` and `comp.provenance.v1`.
- Statement (pinned):

> _fgsa-conditional.md, lines 409–429:_
>
> **Exact statement (L).** Under §1, let `u≥GST` and let the honest
> archival frontier at u be m. Let t_up be the first later time at which
> that frontier exceeds m, or infinity if there is none. Suppose fixed
> F and Z make N1 hold on `[u,min(t_up,u+B_static))`, and suppose the
> execution premises and horizon are available through `u+B_static`.
> Then `t_up≤u+B_static`; that is, a rise above m occurs by
>
> ```text
> u+B_static = u+ρ+2σ,
> ρ = 2L+G+8Δ,     σ = (g+3)P+G+6Δ.
> ```
>
> If no earlier rise ends the interval, base repair completes by u+ρ.
> Every later honest proposal whose full service interval remains in
> that interval receives exact honest HEAD service and a fresh fast
> write at all honest readers at its +6Δ gate. A selected honest
> opening supplies `C_fg` and a nonempty matching target or timeout row
> at every honest validator. Its next two honest slot proposers carry
> the branch and fold the rows. At most two such production steps are
> needed to exceed m. Statements about duties after the first rise are
> not part of (L).

- Status: 2026-09-28 — PROVED (FG-SA; r147 §5). r149 §4.4 (lines
  443–445) confirms that the literal-N1 form stays PROVED.
- Note: this is the statement of the withdrawn `ap.L.fixedF.v1`, refiled
  in `Kit.Compose`. It states FG progress, so it holds for the Simplex
  policy only.

### `comp.rise.movingF.v1` — height rise under effective N1

- Variant `nj`. Source r149 §4.4, lines 436–441. File
  `fgsa-conditional-close.md`, sha256
  `1ea1ccc5c944335b7e7793afe2c6675a056762e35eeaeee13ec1f6066460a902`.
- Hypotheses: `ap.repair.movingF.v1` (OPEN), `ap.source.v1`,
  `ap.rowService.v1`, `ap.carrierKeep.v2`, the Simplex client and
  transition as in `comp.rise.fixedF.v1`; `env.r149`; `fg.N1eff.v1` on
  `[u,u+λ]`; `u ≥ GST`.
- Statement (pinned):

> _fgsa-conditional-close.md, lines 436–441:_
>
> > **(L), OPEN under effective N1.** Set `u_L=GST` and
> > `λ=ρ+2σ`, where `σ=(g+3)P+G+6Δ`. For every `u≥u_L`, m, and Zhat,
> > if the honest archival frontier at u is m and
> > `N1(u,u+λ;m,Zhat)` holds, then the frontier at `u+λ` exceeds m.
> > All execution, proposer, row-inclusion, and horizon premises in §1
> > apply. The initial reachable base state at u is arbitrary.

- Status: 2026-09-28 — OPEN (r149 claim table line 32; r150 claim table
  line 25). The proposed M1 argument is SKETCH (r149 line 33).
- Notes: this is the statement of the withdrawn `ap.L.movingF.v1`,
  refiled in `Kit.Compose`. The only missing input is
  `ap.repair.movingF.v1` (r149 lines 443–450); `ap.reach.v1` suffices for
  it (r150 §5). bp marks the same claim H16 SKETCH (bp §10, lines
  1086–1101); r149 §4.3 shows that the bp argument misses one case.

### `comp.theoremN.v1` — no FG interference for ever from `q_(s*)`

- Variant `nj`. Sources: bp §7.1, §7.2 and §7.4, lines 520–522, 535–541 and
  605–606 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r150
  §2, lines 131–133 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Hypotheses: `env.r150`; `fg.baseSel.nj.v1`; `ap.S.v2`; `ap.Sslow.v1`;
  `fg.base.finalized.v1` (finalized arm); `fg.provenance.v2`;
  `ap.fastSupport.v1`; `comp.provenance.v1`; `fg.causalCap.core.v1`;
  `comp.cut.v1`. No service entry is used (r150 lines 135–136).
- Note (2026-09-28; §0 rule (a)): `fg.provenance.v1` was replaced by
  `fg.provenance.v2`, `ap.fastSupport.v1` and `comp.provenance.v1`;
  `fg.causalCap.v1` was replaced by `fg.causalCap.core.v1` and
  `comp.cut.v1`.
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 520–522:_
>
> Let 𝒫 be the set of all fast bodies at labels s ≥ s*, and all slow bodies
> at labels s whose windows lie in `[s*, ∞)`. For B∈𝒫 at label s put
> `q(B) = q_s`. The FG sources of all honest rows at rounds ≥ r* are in 𝒫.

> _fgsa-healing-blueprint.md, lines 535–541:_
>
> For a time t let IH(t) be the conjunction of:
>
> - (i) (N2)(𝒫;t′) for every t′<t;
> - (ii) in the NJ arm, no honest target row at height x is emitted before t.
>
> (i) is a statement about duties strictly before t. So IH(t) never uses a
> conclusion at t itself.

> _fgsa-healing-blueprint.md, lines 605–606:_
>
> **Theorem N.** For every t, IH(t) holds. In particular (N2)(𝒫;t) holds
> for every t.

> _fgsa-theorem-h.md, lines 131–133:_
>
> **Theorem N — PROVED.** Every B in 𝒫 is kept at every honest duty from
> its transfer time. In the NJ outcome no honest target at x is ever
> emitted. Therefore all three source conclusions above hold forever.

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table line 20). bp has
  PROVED* from (S) and (S_slow) (H7); r149 proves both.

### `comp.fgHealed.v1` — FG-healed from `q_(s*)`

- Variant `nj`. Sources: bp §7.1 and §7.7, lines 520–522, 684–693 and
  695–696 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r150
  §2, lines 116–118 and 154–155 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Protected set (audit W05): 𝒫 = ALL fast bodies at labels ≥ s* and ALL slow
  bodies whose window lies in `[s*,∞)` (bp §7.1). It is not restricted to
  row sources.
- Hypotheses: `comp.theoremN.v1`; `ap.S.v2` (fast bodies, PROVED, r149);
  `ap.Sslow.v1` (slow bodies, PROVED, r149).
- Statement (pinned):

> _fgsa-healing-blueprint.md, lines 520–522:_
>
> Let 𝒫 be the set of all fast bodies at labels s ≥ s*, and all slow bodies
> at labels s whose windows lie in `[s*, ∞)`. For B∈𝒫 at label s put
> `q(B) = q_s`. The FG sources of all honest rows at rounds ≥ r* are in 𝒫.

> _fgsa-healing-blueprint.md, lines 684–693:_
>
> **Definition.** The run is *FG-healed from q_(s*)* iff (N2)(𝒫;t) holds
> for every t, and every B∈𝒫 at label s is in every honest HEAD from q_s
> and in every honest S from `t_s+10Δ`. The run is *healed from t_h* iff it
> is FG-healed and, for every t ≥ t_h:
>
> - (A) all honest S values at t lie on one chain;
> - (B) every honest S at a time t′ ≥ t extends its value at t (monotone,
>   no reorganization), and `F ⪯ S`, so `available = S`;
> - (C) every honest proposal at a slot u with t_u ≥ t_h is in every honest
>   S by `t_u+6Δ`.

> _fgsa-healing-blueprint.md, lines 695–696:_
>
> **Theorem H-FG — PROVED from (S), (S_slow).** The run is FG-healed from
> `q_(s*)`. This is Theorem N with N-a.

> _fgsa-theorem-h.md, lines 154–155:_
>
> Consequently the run is FG-healed from q_s*. This proves preservation
> of the protected bodies; full healing of arbitrary S tips needs §4.

- Status: 2026-09-28 — PROVED (FG-SA; r150 §2). bp has PROVED* (H10).
- Note: the row-source form `ap.S.v1` does not give this protected set. bp
  H17 ("H-FG composes with r147's (S)") concerns a row-source reading; this
  entry does not cite it (audit W05).

### `comp.healed.v1` — full healing (Theorem H) and the proved bound

- Variant `nj`. Source r150 §3.4, §4.5 and §6.4, lines 248–251, 374–392 and
  546–569. File `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`.
- Hypotheses: `env.r150`; `fg.baseSel.nj.v1`; `comp.theoremN.v1`;
  `comp.fgHealed.v1`; `ap.S.v2`; `ap.Sslow.v1`; `ap.Xplus.v1`; for the
  global clause also the literal-N1 arrival count (`comp.rise.fixedF.v1`,
  `fg.oneBullet.core.v1`, `comp.settle.v1`, the r147 §6 counts; r150 §6.1,
  bp §9.4) and `comp.arrivalNJ.v1`. It does not use `ap.X.v1`,
  `ap.repair.movingF.v1` or `comp.rise.movingF.v1`.
- Note (2026-09-28; §0 rule (a)): `fg.oneBullet.v1` was replaced by
  `fg.oneBullet.core.v1` and `comp.settle.v1`.
- Clauses: (local) Theorem H, r150 §4.5, lines 374–392: the run is healed
  from `t_h ≤ q_(s*)+2L+G−Δ`; it needs none of the arrival inputs.
  (global) r150 §6.4, lines 546–569: `t_h < GST+B_proved`. The global
  clause does not cite `comp.healedLit.v1` or `comp.healedUnif.v1`; those
  entries cite only the local clause, so there is no cycle.
- (X+) discharge (audit W03): at each call of `ap.Xplus.v1`, that is, at
  every honest proposal with slot `u ≥ ℓ+1`, `ℓ = s*+2k−1`, this entry
  proves x0 (r150 §3.2, lines 187–202: every proposal-time lease is in 𝒫 and
  on the ordinary walk), x1 (lines 204–206), x2 and x3 (r150 §3.3, lines
  208–240: T = C* if `m_u = x+1`, else the source body of an honest row in
  the last crossing of a maximizing carrier).
- Statement (pinned):

> _fgsa-theorem-h.md, lines 248–251:_
>
> **Service after the boundary — PROVED.** At every honest proposal
> with `u≥ℓ+1`, x0, x1, x2, and x3 hold. The delivery and declared-view
> premises hold by §1. Hence r149's (X+) gives exact P HEADs at v_u
> and `P⪯S_i(d_u)` at every honest reader.

> _fgsa-theorem-h.md, lines 374–392:_
>
> **Theorem H — PROVED.** Under §1 and the actual reset of §1, the run
> is FG-healed from q_s*. There is a repair gate `t_h=d_u` such that,
> for all times from t_h onward, all honest S values lie on one chain,
> each honest S is monotone, every accepted honest F is a prefix of
> every honest S, and every honest proposal emitted from t_h onward
> is in every honest S within 6Δ.
>
> The bound is
>
> ```text
> t_h ≤ t_(s*) + 2L+G+4Δ
>     = q_(s*) + 2L+G−Δ
>     = a_(r*) + 2L+G−2Δ.
> ```
>
> Proof: choose `t_ℓ<t_u≤t_ℓ+G`, use §3.4 at d_u, and apply §§4.1–4.4.
> Then `d_u≤t_ℓ+G+6Δ=t_(s*)+2L+G+4Δ`. The strict proposal choice
> costs no additional G or Δ: its next grid point already exceeds
> E_old. All conclusions also hold from the displayed upper bound. ∎

> _fgsa-theorem-h.md, lines 546–569:_
>
> Under exactly the reachable-execution, count, delivery, recurrence,
> row-inclusion, and horizon premises in §1, and using r146's proved
> arrival result as supplied, define
>
> ```text
> B_proved = min(B_lit, B_NJ,H)
>          = min(3P+[2N+H+2−f_0](ρ+2σ+4Δ), P[3+Nβ])
>            + 2L+G−2Δ.
> ```
>
> There exists `t_h<GST+B_proved` from which all honest S values lie
> on one chain, every honest S is monotone, every honest proposal has
> 6Δ inclusion at all honest readers, and every accepted honest F is
> a prefix of every honest S. Hence `available=S` throughout this
> suffix. The construction allows either the NJ or the named finalized
> outcome of the DC consumer. The uniform proved choice is B_NJ,H;
> the supplied B_base is also valid and is larger by `P+10Δ`.
>
> At the actual reset the local bound, independent of the chosen
> arrival proof, is
>
> ```text
> t_h ≤ q_(s*) + 2L+G−Δ.
> ```

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table lines 21–23).
- Bounds: local `t_h ≤ q_(s*)+2L+G−Δ`. Global
  `GST + min{B_lit, B_NJ + 2L+G−2Δ}`. Example
  (`Δ=1, R=3, k=2, G=8, g=3, D=2, K=5`): `B_NJ,H = 5816Δ`; `B_lit = 7472Δ`
  for `M=1, H=10, f_0=0`; the minimum is 5816Δ (r150 §6.3, lines 528–541).

### `comp.healedLit.v1` — fixed-F (literal N1) arrival and bound

- Variant `nj`. Sources: r150 §6.1, lines 464–481 (file `fgsa-theorem-h.md`,
  sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`); bp
  §9.4, lines 1028–1047 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Hypotheses: `comp.rise.fixedF.v1`; `fg.oneBullet.core.v1`;
  `comp.settle.v1`; the r147 §6 counts; the local Theorem H clause of
  `comp.healed.v1` (r150 §4.5). N = D+K+5, W = λ+4Δ, λ = ρ+2σ.
- Note (2026-09-28; §0 rule (a)): `fg.oneBullet.v1` was replaced by
  `fg.oneBullet.core.v1` and `comp.settle.v1`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 464–481:_
>
> r147's supplied literal-N1 theorem has `λ=ρ+2σ`. At each frontier
> there is at most one top-J event. Count lower F advances separately.
> Use the blueprint §9.4 count, with f_0 the least honest finalized
> height at u_0. Before reaching H+3 their total count is at most
> `H+2−f_0`. Settling costs θ=4Δ for each counted event.
>
> The arrival deadline and Theorem H give the **PROVED** bound
>
> ```text
> B_lit = 3P + [2N + H+2−f_0]W + δ_H;
> t_h < GST+B_lit.
>
> B_lit ≤ 3P + [3N+M]W + δ_H.
> ```
>
> This proof uses literal (L), the counted interruptions, Theorem N,
> and §§3–4. It has no use of original (X) or effective (L). Thus the
> old service qualification on this composition is removed.

> _fgsa-healing-blueprint.md, lines 1028–1047:_
>
> r147's N1 fixes F, Z, and H_d. Every F advance then interrupts the
> static interval, and r147 §6 charges a full `W = 3Δ+B_static` after
> each counted event. Put `λ = λ_147` and use θ=4Δ ≥ 3Δ. At frontier m
> the number of interruptions is at most `1 + n_F(m)`, where n_F(m) counts
> new finalized heights that first appear at frontier m. The case split
> of Theorem HP then gives at most `(2+n_F(m))(λ+θ)` per level. The
> accepted F only increases, and it stays ≤ H+1 before the frontier
> reaches H+3. Thus `Σ_m n_F(m) ≤ H+2−f_0`, with f_0 the least honest h_F
> at u_0, and
>
> ```text
> T_arr  ≤ u_0 + [2(D+K+5) + (H+2−f_0)](λ+θ)
>        ≤ u_0 + [3(D+K+5) + M](λ+θ);
> t_heal < GST + 3P + [3(D+K+5) + M](λ+θ) + 2L + G − 2Δ.
> ```
>
> This bound depends on the initial frontier M, which the pre-GST adversary
> controls. r147's per-level count `N ≤ m−1−f0+ε_J` is the same bound
> before summation. The trunk lemma of §4.1 removes the M term, provided
> that (L) holds under the effective filter (H16, §10).

- Status: 2026-09-28 — PROVED (FG-SA; r150 claim table line 26). bp has
  PROVED* (H14).
- Correction (audit W07): the extra term over the uniform `2N(λ+θ)` is
  `(H+2−f_0)(λ+θ)`, conservatively `(3N+M)(λ+θ)` in total, not `M(λ+θ)`.
  Example (`Δ=1, R=3, k=2, G=8, g=3, D=2, K=5`): 7472Δ for
  `M=1, H=10, f_0=0`; 8502Δ for `M=10, H=15, f_0=0` (bp §9.2 table; r150
  lines 540–541). The conservative form gives 7678Δ for `M=1`. The v1
  reading `2N(λ+θ) + M(λ+θ)` gives 5206Δ and is wrong.

### `comp.arrivalNJ.v1` — supplied arrival bound `B_NJ`

- Variant `nj`. Source r146 §5.1, lines 551–581. File `fgsa-adjudicate.md`,
  sha256 `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 551–581:_
>
> One attempt costs at most
>
> ```text
> P + ρ + P + (3g+6)P ≤ [ceil_div(ρ,P)+3g+8]P.
> ```
>
> A top-J event can interrupt once. Two complete attempts suffice. Set
>
> ```text
> β = 2*ceil_div(ρ,P)+6g+16.
> ```
>
> Take the actual inclusive causal cut at `a_(r_G+2)`, where r_G is the
> first action round at or after GST. Let M be its honest archival maximum.
> Set `H=K*ceil_div(M+D+3,K)`. Then `H+3≤M+D+K+5`.
> Each pre-cut row has height at most M; an old-only crossing can add at
> most one. The unchanged exact-entry/finality consumer in
> `HeightRegimeNamedBaseDeadline` chooses the actual first crossing and
> its actual finality cap. It yields either the uniformly NJ prefix at H
> or a named finalized checkpoint of height `M<x≤H+1`.
>
> With β as the replacement producer, a sufficient arrival budget is
>
> ```text
> B_NJ = P*[3+(D+K+5)*β].
> ```
>
> This is an environment-only paper bound. Source absence cannot deadlock
> it: either the frontier rises, or a long enough retained interval lets
> the base produce the required fast sources. No global base handoff is
> assumed before the NJ search.

- Status: 2026-09-28 — PROVED (FG-SA; r146 claim 3b). Example: 5796Δ. r150
  §6.2 (lines 497–501) uses it as the arrival bound of `a_(r*)`.

### `comp.handoffBase.v1` — supplied base handoff `B_base`

- Variant `nj`. Source r146 §5.3, lines 648–657. File `fgsa-adjudicate.md`,
  sha256 `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 648–657:_
>
> Paying ρ from this start removes arbitrary older descendant leases.
> An honest repair proposal has a slot later than all old S tips; it
> therefore replaces them, rather than retaining an old strict extension.
> The exact proposal and guard comparison of §3.2 then continues. This
> proves the full safe, monotone available suffix, not only its common
> ancestor. A sufficient handoff bound is
>
> ```text
> B_base = B_NJ+P+ρ.
> ```

- Status: 2026-09-28 — PROVED (FG-SA; r146 claim 3e). Example: 5838Δ.
  `comp.healed.v1` gives the smaller `B_NJ,H = B_base − P − 10Δ` (r150
  §6.2).

### `comp.healedUnif.v1` — uniform bound under effective N1

- Variant `nj`. Sources: r150 §6.3, lines 516–526 (file `fgsa-theorem-h.md`,
  sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`); bp
  §9.1, lines 958–967 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Hypotheses: `comp.rise.movingF.v1` (effective (L), OPEN),
  `fg.oneBullet.core.v1`, `comp.settle.v1` and `fg.trunk.v1` (bp Theorem
  HP and Theorem A, PROVED from (L)); the local Theorem H clause of
  `comp.healed.v1` (r150 §4.5). N = D+K+5, θ = 4Δ.
- Note (2026-09-28; §0 rule (a)): `fg.oneBullet.v1` was replaced by
  `fg.oneBullet.core.v1` and `comp.settle.v1`.
- Statement (pinned):

> _fgsa-theorem-h.md, lines 516–526:_
>
> If effective (L) holds with λ, the blueprint's fixed-height split
> costs `2(λ+4Δ)` per gain. N gains suffice. Theorem H then gives
>
> ```text
> B_eff(λ) = 3P + 2N(λ+4Δ) + δ_H;
> t_h < GST+B_eff(λ).
> ```
>
> The implication is **PROVED**. Its instantiation as a new bound from
> the execution premises alone, with `λ=ρ+2σ`, is **OPEN** because §5
> is open. Neither original (X) nor a lease-only argument closes it.

> _fgsa-healing-blueprint.md, lines 958–967:_
>
> ```text
> θ        = 4Δ
> Λ_lvl    = 2(λ+θ)
> T_arr    = u_0 + (D+K+5)·Λ_lvl                 frontier ≥ H+3
> a_(r*)   < T_arr
> t_heal   = a_(r*) + 2L + G − 2Δ
>
> t_heal   < GST + 3P + 2(D+K+5)(λ+4Δ) + 2L + G − 2Δ.
> FG-healed from q_(s*) < GST + 3P + 2(D+K+5)(λ+4Δ) − Δ.
> ```

- Status: 2026-09-28 — OPEN as a bound from the execution premises alone
  (r150 claim table line 29; r149 claim table line 37). The implication from
  `comp.rise.movingF.v1` is PROVED (r150 claim table line 28). Example with
  `λ = ρ+2σ`: 5000Δ, conditional (r150 lines 528–537).

### `comp.healedAtQ.v1` — full healing already at `q_(s*)` (H12)

- Variant `nj`. Sources: bp claim table H12, line 62 (file
  `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`); r150
  §7, lines 576–579 (file `fgsa-theorem-h.md`, sha256
  `8211361a618814fa4d5f4b1a3c593943380c9ccb99235e8b9c413d633876adc3`).
- Statement (pinned):

> _fgsa-healing-blueprint.md, line 62:_
>
> ```text
> │ H12 │ Full healing already at q_s* (no base delay)         │ OPEN    │
> ```

> _fgsa-theorem-h.md, lines 576–579:_
>
> **H12 remains OPEN.** Theorem N proves FG healing at q_s*. Full
> healing of every S tip at that time does not follow. The raw-result
> induction in §4 needs the absence of conflicting unsupported leases
> above C*, which §3.1 establishes later.

- Status: 2026-09-28 — OPEN (r149 §7; r150 §7). The n=7 count stanza is not
  an execution at the actual reset (r149 lines 729–737).

### `comp.finality.v1` — first finality

- Variant `nj`. Sources: r146 §5.4, lines 676–711 (file
  `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`); bp
  §9.5, lines 1051–1054 (file `fgsa-healing-blueprint.md`, sha256
  `4d643d7a6285705ef8bcef6b408b46a45d64641f0d92828b3539f8f938074318`).
- Statement (pinned):

> _fgsa-adjudicate.md, lines 676–711:_
>
> 1. At the selected honest opening-plus-two-slots window, the separate
>    **current-slot finality head** is the slot-1 proposal, with the
>    required latest justification and permitted finality record.
> 2. Select a usable non-NJ height above the relevant frontier and, for
>    proposal inclusion, above the specified later proposal. Prove the
>    height-rate and NJ-spacing argument despite arbitrary non-opening
>    consumption and delayed old carriers.
> 3. Apply the precise strong recurrence and inclusion window to the
>    chosen target, justification, and finality carriers. Prove that
>    the matching rows remain included or already stored on the parent.
>
> The exact opening source after B_base follows from base service and
> the fast count. Named entry agreement follows from §4. These facts
> remove two parts of I, but they are not the current-slot head equality
> or the complete finality deadline construction.
>
> Opus's `(g+2)P+9Δ` is a proposed deadline from the reset for **some new
> finalization**. Astra's expression includes a **specified honest
> opening selected after base handoff**. These are different guarantees.
> Moreover, first finality need not be at H+1: recovery can leave that
> height before the required proposer window. DC's finality kernel also
> selects a justifiable height above a frontier, not necessarily H+1.
>
> Retain the following conditional arithmetic, with I denoting the three
> remaining timed obligations as well as the proved source clauses:
>
> ```text
> J_I     = (3g+6)P+9Δ
> B_first = B_base+(g+1)P+J_I
>         = B_NJ+ρ+(4g+8)P+9Δ.
> ```
>
> The arithmetic and the quorum/finality transition are PROVED given I.
> The environment-only first-finality claim remains SKETCH. Neither
> Opus's shorter expression nor the larger B_first is an unconditional
> proved finality deadline in this adjudication.

> _fgsa-healing-blueprint.md, lines 1051–1054:_
>
> This file claims no first-finality deadline. After t_heal, Theorem H gives
> exact opening service and one named entry per height. The finality-head
> cone, the choice of a non-NJ height, and the strong recurrence remain the
> three timed obligations of [fgsa-adjudicate §5.4](fgsa-adjudicate.md).

- Status: 2026-09-28 — SKETCH (r146 claim 3g). The arithmetic and the
  quorum/finality transition are PROVED given I. The three timed obligations
  are: the current-slot finality head (`ap.finalityHead.v2`) with its record
  permission (a Simplex client fact), a usable non-NJ height, and the timed
  target, justification and finality carriers under
  StrongMultiProposerRecurrence.

### `comp.clean.v1` — AP claims carry over in clean and Outage regimes

- Variant `nj`. Source r146 §3.2, lines 359–364 (claims 1a–1c, claim table
  lines 26–28). File `fgsa-adjudicate.md`, sha256
  `0fe1717f6abbf0d708cada05a8a4d3e3431a530d3d5c3a65e86bf755f5642017`.
- Hypotheses: `ap.armedSafe.v1` specialized to the Simplex policy;
  ArmedRetained B for Outage.
- Statement (pinned):

> _fgsa-adjudicate.md, lines 359–364:_
>
> This induction uses `a<h`, not `a≤f` and not FG quorum turnout. It
> proves clean safety, monotonicity, and 6Δ service. F and S remain on
> the same chain. The accessor is their greater prefix and is monotone.
> The changed proof follows the origin/root/parent/HEAD/guard order in
> `CleanInclusion.lean`; it does not instantiate that theorem on a
> different executable `Run`.

- Status: 2026-09-28 — PROVED (FG-SA; r146 1a–1c).
- Note: it has the same source as `ap.armedSafe.v1`. `ap.armedSafe.v1` is
  the AP-side statement; this entry is its composite form.

## 6. Invariants used by the composition (V03)

Three separate invariants, each over execution prefixes:
- clean history (GST = 0 regimes);
- post-reset source history: from the reset boundary, each source body from
  its first transfer HEAD q_s (not all pre-reset sources: old justification
  disclosure is a counterexample, fgsa-fast.md);
- armed-prefix Outage history: B only, not every later body (two partition
  branches can both extend B).

`Harmless` is stated as compatibility with the body being protected, not as
provenance of one row of a new quorum.

## 7. Changes in v2 (2026-09-28)

- W08: every entry pins its statement and hypotheses, its variant, its
  source lines and the source SHA-256 (§0). Statuses are dated lines.
- W03: `ap.X.v1` is WITHDRAWN (REFUTED, r149 §5). `ap.Xplus.v1` is
  registered with x0 and x3. `comp.healed.v1` discharges x0–x3 at each call
  (r150 §3).
- W05: `comp.fgHealed.v1` covers all fast and slow protected bodies and
  cites `ap.S.v2` and `ap.Sslow.v1`.
- W07: the fixed-F bound is `comp.healedLit.v1` (r150 §6.1, bp §9.4).
  `comp.healedUnif.v1` lists `comp.rise.movingF.v1` (effective (L)) as a
  hypothesis.
- W06: `fg.base.fj.v1` moved to `SimplexFG.fj` (§4), with its own interface
  (`fj.descent.v1`, `fj.canonical.v1`, `fj.inBandLock.v1`,
  `fj.twoChanges.v1`). HNI and its lemmas are `nj` only.
- W09: `fg.baseSel.nj.v1` lists the returned witness. Run-wide HNI in the NJ
  arm is derived in `comp.theoremN.v1`.
- New ids: `fg.frame.v1`, `fg.N2.v2`, `ap.reach.v1`, `fg.causalCap.v1`,
  `fg.baseSel.nj.v1`, `fj.frame.v1`, `fj.descent.v1`, `fj.canonical.v1`,
  `fj.inBandLock.v1`, `fj.twoChanges.v1`, `fj.armedSafe.v1`,
  `fj.firstFinality.v1`, `comp.healedLit.v1`, `comp.arrivalNJ.v1`,
  `comp.handoffBase.v1`.
- W02: `ap.*` entries state only AP service facts. WITHDRAWN as misfiled
  (statuses unchanged): `ap.L.fixedF.v1` (PROVED) and `ap.L.movingF.v1`
  (OPEN), refiled as `comp.rise.fixedF.v1` and `comp.rise.movingF.v1`,
  with service parts `ap.repair.fixedF.v1`, `ap.repair.movingF.v1`
  (OPEN), `ap.source.v1` and `ap.carrierKeep.v2` (block retention);
  `ap.carrierKeep.v1` (FG entries, maturity, rise); `ap.honestSourced.v1`
  (client and plateau-entry facts; now `ap.honestSourced.v2`);
  `ap.finalityHead.v1` (record permission; now `ap.finalityHead.v2`);
  `ap.outputRecovered.v1` (depends on `comp.theoremN.v1`; covered by the
  local clause of `comp.healed.v1`). `comp.healedLit.v1` and
  `comp.healedUnif.v1` cite that local clause; the global clause of
  `comp.healed.v1` no longer cites `comp.healedLit.v1`.
- New ids for W02: `ap.repair.fixedF.v1`, `ap.repair.movingF.v1`,
  `ap.source.v1`, `ap.carrierKeep.v2`, `ap.honestSourced.v2`,
  `ap.finalityHead.v2`, `comp.rise.fixedF.v1`, `comp.rise.movingF.v1`.
- r151 (`fj-theorem-h.md`) registered: `env.r151`, `fj.reset.v1`,
  `fj.theoremN.v1`, `fj.rise.fixedF.v1`, `fj.rise.movingF.v1`,
  `fj.Xplus.v1`, `fj.healed.v1`, `fj.healedUnif.v1`, `fj.healedAtQ.v1`.
  r151 confirms F13 REFUTED. It does not address the Opus `B_reset`
  shortcut (r146 claim 3c stays SKETCH).
- Status changes from v1: `comp.theoremN.v1`, `comp.fgHealed.v1` and
  `fg.base.nj.v1` go from PROVED* to PROVED, because r149 proves (S) and
  (S_slow) and r150 §2 states Theorem N as PROVED.

## 8. Changes after v2: f1 registry splits (2026-09-28)

Agreed with the framework session ethereum-f1. The splits separate pure
FG facts (`fg.*`, `fj.*`) from run facts (`comp.*`) and SA facts (`ap.*`),
as audit W02 requires. No status of an existing claim changes: each
SUPERSEDED entry is the conjunction of its successors.

- §0: new status SUPERSEDED; two hypotheses-list edits keep an id (rules
  (a) and (b)). §0.1 registers `slow-arming.md` and the sources outside
  `tsc/`. §0.3 is a glossary of the two F-number systems (r148 and the
  blueprint F-table).
- `fg.frame.v1` → SUPERSEDED by `fg.frame.v2` (J selected with
  `F_d ⪯ J_d`, as in DC and spec `update_finality` and spec `fg_frame`).
  New lemma `fg.frameCompat.v1` (registry argument): the two rules select
  the same pair at every honest duty view, without `a≤f`. Spec line 357
  says "compatible"; its code tests `F ⪯ J`.
- `fg.provenance.v1` → SUPERSEDED by `fg.provenance.v2` (pure FG),
  `ap.fastSupport.v1` (a fast write has ≥ τ surviving supporters, so an
  honest one) and `comp.provenance.v1` (the source is the signer's
  `C_fg`).
- `fg.causalCap.v1` → SUPERSEDED by `fg.causalCap.core.v1` (the cap for
  any M; row bound LEAN in DC `WeakHeightBounds.lean:42`) and `comp.cut.v1`
  (r_G, `u_0 = a_(r_G+2)`, M at `u_0`).
- `fg.oneBullet.v1` → SUPERSEDED by `fg.oneBullet.core.v1` (items 2–4 of
  bp §4.2) and `comp.settle.v1` (item 1, settling within θ = 4Δ).
- `fj.twoChanges.v1` → SUPERSEDED by `fj.twoChanges.core.v1` (the phase
  count) and `comp.settle.v1` (settling within θ, or P in r148).
- New ids for the blueprint facts: `fg.uniqueJust.v1` (F3; DC Lemma U,
  `Engine.lean:243` `justification_unique_per_height`) and
  `fg.finalLock.v1` (F4; `FinalityComparison.lean:50`
  `finalized_preceq_of_height_lt`; r148's "finalized-crossing law", line
  226). Both are LEAN for DC only.
- New id `fj.crossingNoFinal.v1` (r148 F2, PROVED, lines 234–258).
  `fj.frame.v1` has a note: its contest test is the local witness of r148
  lines 260–270.
- Hypotheses lists that cited a SUPERSEDED id now cite its successors:
  `comp.rise.fixedF.v1`, `comp.theoremN.v1`, `comp.healed.v1`,
  `comp.healedLit.v1`, `comp.healedUnif.v1`, `fg.base.fj.v1`,
  `fj.reset.v1`, `fj.theoremN.v1`, `fj.rise.fixedF.v1`,
  `fj.rise.movingF.v1`. Lists that used F3 or F4 by number now name
  `fg.uniqueJust.v1` or `fg.finalLock.v1`: `fg.trunk.v1`,
  `fg.base.finalized.v1`, `fg.base.nj.v1`, `fg.baseSel.nj.v1`,
  `fj.inBandLock.v1` (note), `fj.reset.v1`.
- New ids: `fg.frame.v2`, `fg.frameCompat.v1`, `ap.fastSupport.v1`,
  `fg.provenance.v2`, `fg.causalCap.core.v1`, `fg.uniqueJust.v1`,
  `fg.finalLock.v1`, `fg.oneBullet.core.v1`, `fj.crossingNoFinal.v1`,
  `fj.twoChanges.core.v1`, `comp.provenance.v1`, `comp.settle.v1`,
  `comp.cut.v1`.
- SUPERSEDED: `fg.frame.v1`, `fg.provenance.v1`, `fg.causalCap.v1`,
  `fg.oneBullet.v1`, `fj.twoChanges.v1`.
- Lean scope (user decision 2026-09-28, relayed by ethereum-f1): the Lean
  FG module is DC-fj (DC's FG without SG and grades, with the FJ root rule
  in place of NJ; FRAMEWORK-DESIGN.md §7.1). NJ is not formalized now. The
  index has a new column "Lean plan". Each entry of the DC-fj plan has the
  line "Lean plan: DC-fj module": `fj.frame.v1`, `fg.accountable.v1`,
  `fj.inBandLock.v1`, `fg.uniqueJust.v1`, `fg.finalLock.v1`,
  `fg.provenance.v2`, `fg.causalCap.core.v1`, `fj.crossingNoFinal.v1`,
  `fj.twoChanges.core.v1`. The nj-only entries have the line "Lean plan:
  none (nj research entry)" and are not planned for Lean now: `fg.frame.v1`,
  `fg.frame.v2`, `fg.Ret.v1`, `fg.N1.v1`, `fg.N1eff.v1`, `fg.N2.v1`,
  `fg.N2.v2`, `fg.HNI.v1`, `fg.trunk.v1`, `fg.oneBullet.v1`,
  `fg.oneBullet.core.v1`, `fg.H19.v1`, `fg.HNIb.v1`,
  `fg.base.finalized.v1`, `fg.base.nj.v1`, `fg.baseSel.nj.v1`. They stay
  as research entries. `fg.frameCompat.v1` is not needed by the DC-fj
  module. `fg.frame.v2` points to its fj counterpart `fj.frame.v1`.
- Open item (2026-09-28): `ap.S.v2`, `ap.Sslow.v1` and `comp.theoremN.v1`
  use `fg.N2.v2` (NJ frame). An fj Kept/N2 form with lo is a new fj entry,
  needed for Kit.Compose. OPEN.
