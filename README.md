# Erdős #593: obligatory 3-uniform hypergraphs

A finite 3-uniform hypergraph is **obligatory** if it appears in every
3-uniform hypergraph whose chromatic cardinal exceeds `aleph_0`.
The research question is to characterize this class.

This repository gives Jared Wilder's finite witnesses, formal definitions,
class-separation arguments and literature-dependent reductions a focused home.

## Current external-status court — 2026-09-14

A later external development materially changes the publication context for this repository.

Eric Li's 2026 preprint **“A Resolution of Erdős Problems 593 and 1177: Obligatory Triple Systems and Exact Spectra”** (`arXiv:2606.24882`) claims a complete characterization of the obligatory finite triple systems. Its public Lean repository is `ericlisg/erdos-593-1177-lean`.

This claim has now passed the following independently inspectable gates:

- the repository contains a hypothesis-free joint certificate
  `Erdos593.full_resolution_unconditional`;
- the final #593 field states, for every finite triple system `F`,
  `FTS.Obligatory F ↔ Bclass F`, together with an intrinsic equivalent characterization;
- the project's GitHub Actions build completed successfully on the advertised main commit;
- the executable axiom audit reports exactly
  `[propext, Classical.choice, Quot.sound]` for the final #593 theorem and the joint certificate;
- the repository's statement-fidelity audit checks that its notions of 3-uniform host, proper coloring, uncountable chromaticity, embedding and obligatoriness match the live problem statement;
- its audit reports no proof-term `sorry`, `admit`, declared project axiom, `unsafe`, or `implemented_by` escape in the final development.

The claimed characterization is: after isolated vertices are removed, a finite triple system is obligatory iff it is linear, every hyperedge-node of its Levi graph has an incident bridge, and every Berge cycle is even; equivalently it lies in the constructive class generated from private-vertex expansions of finite bipartite graphs by the stated closure operations.

**Registry boundary:** `erdosproblems.com/593` still displayed the problem as OPEN when checked on 2026-09-14. Therefore this repository records the external result as a **strong formally verified claimed resolution awaiting registry/community incorporation**, rather than silently rewriting the historical campaign as though it had produced the solution.

This also means the dated September-5 campaign receipt below is historical state, not current external-literature state. Its own instruction was to adjudicate `arXiv:2606.24882`; that adjudication has now been performed at the public build/axiom/fidelity level.

## What this estate contributed before that adjudication

The source campaign did **not** claim to solve #593. It did, however, formally expose several useful pre-resolution facts:

- the Property-B / 2-colorability characterization suggested in the then-current Formal Conjectures file is false, conditional on named literature facts, with independent finite separation witnesses;
- `K_4^(3)` is 2-colorable but neither 3-partite nor linear;
- the dated literature frontier was pinned as
  `loose forests < obligatory < (linear and 3-partite) < 2-colorable`, with explicit witnesses at each strict separation under the named literature hypotheses;
- `C_3^(3)` shows that linearity plus 3-partiteness alone cannot characterize obligatoriness;
- a single hyperedge is proved obligatory unconditionally;
- reusable definitions and peeling lemmas were formalized against the upstream encoding.

These remain useful theorem/audit assets even if the external classification is ultimately accepted.

## Start here

| File | Purpose |
|---|---|
| [Frontier](research/Erdos593Frontier.lean) | Obligatory, linear, three-partite and two-colorable predicates; finite witnesses and conditional refutations |
| [Forest](research/Erdos593Forest.lean) | Loose-forest definition, cycle witnesses and conditional frontier statements |
| [Audit](research/Erdos593Audit.lean) | Declaration dependency checks |
| [Campaign receipt](research/receipts/campaign.json) | Historical statement, evidence boundaries, literature and open obligations as of 2026-09-05 |
| [Receipts and snapshots](research/receipts/) | Historical build logs, audit and dated literature material |

## Formal scope of this repository

Unconditional results include the stated finite witness properties, the
single-edge obligatory lemma, and structural forest lemmas under their
displayed hypotheses.

The refutations of an equivalence between obligatory and two-colorable
hypergraphs use explicitly named literature hypotheses (`hEGH`, `hKo`,
`hEHR`). The forest frontier also uses a hypothesis `hRe`. These assumptions
remain visible in the Lean theorem statements: **this repository itself** is
not the unconditional proof of the external classification.

The campaign records 30 audited declarations. This promotion preserves the
historical logs and sources; no fresh Lean compilation of this repository was
performed during the original promotion.

## Reproduce and trace

```sh
python verification/verify_source.py
```

This checks source integrity, not the mathematical claims. The original
environment is pinned in [campaign.json](research/receipts/campaign.json):
Lean `leanprover/lean4:v4.31.0-rc1`, Mathlib commit
`919544d4309104b3f19724b0e6e48c701d27948f`.
Compile Frontier, then Forest, then Audit with the generated modules on
`LEAN_PATH`; the [historical build helper](research/receipts/build.sh)
records the original environment paths.

All 11 research files are exact copies from the
[campaign archive](https://github.com/jaredwilder/erdos-campaign-archive/tree/main/campaigns/erdos593-close-2026-09-05).
[SOURCE-MANIFEST.json](SOURCE-MANIFEST.json) pins the source commit, paths,
Git blobs, byte counts and SHA-256 hashes. This is the preferred
problem-level entry; the archive remains provenance.

Author: Jared Wilder. Source campaign: 2026-09-05. Focused release: 2026-09-13.
License: Apache-2.0, inherited from the public source.
