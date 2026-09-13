# Erdős #593: obligatory 3-uniform hypergraphs

A finite 3-uniform hypergraph is **obligatory** if it appears in every
3-uniform hypergraph whose chromatic cardinal exceeds `aleph_0`.
The research question is to characterize this class.

This repository gives Jared Wilder's finite witnesses, formal definitions,
class-separation arguments and literature-dependent reductions a focused home.

## Start here

| File | Purpose |
|---|---|
| [Frontier](research/Erdos593Frontier.lean) | Obligatory, linear, three-partite and two-colorable predicates; finite witnesses and conditional refutations |
| [Forest](research/Erdos593Forest.lean) | Loose-forest definition, cycle witnesses and conditional frontier statements |
| [Audit](research/Erdos593Audit.lean) | Declaration dependency checks |
| [Campaign receipt](research/receipts/campaign.json) | Statement, evidence boundaries, literature and open obligations |
| [Receipts and snapshots](research/receipts/) | Historical build logs, audit and dated literature material |

## Formal scope

Unconditional results include the stated finite witness properties, the
single-edge obligatory lemma, and structural forest lemmas under their
displayed hypotheses.

The refutations of an equivalence between obligatory and two-colorable
hypergraphs use explicitly named literature hypotheses (`hEGH`, `hKo`,
`hEHR`). The forest frontier also uses a hypothesis `hRe`. These assumptions
remain visible in the Lean theorem statements: the package is not a formal
proof of the literature inputs themselves or a complete characterization.

The campaign records 30 audited declarations. This promotion preserves the
historical logs and sources; no fresh Lean compilation was performed.
The literature snapshots describe the source campaign's dated record.

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
Git blobs, byte counts and SHA-256 hashes. This is the preferred problem-level
entry; the archive remains provenance.

Author: Jared Wilder. Source campaign: 2026-09-05. Focused release: 2026-09-13.
License: Apache-2.0, inherited from the public source.
