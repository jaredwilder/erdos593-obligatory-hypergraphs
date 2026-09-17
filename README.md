# Erdős #593 — Obligatory 3-Uniform Hypergraphs

**Jared Wilder**

Formal definitions, finite witnesses, class separations, and literature-driven reductions for Erdős Problem #593.

A finite 3-uniform hypergraph is **obligatory** if it appears in every 3-uniform hypergraph of uncountable chromatic number. The problem asks for a characterization of the obligatory finite triple systems.

## Results in this repository

The formal development establishes or records:

- a single hyperedge is obligatory;
- `K_4^(3)` is 2-colorable but is neither 3-partite nor linear;
- `C_3^(3)` separates linear-plus-3-partite structure from obligatoriness;
- the simple Property-B / 2-colorability characterization is incompatible with the named literature inputs used in the campaign;
- reusable definitions and peeling lemmas for loose-forest structure;
- a dated frontier of strict class separations, with explicit finite witnesses.

The relevant literature hypotheses remain explicit in the Lean theorem statements rather than being hidden in prose.

## External 2026 result

Eric Li's 2026 preprint *A Resolution of Erdős Problems 593 and 1177: Obligatory Triple Systems and Exact Spectra* (arXiv:2606.24882) gives a claimed complete characterization and a public Lean development.

Its stated characterization is that, after isolated vertices are removed, a finite triple system is obligatory exactly when it is linear, every hyperedge-node of its Levi graph has an incident bridge, and every Berge cycle is even; the paper gives an equivalent constructive description as well.

This repository predates that classification and preserves Wilder's independent finite and formal work around the problem.

## Start here

| File | Purpose |
|---|---|
| [Frontier](research/Erdos593Frontier.lean) | Obligatory, linear, three-partite, and two-colorable predicates; witnesses and reductions |
| [Forest](research/Erdos593Forest.lean) | Loose-forest structure and cycle witnesses |
| [Audit](research/Erdos593Audit.lean) | Declaration dependency checks |
| [Campaign receipt](research/receipts/campaign.json) | Environment, literature inputs, and historical scope |
| [Receipts](research/receipts/) | Build logs and dated supporting material |

## Reproduce

The original environment is recorded in `research/receipts/campaign.json`:

- Lean `leanprover/lean4:v4.31.0-rc1`
- Mathlib commit `919544d4309104b3f19724b0e6e48c701d27948f`

Source integrity can be checked with:

```sh
python verification/verify_source.py
```

The research files are exact copies from the corresponding campaign archive; `SOURCE-MANIFEST.json` pins paths, Git blobs, byte counts, and SHA-256 hashes.

**License:** Apache-2.0