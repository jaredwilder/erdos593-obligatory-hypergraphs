/-
Erdős Problem 593 — the LOWER edge of the frontier.

  https://www.erdosproblems.com/593   ($500, OPEN)

`Erdos593Frontier.lean` pinned the two upper containments of

    loose forests  ⊆  OBLIGATORY  ⊆  linear ∧ 3-partite  ⊊  2-colourable

and proved the outermost one strict (witness `K₄⁽³⁾`) and the middle one strict (witness
`C₃⁽³⁾`, given [EGH75]). This file closes the picture by proving the FIRST containment strict
as well, with witness `C₄⁽³⁾ = K_{2,2}⁽³⁾`:

  * [Ko01] Komjáth: every finite LOOSE FOREST is obligatory. (Reiher §1.)
    Before [Re24] this was, in Reiher's own words, all that was known — "it has never been shown
    that for any k ≥ 3 there exists an obligatory, k-uniform hypergraph which fails to be a
    forest."
  * [Re24] Reiher, Theorem 1.2: `K_{n,n}⁽ᵏ⁾` is obligatory. At k = 3, n = 2 this is `C₄⁽³⁾`.
  * PROVED HERE, unconditionally: `C₄⁽³⁾` is NOT a loose forest, and it IS linear and 3-partite.

Hence, given Reiher's theorem, the obligatory class strictly contains the loose forests, and it
strictly sits inside `linear ∧ 3-partite`, and the whole of Erdős 593 lives in the gap between
those two lines.

Compute receipt: compiled by `lean` against Mathlib 919544d4309104b3f19724b0e6e48c701d27948f,
toolchain leanprover/lean4:v4.31.0-rc1, on root@51.158.234.15.
-/

import Erdos593Frontier

open Cardinal Set

namespace Erdos593

/-! ############################################################################
    SECTION 1 — loose forests.
    ############################################################################ -/

/-- **Loose forest** ([Ko01], in the phrasing of Reiher §1): the hyperedges admit an
enumeration `e₀, …, e_{n-1}` such that `|eᵢ ∩ ⋃_{j<i} eⱼ| ≤ 1` for every `i`.

This definition is at least as PERMISSIVE as the literature's (any list whose element set is
`F.edges` may be offered, duplicates included), so a proof of `¬ IsLooseForest F` here is at
least as strong as a proof that `F` is not a loose forest in the literature's sense. -/
def IsLooseForest {V : Type} [DecidableEq V] (F : ThreeUniformHypergraph V) : Prop :=
  ∃ L : List (Finset V),
    (∀ e, e ∈ F.edges ↔ e ∈ L) ∧
    ∀ (pre : List (Finset V)) (e : Finset V) (post : List (Finset V)),
      L = pre ++ e :: post → (e ∩ pre.foldr (· ∪ ·) ∅).card ≤ 1

theorem subset_foldr_union {V : Type} [DecidableEq V] {f : Finset V} :
    ∀ L : List (Finset V), f ∈ L → f ⊆ L.foldr (· ∪ ·) ∅ := by
  intro L
  induction L with
  | nil => simp
  | cons a t ih =>
    intro hf
    rcases List.mem_cons.mp hf with rfl | hf'
    · simp
    · exact fun x hx => by
        simp only [List.foldr_cons, Finset.mem_union]
        exact Or.inr (ih hf' hx)

/-- **The peeling obstruction.** If EVERY hyperedge of `F` contains two distinct vertices that
each also lie in some *other* hyperedge, then `F` is not a loose forest.

The proof is the whole content of the loose-forest definition: whichever enumeration is offered,
its LAST edge must meet the union of all the earlier ones — that is, of all the others — in at
most one vertex, and the hypothesis says no edge does. -/
theorem not_looseForest_of_all_heavy {V : Type} [DecidableEq V] {F : ThreeUniformHypergraph V}
    (hne : F.edges.Nonempty)
    (hheavy : ∀ e ∈ F.edges, ∃ x ∈ e, ∃ y ∈ e, x ≠ y ∧
        (∃ f ∈ F.edges, f ≠ e ∧ x ∈ f) ∧ (∃ g ∈ F.edges, g ≠ e ∧ y ∈ g)) :
    ¬ IsLooseForest F := by
  rintro ⟨L, hL, hstep⟩
  -- `L` is nonempty.
  have hLne : L ≠ [] := by
    obtain ⟨e0, he0⟩ := hne
    intro hnil
    have hmem := (hL e0).mp he0
    rw [hnil] at hmem
    simp at hmem
  -- Split off the last entry.
  obtain ⟨pre, last, hLeq⟩ : ∃ pre last, L = pre ++ [last] := by
    rcases List.eq_nil_or_concat L with h | ⟨p, b, hb⟩
    · exact absurd h hLne
    · exact ⟨p, b, by rw [hb, List.concat_eq_append]⟩
  have hcardle : (last ∩ pre.foldr (· ∪ ·) ∅).card ≤ 1 := hstep pre last [] (by rw [hLeq])
  have hlast : last ∈ F.edges := (hL last).mpr (by rw [hLeq]; simp)
  obtain ⟨x, hxlast, y, hylast, hxy, ⟨f, hf, hfne, hxf⟩, ⟨g, hg, hgne, hyg⟩⟩ := hheavy last hlast
  -- Every edge other than `last` sits in `pre`, hence inside the folded union.
  have hpre : ∀ c, c ∈ F.edges → c ≠ last → c ∈ pre := by
    intro c hc hcne
    have hcL : c ∈ L := (hL c).mp hc
    rw [hLeq] at hcL
    rcases List.mem_append.mp hcL with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h) hcne
  have hxin : x ∈ pre.foldr (· ∪ ·) ∅ := subset_foldr_union pre (hpre f hf hfne) hxf
  have hyin : y ∈ pre.foldr (· ∪ ·) ∅ := subset_foldr_union pre (hpre g hg hgne) hyg
  have h2 : 1 < (last ∩ pre.foldr (· ∪ ·) ∅).card :=
    Finset.one_lt_card.mpr
      ⟨x, Finset.mem_inter.mpr ⟨hxlast, hxin⟩, y, Finset.mem_inter.mpr ⟨hylast, hyin⟩, hxy⟩
  omega

/-! ############################################################################
    SECTION 2 — the witness `C₄⁽³⁾ = K_{2,2}⁽³⁾`.
    ############################################################################ -/

/-- The 3-partition of `C₄⁽³⁾`: the two sides of the 4-cycle get colours `0` and `1`, every
expansion vertex gets colour `2`. -/
def p4 : Fin 8 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 2

/-- **`C₄⁽³⁾ = K_{2,2}⁽³⁾`** — the 3-uniform expansion of a 4-cycle: cycle vertices `0,1,2,3`
and one private new vertex `4,5,6,7` added to each cycle edge.

[Re24] Theorem 1.2 (at k = 3, n = 2): this hypergraph IS obligatory. -/
def C4exp : ThreeUniformHypergraph (Fin 8) where
  edges := {({0, 1, 4} : Finset (Fin 8)), {1, 2, 5}, {2, 3, 6}, {3, 0, 7}}
  uniform := by
    intro e he
    have he' : e = ({0, 1, 4} : Finset (Fin 8)) ∨ e = {1, 2, 5} ∨ e = {2, 3, 6} ∨ e = {3, 0, 7} :=
      he
    rcases he' with rfl | rfl | rfl | rfl <;> decide

theorem C4mem (e : Finset (Fin 8))
    (h : e = {0, 1, 4} ∨ e = {1, 2, 5} ∨ e = {2, 3, 6} ∨ e = {3, 0, 7}) : e ∈ C4exp.edges := h

theorem C4cases {e : Finset (Fin 8)} (he : e ∈ C4exp.edges) :
    e = {0, 1, 4} ∨ e = {1, 2, 5} ∨ e = {2, 3, 6} ∨ e = {3, 0, 7} := he

theorem C4exp_threePartite : IsThreePartite C4exp := by
  refine ⟨p4, ?_⟩
  intro e he
  rcases C4cases he with rfl | rfl | rfl | rfl <;> decide

theorem C4exp_linear : IsLinear C4exp := by
  intro e he f hf hne
  rcases C4cases he with rfl | rfl | rfl | rfl <;> rcases C4cases hf with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | decide

theorem C4exp_twoColorable : C4exp.IsTwoColorable :=
  twoColorable_of_threePartite C4exp_threePartite

/-- **`C₄⁽³⁾` is NOT a loose forest.** Every one of its four hyperedges contains two cycle
vertices, and each cycle vertex lies on a second hyperedge — so no enumeration can ever place a
"last" edge that touches the earlier ones only once. -/
theorem C4exp_not_looseForest : ¬ IsLooseForest C4exp := by
  refine not_looseForest_of_all_heavy ⟨{0, 1, 4}, C4mem _ (Or.inl rfl)⟩ ?_
  intro e he
  rcases C4cases he with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, 1, by decide, by decide,
      ⟨{3, 0, 7}, C4mem _ (Or.inr (Or.inr (Or.inr rfl))), by decide, by decide⟩,
      ⟨{1, 2, 5}, C4mem _ (Or.inr (Or.inl rfl)), by decide, by decide⟩⟩
  · exact ⟨1, by decide, 2, by decide, by decide,
      ⟨{0, 1, 4}, C4mem _ (Or.inl rfl), by decide, by decide⟩,
      ⟨{2, 3, 6}, C4mem _ (Or.inr (Or.inr (Or.inl rfl))), by decide, by decide⟩⟩
  · exact ⟨2, by decide, 3, by decide, by decide,
      ⟨{1, 2, 5}, C4mem _ (Or.inr (Or.inl rfl)), by decide, by decide⟩,
      ⟨{3, 0, 7}, C4mem _ (Or.inr (Or.inr (Or.inr rfl))), by decide, by decide⟩⟩
  · exact ⟨3, by decide, 0, by decide, by decide,
      ⟨{2, 3, 6}, C4mem _ (Or.inr (Or.inr (Or.inl rfl))), by decide, by decide⟩,
      ⟨{0, 1, 4}, C4mem _ (Or.inl rfl), by decide, by decide⟩⟩

/-! ############################################################################
    SECTION 3 — the frontier, both edges pinned.
    ############################################################################ -/

/-- **The lower containment is strict**, given [Re24] Theorem 1.2. -/
theorem lower_containment_strict (hRe : IsObligatory C4exp) :
    IsObligatory C4exp ∧ ¬ IsLooseForest C4exp :=
  ⟨hRe, C4exp_not_looseForest⟩

/-- **The whole frontier of Erdős 593, in one statement.**

Given the three literature verdicts — [Re24] `C₄⁽³⁾` obligatory, [EGH75] `C₃⁽³⁾` not
obligatory, [Ko01] obligatory ⟹ 3-partite, [EHR73] obligatory ⟹ linear — the chain

    loose forests  ⊊  OBLIGATORY  ⊊  linear ∧ 3-partite  ⊊  2-colourable

has all three containments STRICT, with the finite witnesses `C₄⁽³⁾`, `C₃⁽³⁾`, `K₄⁽³⁾`
respectively. Every property of every witness is proved by computation in this development; the
only imported facts are the four named hypotheses.

In particular the class the formal-conjectures file conjectures (Property B) is separated from
the obligatory class by TWO strict containments, not zero. -/
theorem frontier_pinned
    (hRe : IsObligatory C4exp)
    (hEGH : ¬ IsObligatory C3exp) :
    -- lower edge: an obligatory hypergraph that is not a loose forest
    (IsObligatory C4exp ∧ ¬ IsLooseForest C4exp ∧ IsLinear C4exp ∧ IsThreePartite C4exp) ∧
    -- upper edge: a linear, 3-partite hypergraph that is not obligatory
    (IsLinear C3exp ∧ IsThreePartite C3exp ∧ ¬ IsObligatory C3exp) ∧
    -- outer edge: a 2-colourable hypergraph failing both known necessary conditions
    (K4exp.IsTwoColorable ∧ ¬ IsThreePartite K4exp ∧ ¬ IsLinear K4exp) :=
  ⟨⟨hRe, C4exp_not_looseForest, C4exp_linear, C4exp_threePartite⟩,
   ⟨C3exp_linear, C3exp_threePartite, hEGH⟩,
   ⟨K4exp_twoColorable, K4exp_not_threePartite, K4exp_not_linear⟩⟩

end Erdos593
