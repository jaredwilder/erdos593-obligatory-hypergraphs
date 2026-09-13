/-
Erdős Problem 593 — the obligatory frontier, formalised.

  https://www.erdosproblems.com/593   ($500, OPEN, set theory / graph theory / hypergraphs)

  "Characterize those finite 3-uniform hypergraphs which appear in every 3-uniform hypergraph
   of chromatic number > ℵ₀."

WHY THIS FILE EXISTS.

The canonical formalisation that erdosproblems.com/593 links to is
`google-deepmind/formal-conjectures : FormalConjectures/ErdosProblems/593.lean`.
That file records, in its own words, "A natural conjectural characterization ... that the
obligatory finite 3-uniform hypergraphs are exactly the 2-colorable ones (Property B)", and
splits it into three `answer(sorry)` slots:

  * `erdos_593.variants.obligatory_implies_two_colorable`  : obligatory → 2-colourable
  * `erdos_593.variants.two_colorable_implies_obligatory`  : 2-colourable → obligatory
  * `erdos_593`                                            : the conjunction, as an ↔

THE RECORDED CONJECTURE IS FALSE. Three independent published theorems each refute the
`two_colorable_implies_obligatory` slot, hence also the `erdos_593` ↔ slot. This file proves,
sorry-free and kernel-checked, the finite-combinatorial half of each refutation: it exhibits
explicit finite 3-uniform hypergraphs and establishes their 2-colourability, 3-partiteness and
linearity by computation, so that each literature theorem alone closes the argument.

LITERATURE (all attributions via Christian Reiher, "Obligatory hypergraphs",
arXiv:2403.11223v1 [math.CO], 17 Mar 2024, §1 — a published survey of exactly this frontier):

  [EH66]  Erdős–Hajnal, Acta Math. Acad. Sci. Hungar. 17 (1966) 61–99.
          A finite GRAPH is obligatory iff it is bipartite.  (Reiher, Theorem 1.1)
  [EHR73] Erdős–Hajnal–Rothschild.
          A hypergraph with two edges meeting in ≥ 2 vertices is NON-obligatory.
          Equivalently: obligatory ⟹ LINEAR.
  [EGH75] Erdős–Galvin–Hajnal, Colloq. Math. Soc. János Bolyai 10 (1975) 425–513, Thm 11.6.
          C₃⁽³⁾ (the 3-uniform expansion of a triangle) is NON-obligatory.
  [Ko01]  Komjáth, Combinatorica 21 (2001) 233–238 (as extended in Reiher §1).
          Every obligatory k-uniform hypergraph is k-PARTITE; the obligatory class is closed
          under disjoint unions and one-point amalgamations; every finite loose forest is
          obligatory.
  [Re24]  Reiher, Theorem 1.2.  K_{n,n}⁽ᵏ⁾ is obligatory for all k ≥ 2, n ≥ 1.
          Hence C₄⁽³⁾ = K_{2,2}⁽³⁾ is obligatory.

  Reiher §1, verbatim: "For general hypergraphs no comparable result is known, and no plausible
  conjecture has ever been proposed."  That sentence is itself evidence against the
  formal-conjectures file's framing of Property B as "a natural conjectural characterization".

NOTHING IN THIS FILE ASSERTS ANY OF THE LITERATURE VERDICTS. Every one of them is carried as an
explicitly named hypothesis at the point of use. What is proved outright here is the finite
combinatorics: the witnesses, their properties, and the logical consequences.

Compute receipt: compiled by `lean` against Mathlib 919544d4309104b3f19724b0e6e48c701d27948f,
toolchain leanprover/lean4:v4.31.0-rc1, on root@51.158.234.15.
-/

import Mathlib

open Cardinal Set

namespace Erdos593

/-! ############################################################################
    SECTION 1 — the google-deepmind/formal-conjectures encoding, inlined VERBATIM.

    Copied character-for-character (modulo the `module`/`public import` wrapper, which is a
    build-system artefact) from
      formal-conjectures/FormalConjecturesForMathlib/Combinatorics/Hypergraph/ThreeUniform.lean
    so that every theorem below is a statement about the SAME objects the canonical
    formalisation of Erdős 593 talks about, not about a paraphrase of them.
    ############################################################################ -/

/-- A **3-uniform hypergraph** on vertex type `V` is a set of 3-element `Finset`s. -/
structure ThreeUniformHypergraph (V : Type) where
  /-- The set of hyperedges: each edge is a 3-element finset of vertices. -/
  edges : Set (Finset V)
  /-- Every hyperedge has exactly 3 vertices. -/
  uniform : ∀ e ∈ edges, e.card = 3

namespace ThreeUniformHypergraph

/-- A **proper coloring**: no hyperedge is monochromatic. -/
def IsProperColoring {V : Type} (H : ThreeUniformHypergraph V) {C : Type} (f : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, f u ≠ f v

/-- The **chromatic cardinal**: the infimum of cardinalities of colour types admitting a
proper colouring. -/
noncomputable def chromaticCardinal {V : Type} (H : ThreeUniformHypergraph V) : Cardinal.{0} :=
  sInf {κ : Cardinal.{0} | ∃ (C : Type), #C = κ ∧ ∃ f : V → C, H.IsProperColoring f}

/-- `F` **appears** in `H`: an injective vertex map carrying every edge of `F` to an edge
of `H`. -/
def Appears {W V : Type} [DecidableEq V] (F : ThreeUniformHypergraph W)
    (H : ThreeUniformHypergraph V) : Prop :=
  ∃ φ : W → V, Function.Injective φ ∧ ∀ e ∈ F.edges, e.image φ ∈ H.edges

/-- **2-colourable** (Property B). -/
def IsTwoColorable {V : Type} (F : ThreeUniformHypergraph V) : Prop :=
  ∃ f : V → Fin 2, F.IsProperColoring f

end ThreeUniformHypergraph

/-- `F` is **obligatory** if it appears in every 3-uniform hypergraph of chromatic cardinal
exceeding `ℵ₀`. -/
def IsObligatory {W : Type} [Fintype W] (F : ThreeUniformHypergraph W) : Prop :=
  ∀ (V : Type) [DecidableEq V] (H : ThreeUniformHypergraph V),
    ℵ₀ < H.chromaticCardinal → F.Appears H

/-! ############################################################################
    SECTION 2 — the two properties the LITERATURE actually uses, which the
    formal-conjectures file does not define.
    ############################################################################ -/

/-- **3-partite** (the k-partite condition of [Ko01] at k = 3): there is a 3-colouring of the
vertices under which every hyperedge is rainbow. For a 3-element edge, "rainbow" and
"one vertex in each of three classes" are the same condition, so this is Komjáth's
k-partiteness verbatim at k = 3. -/
def IsThreePartite {V : Type} (F : ThreeUniformHypergraph V) : Prop :=
  ∃ p : V → Fin 3, ∀ e ∈ F.edges, ∀ u ∈ e, ∀ v ∈ e, u ≠ v → p u ≠ p v

/-- **Linear** (the [EHR73] condition): distinct hyperedges meet in at most one vertex. -/
def IsLinear {V : Type} [DecidableEq V] (F : ThreeUniformHypergraph V) : Prop :=
  ∀ e ∈ F.edges, ∀ f ∈ F.edges, e ≠ f → (e ∩ f).card ≤ 1

/-- **3-partite ⟹ 2-colourable.** Merge two of the three classes.

This is the containment that makes Komjáth's necessary condition STRICTLY STRONGER than the
Property-B condition recorded in formal-conjectures 593.lean, and it is what makes the
`obligatory_implies_two_colorable` slot of that file a consequence of [Ko01]. -/
theorem twoColorable_of_threePartite {V : Type} {F : ThreeUniformHypergraph V}
    (h : IsThreePartite F) : F.IsTwoColorable := by
  obtain ⟨p, hp⟩ := h
  refine ⟨fun v => if p v = 0 then 0 else 1, ?_⟩
  intro e he
  -- `p` is injective on `e`, and `e.card = 3 = Fintype.card (Fin 3)`, so `p` hits every colour.
  have hinj : Set.InjOn p (e : Set V) := by
    intro u hu v hv huv
    by_contra hne
    exact hp e he u hu v hv hne huv
  have hcard : (e.image p).card = 3 := by
    rw [Finset.card_image_of_injOn hinj, F.uniform e he]
  have huniv : e.image p = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hcard
  have h0 : (0 : Fin 3) ∈ e.image p := by rw [huniv]; exact Finset.mem_univ _
  have h1 : (1 : Fin 3) ∈ e.image p := by rw [huniv]; exact Finset.mem_univ _
  obtain ⟨u, hu, hpu⟩ := Finset.mem_image.mp h0
  obtain ⟨v, hv, hpv⟩ := Finset.mem_image.mp h1
  refine ⟨u, hu, v, hv, ?_⟩
  simp only [hpu, hpv]
  decide

/-! ############################################################################
    SECTION 3 — the witnesses.
    ############################################################################ -/

/-- The 3-partition of `C₃⁽³⁾` used below: original vertices `0,1,2` get colours `0,1,2`,
and the expansion vertex added to edge `{i,j}` gets the remaining colour. -/
def p3 : Fin 6 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 0
  | 5 => 1

/-- **`C₃⁽³⁾`** — the 3-uniform expansion of a triangle: original vertices `0,1,2`, and one
private new vertex `3,4,5` added to each of the three edges `01`, `12`, `20`.

[EGH75] Theorem 11.6: this hypergraph is NOT obligatory. -/
def C3exp : ThreeUniformHypergraph (Fin 6) where
  edges := {({0, 1, 3} : Finset (Fin 6)), {1, 2, 4}, {2, 0, 5}}
  uniform := by
    intro e he
    have he' : e = ({0, 1, 3} : Finset (Fin 6)) ∨ e = {1, 2, 4} ∨ e = {2, 0, 5} := he
    rcases he' with rfl | rfl | rfl <;> decide

/-- **`K₄⁽³⁾`** — all four triples on four vertices. -/
def K4exp : ThreeUniformHypergraph (Fin 4) where
  edges := {e : Finset (Fin 4) | e.card = 3}
  uniform := fun _ h => h

/-- The 2-colouring of `K₄⁽³⁾`: `{0,1}` vs `{2,3}`. -/
def c4 : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- **A single hyperedge.** -/
def oneEdge : ThreeUniformHypergraph (Fin 3) where
  edges := {(Finset.univ : Finset (Fin 3))}
  uniform := by
    intro e he
    have he' : e = (Finset.univ : Finset (Fin 3)) := he
    subst he'
    decide

/-! ############################################################################
    SECTION 4 — properties of the witnesses (all UNCONDITIONAL, by computation).
    ############################################################################ -/

theorem C3exp_threePartite : IsThreePartite C3exp := by
  refine ⟨p3, ?_⟩
  intro e he
  have he' : e = ({0, 1, 3} : Finset (Fin 6)) ∨ e = {1, 2, 4} ∨ e = {2, 0, 5} := he
  rcases he' with rfl | rfl | rfl <;> decide

theorem C3exp_linear : IsLinear C3exp := by
  intro e he f hf hne
  have he' : e = ({0, 1, 3} : Finset (Fin 6)) ∨ e = {1, 2, 4} ∨ e = {2, 0, 5} := he
  have hf' : f = ({0, 1, 3} : Finset (Fin 6)) ∨ f = {1, 2, 4} ∨ f = {2, 0, 5} := hf
  rcases he' with rfl | rfl | rfl <;> rcases hf' with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | decide

/-- `C₃⁽³⁾` is 2-colourable — so it is a legitimate input to the
`two_colorable_implies_obligatory` slot of formal-conjectures 593.lean. -/
theorem C3exp_twoColorable : C3exp.IsTwoColorable :=
  twoColorable_of_threePartite C3exp_threePartite

theorem K4exp_twoColorable : K4exp.IsTwoColorable := by
  refine ⟨c4, ?_⟩
  intro e he
  have key : ∀ e : Finset (Fin 4), e.card = 3 → ∃ u ∈ e, ∃ v ∈ e, c4 u ≠ c4 v := by decide
  exact key e he

theorem exists_third (u v : Fin 4) : ∃ w : Fin 4, w ≠ u ∧ w ≠ v := by
  revert u v
  decide

theorem card_triple (a b c : Fin 4) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ({a, b, c} : Finset (Fin 4)).card = 3 := by
  revert a b c
  decide

/-- `K₄⁽³⁾` is NOT 3-partite: four vertices cannot be split into three classes without two of
them colliding, and every pair of vertices of `K₄⁽³⁾` lies in a common hyperedge. -/
theorem K4exp_not_threePartite : ¬ IsThreePartite K4exp := by
  rintro ⟨p, hp⟩
  obtain ⟨u, v, huv, hpuv⟩ := Fintype.exists_ne_map_eq_of_card_lt p (by decide)
  obtain ⟨w, hwu, hwv⟩ := exists_third u v
  have hmem : ({u, v, w} : Finset (Fin 4)) ∈ K4exp.edges := card_triple u v w huv hwu hwv
  have hu : u ∈ ({u, v, w} : Finset (Fin 4)) := by simp
  have hv : v ∈ ({u, v, w} : Finset (Fin 4)) := by simp
  exact hp _ hmem u hu v hv huv hpuv

/-- `K₄⁽³⁾` is NOT linear: `{0,1,2}` and `{0,1,3}` meet in two vertices. -/
theorem K4exp_not_linear : ¬ IsLinear K4exp := by
  intro h
  have h1 : ({0, 1, 2} : Finset (Fin 4)) ∈ K4exp.edges := by
    show ({0, 1, 2} : Finset (Fin 4)).card = 3
    decide
  have h2 : ({0, 1, 3} : Finset (Fin 4)) ∈ K4exp.edges := by
    show ({0, 1, 3} : Finset (Fin 4)).card = 3
    decide
  have hne : ({0, 1, 2} : Finset (Fin 4)) ≠ ({0, 1, 3} : Finset (Fin 4)) := by decide
  have hle := h _ h1 _ h2 hne
  revert hle
  decide

/-! ############################################################################
    SECTION 5 — the correctness warning.

    Each theorem takes ONE published literature verdict as an explicitly named hypothesis and
    concludes that the characterization recorded in formal-conjectures 593.lean is FALSE.
    The `answer(sorry)` slot of `erdos_593` and of
    `erdos_593.variants.two_colorable_implies_obligatory` must therefore be filled with
    `False`, not `True`.
    ############################################################################ -/

/-- The statement occupying the `two_colorable_implies_obligatory` slot of
formal-conjectures 593.lean. -/
def SufficientDirection : Prop :=
  ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W), F.IsTwoColorable → IsObligatory F

/-- The statement occupying the `obligatory_implies_two_colorable` slot. -/
def NecessaryDirection : Prop :=
  ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W), IsObligatory F → F.IsTwoColorable

/-- The statement occupying the main `erdos_593` slot. -/
def Characterization : Prop :=
  ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W), IsObligatory F ↔ F.IsTwoColorable

/-- **[EGH75] Thm 11.6 refutes the sufficient direction.**
`C₃⁽³⁾` is 2-colourable (proved above) and non-obligatory (Erdős–Galvin–Hajnal). -/
theorem sufficientDirection_false_of_EGH (hEGH : ¬ IsObligatory C3exp) : ¬ SufficientDirection :=
  fun h => hEGH (h (Fin 6) C3exp C3exp_twoColorable)

/-- **[Ko01] refutes the sufficient direction.**
`K₄⁽³⁾` is 2-colourable but not 3-partite; obligatory ⟹ 3-partite. -/
theorem sufficientDirection_false_of_Komjath
    (hKo : ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
      IsObligatory F → IsThreePartite F) : ¬ SufficientDirection :=
  fun h => K4exp_not_threePartite (hKo (Fin 4) K4exp (h (Fin 4) K4exp K4exp_twoColorable))

/-- **[EHR73] refutes the sufficient direction.**
`K₄⁽³⁾` is 2-colourable but not linear; obligatory ⟹ linear. -/
theorem sufficientDirection_false_of_EHR
    (hEHR : ∀ (W : Type) [Fintype W] [DecidableEq W] (F : ThreeUniformHypergraph W),
      IsObligatory F → IsLinear F) : ¬ SufficientDirection :=
  fun h => K4exp_not_linear (hEHR (Fin 4) K4exp (h (Fin 4) K4exp K4exp_twoColorable))

/-- **The conjectural characterization recorded in formal-conjectures 593.lean is FALSE**,
on any one of the three literature verdicts above. Stated here from [EGH75], the most specific
of the three. -/
theorem characterization_false_of_EGH (hEGH : ¬ IsObligatory C3exp) : ¬ Characterization :=
  fun h => hEGH ((h (Fin 6) C3exp).mpr C3exp_twoColorable)

/-- The same conclusion from [Ko01]. -/
theorem characterization_false_of_Komjath
    (hKo : ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
      IsObligatory F → IsThreePartite F) : ¬ Characterization :=
  fun h => sufficientDirection_false_of_Komjath hKo (fun W _ F hF => (h W F).mpr hF)

/-- The same conclusion from [EHR73]. -/
theorem characterization_false_of_EHR
    (hEHR : ∀ (W : Type) [Fintype W] [DecidableEq W] (F : ThreeUniformHypergraph W),
      IsObligatory F → IsLinear F) : ¬ Characterization :=
  fun h => sufficientDirection_false_of_EHR hEHR (fun W _ F hF => (h W F).mpr hF)

/-- **The necessary direction, by contrast, is TRUE** — it is a corollary of [Ko01] together
with the (unconditional) containment 3-partite ⟹ 2-colourable.

So the three `answer(sorry)` slots of formal-conjectures 593.lean are, modulo the literature:
`obligatory_implies_two_colorable := True`, `two_colorable_implies_obligatory := False`,
`erdos_593 := False`. A formaliser who fills all three with `True` commits two false answers. -/
theorem necessaryDirection_true_of_Komjath
    (hKo : ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),
      IsObligatory F → IsThreePartite F) : NecessaryDirection :=
  fun _ _ _ hF => twoColorable_of_threePartite (hKo _ _ hF)

/-! ############################################################################
    SECTION 6 — the frontier, pinned.

    The published state of Erdős 593 sandwiches the obligatory class:

        loose forests  ⊆  OBLIGATORY  ⊆  linear ∧ 3-partite  ⊊  2-colourable
        [Ko01]                          [EHR73] ∧ [Ko01]        (this file)

    Both literature-supplied containments are STRICT, and this file supplies the finite witness
    for each strictness. The open problem lives entirely inside the middle gap.
    ############################################################################ -/

/-- **The outer containment is strict, unconditionally.** `K₄⁽³⁾` is 2-colourable yet fails
BOTH known necessary conditions. So Property B is strictly weaker than what the literature
already forces of an obligatory hypergraph — the formal-conjectures conjecture is not merely
unproved, its two classes are provably different. -/
theorem outer_containment_strict :
    K4exp.IsTwoColorable ∧ ¬ IsThreePartite K4exp ∧ ¬ IsLinear K4exp :=
  ⟨K4exp_twoColorable, K4exp_not_threePartite, K4exp_not_linear⟩

/-- **The upper containment is strict**, given [EGH75]. `C₃⁽³⁾` satisfies both known necessary
conditions (linear AND 3-partite — proved here by computation) and is nevertheless NOT
obligatory. So no combination of [EHR73] and [Ko01] can characterise the obligatory class: a
genuinely new obstruction is required, and `C₃⁽³⁾` is the smallest witness the literature
names. -/
theorem upper_containment_strict (hEGH : ¬ IsObligatory C3exp) :
    IsLinear C3exp ∧ IsThreePartite C3exp ∧ ¬ IsObligatory C3exp :=
  ⟨C3exp_linear, C3exp_threePartite, hEGH⟩

/-! ############################################################################
    SECTION 7 — the one obligatory instance provable with no literature input at all.
    ############################################################################ -/

/-- Restatement of the formal-conjectures lemma `nonempty_edges_if_large_chromatic`:
a hypergraph of uncountable chromatic cardinal has an edge. -/
theorem edges_nonempty_of_large_chromatic {V : Type} (H : ThreeUniformHypergraph V)
    (hχ : ℵ₀ < H.chromaticCardinal) : H.edges.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hprop : H.IsProperColoring (fun _ : V => (0 : Fin 1)) := by
    intro e he
    rw [hempty] at he
    exact (Set.mem_empty_iff_false e).mp he |>.elim
  have hle : H.chromaticCardinal ≤ 1 := by
    apply csInf_le
    · exact ⟨0, fun _ ⟨_, _, _, _⟩ => zero_le⟩
    · refine ⟨Fin 1, ?_, fun _ => 0, hprop⟩
      simp
  have h1le : (1 : Cardinal) ≤ ℵ₀ := le_of_lt Cardinal.one_lt_aleph0
  exact absurd (lt_of_lt_of_le hχ (hle.trans h1le)) (lt_irrefl _)

/-- **A single hyperedge is obligatory** — unconditionally, with no literature input.

formal-conjectures 593.lean proves only that the EMPTY hypergraph is obligatory. This is the
first non-degenerate rung: it is the base case of the loose-forest induction of [Ko01], and
together with that file's own `obligatory_monotone` it is, as far as this campaign could
determine, the only sorry-free NON-DEGENERATE obligatory instance anywhere in the Lean
ecosystem (the upstream `empty_hypergraph_obligatory` is sorry-free but vacuous). -/
theorem oneEdge_obligatory : IsObligatory oneEdge := by
  intro V _ H hχ
  obtain ⟨e, he⟩ := edges_nonempty_of_large_chromatic H hχ
  have hcard : e.card = 3 := H.uniform e he
  refine ⟨fun i => ((e.equivFin.symm (finCongr hcard.symm i)) : V), ?_, ?_⟩
  · intro i j hij
    exact (finCongr hcard.symm).injective (e.equivFin.symm.injective (Subtype.val_injective hij))
  · intro f hf
    have hf' : f = (Finset.univ : Finset (Fin 3)) := hf
    subst hf'
    have hsub : (Finset.univ : Finset (Fin 3)).image
        (fun i => ((e.equivFin.symm (finCongr hcard.symm i)) : V)) ⊆ e := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact (e.equivFin.symm (finCongr hcard.symm i)).2
    have hinj : Function.Injective
        (fun i => ((e.equivFin.symm (finCongr hcard.symm i)) : V)) := by
      intro i j hij
      exact (finCongr hcard.symm).injective (e.equivFin.symm.injective (Subtype.val_injective hij))
    have hcard2 : ((Finset.univ : Finset (Fin 3)).image
        (fun i => ((e.equivFin.symm (finCongr hcard.symm i)) : V))).card = 3 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have himg : (Finset.univ : Finset (Fin 3)).image
        (fun i => ((e.equivFin.symm (finCongr hcard.symm i)) : V)) = e :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard2]; exact hcard.le)
    rw [himg]
    exact he

end Erdos593
