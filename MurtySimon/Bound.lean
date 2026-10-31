/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MurtySimon.Components

/-!
# Switch exits and the bound `|E(G) \ M| ≤ |non-edges|` (Section 2 of Das–Fox)

For a maximal matching `M`, a *switch exit* is an ordered pair `(x, y)` such that `xy` is a
noncritical non-edge, `x` is covered by `M` with partner `x* = mate M x`, and `x*y` is a vertex of
the auxiliary graph `𝓘'` (`IsExit`); it belongs to the component of `x*y` (`compOf`). We give the
exit weight `2` if `y` is uncovered (a *safe* exit) and `1` otherwise (`wt`). This is the bipartite
multigraph `𝓙` of the paper, read from the exits: every noncritical non-edge receives total weight
at most `2` (Lemma 2.7), and every left-lopsided component receives weight at least `2`
(Lemmas 2.10 and 2.11, Corollary 2.12). With Lemma 2.4 this gives Lemma 1.2 (`card_Lt_le`) and
the conditions of Corollary 2.14 in the equality case (`eq_case_conditions`).
-/

@[expose] public section

namespace MurtySimon

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable section

/-! ### Matchings -/

/-- `x` is covered by `M`. -/
def Covered (M : Finset (Sym2 V)) (x : V) : Prop := ∃ y, s(x, y) ∈ M

/-- The partner of `x` in `M` (`x` itself if `x` is uncovered). -/
def mate (M : Finset (Sym2 V)) (x : V) : V := if h : ∃ y, s(x, y) ∈ M then h.choose else x

variable {M : Finset (Sym2 V)}

lemma mate_spec {x : V} (h : Covered M x) : s(x, mate M x) ∈ M := by
  have h' : ∃ y, s(x, y) ∈ M := h
  rw [mate, dif_pos h']; exact h'.choose_spec

lemma IsEdgeMatching.eq_of_mem (hM : IsEdgeMatching G M) {x y z : V} (h1 : s(x, y) ∈ M)
    (h2 : s(x, z) ∈ M) : y = z := by
  by_contra hyz
  have hne : s(x, y) ≠ s(x, z) := fun h => hyz (Sym2.congr_right.1 h)
  exact hM.2 _ h1 _ h2 hne x (Sym2.mem_mk_left x y) (Sym2.mem_mk_left x z)

lemma IsEdgeMatching.mate_eq (hM : IsEdgeMatching G M) {x y : V} (h : s(x, y) ∈ M) :
    mate M x = y :=
  hM.eq_of_mem (mate_spec ⟨y, h⟩) h

lemma IsEdgeMatching.mate_mate (hM : IsEdgeMatching G M) {x : V} (h : Covered M x) :
    mate M (mate M x) = x :=
  hM.mate_eq (Sym2.eq_swap ▸ mate_spec h)

lemma covered_mate {x : V} (h : Covered M x) : Covered M (mate M x) :=
  ⟨x, Sym2.eq_swap ▸ mate_spec h⟩

lemma IsEdgeMatching.adj_mate (hM : IsEdgeMatching G M) {x : V} (h : Covered M x) :
    G.Adj x (mate M x) :=
  hM.1 _ (mate_spec h)

lemma IsEdgeMatching.mate_ne (hM : IsEdgeMatching G M) {x : V} (h : Covered M x) :
    mate M x ≠ x :=
  (hM.adj_mate h).ne'

lemma not_mem_of_mate_ne {x y : V} (h : mate M x ≠ y) (hM : IsEdgeMatching G M) :
    s(x, y) ∉ M := fun hm => h (hM.mate_eq hm)

lemma IsMaximalEdgeMatching.covered (hmax : IsMaximalEdgeMatching G M) {a b : V}
    (hab : G.Adj a b) (h : s(a, b) ∉ M) : Covered M a ∨ Covered M b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hcov : ∀ v, ∀ f ∈ M, v ∈ f → Covered M v := by
    intro v f hf hv
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
    exact ⟨w, hf⟩
  have hab' : ∀ v ∈ s(a, b), ¬ Covered M v := by
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ha
    · exact hb
  apply hmax.2 s(a, b) hab h
  refine ⟨fun e he => ?_, fun e he f hf hef v hve hvf => ?_⟩
  · rcases mem_insert.1 he with rfl | he
    · exact hab
    · exact hmax.1.1 e he
  · rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
    · exact hef rfl
    · exact hab' v hve (hcov v f hf hvf)
    · exact hab' v hvf (hcov v e he hve)
    · exact hmax.1.2 e he f hf hef v hve hvf

/-! ### Critical non-edges, oriented -/

lemma IsCrit.exists_mid {x y : V} (h : IsCrit G s(x, y)) : ∃ u, IsMid G x y u := by
  obtain ⟨x', y', u, hf, hm⟩ := h
  rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨u, hm⟩
  · exact ⟨u, hm.symm⟩

/-- A non-edge with a common neighbour `w` is critical iff `w` is its unique common neighbour. -/
lemma isMid_of_isCrit {x y w : V} (h : IsCrit G s(x, y)) (hxw : G.Adj x w) (hwy : G.Adj w y) :
    IsMid G x y w := by
  obtain ⟨u, hu⟩ := h.exists_mid
  have := hu.2.2.2.2 w hxw hwy
  subst this
  exact hu

/-! ### Switch exits -/

variable (G M) in
/-- The noncritical non-edges. -/
def Nc : Finset (Sym2 V) := univ.filter fun f => f ∈ Gᶜ.edgeSet ∧ ¬ IsCrit G f

variable (G M) in
/-- `(x, y)` is a switch exit: `xy` is a noncritical non-edge, `x` is covered and `x*y` is a
vertex of `𝓘'`. -/
def IsExit (p : V × V) : Prop :=
  s(p.1, p.2) ∈ Gᶜ.edgeSet ∧ ¬ IsCrit G s(p.1, p.2) ∧ Covered M p.1 ∧
    s(mate M p.1, p.2) ∈ Lt G M ∪ Rt G

variable (G M) in
/-- The set of switch exits. -/
def exits : Finset (V × V) := univ.filter (IsExit G M)

variable (G M) in
/-- The component of `𝓘'` to which a switch exit belongs. -/
def compOf (p : V × V) : (aux G M).ConnectedComponent :=
  (aux G M).connectedComponentMk s(mate M p.1, p.2)

variable (M) in
/-- The weight of a switch exit: `2` for a safe exit, `1` otherwise. -/
def wt (p : V × V) : ℕ := if Covered M p.2 then 1 else 2

lemma one_le_wt (p : V × V) : 1 ≤ wt M p := by unfold wt; split_ifs <;> omega

/-- **Lemma 2.7.** Each noncritical non-edge receives total weight at most `2`. -/
lemma sum_wt_le : ∑ p ∈ exits G M, wt M p ≤ 2 * #(Nc G) := by
  have hmaps : ∀ p ∈ exits G M, s(p.1, p.2) ∈ Nc G := by
    intro p hp
    obtain ⟨h1, h2, -, -⟩ := (mem_filter.1 hp).2
    exact mem_filter.2 ⟨mem_univ _, h1, h2⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc ∑ f ∈ Nc G, ∑ p ∈ (exits G M).filter (fun p => s(p.1, p.2) = f), wt M p
      ≤ ∑ _f ∈ Nc G, 2 := by
        apply sum_le_sum
        intro f hf
        induction f using Sym2.ind with
        | h x y =>
          have hxy : x ≠ y := by
            have := (mem_filter.1 hf).2.1
            rw [mem_edgeSet, compl_adj] at this
            exact this.1
          have hsub : (exits G M).filter (fun p => s(p.1, p.2) = s(x, y)) ⊆
              ({(x, y), (y, x)} : Finset (V × V)).filter (· ∈ exits G M) := by
            intro p hp
            obtain ⟨hpX, hpf⟩ := mem_filter.1 hp
            refine mem_filter.2 ⟨?_, hpX⟩
            rcases Sym2.eq_iff.1 hpf with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · simp [Prod.ext_iff, h1, h2]
            · simp [Prod.ext_iff, h1, h2]
          refine (sum_le_sum_of_subset hsub).trans ?_
          have hne : (x, y) ≠ (y, x) := fun h => hxy (Prod.ext_iff.1 h).1
          rw [sum_filter, sum_pair hne]
          simp only [exits, mem_filter, mem_univ, true_and, IsExit, wt]
          by_cases hx : Covered M x <;> by_cases hy : Covered M y <;> simp [hx, hy] <;>
            split_ifs <;> omega
    _ = 2 * #(Nc G) := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The total weight of the exits of a component. -/
def compWt (C : (aux G M).ConnectedComponent) : ℕ :=
  ∑ p ∈ (exits G M).filter (fun p => compOf G M p = C), wt M p

lemma two_le_compWt_of_safe {C : (aux G M).ConnectedComponent} {p : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) (hs : ¬ Covered M p.2) : 2 ≤ compWt C := by
  have : wt M p = 2 := by simp [wt, hs]
  rw [← this]
  exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hp, hpC⟩)

lemma two_le_compWt_of_two {C : (aux G M).ConnectedComponent} {p q : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) (hq : q ∈ exits G M) (hqC : compOf G M q = C)
    (hpq : p ≠ q) : 2 ≤ compWt C := by
  have hsub : ({p, q} : Finset (V × V)) ⊆ (exits G M).filter (fun p => compOf G M p = C) := by
    intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · exact mem_filter.2 ⟨hp, hpC⟩
    · rw [mem_singleton.1 hr]; exact mem_filter.2 ⟨hq, hqC⟩
  calc 2 ≤ wt M p + wt M q := by have := one_le_wt (M := M) p; have := one_le_wt (M := M) q; omega
    _ = ∑ r ∈ ({p, q} : Finset (V × V)), wt M r := (sum_pair hpq).symm
    _ ≤ compWt C := sum_le_sum_of_subset hsub

lemma one_le_compWt {C : (aux G M).ConnectedComponent} {p : V × V}
    (hp : p ∈ exits G M) (hpC : compOf G M p = C) : 1 ≤ compWt C :=
  (one_le_wt p).trans (single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hp, hpC⟩))

/-- A switch exit `p` *recovers* the edge `ℓ`: either `x*y = ℓ`, or `x*y` is a critical non-edge
`zy` with critical 2-path `(z, u, y)` and `ℓ = uy`. -/
def Recovers (p : V × V) (ℓ : Sym2 V) : Prop :=
  s(mate M p.1, p.2) = ℓ ∨
    ∃ z u, s(mate M p.1, p.2) = s(z, p.2) ∧ IsMid G z p.2 u ∧ ℓ = s(u, p.2)

lemma Recovers.unique {p : V × V} {ℓ₁ ℓ₂ : Sym2 V} (h₁ : Recovers (G := G) (M := M) p ℓ₁)
    (h₂ : Recovers (G := G) (M := M) p ℓ₂) (hℓ₁ : ℓ₁ ∈ G.edgeSet) (hℓ₂ : ℓ₂ ∈ G.edgeSet) :
    ℓ₁ = ℓ₂ := by
  rcases h₁ with h₁ | ⟨z₁, u₁, hz₁, hm₁, rfl⟩ <;> rcases h₂ with h₂ | ⟨z₂, u₂, hz₂, hm₂, rfl⟩
  · exact h₁.symm.trans h₂
  · have : s(z₂, p.2) ∈ G.edgeSet := by rw [← hz₂, h₁]; exact hℓ₁
    exact absurd this hm₂.2.1
  · have : s(z₁, p.2) ∈ G.edgeSet := by rw [← hz₁, h₂]; exact hℓ₂
    exact absurd this hm₁.2.1
  · have hz : z₁ = z₂ := Sym2.congr_left.1 (hz₁.symm.trans hz₂)
    subst hz
    rw [hm₁.unique hm₂]

/-! ### Left-lopsided components have weight at least two -/

section Lopsided

variable (hM : IsEdgeMatching G M) {C : (aux G M).ConnectedComponent}
  (hC : cA G M C = cB G M C + 1)
include hM hC

/-- **Lemma 2.9.** Switching a left vertex of a left-lopsided component gives a noncritical
non-edge, hence a switch exit. -/
lemma exit_of_left {a b : V} (ha : Covered M a) (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hL : s(mate M a, b) ∈ Lt G M) (hLC : (aux G M).connectedComponentMk s(mate M a, b) = C) :
    (a, b) ∈ exits G M ∧ compOf G M (a, b) = C := by
  refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_, ha, mem_union_left _ hL⟩, hLC⟩
  · rw [mem_edgeSet, compl_adj]; exact ⟨hab, hnadj⟩
  · intro hcrit
    have hmid : IsMid G a b (mate M a) := isMid_of_isCrit hcrit (hM.adj_mate ha) (mem_Lt.1 hL).1
    -- the critical non-edge `ab` has only one neighbour in `𝓘'`
    have hdeg := (comp_count M C).2 hC |>.1 s(a, b) (mem_Rt.2 hcrit) (by
      rw [← hLC]
      apply ConnectedComponent.connectedComponentMk_eq_of_adj
      rw [aux_adj]
      exact Or.inr ⟨(mem_Lt.1 hL).2, (onPath_iff hmid).2 (Or.inr rfl)⟩)
    have hsub : (aux G M).neighborFinset s(a, b) ⊆ {s(mate M a, b)} := by
      intro e he
      obtain ⟨h1 | h1, h2⟩ := (mem_neighborFinset_right hmid).1 he
      · exact absurd (h1 ▸ mate_spec ha) h2
      · exact mem_singleton.2 h1
    have := card_le_card hsub
    rw [card_singleton] at this
    omega

/-- **Lemma 2.10.** A component consisting of a single left vertex has a safe switch exit or two
switch exits. -/
lemma two_le_compWt_single (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G)
    (h1 : cA G M C = 1) : 2 ≤ compWt C := by
  have hB : cB G M C = 0 := by omega
  obtain ⟨e, he⟩ := card_eq_one.1 h1
  have hmem : e ∈ (Lt G M).filter fun e => (aux G M).connectedComponentMk e = C := by
    rw [he]; exact mem_singleton_self e
  have heL : e ∈ Lt G M := (mem_filter.1 hmem).1
  have heC : (aux G M).connectedComponentMk e = C := (mem_filter.1 hmem).2
  -- `e` has no neighbours in `𝓘'`
  have hnb : ∀ f, ¬ (aux G M).Adj e f := by
    intro f hf
    have hfR : f ∈ Rt G := by
      rcases aux_adj_cases hf with h | h
      · exact h.2.1
      · exact absurd h.2.1 (not_mem_Rt_of_mem_Lt heL)
    have hfC : (aux G M).connectedComponentMk f = C :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hf).symm.trans heC
    have : f ∈ (Rt G).filter fun f => (aux G M).connectedComponentMk f = C :=
      mem_filter.2 ⟨hfR, hfC⟩
    have h0 : cB G M C = #((Rt G).filter fun f => (aux G M).connectedComponentMk f = C) := rfl
    rw [hB] at h0
    exact absurd (h0 ▸ card_pos.2 ⟨f, this⟩ : 0 < 0) (lt_irrefl 0)
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨hxy, hxyM⟩ := mem_Lt.1 heL
    rw [mem_edgeSet] at hxy
    -- from a covered endpoint we get a switch exit
    have key : ∀ a b, s(a, b) = s(x, y) → Covered M a →
        (mate M a, b) ∈ exits G M ∧ compOf G M (mate M a, b) = C := by
      intro a b hab ha
      have hadj : G.Adj a b := by rw [← mem_edgeSet, hab]; exact hxy
      have habM : s(a, b) ∉ M := hab ▸ hxyM
      have hne : mate M a ≠ b := fun h => habM (h ▸ mate_spec ha)
      have hnadj : ¬ G.Adj (mate M a) b := by
        intro h'
        obtain ⟨f, hf⟩ := exists_onPath_of_triangle hG hadj (hM.adj_mate ha) h'
        exact hnb f (hab ▸ aux_adj.2 (Or.inl ⟨habM, hf⟩))
      have hmm : mate M (mate M a) = a := hM.mate_mate ha
      exact exit_of_left hM hC (covered_mate ha) hne hnadj (by rw [hmm, hab]; exact heL)
        (by rw [hmm, hab]; exact heC)
    rcases hmax.covered hxy hxyM with hx | hy
    · obtain ⟨hp, hpC⟩ := key x y rfl hx
      by_cases hy : Covered M y
      · obtain ⟨hq, hqC⟩ := key y x Sym2.eq_swap hy
        refine two_le_compWt_of_two hp hpC hq hqC ?_
        intro h
        exact hxy.ne (Prod.ext_iff.1 h).2.symm
      · exact two_le_compWt_of_safe hp hpC hy
    · obtain ⟨hp, hpC⟩ := key y x Sym2.eq_swap hy
      by_cases hx : Covered M x
      · obtain ⟨hq, hqC⟩ := key x y rfl hx
        refine two_le_compWt_of_two hp hpC hq hqC ?_
        intro h
        exact hxy.ne (Prod.ext_iff.1 h).2
      · exact two_le_compWt_of_safe hp hpC hx

/-- The analysis of one leaf in the proof of **Lemma 2.11**: either the component has weight at
least two, or the leaf produces a switch exit from which the leaf can be recovered. -/
lemma leaf_analysis (hmax : IsMaximalEdgeMatching G M) {ℓ : Sym2 V} (hℓL : ℓ ∈ Lt G M)
    (hℓC : (aux G M).connectedComponentMk ℓ = C) (hℓd : #((aux G M).neighborFinset ℓ) = 1) :
    2 ≤ compWt C ∨ ∃ p ∈ exits G M, compOf G M p = C ∧ Recovers (G := G) (M := M) p ℓ := by
  obtain ⟨f, hf⟩ := card_eq_one.1 hℓd
  have hℓf : (aux G M).Adj ℓ f := (mem_neighborFinset _ _ _).1 (hf ▸ mem_singleton_self f)
  have hnbr : ∀ g, (aux G M).Adj ℓ g → g = f := fun g hg =>
    mem_singleton.1 (hf ▸ (mem_neighborFinset _ _ _).2 hg)
  have hfC : (aux G M).connectedComponentMk f = C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hℓf).symm.trans hℓC
  have hon : OnPath G ℓ f := by
    rcases aux_adj_cases hℓf with h | h
    · exact h.2.2
    · exact absurd h.2.1 (not_mem_Rt_of_mem_Lt hℓL)
  -- orient the critical 2-path as `(x, u, y)` with `ℓ = uy`
  obtain ⟨x, y, u, rfl, hm, hℓ⟩ : ∃ x y u, f = s(x, y) ∧ IsMid G x y u ∧ ℓ = s(u, y) := by
    obtain ⟨x, y, u, rfl, hm, rfl⟩ := hon
    exact ⟨y, x, u, Sym2.eq_swap, hm.symm, Sym2.eq_swap⟩
  subst hℓ
  have hfR : s(x, y) ∈ Rt G := mem_Rt.2 hm.isCrit
  -- both edges of the critical 2-path lie in `𝓘'`
  have hdeg := (comp_count M C).2 hC |>.1 s(x, y) hfR hfC
  have hxuM : s(x, u) ∉ M := by
    intro hin
    have hsub : (aux G M).neighborFinset s(x, y) ⊆ {s(u, y)} := by
      intro e he
      obtain ⟨h1 | h1, h2⟩ := (mem_neighborFinset_right hm).1 he
      · exact absurd (h1 ▸ hin) h2
      · exact mem_singleton.2 h1
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
  have huyM : s(u, y) ∉ M := (mem_Lt.1 hℓL).2
  have hxu : G.Adj x u := hm.2.2.1
  have huy : G.Adj u y := hm.2.2.2.1
  have hxuL : s(x, u) ∈ Lt G M := mem_Lt.2 ⟨hxu, hxuM⟩
  have hxuC : (aux G M).connectedComponentMk s(x, u) = C := by
    rw [← hfC]
    apply ConnectedComponent.connectedComponentMk_eq_of_adj
    rw [aux_adj]
    exact Or.inl ⟨hxuM, (onPath_iff hm).2 (Or.inl rfl)⟩
  have hxy : x ≠ y := hm.1
  have hux : u ≠ x := hm.ne_left
  have huy' : u ≠ y := hm.ne_right
  -- Case 1: `u` covered
  have case1 : Covered M u →
      ((mate M u, x) ∈ exits G M ∧ compOf G M (mate M u, x) = C) ∨
      ((mate M u, y) ∈ exits G M ∧ compOf G M (mate M u, y) = C ∧
        Recovers (G := G) (M := M) (mate M u, y) s(u, y)) := by
    intro hu
    have hmm : mate M (mate M u) = u := hM.mate_mate hu
    have hu'x : mate M u ≠ x := fun h => hxuM (by rw [Sym2.eq_swap, ← h]; exact mate_spec hu)
    have hu'y : mate M u ≠ y := fun h => huyM (h ▸ mate_spec hu)
    by_cases h1 : G.Adj (mate M u) x
    · have h2 : ¬ G.Adj (mate M u) y := by
        intro h2
        exact hM.mate_ne hu (hm.2.2.2.2 _ h1.symm h2)
      right
      obtain ⟨hp, hpC⟩ := exit_of_left hM hC (covered_mate hu) hu'y h2
        (by rw [hmm]; exact hℓL) (by rw [hmm]; exact hℓC)
      exact ⟨hp, hpC, Or.inl (by rw [hmm])⟩
    · left
      exact exit_of_left hM hC (covered_mate hu) hu'x h1
        (by rw [hmm, Sym2.eq_swap]; exact hxuL) (by rw [hmm, Sym2.eq_swap]; exact hxuC)
  -- Case 2: `x` covered
  have case2 : Covered M x →
      ((mate M x, u) ∈ exits G M ∧ compOf G M (mate M x, u) = C) ∨
      ((mate M x, y) ∈ exits G M ∧ compOf G M (mate M x, y) = C ∧
        Recovers (G := G) (M := M) (mate M x, y) s(u, y)) := by
    intro hx
    have hmm : mate M (mate M x) = x := hM.mate_mate hx
    have hx'u : mate M x ≠ u := fun h => hxuM (h ▸ mate_spec hx)
    have hx'y : mate M x ≠ y := fun h => hm.2.1 (h ▸ hM.adj_mate hx)
    by_cases h1 : G.Adj (mate M x) u
    · right
      have h2 : ¬ G.Adj (mate M x) y := by
        intro h2
        exact hx'u (hm.2.2.2.2 _ (hM.adj_mate hx) h2)
      have hnc : ¬ IsCrit G s(mate M x, y) := by
        intro hcrit
        have hm' : IsMid G (mate M x) y u := isMid_of_isCrit hcrit h1 huy
        have hadj : (aux G M).Adj s(u, y) s(mate M x, y) :=
          aux_adj.2 (Or.inl ⟨huyM, (onPath_iff hm').2 (Or.inr rfl)⟩)
        have := hnbr _ hadj
        exact hM.mate_ne hx (Sym2.congr_left.1 this)
      refine ⟨mem_filter.2 ⟨mem_univ _, ?_, hnc, covered_mate hx, ?_⟩, ?_, ?_⟩
      · rw [mem_edgeSet, compl_adj]; exact ⟨hx'y, h2⟩
      · rw [hmm]; exact mem_union_right _ hfR
      · simp only [compOf, hmm]; exact hfC
      · exact Or.inr ⟨x, u, by rw [hmm], hm, rfl⟩
    · left
      exact exit_of_left hM hC (covered_mate hx) hx'u h1 (by rw [hmm]; exact hxuL)
        (by rw [hmm]; exact hxuC)
  have hne1 : (mate M u, x) ≠ (mate M x, u) := fun h => hux (Prod.ext_iff.1 h).2.symm
  have hne2 : (mate M u, x) ≠ (mate M x, y) := fun h => hxy (Prod.ext_iff.1 h).2
  have hne3 : (mate M x, u) ≠ (mate M u, y) := fun h => huy' (Prod.ext_iff.1 h).2
  rcases hmax.covered hxu hxuM with hx | hu
  · rcases case2 hx with ⟨hp, hpC⟩ | ⟨hp, hpC, hrec⟩
    · -- Case 2a
      by_cases hu : Covered M u
      · left
        rcases case1 hu with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · exact two_le_compWt_of_two hq hqC hp hpC hne1
        · exact two_le_compWt_of_two hp hpC hq hqC hne3
      · exact Or.inl (two_le_compWt_of_safe hp hpC hu)
    · by_cases hu : Covered M u
      · rcases case1 hu with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · -- Case 1a with `x` covered
          exact Or.inl (two_le_compWt_of_two hq hqC hp hpC hne2)
        · exact Or.inr ⟨_, hp, hpC, hrec⟩
      · exact Or.inr ⟨_, hp, hpC, hrec⟩
  · rcases case1 hu with ⟨hp, hpC⟩ | ⟨hp, hpC, hrec⟩
    · -- Case 1a
      by_cases hx : Covered M x
      · left
        rcases case2 hx with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · exact two_le_compWt_of_two hp hpC hq hqC hne1
        · exact two_le_compWt_of_two hp hpC hq hqC hne2
      · exact Or.inl (two_le_compWt_of_safe hp hpC hx)
    · by_cases hx : Covered M x
      · rcases case2 hx with ⟨hq, hqC⟩ | ⟨hq, hqC, -⟩
        · exact Or.inl (two_le_compWt_of_two hq hqC hp hpC hne3)
        · exact Or.inr ⟨_, hp, hpC, hrec⟩
      · exact Or.inr ⟨_, hp, hpC, hrec⟩

/-- **Corollary 2.12** (Lemmas 2.10 and 2.11). Every left-lopsided component has weight at least
two. -/
lemma two_le_compWt (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) : 2 ≤ compWt C := by
  by_cases h1 : cA G M C = 1
  · exact two_le_compWt_single hM hC hmax hG h1
  have h2 : 2 ≤ cA G M C := by omega
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hC₁, hC₂, hd₁, hd₂⟩ := (comp_count M C).2 hC |>.2 h2
  rcases leaf_analysis hM hC hmax hl₁ hC₁ hd₁ with h | ⟨p, hp, hpC, hrp⟩
  · exact h
  rcases leaf_analysis hM hC hmax hl₂ hC₂ hd₂ with h | ⟨q, hq, hqC, hrq⟩
  · exact h
  refine two_le_compWt_of_two hp hpC hq hqC ?_
  rintro rfl
  exact hne (hrp.unique hrq (mem_Lt.1 hl₁).1 (mem_Lt.1 hl₂).1)

end Lopsided

/-! ### Lemma 1.2 and the equality conditions -/

lemma sum_cA (M : Finset (Sym2 V)) : ∑ C, cA G M C = #(Lt G M) :=
  (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm

lemma sum_cB (M : Finset (Sym2 V)) : ∑ C, cB G M C = #(Rt G) :=
  (card_eq_sum_card_fiberwise fun _ _ => mem_univ _).symm

lemma sum_compWt : ∑ C, compWt (G := G) (M := M) C = ∑ p ∈ exits G M, wt M p :=
  sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) _

/-- The chain of inequalities of Section 2, with the quantities needed for the equality case:
`|E'| − |F_c| ≤ |C_ℓ| ≤ |F_nc|`, where `C_ℓ` is the set of left-lopsided components. -/
lemma main_chain (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) :
    (#(Lt G M) : ℤ) - #(Rt G) =
      ∑ C, ((cA G M C : ℤ) - cB G M C) ∧
    (∀ C, ((cA G M C : ℤ) - cB G M C) ≤ if cA G M C = cB G M C + 1 then 1 else 0) ∧
    2 * #((univ : Finset (aux G M).ConnectedComponent).filter fun C => cA G M C = cB G M C + 1)
      + ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
          (fun C => ¬ cA G M C = cB G M C + 1), compWt (G := G) (M := M) C
      ≤ 2 * #(Nc G) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sum_sub_distrib, ← sum_cA, ← sum_cB]; push_cast; ring
  · intro C
    have := (comp_count M C).1
    split_ifs with h <;> omega
  · have h1 : 2 * #((univ : Finset (aux G M).ConnectedComponent).filter
        fun C => cA G M C = cB G M C + 1) ≤
        ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
          (fun C => cA G M C = cB G M C + 1), compWt (G := G) (M := M) C := by
      rw [mul_comm, ← smul_eq_mul, ← sum_const]
      exact sum_le_sum fun C hC => two_le_compWt hmax.1 (mem_filter.1 hC).2 hmax hG
    have h2 := sum_filter_add_sum_filter_not (univ : Finset (aux G M).ConnectedComponent)
      (fun C => cA G M C = cB G M C + 1) (compWt (G := G) (M := M))
    rw [sum_compWt] at h2
    have h3 := sum_wt_le (G := G) (M := M)
    omega

/-- **Lemma 1.2** (internal form): `|E(G) \ M| ≤ |F_c| + |F_nc|`. -/
theorem card_Lt_le (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G) :
    #(Lt G M) ≤ #(Rt G) + #(Nc G) := by
  obtain ⟨h1, h2, h3⟩ := main_chain hmax hG
  have h4 : ∑ C, ((cA G M C : ℤ) - cB G M C) ≤
      #((univ : Finset (aux G M).ConnectedComponent).filter fun C => cA G M C = cB G M C + 1) := by
    calc ∑ C, ((cA G M C : ℤ) - cB G M C)
        ≤ ∑ C, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) := sum_le_sum fun C _ => h2 C
      _ = _ := by rw [sum_boole]
  omega

/-- **Corollary 2.14.** In the equality case no component is right-lopsided and no balanced
component has a switch exit. -/
theorem eq_case_conditions (hmax : IsMaximalEdgeMatching G M) (hG : IsCritical G)
    (heq : #(Lt G M) = #(Rt G) + #(Nc G)) :
    (∀ C, cB G M C ≤ cA G M C) ∧
    (∀ C, cA G M C = cB G M C → ∀ p ∈ exits G M, compOf G M p ≠ C) := by
  obtain ⟨h1, h2, h3⟩ := main_chain hmax hG
  set L := (univ : Finset (aux G M).ConnectedComponent).filter fun C => cA G M C = cB G M C + 1
  have hsum : ∑ C, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) = #L := by rw [sum_boole]
  refine ⟨fun C0 => ?_, fun C0 hC0 p hp hpC => ?_⟩
  · by_contra hlt
    push Not at hlt
    have h4 : ∑ C, ((cA G M C : ℤ) - cB G M C) ≤
        ∑ C, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) - 1 := by
      rw [← sum_erase_add _ _ (mem_univ C0), ← sum_erase_add _ _ (mem_univ C0)]
      have : ∑ C ∈ univ.erase C0, ((cA G M C : ℤ) - cB G M C) ≤
          ∑ C ∈ univ.erase C0, (if cA G M C = cB G M C + 1 then (1 : ℤ) else 0) :=
        sum_le_sum fun C _ => h2 C
      have hC0 : ¬ cA G M C0 = cB G M C0 + 1 := by omega
      simp only [hC0, if_false]
      omega
    have := h3
    have h5 : 0 ≤ ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun C => ¬ cA G M C = cB G M C + 1), (compWt (G := G) (M := M) C : ℤ) :=
      sum_nonneg fun _ _ => by positivity
    omega
  · have hC0L : C0 ∉ L := by simp [L]; omega
    have h4 : 1 ≤ ∑ C ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun C => ¬ cA G M C = cB G M C + 1), compWt (G := G) (M := M) C :=
      (one_le_compWt hp hpC).trans
        (single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨mem_univ _, by omega⟩))
    have h5 : ∑ C, ((cA G M C : ℤ) - cB G M C) ≤ #L := by
      rw [← hsum]; exact sum_le_sum fun C _ => h2 C
    omega

end

end MurtySimon
