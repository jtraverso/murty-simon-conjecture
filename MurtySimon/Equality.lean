/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MurtySimon.Bound

/-!
# The equality case (Section 3 of Das–Fox)

`G` is an *equality case* (`EqCase G`) if `|E(G) \ M| = |non-edges|` for every maximal matching
`M`. Every matching extends to a maximal one (`exists_maximal_extension`). The components of
`𝓘' = aux G M` refine those of `𝓘 = aux G ∅` (`emb`), and the pieces of a component `C` of `𝓘`
have in total the left vertices of `C` outside `M` and all right vertices of `C` (`sum_pieces`).

* Lemma 3.2 (`lemma_3_2`): in an equality case every component of `𝓘` meeting `E ∪ F_c` is
  left-lopsided, and every matching uses at most one left vertex of it.
* Lemma 3.3 (`isStar_of_lemma_3_3`): if a left-lopsided component of `𝓘` has a right vertex,
  then `G` is a star.
* Lemma 1.3 (`cliqueFree_of_eqCase`): an equality case is triangle-free.
-/

@[expose] public section

namespace MurtySimon

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable section

/-! ### Extending matchings -/

lemma exists_maximal_extension {N : Finset (Sym2 V)} (hN : IsEdgeMatching G N) :
    ∃ M, N ⊆ M ∧ IsMaximalEdgeMatching G M := by
  set S := (univ : Finset (Finset (Sym2 V))).filter fun M => IsEdgeMatching G M ∧ N ⊆ M
  have hS : S.Nonempty := ⟨N, mem_filter.2 ⟨mem_univ _, hN, subset_refl _⟩⟩
  obtain ⟨M, hMS, hmax⟩ := exists_max_image S card hS
  obtain ⟨hM, hNM⟩ := (mem_filter.1 hMS).2
  refine ⟨M, hNM, hM, fun e he heM hins => ?_⟩
  have := hmax (insert e M) (mem_filter.2 ⟨mem_univ _, hins, hNM.trans (subset_insert _ _)⟩)
  rw [card_insert_of_notMem heM] at this
  omega

lemma isEdgeMatching_singleton {e : Sym2 V} (he : e ∈ G.edgeSet) : IsEdgeMatching G {e} := by
  refine ⟨fun f hf => mem_singleton.1 hf ▸ he, fun f hf g hg hfg => ?_⟩
  rw [mem_singleton.1 hf, mem_singleton.1 hg] at hfg
  exact absurd rfl hfg

lemma isEdgeMatching_pair {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : IsEdgeMatching G {s(a, b), s(c, d)} := by
  have hdisj : ∀ v ∈ s(a, b), v ∉ s(c, d) := by
    intro v hv hv'
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> rcases Sym2.mem_iff.1 hv' with h | h
    · exact hac h
    · exact had h
    · exact hbc h
    · exact hbd h
  refine ⟨fun e he => ?_, fun e he f hf hef v hve hvf => ?_⟩
  · rcases mem_insert.1 he with rfl | he
    · exact hab
    · rw [mem_singleton.1 he]; exact hcd
  · rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 hf with rfl | hf
    · exact hef rfl
    · rw [mem_singleton.1 hf] at hvf; exact hdisj v hve hvf
    · rw [mem_singleton.1 he] at hve; exact hdisj v hvf hve
    · rw [mem_singleton.1 he, mem_singleton.1 hf] at hef; exact hef rfl

/-! ### Pieces of the components of `𝓘` -/

variable (G) in
/-- The component of `𝓘 = aux G ∅` containing a component of `𝓘' = aux G M`. -/
def emb (M : Finset (Sym2 V)) : (aux G M).ConnectedComponent → (aux G ∅).ConnectedComponent :=
  ConnectedComponent.map (Hom.ofLE (aux_mono (empty_subset M)))

lemma emb_mk (M : Finset (Sym2 V)) (v : Sym2 V) :
    emb G M ((aux G M).connectedComponentMk v) = (aux G ∅).connectedComponentMk v := rfl

/-- The left vertices of a component of `𝓘`. -/
abbrev LC0 (C : (aux G ∅).ConnectedComponent) : Finset (Sym2 V) :=
  (Lt G ∅).filter fun e => (aux G ∅).connectedComponentMk e = C

lemma sum_pieces (M : Finset (Sym2 V)) (C : (aux G ∅).ConnectedComponent) :
    ∑ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter (fun D => emb G M D = C),
      ((cA G M D : ℤ) - cB G M D) = (#((LC0 C).filter (· ∉ M)) : ℤ) - cB G ∅ C := by
  set F := (univ : Finset (aux G M).ConnectedComponent).filter (fun D => emb G M D = C)
  have hA : ∑ D ∈ F, cA G M D = #((LC0 C).filter (· ∉ M)) := by
    unfold cA
    have hs : (LC0 C).filter (· ∉ M) =
        (Lt G M).filter fun e => (aux G ∅).connectedComponentMk e = C := by
      ext e; simp only [mem_filter, mem_Lt, LC0]; tauto
    rw [hs, card_eq_sum_card_fiberwise (f := (aux G M).connectedComponentMk) (t := F)]
    · refine sum_congr rfl fun D hD => ?_
      congr 1
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        rw [← emb_mk, h2]; exact (mem_filter.1 hD).2
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · intro e he
      exact mem_filter.2 ⟨mem_univ _, by rw [emb_mk]; exact (mem_filter.1 he).2⟩
  have hB : ∑ D ∈ F, cB G M D = cB G ∅ C := by
    unfold cB
    rw [card_eq_sum_card_fiberwise (f := (aux G M).connectedComponentMk) (t := F)]
    · refine sum_congr rfl fun D hD => ?_
      congr 1
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        rw [← emb_mk, h2]; exact (mem_filter.1 hD).2
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · intro e he
      exact mem_filter.2 ⟨mem_univ _, by rw [emb_mk]; exact (mem_filter.1 he).2⟩
  rw [sum_sub_distrib]
  push_cast [← hA, ← hB]
  rfl

/-! ### The equality case -/

variable (G) in
/-- `G` is an equality case: `|E(G) \ M| = |non-edges|` for every maximal matching `M`. -/
def EqCase : Prop := ∀ M, IsMaximalEdgeMatching G M → #(Lt G M) = #(Rt G) + #(Nc G)

lemma pieces_nonneg (hG : IsCritical G) (heq : EqCase G) {M : Finset (Sym2 V)}
    (hmax : IsMaximalEdgeMatching G M) (C : (aux G ∅).ConnectedComponent) :
    cB G ∅ C ≤ #((LC0 C).filter (· ∉ M)) := by
  have h := sum_pieces M C
  have hnn : 0 ≤ ∑ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter
      (fun D => emb G M D = C), ((cA G M D : ℤ) - cB G M D) := by
    apply sum_nonneg
    intro D _
    have := (eq_case_conditions hmax hG (heq M hmax)).1 D
    omega
  omega

lemma card_LC0_split (M : Finset (Sym2 V)) (C : (aux G ∅).ConnectedComponent) :
    #((LC0 C).filter (· ∉ M)) + #((LC0 C).filter (· ∈ M)) = cA G ∅ C := by
  rw [add_comm]; exact card_filter_add_card_filter_not _

/-- **Lemma 3.2.** In an equality case every component of `𝓘` with a vertex in `E ∪ F_c` is
left-lopsided, and every matching uses at most one of its left vertices. -/
theorem lemma_3_2 (hG : IsCritical G) (heq : EqCase G) (C : (aux G ∅).ConnectedComponent)
    (hC : 1 ≤ cA G ∅ C + cB G ∅ C) :
    cA G ∅ C = cB G ∅ C + 1 ∧
      ∀ N, IsEdgeMatching G N → #((LC0 C).filter (· ∈ N)) ≤ 1 := by
  have hle := (comp_count ∅ C).1
  -- for a maximal `M`, the left vertices of `C` in `M` number at most `cA - cB`
  have hmaxM : ∀ M, IsMaximalEdgeMatching G M → #((LC0 C).filter (· ∈ M)) + cB G ∅ C ≤ cA G ∅ C :=
    fun M hmax => by
      have h1 := pieces_nonneg hG heq hmax C
      have h2 := card_LC0_split M C
      omega
  have hext : ∀ N, IsEdgeMatching G N → #((LC0 C).filter (· ∈ N)) + cB G ∅ C ≤ cA G ∅ C := by
    intro N hN
    obtain ⟨M, hNM, hmax⟩ := exists_maximal_extension hN
    have h1 : (LC0 C).filter (· ∈ N) ⊆ (LC0 C).filter (· ∈ M) := fun e he =>
      mem_filter.2 ⟨(mem_filter.1 he).1, hNM (mem_filter.1 he).2⟩
    have := card_le_card h1
    have := hmaxM M hmax
    omega
  have hge : cB G ∅ C ≤ cA G ∅ C := by
    have := hext ∅ ⟨by simp, by simp⟩
    omega
  have heqA : cA G ∅ C = cB G ∅ C + 1 := by
    by_contra hne
    have hAB : cA G ∅ C = cB G ∅ C := by omega
    have hpos : 0 < #(LC0 C) := by
      have : #(LC0 C) = cA G ∅ C := rfl
      omega
    obtain ⟨e, he⟩ := card_pos.1 hpos
    have h1 := hext {e} (isEdgeMatching_singleton (mem_Lt.1 (mem_filter.1 he).1).1)
    have h2 : 1 ≤ #((LC0 C).filter (· ∈ ({e} : Finset (Sym2 V)))) :=
      card_pos.2 ⟨e, mem_filter.2 ⟨he, mem_singleton_self e⟩⟩
    omega
  refine ⟨heqA, fun N hN => ?_⟩
  have := hext N hN
  omega

/-- **Lemma 3.3.** In an equality case, if a left-lopsided component of `𝓘` has a right vertex,
then every edge of `G` contains one fixed vertex (`G` is a star). -/
theorem lemma_3_3 (hG : IsCritical G) (heq : EqCase G) (C : (aux G ∅).ConnectedComponent)
    (hC : cA G ∅ C = cB G ∅ C + 1) (hB : 1 ≤ cB G ∅ C) :
    ∃ u, ∀ a b, G.Adj a b → a = u ∨ b = u := by
  obtain ⟨ℓ, hℓL, -, -, -, hℓC, -, hℓd, -⟩ := (comp_count ∅ C).2 hC |>.2 (by omega)
  have hone := (lemma_3_2 hG heq C (by omega)).2
  obtain ⟨f, hf⟩ := card_eq_one.1 hℓd
  have hℓf : (aux G ∅).Adj ℓ f := (mem_neighborFinset _ _ _).1 (hf ▸ mem_singleton_self f)
  have hnbr : ∀ g, (aux G ∅).Adj ℓ g → g = f := fun g hg =>
    mem_singleton.1 (hf ▸ (mem_neighborFinset _ _ _).2 hg)
  have hfC : (aux G ∅).connectedComponentMk f = C :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hℓf).symm.trans hℓC
  have hon : OnPath G ℓ f := by
    rcases aux_adj_cases hℓf with h | h
    · exact h.2.2
    · exact absurd h.2.1 (not_mem_Rt_of_mem_Lt hℓL)
  obtain ⟨x, y, u, rfl, hm, hℓ⟩ : ∃ x y u, f = s(x, y) ∧ IsMid G x y u ∧ ℓ = s(u, y) := by
    obtain ⟨x, y, u, rfl, hm, rfl⟩ := hon
    exact ⟨y, x, u, Sym2.eq_swap, hm.symm, Sym2.eq_swap⟩
  subst hℓ
  have hxu : G.Adj x u := hm.2.2.1
  have huy : G.Adj u y := hm.2.2.2.1
  have hxy : x ≠ y := hm.1
  have hux : u ≠ x := hm.ne_left
  have huy' : u ≠ y := hm.ne_right
  have hxuC : (aux G ∅).connectedComponentMk s(x, u) = C := by
    rw [← hfC]
    apply ConnectedComponent.connectedComponentMk_eq_of_adj
    rw [aux_adj]
    exact Or.inl ⟨notMem_empty _, (onPath_iff hm).2 (Or.inl rfl)⟩
  have hℓLC : s(u, y) ∈ LC0 C := mem_filter.2 ⟨hℓL, hℓC⟩
  by_cases h3 : ∀ v, G.Adj x v → v = u
  · -- Case 3: `u` is adjacent to every other vertex, and every edge contains `u`
    have hall : ∀ w, w ≠ u → G.Adj u w := by
      intro w hwu
      by_cases hwx : w = x
      · rw [hwx]; exact hxu.symm
      rcases hG.1 x w (Ne.symm hwx) with h | ⟨z, hz1, hz2⟩
      · exact absurd (h3 w h) hwu
      · rw [h3 z hz1] at hz2; exact hz2
    refine ⟨u, fun a b hab => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hau, hbu⟩ := hcon
    have hnot : ∀ w, s(u, w) ≠ s(a, b) := by
      intro w h
      have : u ∈ s(a, b) := h ▸ Sym2.mem_mk_left u w
      rcases Sym2.mem_iff.1 this with h' | h'
      · exact hau h'.symm
      · exact hbu h'.symm
    apply hG.2 s(a, b) hab
    intro p q hpq
    simp only [deleteEdges_adj, Set.mem_singleton_iff]
    by_cases hp : p = u
    · subst hp
      exact Or.inl ⟨hall q (Ne.symm hpq), hnot q⟩
    by_cases hq : q = u
    · subst hq
      exact Or.inl ⟨(hall p hp).symm, by rw [Sym2.eq_swap]; exact hnot p⟩
    exact Or.inr ⟨u, ⟨(hall p hp).symm, by rw [Sym2.eq_swap]; exact hnot p⟩,
      ⟨hall q hq, hnot q⟩⟩
  push Not at h3
  obtain ⟨v, hxv, hvu⟩ := h3
  exfalso
  have hvx : v ≠ x := hxv.ne'
  have hvy : v ≠ y := fun h => hm.2.1 (h ▸ hxv)
  -- the matching `{uy, xv}` and a maximal extension
  have hN : IsEdgeMatching G {s(u, y), s(x, v)} :=
    isEdgeMatching_pair huy hxv hux (Ne.symm hvu) (Ne.symm hxy) hvy.symm
  obtain ⟨M, hNM, hmax⟩ := exists_maximal_extension hN
  have hM := hmax.1
  have huyM : s(u, y) ∈ M := hNM (mem_insert_self _ _)
  have hxvM : s(x, v) ∈ M := hNM (mem_insert_of_mem (mem_singleton_self _))
  have hmatev : mate M v = x := hM.mate_eq (Sym2.eq_swap ▸ hxvM)
  have hcovv : Covered M v := ⟨x, Sym2.eq_swap ▸ hxvM⟩
  -- exactly one left vertex of `C` lies in `M`, so every piece of `C` is balanced
  have hc : #((LC0 C).filter (· ∈ M)) = 1 := by
    have h1 := hone M hM
    have h2 : 1 ≤ #((LC0 C).filter (· ∈ M)) := card_pos.2 ⟨_, mem_filter.2 ⟨hℓLC, huyM⟩⟩
    omega
  have hbal : ∀ D, emb G M D = C → cA G M D = cB G M D := by
    have hsum := sum_pieces M C
    have hsplit := card_LC0_split M C
    have hzero : ∑ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun D => emb G M D = C), ((cA G M D : ℤ) - cB G M D) = 0 := by
      rw [hsum]; omega
    have hnn : ∀ D ∈ (univ : Finset (aux G M).ConnectedComponent).filter
        (fun D => emb G M D = C), 0 ≤ ((cA G M D : ℤ) - cB G M D) := by
      intro D _
      have := (eq_case_conditions hmax hG (heq M hmax)).1 D
      omega
    intro D hD
    have := (sum_eq_zero_iff_of_nonneg hnn).1 hzero D (mem_filter.2 ⟨mem_univ _, hD⟩)
    omega
  have hnoexit : ∀ p ∈ exits G M, emb G M (compOf G M p) ≠ C := by
    intro p hp hpC
    exact (eq_case_conditions hmax hG (heq M hmax)).2 _ (hbal _ hpC) p hp rfl
  by_cases huv : G.Adj u v
  · -- Case 2: `v` is a common neighbour of `x` and `u`
    have hnyv : ¬ G.Adj y v := fun h => hvu (hm.2.2.2.2 v hxv h.symm)
    have hnc : ¬ IsCrit G s(y, v) := by
      intro hcrit
      have hm' : IsMid G y v u := isMid_of_isCrit hcrit huy.symm huv
      have hadj : (aux G ∅).Adj s(u, y) s(y, v) := by
        rw [aux_adj]
        exact Or.inl ⟨notMem_empty _, (onPath_iff hm').2 (Or.inl Sym2.eq_swap)⟩
      have := hnbr _ hadj
      rw [Sym2.eq_swap (a := x)] at this
      exact hvx (Sym2.congr_right.1 this)
    apply hnoexit (v, y)
    · refine mem_filter.2 ⟨mem_univ _, ?_, ?_, hcovv, ?_⟩
      · rw [mem_edgeSet, compl_adj]; exact ⟨hvy, fun h => hnyv h.symm⟩
      · rw [Sym2.eq_swap]; exact hnc
      · rw [hmatev]; exact mem_union_right _ (mem_Rt.2 hm.isCrit)
    · simp only [compOf, hmatev, emb_mk]; exact hfC
  · -- Case 1: `v` is a neighbour of `x` not adjacent to `u`
    have hnc : ¬ IsCrit G s(u, v) := by
      intro hcrit
      have hm' : IsMid G u v x := isMid_of_isCrit hcrit hxu.symm hxv
      have h1 : (aux G ∅).Adj s(x, v) s(u, v) := by
        rw [aux_adj]
        exact Or.inl ⟨notMem_empty _, (onPath_iff hm').2 (Or.inr rfl)⟩
      have h2 : (aux G ∅).Adj s(x, u) s(u, v) := by
        rw [aux_adj]
        exact Or.inl ⟨notMem_empty _, (onPath_iff hm').2 (Or.inl Sym2.eq_swap)⟩
      have hxvC : (aux G ∅).connectedComponentMk s(x, v) = C := by
        rw [ConnectedComponent.connectedComponentMk_eq_of_adj h1,
          ← ConnectedComponent.connectedComponentMk_eq_of_adj h2]
        exact hxuC
      have hxvL : s(x, v) ∈ LC0 C := mem_filter.2 ⟨mem_Lt.2 ⟨hxv, notMem_empty _⟩, hxvC⟩
      have hsub : ({s(u, y), s(x, v)} : Finset (Sym2 V)) ⊆
          (LC0 C).filter (· ∈ ({s(u, y), s(x, v)} : Finset (Sym2 V))) := by
        intro e he
        rcases mem_insert.1 he with rfl | he
        · exact mem_filter.2 ⟨hℓLC, mem_insert_self _ _⟩
        · rw [mem_singleton.1 he]
          exact mem_filter.2 ⟨hxvL, mem_insert_of_mem (mem_singleton_self _)⟩
      have hne : s(u, y) ≠ s(x, v) := by
        intro h
        rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hux h1
        · exact hvu h1.symm
      have := card_le_card hsub
      rw [card_pair hne] at this
      have := hone _ hN
      omega
    have hxuM : s(x, u) ∉ M := by
      intro h
      have := hM.mate_eq h
      rw [hM.mate_eq hxvM] at this
      exact hvu this
    apply hnoexit (v, u)
    · refine mem_filter.2 ⟨mem_univ _, ?_, ?_, hcovv, ?_⟩
      · rw [mem_edgeSet, compl_adj]; exact ⟨hvu, fun h => huv h.symm⟩
      · rw [Sym2.eq_swap]; exact hnc
      · rw [hmatev]; exact mem_union_left _ (mem_Lt.2 ⟨hxu, hxuM⟩)
    · simp only [compOf, hmatev, emb_mk]; exact hxuC

/-- **Lemma 1.3.** An equality case is triangle-free. -/
theorem cliqueFree_of_eqCase (hG : IsCritical G) (heq : EqCase G) : G.CliqueFree 3 := by
  intro t ht
  rw [is3Clique_iff] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
  by_cases hR : (Rt G).Nonempty
  · obtain ⟨f, hf⟩ := hR
    set C := (aux G ∅).connectedComponentMk f
    have hB : 1 ≤ cB G ∅ C := card_pos.2 ⟨f, mem_filter.2 ⟨hf, rfl⟩⟩
    have hA := (lemma_3_2 hG heq C (by omega)).1
    obtain ⟨u, hu⟩ := lemma_3_3 hG heq C hA hB
    rcases hu a b hab with rfl | rfl <;> rcases hu a c hac with h | h <;>
      rcases hu b c hbc with h' | h'
    all_goals first
      | exact hab.ne (by simp_all)
      | exact hac.ne (by simp_all)
      | exact hbc.ne (by simp_all)
  · obtain ⟨g, hg⟩ := exists_onPath_of_triangle hG hab hac hbc.symm
    exact hR ⟨g, mem_Rt.2 hg.isCrit⟩

end

end MurtySimon
