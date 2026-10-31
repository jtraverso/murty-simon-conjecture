/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MurtySimon.Equality

/-!
# The Murty–Simon conjecture (Theorem 1.1 of Das–Fox)

* `card_edgeFinset_le`: an `n`-vertex diameter-2-critical graph has at most `⌊n²/4⌋` edges;
* `nonempty_iso_completeBipartiteGraph`: equality holds only for `K_{⌈n/2⌉,⌊n/2⌋}`;
* `completeBipartiteGraph_isDiameterTwoCritical`, `card_edgeSet_completeBipartiteGraph`: for
  `n ≥ 3` the graph `K_{⌈n/2⌉,⌊n/2⌋}` is diameter-2-critical with `⌊n²/4⌋` edges;
* `lemma_1_2`, `lemma_1_3`: Lemmas 1.2 and 1.3 of the paper, in the notation of the statement.

From Lemma 1.2, `2|E(G)| ≤ binom(n, 2) + |M| ≤ binom(n, 2) + ⌊n/2⌋ = 2⌊n²/4⌋` for a maximal
matching `M`. In the equality case Lemma 1.3 shows that `G` is triangle-free, and Mantel's theorem
with its equality case (Turán's theorem in Mathlib) gives `G ≅ K_{⌈n/2⌉,⌊n/2⌋}`.
-/

@[expose] public section

namespace MurtySimon

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Counting -/

lemma two_mul_card_le {M : Finset (Sym2 V)} (hM : IsEdgeMatching G M) :
    2 * #M ≤ Fintype.card V := by
  classical
  have hcard : ∀ e ∈ M, #(univ.filter (· ∈ e)) = 2 := by
    intro e he
    have hne := hM.1 e he
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at hne
      have : univ.filter (· ∈ s(a, b)) = {a, b} := by
        ext v; simp [Sym2.mem_iff]
      rw [this, card_pair hne.ne]
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint fun e => univ.filter (· ∈ e) := by
    intro e he f hf hef
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    exact hM.2 e he f hf hef v (mem_filter.1 hv).2 (mem_filter.1 hv').2
  calc 2 * #M = ∑ e ∈ M, #(univ.filter (· ∈ e)) := by
        rw [sum_congr rfl hcard, sum_const, smul_eq_mul, mul_comm]
    _ = #(M.biUnion fun e => univ.filter (· ∈ e)) := (card_biUnion hdisj).symm
    _ ≤ #(univ : Finset V) := card_le_univ _
    _ = Fintype.card V := card_univ

lemma choose_two_add_half (n : ℕ) : n.choose 2 + n / 2 = 2 * (n ^ 2 / 4) := by
  rw [Nat.choose_two_right]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * k * (2 * k - 1) = 2 * (k * (2 * k - 1)) by ring,
      show (2 * k) ^ 2 = 4 * k ^ 2 by ring, Nat.mul_div_cancel_left _ (by norm_num),
      Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
    rcases k with _ | k
    · simp
    · rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]; ring
  · rw [show 2 * k + 1 - 1 = 2 * k by omega,
      show (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) by ring,
      show (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 by ring, Nat.mul_div_cancel_left _ (by norm_num),
      show (2 * k + 1) / 2 = k by omega, show (4 * (k ^ 2 + k) + 1) / 4 = k ^ 2 + k by omega]
    ring

variable [DecidableRel G.Adj]

lemma card_sdiff_eq_card_Lt (M : Finset (Sym2 V)) : #(G.edgeFinset \ M) = #(Lt G M) := by
  congr 1; ext e; simp [mem_Lt]

lemma card_compl_eq (G : SimpleGraph V) [DecidableRel G.Adj] :
    #Gᶜ.edgeFinset = #(Rt G) + #(Nc G) := by
  classical
  have hdisj : Disjoint (Rt G) (Nc G) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Nc, mem_filter] at hf'
    exact hf'.2.2 (mem_Rt.1 hf)
  rw [← card_union_of_disjoint hdisj]
  congr 1
  ext f
  simp only [mem_edgeFinset, mem_union, mem_Rt, Nc, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    by_cases hc : IsCrit G f
    · exact Or.inl hc
    · exact Or.inr ⟨h, hc⟩
  · rintro (h | h)
    · obtain ⟨x, y, u, rfl, hm⟩ := h
      rw [mem_edgeSet, compl_adj]; exact ⟨hm.1, hm.2.1⟩
    · exact h.1

lemma card_add_card_compl (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset + #Gᶜ.edgeFinset = (Fintype.card V).choose 2 := by
  rw [← card_edgeFinset_top_eq_card_choose_two, ← card_union_of_disjoint]
  · congr 1
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [mem_union, mem_edgeFinset, mem_edgeSet, compl_adj, top_adj]
      constructor
      · rintro (h | h)
        · exact h.ne
        · exact h.1
      · intro h
        by_cases hab : G.Adj a b
        · exact Or.inl hab
        · exact Or.inr ⟨h, hab⟩
  · rw [Finset.disjoint_left]
    intro e he he'
    rw [mem_edgeFinset] at he he'
    induction e using Sym2.ind with
    | h a b =>
      rw [mem_edgeSet] at he he'
      exact (compl_adj G a b).1 he' |>.2 he

/-! ### Lemmas 1.2 and 1.3 -/

/-- **Lemma 1.2.** For a diameter-2-critical graph and a maximal matching `M`,
`|E(G) \ M| ≤ |non-edges of G|`. -/
theorem lemma_1_2 (hG : IsDiameterTwoCritical G) {M : Finset (Sym2 V)}
    (hM : IsMaximalEdgeMatching G M) : #(G.edgeFinset \ M) ≤ #Gᶜ.edgeFinset := by
  rw [card_sdiff_eq_card_Lt, card_compl_eq]
  exact card_Lt_le hM hG.isCritical

/-- **Lemma 1.3.** A diameter-2-critical graph with equality in Lemma 1.2 for every maximal
matching is triangle-free. -/
theorem lemma_1_3 (hG : IsDiameterTwoCritical G)
    (heq : ∀ M, IsMaximalEdgeMatching G M → #(G.edgeFinset \ M) = #Gᶜ.edgeFinset) :
    G.CliqueFree 3 := by
  refine cliqueFree_of_eqCase hG.isCritical fun M hM => ?_
  rw [← card_sdiff_eq_card_Lt, ← card_compl_eq]
  exact heq M hM

/-! ### Theorem 1.1 -/

lemma two_mul_card_le_aux (hG : IsDiameterTwoCritical G) {M : Finset (Sym2 V)}
    (hM : IsMaximalEdgeMatching G M) :
    2 * #G.edgeFinset ≤ (Fintype.card V).choose 2 + #M := by
  have h1 := lemma_1_2 hG hM
  have h2 := card_add_card_compl G
  have hsub : M ⊆ G.edgeFinset := fun e he => mem_edgeFinset.2 (hM.1.1 e he)
  have h3 := card_sdiff_add_card_inter G.edgeFinset M
  rw [inter_eq_right.2 hsub] at h3
  omega

/-- **Theorem 1.1**, the bound: an `n`-vertex diameter-2-critical graph has at most `⌊n²/4⌋`
edges. -/
theorem card_edgeFinset_le (hG : IsDiameterTwoCritical G) :
    #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by
  obtain ⟨M, -, hM⟩ := exists_maximal_extension (G := G) (N := ∅) ⟨by simp, by simp⟩
  have h1 := two_mul_card_le_aux hG hM
  have h2 := two_mul_card_le hM.1
  have h3 := choose_two_add_half (Fintype.card V)
  omega

/-- The isomorphism between the Turán graph `T(n, 2)` and `K_{⌈n/2⌉,⌊n/2⌋}`. -/
def turanEquiv (n : ℕ) : Fin n ≃ Fin ((n + 1) / 2) ⊕ Fin (n / 2) where
  toFun i := if h : i.val % 2 = 0 then Sum.inl ⟨i.val / 2, by have := i.isLt; omega⟩
    else Sum.inr ⟨i.val / 2, by have := i.isLt; omega⟩
  invFun
    | Sum.inl j => ⟨2 * j.val, by have := j.isLt; omega⟩
    | Sum.inr j => ⟨2 * j.val + 1, by have := j.isLt; omega⟩
  left_inv i := by
    by_cases h : i.val % 2 = 0
    · simp only [dif_pos h]; apply Fin.ext; dsimp only; omega
    · simp only [dif_neg h]; apply Fin.ext; dsimp only; omega
  right_inv s := by
    rcases s with j | j
    · dsimp only
      rw [dif_pos (by omega)]
      congr 1; apply Fin.ext; dsimp only; omega
    · dsimp only
      rw [dif_neg (by omega)]
      congr 1; apply Fin.ext; dsimp only; omega

/-- `T(n, 2) ≅ K_{⌈n/2⌉,⌊n/2⌋}`. -/
def turanIso (n : ℕ) :
    turanGraph n 2 ≃g completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2)) where
  toEquiv := turanEquiv n
  map_rel_iff' {a b} := by
    rw [turanGraph_adj]
    simp only [turanEquiv, completeBipartiteGraph_adj]
    by_cases ha : a.val % 2 = 0 <;> by_cases hb : b.val % 2 = 0 <;> simp [ha, hb]
    all_goals omega

/-- **Theorem 1.1**, the equality case: an `n`-vertex diameter-2-critical graph with `⌊n²/4⌋`
edges is isomorphic to `K_{⌈n/2⌉,⌊n/2⌋}`. -/
theorem nonempty_iso_completeBipartiteGraph (hG : IsDiameterTwoCritical G)
    (hE : #G.edgeFinset = Fintype.card V ^ 2 / 4) :
    Nonempty (G ≃g completeBipartiteGraph (Fin ((Fintype.card V + 1) / 2))
      (Fin (Fintype.card V / 2))) := by
  have hcf : G.CliqueFree 3 := by
    apply lemma_1_3 hG
    intro M hM
    have h1 := lemma_1_2 hG hM
    have h2 := card_add_card_compl G
    have h3 := two_mul_card_le hM.1
    have h4 := choose_two_add_half (Fintype.card V)
    have hsub : M ⊆ G.edgeFinset := fun e he => mem_edgeFinset.2 (hM.1.1 e he)
    have h5 := card_sdiff_add_card_inter G.edgeFinset M
    rw [inter_eq_right.2 hsub] at h5
    omega
  have hT : G.IsTuranMaximal 2 := by
    refine ⟨hcf, fun H _ hH => ?_⟩
    rw [hE, ← turanNumber_two]
    exact hH.card_edgeFinset_le
  obtain ⟨e⟩ := (isTuranMaximal_iff_nonempty_iso_turanGraph (by norm_num)).1 hT
  exact ⟨e.trans (turanIso _)⟩

/-! ### Sharpness -/

lemma two_le_edist {W : Type*} {H : SimpleGraph W} {u v : W} (hne : u ≠ v) (hn : ¬ H.Adj u v) :
    2 ≤ H.edist u v := by
  by_contra h
  push Not at h
  have hne' : H.edist u v ≠ ⊤ := ne_top_of_lt h
  obtain ⟨p, hp⟩ := (reachable_of_edist_ne_top hne').exists_walk_length_eq_edist
  have hlen : p.length < 2 := by rw [← hp] at h; exact_mod_cast h
  rcases p with _ | ⟨h1, _ | ⟨h2, p⟩⟩
  · exact hne rfl
  · exact hn h1
  · simp at hlen

lemma completeBipartiteGraph_no_common {A B : Type*} {p q w : A ⊕ B}
    (hpq : (completeBipartiteGraph A B).Adj p q) (hpw : (completeBipartiteGraph A B).Adj p w)
    (hwq : (completeBipartiteGraph A B).Adj w q) : False := by
  rcases p with p | p <;> rcases q with q | q <;> rcases w with w | w <;> simp_all

/-- For `n ≥ 3`, `K_{⌈n/2⌉,⌊n/2⌋}` is diameter-2-critical. -/
theorem completeBipartiteGraph_isDiameterTwoCritical {n : ℕ} (hn : 3 ≤ n) :
    IsDiameterTwoCritical (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))) := by
  set H := completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))
  have hd : DiamLeTwo H := by
    intro p q hpq
    rcases p with p | p <;> rcases q with q | q
    · exact Or.inr ⟨Sum.inr ⟨0, by omega⟩, by simp [H], by simp [H]⟩
    · exact Or.inl (by simp [H])
    · exact Or.inl (by simp [H])
    · exact Or.inr ⟨Sum.inl ⟨0, by omega⟩, by simp [H], by simp [H]⟩
  refine ⟨le_antisymm ((ediam_le_two_iff H).2 hd) ?_, fun e he => ?_⟩
  · have h01 : (Sum.inl ⟨0, by omega⟩ : Fin ((n + 1) / 2) ⊕ Fin (n / 2)) ≠
        Sum.inl ⟨1, by omega⟩ := by simp
    exact (two_le_edist h01 (by simp [H])).trans (edist_le_ediam)
  · rw [← not_le, ediam_le_two_iff]
    intro hd'
    induction e using Sym2.ind with
    | h p q =>
      rw [mem_edgeSet] at he
      rcases hd' p q he.ne with h | ⟨w, h1, h2⟩
      · simp at h
      · simp only [deleteEdges_adj] at h1 h2
        exact completeBipartiteGraph_no_common he h1.1 h2.1

/-- For every `n`, `K_{⌈n/2⌉,⌊n/2⌋}` has `⌊n²/4⌋` edges. -/
theorem card_edgeSet_completeBipartiteGraph (n : ℕ) :
    Nat.card (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))).edgeSet = n ^ 2 / 4 := by
  rw [← Nat.card_congr (turanIso n).mapEdgeSet, Nat.card_eq_fintype_card, ← edgeFinset_card,
    ← turanNumber_two]

end MurtySimon
