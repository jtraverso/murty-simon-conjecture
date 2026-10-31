/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MurtySimon.Defs

/-!
# Critical non-edges and the auxiliary graph

A non-edge `xy` is *critical* if `x` and `y` have exactly one common neighbour `u`; then
`(x, u, y)` is its *critical 2-path* (`IsMid G x y u`). Lemma 2.2 of Das–Fox: in a
diameter-2-critical graph every edge in a triangle lies on some critical 2-path
(`exists_onPath_of_triangle`).

Given a set `M` of edges, the auxiliary bipartite graph `𝓘'` of the paper has the edges of `G`
not in `M` on one side and the critical non-edges on the other, an edge `e` being joined to a
critical non-edge `f` when `e` lies on the critical 2-path of `f`. We build it on the whole of
`Sym2 V` (`aux G M`); every other element of `Sym2 V` is isolated. For `M = ∅` it is the graph
`𝓘` of the paper.
-/

@[expose] public section

namespace MurtySimon

open Finset SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `u` is the unique common neighbour of the distinct nonadjacent vertices `x` and `y`: the
non-edge `xy` is critical with critical 2-path `(x, u, y)`. -/
def IsMid (x y u : V) : Prop :=
  x ≠ y ∧ ¬ G.Adj x y ∧ G.Adj x u ∧ G.Adj u y ∧ ∀ w, G.Adj x w → G.Adj w y → w = u

/-- A critical non-edge. -/
def IsCrit (f : Sym2 V) : Prop := ∃ x y u, f = s(x, y) ∧ IsMid G x y u

/-- `e` is an edge on the critical 2-path of the critical non-edge `f`. -/
def OnPath (e f : Sym2 V) : Prop := ∃ x y u, f = s(x, y) ∧ IsMid G x y u ∧ e = s(x, u)

/-- The auxiliary bipartite graph `𝓘'` of the paper (the graph `𝓘` for `M = ∅`), built on the
whole of `Sym2 V`. -/
def aux (M : Finset (Sym2 V)) : SimpleGraph (Sym2 V) :=
  SimpleGraph.fromRel fun e f => e ∉ M ∧ OnPath G e f

variable {G}

lemma IsMid.symm {x y u : V} (h : IsMid G x y u) : IsMid G y x u := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1.symm, fun h => h2 h.symm, h4.symm, h3.symm, fun w hw1 hw2 => h5 w hw2.symm hw1.symm⟩

lemma IsMid.unique {x y u u' : V} (h : IsMid G x y u) (h' : IsMid G x y u') : u' = u :=
  h.2.2.2.2 u' h'.2.2.1 h'.2.2.2.1

lemma IsMid.ne_left {x y u : V} (h : IsMid G x y u) : u ≠ x := h.2.2.1.ne'

lemma IsMid.ne_right {x y u : V} (h : IsMid G x y u) : u ≠ y := h.2.2.2.1.ne

lemma IsMid.unique_of_eq {x y x' y' u u' : V} (hf : s(x, y) = s(x', y')) (h : IsMid G x y u)
    (h' : IsMid G x' y' u') : u' = u := by
  rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h.unique h'
  · exact h.symm.unique h'

lemma IsMid.isCrit {x y u : V} (h : IsMid G x y u) : IsCrit G s(x, y) := ⟨x, y, u, rfl, h⟩

lemma IsCrit.not_mem_edgeSet {f : Sym2 V} (h : IsCrit G f) : f ∉ G.edgeSet := by
  obtain ⟨x, y, u, rfl, hm⟩ := h
  exact hm.2.1

lemma IsCrit.not_isDiag {f : Sym2 V} (h : IsCrit G f) : ¬ f.IsDiag := by
  obtain ⟨x, y, u, rfl, hm⟩ := h
  simpa using hm.1

lemma OnPath.mem_edgeSet {e f : Sym2 V} (h : OnPath G e f) : e ∈ G.edgeSet := by
  obtain ⟨x, y, u, -, hm, rfl⟩ := h
  exact hm.2.2.1

lemma OnPath.isCrit {e f : Sym2 V} (h : OnPath G e f) : IsCrit G f := by
  obtain ⟨x, y, u, rfl, hm, -⟩ := h
  exact hm.isCrit

lemma OnPath.ne {e f : Sym2 V} (h : OnPath G e f) : e ≠ f := by
  rintro rfl
  exact h.isCrit.not_mem_edgeSet h.mem_edgeSet

/-- The edges on the critical 2-path `(x, u, y)` are `xu` and `uy`. -/
lemma onPath_iff {x y u : V} (h : IsMid G x y u) {e : Sym2 V} :
    OnPath G e s(x, y) ↔ e = s(x, u) ∨ e = s(u, y) := by
  constructor
  · rintro ⟨x', y', u', hf, hm, rfl⟩
    have hu : u' = u := h.unique_of_eq hf hm
    subst hu
    rcases Sym2.eq_iff.1 hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr Sym2.eq_swap
  · rintro (rfl | rfl)
    · exact ⟨x, y, u, rfl, h, rfl⟩
    · exact ⟨y, x, u, Sym2.eq_swap, h.symm, Sym2.eq_swap⟩

lemma aux_adj {M : Finset (Sym2 V)} {e f : Sym2 V} :
    (aux G M).Adj e f ↔ (e ∉ M ∧ OnPath G e f) ∨ (f ∉ M ∧ OnPath G f e) := by
  rw [aux, fromRel_adj]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h <;> exact h.2.ne rfl

lemma aux_mono {M N : Finset (Sym2 V)} (h : N ⊆ M) : aux G M ≤ aux G N := by
  intro e f hef
  rw [aux_adj] at hef ⊢
  rcases hef with hef | hef
  · exact Or.inl ⟨fun hN => hef.1 (h hN), hef.2⟩
  · exact Or.inr ⟨fun hN => hef.1 (h hN), hef.2⟩

/-- **Lemma 2.2.** In a diameter-2-critical graph, every edge in a triangle lies on some critical
2-path. -/
lemma exists_onPath_of_triangle (hG : IsCritical G) {x y w : V} (hxy : G.Adj x y)
    (hxw : G.Adj x w) (hwy : G.Adj w y) : ∃ f, OnPath G s(x, y) f := by
  have hnd := hG.2 s(x, y) hxy
  have hwx : w ≠ x := hxw.ne'
  have hwy' : w ≠ y := hwy.ne
  -- an edge through `w` is not `xy`
  have hw : ∀ p, s(p, w) ≠ s(x, y) := by
    intro p hp
    have : w ∈ s(x, y) := hp ▸ Sym2.mem_mk_right p w
    rcases Sym2.mem_iff.1 this with h | h
    · exact hwx h
    · exact hwy' h
  have hw' : ∀ p, s(w, p) ≠ s(x, y) := fun p => by rw [Sym2.eq_swap]; exact hw p
  have hdel : ∀ p q, (G.deleteEdges {s(x, y)}).Adj p q ↔ G.Adj p q ∧ s(p, q) ≠ s(x, y) := by
    intro p q; simp
  unfold DiamLeTwo at hnd
  push Not at hnd
  obtain ⟨a, b, hab, hnab, hcom⟩ := hnd
  simp only [hdel, not_and, not_not] at hnab hcom
  by_cases hadj : G.Adj a b
  · have he : s(a, b) = s(x, y) := hnab hadj
    exfalso
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hw' b (hcom w ⟨hxw, hw a⟩ hwy)
    · exact hw' b (hcom w ⟨hwy.symm, hw a⟩ hxw.symm)
  · obtain hab' | ⟨u, hau, hub⟩ := hG.1 a b hab
    · exact absurd hab' hadj
    -- every common neighbour uses the edge `xy`
    have huse : ∀ z, G.Adj a z → G.Adj z b → s(a, z) = s(x, y) ∨ s(z, b) = s(x, y) := by
      intro z hz1 hz2
      by_contra hcon
      push Not at hcon
      exact hcon.2 (hcom z ⟨hz1, hcon.1⟩ hz2)
    have huniq : ∀ z, G.Adj a z → G.Adj z b → z = u := by
      intro z hz1 hz2
      rcases huse z hz1 hz2 with h1 | h1 <;> rcases huse u hau hub with h2 | h2
      · exact Sym2.congr_right.1 (h1.trans h2.symm)
      · rcases Sym2.eq_iff.1 (h1.trans h2.symm) with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd (h ▸ hau) (G.loopless.irrefl u)
        · exact h
      · rcases Sym2.eq_iff.1 (h1.trans h2.symm) with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h.symm (hz1.ne)
        · exact h
      · exact Sym2.congr_left.1 (h1.trans h2.symm)
    have hm : IsMid G a b u := ⟨hab, hadj, hau, hub, huniq⟩
    refine ⟨s(a, b), (onPath_iff hm).2 ?_⟩
    rcases huse u hau hub with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

end MurtySimon
