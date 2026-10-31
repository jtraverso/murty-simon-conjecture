/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Diameter-2-critical graphs and matchings: definitions

A graph is *diameter-2-critical* if its diameter is `2` and deleting any edge increases the
diameter. We use Mathlib's extended diameter `SimpleGraph.ediam`. For the proofs we work with the
elementary form `DiamLeTwo G`: every two distinct vertices are adjacent or have a common neighbour,
which is equivalent to `G.ediam ≤ 2` (`ediam_le_two_iff`).

A matching is a finite set of edges of `G`, no two of which share a vertex; it is maximal if no
further edge of `G` can be added.
-/

@[expose] public section

namespace MurtySimon

open SimpleGraph

variable {V : Type*}

/-- A graph is diameter-2-critical if its diameter is `2` and deleting any edge increases the
diameter. -/
def IsDiameterTwoCritical (G : SimpleGraph V) : Prop :=
  G.ediam = 2 ∧ ∀ e ∈ G.edgeSet, 2 < (G.deleteEdges {e}).ediam

/-- A matching of `G`: a finite set of edges of `G`, no two of which share a vertex. -/
def IsEdgeMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v ∈ e, v ∉ f

/-- A maximal matching of `G`: a matching to which no further edge of `G` can be added. -/
def IsMaximalEdgeMatching [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  IsEdgeMatching G M ∧ ∀ e ∈ G.edgeSet, e ∉ M → ¬ IsEdgeMatching G (insert e M)

/-- Every two distinct vertices are adjacent or have a common neighbour. -/
def DiamLeTwo (G : SimpleGraph V) : Prop :=
  ∀ u v, u ≠ v → G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

theorem diamLeTwo_iff_edist (G : SimpleGraph V) : DiamLeTwo G ↔ ∀ u v, G.edist u v ≤ 2 := by
  constructor
  · intro h u v
    by_cases huv : u = v
    · subst huv; simp
    rcases h u v huv with hadj | ⟨w, h1, h2⟩
    · calc G.edist u v ≤ (Walk.cons hadj Walk.nil).length := G.edist_le _
        _ ≤ 2 := by simp
    · calc G.edist u v ≤ (Walk.cons h1 (Walk.cons h2 Walk.nil)).length := G.edist_le _
        _ = 2 := by simp
  · intro h u v huv
    have hne : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (by decide) (h u v)
    obtain ⟨p, hp⟩ := (reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
    have hlen : p.length ≤ 2 := by
      have := h u v
      rw [← hp] at this
      exact_mod_cast this
    rcases p with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, p⟩⟩⟩
    · exact absurd rfl huv
    · exact Or.inl h1
    · exact Or.inr ⟨_, h1, h2⟩
    · simp at hlen

theorem ediam_le_two_iff (G : SimpleGraph V) : G.ediam ≤ 2 ↔ DiamLeTwo G := by
  rw [ediam_le_iff, diamLeTwo_iff_edist]

/-- The elementary form of diameter-2-criticality used in the proofs. -/
def IsCritical (G : SimpleGraph V) : Prop :=
  DiamLeTwo G ∧ ∀ e ∈ G.edgeSet, ¬ DiamLeTwo (G.deleteEdges {e})

theorem IsDiameterTwoCritical.isCritical {G : SimpleGraph V} (h : IsDiameterTwoCritical G) :
    IsCritical G := by
  refine ⟨(ediam_le_two_iff G).1 h.1.le, fun e he hd => ?_⟩
  have := (ediam_le_two_iff _).2 hd
  exact absurd (h.2 e he) (not_lt.2 this)

end MurtySimon
