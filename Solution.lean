/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MurtySimon.Main

/-!
# The Murty–Simon conjecture on diameter-2-critical graphs

S. Das and J. Fox, *A proof of the Murty–Simon conjecture on diameter-2-critical graphs*,
arXiv:2610.39032 (2026).

A graph is *diameter-2-critical* if its diameter is `2` and deleting any edge increases the
diameter (`IsDiameterTwoCritical`, with Mathlib's extended diameter `SimpleGraph.ediam`). The
Murty–Simon conjecture, proved for all `n` by Das and Fox (Theorem 1.1), states that every
diameter-2-critical graph on `n` vertices has at most `⌊n²/4⌋` edges, with equality only for the
balanced complete bipartite graph `K_{⌈n/2⌉,⌊n/2⌋}`.

The proofs are in the library `MurtySimon` (`MurtySimon.Main`); the definitions below are
copied verbatim from `Challenge.lean`.

Statements, in the namespace `MurtySimonConjecture`:

* `murty_simon`: the bound `|E(G)| ≤ ⌊n²/4⌋` (Theorem 1.1);
* `murty_simon_equality`: a diameter-2-critical graph with `⌊n²/4⌋` edges is isomorphic to
  `K_{⌈n/2⌉,⌊n/2⌋}` (Theorem 1.1, equality case);
* `murty_simon_sharp`: for `n ≥ 3`, `K_{⌈n/2⌉,⌊n/2⌋}` is diameter-2-critical and has `⌊n²/4⌋`
  edges, so the bound is attained;
* `lemma_1_2`: for every maximal matching `M` of a diameter-2-critical graph,
  `|E(G) \ M| ≤ |non-edges of G|` (Lemma 1.2);
* `lemma_1_3`: a diameter-2-critical graph with equality in Lemma 1.2 for every maximal matching
  is triangle-free (Lemma 1.3).

A matching is a finite set of edges of `G`, no two of which share a vertex (`IsEdgeMatching`); it
is maximal if no further edge of `G` can be added (`IsMaximalEdgeMatching`). The non-edges of `G`
are the edges of its complement `Gᶜ`.
-/

@[expose] public section

namespace MurtySimonConjecture

open Finset SimpleGraph

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

/-- **The Murty–Simon conjecture** (Das–Fox, Theorem 1.1): a diameter-2-critical graph on `n`
vertices has at most `⌊n²/4⌋` edges. -/
theorem murty_simon [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G) : #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 :=
  MurtySimon.card_edgeFinset_le hG

/-- **The equality case** (Das–Fox, Theorem 1.1): a diameter-2-critical graph on `n` vertices
with `⌊n²/4⌋` edges is isomorphic to `K_{⌈n/2⌉,⌊n/2⌋}`. -/
theorem murty_simon_equality [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsDiameterTwoCritical G)
    (hE : #G.edgeFinset = Fintype.card V ^ 2 / 4) :
    Nonempty (G ≃g completeBipartiteGraph (Fin ((Fintype.card V + 1) / 2))
      (Fin (Fintype.card V / 2))) :=
  MurtySimon.nonempty_iso_completeBipartiteGraph hG hE

/-- **Sharpness**: for `n ≥ 3`, `K_{⌈n/2⌉,⌊n/2⌋}` is diameter-2-critical and has `⌊n²/4⌋`
edges. -/
theorem murty_simon_sharp (n : ℕ) (hn : 3 ≤ n) :
    IsDiameterTwoCritical (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))) ∧
      Nat.card (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))).edgeSet =
        n ^ 2 / 4 :=
  ⟨MurtySimon.completeBipartiteGraph_isDiameterTwoCritical hn,
    MurtySimon.card_edgeSet_completeBipartiteGraph n⟩

/-- **Lemma 1.2** (Das–Fox): for every maximal matching `M` of a diameter-2-critical graph,
`|E(G) \ M| ≤ |non-edges of G|`. -/
theorem lemma_1_2 [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G) (M : Finset (Sym2 V)) (hM : IsMaximalEdgeMatching G M) :
    #(G.edgeFinset \ M) ≤ #Gᶜ.edgeFinset :=
  MurtySimon.lemma_1_2 hG hM

/-- **Lemma 1.3** (Das–Fox): a diameter-2-critical graph with `|E(G) \ M| = |non-edges of G|` for
every maximal matching `M` is triangle-free. -/
theorem lemma_1_3 [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G)
    (heq : ∀ M, IsMaximalEdgeMatching G M → #(G.edgeFinset \ M) = #Gᶜ.edgeFinset) :
    G.CliqueFree 3 :=
  MurtySimon.lemma_1_3 hG heq

end MurtySimonConjecture
