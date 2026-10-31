# The Murty–Simon conjecture in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the proof of the Murty–Simon conjecture by Sanjana Das and
Jacob Fox, *A proof of the Murty–Simon conjecture on diameter-2-critical graphs*,
[arXiv:2610.39032](https://arxiv.org/abs/2610.39032) (2026).

A graph is *diameter-2-critical* if its diameter is `2` and deleting any edge increases the
diameter. The Murty–Simon conjecture (Plesník 1975; Murty and Simon) states that such a graph on
`n` vertices has at most `⌊n²/4⌋` edges, with equality only for the balanced complete bipartite
graph. Füredi proved it in 1992 for `n` larger than a tower of 2's; Das and Fox prove it for every
`n`.

| Lean (namespace `MurtySimonConjecture`) | Paper | Statement |
|---|---|---|
| `murty_simon` | Theorem 1.1 | A diameter-2-critical graph on `n` vertices has at most `⌊n²/4⌋` edges. |
| `murty_simon_equality` | Theorem 1.1 | A diameter-2-critical graph with `⌊n²/4⌋` edges is isomorphic to `K_{⌈n/2⌉,⌊n/2⌋}`. |
| `murty_simon_sharp` | Theorem 1.1 | For `n ≥ 3`, `K_{⌈n/2⌉,⌊n/2⌋}` is diameter-2-critical with `⌊n²/4⌋` edges. |
| `lemma_1_2` | Lemma 1.2 | For every maximal matching `M`, `|E(G) \ M| ≤ |non-edges of G|`. |
| `lemma_1_3` | Lemma 1.3 | Equality in Lemma 1.2 for every maximal matching forces `G` to be triangle-free. |

## Files

- [`Challenge.lean`](Challenge.lean): the definitions and the five statements; it imports only
  Mathlib. Diameter-2-criticality uses Mathlib's extended diameter `SimpleGraph.ediam`; a matching
  is a finite set of edges of `G` with no common vertex, maximal if no edge of `G` can be added.
- [`Solution.lean`](Solution.lean): the same definitions and the five theorems, proved from the
  library.
- [`MurtySimon/`](MurtySimon): the proof.
  - `Defs.lean`: the definitions and the equivalence of `ediam ≤ 2` with "adjacent or with a
    common neighbour";
  - `Basic.lean`: critical non-edges, the auxiliary graph `𝓘'`, Lemma 2.2;
  - `Components.lean`: Lemma 2.4 (counting in the components of `𝓘'`);
  - `Bound.lean`: switch exits, Lemmas 2.7, 2.9–2.11, Corollary 2.12, Lemma 1.2, Corollary 2.14;
  - `Equality.lean`: Lemmas 3.2, 3.3 and 1.3;
  - `Main.lean`: Theorem 1.1, with Mantel's theorem from Mathlib's Turán theorem, and sharpness.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## How the proof goes

Fix a maximal matching `M`. A non-edge is *critical* if its endpoints have exactly one common
neighbour. The auxiliary bipartite graph `𝓘'` joins each edge outside `M` to the critical non-edges
whose unique 2-path uses it. Every critical non-edge has degree at most two, so each component has
at most one more edge-vertex than non-edge-vertex, and the *left-lopsided* components are trees
whose leaves are edges. Each such component has a safe *switch exit* or two switch exits
(noncritical non-edges obtained by swapping an endpoint with its partner in `M`), while every
noncritical non-edge serves at most twice. This gives `|E \ M| ≤ |non-edges|`, hence
`2|E| ≤ binom(n,2) + ⌊n/2⌋ = 2⌊n²/4⌋`. In the equality case the same counting, applied to
suitably chosen maximal matchings, shows that `G` has no critical non-edge unless it is a star,
so `G` is triangle-free and Mantel's theorem gives `K_{⌈n/2⌉,⌊n/2⌋}`.

In the formalization the auxiliary graph lives on the whole of `Sym2 V`, and the bipartite
multigraph `𝓙` of the paper is replaced by a weighting of the switch exits (weight `2` for a safe
exit, `1` otherwise), which gives the same double counting.

## Checks

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for the five
theorems; the elaborated statements and definitions of `Challenge.lean` and `Solution.lean` are
identical (`pp.all`).

The Lean development was written by Claude Opus 5.5 (Anthropic) in Claude Code under the
author's direction; see `formalization.yaml`. The article's authors were not involved.
