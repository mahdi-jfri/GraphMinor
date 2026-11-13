module

public import GraphMinor.GM16.Defs
public import GraphMinor.Statement

/-!
# The structure theorem stated in XVI (1.3)

We state the clique-sum consequence on pages 45 and 51–52.
Nonplanarity means that the excluded finite graph has no drawing in
a sphere. The surfaces in the conclusion are precisely closed connected
surfaces in which it has no drawing, so no choice of representatives
of their homeomorphism classes is needed in the statement.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph Surface
universe u v w u' v'

/-- Graph Minors XVI, (1.3), page 46:
"Let $L$ be a nonplanar graph, and let $\Sigma_1, \dots, \Sigma_s$ be all the connected surfaces
(up to homeomorphism) in which $L$ cannot be drawn. Then there are numbers $r, d, w$ such that
every graph with no $L$-minor may be constructed by clique-sums, starting from graphs $G'$ with the
following property: $G'$ is a $(\le w)$-vertex extension of an outgrowth by $\le d$ $r$-rings of a
graph that can be drawn in one of $\Sigma_1, \dots, \Sigma_s$." -/
def GM16Theorem13Statement : Prop :=
  ∀ {α' : Type u'} {β' : Type v'} (L : Graph α' β'),
    V(L).Finite → E(L).Finite →
    (∀ (S : Type w) [TopologicalSpace S] [T2Space S],
      IsSphere S → ¬ CanBeDrawnIn S L) →
    ∃ r d w₀ : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β),
        V(G).Finite → E(G).Finite → ¬ IsIsoMinor L G →
        HasTreeStructureOver
          {H : Graph α (β ⊕ ℕ) | ∃ (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
            (H₀ : Graph α (β ⊕ ℕ)),
            IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
            IsVertexExtension w₀ H H₀ ∧ IsOutgrowthByRings S H₀ d r}
          (liftEdgeInl G)

end GraphMinor.GM16
