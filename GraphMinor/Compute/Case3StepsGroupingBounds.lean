module

public import GraphMinor.Compute.Case3StepsComponentBounds

/-!
# Size bounds for routing the compact compass

Restricting a multigraph through an injective vertex numbering cannot
increase its edge count. The combined routing cost is bounded by the same
case (iii) size parameter as the core computation. These bounds also cover
the full multiplicity words copied into member encodings.
-/

public section

namespace GraphMinor.Compute

open scoped BigOperators

/-- An injective vertex restriction cannot increase the total multiplicity. -/
theorem case3NumEdges_induce_le {m n : ℕ} (D : MultiDigraph n) (e : Fin m ↪ Fin n) :
    (D.induce e).numEdges ≤ D.numEdges := by
  have hsum (f : Fin n → ℕ) : (∑ u : Fin m, f (e u)) ≤ ∑ v : Fin n, f v := by
    calc
      _ = ∑ v ∈ Finset.univ.image e, f v :=
        (Finset.sum_image (fun i _ j _ hij => e.injective hij)).symm
      _ ≤ ∑ v : Fin n, f v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  change (∑ u : Fin m, ∑ v : Fin m, D.edgeMult (e u) (e v)) ≤
    ∑ u : Fin n, ∑ v : Fin n, D.edgeMult u v
  calc
    _ ≤ ∑ u : Fin m, ∑ v : Fin n, D.edgeMult (e u) v :=
      Finset.sum_le_sum (fun u _ => hsum (D.edgeMult (e u)))
    _ ≤ _ := hsum (fun u => ∑ v : Fin n, D.edgeMult u v)

/-- The compact compass contains at most the original graph's number of edges,
counted with their complete directed multiplicities. -/
theorem case3CompactCompass_numEdges_le {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h (G.deleteVertices X)) :
    (case3CompactCompassMultigraph (G.deleteVertices X) W).numEdges ≤ G.numEdges :=
  (case3NumEdges_induce_le (G.deleteVertices X) (compassEmb W).toEmbedding).trans
    (G.numEdges_deleteVertices_le X)

/-- All selected-member routing passes fit the case (iii) time parameter. -/
theorem case3Grouping_cost_le {k m a n e : ℕ} (hk : k ≤ n) (hm : m ≤ a) (ha : a ≤ e) :
    k * k + 11 * k + 42 * m + 43 * a + (k + m) * (77 * k + 141) + 58 ≤
      1000 * ((n + 1) * (e + n + 1)) := by
  have hkk := Nat.mul_le_mul hk hk
  have hme := hm.trans ha
  have hkm := Nat.mul_le_mul hk hme
  nlinarith [Nat.zero_le (n * e), Nat.zero_le (n * n)]

end GraphMinor.Compute
