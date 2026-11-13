module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SplicedLinkage
import GraphMinor.GM06.Section5SpliceWinding

/-!
# The terminal linkage

This is Lemma 16 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`), for `k ≥ 2`. Suppose
that for every `i` we have a path `Qᵢ` of `G` from `sᵢ` to a vertex `uᵢ ≠ sᵢ₊₁` of `Pᵢ₊₁`, lying in
the strip `Σᵢ` apart from its ends, and meeting `Pᵢ₊₁` only at `uᵢ`. These are the properties that
Lemma 15 gives. Then the paths `Qᵢ · Pᵢ₊₁[uᵢ, tᵢ₊₁]` form a linkage whose winding is `θ + 1/k`.

Both halves are proved in the files on Section 5: `exists_spliced_linkage_of_strip_paths` builds the
linkage, and `theta_next_of_spliced_linkage` computes its winding. This file puts them together.
For `k = 1` the same statement is `isThetaFeasible_successor_of_single_path_right_contact`.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- **Lemma 16**, for `k ≥ 2`. Paths `Qᵢ` with the properties of Lemma 15 give a linkage with
winding `θ + 1/k`. -/
theorem isThetaFeasible_next_of_strip_paths
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ)
    (hpaths : ∀ i, ∃ t ∈ (L.pathDrawing (finSuccCycle i)).V,
      t ≠ cylinderM1Point k (finSuccCycle i) ∧ ∃ Q : Drawing ClosedCylinder,
        IsSubpathOf G Q (cylinderM1Point k i) t ∧
        Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, t} ∧
        Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {t}) :
    IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by
  obtain ⟨L', hend, hconf, -⟩ := exists_spliced_linkage_of_strip_paths L hG hθ hpaths
  exact ⟨L', theta_next_of_spliced_linkage L L' hG hk hθ hend hconf⟩

end GraphMinor.GM06
