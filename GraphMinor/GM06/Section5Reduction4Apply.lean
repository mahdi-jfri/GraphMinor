module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5OwnPathSplice
import GraphMinor.GM06.Section5ReplaceLinkagePath
import GraphMinor.GM06.Section5Reduction4Prefix
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Applying Reduction 4 at a first return to the old path

In the boundary-contact step of VI (5.1), page 129, a region path
returning to its old linkage path gives a replacement prefix. Its
only contacts with that path are its ends, and it misses all other
linkage paths. Splice it with the old tail and retain the other
members. The initial-edge exclusion proves that the old prefix is
not wholly incident with the region, so this is Reduction 4.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A region path making its first noninitial linkage contact on its
own old path produces an actual Reduction 4 in the larger-valency
case of VI (5.1), including a terminal contact. -/
theorem reduction4_applies_of_first_return_region_path
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {v : ClosedCylinder} (hv : v ∈ (L.pathDrawing i).V) (hvs : v ≠ cylinderM1Point k i)
    {Q : Drawing ClosedCylinder} (hQG : Q.IsSubdrawing G)
    (hQ : IsPathDrawing Q (cylinderM1Point k i) v)
    (hQR : Q.U ⊆ closure (cylinderRegion k G i))
    (hcontact : Q.U ∩ (L.pathDrawing i).U ⊆ {cylinderM1Point k i, v})
    (hother : ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U) :
    Section5AnyReductionApplies k G L := by
  obtain ⟨T, R, hTail, hTP, hR, hRU⟩ := exists_path_after_own_linkage_tail
    (L.isSubdrawing i).1 hQG (L.isPath i) hQ hv hvs hcontact
  have hdisj : ∀ j, j ≠ i → Disjoint R.U (L.pathDrawing j).U := by
    intro j hj
    rw [hRU]
    exact (hother j hj).union_left ((L.pairwise_disjoint hj.symm).mono_left hTP.U_subset)
  obtain ⟨L', hRi, _, hunchanged⟩ := exists_linkage_replacing_path L i hR.1 hR.2.2 hdisj
  obtain ⟨A, hA⟩ := exists_subpath_of_isPathDrawing (L.isPath i)
    (isPathDrawing_end_vertices (L.isPath i)).1 hv hvs.symm
  have hnotA := initial_subpath_not_subset_region_closure L hk hG hθ hno i hval hA
  have hvR : v ∈ closure (cylinderRegion k G i) :=
    hQR (Q.V_subset_U (isPathDrawing_end_vertices hQ).2)
  refine ⟨G, L', hG, Or.inr (Or.inr (Or.inr ?_))⟩
  refine ⟨rfl, Or.inl ⟨hk, i, v, A, T, Q, hv, hvR, hA, hTail, hnotA,
    hQG, hQG.U_subset, hQ, hQR, ?_, hunchanged⟩⟩
  rw [hRi, hRU]

end GraphMinor.GM06
