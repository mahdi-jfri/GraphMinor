module

public import GraphMinor.GM06.Alg57CurrentCornerProjection
public import GraphMinor.GM06.Alg57CurrentPathCornerSteps
public import GraphMinor.GM06.Alg57ComparisonStripRegions
import GraphMinor.GM06.Section5StripDisjoint
import GraphMinor.GM06.Section5

/-!
# Actual strip labels on the two sides of the linkage rows

For Lemma 10 in VI (5.7), page 133, the comparison corner at a reverse
inner gap is exactly its strip region. Following an actual path row
keeps the following strip on its forward side and the preceding strip
on its reverse side. Distinct gap indices give distinct strip labels.
These labels and all their invariances are constructed from the
current drawing relation and its positive rows.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The actual current drawing supplies numeric strip-corner labels.
The forward and reverse ends of each linkage row have its following
and preceding strip labels, and the inner-gap labels are distinct. -/
theorem exists_strip_corner_labels (hG : IsCylinderSection5Drawing k G) :
    ∃ (H : Drawing ClosedCylinder) (_hHF : H.IsSubdrawing rep.cuffed),
      H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder ∧
      H.V = ⋃ j : Fin k, (L.pathDrawing j).V ∧
      ∃ g : ℕ → Option (cylinderSphereDrawing H).R,
        (∀ row ∈ x.rotations, ∀ r ∈ row,
          gm06LinkageCuffKeep rep.tagged.length x.linkage r = false →
            g (row.formPerm.symm r) = g r) ∧
        (∀ r ∈ x.rotations.flatten,
          g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r) ∧
        (∀ i : Fin k, ∀ d ∈ (x.linkage[i.val]'(by rw [rep.linkage.1]; exact i.isLt)),
          g d = g (2 * (rep.tagged.length + i.val) + 1) ∧
            g (gm06DartMate d) =
              g (2 * (rep.tagged.length + gm06PreviousCuffIndex k i.val) + 1)) ∧
        (∀ i : Fin k, ∃ s : (cylinderSphereDrawing H).R,
          g (2 * (rep.tagged.length + i.val) + 1) = some s ∧
            s.val = cylinderToSphere '' (cylinderStrip L i \ bd ClosedCylinder)) ∧
        ∀ i j : Fin k, g (2 * (rep.tagged.length + i.val) + 1) =
          g (2 * (rep.tagged.length + j.val) + 1) → i = j := by
  obtain ⟨H, hHF, hHU, hHV, g, _, hskip, hface, _, hgap⟩ := rep.exists_numeric_comparison_labels hG
  have hwords : ∀ r ∈ x.rotations.flatten,
      g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm) r) = g r := by
    intro r hr
    obtain ⟨d, rfl⟩ := (rep.row_label_cover r).mp hr
    exact hface d
  have hstrips (i : Fin k) : ∃ s : (cylinderSphereDrawing H).R,
      g (2 * (rep.tagged.length + i.val) + 1) = some s ∧
        s.val = cylinderToSphere '' (cylinderStrip L i \ bd ClosedCylinder) := by
    obtain ⟨s, hs, hsub⟩ := hgap i
    exact ⟨s, hs, comparison_region_eq_strip_of_contains L hG rep.cuffed_U hHU i s hsub⟩
  refine ⟨H, hHF, hHU, hHV, g, hskip, hwords, rep.path_corner_labels hG g hskip hwords,
    hstrips, fun i j hij => ?_⟩
  by_contra hne
  obtain ⟨si, hgi, hsi⟩ := hstrips i
  obtain ⟨sj, hgj, hsj⟩ := hstrips j
  have hs : si = sj := Option.some.inj (hgi.symm.trans (hij.trans hgj))
  obtain ⟨p, hp⟩ := region_nonempty si.property
  have hpi : p ∈ cylinderToSphere '' (cylinderStrip L i \ bd ClosedCylinder) := by
    rw [← hsi]
    exact hp
  have hpj : p ∈ cylinderToSphere '' (cylinderStrip L j \ bd ClosedCylinder) := by
    rw [← hsj, ← hs]
    exact hp
  obtain ⟨a, ha, hap⟩ := hpi
  obtain ⟨b, hb, hbp⟩ := hpj
  have hab : a = b := injective_cylinderToSphere (hap.trans hbp.symm)
  obtain ⟨θ, hθ⟩ := L.exists_hasTheta hG.1
  exact disjoint_left.mp (disjoint_cylinderStrip L hG hθ hne) ha.1 (hab.symm ▸ hb.1)

end GM06CurrentDrawingRep
end GraphMinor.GM06
