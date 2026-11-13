module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5AdjoinBoundary

/-!
# Adjoining the cuffs before and after contraction

The lifted-region construction for VI (5.5), page 130, uses drawings
with their cuff arcs adjoined. A boundary-fixed contraction maps the
old cuff set onto itself. Thus the two augmented drawings still have
the required image relation for their underlying point sets.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Adjoining the cuffs is compatible with a boundary-fixed
contraction, without changing either vertex set. -/
theorem exists_cuff_drawings_of_boundary_fixed_contraction
    {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hG : IsCylinderSection5Drawing k G) (hG' : IsCylinderSection5Drawing k G')
    (π : C(ClosedCylinder, ClosedCylinder)) (hU : G'.U = π '' G.U)
    (hbd : ∀ p ∈ bd ClosedCylinder, π p = p) :
    ∃ F F' : Drawing ClosedCylinder,
      G.IsSubdrawing F ∧ G'.IsSubdrawing F' ∧
      F.U = G.U ∪ bd ClosedCylinder ∧ F'.U = G'.U ∪ bd ClosedCylinder ∧
      F.V = G.V ∧ F'.V = G'.V ∧ F'.U = π '' F.U := by
  obtain ⟨F, hGF, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  obtain ⟨F', hG'F', hF'U, hF'V⟩ := exists_drawing_adjoining_boundary L' hG'
  have himbd : π '' bd ClosedCylinder = bd ClosedCylinder := by
    apply subset_antisymm
    · rintro p ⟨x, hx, hxp⟩
      exact ((hbd x hx).symm.trans hxp) ▸ hx
    · intro p hp
      exact ⟨p, hp, hbd p hp⟩
  refine ⟨F, F', hGF, hG'F', hFU, hF'U, hFV, hF'V, ?_⟩
  rw [hF'U, hFU, image_union, himbd, hU]

end GraphMinor.GM06
