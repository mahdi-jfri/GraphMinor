module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5AttachedSeparationHelix
import GraphMinor.GM06.Section5SinglePathSeparationHelix

/-!
# Helix pullback for Reduction 2

Graph Minors VI (5.5), page 130, treats Reduction 2 by disc
surgeries. For at least two paths the retained cuffs give a
connected punctured barrier. For one path first exhaust clockwise
discarded edges, then construct the barrier and enclosures on the
cut disc. Both cases provide actual potential-nonincreasing helix
pullbacks from the printed separation data.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Graph Minors VI (5.5), page 130, for Reduction 2, including
the one-path cut-disc case. -/
theorem theorem_5_5_red2
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hG : IsCylinderSection5Drawing k G) (hG' : IsCylinderSection5Drawing k G')
    (hRed : Section5Reduction2Step k G L G' L')
    (f : Curve ClosedCylinder) (hf : IsHelix k G' f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k G' f := by
  obtain ⟨i, G₂, hsep, _, _, hover, _, hPaths, _⟩ := hRed
  by_cases hk1 : k = 1
  · subst k
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi] at hover
    exact theorem_5_5_red2_of_one L L' hG hG' hsep hover hPaths f hf
  · have hk : 1 < k := by have := hG.1; omega
    exact theorem_5_5_red2_of_two_le L L' hk hG hG' i hsep hover f hf

end GraphMinor.GM06
