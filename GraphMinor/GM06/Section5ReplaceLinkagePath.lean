module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks

/-!
# Replacing one path of a cylinder linkage

For Reduction 4 of VI, page 129, retain the paths and curves at all
other indices. A replacement path with the same ends and disjoint
from those other paths supplies the changed linkage member. Choose
an injective parametrization of that path and keep its prescribed
terminal vertex.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A path with the same ends, disjoint from the other linkage paths,
can replace one linkage member while retaining every other curve. -/
theorem exists_linkage_replacing_path
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {R : Drawing ClosedCylinder} (hRG : R.IsSubdrawing G)
    (hR : IsPathDrawing R (cylinderM1Point k i) (L.curve i 1))
    (hdisj : ∀ j, j ≠ i → Disjoint R.U (L.pathDrawing j).U) :
    ∃ L' : CylinderLinkage k G, L'.pathDrawing i = R ∧
      L'.curve i 1 = L.curve i 1 ∧
      ∀ j, j ≠ i → L'.pathDrawing j = L.pathDrawing j ∧ L'.curve j = L.curve j := by
  classical
  obtain ⟨f, hf⟩ := hR.2
  let P := fun j => if j = i then R else L.pathDrawing j
  let g := fun j => if j = i then f else L.curve j
  have hgend : ∀ j, g j 1 = L.curve j 1 := by
    intro j
    by_cases hj : j = i
    · subst j; simpa [g] using hf.2.2.2
    · simp [g, hj]
  let L' : CylinderLinkage k G := {
    pathDrawing := P
    curve := g
    isSubdrawing j := by
      by_cases hj : j = i
      · subst j; simpa [P] using And.intro hRG hRG.U_subset
      · simpa [P, hj] using L.isSubdrawing j
    isPath j := by
      rw [hgend]
      by_cases hj : j = i
      · subst j; simpa [P] using hR
      · simpa [P, hj] using L.isPath j
    curve_parametrizes j := by
      rw [hgend]
      by_cases hj : j = i
      · subst j; simpa [P, g] using hf
      · simpa [P, g, hj] using L.curve_parametrizes j
    curve_one_mem j := by rw [hgend]; exact L.curve_one_mem j
    pairwise_disjoint := by
      intro j l hjl
      by_cases hj : j = i
      · subst j; simpa [P, Ne.symm hjl] using hdisj l (Ne.symm hjl)
      · by_cases hl : l = i
        · subst l; simpa [P, hj] using (hdisj j hj).symm
        · simpa [P, hj, hl] using L.pairwise_disjoint hjl }
  exact ⟨L', by simp [L', P], hgend i,
    fun j hj => ⟨by simp [L', P, hj], by simp [L', g, hj]⟩⟩

end GraphMinor.GM06
