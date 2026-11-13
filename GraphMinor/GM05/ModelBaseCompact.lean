module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.ModelPartners
import GraphMinor.GM05.ModelQuotientFibers

/-!
# Compact model bases and the point at infinity

For the fixed disc in the orientation obstruction of GM V, (8.10),
use a neighbourhood of the point at infinity, away from the supported
half turn. The model base is closed in the one-point compactification,
since its complement is the union of the removed open holes. The point
at infinity is in the base and has a singleton quotient fiber.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface

open scoped OnePoint

/-- The sphere with the open model holes removed is closed. -/
theorem isClosed_modelBase (n : ℕ) : IsClosed (modelBase n) := by
  have he : modelBase n=⋂ i : ℕ,⋂ (_ : i<n),
      (((↑) : EuclideanPlane → OnePoint EuclideanPlane) '' ball (modelCentre i) 1)ᶜ := by
    ext p
    constructor
    · intro hp
      apply mem_iInter₂.mpr
      intro i hi
      rintro ⟨x,hx,hxp⟩
      have hn := hp i hi x hxp.symm
      exact (not_lt_of_ge hn) (mem_ball.mp hx)
    · intro hp i hi x hpx
      have hn := mem_iInter₂.mp hp i hi
      apply le_of_not_gt
      intro hx
      exact hn ⟨x,mem_ball.mpr hx,hpx.symm⟩
  rw [he]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun _ ↦
    (OnePoint.isOpenMap_coe _ isOpen_ball).isClosed_compl

/-- A model base is compact as a closed part of the sphere. -/
theorem isCompact_modelBase (n : ℕ) : IsCompact (modelBase n) := (isClosed_modelBase n).isCompact

/-- The point at infinity lies outside every removed model hole. -/
def modelBaseInfinity (n : ℕ) : modelBase n :=
  ⟨∞,fun _ _ x he ↦ (OnePoint.infty_ne_coe x he).elim⟩

/-- The base point at infinity has the expected underlying point. -/
theorem modelBaseInfinity_val (n : ℕ) : (modelBaseInfinity n).1=∞ := by rfl

/-- The point at infinity has a singleton fiber in every model quotient. -/
theorem model_quot_infinity_fiber {a b n : ℕ} {p : modelBase n}
    (he : Quot.mk (ModelGlue a b n) (modelBaseInfinity n)=Quot.mk _ p) : p=modelBaseInfinity n := by
  rcases model_quot_eq_iff.mp he with he|he
  · exact he.symm
  rcases model_gluing_cases he with h|h|h
  all_goals
    obtain ⟨i,hi,u,hu,hp,hq⟩ := h
    rw [modelBaseInfinity_val] at hp
    exact (OnePoint.infty_ne_coe _ hp).elim

end GraphMinor.GM05
