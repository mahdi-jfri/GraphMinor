module

public import GraphMinor.GM05.CrosscapModelMap
import GraphMinor.GM05.ModelBaseCompact
import GraphMinor.Surface.DrawCarry
import GraphMinor.GM19.FragmentDirection

/-!
# A fixed disc away from the supported half turn

For the crosscap obstruction in GM V, (8.10), the half turn fixes an
open neighbourhood of the model point at infinity. The image of its
closed support region is compact, hence closed. Infinity is outside
that image because its quotient fiber is a singleton. A small closed
disc in the complementary neighbourhood is fixed pointwise.
-/

public section

namespace GraphMinor.GM05

open Set Topology Metric Surface GM19

open scoped OnePoint

/-- A supported crosscap half turn on a closed model fixes a closed
disc pointwise, in a neighbourhood of infinity off its compact support. -/
theorem crosscap_half_turn_fixed_disc {a b k : ℕ} (hk : k<b)
    (Θ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hnorm : ∀ x,dist (Θ x) (modelCentre (2*a+k))=dist x (modelCentre (2*a+k)))
    (hfix : ∀ x,3/2 ≤ dist x (modelCentre (2*a+k)) → Θ x=x)
    (hcircle : ∀ u : EuclideanPlane,‖u‖=1 → Θ (modelCentre (2*a+k)+u)=modelCentre (2*a+k)-u) :
    ∃ D : Set (SurfaceModel a b 0),IsClosedDisc D ∧
      ∀ x ∈ D,crosscapModelHalfTurn hk Θ hnorm hfix hcircle x=x := by
  let n := 2*a+b+0
  have hS := isClosedSurface_model a b
  let : T2Space (SurfaceModel a b 0) := hS.2.1
  let : CompactSpace (modelBase n) := isCompact_iff_compactSpace.mp (isCompact_modelBase n)
  let q : modelBase n → SurfaceModel a b 0 := Quot.mk _
  let A : Set (OnePoint EuclideanPlane) :=
    ((↑) : EuclideanPlane → OnePoint EuclideanPlane) '' closedBall (modelCentre (2*a+k)) (3/2)
  let K : Set (modelBase n) := Subtype.val ⁻¹' A
  have hA : IsClosed A := ((isCompact_closedBall _ _).image OnePoint.continuous_coe).isClosed
  have hK : IsCompact K := (hA.preimage continuous_subtype_val).isCompact
  have hq : Continuous q := continuous_quot_mk
  have hclosed : IsClosed (q '' K) := (hK.image hq).isClosed
  let xInf : SurfaceModel a b 0 := q (modelBaseInfinity n)
  have hinfty : xInf ∈ (q '' K)ᶜ := by
    rintro ⟨p,hp,he⟩
    have hep : p=modelBaseInfinity n := model_quot_infinity_fiber he.symm
    rw [hep] at hp
    change (modelBaseInfinity n).1 ∈ A at hp
    rw [modelBaseInfinity_val] at hp
    obtain ⟨x,hx,hxe⟩ := hp
    exact OnePoint.coe_ne_infty x hxe
  have hfixed : ∀ x ∈ (q '' K)ᶜ,crosscapModelHalfTurn hk Θ hnorm hfix hcircle x=x := by
    intro x hx
    obtain ⟨p,rfl⟩ := Quot.exists_rep x
    rw [crosscapModelHalfTurn_mk]
    apply congrArg (Quot.mk _)
    apply Subtype.ext
    rw [modelBaseHalfTurn_apply_val]
    cases hp : p.1 using OnePoint.rec with
    | infty => rfl
    | coe v =>
      change (↑(Θ v) : OnePoint EuclideanPlane)=↑v
      apply congrArg ((↑) : EuclideanPlane → OnePoint EuclideanPlane)
      apply hfix
      by_contra hn
      have hpk : p ∈ K := ⟨v,mem_closedBall.mpr (le_of_lt (lt_of_not_ge hn)),hp.symm⟩
      exact hx ⟨p,hpk,rfl⟩
  obtain ⟨D,hD,-,hs⟩ := exists_small_disc (hS.2.2 xInf) hclosed.isOpen_compl hinfty
  exact ⟨D,hD,fun x hx ↦ hfixed x (hs hx)⟩

end GraphMinor.GM05
