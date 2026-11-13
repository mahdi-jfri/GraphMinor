module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.GM19.Defs2
import GraphMinor.GM05.OrientationObstruction
import GraphMinor.GM05.CrosscapHalfTurn
import GraphMinor.GM05.CrosscapFixedDisc
import GraphMinor.GM05.CrosscapChartReflection
import GraphMinor.GM05.ReflectedDiscImage
import GraphMinor.Surface.ModelCriterion
import GraphMinor.Surface.DrawCarry
import GraphMinor.GM19.Section4c
import GraphMinor.GM19.Section5o

/-!
# Closed orientable surfaces have handle models

For GM V, (8.10), remove the representation hypothesis from the
connected circle-cut construction. A model with a crosscap has a
supported half turn that fixes a disc near infinity and reflects the
local polar disc at the crosscap. The orientation obstruction rules
it out. Classification of a closed connected surface then has no
cuffs, and orientability forces its crosscap count to be zero.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- A closed model with at least one crosscap has no disc orientation:
the supported half turn fixes one disc and reverses another. -/
theorem not_orientable_closedModel_of_pos_crosscaps (a b : ℕ) (hb : 0<b) :
    ¬IsOrientableSurface (SurfaceModel a b 0) := by
  let : T2Space (SurfaceModel a b 0) := (isClosedSurface_model a b).2.1
  let : T2Space (Quot (ModelGlue a b (2*a+b+0))) := (isClosedSurface_model a b).2.1
  let : ConnectedSpace (SurfaceModel a b 0) := (modelCriterion.1 a b 0).2
  obtain ⟨Θ,hnorm,hfix,hcore⟩ := exists_crosscap_half_turn_core (2*a+0)
  have hcircle (u : EuclideanPlane) (hu : ‖u‖=1) :
      Θ (modelCentre (2*a+0)+u)=modelCentre (2*a+0)-u := hcore u (by rw [hu]; norm_num)
  let e : SurfaceModel a b 0 ≃ₜ SurfaceModel a b 0 := crosscapModelHalfTurn hb Θ hnorm hfix hcircle
  obtain ⟨D,hD,hDfix⟩ := crosscap_half_turn_fixed_disc hb Θ hnorm hfix hcircle
  obtain ⟨E,hE,hEimage,p,q,r,hp,hq,hr,hpq,hqr,hpr,hep,heq,her⟩ :=
    reflected_disc_image (crosscapPolarChart a b 0 0) (continuous_crosscapPolarChart hb)
      (injective_crosscapPolarChart a b 0 0) e
      (crosscapPolarChart_reflection hb Θ hnorm hfix hcircle hcore)
  exact not_orientable_of_disc_swap (modelCriterion.1 a b 0).1 e hD hE hDfix hEimage
    hp hq hr hpq hqr hpr hep heq her

/-- An orientation of a closed model forces its crosscap count to zero. -/
theorem closedModel_crosscaps_eq_zero (a b : ℕ) (hO : IsOrientableSurface (SurfaceModel a b 0)) : b=0 := by
  by_contra hb
  exact not_orientable_closedModel_of_pos_crosscaps a b (Nat.pos_of_ne_zero hb) hO

/-- A connected closed orientable surface is homeomorphic to a sphere
with handles. This supplies the handle-model representation used in
the connected case of Graph Minors V, (8.10). -/
theorem orientable_closedSurface_handle_model {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (hO : IsOrientableSurface S) :
    ∃ g : ℕ,Nonempty (S ≃ₜ SurfaceModel g 0 0) := by
  let : T2Space S := hS.2.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨a,b,c,⟨e⟩⟩ := classification S hs inferInstance
  have hbd : bd S=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx (hS.2.2 x)
  have hnum : numCuffs S=0 := by
    simp only [numCuffs,cuffs,hbd,componentsIn,image_empty,ncard_empty]
  have hc : c=0 := by
    have h := numCuffs_eq e
    rw [numCuffs_model,hnum] at h
    exact h.symm
  subst c
  have hOm : IsOrientableSurface (SurfaceModel a b 0) := isOrientable_of_homeo e.symm hO
  have hb := closedModel_crosscaps_eq_zero a b hOm
  subst b
  exact ⟨a,⟨e⟩⟩

end GraphMinor.GM05
