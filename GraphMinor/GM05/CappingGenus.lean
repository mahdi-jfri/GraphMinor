module

public import GraphMinor.GM05.SurfaceDescent
public import GraphMinor.GM19.Defs2
import GraphMinor.GM19.Section4c
import GraphMinor.GM19.CapModel
public import GraphMinor.GM19.Perimeter
import GraphMinor.Surface.ModelCriterion

/-!
# The genus calculation after capping

In the connected case of Graph Minors V, (8.10), the library circle cut
gives a simpler surface. Represent the original surface by its handle
model. The model criterion forces every model in the simpler-surface
comparison to have no crosscaps. Capping removes its cuffs and preserves
its handles, so its closed genus strictly decreases.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- Capping a surface homeomorphic to a sphere with handles and cuffs
preserves its number of handles. -/
theorem connectedGenus_capping_of_model {Y T : Type}
    [TopologicalSpace Y] [TopologicalSpace T] (cap : IsCappedSurface Y T)
    {a c : ℕ} (e : Y ≃ₜ SurfaceModel a 0 c) : connectedGenus T=a := by
  obtain ⟨f⟩ := capModel a 0 c T (cap.ofHomeo e.symm)
  exact connectedGenus_eq_of_model f

/-- The explicit handle model survives cutting and capping. This
retains the model data used in the surface choice for GM V, (8.14). -/
theorem exists_handle_model_capping_of_simpler {Y T S : Type}
    [TopologicalSpace Y] [TopologicalSpace T] [TopologicalSpace S]
    (cap : IsCappedSurface Y T) (hsimple : IsSimplerThan Y S)
    {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0) :
    ∃ a : ℕ, a<g ∧ Nonempty (T ≃ₜ SurfaceModel a 0 0) := by
  obtain ⟨a,b,c,a',b',c',⟨eY⟩,⟨eS'⟩,haa,hbb,hlt⟩ := hsimple
  have hc := (modelCriterion.2 g 0 0 a' b' c').mp ⟨eS.symm.trans eS'⟩
  have hb' : b'=0 := hc.2.2.mp rfl
  have hb : b=0 := Nat.eq_zero_of_le_zero (hb' ▸ hbb)
  have ha' : a'=g := by omega
  subst b
  obtain ⟨f⟩ := capModel a 0 c T (cap.ofHomeo eY.symm)
  exact ⟨a,by omega,⟨f⟩⟩

/-- The connected simpler-cut case of the genus calculation in
Graph Minors V, (8.10). The comparison is the proved library cut's
simpler-surface alternative, and the capping is the library capping. -/
theorem connectedGenus_capping_lt_of_simpler {Y T S : Type}
    [TopologicalSpace Y] [TopologicalSpace T] [TopologicalSpace S]
    (cap : IsCappedSurface Y T) (hsimple : IsSimplerThan Y S)
    {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0) : connectedGenus T<connectedGenus S := by
  obtain ⟨a,b,c,a',b',c',⟨eY⟩,⟨eS'⟩,haa,hbb,hlt⟩ := hsimple
  have hc := (modelCriterion.2 g 0 0 a' b' c').mp ⟨eS.symm.trans eS'⟩
  have hb' : b'=0 := hc.2.2.mp rfl
  have hb : b=0 := Nat.eq_zero_of_le_zero (hb' ▸ hbb)
  have ha' : a'=g := by omega
  subst b
  rw [connectedGenus_capping_of_model cap eY,connectedGenus_eq_of_model eS]
  omega

/-- The connected simpler-cut case decreases the actual component-genus
list, rather than merely a numerical complexity of surfaces with cuffs. -/
theorem surfaceGenusLT_capping_of_simpler {Y T S : Type}
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace T] [TopologicalSpace S] [ConnectedSpace S]
    (cap : IsCappedSurface Y T) (hS : IsClosedSurface S)
    (hsimple : IsSimplerThan Y S) {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0) :
    SurfaceGenusLT cap.isClosedSurface hS := by
  let : ConnectedSpace T := cap.connected
  change GenusListLT (surfaceGenusList T cap.isClosedSurface) (surfaceGenusList S hS)
  rw [surfaceGenusList_of_connected,surfaceGenusList_of_connected]
  exact ⟨[],connectedGenus T,connectedGenus S,[],[],rfl,rfl,
    connectedGenus_capping_lt_of_simpler cap hsimple eS⟩

end GraphMinor.GM05
