module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutOArc
import GraphMinor.Surface.ModelCriterion

/-!
# The two component models of a separating cut

In Graph Minors V, (8.10), a separating circle in a connected handle
surface cuts it into two surfaces with one cuff each. The library
pasting calculation adds their handle and crosscap counts. The model
criterion therefore makes their crosscap counts zero, their cuff counts
one, and the sum of their handle counts the original genus.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u

/-- The two components of a two-sided cut of a closed handle surface
have one cuff each, no crosscaps, and genera summing to the original
genus. This is the separating-cut calculation for GM V, (8.10). -/
theorem separating_cut_models {Y S : Type u} [TopologicalSpace Y]
    [TopologicalSpace S] [T2Space S] (hY : IsSurface Y)
    {ψ : Y → S} {C : Set S} (hψ : IsCutting ψ C)
    {g : ℕ} (eS : S ≃ₜ SurfaceModel g 0 0)
    {X X' W₁ W₂ : Set Y} (hun : X ∪ X'=ψ ⁻¹' C)
    (hb : BijOn ψ X C) (hb' : BijOn ψ X' C) (hX : IsOArc X) (hX' : IsOArc X')
    (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂) (hdW : Disjoint W₁ W₂)
    (huW : W₁ ∪ W₂=univ) (hsX : X ⊆ W₁) (hsX' : X' ⊆ W₂)
    [ConnectedSpace W₁] [ConnectedSpace W₂] :
    ∃ a₁ a₂ : ℕ, a₁+a₂=g ∧ Nonempty (W₁ ≃ₜ SurfaceModel a₁ 0 1) ∧
      Nonempty (W₂ ≃ₜ SurfaceModel a₂ 0 1) := by
  let : T2Space Y := hY.2.1
  let : CompactSpace Y := hY.1
  have hneX : X.Nonempty := by obtain ⟨e⟩ := hX; exact ⟨_,(e 1).2⟩
  obtain ⟨x,hx⟩ := hneX
  let : Nonempty S := ⟨ψ x⟩
  have htX : X ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hun ▸ Or.inl hz)
  have htX' : X' ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hun ▸ Or.inr hz)
  obtain ⟨a₁,b₁,c₁,⟨e₁⟩⟩ := classification W₁ (isSurface_sub hY hW₁) inferInstance
  obtain ⟨a₂,b₂,c₂,⟨e₂⟩⟩ := classification W₂ (isSurface_sub hY hW₂) inferInstance
  obtain ⟨i,j,σ,f,-,-,hi,hj,hf,-⟩ :=
    loop_comps_aux hY hψ hun hb hb' hX hX' hW₁ hW₂ hdW huW e₁ e₂ hsX hsX' htX htX'
  obtain ⟨hN₁,hL₁⟩ := erase_facts c₁ i
  obtain ⟨hN₂,hL₂⟩ := erase_facts c₂ j
  obtain ⟨e'⟩ := homeo_of_two_loop hi hj hN₁ hN₂ hL₁ hL₂ hf
  rw [length_erase_range hi,length_erase_range hj] at e'
  have hc := (modelCriterion.2 g 0 0 (a₂+a₁) (b₂+b₁) (c₂-1+(c₁-1))).mp ⟨eS.symm.trans e'⟩
  have hb0 := hc.2.2.mp rfl
  have hb₁ : b₁=0 := by omega
  have hb₂ : b₂=0 := by omega
  have hc₁ : c₁=1 := by omega
  have hc₂ : c₂=1 := by omega
  have ha : a₁+a₂=g := by omega
  subst b₁
  subst b₂
  subst c₁
  subst c₂
  exact ⟨a₁,a₂,ha,⟨e₁⟩,⟨e₂⟩⟩

end GraphMinor.GM05
