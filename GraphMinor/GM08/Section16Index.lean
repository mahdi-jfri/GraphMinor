module

public import GraphMinor.GM08.Section16Defs
import GraphMinor.GM08.Section16Split

/-!
# Index bounds for cutting a tube

A normal hoop with fewer vertices than one boundary yields a graft of smaller
index on the other side. Counting the overlap of the boundary hoops is needed
because the two boundary hoops can meet. These are the index bounds in Cases 2
and 3 of Graph Minors VIII (16.2), pages 283–284.
-/

public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface GraphMinor.GM11

universe u v w

private theorem ncard_union_lt_of_inter_subset {α : Type*} {A B C : Set α}
    (hA : A.Finite) (hB : B.Finite) (hC : C.Finite)
    (hinter : A ∩ B ⊆ C) (hlt : C.ncard < B.ncard) :
    (A ∪ C).ncard < (A ∪ B).ncard := by
  have h₁ := ncard_union_add_ncard_inter A B hA hB
  have h₂ := ncard_union_add_ncard_inter A C hA hC
  have h₃ : (A ∩ B).ncard ≤ (A ∩ C).ncard :=
    ncard_le_ncard (fun x hx => ⟨hx.1, hinter hx⟩) (hA.subset inter_subset_left)
  omega

/-- Every vertex common to the two boundary hoops lies on any intermediate hoop. -/
theorem Tube.boundary_inter_subset_hoop {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {H : Set S} (hH : IsHoop H) (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂) :
    τ.F₁ ∩ τ.F₂ ⊆ H := by
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  obtain ⟨hleft, hright⟩ := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hH hle).mp hsub
  have h := areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub
  intro x hx
  rw [← cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hH τ.isHoop_F₂ hleft hright]
  exact ⟨subset_cylinderBetween_left h.1 hx.1, subset_cylinderBetween_right h.2 hx.2⟩

/-- Cutting at a hoop smaller than the second boundary strictly decreases the
index of the graft on the first side, as used in VIII (16.2). -/
theorem Tube.Framing.index_left_lt_of_hoop {S : Type w} [TopologicalSpace S]
    {τ : Tube S} {α : Type u} {β : Type v} {X : Graft α β} (fr : τ.Framing X)
    {H : Set S} (hH : IsHoop H) (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hlt : (τ.Γ.V ∩ H).ncard < (τ.Γ.V ∩ τ.F₂).ncard) :
    (fr.subGraft (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).1).index <
      X.index := by
  have hinter : fr.vertsIn τ.F₁ ∩ fr.vertsIn τ.F₂ ⊆ fr.vertsIn H := by
    rw [← fr.vertsIn_inter]
    exact fr.vertsIn_mono (τ.boundary_inter_subset_hoop hH hsub)
  have hcard : (fr.vertsIn H).ncard < (fr.vertsIn τ.F₂).ncard := by
    rw [fr.ncard_vertsIn, fr.ncard_vertsIn, inter_comm H, inter_comm τ.F₂]
    exact hlt
  have h := ncard_union_lt_of_inter_subset
    (X.finite_G.1.subset (fr.vertsIn_subset_V τ.F₁))
    (X.finite_G.1.subset (fr.vertsIn_subset_V τ.F₂))
    (X.finite_G.1.subset (fr.vertsIn_subset_V H)) hinter hcard
  change (fr.vertsIn τ.F₁ ∪ fr.vertsIn H).ncard < X.T.ncard
  rwa [fr.vertsIn_F_union] at h

/-- Cutting at a hoop smaller than the first boundary strictly decreases the
index of the graft on the second side, as used in VIII (16.2). -/
theorem Tube.Framing.index_right_lt_of_hoop {S : Type w} [TopologicalSpace S]
    {τ : Tube S} {α : Type u} {β : Type v} {X : Graft α β} (fr : τ.Framing X)
    {H : Set S} (hH : IsHoop H) (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hlt : (τ.Γ.V ∩ H).ncard < (τ.Γ.V ∩ τ.F₁).ncard) :
    (fr.subGraft (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).2).index <
      X.index := by
  have hinter : fr.vertsIn τ.F₂ ∩ fr.vertsIn τ.F₁ ⊆ fr.vertsIn H := by
    rw [inter_comm, ← fr.vertsIn_inter]
    exact fr.vertsIn_mono (τ.boundary_inter_subset_hoop hH hsub)
  have hcard : (fr.vertsIn H).ncard < (fr.vertsIn τ.F₁).ncard := by
    rw [fr.ncard_vertsIn, fr.ncard_vertsIn, inter_comm H, inter_comm τ.F₁]
    exact hlt
  have h := ncard_union_lt_of_inter_subset
    (X.finite_G.1.subset (fr.vertsIn_subset_V τ.F₂))
    (X.finite_G.1.subset (fr.vertsIn_subset_V τ.F₁))
    (X.finite_G.1.subset (fr.vertsIn_subset_V H)) hinter hcard
  change (fr.vertsIn H ∪ fr.vertsIn τ.F₂).ncard < X.T.ncard
  rwa [union_comm (fr.vertsIn τ.F₂) (fr.vertsIn H),
    union_comm (fr.vertsIn τ.F₂) (fr.vertsIn τ.F₁), fr.vertsIn_F_union] at h

/-- Case 3 of Graph Minors VIII (16.2), page 284. A normal hoop smaller than
both boundary hoops cuts the graft into two tubular grafts of index at most `k - 1`. -/
theorem Tube.Framing.mem_WGraftClass_of_smaller_hoop {S : Type w} [TopologicalSpace S]
    {τ : Tube S} {α : Type u} {β : Type v} [Infinite α] {X : Graft α β} (fr : τ.Framing X)
    {k : ℕ} (hk : X.index ≤ k) {H : Set S} (hH : IsHoop H) (hNH : τ.Γ.IsNormal H)
    (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hlt₁ : (τ.Γ.V ∩ H).ncard < (τ.Γ.V ∩ τ.F₁).ncard)
    (hlt₂ : (τ.Γ.V ∩ H).ncard < (τ.Γ.V ∩ τ.F₂).ncard) :
    X ∈ WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classB ((k : ℤ) - 1))) := by
  have hlam := areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub
  apply fr.mem_WGraftClass_of_hoop hH hNH hsub (isoGraftClass_classB_eq _) (isoGraftClass_classB_eq _)
  · refine ⟨IsTubularGraft.of_framing
      (fr.isFraming_subTube hlam.1 τ.isNormal_F₁ hNH), ?_⟩
    have hidx := fr.index_left_lt_of_hoop hH hsub hlt₂
    change ((fr.subGraft hlam.1).index : ℤ) ≤ (k : ℤ) - 1
    omega
  · refine ⟨IsTubularGraft.of_framing
      (fr.isFraming_subTube hlam.2 hNH τ.isNormal_F₂), ?_⟩
    have hidx := fr.index_right_lt_of_hoop hH hsub hlt₁
    change ((fr.subGraft hlam.2).index : ℤ) ≤ (k : ℤ) - 1
    omega

end GraphMinor.GM08
