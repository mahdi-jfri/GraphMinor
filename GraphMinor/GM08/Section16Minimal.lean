module

public import GraphMinor.GM08.Section16Defs

/-!
# The closest small hoop

In Case 2 of Graph Minors VIII (16.2), page 283, a hoop with fewer vertices
than the first boundary is chosen with as few vertices as possible on its
first side. A further inward hoop then has no smaller cut between it and the
first boundary. This file proves the finite minimization and counting steps.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- Vertices strictly on the first side of a hoop within a tube. This is the
quantity minimized in Case 2 of VIII (16.2), page 283. -/
def Tube.firstSideVertices {S : Type w} [TopologicalSpace S] (τ : Tube S) (H : Set S) : Set S :=
  τ.Γ.V ∩ (cylinderBetween τ.F₁ H \ H)

/-- Choose the small hoop with the fewest vertices on its first side, as in
Case 2 of VIII (16.2), page 283. -/
theorem Tube.exists_closest_small_hoop {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {m : ℕ}
    (hex : ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧
      H ⊆ cylinderBetween τ.F₁ τ.F₂ ∧ (τ.Γ.V ∩ H).ncard < m) :
    ∃ F : Set S, IsHoop F ∧ τ.Γ.IsNormal F ∧
      F ⊆ cylinderBetween τ.F₁ τ.F₂ ∧ (τ.Γ.V ∩ F).ncard < m ∧
      ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween τ.F₁ τ.F₂ →
        (τ.Γ.V ∩ H).ncard < m →
        (τ.firstSideVertices F).ncard ≤ (τ.firstSideVertices H).ncard := by
  classical
  let P : ℕ → Prop := fun n => ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧
    H ⊆ cylinderBetween τ.F₁ τ.F₂ ∧ (τ.Γ.V ∩ H).ncard < m ∧
    (τ.firstSideVertices H).ncard = n
  have hex' : ∃ n, P n := by
    obtain ⟨H, hH, hNH, hsub, hlt⟩ := hex
    exact ⟨_, H, hH, hNH, hsub, hlt, rfl⟩
  obtain ⟨F, hF, hNF, hsub, hlt, heq⟩ := Nat.find_spec hex'
  refine ⟨F, hF, hNF, hsub, hlt, fun H hH hNH hHsub hHlt => ?_⟩
  rw [heq]
  exact Nat.find_min' hex' ⟨H, hH, hNH, hHsub, hHlt, rfl⟩

private theorem firstSideVertices_mono_of_disc_subset {S : Type w} [TopologicalSpace S]
    (τ : Tube S) (cap : CylinderSphereCap S) {H K : Set S} (hH : IsHoop H) (hK : IsHoop K)
    (h₁ : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 hH)
    (h₂ : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 hK) :
    τ.firstSideVertices H ⊆ τ.firstSideVertices K := by
  have hsub := cap.cylinderBetween_mono τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₁ hH hK
    Subset.rfl h₁ h₂
  have hinter := cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hH hK h₁ h₂
  have hlam : AreLaminarHoops H K := (cap.areLaminarHoops_iff τ.isCylinder hH hK).mpr (Or.inl h₂)
  rintro x ⟨hxV, hxH, hxnot⟩
  refine ⟨hxV, hsub hxH, fun hxK => hxnot ?_⟩
  rw [← hinter]
  exact ⟨hxH, subset_cylinderBetween_right hlam hxK⟩

/-- Moving a hoop towards the first boundary cannot add vertices strictly on
its first side. -/
theorem Tube.firstSideVertices_mono {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {F H : Set S} (hF : IsHoop F) (hH : IsHoop H)
    (hFsub : F ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hHsub : H ⊆ cylinderBetween τ.F₁ F) :
    τ.firstSideVertices H ⊆ τ.firstSideVertices F := by
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have hFpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hF hle).mp hFsub
  have hHpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ hF hH hFpos.1).mp hHsub
  exact firstSideVertices_mono_of_disc_subset τ cap hH hF hHpos.1 hHpos.2

/-- A vertex on an intermediate hoop but off the outer hoop makes every
hoop before it have strictly fewer first-side vertices than the outer hoop. -/
theorem Tube.firstSideVertices_ncard_lt {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {F K H : Set S} (hF : IsHoop F) (hK : IsHoop K) (hH : IsHoop H)
    (hFsub : F ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hKsub : K ⊆ cylinderBetween τ.F₁ F) (hHsub : H ⊆ cylinderBetween τ.F₁ K)
    {v : S} (hvV : v ∈ τ.Γ.V) (hvK : v ∈ K) (hvF : v ∉ F) :
    (τ.firstSideVertices H).ncard < (τ.firstSideVertices F).ncard := by
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have hFpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hF hle).mp hFsub
  have hKpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ hF hK hFpos.1).mp hKsub
  have hHpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ hK hH hKpos.1).mp hHsub
  have hmono := firstSideVertices_mono_of_disc_subset τ cap hH hF
    hHpos.1 (hHpos.2.trans hKpos.2)
  have hvOld : v ∈ τ.firstSideVertices F := ⟨hvV, hKsub hvK, hvF⟩
  have hvNew : v ∉ τ.firstSideVertices H := by
    rintro ⟨_, hvSide, hvnot⟩
    have hlam : AreLaminarHoops H K :=
      (cap.areLaminarHoops_iff τ.isCylinder hH hK).mpr (Or.inl hHpos.2)
    apply hvnot
    rw [← cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hH hK hHpos.1 hHpos.2]
    exact ⟨hvSide, subset_cylinderBetween_right hlam hvK⟩
  exact ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨hmono, fun heq => hvNew (heq ▸ hvOld)⟩)
    (τ.Γ.finite_V.subset inter_subset_left)

/-- The choice of the closest small hoop rules out a small normal hoop
between the first boundary and any strictly inward hoop. This is the
minimality argument used before Menger in Case 2 of VIII (16.2), page 283. -/
theorem Tube.hoop_ncard_ge_of_closest {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {m : ℕ} {F K : Set S} (hF : IsHoop F) (hK : IsHoop K)
    (hFsub : F ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hKsub : K ⊆ cylinderBetween τ.F₁ F)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.Γ.V ∩ H).ncard < m →
      (τ.firstSideVertices F).ncard ≤ (τ.firstSideVertices H).ncard)
    {v : S} (hvV : v ∈ τ.Γ.V) (hvK : v ∈ K) (hvF : v ∉ F) :
    ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween τ.F₁ K →
      m ≤ (τ.Γ.V ∩ H).ncard := by
  have hlamF := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hF hFsub).1
  have hlamK := (areLaminarHoops_of_subset_cylinderBetween hlamF hK hKsub).1
  have hKall : K ⊆ cylinderBetween τ.F₁ τ.F₂ := hKsub.trans
    (cylinderBetween_subset_cylinderBetween τ.laminar hlamF
      (subset_cylinderBetween_left τ.laminar) hFsub)
  have hsuball := cylinderBetween_subset_cylinderBetween τ.laminar hlamK
    (subset_cylinderBetween_left τ.laminar) hKall
  intro H hH hNH hHsub
  by_contra hnot
  have hlt := τ.firstSideVertices_ncard_lt hF hK hH hFsub hKsub hHsub hvV hvK hvF
  have hle := hmin H hH hNH (hHsub.trans hsuball) (Nat.lt_of_not_ge hnot)
  exact (Nat.not_lt_of_ge hle) hlt

end GraphMinor.GM08
