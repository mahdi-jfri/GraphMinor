module

public import GraphMinor.GM08.Section15Defs
import GraphMinor.GM07.CylinderWheel

/-!
# Spokes in the caps of a cylinder

To push the roots of a graft off the boundary in the proof of (17.2), we cap
the cylinder `S` to a sphere, choose a smaller disc `Eᵢ` inside each cap `Dᵢ`,
and join each boundary point `x` in a given set `P` to a point `q x` on the
boundary of the small disc by a spoke. Spokes of different points are disjoint,
meet the image of `S` only at their start, and meet the small discs only at
their end. This is the wheel of `GM07.exists_wheel`, taken in both caps.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- Two small discs inside the caps of a capped cylinder, and a spoke from each
point of `P` to the boundary of the small disc in its cap. -/
structure CollarWheel (cap : CylinderSphereCap S) (P : Set S) where
  /-- The small disc in the first cap. -/
  E₁ : Set cap.Z
  /-- The small disc in the second cap. -/
  E₂ : Set cap.Z
  /-- The end of the spoke starting at a point. -/
  q : cap.Z → cap.Z
  /-- The spoke starting at a point. -/
  ℓ : cap.Z → Set cap.Z
  isClosedDisc_E₁ : IsClosedDisc E₁
  isClosedDisc_E₂ : IsClosedDisc E₂
  E₁_subset : E₁ ⊆ discInt cap.D₁
  E₂_subset : E₂ ⊆ discInt cap.D₂
  line : ∀ x ∈ P, IsLineWithEnds (ℓ (cap.j x)) (cap.j x) (q (cap.j x))
  ne : ∀ x ∈ P, cap.j x ≠ q (cap.j x)
  inter_range : ∀ x ∈ P, ℓ (cap.j x) ∩ range cap.j = {cap.j x}
  inter_E : ∀ x ∈ P, ℓ (cap.j x) ∩ (E₁ ∪ E₂) = {q (cap.j x)}
  q_mem₁ : ∀ x ∈ P, x ∈ cap.C₁ → q (cap.j x) ∈ discBd E₁
  q_mem₂ : ∀ x ∈ P, x ∈ cap.C₂ → q (cap.j x) ∈ discBd E₂
  disjoint : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → Disjoint (ℓ (cap.j x)) (ℓ (cap.j y))

/-- Spokes exist for every set of boundary points. -/
theorem CylinderSphereCap.exists_collarWheel (cap : CylinderSphereCap S) {P : Set S}
    (hP : P ⊆ bd S) : Nonempty (CollarWheel cap P) := by
  classical
  have : T2Space cap.Z := cap.t2Space_Z
  have hA₁ : cap.j '' (P ∩ cap.C₁) ⊆ discBd cap.D₁ := by
    rw [cap.discBd_D₁]; exact image_mono inter_subset_right
  have hA₂ : cap.j '' (P ∩ cap.C₂) ⊆ discBd cap.D₂ := by
    rw [cap.discBd_D₂]; exact image_mono inter_subset_right
  obtain ⟨E₁, q₁, ℓ₁, hE₁, hE₁D, hw₁, hd₁⟩ := GM07.exists_wheel cap.isClosedDisc_D₁ hA₁
  obtain ⟨E₂, q₂, ℓ₂, hE₂, hE₂D, hw₂, hd₂⟩ := GM07.exists_wheel cap.isClosedDisc_D₂ hA₂
  let q : cap.Z → cap.Z := fun z => if z ∈ cap.D₁ then q₁ z else q₂ z
  let ℓ : cap.Z → Set cap.Z := fun z => if z ∈ cap.D₁ then ℓ₁ z else ℓ₂ z
  have hjD₁ : ∀ x, x ∈ cap.C₁ → cap.j x ∈ cap.D₁ := fun x hx =>
    discBd_subset _ (cap.discBd_D₁ ▸ mem_image_of_mem cap.j hx)
  have hjD₂ : ∀ x, x ∈ cap.C₂ → cap.j x ∈ cap.D₂ := fun x hx =>
    discBd_subset _ (cap.discBd_D₂ ▸ mem_image_of_mem cap.j hx)
  have hE₁₁ : E₁ ⊆ cap.D₁ := hE₁D.trans (discInt_subset _)
  have hE₂₂ : E₂ ⊆ cap.D₂ := hE₂D.trans (discInt_subset _)
  -- each point of `P` is on exactly one cuff, and its spoke is the one of that cap
  have hcase : ∀ x ∈ P,
      (x ∈ cap.C₁ ∧ q (cap.j x) = q₁ (cap.j x) ∧ ℓ (cap.j x) = ℓ₁ (cap.j x)) ∨
      (x ∈ cap.C₂ ∧ q (cap.j x) = q₂ (cap.j x) ∧ ℓ (cap.j x) = ℓ₂ (cap.j x)) := by
    intro x hx
    rcases (cap.bd_eq ▸ hP hx : x ∈ cap.C₁ ∪ cap.C₂) with h | h
    · exact .inl ⟨h, by simp [q, hjD₁ x h], by simp [ℓ, hjD₁ x h]⟩
    · have hn : cap.j x ∉ cap.D₁ := fun h' =>
        disjoint_left.mp cap.disjoint_D h' (hjD₂ x h)
      exact .inr ⟨h, by simp [q, hn], by simp [ℓ, hn]⟩
  -- the spoke of a point of `P` with its properties
  have hspoke : ∀ x ∈ P, IsLineWithEnds (ℓ (cap.j x)) (cap.j x) (q (cap.j x)) ∧
      cap.j x ≠ q (cap.j x) ∧ ℓ (cap.j x) ∩ range cap.j = {cap.j x} ∧
      ℓ (cap.j x) ∩ (E₁ ∪ E₂) = {q (cap.j x)} ∧
      (x ∈ cap.C₁ → q (cap.j x) ∈ discBd E₁ ∧ ℓ (cap.j x) ⊆ cap.D₁) ∧
      (x ∈ cap.C₂ → q (cap.j x) ∈ discBd E₂ ∧ ℓ (cap.j x) ⊆ cap.D₂) := by
    intro x hx
    rcases hcase x hx with ⟨h, hq, hℓ⟩ | ⟨h, hq, hℓ⟩
    · obtain ⟨hqE, hL, hne, hsub, hbd, hE⟩ := hw₁ (cap.j x) ⟨x, ⟨hx, h⟩, rfl⟩
      rw [hq, hℓ]
      refine ⟨hL, hne, ?_, ?_, fun _ => ⟨hqE, hsub⟩, fun h' =>
        absurd h' (disjoint_left.mp cap.disjoint_cuffs h)⟩
      · apply subset_antisymm
        · rintro z ⟨hz, hzr⟩
          have hzb : z ∈ discBd cap.D₁ := cap.discBd_D₁ ▸ cap.inter_D₁ ▸ ⟨hzr, hsub hz⟩
          exact hbd.subset ⟨hz, hzb⟩
        · rintro _ rfl
          obtain ⟨φ, h0, -⟩ := hL
          refine ⟨?_, x, rfl⟩
          have h := (φ 0).2
          rwa [h0] at h
      · rw [inter_union_distrib_left, hE]
        have : ℓ₁ (cap.j x) ∩ E₂ = ∅ := by
          refine eq_empty_iff_forall_notMem.mpr fun z ⟨hz, hz₂⟩ => ?_
          exact disjoint_left.mp cap.disjoint_D (hsub hz) (hE₂₂ hz₂)
        rw [this, union_empty]
    · obtain ⟨hqE, hL, hne, hsub, hbd, hE⟩ := hw₂ (cap.j x) ⟨x, ⟨hx, h⟩, rfl⟩
      rw [hq, hℓ]
      refine ⟨hL, hne, ?_, ?_, fun h' =>
        absurd h (disjoint_left.mp cap.disjoint_cuffs h'), fun _ => ⟨hqE, hsub⟩⟩
      · apply subset_antisymm
        · rintro z ⟨hz, hzr⟩
          have hzb : z ∈ discBd cap.D₂ := cap.discBd_D₂ ▸ cap.inter_D₂ ▸ ⟨hzr, hsub hz⟩
          exact hbd.subset ⟨hz, hzb⟩
        · rintro _ rfl
          obtain ⟨φ, h0, -⟩ := hL
          refine ⟨?_, x, rfl⟩
          have h := (φ 0).2
          rwa [h0] at h
      · rw [inter_union_distrib_left, hE]
        have : ℓ₂ (cap.j x) ∩ E₁ = ∅ := by
          refine eq_empty_iff_forall_notMem.mpr fun z ⟨hz, hz₁⟩ => ?_
          exact disjoint_left.mp cap.disjoint_D (hE₁₁ hz₁) (hsub hz)
        rw [this, empty_union]
  refine ⟨⟨E₁, E₂, q, ℓ, hE₁, hE₂, hE₁D, hE₂D, fun x hx => (hspoke x hx).1,
    fun x hx => (hspoke x hx).2.1, fun x hx => (hspoke x hx).2.2.1,
    fun x hx => (hspoke x hx).2.2.2.1, fun x hx h => ((hspoke x hx).2.2.2.2.1 h).1,
    fun x hx h => ((hspoke x hx).2.2.2.2.2 h).1, ?_⟩⟩
  intro x hx y hy hxy
  have hjxy : cap.j x ≠ cap.j y := fun h => hxy (cap.inj h)
  rcases hcase x hx with ⟨h₁, -, hℓx⟩ | ⟨h₁, -, hℓx⟩ <;>
    rcases hcase y hy with ⟨h₂, -, hℓy⟩ | ⟨h₂, -, hℓy⟩ <;> rw [hℓx, hℓy]
  · exact hd₁ _ ⟨x, ⟨hx, h₁⟩, rfl⟩ _ ⟨y, ⟨hy, h₂⟩, rfl⟩ hjxy
  · exact cap.disjoint_D.mono ((hw₁ _ ⟨x, ⟨hx, h₁⟩, rfl⟩).2.2.2.1)
      ((hw₂ _ ⟨y, ⟨hy, h₂⟩, rfl⟩).2.2.2.1)
  · exact cap.disjoint_D.symm.mono ((hw₂ _ ⟨x, ⟨hx, h₁⟩, rfl⟩).2.2.2.1)
      ((hw₁ _ ⟨y, ⟨hy, h₂⟩, rfl⟩).2.2.2.1)
  · exact hd₂ _ ⟨x, ⟨hx, h₁⟩, rfl⟩ _ ⟨y, ⟨hy, h₂⟩, rfl⟩ hjxy

end GraphMinor.GM08
