module

public import GraphMinor.Surface.Dihedral
import GraphMinor.GM08.Section18CutOrbits
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Counting cut sectors by their ends

Every sector in a cut vertex orbit contains exactly two fixed side ends.
Partitioning the fixed ends by their image therefore gives twice the
number of sectors. This turns the orbit calculation into the vertex
fibre count used by VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Function Relation GraphMinor.Surface

/-- The number of fixed side ends in an original vertex orbit is twice
the number of its images after cutting. This is the local double count
in the proof of VIII (18.2), page 286. The map identifies exactly the
orbits of the two cut involutions. -/
theorem fixed_ends_ncard_eq_twice_cut_images {G H : Type*} [Finite G]
    {τ π σ : G → G} (hτ : Involutive τ) (hπ : Involutive π) (hσ : Involutive σ)
    (hfree : ∀ a, τ a ≠ a) (hs : ∀ a, σ a = a ∨ σ a = π a)
    {c : G} (hc : σ c = c) (f : G → H)
    (hf : ∀ a b, f a = f b ↔ TwoOrb τ σ a b) :
    {a | TwoOrb τ π c a ∧ σ a = a}.ncard =
      2 * (f '' {a | TwoOrb τ π c a}).ncard := by
  classical
  let A : Set G := {a | TwoOrb τ π c a}
  let F : Set G := {a | a ∈ A ∧ σ a = a}
  let B : Set H := f '' A
  have hB : B.Finite := (toFinite A).image f
  have hsub : ∀ a b, TwoOrb τ σ a b → TwoOrb τ π a b := by
    intro a b hab
    induction hab with
    | rel a b h =>
      rcases h with rfl | rfl
      · exact TwoOrb.left _ _ _
      · rcases hs a with heq | heq
        · rw [heq]; exact .refl _
        · rw [heq]; exact TwoOrb.right _ _ _
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  let fibre : H → Set G := fun b => {a | a ∈ F ∧ f a = b}
  have hcount : ∀ b ∈ B, (fibre b).ncard = 2 := by
    rintro b ⟨g, hg, rfl⟩
    have heq : fibre (f g) = {z | TwoOrb τ σ g z ∧ σ z = z} := by
      ext z
      constructor
      · rintro ⟨⟨hzA, hz⟩, heq⟩
        exact ⟨(hf g z).mp heq.symm, hz⟩
      · rintro ⟨hgz, hz⟩
        exact ⟨⟨EqvGen.trans _ _ _ hg (hsub g z hgz), hz⟩, (hf g z).mpr hgz |>.symm⟩
    rw [heq]
    exact cut_orbit_fixed_ends_ncard hτ hπ hσ hfree hs hc hg
  have hunion : F = ⋃ b ∈ B, fibre b := by
    ext a
    constructor
    · intro ha
      exact mem_iUnion₂.mpr ⟨f a, mem_image_of_mem f ha.1, ha, rfl⟩
    · intro ha
      obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp ha
      exact hab.1
  have hdis : B.PairwiseDisjoint fibre := by
    intro b hb d hd hbd
    exact disjoint_left.mpr (fun a ha ha' => hbd (ha.2.symm.trans ha'.2))
  change F.ncard = 2 * B.ncard
  rw [hunion, hB.ncard_biUnion (fun _ _ => toFinite _) hdis]
  rw [finsum_mem_eq_finite_toFinset_sum _ hB]
  have hsum : (∑ b ∈ hB.toFinset, (fibre b).ncard) = ∑ _b ∈ hB.toFinset, 2 := by
    apply Finset.sum_congr rfl
    intro b hb
    exact hcount b (hB.mem_toFinset.mp hb)
  rw [hsum]
  simp only [Finset.sum_const, smul_eq_mul]
  rw [Set.ncard_eq_toFinset_card B hB, Nat.mul_comm]

end GraphMinor.GM08
