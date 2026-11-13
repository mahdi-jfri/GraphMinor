module

public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.Finset.Card

/-!
# Face orbits of a cut rotation project to face orbits

Section 9 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) cuts the cuffed graph `G⁺`
along the linkage. Each linkage vertex gets two copies, and each copy keeps a block of consecutive
darts of the old rotation. The face orbit of `c̄ᵢ` in the cut graph `Kᵢ` should project onto the
face orbit of `c̄ᵢ` in `G⁺` (Lemma 10, combinatorial part). Here is the abstract reason.

Let `σ'` and `σ` be the rotations of the cut and old darts, `τ'` and `τ` the reversals, and `π` the
projection of a copy to its old dart, with `π ∘ τ' = τ ∘ π`. The face permutations are
`ψ = σ'⁻¹ τ'` and `φ = σ⁻¹ τ`. Call a cut dart *first* if it starts its block, and *last* if it
ends it. Three local facts:

* (C1) a dart that is not first has as predecessor the copy of its old predecessor;
* (C2) the predecessor of a first dart is last (it wraps around its block);
* (C3) the reverse of a last dart is first (the blocks fit together along the linkage and cuffs).

Then the cut darts whose reverse is first are closed under `ψ`: they form the outer boundary faces
of the cut graph. Every other cut orbit avoids them, and on it `π ∘ ψ = φ ∘ π`. So for a dart `c`
whose reverse is not first, `π (ψⁿ c) = φⁿ (π c)` for all `n` (`cut_orbit_projection`).
-/

public section

namespace GraphMinor.GM06

open Equiv

/-- **Projection of a cut face orbit.** With (C1)–(C3) on a finite set `S` of cut darts closed
under `σ'⁻¹` and `τ'`, a dart `c ∈ S` whose reverse is not first has `π (ψⁿ c) = φⁿ (π c)` for every
`n`, where `ψ = σ'⁻¹ τ'` and `φ = σ⁻¹ τ`. -/
theorem cut_orbit_projection {α β : Type*} (σ' τ' : Perm β) (σ τ : Perm α) (π : β → α)
    (S : Finset β) (F Λ : Set β)
    (hSσ : ∀ x ∈ S, σ'.symm x ∈ S) (hSτ : ∀ x ∈ S, τ' x ∈ S)
    (hπτ : ∀ x, π (τ' x) = τ (π x))
    (C1 : ∀ x ∈ S, x ∉ F → π (σ'.symm x) = σ.symm (π x))
    (C2 : ∀ x ∈ S, x ∈ F → σ'.symm x ∈ Λ)
    (C3 : ∀ y ∈ S, y ∈ Λ → τ' y ∈ F)
    {c : β} (hc : c ∈ S) (hcF : τ' c ∉ F) (n : ℕ) :
    (τ'.trans σ'.symm)^[n] c ∈ S ∧ τ' ((τ'.trans σ'.symm)^[n] c) ∉ F ∧
      π ((τ'.trans σ'.symm)^[n] c) = (τ.trans σ.symm)^[n] (π c) := by
  classical
  set ψ := τ'.trans σ'.symm
  have hψ : ∀ x, ψ x = σ'.symm (τ' x) := fun x => rfl
  have hSψ : ∀ x ∈ S, ψ x ∈ S := fun x hx => hSσ _ (hSτ x hx)
  -- the boundary darts
  set B := S.filter (fun d => τ' d ∈ F)
  have hBψ : ∀ d ∈ B, ψ d ∈ B := by
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    refine ⟨hSψ d hd.1, ?_⟩
    rw [hψ]
    exact C3 _ (hSψ d hd.1) (C2 _ (hSτ d hd.1) hd.2)
  have himage : B.image ψ = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      exact hBψ d hd
    · rw [Finset.card_image_of_injective _ ψ.injective]
  have hout : ∀ d ∈ S, τ' d ∉ F → τ' (ψ d) ∉ F := by
    intro d hd hdF hψF
    have hmem : ψ d ∈ B := Finset.mem_filter.mpr ⟨hSψ d hd, hψF⟩
    rw [← himage] at hmem
    obtain ⟨d', hd', heq⟩ := Finset.mem_image.mp hmem
    rw [ψ.injective heq] at hd'
    exact hdF (Finset.mem_filter.mp hd').2
  induction n with
  | zero => exact ⟨hc, hcF, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨hSψ _ h1, hout _ h1 h2, ?_⟩
    rw [hψ, C1 _ (hSτ _ h1) h2, hπτ, h3]
    rfl

end GraphMinor.GM06
