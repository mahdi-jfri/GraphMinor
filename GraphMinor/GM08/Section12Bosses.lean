module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section6
import Mathlib.Order.Preorder.Finite

/-!
# Choosing the bosses for a foundation in the disc case

The foundation used in VIII, Section 12 starts with the choice on
page 267. There are only finitely many boss edge sets because the
drawing has finitely many edges. Take the maximal such sets. The
trichotomy (6.7) makes distinct maximal sets disjoint, and every boss
edge set lies in a maximal one.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The maximal bosses used to start the foundation construction on
page 267 of VIII. Section 12 uses the resulting foundation for each
drawing in its sequence. This proves conditions (i) and (ii) there
from (6.7) and finiteness of the edge set. -/
theorem exists_maximal_boss_family {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    ∃ (t : ℕ) (C : Fin t → DiscCircuit D Δ),
      (∀ i, IsBoss D Δ (C i)) ∧
      Pairwise (fun i j => Disjoint (bossDelta D Δ (C i)) (bossDelta D Δ (C j))) ∧
      ∀ B : DiscCircuit D Δ, IsBoss D Δ B →
        ∃ i, bossDelta D Δ B ⊆ bossDelta D Δ (C i) := by
  classical
  let A : Set (Set (Set S)) := {E | ∃ C : DiscCircuit D Δ, IsBoss D Δ C ∧ bossDelta D Δ C = E}
  have hsub : ∀ C : DiscCircuit D Δ, bossDelta D Δ C ⊆ D.E := by
    intro C e he
    simp only [bossDelta, mem_iUnion] at he
    obtain ⟨F, _, he⟩ := he
    exact he.1
  have hAf : A.Finite := D.finite_edges.powerset.subset (by
    rintro E ⟨C, _, rfl⟩
    exact hsub C)
  let M : Set (Set (Set S)) := {E | Maximal (· ∈ A) E}
  have hMf : M.Finite := hAf.subset (fun _ h => h.1)
  have : Fintype M := hMf.fintype
  let e : Fin (Fintype.card M) ≃ M := (Fintype.equivFin M).symm
  have hex : ∀ E : M, ∃ C : DiscCircuit D Δ, IsBoss D Δ C ∧ bossDelta D Δ C = E.1 :=
    fun E => E.2.1
  choose C hCb hCE using hex
  refine ⟨Fintype.card M, fun i => C (e i), fun i => hCb (e i), ?_, ?_⟩
  · intro i j hij
    have hne : bossDelta D Δ (C (e i)) ≠ bossDelta D Δ (C (e j)) := by
      rw [hCE, hCE]
      exact fun heq => hij (e.injective (Subtype.ext heq))
    rcases theorem_6_7_proof hΔ (hCb (e i)) (hCb (e j)) with h | h | h
    · exfalso
      apply hne
      apply Subset.antisymm h
      have hmax := (e i).2
      rw [← hCE (e i)] at hmax
      exact hmax.2 ⟨C (e j), hCb (e j), rfl⟩ h
    · exfalso
      apply hne
      apply Subset.antisymm _ h
      have hmax := (e j).2
      rw [← hCE (e j)] at hmax
      exact hmax.2 ⟨C (e i), hCb (e i), rfl⟩ h
    · exact h
  · intro B hB
    obtain ⟨E, hBE, hmax⟩ := hAf.exists_le_maximal (show bossDelta D Δ B ∈ A from ⟨B, hB, rfl⟩)
    refine ⟨e.symm ⟨E, hmax⟩, ?_⟩
    dsimp only
    rw [e.apply_symm_apply, hCE]
    exact hBE

end GraphMinor.GM08
