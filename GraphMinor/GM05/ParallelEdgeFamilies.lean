module

public import GraphMinor.GM05.FreshParallelEdge
import GraphMinor.Surface.SurfaceGraph
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite families of parallel edge curves

For the actual copy drawings in GM V, (8.14), first choose one
parallel curve for every copy and edge label. Add the curves one at
a time. Each new curve avoids the original drawing and every earlier
curve away from the original vertices. Their interiors are therefore
pairwise disjoint before the vertex stars are replaced.
-/

public section
namespace GraphMinor.GM05
open Set Surface

private theorem exists_old_index {n : ℕ} (i : Fin (n+1)) (hi : i ≠ Fin.last n) :
    ∃ j : Fin n, j.castSucc = i :=
  Fin.lastCases (fun h ↦ (h rfl).elim) (fun j _ ↦ ⟨j,rfl⟩) i hi

private theorem exists_parallel_family_fin {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (D : Drawing S) (n : ℕ)
    (e : Fin n → Set S) (u v : Fin n → S)
    (hl : ∀ i, D.toGraph.IsLink (e i) (u i) (v i)) (huv : ∀ i, u i ≠ v i) :
    ∃ P : Fin n → Set S,
      (∀ i, IsLineWithEnds (P i) (u i) (v i) ∧ P i ∩ D.U = {u i,v i}) ∧
      ∀ i j, i ≠ j → P i ∩ P j ⊆ D.V := by
  classical
  let : T2Space S := hS.2.1
  induction n with
  | zero => exact ⟨Fin.elim0,fun i ↦ i.elim0,fun i ↦ i.elim0⟩
  | succ n ih =>
    obtain ⟨P,hP,hPP⟩ := ih (fun i ↦ e i.castSucc) (fun i ↦ u i.castSucc)
      (fun i ↦ v i.castSucc) (fun i ↦ hl i.castSucc) (fun i ↦ huv i.castSucc)
    have hFc : ∀ Q ∈ range P, IsClosed Q := by
      rintro Q ⟨i,rfl⟩
      exact (hP i).1.isCompact.isClosed
    have hFU : ∀ Q ∈ range P, Q ∩ D.U ⊆ D.V := by
      rintro Q ⟨i,rfl⟩
      rw [(hP i).2]
      exact pair_subset (hl i.castSucc).left_mem (hl i.castSucc).right_mem
    obtain ⟨Q,hQ,hQU,hQP⟩ := exists_fresh_parallel_edge hS D
      (hl (Fin.last n)) (huv (Fin.last n)) (finite_range P) hFc hFU
    refine ⟨Fin.snoc P Q,?_,?_⟩
    · intro i
      exact Fin.lastCases (by simpa using And.intro hQ hQU)
        (fun j ↦ by simpa using hP j) i
    · intro i j hij
      by_cases hi : i = Fin.last n
      · subst i
        obtain ⟨j,rfl⟩ := exists_old_index j (Ne.symm hij)
        simpa using hQP (P j) ⟨j,rfl⟩
      · obtain ⟨i,rfl⟩ := exists_old_index i hi
        by_cases hj : j = Fin.last n
        · subst j
          simpa only [Fin.snoc_castSucc,Fin.snoc_last,inter_comm] using hQP (P i) ⟨i,rfl⟩
        · obtain ⟨j,rfl⟩ := exists_old_index j hj
          have hij' : i ≠ j := fun he ↦ hij (congrArg Fin.castSucc he)
          simpa using hPP i j hij'

/-- Simultaneous parallel curves for finitely many edge labels,
including repeated labels of the same original edge, in GM V, (8.14),
page 113. Each curve meets the original drawing only at its two ends,
and distinct curves meet only at original vertices. -/
theorem exists_parallel_edge_curves {S ι : Type} [TopologicalSpace S] [Finite ι]
    (hS : IsClosedSurface S) (D : Drawing S) (e : ι → Set S) (u v : ι → S)
    (hl : ∀ i, D.toGraph.IsLink (e i) (u i) (v i)) (huv : ∀ i, u i ≠ v i) :
    ∃ P : ι → Set S,
      (∀ i, IsLineWithEnds (P i) (u i) (v i) ∧ P i ∩ D.U = {u i,v i}) ∧
      ∀ i j, i ≠ j → P i ∩ P j ⊆ D.V := by
  let : Fintype ι := Fintype.ofFinite ι
  let q := Fintype.equivFin ι
  obtain ⟨P,hP,hPP⟩ := exists_parallel_family_fin hS D (Fintype.card ι)
    (fun i ↦ e (q.symm i)) (fun i ↦ u (q.symm i)) (fun i ↦ v (q.symm i))
    (fun i ↦ hl (q.symm i)) (fun i ↦ huv (q.symm i))
  refine ⟨fun i ↦ P (q i),?_,?_⟩
  · intro i
    simpa using hP (q i)
  · intro i j hij
    exact hPP (q i) (q j) (fun he ↦ hij (q.injective he))

end GraphMinor.GM05
