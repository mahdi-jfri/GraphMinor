module

public import GraphMinor.GM08.Defs6to18
public import GraphMinor.GM11.Defs
import GraphMinor.GM08.Section12LoopPetals
import GraphMinor.GM08.Section12LoopDrawing
import GraphMinor.GM08.Section12DrawingUnion
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM11.Walks

/-!
# Replacing the loops by their empty petals

Keep all vertices and all non-loop edges of the original drawing.
Replace each loop by the one-edge drawing on its chosen petal boundary.
The finite union lemma makes these into a proper drawing with exactly
the same vertices. The exact new edge set and the loop closures are
recorded for the graph isomorphism and cellularity checks in the disc
induction of VIII, Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Assemble the petal replacement of the loops for the cellular
drawing used in VIII, Section 12, page 274. Vertices stay fixed, and
only the loop edges are replaced. -/
theorem exists_loop_replacement {S : Type u} [TopologicalSpace S] [T1Space S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S) (hprop : D.IsProper) :
    ∃ (v : {e : Set S // e ∈ D.E ∧ D.IsLoop e} → S)
      (E : {e : Set S // e ∈ D.E ∧ D.IsLoop e} → Set S) (H : Drawing S),
      (∀ i, closure i.1 ∩ D.V = {v i} ∧ IsClosedDisc (E i) ∧
        v i ∈ discBd (E i) ∧ E i ∩ D.U = {v i} ∧
        closure (discBd (E i) \ {v i}) = discBd (E i)) ∧
      (∀ i j, i ≠ j → E i ∩ E j ⊆ {v i} ∩ {v j}) ∧
      H.V = D.V ∧
      H.E = {e ∈ D.E | ¬ D.IsLoop e} ∪ range (fun i => discBd (E i) \ {v i}) ∧
      H.U = (D.span D.V {e ∈ D.E | ¬ D.IsLoop e}).U ∪ ⋃ i, discBd (E i) ∧
      H.IsProper := by
  classical
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  let L := {e : Set S // e ∈ D.E ∧ D.IsLoop e}
  have : Finite L := (D.finite_edges.subset (sep_subset _ _)).to_subtype
  have hex : ∀ i : L, ∃ v : S, closure i.1 ∩ D.V = {v} := fun i => i.2.2.2
  choose v hcap using hex
  obtain ⟨E, hE, hEE⟩ := exists_loop_petal_family hS D (fun i : L => i.1) v
    (fun i => i.2.1) hcap
  choose P hPU hPV hPE hPcl using fun i =>
    exists_one_loop_drawing (hE i).1.isOArc_discBd (hE i).2.1
  let N : Set (Set S) := {e ∈ D.E | ¬ D.IsLoop e}
  let D₀ := D.span D.V N
  have hD₀ : D₀.IsSubdrawing D := Drawing.span_isSubdrawing D _ _
  have hV₀ : D₀.V = D.V := by
    apply Subset.antisymm (D.spanV_subset _ _)
    exact fun x hx => .inl ⟨hx, hx⟩
  have hE₀ : D₀.E = N := by
    rw [D.span_E]
    exact inter_eq_left.mpr (sep_subset _ _)
  have hvD : ∀ i, v i ∈ D.V := by
    intro i
    have hvpair : v i ∈ closure i.1 ∩ D.V := (hcap i).symm ▸ mem_singleton (v i)
    exact hvpair.2
  have hPsub : ∀ i, (P i).V ⊆ D₀.V := by
    intro i
    rw [hPV i, hV₀]
    exact singleton_subset_iff.mpr (hvD i)
  have hPD : ∀ i, (P i).U ∩ D₀.U ⊆ (P i).V := by
    intro i x hx
    rw [hPV i]
    exact (hE i).2.2.1 ▸ And.intro
      (discBd_subset _ (hPU i ▸ hx.1)) (hD₀.U_subset hx.2)
  have hPP : Pairwise fun i j => (P i).U ∩ (P j).U ⊆ D₀.V := by
    intro i j hij x hx
    rw [hV₀]
    have hxij := hEE i j hij ⟨discBd_subset _ (hPU i ▸ hx.1), discBd_subset _ (hPU j ▸ hx.2)⟩
    exact mem_singleton_iff.mp hxij.1 ▸ hvD i
  have hD₀prop : D₀.IsProper := by
    intro x hx
    rw [hV₀]
    exact hprop ⟨hx.1, hD₀.U_subset hx.2⟩
  have hPprop : ∀ i, (P i).IsProper := by
    intro i x hx
    rw [hPV i]
    exact (hE i).2.2.2 ⟨discBd_subset _ (hPU i ▸ hx.2), hx.1⟩
  obtain ⟨H, hHV, hHE, hHU, hHp⟩ :=
    exists_drawing_union_at_vertices D₀ P hPsub hPD hPP hD₀prop hPprop
  refine ⟨v, E, H, fun i => ⟨hcap i, (hE i).1, (hE i).2.1, (hE i).2.2.1, hPcl i⟩,
    hEE, hHV.trans hV₀, ?_, ?_, hHp⟩
  · rw [hHE, hE₀]
    congr 1
    ext e
    simp only [mem_iUnion, hPE, mem_singleton_iff, mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  · rw [hHU]
    congr 1
    exact iUnion_congr fun i => hPU i

end GraphMinor.GM08
