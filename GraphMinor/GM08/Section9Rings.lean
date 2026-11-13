module

public import GraphMinor.GM08.Section9
import GraphMinor.GM07.CuffFrame
import GraphMinor.GM11.OArcCircuit

/-!
# Normal rings between successive nest circuits

To apply Graph Minors VII (9.4) in VIII (9.3), replace a nest circuit
by a parallel normal ring just outside it. The parallel disc construction
keeps the drawing vertices on its boundary and adds no drawing points
outside the original circuit disc.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The parallel ring used when applying VII (9.4) to the nest in VIII
(9.3), page 270. It lies between two successive circuit discs and has
exactly the vertices of the inner circuit on its boundary. -/
theorem DrawingNest.exists_parallel_disc {S : Type u} [TopologicalSpace S]
    [T2Space S] [CompactSpace S] [ConnectedSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) {i j : Fin s} (hij : i < j) :
    ∃ B : Set S, IsClosedDisc B ∧ (N.circuit i).ins ⊆ B ∧
      B ⊆ discInt (N.circuit j).ins ∧ D.IsNormal (discBd B) ∧
      D.V ∩ discBd B ⊆ (N.circuit i).U ∧
      ∀ x ∈ D.U, x ∈ B → x ∈ (N.circuit i).ins := by
  obtain ⟨C, -, hCD, hCU⟩ := GM11.exists_circuit_of_oArc
    (N.circuit i).isOArc_U (N.circuit i).U_sub_drawing
  have hbd : discBd (N.circuit i).ins = (id : S → S) '' C.U := by
    simpa only [image_id, hCU] using (N.circuit i).isInside.2.2.1
  obtain ⟨B, hB, hiB, hBj, hnormal, hV, hpoints⟩ :=
    GM07.exists_parallel_disc hCD (Homeomorph.refl S).isClosedEmbedding
      (N.circuit i).isInside.2.1 (N.circuit j).isInside.2.1
      (N.insideDisc_subset_discInt_of_lt hΔ hij) hbd
  refine ⟨B, hB, hiB, hBj, ?_, ?_, hpoints⟩
  · simpa only [Homeomorph.refl_apply, preimage_id_eq, id_eq] using hnormal
  · have heq : D.V ∩ discBd B = C.V := by
      simpa only [Homeomorph.refl_apply, preimage_id_eq, id_eq] using hV
    intro x hx
    rw [heq] at hx
    exact hCU ▸ C.V_subset_U hx

/-- Two separated portions of a nest give two disjoint normal rings.
The inner parallel disc lies in the interior of the outer one, and the
outer ring misses the boundary of the ambient disc. These are the
separation conditions in the application of VII (9.4) to VIII (9.3). -/
theorem DrawingNest.exists_two_parallel_discs {S : Type u} [TopologicalSpace S]
    [T2Space S] [CompactSpace S] [ConnectedSpace S]
    {D : Drawing S} {Δ : Set S} (hΔ : IsClosedDisc Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) {i j k l : Fin s}
    (hij : i < j) (hjk : j ≤ k) (hkl : k < l) :
    ∃ B₁ B₂ : Set S, IsClosedDisc B₁ ∧ IsClosedDisc B₂ ∧
      (N.circuit i).ins ⊆ B₁ ∧ B₁ ⊆ discInt (N.circuit j).ins ∧
      (N.circuit k).ins ⊆ B₂ ∧ B₂ ⊆ discInt (N.circuit l).ins ∧
      D.IsNormal (discBd B₁) ∧ D.IsNormal (discBd B₂) ∧
      B₁ ⊆ discInt B₂ ∧ Disjoint (discBd B₁) (discBd B₂) ∧
      Disjoint B₂ (discBd Δ) := by
  obtain ⟨B₁, hB₁, hi, hj, hn₁, -, -⟩ := N.exists_parallel_disc hΔ hij
  obtain ⟨B₂, hB₂, hk, hl, hn₂, -, -⟩ := N.exists_parallel_disc hΔ hkl
  have hB₂Δ : B₂ ⊆ Δ := hl.trans
    ((discInt_subset _).trans (N.circuit l).isInside.1)
  have hjk' : (N.circuit j).ins ⊆ (N.circuit k).ins :=
    (N.insideDisc_subset_of_le hΔ hjk).1
  have hinner : B₁ ⊆ discInt B₂ := hj.trans
    (discInt_mono_of_closedDisc hΔ (N.circuit j).isInside.1
      (N.circuit j).isInside.2.1 (hjk'.trans hk) hB₂Δ hB₂)
  refine ⟨B₁, B₂, hB₁, hB₂, hi, hj, hk, hl, hn₁, hn₂, hinner, ?_, ?_⟩
  · exact disjoint_left.mpr fun x hx₁ hx₂ =>
      (hinner (discBd_subset B₁ hx₁)).2 hx₂
  · exact ((N.circuit l).isInside.2.2.2.2.1).mono_left (by
      simpa only [discInt, (N.circuit l).isInside.2.2.1] using hl)

end GraphMinor.GM08
