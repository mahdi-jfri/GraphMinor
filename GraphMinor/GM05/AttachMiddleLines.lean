module

public import GraphMinor.Surface.Defs
import GraphMinor.GM16.FiniteLineDrawing
import GraphMinor.GM11.RadialBasics
import GraphMinor.GM11.Walks
import GraphMinor.Surface.ChartCells
import GraphMinor.Surface.SurfaceGraph

/-!
# Attaching the disjoint edge middles

For GM V, (8.14), first planarize the stars. Each remaining middle
line meets that drawing only at its two port vertices. Draw these
lines without subdivision, then glue the two drawings along their
ports. The stars remain subdrawings and every middle is a single
edge, disjoint from the edges of the star drawing.
-/

public section
namespace GraphMinor.GM05
open Set Surface Graph

/-- Glue disjoint middle lines to the planarized star drawing in
GM V, (8.14), page 113, preserving each middle as one edge. -/
theorem exists_drawing_attach_middle_lines {S ι : Type*} [TopologicalSpace S]
    [T2Space S] [Finite ι] (D : Drawing S) (p q : ι → S) (M : ι → Set S)
    (hM : ∀ a, IsLineWithEnds (M a) (p a) (q a)) (hne : ∀ a, p a ≠ q a)
    (hp : ∀ a, p a ∈ D.V) (hq : ∀ a, q a ∈ D.V)
    (hMU : ∀ a, M a ∩ D.U = {p a,q a})
    (hdis : Pairwise (fun a b ↦ Disjoint (M a) (M b))) :
    ∃ H : Drawing S, D.IsSubdrawing H ∧ H.V = D.V ∧ H.U = D.U ∪ ⋃ a, M a ∧
      (∀ a, H.toGraph.IsLink (M a \ {p a,q a}) (p a) (q a)) ∧
      Disjoint D.E (range fun a ↦ M a \ {p a,q a}) := by
  classical
  have hMV : ∀ a, M a ∩ D.V = {p a,q a} := by
    intro a
    apply subset_antisymm
    · exact (inter_subset_inter_right _ D.V_subset_U).trans (hMU a).subset
    · rintro x (rfl | rfl)
      · exact ⟨(hM a).left_mem,hp a⟩
      · exact ⟨(hM a).right_mem,hq a⟩
  obtain ⟨K,hKU,hKV,hKE⟩ := GM16.exists_drawing_of_finite_lines
    (toFinite (univ : Set ι)) D.finite_V p q M
    (fun a _ ↦ hM a) (fun a _ ↦ hne a) (fun a _ ↦ hMV a)
    (fun a _ b _ hab ↦ (hdis hab).inter_eq ▸ empty_subset D.V)
  simp only [mem_univ,iUnion_true] at hKU hKE
  have hglue : D.U ∩ K.U ⊆ D.V ∩ K.V := by
    rintro x ⟨hxD,hxK⟩
    rw [hKU] at hxK
    have hxV : x ∈ D.V := by
      rcases hxK with hxV | hxM
      · exact hxV
      · obtain ⟨a,hxa⟩ := mem_iUnion.mp hxM
        have hh : x ∈ ({p a,q a} : Set S) := hMU a ▸ ⟨hxa,hxD⟩
        exact hh.elim (fun he ↦ he ▸ hp a) (fun he ↦ he ▸ hq a)
    exact ⟨hxV,hKV.symm ▸ hxV⟩
  let H := D.glue K hglue
  have hHV : H.V = D.V := by change D.V ∪ K.V = D.V; rw [hKV,union_self]
  have hHU : H.U = D.U ∪ ⋃ a, M a := by
    change D.U ∪ K.U = _
    rw [hKU,← union_assoc,union_eq_self_of_subset_right D.V_subset_U]
  have hsub : D.IsSubdrawing H := by
    refine ⟨fun x hx ↦ hHV.symm ▸ hx,?_⟩
    change D.E ⊆ (D.glue K hglue).E
    rw [Drawing.glue_E]
    exact subset_union_left
  have hmidK : ∀ a, M a \ {p a,q a} ∈ K.E := by
    intro a
    rw [hKE]
    exact ⟨a,mem_univ _,rfl⟩
  have hmidH : ∀ a, M a \ {p a,q a} ∈ H.E := by
    intro a
    change M a \ {p a,q a} ∈ (D.glue K hglue).E
    rw [Drawing.glue_E]
    exact Or.inr (hmidK a)
  have hcl : ∀ a, closure (M a \ {p a,q a}) = M a := fun a ↦
    subset_antisymm (closure_minimal sdiff_subset (hM a).isCompact.isClosed) (hM a).subset_closure_diff
  refine ⟨H,hsub,hHV,hHU,?_,?_⟩
  · intro a
    refine ⟨hmidH a,hHV.symm ▸ hp a,hHV.symm ▸ hq a,?_⟩
    rw [hcl a,hHV,hMV a]
  · apply disjoint_left.mpr
    rintro e he ⟨a,rfl⟩
    obtain ⟨x,hx⟩ := (hmidK a).1
    have hxU := (he.2.1 hx).1
    have hh : x ∈ ({p a,q a} : Set S) := hMU a ▸ ⟨hx.1,hxU⟩
    exact hx.2 hh

/-- Distinct disjoint middle lines give distinct representing edges. -/
theorem middle_open_edge_injective {S ι : Type*} [TopologicalSpace S]
    (H : Drawing S) (p q : ι → S) (M : ι → Set S)
    (hl : ∀ a, H.toGraph.IsLink (M a \ {p a,q a}) (p a) (q a))
    (hdis : Pairwise (fun a b ↦ Disjoint (M a) (M b))) :
    Function.Injective (fun a ↦ M a \ {p a,q a}) := by
  intro a b he
  change M a \ {p a,q a} = M b \ {p b,q b} at he
  by_contra hab
  obtain ⟨x,hx⟩ := (hl a).edge_mem.1
  have hy : x ∈ M b \ {p b,q b} := he ▸ hx
  exact disjoint_left.mp (hdis hab) hx.1 hy.1

end GraphMinor.GM05
