module

public import GraphMinor.GM01.CombReflection
public import GraphMinor.GM01.CombShiftRanges
import GraphMinor.GM01.CombInteriorForkReflection
import GraphMinor.GM01.SubdivisionReindex

/-!
# Orienting the layer subdivision by reflection

After Graph Minors I, (4.9), page 58, reverse `D` if its first
attachment lies in its second end. Reflection reindexes the actual
centres and replacing paths, preserving their cover and intersections.
Its first two source cells are the last two original cells, so the
reflected first end is exactly the original second end. Thus the
first-end orientation used in (4.10) can always be chosen.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- Spine reflection on the actual vertex type of a comb. -/
@[expose] def combReflectionEmbedding {γ L : ℕ} : (pathComb γ L).verts ↪ (pathComb γ L).verts where
  toFun v := ⟨combReflectVertex v.val, combReflectVertex_mem v.property⟩
  inj' := fun _ _ h ↦ Subtype.ext (combReflectVertex_injective (congrArg Subtype.val h))

/-- Reflecting the actual source vertices twice fixes every vertex. -/
theorem combReflectionEmbedding_involutive {γ L : ℕ} :
    Involutive (combReflectionEmbedding (γ := γ) (L := L)) := by
  intro v
  exact Subtype.ext (combReflectVertex_involutive v.val)

/-- Reflection preserves source adjacency. -/
theorem combReflectionEmbedding_adj {γ L : ℕ} {u v : (pathComb γ L).verts}
    (huv : (pathComb γ L).coe.Adj u v) :
    (pathComb γ L).coe.Adj (combReflectionEmbedding u) (combReflectionEmbedding v) :=
  combReflectVertex_adj huv

/-- The actual source edge reindexing induced by spine reflection. -/
@[expose] def combReflectionEdges {γ L : ℕ} :
    (pathComb γ L).coe.edgeSet ↪ (pathComb γ L).coe.edgeSet :=
  subdivisionEmbeddingEdges combReflectionEmbedding combReflectionEmbedding_adj

/-- Reflecting source edges twice fixes each edge. -/
theorem combReflectionEdges_involutive {γ L : ℕ} :
    Involutive (combReflectionEdges (γ := γ) (L := L)) :=
  subdivisionEmbeddingEdges_involutive _ _ combReflectionEmbedding_involutive

/-- The first end of the reflected subdivision is exactly its original
second end, justifying the orientation choice after GM01 (4.9), page 58. -/
theorem combFirstEndSupport_reflect_eq_second {α β : Type*} {γ L : ℕ} (hL : 2 ≤ L)
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β) :
    combFirstEndSupport hL (fun v ↦ c (combReflectionEmbedding v)) (fun e ↦ P (combReflectionEdges e)) =
      combSecondEndSupport hL c P := by
  let r := combReflectionEmbedding (γ := γ) (L := L)
  let E := combReflectionEdges (γ := γ) (L := L)
  have hidx : ∀ v : (pathComb γ L).verts,
      (pathCombSpineIndex (r v).val).val = L - ((pathCombSpineIndex v.val).val + 1) :=
    fun v ↦ combReflectVertex_spineIndex v.val
  have hInv : Involutive r := combReflectionEmbedding_involutive
  have hEInv : Involutive E := combReflectionEdges_involutive
  ext x
  change x ∈ combSegmentSupport (fun v ↦ c (r v)) (fun e ↦ P (E e)) 0 (by omega : 0 + 2 ≤ L) ↔
    x ∈ combSegmentSupport c P (L - 2) (by omega : L - 2 + 2 ≤ L)
  rw [mem_combSegmentSupport_iff, mem_combSegmentSupport_iff]
  constructor
  · rintro (⟨v, hlo, hhi, hv⟩ | ⟨e, hxe, hEnds⟩)
    · have hi := hidx v
      have hvL := (pathCombSpineIndex v.val).isLt
      exact Or.inl ⟨r v, by omega, by omega, hv⟩
    · refine Or.inr ⟨E e, hxe, ?_⟩
      intro u hu
      change u ∈ Sym2.map r e.val at hu
      obtain ⟨v, hv, hrv⟩ := Sym2.mem_map.mp hu
      have h := hEnds v hv
      have hi := hidx v
      have hvL := (pathCombSpineIndex v.val).isLt
      rw [← hrv]
      exact ⟨by omega, by omega⟩
  · rintro (⟨v, hlo, hhi, hv⟩ | ⟨e, hxe, hEnds⟩)
    · have hi := hidx v
      have hvL := (pathCombSpineIndex v.val).isLt
      refine Or.inl ⟨r v, Nat.zero_le _, by omega, ?_⟩
      rw [hInv v]
      exact hv
    · refine Or.inr ⟨E e, ?_, ?_⟩
      · rw [hEInv e]
        exact hxe
      · intro u hu
        change u ∈ Sym2.map r e.val at hu
        obtain ⟨v, hv, hrv⟩ := Sym2.mem_map.mp hu
        have h := hEnds v hv
        have hi := hidx v
        have hvL := (pathCombSpineIndex v.val).isLt
        rw [← hrv]
        exact ⟨Nat.zero_le _, by omega⟩

/-- The explicit orientation choice after GM01 (4.9), page 58. The
centres and paths either stay as given or are reflected. All subdivision
conditions are proved for the chosen data, and the attachment then lies
in its first end. -/
theorem exists_first_end_orientation {α β : Type*} {γ L : ℕ} (hL : 2 ≤ L)
    {D : Graph α β} (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    {x : α} (hx : x ∈ combFirstEndSupport hL c P ∪ combSecondEndSupport hL c P) :
    ∃ c' : (pathComb γ L).verts → α, ∃ P' : (pathComb γ L).coe.edgeSet → Graph α β,
      Injective c' ∧ V(D) = range c' ∪ ⋃ e, V(P' e) ∧
      (∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
        IsGraphPathWithEnds D (P' e) (c' a) (c' b) ∧ V(P' e) ∩ range c' = {c' a,c' b}) ∧
      (∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
        V(P' e) ∩ V(P' f) ⊆ range c' ∧ Disjoint E(P' e) E(P' f)) ∧
      x ∈ combFirstEndSupport hL c' P' := by
  rcases hx with hx | hx
  · exact ⟨c, P, hc, hV, hPaths, hInter, hx⟩
  · let r := combReflectionEmbedding (γ := γ) (L := L)
    let E := combReflectionEdges (γ := γ) (L := L)
    have hdata := subdivision_reindex r combReflectionEmbedding_adj combReflectionEmbedding_involutive
      c P hV hPaths hInter
    refine ⟨(fun v ↦ c (r v)), (fun e ↦ P (E e)), hc.comp r.injective, hdata.1,
      hdata.2.1, hdata.2.2, ?_⟩
    rw [combFirstEndSupport_reflect_eq_second hL c P]
    exact hx

end GraphMinor.GM01
