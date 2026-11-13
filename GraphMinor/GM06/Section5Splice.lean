module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5TailWalk
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
public import GraphMinor.GM11.Walks

/-!
# Joining a region path to the remaining linkage tail

In VI (5.1), page 129, the region path Qᵢ stops at tᵢ on Pᵢ₊₁.
Split Pᵢ₊₁ there and append its suffix to Qᵢ. The walks meet only at
the joining vertex, so the appended walk is simple. Its point set
is exactly the union of Qᵢ and the suffix, and it misses sᵢ₊₁.
The same construction works when the suffix is a single vertex.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u v

/-- Appending simple walks that share only their joining vertex
preserves simplicity. -/
theorem isSimple_append_at_only_common_vertex
    {α : Type u} {β : Type v} {G : Graph α β} {s x t : α}
    (A : GraphWalk G s x) (B : GraphWalk G x t)
    (hA : A.IsSimple) (hB : B.IsSimple)
    (hinter : ∀ y ∈ A.support, y ∈ B.support → y = x) :
    (A.append B).IsSimple := by
  have hxNot : x ∉ B.support.tail := by
    have hh := hB
    change B.support.Nodup at hh
    rw [B.support_eq_cons] at hh
    exact (List.nodup_cons.mp hh).1
  change (A.append B).support.Nodup
  rw [GraphWalk.support_append]
  refine List.nodup_append.mpr ⟨hA, List.Nodup.tail hB, ?_⟩
  intro y hy z hz heq
  subst z
  have hyB : y ∈ B.support := by
    rw [B.support_eq_cons]
    exact List.mem_cons_of_mem x hz
  exact hxNot (hinter y hy hyB ▸ hz)

/-- The drawing of an appended walk is the union of the two walk
point sets. -/
theorem walkDrawing_append_U
    {S : Type u} [TopologicalSpace S] [T1Space S] (G : Drawing S) {s x t : S}
    (A : GraphWalk G.toGraph s x) (B : GraphWalk G.toGraph x t) :
    (walkDrawing G (A.append B)).U = (walkDrawing G A).U ∪ (walkDrawing G B).U := by
  ext y
  simp only [mem_walkDrawing_U, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append, mem_union]
  constructor
  · rintro ((hA | hB) | ⟨e, heA | heB, hye⟩)
    · exact Or.inl (Or.inl hA)
    · exact Or.inr (Or.inl hB)
    · exact Or.inl (Or.inr ⟨e, heA, hye⟩)
    · exact Or.inr (Or.inr ⟨e, heB, hye⟩)
  · rintro ((hA | ⟨e, heA, hye⟩) | (hB | ⟨e, heB, hye⟩))
    · exact Or.inl (Or.inl hA)
    · exact Or.inr ⟨e, Or.inl heA, hye⟩
    · exact Or.inl (Or.inr hB)
    · exact Or.inr ⟨e, Or.inr heB, hye⟩

/-- Concatenate the path to a noninitial contact with the old linkage
tail, as in VI (5.1), page 129. The resulting path avoids the old
initial vertex. Terminal contacts use the singleton tail. -/
theorem exists_path_after_linkage_tail
    {G P Q : Drawing ClosedCylinder} {s₀ s x t : ClosedCylinder}
    (hPG : P.IsSubdrawing G) (hQG : Q.IsSubdrawing G)
    (hP : IsPathDrawing P s₀ t) (hQ : IsPathDrawing Q s x)
    (hx : x ∈ P.V) (hxs : x ≠ s₀) (hinter : Q.U ∩ P.U ⊆ {x}) :
    ∃ T R : Drawing ClosedCylinder,
      IsSection5Tail P T x t ∧ T.IsSubdrawing P ∧
      IsSubpathOf G R s t ∧ R.U = Q.U ∪ T.U ∧ s₀ ∉ R.U := by
  obtain ⟨B, hB, hTail, hs₀Not⟩ := exists_tail_walk_avoiding_start hP hx hxs
  let T := walkDrawing P B
  have hTP : T.IsSubdrawing P := walkDrawing_isSubdrawing P B
  obtain ⟨W, hW, hVQ, hEQ⟩ := hQ.1
  obtain ⟨A, hAS, hAE⟩ := hQG.exists_walk_up W
  obtain ⟨C, hCS, hCE⟩ := hPG.exists_walk_up B
  have hA : A.IsSimple := by simpa only [GraphWalk.IsSimple, hAS] using hW
  have hC : C.IsSimple := by simpa only [GraphWalk.IsSimple, hCS] using hB
  have hAQ : walkDrawing G A = Q := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hAS, hVQ]
    · rw [walkDrawing_E, hAE, hEQ]
  have hCT : walkDrawing G C = T := by
    apply Drawing.ext_of_V_E
    · simp only [T, walkDrawing_V, hCS]
    · simp only [T, walkDrawing_E, hCE]
  have hwalk : ∀ y ∈ A.support, y ∈ C.support → y = x := by
    intro y hyA hyC
    have hyQ : y ∈ Q.U := by
      rw [← hAQ, mem_walkDrawing_U]
      exact Or.inl hyA
    have hyT : y ∈ T.U := by
      rw [← hCT, mem_walkDrawing_U]
      exact Or.inl hyC
    exact mem_singleton_iff.mp (hinter ⟨hyQ, hTP.U_subset hyT⟩)
  have hsimple := isSimple_append_at_only_common_vertex A C hA hC hwalk
  have hsQ : s ∈ Q.U := Q.V_subset_U (isPathDrawing_end_vertices hQ).1
  have hsOff : s ∉ P.U := by
    intro hsP
    exact isPathDrawing_start_ne_end hQ (mem_singleton_iff.mp (hinter ⟨hsQ, hsP⟩))
  have hst : s ≠ t := by
    intro heq
    exact hsOff (heq.symm ▸ P.V_subset_U (isPathDrawing_end_vertices hP).2)
  have hRG := walkDrawing_isSubdrawing G (A.append C)
  have hRU : (walkDrawing G (A.append C)).U = Q.U ∪ T.U := by
    rw [walkDrawing_append_U, hAQ, hCT]
  refine ⟨T, walkDrawing G (A.append C), hTail, hTP,
    ⟨hRG, hRG.U_subset, isPathDrawing_walkDrawing_of_isSimple G hsimple hst⟩, hRU, ?_⟩
  rw [hRU]
  rintro (hs₀Q | hs₀T)
  · have hs₀P : s₀ ∈ P.U := P.V_subset_U (isPathDrawing_end_vertices hP).1
    exact hxs (mem_singleton_iff.mp (hinter ⟨hs₀Q, hs₀P⟩)).symm
  · exact hs₀Not hs₀T

end GraphMinor.GM06
