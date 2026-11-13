module

public import GraphMinor.GM21.Section6LastLines
import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM11.Walks

/-!
# Graph Minors XXI, (6.3), the last step: the jumps cover the drawing

Graph Minors XXI, Section 6 (page 24 of the preprint): "If $L$ is exhaustive, then every edge of
$\Gamma$ is in a unique $\Sigma$-jump, and any two $\Sigma$-jumps have no common vertices except
possibly one end."

We read this in the drawing. Let `B` be the set of vertices of `Γ` in `bd(Σ)`, and let `J` be a
jump. The rest of the drawing is `otherPart Γ ιV ιE J`: the closures of the edges not in `J`,
and the vertices not in `J`. It is closed.
* `U_subset_jumpLine_union`: `U(Γ)` is the line of `J` together with the rest.
* `jumpLine_inter_otherPart_subset`: the line of `J` meets the rest only in the ends of `J`. An
  inner vertex of `J` is not in `B`, so both of its edges are in `J`.
* `jumpLine_subset_otherPart`: the line of a different jump lies in the rest, since two jumps with a
  common edge are equal.
* `jumpLine_inter_bd_subset`: the line of `J` meets `bd(Σ)` only in the ends of `J`.
* `U_subset_bd_union_jumpLine`: `U(Γ)` lies in `bd(Σ)` and the lines of the jumps. A vertex off
  `bd(Σ)` has two edges, and each edge is in a jump.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Function Hypergraph GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- The rest of the drawing besides the jump `J`: the closures of the edges `e` of `Γ` with
`ιE e ∉ E(J)`, and the vertices `z` of `Γ` with `ιV z ∉ V(J)`. -/
def otherPart (Γ : Drawing S) (ιV : S → α) (ιE : Set S → β) (J : Hypergraph α β) : Set S :=
  (⋃ f ∈ {f ∈ Γ.E | ιE f ∉ J.edgeSet}, closure f) ∪ {z ∈ Γ.V | ιV z ∉ J.vertexSet}

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {J K : Hypergraph α β}

theorem isClosed_otherPart [T1Space S] : IsClosed (otherPart Γ ιV ιE J) :=
  ((Finite.subset Γ.finite_edges (sep_subset _ _)).isClosed_biUnion fun _ _ => isClosed_closure).union
    (Finite.subset Γ.finite_V (sep_subset _ _)).isClosed

/-- The vertices of `Γ` in the closure of an edge `e` of `Γ` are those mapped to ends of `ιE e`. -/
theorem inc_of_mem_closure (hiso : IsDrawingIso Γ Γ_sub ιV ιE) {e : Set S} (he : e ∈ Γ.E) {z : S}
    (hz : z ∈ Γ.V) (hze : z ∈ closure e) : Γ_sub.Inc (ιE e) (ιV z) :=
  (hiso.inc_iff e he z hz).2 hze

variable [T2Space S]

/-- `U(Γ)` is the line of the jump `J` together with the rest of the drawing. -/
theorem U_subset_jumpLine_union (hiso : IsDrawingIso Γ Γ_sub ιV ιE)
    (h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2) (hJ : J ≤ Γ_sub) (hJp : IsPathGraph J)
    (hJE : J.edgeSet.Nonempty) : Γ.U ⊆ jumpLine Γ ιE J ∪ otherPart Γ ιV ιE J := by
  intro z hz
  by_cases hzV : z ∈ Γ.V
  · by_cases hzJ : ιV z ∈ J.vertexSet
    · obtain ⟨-, -, -, -, -, -, -, hV⟩ := jumpLine_spec hiso h2 hJ hJp hJE
      have : z ∈ jumpLine Γ ιE J ∩ Γ.V := hV ▸ ⟨hzV, hzJ⟩
      exact Or.inl this.1
    · exact Or.inr (Or.inr ⟨hzV, hzJ⟩)
  · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hz hzV
    by_cases heJ : ιE e ∈ J.edgeSet
    · exact Or.inl (mem_jumpLine.2 ⟨e, he, heJ, subset_closure hze⟩)
    · exact Or.inr (Or.inl (mem_iUnion₂.2 ⟨e, ⟨he, heJ⟩, subset_closure hze⟩))

omit [T2Space S] in
/-- A vertex of `Γ` in the line of a jump `J` is a vertex of `J`. -/
theorem mem_vertexSet_of_mem_jumpLine (hiso : IsDrawingIso Γ Γ_sub ιV ιE) (hJ : J ≤ Γ_sub)
    {z : S} (hzV : z ∈ Γ.V) (hz : z ∈ jumpLine Γ ιE J) :
    ∃ e ∈ Γ.E, ιE e ∈ J.edgeSet ∧ J.Inc (ιE e) (ιV z) ∧ ιV z ∈ J.vertexSet := by
  obtain ⟨e, he, heJ, hze⟩ := mem_jumpLine.1 hz
  have hinc : J.Inc (ιE e) (ιV z) :=
    (GM10.inc_iff_of_le hJ heJ).2 (inc_of_mem_closure hiso he hzV hze)
  exact ⟨e, he, heJ, hinc, J.vertex_mem_of_inc hinc⟩

variable (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)
include hdeg

/-- "any two $\Sigma$-jumps have no common vertices except possibly one end": the line of a jump
`J` meets the rest of the drawing only in the ends of `J`. -/
theorem jumpLine_inter_otherPart_subset (hiso : IsDrawingIso Γ Γ_sub ιV ιE)
    (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) :
    jumpLine Γ ιE J ∩ otherPart Γ ιV ιE J ⊆ {z ∈ Γ.V | ιV z ∈ terminals J} := by
  rintro z ⟨hz, hzo⟩
  obtain ⟨e, he, heJ, hze⟩ := mem_jumpLine.1 hz
  rcases hzo with hzf | ⟨hzV, hzJ⟩
  · obtain ⟨f, ⟨hf, hfJ⟩, hzf⟩ := mem_iUnion₂.1 hzf
    have hef : e ≠ f := fun h => hfJ (h ▸ heJ)
    have hzV : z ∈ Γ.V := closure_inter_closure_subset Γ he hf hef ⟨hze, hzf⟩
    obtain ⟨-, -, -, -, hzJ⟩ := mem_vertexSet_of_mem_jumpLine hiso hJ.1 hzV hz
    refine ⟨hzV, ?_⟩
    by_contra hterm
    have hzB : ιV z ∉ ιV '' (Γ.V ∩ bd S) := fun hB =>
      hterm (mem_terminals_of_mem_jumpSet hJ hzJ hB)
    have hfinc : ιE f ∈ incidentEdges Γ_sub (ιV z) :=
      ⟨hiso.ιE_image ▸ mem_image_of_mem ιE hf, inc_of_mem_closure hiso hf hzV hzf⟩
    rw [← incidentEdges_jump_eq hdeg hJ hzJ hzB] at hfinc
    exact hfJ hfinc.1
  · obtain ⟨-, -, -, -, hzJ'⟩ := mem_vertexSet_of_mem_jumpLine hiso hJ.1 hzV hz
    exact (hzJ hzJ').elim

omit [T2Space S] in
/-- "every edge of $\Gamma$ is in a unique $\Sigma$-jump": the line of a jump `K ≠ J` lies in the
rest of the drawing besides `J`. -/
theorem jumpLine_subset_otherPart (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)))
    (hK : K ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) (hJK : J ≠ K) :
    jumpLine Γ ιE K ⊆ otherPart Γ ιV ιE J := by
  intro z hz
  obtain ⟨e, he, heK, hze⟩ := mem_jumpLine.1 hz
  refine Or.inl (mem_iUnion₂.2 ⟨e, ⟨he, fun heJ => hJK ?_⟩, hze⟩)
  exact jump_eq_of_edge hdeg hJ hK heJ heK

omit [T2Space S] hdeg in
/-- The line of a jump meets `bd(Σ)` only in the ends of the jump. -/
theorem jumpLine_inter_bd_subset (hprop : Γ.IsProper) (hiso : IsDrawingIso Γ Γ_sub ιV ιE)
    (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))) :
    jumpLine Γ ιE J ∩ bd S ⊆ {z ∈ Γ.V | ιV z ∈ terminals J} := by
  rintro z ⟨hz, hzb⟩
  obtain ⟨e, he, -, hze⟩ := mem_jumpLine.1 hz
  have hzU : z ∈ Γ.U := closure_minimal (fun y hy => (he.2.1 hy).1) Γ.isClosed_U hze
  have hzV : z ∈ Γ.V := hprop ⟨hzb, hzU⟩
  obtain ⟨-, -, -, -, hzJ⟩ := mem_vertexSet_of_mem_jumpLine hiso hJ.1 hzV hz
  exact ⟨hzV, mem_terminals_of_mem_jumpSet hJ hzJ (mem_image_of_mem ιV ⟨hzV, hzb⟩)⟩

omit [T2Space S] in
/-- `U(Γ)` lies in `bd(Σ)` and the lines of the jumps. -/
theorem U_subset_bd_union_jumpLine (hiso : IsDrawingIso Γ Γ_sub ιV ιE) (hK : IsLinkage G Γ_sub) :
    Γ.U ⊆ bd S ∪ ⋃ J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)), jumpLine Γ ιE J := by
  intro z hz
  by_cases hzb : z ∈ bd S
  · exact Or.inl hzb
  right
  -- An edge `e` of `Γ` with `z ∈ closure e`.
  obtain ⟨e, he, hze⟩ : ∃ e ∈ Γ.E, z ∈ closure e := by
    by_cases hzV : z ∈ Γ.V
    · have hzB : ιV z ∉ ιV '' (Γ.V ∩ bd S) := by
        rintro ⟨y, hy, hyz⟩
        exact hzb (hiso.ιV_injOn hy.1 hzV hyz ▸ hy.2)
      have hzΓ : ιV z ∈ Γ_sub.vertexSet := hiso.ιV_image ▸ mem_image_of_mem ιV hzV
      obtain ⟨f, hf⟩ : (incidentEdges Γ_sub (ιV z)).Nonempty :=
        nonempty_of_ncard_ne_zero (by rw [hdeg _ hzΓ hzB]; omega)
      obtain ⟨e, he, rfl⟩ : f ∈ ιE '' Γ.E := hiso.ιE_image ▸ hf.1
      exact ⟨e, he, (hiso.inc_iff e he z hzV).1 hf.2⟩
    · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hz hzV
      exact ⟨e, he, subset_closure hze⟩
  obtain ⟨J, hJ, heJ⟩ := exists_jump_of_edge hK hdeg (hiso.ιE_image ▸ mem_image_of_mem ιE he)
  exact mem_iUnion₂.2 ⟨J, hJ, mem_jumpLine.2 ⟨e, he, heJ, hze⟩⟩

end LastStep
end GM21
end GraphMinor
