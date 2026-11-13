module

public import GraphMinor.GM06.Alg34InducedListImages

/-!
# The division represented by the vertex-deletion payload

Restrict each old division block to surviving vertices and discard
empty intersections. The computed division lists denote exactly these
sets through the explicit new vertex labels. This verifies the division
field of the updated representation. For singleton deletion, the
restriction is the paper's removal of its singleton block.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- Restrict old division blocks to surviving vertices and discard empty sets. -/
def inducedDivision (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) : Set (Set S) :=
  (fun δ => δ ∩ h.vertexImage vs) '' {δ ∈ Δ | (δ ∩ h.vertexImage vs).Nonempty}

private theorem alg34_image_block_nonempty {n : ℕ} (f : Fin n → S) (B : List (Fin n)) :
    (f '' GM06DrawingData.block B).Nonempty ↔ B.isEmpty = false := by
  cases B with
  | nil => simp [GM06DrawingData.block]
  | cons v B =>
    constructor
    · intro _; rfl
    · intro _; exact ⟨f v, ⟨v, List.mem_cons_self, rfl⟩⟩

/-- The division lists in the computed payload denote exactly the
nonempty restrictions of the old actual division blocks. -/
theorem inducedData_division_image (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    h.inducedDivision vs =
      (fun L => (fun i => (h.inducedVertex vs i).val) '' GM06DrawingData.block L) ''
        {L | L ∈ (x.inducedData vs).division} := by
  apply Set.Subset.antisymm
  · rintro A ⟨δ, ⟨hδ, hnonempty⟩, rfl⟩
    obtain ⟨B, hB, hBδ⟩ := h.division.subset hδ
    have heq : (fun i => (h.inducedVertex vs i).val) '' GM06DrawingData.block (x.relabelVertexList vs B) =
        δ ∩ h.vertexImage vs := (h.image_relabelVertexList vs B).trans
          (congrArg (fun δ => δ ∩ h.vertexImage vs) hBδ)
    have hnonempty' : ((fun i => (h.inducedVertex vs i).val) ''
        GM06DrawingData.block (x.relabelVertexList vs B)).Nonempty := heq.symm ▸ hnonempty
    have hflag := (alg34_image_block_nonempty _ _).mp hnonempty'
    refine ⟨x.relabelVertexList vs B, ?_, heq⟩
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨B, hB, rfl⟩,
      by rw [hflag]; rfl⟩
  · rintro A ⟨B, hB, rfl⟩
    obtain ⟨hBmap, hBflag⟩ := List.mem_filter.mp hB
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hBmap
    have hLΔ : ((fun v => (h.vertex v).val) '' GM06DrawingData.block L) ∈ Δ :=
      h.division.symm.subset ⟨L, hL, rfl⟩
    have hflag : (x.relabelVertexList vs L).isEmpty = false :=
      by simpa only [Bool.not_eq_true'] using hBflag
    have hnonempty := (alg34_image_block_nonempty (fun i => (h.inducedVertex vs i).val) _).mpr hflag
    have heq := h.image_relabelVertexList vs L
    exact ⟨_, ⟨hLΔ, heq ▸ hnonempty⟩, heq.symm⟩

end GraphMinor.Compute.GM06DrawingRep
