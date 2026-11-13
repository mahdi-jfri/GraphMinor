module

public import GraphMinor.GM21.Section6CutLift
public import GraphMinor.GM07.Open
import GraphMinor.GM07.Section46PullGraph
import GraphMinor.GM07.PullForest
import GraphMinor.GM11.RadialChord
import GraphMinor.GM11.Defs
import GraphMinor.GM06.Section3Dual
import GraphMinor.GM21.Section6TwoEdges

/-!
# Graph Minors XXI, (6.3), claim (2): the drawing on the cut surface

Claim (2) of the proof of (6.3) (page 28 of the preprint) says: "Let $\Gamma'$ be the drawing in
$\Sigma'$ obtained from $\Gamma$ by splitting appropriately the vertices of $\Gamma$ in $F$." Here
`F` is a proper line with ends `a, b ∈ V(Γ)` and no other point in `U(Γ)`. The drawing is
`ψ⁻¹(Γ)`: its points are the points over `U(Γ)` and its vertices the points over `V(Γ)`. The
vertices `a, b` become two vertices each, and every other vertex stays one vertex.

* `isCutAlongGraph`: `ψ` undoes a cut along the drawing with one edge `F`, in the sense of
  Graph Minors VII. So the pullback of Graph Minors VII (`GM07.exists_pullback_graph`) gives the
  drawing `Γ'` (`exists_cutDrawing`), proper, whose edges are the sets `ψ⁻¹(e)`.
* `preimage_mem_E`: conversely, each `ψ⁻¹(e)` is an edge of `Γ'`.
* `closure_preimage_edge`: an edge `e` of `Γ` with two ends `u ≠ w` lifts to an edge whose closure
  is a line, mapped one to one onto `ē`. So it has one end over `u` and one over `w`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

namespace IsLineCut

variable (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂)
include h

/-- The cut along `F` is a cut along the drawing with the one edge `F \ {a, b}`. -/
theorem isCutAlongGraph (hS : IsSurface S) (hF : IsProperLineInSurface F a b) :
    have : T2Space S := hS.2.1
    GM07.IsCutAlongGraph (GM11.lineDrawing hF.1 hF.ne) S' ψ := by
  have : T2Space S := hS.2.1
  refine GM07.IsCutAlongSet.isCutAlongGraph (h.isCutAlongSet hS hF) ?_ ?_
  · intro x hx
    have : x ∈ F ∩ bd S := ⟨hx.2, hx.1⟩
    rwa [hF.inter_bd_eq] at this
  · intro v hv
    refine ⟨F \ {a, b}, by rw [GM11.lineDrawing_E]; rfl, hv, Or.inl (by
      rw [GM11.lineDrawing_E]; rfl), ?_⟩
    rw [GM11.closure_sdiff_pair hF.1]
    rcases hv with rfl | rfl
    · exact hF.1.left_mem
    · exact hF.1.right_mem

/-- **The drawing on the cut surface.** If `F` meets `U(Γ)` only in vertices, then `ψ⁻¹(Γ)` is a
proper drawing in `Σ'`, and each of its edges is `ψ⁻¹(e)` for an edge `e` of `Γ`. -/
theorem exists_cutDrawing (hS : IsSurface S) (hF : IsProperLineInSurface F a b) {Γ : Drawing S}
    (hΓ : Γ.IsProper) (hFU : F ∩ Γ.U ⊆ Γ.V) :
    ∃ Γ' : Drawing S', Γ'.U = ψ ⁻¹' Γ.U ∧ Γ'.V = ψ ⁻¹' Γ.V ∧ Γ'.IsProper ∧
      ∀ e' ∈ Γ'.E, ∃ e ∈ Γ.E, e' = ψ ⁻¹' e := by
  have : T2Space S := hS.2.1
  obtain ⟨Γ', ⟨hU, hV⟩, hp, hE⟩ := GM07.exists_pullback_graph hS (h.isCutAlongGraph hS hF) hΓ hFU
  exact ⟨Γ', hU, hV, hp, hE⟩

omit h in
/-- An edge of `Γ` misses `F`, since `F` meets `U(Γ)` only in vertices. -/
theorem edge_disjoint (Γ : Drawing S) (hFU : F ∩ Γ.U ⊆ Γ.V) {e : Set S} (he : e ∈ Γ.E) :
    Disjoint e F :=
  disjoint_left.mpr fun _ hx hxF => (he.2.1 hx).2 (hFU ⟨hxF, (he.2.1 hx).1⟩)

/-- **Each `ψ⁻¹(e)` is an edge of the drawing on the cut surface.** -/
theorem preimage_mem_E {Γ : Drawing S} {Γ' : Drawing S'} (hU : Γ'.U = ψ ⁻¹' Γ.U)
    (hV : Γ'.V = ψ ⁻¹' Γ.V) (hE : ∀ e' ∈ Γ'.E, ∃ e ∈ Γ.E, e' = ψ ⁻¹' e) {e : Set S}
    (he : e ∈ Γ.E) : ψ ⁻¹' e ∈ Γ'.E := by
  obtain ⟨x, hx⟩ := he.1
  obtain ⟨z, rfl⟩ := h.cutting.2.1 x
  have hzU : z ∈ Γ'.U := hU ▸ (he.2.1 hx).1
  have hzV : z ∉ Γ'.V := fun hz => (he.2.1 hx).2 (by rw [hV] at hz; exact hz)
  obtain ⟨e', he', hze'⟩ := GM07.exists_edge_of_mem hzU hzV
  obtain ⟨e₀, he₀, rfl⟩ := hE e' he'
  have : e₀ = e := by
    by_contra hne
    exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he₀ he hne) hze' hx
  rwa [← this]

/-- **The lift of an edge with two ends.** Let `e` be an edge of `Γ` with ends `u ≠ w`. Then the
closure of `ψ⁻¹(e)` is a line with ends over `u` and `w`, which `ψ` maps one to one onto `ē`. -/
theorem closure_preimage_edge (hS : IsSurface S) {Γ : Drawing S} (hFU : F ∩ Γ.U ⊆ Γ.V)
    {e : Set S} (he : e ∈ Γ.E) {u w : S} (hcl : closure e ∩ Γ.V = {u, w}) (huw : u ≠ w) :
    ∃ u' w' : S', IsLineWithEnds (closure (ψ ⁻¹' e)) u' w' ∧ ψ u' = u ∧ ψ w' = w ∧
      InjOn ψ (closure (ψ ⁻¹' e)) ∧ ψ '' closure (ψ ⁻¹' e) = closure e := by
  have : T2Space S := hS.2.1
  have : T2Space S' := h.t2Space
  have hline := DiscLine.isLineWithEnds_closure_edge Γ he hcl huw
  have hAF : closure e ∩ F ⊆ {u, w} := fun x hx => by
    rw [← hcl]
    exact ⟨hx.1, hFU ⟨hx.2, Γ.closure_subset_U he hx.1⟩⟩
  obtain ⟨u', w', hL, hu, hw, him, hinj⟩ := h.isLineWithEnds_lift hS huw hline hAF
  have huV : u ∈ Γ.V := (hcl.symm ▸ (Or.inl rfl : u ∈ ({u, w} : Set S)) : u ∈ closure e ∩ Γ.V).2
  have hwV : w ∈ Γ.V := (hcl.symm ▸ (Or.inr rfl : w ∈ ({u, w} : Set S)) : w ∈ closure e ∩ Γ.V).2
  have hce : closure e = e ∪ {u, w} := GM06.closure_edge_eq_union_ends Γ ⟨he, huV, hwV, hcl⟩ huw
  have heq : closure (ψ ⁻¹' e) = lift ψ F (closure e) := by
    apply subset_antisymm
    · refine closure_mono fun z hz => ⟨subset_closure hz, fun hzF => ?_⟩
      exact disjoint_left.mp (edge_disjoint Γ hFU he) hz hzF
    · rw [← GM11.closure_sdiff_pair hL]
      refine closure_mono fun z hz => ?_
      have hzA : ψ z ∈ closure e := him ▸ mem_image_of_mem ψ hz.1
      rw [hce] at hzA
      rcases hzA with hze | hzuw
      · exact hze
      · exfalso
        rcases hzuw with hzu | hzw
        · exact hz.2 (Or.inl (hinj hz.1 hL.left_mem (hzu.trans hu.symm)))
        · exact hz.2 (Or.inr (hinj hz.1 hL.right_mem (hzw.trans hw.symm)))
  rw [heq]
  exact ⟨u', w', hL, hu, hw, hinj, him⟩

end IsLineCut

end CutLine
end GM21
end GraphMinor
