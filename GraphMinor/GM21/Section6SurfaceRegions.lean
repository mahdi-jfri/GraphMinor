module

public import GraphMinor.GM06.Defs
import GraphMinor.GM07.FlatEdges
import GraphMinor.GM11.Regions
import GraphMinor.GM11.EdgeSides
import GraphMinor.GM21.Section6TwoEdges
import GraphMinor.Surface.CutLift
public import GraphMinor.GM21.Section4

/-!
# Graph Minors XXI, Section 6: regions along an edge, in any surface

The choice of regions in the proofs of (6.6), (6.7) and of claim (3) of (6.3) in *Graph Minors XXI*
(pages 27–29 of the preprint) follows the regions along a jump. Two local facts are used, and this
file proves them for a proper drawing in any surface, possibly with boundary.

* `edge_subset_closure_of_incident`: a region whose closure meets an edge with two ends contains
  the whole edge in its closure. The proof puts the closure of the edge in a closed disc that meets
  the rest of `U(Γ)` and `bd(Σ)` only at the ends of the edge (`GM07.exists_line_lens`). The edge
  cuts the inside of the disc into two connected sides, each with the whole edge in its closure, and
  a region that comes near the edge contains one of the sides.
* `exists_parallel_line`: next to a line `L` with ends `x, u` in `bd(Σ)` that meets a closed set
  `W` and `bd(Σ)` only at its ends, there is a proper line `F` with the same ends that meets
  `L ∪ W` only at its ends. It is an arc of the boundary of the disc of `GM07.exists_line_lens`.
  Applied to a jump `J`, with `W` the rest of `U(Γ)`, it gives a proper line with the ends of `J`
  and no internal point in `U(Γ)`.
* `subset_closure_of_two_edges`: at a vertex `w ∉ bd(Σ)` with exactly two edges `e, e'`, a region
  whose closure meets `e` contains `e'` in its closure. This is
  `DiscLine.subset_closure_of_two_edges_of_edge` with the first fact.
  `union_subset_closure_of_two_edges` starts from any point of `e ∪ {w} ∪ e'`, also from `w`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Regions

open Set Topology GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- **A region along an edge.** In a surface, a region of a proper drawing whose closure meets an
edge `E` with two ends `u ≠ v` contains `E` in its closure. -/
theorem edge_subset_closure_of_incident (hS : IsSurface S) {Γ : Drawing S} (hΓ : Γ.IsProper)
    {E : Set S} (hE : E ∈ Γ.E) {u v : S} (huv : u ≠ v) (hcl : closure E ∩ Γ.V = {u, v})
    {r : Set S} (hr : r ∈ Γ.R) (hinc : (E ∩ closure r).Nonempty) : E ⊆ closure r := by
  have : T2Space S := hS.2.1
  have hL : IsLineWithEnds (closure E) u v := DiscLine.isLineWithEnds_closure_edge Γ hE hcl huv
  have hEU : E ⊆ Γ.U \ Γ.V := hE.2.1
  have hclU : closure E ⊆ Γ.U :=
    closure_minimal (fun z hz => (hEU hz).1) Γ.isClosed_U
  have hW : IsClosed (Γ.U \ E) := GM11.isClosed_U_sdiff_edge Γ hE
  have hends : ∀ z ∈ closure E, z ∈ Γ.V → z ∈ ({u, v} : Set S) := fun z hz hzV => by
    rw [← hcl]; exact ⟨hz, hzV⟩
  have hLW : closure E ∩ (Γ.U \ E) ⊆ {u, v} := by
    rintro z ⟨hzc, hzU, hzE⟩
    by_contra hzuv
    exact hzE (DiscLine.closure_inter_sdiff_subset Γ hE
      ⟨hzc, hzU, fun hzV => hzuv (hends z hzc hzV)⟩)
  have hLb : closure E ∩ bd S ⊆ {u, v} := fun z hz =>
    hends z hz.1 (hΓ ⟨hz.2, hclU hz.1⟩)
  obtain ⟨Δ, A, B, -, hLΔ, hΔW, -, -, hΔL, hint, hcov, hAΔ, hBΔ, -, hAL, hBL, hA, hB, hAc,
    hBc⟩ := GM07.exists_line_lens hS hL hW hLW hLb
  obtain ⟨p, hpE, hpr⟩ := hinc
  have huvV : u ∈ Γ.V ∧ v ∈ Γ.V := by
    have hu : u ∈ closure E ∩ Γ.V := hcl ▸ Or.inl rfl
    have hv : v ∈ closure E ∩ Γ.V := hcl ▸ Or.inr rfl
    exact ⟨hu.2, hv.2⟩
  have hEsub : E ⊆ closure E \ {u, v} := fun z hz => ⟨subset_closure hz, by
    rintro (rfl | rfl)
    exacts [(hEU hz).2 huvV.1, (hEU hz).2 huvV.2]⟩
  have hpint : p ∈ Δ \ discBd Δ := ⟨hLΔ (subset_closure hpE), fun h => (hEsub hpE).2
    (hΔL ⟨h, subset_closure hpE⟩)⟩
  obtain ⟨x, hxint, hxr⟩ := mem_closure_iff.mp hpr _ hint hpint
  have hxU : x ∉ Γ.U := GM11.region_subset hr hxr
  -- A side of the edge misses `U(Γ)`.
  have hside : ∀ C : Set S, C ⊆ Δ \ discBd Δ → Disjoint C (closure E) → Disjoint C Γ.U :=
    fun C hCΔ hCL => disjoint_left.mpr fun z hzC hzU => by
      by_cases hzE : z ∈ E
      · exact disjoint_left.mp hCL hzC (subset_closure hzE)
      · have hz : z ∈ ({u, v} : Set S) := hΔW ⟨(hCΔ hzC).1, Or.inl ⟨hzU, hzE⟩⟩
        rcases hz with rfl | hz
        · exact disjoint_left.mp hCL hzC hL.left_mem
        · exact disjoint_left.mp hCL hzC ((mem_singleton_iff.mp hz) ▸ hL.right_mem)
  rcases hcov hxint with (hxA | hxB) | hxL
  · have hAr : A ⊆ r := GM11.subset_region hr hA.isConnected.isPreconnected
      (hside A hAΔ hAL) hxA hxr
    exact fun z hz => closure_mono hAr (hAc (hEsub hz))
  · have hBr : B ⊆ r := GM11.subset_region hr hB.isConnected.isPreconnected
      (hside B hBΔ hBL) hxB hxr
    exact fun z hz => closure_mono hBr (hBc (hEsub hz))
  · exact (hxU (hclU hxL)).elim

/-- **A line next to a line.** Let `L` be a line with ends `x ≠ u` in `bd(Σ)`, which meets a closed
set `W` and `bd(Σ)` only at its ends. Then there is a proper line `F` with ends `x, u` which meets
`L ∪ W` only at its ends. It is one of the two arcs between `x` and `u` of the boundary of a closed
disc `Δ ⊇ L` that meets `W ∪ bd(Σ)` only at `x, u` (`GM07.exists_line_lens`). -/
theorem exists_parallel_line (hS : IsSurface S) {L W : Set S} {x u : S}
    (hL : IsLineWithEnds L x u) (hW : IsClosed W) (hLW : L ∩ W ⊆ {x, u})
    (hLb : L ∩ bd S ⊆ {x, u}) (hx : x ∈ bd S) (hu : u ∈ bd S) (hxu : x ≠ u) :
    ∃ F : Set S, IsProperLineInSurface F x u ∧ F ∩ (L ∪ W) ⊆ {x, u} := by
  have : T2Space S := hS.2.1
  obtain ⟨Δ, -, -, hΔ, hLΔ, hΔW, hxΔ, huΔ, hΔL, -⟩ := GM07.exists_line_lens hS hL hW hLW hLb
  obtain ⟨F, F', hF, -, hFun, -⟩ := hΔ.isOArc_discBd.lines hxΔ huΔ hxu
  have hFbd : F ⊆ discBd Δ := hFun ▸ subset_union_left
  have hFΔ : F ⊆ Δ := hFbd.trans (discBd_subset Δ)
  have hFLW : F ∩ (L ∪ W) ⊆ {x, u} := by
    rintro z ⟨hzF, hzL | hzW⟩
    · exact hΔL ⟨hFbd hzF, hzL⟩
    · exact hΔW ⟨hFΔ hzF, Or.inl hzW⟩
  refine ⟨F, ⟨hF, hx, hu, disjoint_left.mpr fun z hz hzb => hz.2 (hΔW ⟨hFΔ hz.1, Or.inr hzb⟩)⟩,
    hFLW⟩

/-- **Regions at a vertex with two edges**, in any surface. Let `w` be a vertex of a proper drawing
`Γ`, not in `bd(Σ)`, whose only edges are `e` (with ends `u, w`) and `e'` (with ends `w, v`), where
`u, w, v` are distinct. Then every region whose closure meets `e` contains `e'` in its closure. -/
theorem subset_closure_of_two_edges (hS : IsSurface S) {Γ : Drawing S}
    (hΓ : Γ.IsProper) {e e' : Set S} {u w v : S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) (hee : e ≠ e')
    (hcl : closure e ∩ Γ.V = {u, w}) (hcl' : closure e' ∩ Γ.V = {w, v}) (huw : u ≠ w)
    (hvw : v ≠ w) (huv : u ≠ v) (hdeg : ∀ f ∈ Γ.E, w ∈ closure f → f = e ∨ f = e')
    (hwbd : w ∉ bd S) {r : Set S} (hr : r ∈ Γ.R) (her : (e ∩ closure r).Nonempty) :
    e' ⊆ closure r :=
  have : T2Space S := hS.2.1
  DiscLine.subset_closure_of_two_edges_of_edge
    (fun _ hΓ' _ hE _ _ hne hcl₀ _ hr' hinc =>
      edge_subset_closure_of_incident hS hΓ' hE hne hcl₀ hr' hinc)
    hΓ he he' hee hcl hcl' huw hvw huv hdeg hwbd hr her

/-- **Regions at a vertex with two edges**, in any surface, starting from the vertex. Let `w` be a
vertex of a proper drawing `Γ`, not in `bd(Σ)`, whose only edges are `e` (with ends `u, w`) and `e'`
(with ends `w, v`), where `u, w, v` are distinct. Then every region whose closure meets
`e ∪ {w} ∪ e'` contains all of it in its closure. -/
theorem union_subset_closure_of_two_edges (hS : IsSurface S) {Γ : Drawing S}
    (hΓ : Γ.IsProper) {e e' : Set S} {u w v : S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) (hee : e ≠ e')
    (hcl : closure e ∩ Γ.V = {u, w}) (hcl' : closure e' ∩ Γ.V = {w, v}) (huw : u ≠ w)
    (hvw : v ≠ w) (huv : u ≠ v) (hdeg : ∀ f ∈ Γ.E, w ∈ closure f → f = e ∨ f = e')
    (hwbd : w ∉ bd S) {r : Set S} (hr : r ∈ Γ.R) (her : ((e ∪ {w} ∪ e') ∩ closure r).Nonempty) :
    e ∪ {w} ∪ e' ⊆ closure r :=
  have : T2Space S := hS.2.1
  DiscLine.union_subset_closure_of_two_edges_of_edge
    (fun _ hΓ' _ hE _ _ hne hcl₀ _ hr' hinc =>
      edge_subset_closure_of_incident hS hΓ' hE hne hcl₀ hr' hinc)
    hΓ he he' hee hcl hcl' huw hvw huv hdeg hwbd hr her

end Regions
end GM21
end GraphMinor
