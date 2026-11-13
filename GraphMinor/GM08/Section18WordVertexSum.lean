module

public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.CutEdges
import GraphMinor.GM08.Section18GraphDegreeSum
import GraphMinor.GM08.Section18WordVertexDegree
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Total vertex count over the cutting graph

Sum the exact fibre formula over the vertices incident with cut edges.
The sum of cut degrees is twice the edge count, and boundary contacts
contribute one further lift each. This is the vertex term in the Euler
calculation of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

private theorem ncard_preimage_eq_sum {X Y : Type*} (ψ : Y → X) {V : Set X}
    (hV : V.Finite) (hfin : ∀ v ∈ V, (ψ ⁻¹' {v}).Finite) :
    (ψ ⁻¹' V).ncard = ∑ v ∈ hV.toFinset, (ψ ⁻¹' {v}).ncard := by
  classical
  have heq : ψ ⁻¹' V = ⋃ v ∈ V, ψ ⁻¹' {v} := by ext y; simp
  have hdis : V.PairwiseDisjoint (fun v => ψ ⁻¹' {v}) := by
    intro v hv w hw hne
    exact disjoint_left.mpr (fun y hy hy' => hne (hy.symm.trans hy'))
  rw [heq, hV.ncard_biUnion hfin hdis, finsum_mem_eq_finite_toFinset_sum _ hV]

/-- The lifted cut vertices number twice the cut edges plus the old
boundary contacts. This is the complete vertex count in VIII (18.2),
page 286, for the constructed word cut. -/
theorem word_cut_vertices_ncard {S Y : Type u} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space S] [T2Space Y]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {D : Set (Set S)} (hDE : D ⊆ E)
    (hmid : ∀ e ∈ D, edgeMid A e ∉ bd S)
    {g : ℕ × ℂ → Y} (hg : Presents (cutW W (lab '' D)) g) {ψ : Y → S}
    (hψ : ∀ a ∈ Dsk W, ψ (g a) = f a) (hcm : GM19.IsCutMap ψ (⋃₀ D))
    (hbd : ⋃₀ D ∩ bd S ⊆ V) :
    (ψ ⁻¹' (V ∩ ⋃₀ D)).ncard = 2 * D.ncard + (⋃₀ D ∩ bd S).ncard := by
  classical
  have hgraph := isGraph_edge_subfamily hw.graph hDE
  have hcount : ∀ v ∈ V ∩ ⋃₀ D, (ψ ⁻¹' {v}).ncard =
      {e ∈ D | v ∈ e}.ncard + if v ∈ bd S then 1 else 0 :=
    fun v hv => word_cut_vertex_fibre_eq_degree hw hDE hmid hg hψ hv.1 hv.2
  have hbdset : (V ∩ ⋃₀ D) ∩ bd S = ⋃₀ D ∩ bd S := by
    ext x
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨hbd hx, hx.1⟩, hx.2⟩⟩
  rw [ncard_preimage_eq_sum ψ hgraph.fin (fun v _ => hcm.2.2.2.1 v)]
  have hsum : (∑ v ∈ hgraph.fin.toFinset, (ψ ⁻¹' {v}).ncard) =
      ∑ v ∈ hgraph.fin.toFinset,
        ({e ∈ D | v ∈ e}.ncard + if v ∈ bd S then 1 else 0) :=
    Finset.sum_congr rfl (fun v hv => hcount v (hgraph.fin.mem_toFinset.mp hv))
  rw [hsum, Finset.sum_add_distrib, graph_sum_degrees hgraph]
  congr 1
  rw [← Finset.card_filter, ← ncard_coe_finset, ← hbdset]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, hgraph.fin.mem_toFinset, mem_inter_iff]

end GraphMinor.GM08
