module

public import GraphMinor.GM06.Section5ContractedMaskGraph
public import GraphMinor.GM06.Section5ContractedVertexLabels
public import GraphMinor.Compute.GM06RefreshContractedMasks

/-!
# The finite active graph represented after an initial-edge contraction

For Reduction 3 of VI (5.7), page 133, the endpoint and activity
writes form an explicit finite edge table. Its surviving endpoints
are live under the new vertex labelling. Combining the live-vertex
construction with the image-link proof identifies every active
link, all active edges and the complete vertex set of the actual
contracted drawing. The original edge-label positions remain fixed.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute

/-- The concrete contracted finite edge table represents the
actual contracted graph, with an injective live vertex labelling,
exact vertex image, injective active edge labels and all new links. -/
theorem exists_contracted_finite_graph_representation
    {n k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (hvertex : ∀ x ∈ A, vertex x ∈ G.V)
    (hcoverV : ∀ p ∈ G.V, ∃ x ∈ A, vertex x = p)
    (d : Fin tagged.length) (hd : tagged[d].2 = 1) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hpoint : vertex a = cylinderM1Point k i)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d))
    (hi : InjOn π (closure (edge d))ᶜ)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {edge d})) :
    let updated := gm06ContractTaggedEdges tagged a b d.val
    let edge' : Fin updated.length → Set ClosedCylinder :=
      fun j => π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d.val) j)
    ∃ vertex' : Fin n ↪ ClosedCylinder,
      (∀ x ∈ A.erase b, vertex' x = π (vertex x)) ∧
      G'.V = vertex' '' (A.erase b : Set (Fin n)) ∧ vertex' a = cylinderM1Point k i ∧
      InjOn edge' {j | updated[j].2 = 1} ∧
      (∀ j : Fin updated.length, updated[j].2 = 1 →
        G'.toGraph.IsLink (edge' j) (vertex' updated[j].1.1) (vertex' updated[j].1.2)) ∧
      (∀ e ∈ G'.E, ∃ j : Fin updated.length, updated[j].2 = 1 ∧ edge' j = e) := by
  dsimp only
  let updated := gm06ContractTaggedEdges tagged a b d.val
  let mask := (tagged.map Prod.snd).set d.val 0
  let old : Fin updated.length → Fin tagged.length :=
    Fin.cast (gm06ContractTaggedEdges_length tagged a b d.val)
  have hrow : ∀ j : Fin updated.length,
      updated[j] = ((gm06ContractVertexLabel a b tagged[old j].1.1,
        gm06ContractVertexLabel a b tagged[old j].1.2), if j.val = d.val then 0 else tagged[old j].2) := by
    intro j
    exact gm06ContractTaggedEdges_getElem tagged a b d.val (old j).isLt
  have hmask : ∀ j : Fin updated.length, updated[j].2 =
      mask[(old j).val]'(by simp only [mask, List.length_set, List.length_map]; exact (old j).isLt) := by
    intro j
    rw [hrow, List.getElem_set]
    simp only [List.getElem_map, old, Fin.val_cast]
    by_cases h : j.val = d.val
    · simp [h]
    · simp [h, Ne.symm h]
  have hactive : ∀ j : Fin updated.length, updated[j].2 = 1 → tagged[old j].2 = 1 := by
    intro j hj
    rw [hrow] at hj
    by_cases h : j.val = d.val
    · simp only [h, ite_true] at hj; omega
    · simpa only [h, ite_false] using hj
  obtain ⟨hnewInj, hnewLinks, hnewCover⟩ := contracted_mask_links_and_cover tagged vertex edge hinj
    hlinks hcover d hd a b hpoint hval hl hvs π hfiber hi hV hE
  obtain ⟨vertex', hv, hnewV, hnewPoint⟩ := exists_contracted_live_vertex_labels vertex A a b
    ha hb hab hvertex hcoverV hpoint hval hl hvs π hfiber hi hV
  have hLive : ∀ x, vertex x ∈ G.V → x ∈ A := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcoverV (vertex x) hx
    exact vertex.injective hyx ▸ hy
  have hnewEnds : ∀ j : Fin updated.length, updated[j].2 = 1 →
      updated[j].1.1 ∈ A.erase b ∧ updated[j].1.2 ∈ A.erase b := by
    intro j hj
    have hl' := hlinks (old j) (hactive j hj)
    rw [hrow]
    exact ⟨gm06ContractVertexLabel_mem_erase A a b _ ha (hLive _ hl'.left_mem) hab,
      gm06ContractVertexLabel_mem_erase A a b _ ha (hLive _ hl'.right_mem) hab⟩
  refine ⟨vertex', hv, hnewV, hnewPoint, ?_, ?_, ?_⟩
  · intro j hj l hl' heq
    have hjo := hnewInj (old j) (old l) ((hmask j).symm.trans hj) ((hmask l).symm.trans hl') heq
    exact Fin.ext (congrArg (fun z : Fin tagged.length => z.val) hjo)
  · intro j hj
    have hh := hnewLinks (old j) ((hmask j).symm.trans hj)
    have hend := hnewEnds j hj
    rw [hv _ hend.1, hv _ hend.2, hrow]
    exact hh
  · intro e he
    obtain ⟨j, hj, hje⟩ := hnewCover e he
    let j' : Fin updated.length := Fin.cast (gm06ContractTaggedEdges_length tagged a b d.val).symm j
    refine ⟨j', ?_, ?_⟩
    · rw [hmask]
      simpa only [j', old, Fin.val_cast] using hj
    · simpa only [j', old, Fin.cast_cast, Fin.cast_eq_self] using hje

end GraphMinor.GM06
