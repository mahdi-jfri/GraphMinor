module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks

/-!
# Edge labels and links after contracting an initial edge

For Reduction 3 of VI (5.7), page 133, remove the contracted edge's
original label and take the image of each remaining edge. Deleting
the old initial vertex makes the collapse injective on the remaining
drawing. Its links therefore map to links, and distinct edge labels
stay distinct. Replacing the neighbour label by the initial label
agrees with the collapse because their images are equal.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A continuous map injective on a drawing's point set preserves
links when the target has exactly its image vertices and edges. -/
theorem isLink_image_of_injOn_pointSet {P Q : Drawing ClosedCylinder}
    (π : C(ClosedCylinder, ClosedCylinder)) (hi : InjOn π P.U)
    (hV : Q.V = π '' P.V) (hE : Q.E = (image π) '' P.E)
    {e : Set ClosedCylinder} {x y : ClosedCylinder} (hl : P.toGraph.IsLink e x y) :
    Q.toGraph.IsLink (π '' e) (π x) (π y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE]; exact mem_image_of_mem (image π) hl.1
  · rw [hV]; exact mem_image_of_mem π hl.2.1
  · rw [hV]; exact mem_image_of_mem π hl.2.2.1
  · rw [hV, π.continuous.isClosedMap.closure_image_eq_of_continuous π.continuous,
      ← hi.image_inter (P.closure_subset_U hl.1) P.V_subset_U, hl.2.2.2, image_pair]

private theorem image_edges_injective {P : Drawing ClosedCylinder}
    {π : ClosedCylinder → ClosedCylinder} (hi : InjOn π P.U) :
    InjOn (image π) P.E := by
  have hsub : ∀ e ∈ P.E, ∀ f ∈ P.E, π '' e = π '' f → e ⊆ f := by
    intro e he f hf hef x hx
    have hπx : π x ∈ π '' f := hef ▸ mem_image_of_mem π hx
    obtain ⟨y, hy, hxy⟩ := hπx
    have hyx : y = x := hi (P.closure_subset_U hf (subset_closure hy))
      (P.closure_subset_U he (subset_closure hx)) hxy
    exact hyx ▸ hy
  intro e he f hf hef
  exact subset_antisymm (hsub e he f hf hef) (hsub f hf e he hef.symm)

/-- Every link off the collapsed edge maps to an actual link of
the contracted drawing, whose distinct remaining edges have
distinct images. These facts follow from the collapse's injectivity
on the drawing with the initial vertex deleted. -/
theorem initial_edge_collapse_links_and_injective
    {k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v) (hvs : v ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure a) (hi : InjOn π (closure a)ᶜ)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {a})) :
    (∀ e x y, e ≠ a → G.toGraph.IsLink e x y →
      G'.toGraph.IsLink (π '' e) (π x) (π y)) ∧
      InjOn (image π) (G.E \ {a}) := by
  let J := induceDrawing G (G.V \ {cylinderM1Point k i})
  have hJV : J.V = G.V \ {cylinderM1Point k i} := induceDrawing_V G sdiff_subset
  obtain ⟨hJE, _, _⟩ := deleted_initial_vertex_drawing hval hl hvs
  have hJi : InjOn π J.U := injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi
  have hπa : π (cylinderM1Point k i) = cylinderM1Point k i := by
    have ha : cylinderM1Point k i ∈ closure a :=
      (show cylinderM1Point k i ∈ closure a ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ _).1
    have hh : cylinderM1Point k i ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ ha
    exact hh
  have hπv : π v = cylinderM1Point k i := by
    have hv : v ∈ closure a :=
      (show v ∈ closure a ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have hh : v ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hv
    exact hh
  have hVJ : G'.V = π '' J.V := by
    rw [hV, hJV]
    apply subset_antisymm
    · rintro z ⟨x, hx, rfl⟩
      by_cases hxs : x = cylinderM1Point k i
      · refine ⟨v, ⟨hl.2.2.1, hvs⟩, ?_⟩
        rw [hxs, hπa, hπv]
      · exact ⟨x, ⟨hx, hxs⟩, rfl⟩
    · exact image_mono sdiff_subset
  have hEJ : G'.E = (image π) '' J.E := by rw [hE, hJE]
  constructor
  · intro e x y hea hlink
    have heJ : e ∈ J.E := by rw [hJE]; exact ⟨hlink.1, hea⟩
    have hJG : J.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
    exact isLink_image_of_injOn_pointSet π hJi hVJ hEJ ((hJG.isLink_iff heJ).mpr hlink)
  · rw [← hJE]
    exact image_edges_injective hJi

/-- Clearing the selected original edge bit and relabelling its
neighbour gives all actual links and all edges of the contracted
drawing. The active image labels remain injective. -/
theorem contracted_mask_links_and_cover
    {n k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (d : Fin tagged.length) (hd : tagged[d].2 = 1) (a b : Fin n)
    (hpoint : vertex a = cylinderM1Point k i)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d))
    (hi : InjOn π (closure (edge d))ᶜ)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {edge d})) :
    let active := (tagged.map Prod.snd).set d.val 0
    (∀ j l : Fin tagged.length,
      active[j.val]'(by simp only [active, List.length_set, List.length_map]; exact j.isLt) = 1 →
      active[l.val]'(by simp only [active, List.length_set, List.length_map]; exact l.isLt) = 1 →
      π '' edge j = π '' edge l → j = l) ∧
    (∀ j : Fin tagged.length,
      active[j.val]'(by simp only [active, List.length_set, List.length_map]; exact j.isLt) = 1 →
      G'.toGraph.IsLink (π '' edge j)
        (π (vertex (if tagged[j].1.1 = b then a else tagged[j].1.1)))
        (π (vertex (if tagged[j].1.2 = b then a else tagged[j].1.2)))) ∧
    (∀ e ∈ G'.E, ∃ j : Fin tagged.length,
      active[j.val]'(by simp only [active, List.length_set, List.length_map]; exact j.isLt) = 1 ∧ π '' edge j = e) := by
  intro active
  have hremaining : ∀ j : Fin tagged.length,
      active[j.val]'(by simp only [active, List.length_set, List.length_map]; exact j.isLt) = 1 →
      tagged[j].2 = 1 ∧ edge j ≠ edge d := by
    intro j hj
    have hjd : j ≠ d := by
      intro h; subst j
      have hz := List.getElem_set_self (l := tagged.map Prod.snd) (i := d.val) (a := 0)
        (by simpa only [List.length_set, List.length_map] using d.isLt)
      exact Nat.zero_ne_one (hz.symm.trans hj)
    have hne : d.val ≠ j.val := fun h => hjd (Fin.ext h.symm)
    have hj' : tagged[j].2 = 1 := by simpa [active, List.getElem_set_ne hne] using hj
    exact ⟨hj', fun h => hjd (hinj hj' hd h)⟩
  obtain ⟨himage, himageInj⟩ := initial_edge_collapse_links_and_injective hval hl hvs π hfiber hi hV hE
  have hπab : π (vertex a) = π (vertex b) := by
    have ha : vertex a ∈ closure (edge d) :=
      hpoint.symm ▸ (show cylinderM1Point k i ∈ closure (edge d) ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ _).1
    have hb : vertex b ∈ closure (edge d) :=
      (show vertex b ∈ closure (edge d) ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have ha' : vertex a ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ ha
    have hb' : vertex b ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hb
    exact ha'.trans hb'.symm
  have hrelab : ∀ x : Fin n, π (vertex (if x = b then a else x)) = π (vertex x) := by
    intro x; by_cases h : x = b <;> simp only [h, ite_true, ite_false]; exact hπab
  refine ⟨?_, ?_, ?_⟩
  · intro j l hj hl' heq
    obtain ⟨hj', hjd⟩ := hremaining j hj
    obtain ⟨hl'', hld⟩ := hremaining l hl'
    exact hinj hj' hl'' (himageInj ⟨(hlinks j hj').1, hjd⟩ ⟨(hlinks l hl'').1, hld⟩ heq)
  · intro j hj
    obtain ⟨hj', hjd⟩ := hremaining j hj
    rw [hrelab, hrelab]
    exact himage _ _ _ hjd (hlinks j hj')
  · intro e he
    rw [hE] at he
    obtain ⟨f, hf, rfl⟩ := he
    obtain ⟨j, hj, hje⟩ := hcover f hf.1
    have hne : d.val ≠ j.val := by
      intro hh
      exact hf.2 (hje ▸ congrArg edge (Fin.ext hh.symm))
    refine ⟨j, ?_, congrArg (image π) hje⟩
    simpa [active, List.getElem_set_ne hne] using hj

end GraphMinor.GM06
