module

public import GraphMinor.GM06.Section5ContractedMaskGraph
public import GraphMinor.Compute.GM06WalkDartEncoding
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM11.Walks

/-!
# Transporting encoded walks through an initial-edge collapse

For Reduction 3 of VI (5.7), page 133, walks that avoid the
contracted edge keep their original directed words. Their edge
sets and vertex sequences take their actual images under the
collapse. The finite endpoint substitution describes those same
images in the new live labelling. Induction on the encoded walk
therefore gives an encoded image walk. Injectivity on its support
preserves simplicity, and continuity gives the image point set.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.Compute GraphMinor.GM11

/-- An encoded walk avoiding the contracted edge has an encoded
image walk with exactly the same directed words. Its support and
edge list are the termwise images of the old lists. -/
theorem exists_contracted_encoded_walk
    {n k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex vertex' : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hLive : ∀ x, vertex x ∈ G.V → x ∈ A)
    (a b : Fin n) (ha : a ∈ A) (hab : a ≠ b)
    (hpoint : vertex a = cylinderM1Point k i)
    (d₀ : Fin tagged.length)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d₀) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d₀))
    (hi : InjOn π (closure (edge d₀))ᶜ)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {edge d₀}))
    (hnew : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    {s t : ClosedCylinder} (W : GraphWalk G.toGraph s t) (row : List ℕ)
    (henc : GM06WalkDartEncoding G.toGraph tagged vertex edge W row)
    (hnot : ∀ e ∈ W.edges, e ≠ edge d₀) :
    let updated := gm06ContractTaggedEdges tagged a b d₀.val
    let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
      π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)
    ∃ W' : GraphWalk G'.toGraph (π s) (π t),
      GM06WalkDartEncoding G'.toGraph updated vertex' edge' W' row ∧
      W'.support = W.support.map π ∧ W'.edges = W.edges.map (image π) := by
  let updated := gm06ContractTaggedEdges tagged a b d₀.val
  let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
    π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)
  have hπab : π (vertex a) = π (vertex b) := by
    have hx : vertex a ∈ closure (edge d₀) := hpoint.symm ▸
      (show cylinderM1Point k i ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ _).1
    have hy : vertex b ∈ closure (edge d₀) :=
      (show vertex b ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have hx' : vertex a ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    have hy' : vertex b ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hy
    exact hx'.trans hy'.symm
  have hrelab : ∀ x : Fin n,
      π (vertex (gm06ContractVertexLabel a b x)) = π (vertex x) := by
    intro x
    by_cases h : x = b
    · simpa only [gm06ContractVertexLabel, h, ite_true] using hπab
    · simp only [gm06ContractVertexLabel, h, ite_false]
  have himage := (initial_edge_collapse_links_and_injective hval hl hvs π hfiber hi hV hE).1
  revert hnot
  induction henc with
  | nil hx =>
    intro hnot
    have hx' : π _ ∈ G'.V := hV.symm ▸ mem_image_of_mem π hx
    exact ⟨.nil hx', .nil hx', rfl, rfl⟩
  | @cons x y z e hlink R rest d hd hactive hedge htail hhead hrest ihR =>
    intro hnot
    have heNot : e ≠ edge d₀ := hnot e (by simp)
    have hIndexNe : d / 2 ≠ d₀.val := by
      intro h
      exact heNot (hedge.symm.trans (congrArg edge (Fin.ext h)))
    have hrestNot : ∀ f ∈ R.edges, f ≠ edge d₀ := fun f hf => hnot f (by simp [hf])
    obtain ⟨R', hencR', hsR', heR'⟩ := ihR hrestNot
    have hlink' : G'.toGraph.IsLink (π '' e) (π x) (π y) := himage e x y heNot hlink
    have hd' : d < 2 * updated.length := by rw [gm06ContractTaggedEdges_length]; exact hd
    have hj : d / 2 < tagged.length := by omega
    have hactive' : (updated[d / 2]'(by rw [gm06ContractTaggedEdges_length]; exact hj)).2 = 1 := by
      rw [gm06ContractTaggedEdges_getElem tagged a b d₀.val hj]
      simpa only [hIndexNe, ite_false] using hactive
    have hedge' : edge' ⟨d / 2, by rw [gm06ContractTaggedEdges_length]; exact hj⟩ = π '' e := by
      change π '' edge ⟨d / 2, hj⟩ = π '' e
      exact congrArg (image π) hedge
    have htailLive : gm06DartTail tagged ⟨d, hd⟩ ∈ A :=
      hLive _ (gm06Dart_isLink G.toGraph tagged vertex edge hlinks ⟨d, hd⟩ hactive).left_mem
    have hheadLive : gm06DartHead tagged ⟨d, hd⟩ ∈ A :=
      hLive _ (gm06Dart_isLink G.toGraph tagged vertex edge hlinks ⟨d, hd⟩ hactive).right_mem
    have htail' : vertex' (gm06DartTail updated ⟨d, hd'⟩) = π x := by
      have hh : gm06DartTail updated ⟨d, hd'⟩ =
          gm06ContractVertexLabel a b (gm06DartTail tagged ⟨d, hd⟩) := by
        simpa only [Fin.cast_mk] using gm06DartTail_contract tagged a b d₀.val ⟨d, hd⟩
      rw [hh]
      rw [hnew _ (gm06ContractVertexLabel_mem_erase A a b _ ha htailLive hab), hrelab]
      exact congrArg π htail
    have hhead' : vertex' (gm06DartHead updated ⟨d, hd'⟩) = π y := by
      have hh : gm06DartHead updated ⟨d, hd'⟩ =
          gm06ContractVertexLabel a b (gm06DartHead tagged ⟨d, hd⟩) := by
        simpa only [Fin.cast_mk] using gm06DartHead_contract tagged a b d₀.val ⟨d, hd⟩
      rw [hh]
      rw [hnew _ (gm06ContractVertexLabel_mem_erase A a b _ ha hheadLive hab), hrelab]
      exact congrArg π hhead
    refine ⟨.cons hlink' R', .cons hd' hactive' hedge' htail' hhead' hencR', ?_, ?_⟩
    · simp only [GraphWalk.support_cons, hsR', List.map_cons]
    · simp only [GraphWalk.edges_cons, heR', List.map_cons]

/-- Termwise support images preserve a simple walk whenever the
collapse is injective on that walk's actual support. -/
theorem image_walk_isSimple {G G' : Drawing ClosedCylinder}
    {π : ClosedCylinder → ClosedCylinder} {s t : ClosedCylinder}
    {W : GraphWalk G.toGraph s t} {W' : GraphWalk G'.toGraph (π s) (π t)}
    (hs : W'.support = W.support.map π) (hW : W.IsSimple)
    (hi : InjOn π {x | x ∈ W.support}) : W'.IsSimple := by
  change W'.support.Nodup
  rw [hs]
  exact List.Nodup.map_on (fun x hx y hy hxy => hi hx hy hxy) hW

/-- The drawing of an image walk is the image of the old walk's
point set. Closure commutes with the continuous map because the
cylinder is compact and its target is Hausdorff. -/
theorem walkDrawing_image_pointSet {G G' : Drawing ClosedCylinder}
    (π : C(ClosedCylinder, ClosedCylinder)) {s t u v : ClosedCylinder}
    (W : GraphWalk G.toGraph s t) (W' : GraphWalk G'.toGraph u v)
    (hs : W'.support = W.support.map π) (he : W'.edges = W.edges.map (image π)) :
    (walkDrawing G' W').U = π '' (walkDrawing G W).U := by
  ext z
  rw [mem_walkDrawing_U]
  constructor
  · rintro (hz | hz)
    · rw [hs] at hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      exact ⟨x, (mem_walkDrawing_U G W (x := x)).mpr (Or.inl hx), rfl⟩
    · obtain ⟨f, hf, hzf⟩ := hz
      rw [he] at hf
      obtain ⟨e, heW, rfl⟩ := List.mem_map.mp hf
      rw [π.continuous.isClosedMap.closure_image_eq_of_continuous π.continuous] at hzf
      obtain ⟨x, hx, rfl⟩ := hzf
      exact ⟨x, (mem_walkDrawing_U G W (x := x)).mpr (Or.inr ⟨e, heW, hx⟩), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [mem_walkDrawing_U] at hx
    rcases hx with hx | ⟨e, heW, hx⟩
    · left
      rw [hs]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩
    · right
      refine ⟨π '' e, ?_, ?_⟩
      · rw [he]; exact List.mem_map.mpr ⟨e, heW, rfl⟩
      · rw [π.continuous.isClosedMap.closure_image_eq_of_continuous π.continuous]
        exact mem_image_of_mem π hx

/-- The point set of a walk beginning with an edge is the closed
first edge together with the point set of its remaining walk. -/
theorem walkDrawing_cons_pointSet {G : Drawing ClosedCylinder}
    {s v t : ClosedCylinder} {e : Set ClosedCylinder}
    (hl : G.toGraph.IsLink e s v) (R : GraphWalk G.toGraph v t) :
    (walkDrawing G (.cons hl R)).U = closure e ∪ (walkDrawing G R).U := by
  have hs : s ∈ closure e :=
    (show s ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ _).1
  ext x
  rw [mem_walkDrawing_U, mem_union, mem_walkDrawing_U]
  simp only [GraphWalk.support_cons, GraphWalk.edges_cons, List.mem_cons, exists_eq_or_imp]
  constructor
  · rintro ((rfl | hx) | (hx | hx))
    · exact Or.inl hs
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  · rintro (hx | (hx | hx))
    · exact Or.inr (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inr hx)

/-- Removing the first word of a simple initial path gives an
encoded simple image walk in the contracted drawing. Its point
set is the image of the whole original path, since the removed
closed edge collapses onto the suffix's initial vertex. -/
theorem exists_contracted_encoded_initial_suffix
    {n k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex vertex' : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hLive : ∀ x, vertex x ∈ G.V → x ∈ A)
    (a b : Fin n) (ha : a ∈ A) (hab : a ≠ b)
    (hpoint : vertex a = cylinderM1Point k i)
    (d₀ : Fin tagged.length)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d₀) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d₀))
    (hi : InjOn π (closure (edge d₀))ᶜ)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {edge d₀}))
    (hnew : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    {t : ClosedCylinder} (W : GraphWalk G.toGraph (cylinderM1Point k i) t)
    (hW : W.IsSimple) (first : ℕ) (row : List ℕ)
    (henc : GM06WalkDartEncoding G.toGraph tagged vertex edge W (first :: row))
    (hfirst : first / 2 = d₀.val) :
    let updated := gm06ContractTaggedEdges tagged a b d₀.val
    let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
      π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)
    ∃ W' : GraphWalk G'.toGraph (π (vertex b)) (π t),
      W'.IsSimple ∧ GM06WalkDartEncoding G'.toGraph updated vertex' edge' W' row ∧
      (walkDrawing G' W').U = π '' (walkDrawing G W).U := by
  obtain ⟨hd, z, e, hl₀, R, hWeq, hedge, htail, hhead, hrest⟩ := henc.first_step
  have he : e = edge d₀ := hedge.symm.trans (congrArg edge (Fin.ext hfirst))
  have hl₀' : G.toGraph.IsLink (edge d₀) (cylinderM1Point k i) z := he ▸ hl₀
  have hz : z = vertex b := hl.isLink_iff_eq.mp hl₀'
  cases hz
  have hSupport : (cylinderM1Point k i :: R.support).Nodup := by
    simpa only [hWeq, GraphWalk.IsSimple, GraphWalk.support_cons] using hW
  have hR : R.IsSimple := (List.nodup_cons.mp hSupport).2
  have hsNot : cylinderM1Point k i ∉ R.support := (List.nodup_cons.mp hSupport).1
  have hEdges : (e :: R.edges).Nodup := by
    simpa only [hWeq, GraphWalk.edges_cons] using hW.edges_nodup
  have heNot : e ∉ R.edges := (List.nodup_cons.mp hEdges).1
  have hnot : ∀ f ∈ R.edges, f ≠ edge d₀ := by
    intro f hf heq
    exact heNot ((heq.trans he.symm) ▸ hf)
  let J := induceDrawing G (G.V \ {cylinderM1Point k i})
  have hJV : J.V = G.V \ {cylinderM1Point k i} := induceDrawing_V G sdiff_subset
  have hJi : InjOn π J.U := injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi
  have hRU : ∀ x ∈ R.support, x ∈ J.U := by
    intro x hx
    apply J.V_subset_U
    rw [hJV]
    refine ⟨R.mem_vertexSet_of_mem_support hx, ?_⟩
    intro hxs
    exact hsNot (hxs ▸ hx)
  obtain ⟨W', henc', hs', he'⟩ := exists_contracted_encoded_walk tagged vertex vertex' edge A
    hlinks hLive a b ha hab hpoint d₀ hval hl hvs π hfiber hi hV hE hnew R row hrest hnot
  have hSimple : W'.IsSimple := image_walk_isSimple hs' hR
    (fun x hx y hy hxy => hJi (hRU x hx) (hRU y hy) hxy)
  have hFull : (walkDrawing G W).U = closure (edge d₀) ∪ (walkDrawing G R).U := by
    calc
      (walkDrawing G W).U = closure e ∪ (walkDrawing G R).U := by
        rw [hWeq]
        exact walkDrawing_cons_pointSet hl₀ R
      _ = _ := congrArg (fun f => closure f ∪ (walkDrawing G R).U) he
  have hCollapsed : π '' closure (edge d₀) ⊆ π '' (walkDrawing G R).U := by
    rintro y ⟨x, hx, rfl⟩
    have hpx : x ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    have hbCl : vertex b ∈ closure (edge d₀) :=
      (show vertex b ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have hpb : vertex b ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hbCl
    exact ⟨vertex b, (mem_walkDrawing_U G R).mpr (Or.inl R.start_mem_support), hpb.trans hpx.symm⟩
  refine ⟨W', hSimple, henc', ?_⟩
  rw [walkDrawing_image_pointSet π R W' hs' he', hFull, image_union,
    union_eq_right.mpr hCollapsed]

end GraphMinor.GM06
