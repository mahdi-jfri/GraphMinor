module

public import GraphMinor.GM06.Section5ContractedWalkEncoding
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5Red

/-!
# The ordinary path rows represent a cylinder linkage

A linkage consists of the disjoint paths defined in VI, pages
127–128. Its supplied row field records a simple walk for each
path, with directed edge words and the same path drawing. This
relation only interprets that ordinary input field. Removing the
selected initial word and keeping the other rows gives an encoding
of the actual contracted linkage in VI (5.7), page 133.
-/

public section
namespace GraphMinor.Compute
open Set Topology GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

/-- The path field has one row per given linkage path, encoding
its oriented simple walk in the current finite active graph. -/
@[expose] def GM06LinkageRowsEncoding {n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (tagged : List ((Fin n × Fin n) × ℕ))
    (vertex : Fin n → ClosedCylinder) (edge : Fin tagged.length → Set ClosedCylinder)
    (rows : List (List ℕ)) : Prop :=
  rows.length = k ∧ ∀ j : Fin k,
    ∃ W : GraphWalk G.toGraph (cylinderM1Point k j) (L.curve j 1),
      W.IsSimple ∧ GM06WalkDartEncoding G.toGraph tagged vertex edge W (rows[j.val]?.getD []) ∧
      walkDrawing G W = L.pathDrawing j

namespace GM06LinkageRowsEncoding

/-- Read the actual indexed path row from its encoding relation. -/
theorem path {n k : ℕ} {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (h : GM06LinkageRowsEncoding L tagged vertex edge rows) (j : Fin k) :
    ∃ W : GraphWalk G.toGraph (cylinderM1Point k j) (L.curve j 1),
      W.IsSimple ∧ GM06WalkDartEncoding G.toGraph tagged vertex edge W
        (rows[j.val]'(by rw [h.1]; exact j.isLt)) ∧ walkDrawing G W = L.pathDrawing j := by
  simpa only [List.getElem?_eq_getElem (show j.val < rows.length by rw [h.1]; exact j.isLt),
    Option.getD_some] using h.2 j

/-- Every row of a linkage encoding is nonempty, because its path
has distinct initial and terminal vertices. -/
theorem row_nonempty {n k : ℕ} {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (h : GM06LinkageRowsEncoding L tagged vertex edge rows) (j : Fin k) :
    0 < (rows[j.val]'(by have hh := h.1; omega)).length := by
  obtain ⟨W, _, henc, _⟩ := h.path j
  have hlen := henc.length_eq
  by_contra hpos
  have hz : W.length = 0 := by
    change W.edges.length = 0
    omega
  exact isPathDrawing_start_ne_end (L.isPath j) (GraphWalk.eq_of_length_eq_zero hz)

/-- The first supplied word of each linkage row is active, lies
on that actual path and reads its initial vertex label. All three
facts follow from the ordinary walk encoding. -/
theorem first_word_data {n k : ℕ} {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (h : GM06LinkageRowsEncoding L tagged vertex edge rows) (j : Fin k)
    (hinj : Function.Injective vertex) (a : Fin n) (ha : vertex a = cylinderM1Point k j) :
    ∃ (first : ℕ) (rest : List ℕ) (hd : first < 2 * tagged.length),
      (rows[j.val]'(by rw [h.1]; exact j.isLt)) = first :: rest ∧
      (tagged[first / 2]'(by omega)).2 = 1 ∧
      edge ⟨first / 2, by omega⟩ ∈ (L.pathDrawing j).E ∧
      (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[first]?.getD 0 = a.val := by
  obtain ⟨W, hW, henc, hP⟩ := h.path j
  cases hrow : rows[j.val]'(by rw [h.1]; exact j.isLt) with
  | nil =>
    have hh := h.row_nonempty j
    rw [hrow] at hh
    simp only [List.length_nil] at hh
    omega
  | cons first rest =>
    rw [hrow] at henc
    obtain ⟨hd, hactive⟩ := henc.active_words first (by simp)
    refine ⟨first, rest, hd, rfl, hactive, ?_, henc.first_source_word hinj a ha⟩
    rw [← hP, walkDrawing_E]
    exact (henc.edge_mem_iff _).mpr ⟨first, by simp, hd, rfl⟩

end GM06LinkageRowsEncoding

private theorem subdrawing_eq_of_pointSet_eq {G P Q : Drawing ClosedCylinder}
    (hP : P.IsSubdrawing G) (hQ : Q.IsSubdrawing G) (hU : P.U = Q.U) : P = Q := by
  have hVerts : ∀ {P Q : Drawing ClosedCylinder}, P.IsSubdrawing G → Q.IsSubdrawing G →
      P.U = Q.U → P.V ⊆ Q.V := by
    intro P Q hP hQ hU x hx
    by_contra hxQ
    have hxU : x ∈ Q.U := hU ▸ P.V_subset_U hx
    obtain ⟨e, he, hxe⟩ := Q.exists_edge_of_mem hxU hxQ
    exact ((hQ.2 he).2.1 hxe).2 (hP.1 hx)
  have hEdges : ∀ {P Q : Drawing ClosedCylinder}, P.IsSubdrawing G → Q.IsSubdrawing G →
      P.U = Q.U → P.E ⊆ Q.E := by
    intro P Q hP hQ hU e he
    obtain ⟨x, hx⟩ := he.1
    have hxU : x ∈ Q.U := hU ▸ (he.2.1 hx).1
    have hxV : x ∉ Q.V := fun h => ((hP.2 he).2.1 hx).2 (hQ.1 h)
    obtain ⟨f, hf, hxf⟩ := Q.exists_edge_of_mem hxU hxV
    rw [G.edge_eq_of_mem (hP.2 he) (hQ.2 hf) hx hxf]
    exact hf
  exact Drawing.ext_of_V_E
    (subset_antisymm (hVerts hP hQ hU) (hVerts hQ hP hU.symm))
    (subset_antisymm (hEdges hP hQ hU) (hEdges hQ hP hU.symm))

private theorem encoded_walk_endpoints {n : ℕ} {G : Drawing ClosedCylinder}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {row : List ℕ} {P : Drawing ClosedCylinder}
    {s' t' s t : ClosedCylinder} (hs : s' = s) (ht : t' = t)
    (h : ∃ W : GraphWalk G.toGraph s' t', W.IsSimple ∧
      GM06WalkDartEncoding G.toGraph tagged vertex edge W row ∧ walkDrawing G W = P) :
    ∃ W : GraphWalk G.toGraph s t, W.IsSimple ∧
      GM06WalkDartEncoding G.toGraph tagged vertex edge W row ∧ walkDrawing G W = P := by
  cases hs
  cases ht
  exact h

/-- In the actual initial-edge collapse, replacing the selected
row by its tail and leaving every other row fixed represents the
new linkage. Each resulting walk and its complete path drawing
are constructed from the old encoded paths. -/
theorem gm06LinkageRowsEncoding_contract
    {n k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G) (M : CylinderLinkage k G')
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex vertex' : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hLive : ∀ x, vertex x ∈ G.V → x ∈ A)
    (a b : Fin n) (ha : a ∈ A) (hab : a ≠ b) (i : Fin k)
    (hpoint : vertex a = cylinderM1Point k i) (d₀ : Fin tagged.length)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d₀) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d₀)) (hi : InjOn π (closure (edge d₀))ᶜ)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {edge d₀}))
    (hnew : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
    (hbd : ∀ x ∈ bd ClosedCylinder, π x = x)
    (hMU : ∀ j, (M.pathDrawing j).U = π '' (L.pathDrawing j).U)
    (hHom : ∀ j, CurvesHomotopic (M.curve j) (π.comp (L.curve j)))
    (rows : List (List ℕ)) (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    (first : ℕ) (rest : List ℕ) (hrow : rows[i.val]'(by have hh := hrows.1; omega) = first :: rest)
    (hfirst : first / 2 = d₀.val) :
    let updated := gm06ContractTaggedEdges tagged a b d₀.val
    let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
      π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)
    GM06LinkageRowsEncoding M updated vertex' edge' (rows.set i.val rest) := by
  let updated := gm06ContractTaggedEdges tagged a b d₀.val
  let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
    π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)
  have hTerm : ∀ j, π (L.curve j 1) = M.curve j 1 := by
    intro j
    obtain ⟨H, _, h0, h1, hs0, hs1, ht0, ht1⟩ := hHom j
    exact (ht1 0).symm.trans (ht0 0)
  have hStart : ∀ j, π (cylinderM1Point k j) = cylinderM1Point k j :=
    fun j => hbd _ (cylinderM1Point_mem_bd k j)
  obtain ⟨Wi, hWi, henci, hPi⟩ := hrows.path i
  rw [hrow] at henci
  obtain ⟨hd, z, e, hl₀, R, hWeq, hedge, htail, hhead, hrest⟩ := henci.first_step
  have he : e = edge d₀ := hedge.symm.trans (congrArg edge (Fin.ext hfirst))
  have hePi : edge d₀ ∈ (L.pathDrawing i).E := by
    rw [← hPi, walkDrawing_E]
    change edge d₀ ∈ Wi.edges
    rw [hWeq, GraphWalk.edges_cons]
    exact List.mem_cons.mpr (Or.inl he.symm)
  have hπb : π (vertex b) = cylinderM1Point k i := by
    have hx : vertex b ∈ closure (edge d₀) :=
      (show vertex b ∈ closure (edge d₀) ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have hx' : vertex b ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    exact hx'
  refine ⟨by simpa only [List.length_set] using hrows.1, ?_⟩
  intro j
  have hjRows : j.val < rows.length := by rw [hrows.1]; exact j.isLt
  rw [List.getElem?_eq_getElem (show j.val < (rows.set i.val rest).length by simpa only [List.length_set] using hjRows),
    Option.getD_some]
  by_cases hji : j = i
  · subst j
    have hex := exists_contracted_encoded_initial_suffix tagged vertex vertex' edge A hlinks hLive
      a b ha hab hpoint d₀ hval hl hvs π hfiber hi hV hE hnew Wi hWi first rest henci hfirst
    obtain ⟨W', hSimple, henc', hWU⟩ := hex
    have hExists : ∃ W' : GraphWalk G'.toGraph (π (vertex b)) (π (L.curve i 1)),
        W'.IsSimple ∧ GM06WalkDartEncoding G'.toGraph updated vertex' edge' W' rest ∧
        walkDrawing G' W' = M.pathDrawing i := by
      refine ⟨W', hSimple, henc', ?_⟩
      apply subdrawing_eq_of_pointSet_eq (walkDrawing_isSubdrawing G' W') (M.isSubdrawing i).1
      exact hWU.trans ((congrArg (image π) (congrArg Drawing.U hPi)).trans (hMU i).symm)
    simpa only [List.getElem_set_self] using encoded_walk_endpoints hπb (hTerm i) hExists
  · obtain ⟨W, hW, henc, hP⟩ := hrows.path j
    have hnot : ∀ f ∈ W.edges, f ≠ edge d₀ := by
      intro f hf hfe
      obtain ⟨x, hx⟩ := hePi.1
      have hxi : x ∈ (L.pathDrawing i).U := (L.pathDrawing i).closure_subset_U hePi (subset_closure hx)
      have hxj : x ∈ (L.pathDrawing j).U := by
        rw [← hP, mem_walkDrawing_U]
        exact Or.inr ⟨f, hf, hfe.symm ▸ subset_closure hx⟩
      exact disjoint_left.mp (L.pairwise_disjoint hji) hxj hxi
    let J := induceDrawing G (G.V \ {cylinderM1Point k i})
    have hJV : J.V = G.V \ {cylinderM1Point k i} := induceDrawing_V G sdiff_subset
    have hJi : InjOn π J.U := injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi
    have hWU : ∀ x ∈ W.support, x ∈ J.U := by
      intro x hx
      apply J.V_subset_U
      rw [hJV]
      refine ⟨W.mem_vertexSet_of_mem_support hx, ?_⟩
      intro hxs
      have hxj : x ∈ (L.pathDrawing j).U := by
        rw [← hP, mem_walkDrawing_U]; exact Or.inl hx
      have hxi : x ∈ (L.pathDrawing i).U := by
        rw [hxs, ← (L.curve_parametrizes i).2.1]
        exact ⟨0, (L.curve_parametrizes i).2.2.1⟩
      exact disjoint_left.mp (L.pairwise_disjoint hji) hxj hxi
    obtain ⟨W', henc', hs', he'⟩ := exists_contracted_encoded_walk tagged vertex vertex' edge A
      hlinks hLive a b ha hab hpoint d₀ hval hl hvs π hfiber hi hV hE hnew W (rows[j.val]'hjRows) henc hnot
    have hSimple := image_walk_isSimple hs' hW (fun x hx y hy hxy => hJi (hWU x hx) (hWU y hy) hxy)
    have hWU' : (walkDrawing G' W').U = (M.pathDrawing j).U := by
      rw [walkDrawing_image_pointSet π W W' hs' he', hP, hMU]
    have hExists : ∃ W' : GraphWalk G'.toGraph (π (cylinderM1Point k j)) (π (L.curve j 1)),
        W'.IsSimple ∧ GM06WalkDartEncoding G'.toGraph updated vertex' edge' W' (rows[j.val]'hjRows) ∧
        walkDrawing G' W' = M.pathDrawing j :=
      ⟨W', hSimple, henc', subdrawing_eq_of_pointSet_eq (walkDrawing_isSubdrawing G' W') (M.isSubdrawing j).1 hWU'⟩
    have hne : i.val ≠ j.val := fun h => hji (Fin.ext h.symm)
    simpa only [List.getElem_set_ne hne] using encoded_walk_endpoints (hStart j) (hTerm j) hExists

end GraphMinor.Compute
