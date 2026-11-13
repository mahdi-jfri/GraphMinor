module

public import GraphMinor.Compute.GM06ApplyReduction3
public import GraphMinor.Compute.GM06UndoDrawing
public import GraphMinor.GM06.Section5ContractedFiniteGraph
public import GraphMinor.GM06.Section5InitialEdgeCollapse
import GraphMinor.GM06.Section5ContractedDrawing
import GraphMinor.GM06.Section5ContractedLinkage
import GraphMinor.GM06.Section5ContractionBoundary
import GraphMinor.GM06.Section5Reduction3Apply
import GraphMinor.GM06.Section5ContractedCuffLabels
import GraphMinor.GM06.Section5InitialNeighbourUnique
import GraphMinor.GM06.Section5ContractedRegionEquiv

/-!
# The selected contraction's graph, linkage and inverse record

Reduction 3 in VI (5.7), page 133, updates the finite endpoint
columns, both masks, the given path and its inverse record together.
We construct one actual collapse and use it for all these parts.
The shortened row encodes its new linkage, every active endpoint
has its new geometric meaning, and UNDO has exactly the recorded
first directed word. Cuff labels remain at their original points.

The source rotation's positive cyclic order is a separate local
geometric statement. The result here constructs the remaining
parts of the drawing state without assuming that rotation order.
-/

public section
namespace GraphMinor.Compute
open Set Topology GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11

/-- An eligible first word determines one actual contraction, its
finite graph and shortened linkage, and its valid inverse record.
The chart, region bijection, graph, linkage and inverse record
are constructed using the same continuous collapse. -/
theorem exists_selected_rectangular_contraction_representation
    {n k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (hvertex : ∀ x ∈ A, vertex x ∈ G.V)
    (hcoverV : ∀ p ∈ G.V, ∃ x ∈ A, vertex x = p)
    (a b : Fin n) (hpoint : vertex a = cylinderM1Point k i)
    (d : Fin tagged.length) (hd : tagged[d].2 = 1)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i) (hoff : vertex b ∉ cylinderCuff2)
    (paths : List (List ℕ)) (hpaths : GM06LinkageRowsEncoding L tagged vertex edge paths)
    (first : ℕ) (rest : List ℕ)
    (hrow : paths[i.val]'(by rw [hpaths.1]; exact i.isLt) = first :: rest)
    (hfirst : first / 2 = d.val) :
    ∃ (π : C(ClosedCylinder, ClosedCylinder)) (G' : Drawing ClosedCylinder)
      (M : CylinderLinkage k G') (vertex' : Fin n ↪ ClosedCylinder),
      (let updated := gm06ContractTaggedEdges tagged a b d.val
      let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
        π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d.val) j)
      IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' M ∧
      π ⁻¹' {cylinderM1Point k i} = closure (edge d) ∧ InjOn π (closure (edge d))ᶜ ∧
      G'.U = π '' G.U ∧ G'.V = π '' G.V ∧ G'.E = (image π) '' (G.E \ {edge d}) ∧
      (∀ x ∈ A.erase b, vertex' x = π (vertex x)) ∧
      G'.V = vertex' '' (A.erase b : Set (Fin n)) ∧ vertex' a = cylinderM1Point k i ∧
      InjOn edge' {j | updated[j].2 = 1} ∧
      (∀ j : Fin updated.length, updated[j].2 = 1 →
        G'.toGraph.IsLink (edge' j) (vertex' updated[j].1.1) (vertex' updated[j].1.2)) ∧
      (∀ e ∈ G'.E, ∃ j : Fin updated.length, updated[j].2 = 1 ∧ edge' j = e) ∧
      GM06LinkageRowsEncoding M updated vertex' edge' (paths.set i.val rest) ∧
      (∀ x ∈ A, vertex x ∈ bd ClosedCylinder → x ∈ A.erase b ∧ vertex' x = vertex x) ∧
      GM06UndoStep n k ⟨G, tagged, vertex, edge⟩ ⟨G', updated, vertex', edge'⟩
        (some (i.val, first))) ∧
      ∃ (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
        (D : Set ClosedCylinder) (E : Section5CollapseRectangle ≃ₜ D),
        IsClosed D ∧
        (∀ t z, H (t, (E z).val) = (E (section5RectangleCollapseHomotopy (t, z))).val) ∧
        (∀ x ∉ D, ∀ t, H (t, x) = x) ∧
        (E section5RectangleOrigin).val = cylinderM1Point k i ∧
        (fun z => (E z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} = closure (edge d) ∧
        (∀ x, H (0, x) = x) ∧ (∀ x, H (1, x) = π x) ∧
        (∀ x ∈ bd ClosedCylinder, ∀ t, H (t, x) = x) ∧
        ∃ η : G.R ≃ G'.R,
          (∀ r, (η r).val = π '' r.val) ∧
          (∀ r, (η.symm r).val = π ⁻¹' r.val) ∧
          ∀ r, π '' closure r.val = closure (η r).val := by
  have hLive : ∀ x, vertex x ∈ G.V → x ∈ A := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcoverV _ hx
    exact vertex.injective hyx ▸ hy
  have ha : a ∈ A := hLive a (hpoint.symm ▸ hl.left_mem)
  have hb : b ∈ A := hLive b hl.right_mem
  have hab : a ≠ b := fun heq => hvs (heq ▸ hpoint)
  obtain ⟨W, _, henc, hP⟩ := hpaths.path i
  rw [hrow] at henc
  obtain ⟨hbound, z, f, hf, R, _, hedge, htail, hhead, _⟩ := henc.first_step
  have hfe : f = edge d := hedge.symm.trans (congrArg edge (Fin.ext hfirst))
  have hz : z = vertex b :=
    (initial_link_unique_of_valency_one hval hl hvs (hfe ▸ hf)).2
  have hePath : edge d ∈ (L.pathDrawing i).E := by
    rw [← hP, walkDrawing_E]
    exact (henc.edge_mem_iff _).mpr ⟨first, by simp, hbound, congrArg edge (Fin.ext hfirst)⟩
  have hbInterior := L.initial_neighbour_not_mem_boundary hG i hePath hl hvs hoff
  obtain ⟨π, H, D, E, hD, hchart, hout, horigin, hsegment,
      hH0, hH1, hHbd, hfiber, hhomeo, hi, hsurj, hopen, hfix⟩ :=
    exists_rectangular_collapse_of_initial_valency_one_edge L hG i hval hl hvs hoff
  have hbd : ∀ x ∈ bd ClosedCylinder, π x = x :=
    fun x hx => (hH1 x).symm.trans (hHbd x hx 1)
  have hπfix : ∀ j, j ≠ i → ∀ x ∈ (L.pathDrawing j).U, π x = x :=
    fun j hj x hx => (hH1 x).symm.trans (hfix j hj x hx 1)
  obtain ⟨G', hU, hV, hE⟩ := exists_contracted_initial_edge_drawing hval hl hvs π hfiber hi
  obtain ⟨M, hM, hothers⟩ := exists_linkage_of_initial_edge_collapse L i hval hl hvs hoff
    π hfiber hi hbd hπfix hV hE
  have hG' := isCylinderSection5Drawing_of_initial_edge_collapse hG hl π hfiber hi hbd hU hV
  have hred : Section5Reduction3Step k G L G' M :=
    ⟨i, edge d, vertex b, π, H, hval, hl.1, hl.right_mem, hvs, hoff, hl,
      hH0, hH1, hHbd, hfiber, hhomeo, hi, hsurj, hopen, hU, hV, hE, hM, hothers⟩
  obtain ⟨vertex', hnew, hnewV, hnewPoint, hnewInj, hnewLinks, hnewCover⟩ :=
    exists_contracted_finite_graph_representation tagged vertex edge A hinj hlinks hcover
      hvertex hcoverV d hd a b ha hb hab hpoint hval hl hvs π hfiber hi hV hE
  have hrows := gm06LinkageRowsEncoding_contract L M tagged vertex vertex' edge A hlinks hLive
    a b ha hab i hpoint d hval hl hvs π hfiber hi hV hE hnew hbd
    (fun j => (hM j).1) (fun j => (hM j).2) paths hpaths first rest hrow hfirst
  have hundo := GM06UndoStep.contraction i hG tagged vertex vertex' edge A hinj hlinks
    hLive a b ha hab hpoint d hd hval hl hvs π hfiber hi hV hnew H hH0 hH1 hHbd
    first hbound hfirst htail (hhead.trans hz)
  have hsNew : cylinderM1Point k i ∈ G'.U := by
    apply G'.V_subset_U
    rw [hnewV, ← hnewPoint]
    exact ⟨a, Finset.mem_erase.mpr ⟨hab, ha⟩, rfl⟩
  obtain ⟨η, hη, hηinv, hηcl⟩ := exists_initial_edge_collapse_region_equiv hl π
    hfiber hi hsurj hsNew hU
  refine ⟨π, G', M, vertex', ?_, H, D, E, hD, hchart, hout, horigin, hsegment,
    hH0, hH1, hHbd, η, hη, hηinv, hηcl⟩
  refine ⟨hG', hred, hfiber, hi, hU, hV, hE, hnew, hnewV,
    hnewPoint, hnewInj, hnewLinks, hnewCover, hrows, ?_, hundo⟩
  intro x hx hxBd
  exact contracted_label_eq_on_boundary vertex vertex' A b hbInterior π hbd hnew hx hxBd

/-- An eligible first word determines one actual contraction, its
finite graph and shortened linkage, and its valid inverse record.
All three are constructed using the same continuous collapse. -/
theorem exists_selected_contraction_representation
    {n k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (hvertex : ∀ x ∈ A, vertex x ∈ G.V)
    (hcoverV : ∀ p ∈ G.V, ∃ x ∈ A, vertex x = p)
    (a b : Fin n) (hpoint : vertex a = cylinderM1Point k i)
    (d : Fin tagged.length) (hd : tagged[d].2 = 1)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i) (hoff : vertex b ∉ cylinderCuff2)
    (paths : List (List ℕ)) (hpaths : GM06LinkageRowsEncoding L tagged vertex edge paths)
    (first : ℕ) (rest : List ℕ)
    (hrow : paths[i.val]'(by rw [hpaths.1]; exact i.isLt) = first :: rest)
    (hfirst : first / 2 = d.val) :
    ∃ (π : C(ClosedCylinder, ClosedCylinder)) (G' : Drawing ClosedCylinder)
      (M : CylinderLinkage k G') (vertex' : Fin n ↪ ClosedCylinder),
      let updated := gm06ContractTaggedEdges tagged a b d.val
      let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
        π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d.val) j)
      IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' M ∧
      π ⁻¹' {cylinderM1Point k i} = closure (edge d) ∧ InjOn π (closure (edge d))ᶜ ∧
      G'.U = π '' G.U ∧ G'.V = π '' G.V ∧ G'.E = (image π) '' (G.E \ {edge d}) ∧
      (∀ x ∈ A.erase b, vertex' x = π (vertex x)) ∧
      G'.V = vertex' '' (A.erase b : Set (Fin n)) ∧ vertex' a = cylinderM1Point k i ∧
      InjOn edge' {j | updated[j].2 = 1} ∧
      (∀ j : Fin updated.length, updated[j].2 = 1 →
        G'.toGraph.IsLink (edge' j) (vertex' updated[j].1.1) (vertex' updated[j].1.2)) ∧
      (∀ e ∈ G'.E, ∃ j : Fin updated.length, updated[j].2 = 1 ∧ edge' j = e) ∧
      GM06LinkageRowsEncoding M updated vertex' edge' (paths.set i.val rest) ∧
      (∀ x ∈ A, vertex x ∈ bd ClosedCylinder → x ∈ A.erase b ∧ vertex' x = vertex x) ∧
      GM06UndoStep n k ⟨G, tagged, vertex, edge⟩ ⟨G', updated, vertex', edge'⟩
        (some (i.val, first)) := by
  obtain ⟨π, G', M, vertex', hrep, _⟩ :=
    exists_selected_rectangular_contraction_representation L hG i tagged vertex edge A
      hinj hlinks hcover hvertex hcoverV a b hpoint d hd hval hl hvs hoff
      paths hpaths first rest hrow hfirst
  exact ⟨π, G', M, vertex', hrep⟩

/-- The actual RAM contraction constructs a proper reduced drawing,
its finite active graph and its shortened given linkage. Its history
write is interpreted by the inverse operation proved above. The
rotation array is its exact numeric splice; its geometric order is
established separately. -/
theorem gm06ApplyReduction3Prog_graph
    {w n k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (hvertex : ∀ x ∈ A, vertex x ∈ G.V)
    (hcoverV : ∀ p ∈ G.V, ∃ x ∈ A, vertex x = p)
    (a b : Fin n) (hpoint : vertex a = cylinderM1Point k i)
    (d : Fin tagged.length) (hd : tagged[d].2 = 1)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink (edge d) (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i) (hoff : vertex b ∉ cylinderCuff2)
    (paths : List (List ℕ)) (hpaths : GM06LinkageRowsEncoding L tagged vertex edge paths)
    (first : ℕ) (rest : List ℕ)
    (hrow : paths[i.val]'(by rw [hpaths.1]; exact i.isLt) = first :: rest)
    (hfirst : first / 2 = d.val)
    (rots : List (List ℕ)) (hrots : rots.length = n)
    (hnda : (rots[a.val]'(hrots.symm ▸ a.isLt)).Nodup)
    (hndb : (rots[b.val]'(hrots.symm ▸ b.isLt)).Nodup)
    (hrotD : first ∈ rots[a.val]'(hrots.symm ▸ a.isLt))
    (hrotMate : gm06DartMate first ∈ rots[b.val]'(hrots.symm ▸ b.isLt))
    (hist : List ℕ) (c : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hrotLen : 4 * (gm06EncodeRows rots).length < 2 ^ w)
    (hrotWords : ∀ x ∈ gm06EncodeRows rots, x < 2 ^ w)
    (hpathLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpathWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hhist : hist.length < 2 ^ w) (hslot : 2 * c + 1 < hist.length)
    (h3 : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (h4 : s.arrs 4 = gm06EncodeRows rots) (h8 : s.arrs 8 = gm06EncodeRows paths)
    (h9 : s.arrs 9 = hist) (h12 : s.arrs 12 = tagged.map Prod.snd)
    (h14 : s.arrs 14 = gm02VertexBits A)
    (h22 : s.regs 22 = a.val) (h301 : s.regs 301 = b.val)
    (h328 : s.regs 328 = i.val) (h23 : s.regs 23 = first)
    (h24 : s.regs 24 = gm06DartMate first) (h309 : s.regs 309 = c) :
    ∃ s' t, Exec w gm06ApplyReduction3Prog s s' t ∧
      t ≤ 682 + 28 * tagged.length + 1000 * (gm06EncodeRows rots).length +
        17 * i.val + 22 * (rest.length + 1) + 32 * (gm06EncodeRows paths).length ∧
      TwoPaths.Keeps [295, 309, 31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98,
        311, 310, 312, 308, 307] [9, 25, 26, 27, 4, 28, 24, 8, 3, 12, 14] s s' ∧
      s'.regs 309 = c + 1 ∧ s'.arrs 9 = (hist.set (2 * c) i.val).set (2 * c + 1) first ∧
      s'.arrs 4 = gm06EncodeRows ((rots.set a.val
        (gm06SplicedRotation rots[a.val] rots[b.val]
          (rots[a.val].idxOf first) (rots[b.val].idxOf (gm06DartMate first)))).set b.val []) ∧
      s'.arrs 8 = gm06EncodeRows (paths.set i.val rest) ∧
      (s'.arrs 12).count 1 + 1 = (s.arrs 12).count 1 ∧
      (s'.arrs 14).count 1 + 1 = (s.arrs 14).count 1 ∧
      ∃ (π : C(ClosedCylinder, ClosedCylinder)) (G' : Drawing ClosedCylinder)
        (M : CylinderLinkage k G') (vertex' : Fin n ↪ ClosedCylinder),
        let updated := gm06ContractTaggedEdges tagged a b d.val
        let edge' : Fin updated.length → Set ClosedCylinder := fun j =>
          π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d.val) j)
        IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' M ∧
        s'.arrs 3 = gm06EndpointWords (updated.map fun p => (p.1.1.val, p.1.2.val)) ∧
        s'.arrs 12 = updated.map Prod.snd ∧ s'.arrs 14 = gm02VertexBits (A.erase b) ∧
        G'.V = vertex' '' (A.erase b : Set (Fin n)) ∧ vertex' a = cylinderM1Point k i ∧
        InjOn edge' {j | updated[j].2 = 1} ∧
        (∀ j : Fin updated.length, updated[j].2 = 1 →
          G'.toGraph.IsLink (edge' j) (vertex' updated[j].1.1) (vertex' updated[j].1.2)) ∧
        (∀ e ∈ G'.E, ∃ j : Fin updated.length, updated[j].2 = 1 ∧ edge' j = e) ∧
        GM06LinkageRowsEncoding M updated vertex' edge' (paths.set i.val rest) ∧
        (∀ x ∈ A, vertex x ∈ bd ClosedCylinder → x ∈ A.erase b ∧ vertex' x = vertex x) ∧
        GM06UndoStep n k ⟨G, tagged, vertex, edge⟩ ⟨G', updated, vertex', edge'⟩
          (some (i.val, first)) := by
  obtain ⟨π, G', M, vertex', hG', hred, _, _, _, _, _, _, hnewV, hpoint',
      hinj', hlinks', hcover', hpaths', hcuffs, hundo⟩ :=
    exists_selected_contraction_representation L hG i tagged vertex edge A hinj hlinks hcover
      hvertex hcoverV a b hpoint d hd hval hl hvs hoff paths hpaths first rest hrow hfirst
  have hip : i.val < paths.length := by rw [hpaths.1]; exact i.isLt
  have hne : 0 < paths[i.val].length := by simp only [hrow, List.length_cons]; omega
  have hab : a.val ≠ b.val := fun heq => hvs ((Fin.ext heq : a = b) ▸ hpoint)
  have hbound : first < 2 * tagged.length := by have hh := d.isLt; omega
  have hbA : b ∈ A := by
    obtain ⟨x, hx, hxb⟩ := hcoverV _ hl.right_mem
    exact vertex.injective hxb ▸ hx
  have hlive : (gm02VertexBits A)[b.val]'(by simp only [gm02VertexBits, List.length_ofFn]; exact b.isLt) = 1 := by
    simp only [gm02VertexBits, List.getElem_ofFn, Fin.eta, hbA, ite_true]
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  have hxsLen : xs.length = 2 * tagged.length := by
    simp only [xs, gm06EndpointWords_length, List.length_map]
  have hxsWords : ∀ x ∈ xs, x < 2 ^ w := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact q.1.1.isLt.trans hn
    · exact q.1.2.isLt.trans hn
  obtain ⟨s', t, he, ht, hk, _, hcount, hhist', hends, hrots', hpath', hmask, hLive,
      hmaskDrop, hLiveDrop, _, _⟩ :=
    gm06ApplyReduction3Prog_exec xs (tagged.map Prod.snd) (gm02VertexBits A) hist rots paths
      a.val b.val i.val (gm06DartMate first) c (hrots.symm ▸ a.isLt) (hrots.symm ▸ b.isLt)
      hab hip hne hnda hndb (by simpa only [hrow, List.getElem_cons_zero] using hrotD)
      hrotMate s hw hrotLen hrotWords hpathLen hpathWords (hxsLen.symm ▸ hm)
      (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
      (by simpa only [List.length_map] using hm) hxsWords (a.isLt.trans hn)
      (by simpa only [gm02VertexBits, List.length_ofFn] using b.isLt)
      (by simpa only [hrow, List.getElem_cons_zero, List.length_map] using hbound)
      (by simpa only [hrow, List.getElem_cons_zero, hfirst, List.getElem_map, Fin.getElem_fin] using hd)
      hlive hhist hslot h3 h4 h8 h9 h12 h14 h22 h301 h328
      (by simpa only [hrow, List.getElem_cons_zero] using h23) h24 h309
  have htime : t ≤ 682 + 28 * tagged.length + 1000 * (gm06EncodeRows rots).length +
      17 * i.val + 22 * (rest.length + 1) + 32 * (gm06EncodeRows paths).length := by
    rw [hxsLen, hrow, List.length_cons] at ht
    omega
  refine ⟨s', t, he, htime, hk, hcount, ?_, ?_, ?_, ?_, ?_, π, G', M, vertex', hG', hred,
    ?_, ?_, ?_, hnewV, hpoint', hinj', hlinks', hcover', hpaths', hcuffs, hundo⟩
  · simpa only [hrow, List.getElem_cons_zero] using hhist'
  · simpa only [hrow, List.getElem_cons_zero] using hrots'
  · simpa only [hrow, List.tail_cons] using hpath'
  · simpa only [h12] using hmaskDrop
  · simpa only [h14] using hLiveDrop
  · rw [gm06ContractTaggedEdges_endpointWords]; exact hends
  · rw [gm06ContractTaggedEdges_activity]
    simpa only [hrow, List.getElem_cons_zero, hfirst] using hmask
  · rw [← gm06VertexBits_set_zero]
    exact hLive

end GraphMinor.Compute
