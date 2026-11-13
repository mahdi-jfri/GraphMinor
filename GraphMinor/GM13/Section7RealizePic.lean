module

public import GraphMinor.GM13.Section7LatPic

/-!
# Graph Minors XIII, (7.3): the picture of a realization

A realization `R` of a shape `τ` from height `h` to height `h'` (`Shape.Realization`) sends each
vertex `p` of the elementary wall of height `h'` to an old vertex `R.vmap p`, and each edge `pq`
to an old path `R.full p q`. Drawn as in Fig. 1, these old vertices and paths form a lattice
picture of the wall of height `h'` (`Shape.Realization.pic`): the cells of the edge `pq` are the
kept cells that go to `pq`. The wall of Fig. 1 of height `h'` is another lattice picture
(`stdPic`). If the rays of the side vertices leave the kept cells (`Realization.RayOK`) and
`R.vmap` keeps the order of the rows (`Realization.RowMono`), both pictures are good, and
`LatPic.Good.exists_homeo` gives a homeomorphism of the plane that maps each cell `m'` of the
new wall onto the old cells that go to `m'` (`Realization.exists_homeo`).

The edges of the picture of a realization are lines since a path of the elementary wall that does
not repeat vertices is drawn as a line (`pathCells_isLine`), by induction with
`IsLineWithEnds.union`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open GraphMinor.Surface
open GraphMinor.GM16 (latticePoint)

/-- The segment of an edge `pq` of the elementary wall is a line from `p` to `q`. -/
theorem fig1Segment_isLine {h : ℕ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    IsLineWithEnds (fig1Segment p q) (latticePoint p) (latticePoint q) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rcases hpq.2.2 with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · simp only at hy hx
    subst hy
    rcases hx with rfl | rfl
    · simp only [fig1Segment, ↓reduceIte, min_self, show min p1 (p1 + 1) = p1 by omega]
      exact GraphMinor.GM16.horizontalLatticeLine_isLine p1 p2
    · simp only [fig1Segment, ↓reduceIte, min_self, show min (q1 + 1) q1 = q1 by omega]
      exact (GraphMinor.GM16.horizontalLatticeLine_isLine q1 p2).symm
  · simp only at hy hx
    subst hx
    rcases hy with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [fig1Segment, show p2 ≠ p2 + 1 by omega, ↓reduceIte, min_self,
        show min p2 (p2 + 1) = p2 by omega]
      exact GraphMinor.GM16.verticalLatticeLine_isLine p1 p2
    · simp only [fig1Segment, show q2 + 1 ≠ q2 by omega, ↓reduceIte, min_self,
        show min (q2 + 1) q2 = q2 by omega]
      exact (GraphMinor.GM16.verticalLatticeLine_isLine p1 q2).symm

theorem cellSet_inter (A B : Set (ℤ × ℤ)) : cellSet A ∩ cellSet B = cellSet (A ∩ B) := rfl

/-! ## Paths of the elementary wall are drawn as lines -/

/-- The cells of a path of the elementary wall given by its list of vertices: the cells of its
vertices and of its edges. -/
def pathCells (L : List (ℕ × ℕ)) : Set (ℤ × ℤ) :=
  {m | ∃ u ∈ L, m = vCell u} ∪ {m | ∃ uw ∈ L.zip L.tail, m = eCell uw.1 uw.2}

theorem pathCells_cons_cons (a b : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    pathCells (a :: b :: l) = {vCell a, eCell a b, vCell b} ∪ pathCells (b :: l) := by
  ext m
  simp only [pathCells, List.tail_cons, List.zip_cons_cons, mem_union, mem_ofPred_eq,
    List.mem_cons, exists_eq_or_imp, mem_insert_iff, mem_singleton_iff]
  generalize (∃ a ∈ l, m = vCell a) = A
  generalize (∃ a ∈ (b :: l).zip l, m = eCell a.1 a.2) = B
  tauto

theorem mem_of_mem_zip_tail {L : List (ℕ × ℕ)} {uw : (ℕ × ℕ) × (ℕ × ℕ)}
    (h : uw ∈ L.zip L.tail) : uw.1 ∈ L ∧ uw.2 ∈ L :=
  ⟨(List.of_mem_zip h).1, List.mem_of_mem_tail (List.of_mem_zip h).2⟩

/-- **A path of the elementary wall is drawn as a line** from its first vertex to its last. -/
theorem pathCells_isLine {h : ℕ} : ∀ (l : List (ℕ × ℕ)) (a b : ℕ × ℕ),
    List.IsChain (elementaryWallAdj h) (a :: b :: l) → (a :: b :: l).Nodup →
    IsLineWithEnds (cellSet (pathCells (a :: b :: l))) (latticePoint a)
      (latticePoint ((b :: l).getLast (List.cons_ne_nil _ _)))
  | [], a, b, hc, _ => by
    have hab := (List.isChain_cons_cons.mp hc).1
    have : pathCells [a, b] = fig1SegmentCells a b := by
      rw [pathCells_cons_cons, fig1SegmentCells_eq hab]
      ext m
      simp only [pathCells, List.tail_cons, List.zip_nil_right, List.not_mem_nil, false_and,
        exists_false, ofPred_false, union_empty, List.mem_singleton, exists_eq_left, mem_union,
        mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
      tauto
    rw [this, ← fig1Segment_eq_cellSet]
    exact fig1Segment_isLine hab
  | c :: l, a, b, hc, hn => by
    have hab := (List.isChain_cons_cons.mp hc).1
    have hc' := (List.isChain_cons_cons.mp hc).2
    have hn' := (List.nodup_cons.mp hn).2
    have ha := (List.nodup_cons.mp hn).1
    have ih := pathCells_isLine l b c hc' hn'
    rw [pathCells_cons_cons]
    rw [show cellSet ({vCell a, eCell a b, vCell b} ∪ pathCells (b :: c :: l)) =
      cellSet {vCell a, eCell a b, vCell b} ∪ cellSet (pathCells (b :: c :: l)) from rfl,
      List.getLast_cons (List.cons_ne_nil _ _)]
    have hseg := fig1Segment_isLine hab
    rw [fig1Segment_eq_cellSet, fig1SegmentCells_eq hab] at hseg
    refine hseg.union ih ?_
    rw [cellSet_inter, ← cellSet_vCell]
    congr 1
    ext m
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff, pathCells, mem_union,
      mem_ofPred_eq]
    constructor
    · rintro ⟨hm | hm | hm, hm'⟩
      · exfalso
        subst hm
        rcases hm' with ⟨u, hu, e⟩ | ⟨uw, huw, e⟩
        · exact ha (vCell_injective e ▸ hu)
        · exact eCell_ne_vCell (List.rel_of_mem_zip_of_isChain hc' uw huw) a e.symm
      · exfalso
        subst hm
        rcases hm' with ⟨u, hu, e⟩ | ⟨uw, huw, e⟩
        · exact eCell_ne_vCell hab u e
        · have hs := sym2_eq_of_eCell_eq hab (List.rel_of_mem_zip_of_isChain hc' uw huw) e
          have hm := mem_of_mem_zip_tail huw
          rcases Sym2.eq_iff.mp hs with ⟨e1, -⟩ | ⟨e1, -⟩
          · exact ha (e1 ▸ hm.1)
          · exact ha (e1 ▸ hm.2)
      · exact hm
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), Or.inl ⟨b, List.mem_cons_self, rfl⟩⟩

/-! ## The wall of Fig. 1 as a lattice picture -/

/-- The wall of Fig. 1 of height `h` as a lattice picture: the vertex `p` at the point `p`, and
the edge `pq` on its open unit segment. -/
def stdPic (h : ℕ) : LatPic h where
  vpt p := ((p.1 : ℤ), (p.2 : ℤ))
  ecells p q := {eCell p q}

theorem stdPic_vc (h : ℕ) (p : ℕ × ℕ) : (stdPic h).vc p = vCell p := rfl

theorem stdPic_pt (h : ℕ) (p : ℕ × ℕ) : (stdPic h).pt p = latticePoint p := by
  simp [LatPic.pt, stdPic, latticePoint]

/-- **The wall of Fig. 1 is a good lattice picture.** Its rays go out of the wall at once. -/
theorem stdPic_good {h : ℕ} (hh : 2 ≤ h) (he : Even h) : (stdPic h).Good := by
  refine LatPic.good_of (K := fig1WallCells h) (fun p q hpq => ?_) (fun p q _ => ?_)
    (fun p q p' q' hpq hpq' hne => ?_) (fun p q hpq r _ => ?_) (fun p _ q _ e => ?_)
    (fun p q hpq => ?_) (fun p hp => mem_fig1WallCells_vCell hh he hp)
    (fun p hp hs m hm hmK => ?_) (fun p _ q _ hlt => ?_)
  · rw [stdPic_pt, stdPic_pt]
    have : (stdPic h).closedCells p q = fig1SegmentCells p q := by
      rw [fig1SegmentCells_eq hpq]
      simp only [LatPic.closedCells, stdPic_vc]
      simp only [stdPic]
      ext m
      simp only [mem_union, mem_insert_iff, mem_singleton_iff]
      tauto
    rw [this, ← fig1Segment_eq_cellSet]
    exact fig1Segment_isLine hpq
  · simp only [stdPic, eCell_comm]
  · simp only [stdPic, disjoint_singleton]
    exact fun e => hne (sym2_eq_of_eCell_eq hpq hpq' e)
  · simp only [stdPic, mem_singleton_iff]
    exact fun e => eCell_ne_vCell hpq r e.symm
  · simp only [stdPic, Prod.mk.injEq, Nat.cast_inj] at e
    exact Prod.ext e.1 e.2
  · simp only [stdPic, singleton_subset_iff]
    exact mem_fig1WallCells_eCell hh he hpq
  · rw [mem_fig1WallCells_iff (by omega) he] at hmK
    obtain ⟨hp1, hp2, -, -⟩ := hp
    unfold LatPic.ray at hm
    rw [stdPic_vc, vCell, mem_rayCells_iff (isAxisDir_sideDir h p)] at hm
    rw [stdPic_vc, vCell]
    unfold IsSideVert at hs
    unfold sideDir at hm
    unfold IsWallCell at hmK
    obtain ⟨m1, m2⟩ := m
    split_ifs at hm <;> simp only [Int.reduceNeg, true_implies, zero_ne_one, false_implies,
      one_ne_zero, reduceCtorEq, and_true, true_and, neg_eq_zero, Prod.mk.injEq] at hm hmK ⊢ <;>
      omega
  · simp only [stdPic]
    exact_mod_cast hlt

/-! ## The lattice picture of a realization -/

namespace Shape.Realization

variable {h h' : ℕ} {τ : Shape h h'} (R : τ.Realization)

/-- **The rays leave the kept cells**: the ray of each side vertex of the new wall, started at its
old vertex, meets no kept cell but its start. -/
def RayOK : Prop :=
  ∀ p ∈ elementaryWallVerts h', IsSideVert h' p →
    ∀ m ∈ rayCells (vCell (R.vmap p)) (sideDir h' p), m ∈ fig1WallCells h → τ.own m ≠ none →
      m = vCell (R.vmap p)

/-- **The old vertices keep the order of the rows.** -/
def RowMono : Prop :=
  ∀ p ∈ elementaryWallVerts h', ∀ q ∈ elementaryWallVerts h', p.2 < q.2 →
    (R.vmap p).2 < (R.vmap q).2

/-- The lattice picture of a realization: the new vertex `p` at the point of its old vertex, and
the new edge `pq` on the kept cells that go to `pq`. -/
def pic : LatPic h' where
  vpt p := (((R.vmap p).1 : ℤ), ((R.vmap p).2 : ℤ))
  ecells p q := {m | m ∈ fig1WallCells h ∧ τ.own m = some (eCell p q)}

theorem pic_vc (p : ℕ × ℕ) : R.pic.vc p = vCell (R.vmap p) := rfl

theorem pic_pt (p : ℕ × ℕ) : R.pic.pt p = latticePoint (R.vmap p) := by
  simp [LatPic.pt, pic, latticePoint]

/-- The cells of the closed edge `pq` of the picture are the cells of the old path of `pq`: its
inner vertices and edges go to `pq`, and every kept cell that goes to `pq` is one of them, since
the paths of the other edges go to other edges. -/
theorem pic_closedCells (hh : 2 ≤ h) (he : Even h) {p q : ℕ × ℕ}
    (hpq : elementaryWallAdj h' p q) : R.pic.closedCells p q = pathCells (R.full p q) := by
  have hfull : R.full p q = R.vmap p :: (R.inner p q ++ [R.vmap q]) := rfl
  have hverts : ∀ u ∈ R.full p q, u ∈ elementaryWallVerts h :=
    mem_verts_of_isChain (R.chain p q hpq) (R.vmap_mem p hpq.1)
  have hsteps : ∀ uw ∈ (R.full p q).zip (R.full p q).tail,
      elementaryWallAdj h uw.1 uw.2 := fun uw huw =>
    List.rel_of_mem_zip_of_isChain (R.chain p q hpq) uw huw
  ext m
  simp only [LatPic.closedCells, pic, pathCells, mem_union, mem_ofPred_eq, mem_insert_iff,
    mem_singleton_iff]
  constructor
  · rintro (⟨hm, hown⟩ | rfl | rfl)
    · rcases R.own_cover m hm (by rw [hown]; exact Option.some_ne_none _) with
        ⟨r, hr, rfl⟩ | ⟨p', q', hpq', ⟨u, hu, rfl⟩ | ⟨uw, huw, rfl⟩⟩
      · rw [R.own_vmap r hr] at hown
        exact absurd (Option.some_injective _ hown).symm (eCell_ne_vCell hpq r)
      · rw [R.own_inner p' q' hpq' u hu] at hown
        have hs := sym2_eq_of_eCell_eq hpq' hpq (Option.some_injective _ hown)
        refine Or.inl ⟨u, ?_, rfl⟩
        rw [hfull]
        rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp [hu]
        · rw [R.inner_symm _ _ hpq] at hu
          simp [List.mem_reverse.mp hu]
      · rw [R.own_step p' q' hpq' uw huw] at hown
        have hs := sym2_eq_of_eCell_eq hpq' hpq (Option.some_injective _ hown)
        rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨uw, huw, rfl⟩
        · refine Or.inr ⟨(uw.2, uw.1), ?_, eCell_comm _ _⟩
          have h1 := List.mem_zip_tail_reverse (L := R.full p' q')
            (a := uw.1) (b := uw.2) (by exact huw)
          have hrev : (R.full p' q').reverse = R.full q' p' := by
            simp [full, R.inner_symm _ _ hpq']
          rwa [hrev] at h1
    · exact Or.inl ⟨R.vmap p, List.mem_cons_self, rfl⟩
    · exact Or.inl ⟨R.vmap q, by simp [full], rfl⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨uw, huw, rfl⟩)
    · rcases R.mem_full hu with rfl | rfl | hu'
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨mem_fig1WallCells_vCell hh he (hverts u hu), R.own_inner p q hpq u hu'⟩
    · exact Or.inl ⟨mem_fig1WallCells_eCell hh he (hsteps uw huw), R.own_step p q hpq uw huw⟩

/-- **The picture of a realization is good** when its rays leave the kept cells and the old
vertices keep the order of the rows. The kept cells play the part of `K` in `LatPic.good_of`. -/
theorem pic_good (hh : 2 ≤ h) (he : Even h) (hray : R.RayOK) (hmono : R.RowMono) :
    R.pic.Good := by
  refine LatPic.good_of (K := {m | m ∈ fig1WallCells h ∧ τ.own m ≠ none}) (fun p q hpq => ?_)
    (fun p q _ => ?_) (fun p q p' q' hpq hpq' hne => ?_) (fun p q hpq r hr => ?_)
    (fun p hp q hq e => ?_) (fun p q hpq => ?_) (fun p hp => ?_) (fun p hp hs m hm hmK => ?_)
    (fun p hp q hq hlt => ?_)
  · rw [pic_closedCells R hh he hpq, pic_pt, pic_pt]
    obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil (List.append_ne_nil_of_right_ne_nil
      (R.inner p q) (List.cons_ne_nil (R.vmap q) []))
    have hfull : R.full p q = R.vmap p :: b :: l := by rw [full, hbl]
    have hc := R.chain p q hpq
    have hn := R.nodup p q hpq
    rw [← full, hfull] at hc hn
    have hlast : (b :: l).getLast (List.cons_ne_nil _ _) = R.vmap q := by
      simp only [← hbl, List.getLast_append_singleton]
    have := pathCells_isLine l (R.vmap p) b hc hn
    rwa [hlast, ← hfull] at this
  · simp only [pic, eCell_comm]
  · refine disjoint_left.mpr fun m hm hm' => hne ?_
    exact sym2_eq_of_eCell_eq hpq hpq' (Option.some_injective _ (hm.2.symm.trans hm'.2))
  · rintro ⟨-, hown⟩
    rw [pic_vc, R.own_vmap r hr] at hown
    exact eCell_ne_vCell hpq r (Option.some_injective _ hown).symm
  · simp only [pic, Prod.mk.injEq, Nat.cast_inj] at e
    exact R.vmap_injOn hp hq (Prod.ext e.1 e.2)
  · rintro m ⟨hm, hown⟩
    exact ⟨hm, by rw [hown]; exact Option.some_ne_none _⟩
  · rw [pic_vc]
    exact ⟨mem_fig1WallCells_vCell hh he (R.vmap_mem p hp), by
      rw [R.own_vmap p hp]; exact Option.some_ne_none _⟩
  · exact hray p hp hs m hm hmK.1 hmK.2
  · simp only [pic]
    exact_mod_cast hmono p hp q hq hlt

/-- The kept cells that go to the vertex `p` of the new wall: only the cell of its old vertex. -/
theorem own_eq_vCell_iff (hh : 2 ≤ h) (he : Even h) {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h')
    (m : ℤ × ℤ) : (m ∈ fig1WallCells h ∧ τ.own m = some (vCell p)) ↔ m = vCell (R.vmap p) := by
  constructor
  · rintro ⟨hm, hown⟩
    rcases R.own_cover m hm (by rw [hown]; exact Option.some_ne_none _) with
      ⟨r, hr, rfl⟩ | ⟨p', q', hpq', ⟨u, hu, rfl⟩ | ⟨uw, huw, rfl⟩⟩
    · rw [R.own_vmap r hr] at hown
      rw [vCell_injective (Option.some_injective _ hown)]
    · rw [R.own_inner p' q' hpq' u hu] at hown
      exact absurd (Option.some_injective _ hown) (eCell_ne_vCell hpq' p)
    · rw [R.own_step p' q' hpq' uw huw] at hown
      exact absurd (Option.some_injective _ hown) (eCell_ne_vCell hpq' p)
  · rintro rfl
    exact ⟨mem_fig1WallCells_vCell hh he (R.vmap_mem p hp), R.own_vmap p hp⟩

/-- Taking the two end points out of the closed edge of a good picture leaves the open edge. -/
theorem _root_.GraphMinor.GM13.LatPic.Good.cellSet_closed_diff {h : ℕ} {P : LatPic h}
    (hP : P.Good) {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    cellSet (P.closedCells p q) \ {P.pt p, P.pt q} = cellSet (P.ecells p q) := by
  ext z
  simp only [LatPic.closedCells, cellSet, mem_sdiff, mem_ofPred_eq, mem_union, mem_insert_iff,
    mem_singleton_iff, ← P.cellCode_eq_vc_iff]
  have h1 := hP.novert p q hpq p hpq.1
  have h2 := hP.novert p q hpq q hpq.2.1
  constructor
  · tauto
  · intro hz
    refine ⟨Or.inl hz, ?_⟩
    rintro (e | e) <;> rw [e] at hz
    · exact h1 hz
    · exact h2 hz

/-- **A step is a homeomorphism of the plane.** If the rays leave the kept cells and the old
vertices keep the order of the rows, a homeomorphism of the plane maps each cell `m'` of the new
wall drawn as in Fig. 1 onto the kept old cells that go to `m'`. It is the homeomorphism of
`LatPic.Good.exists_homeo` between the wall of Fig. 1 and the picture of the realization. It maps
the point of a vertex `p` to the point of `R.vmap p`, and the closed segment of an edge `pq` onto
the closed edge of the picture, so also the open segment onto the open edge. -/
theorem exists_homeo (hh : 2 ≤ h) (he : Even h) (hh' : 2 ≤ h') (he' : Even h') (hray : R.RayOK)
    (hmono : R.RowMono) :
    ∃ ψ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ m' ∈ fig1WallCells h',
      ψ '' cellSet {m'} = cellSet {m | m ∈ fig1WallCells h ∧ τ.own m = some m'} := by
  have hS := stdPic_good hh' he'
  have hR := R.pic_good hh he hray hmono
  obtain ⟨ψ, hv, hE⟩ := hS.exists_homeo hR hh' he'
  refine ⟨ψ, fun m' hm' => ?_⟩
  simp only [fig1WallCells, mem_iUnion] at hm'
  obtain ⟨p, q, hpq, hm'⟩ := hm'
  rw [fig1SegmentCells_eq hpq] at hm'
  have hvert : ∀ r ∈ elementaryWallVerts h',
      ψ '' cellSet {vCell r} = cellSet {m | m ∈ fig1WallCells h ∧ τ.own m = some (vCell r)} := by
    intro r hr
    have : {m | m ∈ fig1WallCells h ∧ τ.own m = some (vCell r)} = {vCell (R.vmap r)} := by
      ext m
      exact R.own_eq_vCell_iff hh he hr m
    rw [this, cellSet_vCell, cellSet_vCell, image_singleton, ← stdPic_pt, hv r hr, pic_pt]
  rcases hm' with rfl | rfl | rfl
  · exact hvert p hpq.1
  · have h1 := hS.cellSet_closed_diff hpq
    have h2 := hR.cellSet_closed_diff hpq
    change ψ '' cellSet ((stdPic h').ecells p q) = _
    rw [← h1, image_sdiff ψ.injective, hE p q hpq, image_insert_eq, image_singleton,
      hv p hpq.1, hv q hpq.2.1, h2]
    rfl
  · exact hvert q hpq.2.1

end Shape.Realization

end GraphMinor.GM13
