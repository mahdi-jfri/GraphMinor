module

public import GraphMinor.GM13.Section7SphereRay
public import GraphMinor.GM13.Section7ApexWall
public import GraphMinor.GM16.FiniteLineGraphDrawing
public import GraphMinor.GM14.Whitney
public import GraphMinor.GM09.RuralAdd

/-!
# Graph Minors XIII, (7.3): two lattice pictures of a wall differ by a homeomorphism

A *lattice picture* of the elementary wall of height `h` (`LatPic h`) puts each vertex `p` at a
lattice point `vpt p` and each edge `pq` on a set of cells `ecells p q` (the edge without its
ends). Each vertex `p` on a side of the wall also gets a ray of cells, which starts at `p` and
goes straight down, up, left or right (`sideDir`), away from the wall. When the edges are lines
that meet only at common ends and the rays meet nothing else (`LatPic.Good`), the picture, with
the rays and the point at infinity, is a drawing in the sphere of the wall with a vertex at
infinity (`apexWall`, `LatPic.Good.exists_drawing`).

By `Section7ApexWall.lean` this graph is a subdivision of a simple 3-connected graph. So
Whitney's theorem (`GraphMinor.GM14.Whitney.whitney_fixing`) gives a homeomorphism of the sphere
between two good lattice pictures. It fixes `∞`, since `∞` is the new vertex in both, so it is a
homeomorphism of the plane, which maps each vertex and each edge of one picture to the same
vertex and edge of the other (`LatPic.Good.exists_homeo`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph
open scoped OnePoint
open GraphMinor.Surface

/-- The direction of the ray of a side vertex `p` of the elementary wall of height `h`: down on
the bottom row, up on the top row, and otherwise left on the left side and right on the right
side. -/
def sideDir (h : ℕ) (p : ℕ × ℕ) : ℤ × ℤ :=
  if p.2 = 0 then (0, -1) else if p.2 = h then (0, 1) else if p.1 = 0 then (-1, 0) else (1, 0)

theorem isAxisDir_sideDir (h : ℕ) (p : ℕ × ℕ) : IsAxisDir (sideDir h p) := by
  unfold sideDir IsAxisDir
  split_ifs <;> simp

theorem sideDir_ne_zero (h : ℕ) (p : ℕ × ℕ) :
    (((sideDir h p).1 : ℝ), ((sideDir h p).2 : ℝ)) ≠ 0 := by
  unfold sideDir
  split_ifs <;> simp

/-- **A lattice picture** of the elementary wall of height `h`: a lattice point for each vertex
and a set of cells for each edge, without its ends. -/
structure LatPic (h : ℕ) where
  /-- The lattice point of each vertex. -/
  vpt : ℕ × ℕ → ℤ × ℤ
  /-- The cells of each edge, without its ends. -/
  ecells : ℕ × ℕ → ℕ × ℕ → Set (ℤ × ℤ)

namespace LatPic

variable {h : ℕ} (P : LatPic h)

/-- The cell of a vertex. -/
def vc (p : ℕ × ℕ) : ℤ × ℤ := (2 * (P.vpt p).1, 2 * (P.vpt p).2)

/-- The point of a vertex. -/
def pt (p : ℕ × ℕ) : ℝ × ℝ := (((P.vpt p).1 : ℝ), ((P.vpt p).2 : ℝ))

/-- The cells of an edge with its ends. -/
def closedCells (p q : ℕ × ℕ) : Set (ℤ × ℤ) := P.ecells p q ∪ {P.vc p, P.vc q}

/-- The cells of the ray of a side vertex, its start included. -/
def ray (p : ℕ × ℕ) : Set (ℤ × ℤ) := rayCells (P.vc p) (sideDir h p)

/-- **A good lattice picture**: the edges are lines between the points of their ends, they meet
only at common ends, no vertex lies inside an edge, distinct vertices have distinct points, and
the ray of a side vertex meets no edge, no other vertex and no other ray. -/
structure Good : Prop where
  line : ∀ p q, elementaryWallAdj h p q →
    IsLineWithEnds (cellSet (P.closedCells p q)) (P.pt p) (P.pt q)
  symm : ∀ p q, elementaryWallAdj h p q → P.ecells q p = P.ecells p q
  disj : ∀ p q p' q', elementaryWallAdj h p q → elementaryWallAdj h p' q' → s(p, q) ≠ s(p', q') →
    Disjoint (P.ecells p q) (P.ecells p' q')
  novert : ∀ p q, elementaryWallAdj h p q → ∀ r ∈ elementaryWallVerts h, P.vc r ∉ P.ecells p q
  inj : InjOn P.vpt (elementaryWallVerts h)
  ray_edge : ∀ p ∈ elementaryWallVerts h, IsSideVert h p → ∀ q r, elementaryWallAdj h q r →
    Disjoint (P.ray p) (P.ecells q r)
  ray_vert : ∀ p ∈ elementaryWallVerts h, IsSideVert h p → ∀ q ∈ elementaryWallVerts h,
    P.vc q ∈ P.ray p → q = p
  ray_ray : ∀ p ∈ elementaryWallVerts h, IsSideVert h p → ∀ q ∈ elementaryWallVerts h,
    IsSideVert h q → p ≠ q → Disjoint (P.ray p) (P.ray q)

theorem cellCode_eq_vc_iff {z : ℝ × ℝ} {p : ℕ × ℕ} : cellCode z = P.vc p ↔ z = P.pt p := by
  obtain ⟨z1, z2⟩ := z
  simp only [cellCode, vc, pt, Prod.mk.injEq, cellCode1_eq_even_iff]

/-- The point of a vertex `p` of the elementary wall in the sphere, and `∞` for the new
vertex. -/
noncomputable def sv : Option (ℕ × ℕ) → OnePoint EuclideanPlane
  | none => ∞
  | some p => sphPt (P.pt p)

/-- The cells of the edge `ab` of `apexWall h`: those of the edge of the wall, or those of the
ray. -/
def kc : Option (ℕ × ℕ) → Option (ℕ × ℕ) → Set (ℤ × ℤ)
  | some p, some q => P.ecells p q ∪ P.ecells q p ∪ {P.vc p, P.vc q}
  | none, some q => P.ray q
  | some p, none => P.ray p
  | none, none => ∅

/-- The closed edge `ab` of `apexWall h` in the sphere: a ray also contains `∞`. -/
noncomputable def lab (a b : Option (ℕ × ℕ)) : Set (OnePoint EuclideanPlane) :=
  sphPt '' cellSet (P.kc a b) ∪ (if a = none ∨ b = none then {∞} else ∅)

theorem kc_comm (a b : Option (ℕ × ℕ)) : P.kc a b = P.kc b a := by
  cases a <;> cases b <;> simp only [kc]
  rw [union_comm (P.ecells _ _), pair_comm]

theorem lab_comm (a b : Option (ℕ × ℕ)) : P.lab a b = P.lab b a := by
  simp only [lab, kc_comm P a b, or_comm]

/-- The closed edge of `apexWall h` in the sphere, as a function of the edge. -/
noncomputable def edgePts (e : Sym2 (Option (ℕ × ℕ))) : Set (OnePoint EuclideanPlane) :=
  Sym2.lift ⟨P.lab, P.lab_comm⟩ e

theorem edgePts_mk (a b : Option (ℕ × ℕ)) : P.edgePts s(a, b) = P.lab a b := Sym2.lift_mk _ _ _

theorem lab_some_some (p q : ℕ × ℕ) :
    P.lab (some p) (some q) =
      sphPt '' cellSet (P.ecells p q ∪ P.ecells q p ∪ {P.vc p, P.vc q}) := by
  simp [lab, kc]

theorem lab_none_some (q : ℕ × ℕ) : P.lab none (some q) = sphPt '' cellSet (P.ray q) ∪ {∞} := by
  simp [lab, kc]

/-- Every edge of `apexWall h` is an edge of the wall or joins `none` to a side vertex. -/
theorem edge_cases {e : Sym2 (Option (ℕ × ℕ))} (he : e ∈ E(apexWall h)) :
    (∃ p q, elementaryWallAdj h p q ∧ e = s(some p, some q)) ∨
      ∃ r ∈ elementaryWallVerts h, IsSideVert h r ∧ e = s(none, some r) := by
  obtain ⟨a, b, hab, rfl⟩ := he
  cases a with
  | none =>
    cases b with
    | none => exact absurd hab (by simp [apexAdj])
    | some r => exact Or.inr ⟨r, hab.1, hab.2, rfl⟩
  | some p =>
    cases b with
    | none => exact Or.inr ⟨p, hab.1, hab.2, Sym2.eq_swap⟩
    | some q => exact Or.inl ⟨p, q, hab, rfl⟩

variable {P}

theorem vc_inj (hP : P.Good) {p q : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h)
    (hq : q ∈ elementaryWallVerts h) (e : P.vc p = P.vc q) : p = q := by
  apply hP.inj hp hq
  simp only [vc, Prod.mk.injEq] at e
  ext <;> omega

/-- The edge cells of an edge of the wall, read in both directions. -/
theorem Good.kc_some (hP : P.Good) {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    P.kc (some p) (some q) = P.closedCells p q := by
  simp only [kc, closedCells, hP.symm p q hpq, union_self]

theorem Good.lab_some (hP : P.Good) {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    P.lab (some p) (some q) = sphPt '' cellSet (P.closedCells p q) := by
  rw [← hP.kc_some hpq]
  simp [lab]

/-- A point of a closed edge is `∞` or the point of one of its cells. -/
theorem mem_lab {a b : Option (ℕ × ℕ)} {z : OnePoint EuclideanPlane} (hz : z ∈ P.lab a b) :
    z = ∞ ∨ ∃ w, z = sphPt w ∧ cellCode w ∈ P.kc a b := by
  rcases hz with ⟨w, hw, rfl⟩ | hz
  · exact Or.inr ⟨w, rfl, hw⟩
  · split_ifs at hz
    · exact Or.inl hz
    · exact absurd hz (notMem_empty _)

/-- Two distinct edges of `apexWall h` share only cells of vertices. -/
theorem Good.kc_inter (hP : P.Good) {e d : Sym2 (Option (ℕ × ℕ))} (he : e ∈ E(apexWall h))
    (hd : d ∈ E(apexWall h)) (hne : e ≠ d) {m : ℤ × ℤ}
    (hme : m ∈ Sym2.lift ⟨P.kc, P.kc_comm⟩ e) (hmd : m ∈ Sym2.lift ⟨P.kc, P.kc_comm⟩ d) :
    ∃ r ∈ elementaryWallVerts h, m = P.vc r := by
  rcases edge_cases he with ⟨p, q, hpq, rfl⟩ | ⟨r, hr, hrs, rfl⟩ <;>
    rcases edge_cases hd with ⟨p', q', hpq', rfl⟩ | ⟨r', hr', hrs', rfl⟩ <;>
    simp only [Sym2.lift_mk, kc] at hme hmd
  · rw [hP.symm p q hpq, union_self] at hme
    rw [hP.symm p' q' hpq', union_self] at hmd
    rcases hme with hme | rfl | rfl
    · exfalso
      have hne' : s(p, q) ≠ s(p', q') := fun h' => hne (by
        rcases Sym2.eq_iff.mp h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap)
      rcases hmd with hmd | rfl | rfl
      · exact disjoint_left.mp (hP.disj p q p' q' hpq hpq' hne') hme hmd
      · exact hP.novert p q hpq p' hpq'.1 hme
      · exact hP.novert p q hpq q' hpq'.2.1 hme
    · exact ⟨p, hpq.1, rfl⟩
    · exact ⟨q, hpq.2.1, rfl⟩
  · rw [hP.symm p q hpq, union_self] at hme
    rcases hme with hme | rfl | rfl
    · exact absurd hme (disjoint_left.mp (hP.ray_edge r' hr' hrs' p q hpq) hmd)
    · exact ⟨p, hpq.1, rfl⟩
    · exact ⟨q, hpq.2.1, rfl⟩
  · rw [hP.symm p' q' hpq', union_self] at hmd
    rcases hmd with hmd | rfl | rfl
    · exact absurd hmd (disjoint_left.mp (hP.ray_edge r hr hrs p' q' hpq') hme)
    · exact ⟨p', hpq'.1, rfl⟩
    · exact ⟨q', hpq'.2.1, rfl⟩
  · have hrr : r ≠ r' := fun e => hne (by rw [e])
    exact absurd hmd (disjoint_left.mp (hP.ray_ray r hr hrs r' hr' hrs' hrr) hme)

/-- The ray of a side vertex, with `∞`, is a line from the vertex to `∞`. -/
theorem ray_line (p : ℕ × ℕ) :
    IsLineWithEnds (sphPt '' cellSet (P.ray p) ∪ {∞}) (sphPt (P.pt p)) ∞ := by
  rw [ray, vc, cellSet_rayCells (isAxisDir_sideDir h p)]
  exact isLine_sphRay _ _ (sideDir_ne_zero h p)

theorem sv_injOn (hP : P.Good) : InjOn P.sv V(apexWall h) := by
  rintro (_ | p) hp (_ | q) hq e
  · rfl
  · exact absurd e.symm (sphPt_ne_infty _)
  · exact absurd e (sphPt_ne_infty _)
  · obtain ⟨p', hp', e1⟩ := (mem_insert_iff.mp hp).resolve_left (by simp)
    obtain ⟨q', hq', e2⟩ := (mem_insert_iff.mp hq).resolve_left (by simp)
    cases e1
    cases e2
    have e' := sphPt_injective e
    simp only [pt, Prod.mk.injEq, Int.cast_inj] at e'
    rw [hP.inj hp' hq' (Prod.ext e'.1 e'.2)]

/-- **A good lattice picture is a drawing of the wall with a vertex at infinity** in the
sphere: the new vertex is drawn at `∞`, each vertex at its point, each edge on its cells and each
new edge on a ray. We use `exists_graphDrawing_of_finite_lines`: the closed edges are lines with
the right ends (`Good.line`, `ray_line`), a vertex on a closed edge is an end of it, and two
closed edges meet only at vertices (`Good.kc_inter`). -/
theorem Good.exists_drawing (hP : P.Good) (hh : 2 ≤ h) (he : Even h) :
    ∃ D : GraphDrawing (apexWall h) (OnePoint EuclideanPlane),
      (∀ v : V(apexWall h), (D.iso.vertexEquiv v).1 = P.sv v.1) ∧
      ∀ e : E(apexWall h), closure (D.iso.edgeEquiv e).1 = P.edgePts e.1 := by
  have hG := apexWall_connGood hh he
  -- a point of a cell of a vertex is the point of that vertex
  have hvpt : ∀ {w : ℝ × ℝ} {r : ℕ × ℕ}, r ∈ elementaryWallVerts h → cellCode w = P.vc r →
      sphPt w ∈ P.sv '' V(apexWall h) := fun {w r} hr hw => by
    rw [(P.cellCode_eq_vc_iff).mp hw]
    exact ⟨some r, Or.inr ⟨r, hr, rfl⟩, rfl⟩
  -- the closed edges are lines with the right ends
  have hLine : ∀ e ∈ E(apexWall h), ∀ a b, (apexWall h).IsLink e a b →
      IsLineWithEnds (P.edgePts e) (P.sv a) (P.sv b) := by
    rintro e - a b ⟨hab, rfl⟩
    rw [edgePts_mk]
    cases a with
    | none =>
      cases b with
      | none => exact absurd hab (by simp [apexAdj])
      | some q => rw [lab_none_some]; exact (ray_line q).symm
    | some p =>
      cases b with
      | none => rw [lab_comm, lab_none_some]; exact ray_line p
      | some q =>
        rw [hP.lab_some hab]
        exact GraphMinor.GM16.isLineWithEnds_image_embedding isOpenEmbedding_sphPt.isEmbedding
          (hP.line p q hab)
  -- a vertex on a closed edge is an end of it
  have hVert : ∀ e ∈ E(apexWall h), ∀ v ∈ V(apexWall h), P.sv v ∈ P.edgePts e →
      (apexWall h).Inc e v := by
    intro e he v hv hz
    rcases edge_cases he with ⟨p, q, hpq, rfl⟩ | ⟨r, hr, hrs, rfl⟩
    · rw [edgePts_mk] at hz
      cases v with
      | none =>
        exfalso
        rcases hz with ⟨w, -, hw⟩ | hz
        · exact sphPt_ne_infty w hw
        · simp at hz
      | some t =>
        obtain ⟨t', ht', e1⟩ := (mem_insert_iff.mp hv).resolve_left (by simp)
        cases e1
        rcases hz with ⟨w, hw, e2⟩ | hz
        · have e3 := sphPt_injective e2
          change cellCode w ∈ P.kc (some p) (some q) at hw
          rw [hP.kc_some hpq, e3, (P.cellCode_eq_vc_iff).mpr rfl] at hw
          rcases hw with hw | hw | hw
          · exact absurd hw (hP.novert p q hpq t ht')
          · rw [vc_inj hP ht' hpq.1 hw]
            exact ⟨some q, hpq, rfl⟩
          · rw [vc_inj hP ht' hpq.2.1 hw]
            exact ⟨some p, elementaryWallAdj_symm hpq, Sym2.eq_swap⟩
        · simp at hz
    · rw [edgePts_mk] at hz
      cases v with
      | none => exact ⟨some r, ⟨hr, hrs⟩, rfl⟩
      | some t =>
        obtain ⟨t', ht', e1⟩ := (mem_insert_iff.mp hv).resolve_left (by simp)
        cases e1
        rw [lab_none_some] at hz
        rcases hz with ⟨w, hw, e2⟩ | hz
        · have e3 := sphPt_injective e2
          change cellCode w ∈ P.ray r at hw
          rw [e3, (P.cellCode_eq_vc_iff).mpr rfl] at hw
          rw [hP.ray_vert r hr hrs t ht' hw]
          exact ⟨none, ⟨hr, hrs⟩, Sym2.eq_swap⟩
        · exact absurd (mem_singleton_iff.mp hz) (sphPt_ne_infty _)
  -- two closed edges meet only at vertices
  have hMeet : ∀ e ∈ E(apexWall h), ∀ d ∈ E(apexWall h), e ≠ d →
      P.edgePts e ∩ P.edgePts d ⊆ P.sv '' V(apexWall h) := by
    intro e he d hd hne z ⟨hze, hzd⟩
    have hlift : ∀ c : Sym2 (Option (ℕ × ℕ)), P.edgePts c =
        sphPt '' cellSet (Sym2.lift ⟨P.kc, P.kc_comm⟩ c) ∪
          (if (none : Option (ℕ × ℕ)) ∈ c then {∞} else ∅) := by
      intro c
      induction c using Sym2.ind with
      | h a b =>
        rw [edgePts_mk, Sym2.lift_mk, lab]
        congr 1
        simp only [Sym2.mem_iff, eq_comm]
    rw [hlift] at hze hzd
    rcases hze with ⟨w, hw, rfl⟩ | hze
    · rcases hzd with ⟨w', hw', e'⟩ | hzd
      · cases sphPt_injective e'
        obtain ⟨r, hr, hm⟩ := hP.kc_inter he hd hne hw hw'
        exact hvpt hr hm
      · split_ifs at hzd
        · exact absurd (mem_singleton_iff.mp hzd) (sphPt_ne_infty _)
        · exact absurd hzd (notMem_empty _)
    · split_ifs at hze
      · rw [mem_singleton_iff.mp hze]
        exact ⟨none, mem_insert _ _, rfl⟩
      · exact absurd hze (notMem_empty _)
  obtain ⟨D, -, hv, he⟩ := GraphMinor.GM16.exists_graphDrawing_of_finite_lines (apexWall h)
    hG.finV hG.finE P.sv (sv_injOn hP) P.edgePts (fun e v hl => hG.no_loop e v hl) hLine hVert
    hMeet
  exact ⟨D, hv, he⟩

/-- **A lattice picture is good when its rays leave the wall.** Let `K` be a set of cells that
contains the cells of all vertices and edges. If the ray of each side vertex meets `K` only at its
start, and the rows of the vertices keep their order, then the rays meet no edge, no other vertex
and no other ray. For two rays that go the same way along one line, the start of one lies on the
other. Two rays that go left (or right) start on different rows, by the order of the rows. A ray
that goes left and one that goes right on the same row would meet only if the start of one lies on
the other. A ray that goes down starts below every ray that goes left, right or up, and a ray that
goes up starts above every ray that goes left or right. -/
theorem good_of (line : ∀ p q, elementaryWallAdj h p q →
      IsLineWithEnds (cellSet (P.closedCells p q)) (P.pt p) (P.pt q))
    (symm : ∀ p q, elementaryWallAdj h p q → P.ecells q p = P.ecells p q)
    (disj : ∀ p q p' q', elementaryWallAdj h p q → elementaryWallAdj h p' q' →
      s(p, q) ≠ s(p', q') → Disjoint (P.ecells p q) (P.ecells p' q'))
    (novert : ∀ p q, elementaryWallAdj h p q → ∀ r ∈ elementaryWallVerts h, P.vc r ∉ P.ecells p q)
    (inj : InjOn P.vpt (elementaryWallVerts h)) {K : Set (ℤ × ℤ)}
    (hKe : ∀ p q, elementaryWallAdj h p q → P.ecells p q ⊆ K)
    (hKv : ∀ p ∈ elementaryWallVerts h, P.vc p ∈ K)
    (hray : ∀ p ∈ elementaryWallVerts h, IsSideVert h p → ∀ m ∈ P.ray p, m ∈ K → m = P.vc p)
    (hmono : ∀ p ∈ elementaryWallVerts h, ∀ q ∈ elementaryWallVerts h, p.2 < q.2 →
      (P.vpt p).2 < (P.vpt q).2) : P.Good := by
  have hvc : ∀ {p q}, p ∈ elementaryWallVerts h → q ∈ elementaryWallVerts h → P.vc p = P.vc q →
      p = q := fun {p q} hp hq e => by
    apply inj hp hq
    simp only [vc, Prod.mk.injEq] at e
    ext <;> omega
  have hstart : ∀ p ∈ elementaryWallVerts h, IsSideVert h p → ∀ q ∈ elementaryWallVerts h,
      P.vc q ∈ P.ray p → q = p := fun p hp hs q hq hm => hvc hq hp (hray p hp hs _ hm (hKv q hq))
  refine ⟨line, symm, disj, novert, inj,
    fun p hp hs q r hqr => disjoint_left.mpr fun m hm hm' => ?_,
    hstart, fun p hp hs q hq hs' hne => disjoint_left.mpr fun m hm hm' => ?_⟩
  · rw [hray p hp hs m hm (hKe q r hqr hm')] at hm'
    exact novert q r hqr p hp hm'
  · have hpq : P.vc p ∉ P.ray q := fun h' => hne (hstart q hq hs' p hp h')
    have hqp : P.vc q ∉ P.ray p := fun h' => hne.symm (hstart p hp hs q hq h')
    have h1 := hmono p hp q hq
    have h2 := hmono q hq p hp
    have hne' : ¬ (p.1 = q.1 ∧ p.2 = q.2) := fun h' => hne (Prod.ext h'.1 h'.2)
    obtain ⟨-, hph, -, -⟩ := hp
    obtain ⟨-, hqh, -, -⟩ := hq
    unfold ray vc at hm hm' hpq hqp
    rw [mem_rayCells_iff (isAxisDir_sideDir h p)] at hm hqp
    rw [mem_rayCells_iff (isAxisDir_sideDir h q)] at hm' hpq
    unfold IsSideVert at hs hs'
    unfold sideDir at hm hm' hpq hqp
    split_ifs at hm hm' hpq hqp <;> simp only [Int.reduceNeg, true_implies, zero_ne_one,
      false_implies, one_ne_zero, reduceCtorEq, and_true, true_and, neg_eq_zero,
      not_and, not_le] at hm hm' hpq hqp <;> omega

/-- A homeomorphism of the sphere that fixes `∞` is a homeomorphism of the plane: it maps the
points other than `∞`, which are the points `sphPt z`, onto themselves. -/
theorem exists_planeHomeo_of_infty (g : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane)
    (hg : g ∞ = ∞) : ∃ ψ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ z, sphPt (ψ z) = g (sphPt z) := by
  have hr : ∀ x, x ∈ range sphPt ↔ x ≠ ∞ := by
    intro x
    rw [OnePoint.ne_infty_iff_exists]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨fig1PlaneEquiv.symm y, by simp [sphPt]⟩
  have hiff : ∀ x, x ∈ range sphPt ↔ g x ∈ range sphPt := by
    intro x
    rw [hr, hr]
    refine not_congr ⟨fun e => by rw [e, hg], fun e => g.injective (e.trans hg.symm)⟩
  let e0 := isOpenEmbedding_sphPt.isEmbedding.toHomeomorph
  refine ⟨e0.trans ((g.subtype hiff).trans e0.symm), fun z => ?_⟩
  have key : ∀ y : range sphPt, sphPt (e0.symm y) = y.1 := fun y => by
    conv_rhs => rw [← e0.apply_symm_apply y]
    rfl
  exact key _

variable {P₁ P₂ : LatPic h}

/-- **Two good lattice pictures differ by a homeomorphism of the plane**, which maps each vertex
and each edge of the first to the same vertex and edge of the second. Both are drawings of
`apexWall h` in the sphere (`Good.exists_drawing`), and `apexWall h` is a subdivision of a simple
3-connected graph (`isSubdivision_of_iso_apexWall`), so Whitney's theorem gives a homeomorphism of
the sphere between them. It fixes `∞`, the point of the new vertex in both pictures, so it is a
homeomorphism of the plane (`exists_planeHomeo_of_infty`). -/
theorem Good.exists_homeo (h₁ : P₁.Good) (h₂ : P₂.Good) (hh : 2 ≤ h) (he : Even h) :
    ∃ ψ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), (∀ p ∈ elementaryWallVerts h, ψ (P₁.pt p) = P₂.pt p) ∧
      ∀ p q, elementaryWallAdj h p q →
        ψ '' cellSet (P₁.closedCells p q) = cellSet (P₂.closedCells p q) := by
  obtain ⟨D₁, hv₁, he₁⟩ := h₁.exists_drawing hh he
  obtain ⟨D₂, hv₂, he₂⟩ := h₂.exists_drawing hh he
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hSurf : IsSurface (OnePoint EuclideanPlane) :=
    GraphMinor.Surface.IsClosedSurface.isSurface GraphMinor.GM09.isClosedSurface_sphere
  have hsub := isSubdivision_of_iso_apexWall hh he D₁.iso
  let φ : GraphMinor.Iso D₁.drawing.toGraph D₂.drawing.toGraph :=
    { vertexEquiv := D₁.iso.vertexEquiv.symm.trans D₂.iso.vertexEquiv
      edgeEquiv := D₁.iso.edgeEquiv.symm.trans D₂.iso.edgeEquiv
      isLink_iff := fun e x y => by
        have h1 := D₁.iso.isLink_iff (D₁.iso.edgeEquiv.symm e) (D₁.iso.vertexEquiv.symm x)
          (D₁.iso.vertexEquiv.symm y)
        have h2 := D₂.iso.isLink_iff (D₁.iso.edgeEquiv.symm e) (D₁.iso.vertexEquiv.symm x)
          (D₁.iso.vertexEquiv.symm y)
        simp only [Equiv.apply_symm_apply] at h1
        exact h1.symm.trans h2 }
  obtain ⟨g, hgv, hge, -⟩ := GraphMinor.GM14.Whitney.whitney_fixing hSurf hsph D₁.drawing
    D₂.drawing hsub φ ∅ (fun _ h' => absurd h' (notMem_empty _))
  have hgs : ∀ v : V(apexWall h), g (P₁.sv v.1) = P₂.sv v.1 := by
    intro v
    have := hgv (D₁.iso.vertexEquiv v)
    rw [hv₁] at this
    rw [this]
    simp only [φ, Equiv.trans_apply, Equiv.symm_apply_apply]
    exact hv₂ v
  have hgE : ∀ e : E(apexWall h), g '' P₁.edgePts e.1 = P₂.edgePts e.1 := by
    intro e
    rw [← he₁, ← he₂, g.image_closure, hge (D₁.iso.edgeEquiv e)]
    simp only [φ, Equiv.trans_apply, Equiv.symm_apply_apply]
  obtain ⟨ψ, hψ⟩ := exists_planeHomeo_of_infty g (hgs ⟨none, mem_insert _ _⟩)
  refine ⟨ψ, fun p hp => ?_, fun p q hpq => ?_⟩
  · apply sphPt_injective
    rw [hψ]
    exact hgs ⟨some p, Or.inr ⟨p, hp, rfl⟩⟩
  · have := hgE ⟨s(some p, some q), p, q, hpq, rfl⟩
    simp only [edgePts_mk, h₁.lab_some hpq, h₂.lab_some hpq] at this
    apply sphPt_injective.image_injective
    rw [← this, image_image, image_image]
    simp only [hψ]

end LatPic

end GraphMinor.GM13
