module

public import GraphMinor.HP25.Web
public import GraphMinor.Surface.CrossCut
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.PlaneSeparation
import GraphMinor.Surface.DiscGrow

/-!
# Faces of a plane embedding

Basic facts on the plane embeddings of `HP25/Web.lean`, used by all results of Sections 2 and 3 of
Humeau and Pous that look at a drawing.

* The drawn set `φ.U` is compact (`PlaneEmbedding.isCompact_U`), so it misses a neighbourhood of
  infinity, and some face is unbounded (`PlaneEmbedding.exists_unbounded_face`).
* A face is open and connected (`PlaneEmbedding.isOpen_of_mem_faces`).
* A face whose frontier is an `O`-arc `F` drawn inside `φ.U` is the inner or the outer domain of `F`
  (`PlaneEmbedding.eq_inner_of_frontier`, `PlaneEmbedding.eq_outer_of_frontier`). The reason is that
  a face is open, and it is closed in the complement of `F` because its frontier is `F`. So it is a
  whole component of the complement of `F`, and the Jordan curve theorem names the two components.
* The line of a triangle is an `O`-arc (`PlaneEmbedding.isOArc_cycleImage_three`).
-/

@[expose] public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- The pairs of cyclically consecutive entries of `x :: t` are the pairs of consecutive entries of
`x :: t ++ [x]`. -/
theorem zip_rotate_one_cons (x : V) (t : List V) :
    (x :: t).zip ((x :: t).rotate 1) = (x :: t ++ [x]).zip (x :: t ++ [x]).tail := by
  have h1 : (x :: t).rotate 1 = t ++ [x] := by simp
  have h2 := List.zip_append (l₁ := x :: t) (r₁ := [x]) (l₂ := t ++ [x]) (r₂ := []) (by simp)
  rw [h1]
  simp only [List.append_nil, List.zip_nil_right, List.cons_append, List.tail_cons] at h2 ⊢
  exact h2.symm

/-- A pair of consecutive entries of a list. -/
theorem mem_zip_tail_iff {l : List V} {a b : V} :
    (a, b) ∈ l.zip l.tail ↔ ∃ i, ∃ (hi : i + 1 < l.length), l[i] = a ∧ l[i + 1] = b := by
  constructor
  · intro hab
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hab
    simp only [List.getElem_zip, Prod.mk.injEq] at he
    have hi' : i + 1 < l.length := by
      rw [List.length_zip, List.length_tail] at hi
      omega
    refine ⟨i, hi', he.1, ?_⟩
    rw [← he.2, List.getElem_tail]
  · rintro ⟨i, hi, rfl, rfl⟩
    have hi' : i < (l.zip l.tail).length := by
      rw [List.length_zip, List.length_tail]
      omega
    have := List.getElem_mem hi'
    simpa [List.getElem_zip, List.getElem_tail] using this

/-- A list is a chain of a relation when all pairs of consecutive entries are related. -/
theorem isChain_iff_zip {r : V → V → Prop} {l : List V} :
    l.IsChain r ↔ ∀ p ∈ l.zip l.tail, r p.1 p.2 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil => simp
    | cons y l =>
      rw [List.isChain_cons_cons, ih]
      simp [List.zip_cons_cons]


/-- The pairs of cyclically consecutive entries of a rotated list are those of the list. -/
theorem zip_rotate_rotate (C : List V) (k : ℕ) :
    (C.rotate k).zip ((C.rotate k).rotate 1) = (C.zip (C.rotate 1)).rotate k := by
  simp only [List.zip_eq_zipWith]
  rw [List.zipWith_rotate_distrib _ _ _ _ (by simp), List.rotate_rotate,
    List.rotate_rotate, add_comm]

/-- A rotation of a cycle is a cycle. -/
theorem IsCycleList.rotate {C : List V} (hC : IsCycleList G C) (k : ℕ) :
    IsCycleList G (C.rotate k) := by
  refine ⟨by rw [List.length_rotate]; exact hC.1, List.nodup_rotate.mpr hC.2.1, fun p hp => ?_⟩
  rw [zip_rotate_rotate, List.mem_rotate] at hp
  exact hC.2.2 p hp

/-- A list of vertices is a path of `G` on `R`: distinct vertices of `R`, consecutive ones
adjacent. -/
def IsPathList (G : SimpleGraph V) (R : Set V) (l : List V) : Prop :=
  l.Nodup ∧ l.IsChain G.Adj ∧ ∀ x ∈ l, x ∈ R

theorem IsPathList.tail {x : V} {l : List V} (h : IsPathList G R (x :: l)) : IsPathList G R l :=
  ⟨(List.nodup_cons.mp h.1).2, h.2.1.tail, fun y hy => h.2.2 y (List.mem_cons_of_mem _ hy)⟩


/-- In a list without repetitions and with at least three entries, the first and the last entries
are not consecutive. -/
theorem not_ends_consecutive {l : List V} (hnd : l.Nodup) (h3 : 3 ≤ l.length) {i : ℕ}
    (hi : i + 1 < l.length) :
    s(l[0], l[l.length - 1]) ≠ s(l[i], l[i + 1]) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := (List.Nodup.getElem_inj_iff hnd).mp h1
    have := (List.Nodup.getElem_inj_iff hnd).mp h2
    omega
  · have := (List.Nodup.getElem_inj_iff hnd).mp h1
    have := (List.Nodup.getElem_inj_iff hnd).mp h2
    omega

/-- A cycle of `G` on `R` is a path list. -/
theorem IsCycleList.isPathList {C : List V} (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R) :
    IsPathList G R C := by
  refine ⟨hC.2.1, ?_, hR⟩
  obtain ⟨x, t, rfl⟩ : ∃ x t, C = x :: t := by
    cases C with
    | nil => simp [IsCycleList] at hC
    | cons x t => exact ⟨x, t, rfl⟩
  have h := hC.2.2
  rw [zip_rotate_one_cons] at h
  have h2 : (x :: t ++ [x]).IsChain G.Adj := isChain_iff_zip.mpr h
  exact h2.left_of_append


namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

theorem pt_mem_U {u : V} (hu : u ∈ R) : φ.pt u ∈ φ.U :=
  Or.inl (mem_image_of_mem _ hu)

theorem line_subset_U {u v : V} (hu : u ∈ R) (hv : v ∈ R) (h : G.Adj u v) : φ.line u v ⊆ φ.U :=
  fun _ hz => Or.inr (mem_iUnion₂.mpr ⟨u, hu, mem_iUnion₂.mpr ⟨v, hv, mem_iUnion.mpr ⟨h, hz⟩⟩⟩)

/-- The drawn set is compact: finitely many points and finitely many lines. -/
theorem isCompact_U : IsCompact φ.U := by
  refine (φ.finite.image _).isCompact.union ?_
  refine φ.finite.isCompact_biUnion fun u hu => φ.finite.isCompact_biUnion fun v hv => ?_
  by_cases h : G.Adj u v
  · simp only [h, iUnion_true]
    exact (φ.isLine u hu v hv h).isCompact
  · simp [h]

theorem isClosed_U : IsClosed φ.U :=
  φ.isCompact_U.isClosed

/-- A face is an open connected set that misses the drawn set. -/
theorem isOpen_of_mem_faces {r : Set ℂ} (hr : r ∈ φ.faces) :
    IsOpen r ∧ IsConnected r ∧ r ⊆ φ.Uᶜ := by
  obtain ⟨z, hz, rfl⟩ := hr
  rw [← compl_eq_univ_sdiff] at hz ⊢
  exact ⟨φ.isClosed_U.isOpen_compl.connectedComponentIn, isConnected_connectedComponentIn_iff.mpr hz,
    connectedComponentIn_subset _ _⟩

/-- A connected set that misses the drawn set and meets a face lies in it. -/
theorem subset_face {r A : Set ℂ} (hr : r ∈ φ.faces) (hA : IsPreconnected A) (hAU : A ⊆ φ.Uᶜ)
    {z : ℂ} (hzA : z ∈ A) (hzr : z ∈ r) : A ⊆ r := by
  obtain ⟨w, hw, rfl⟩ := hr
  rw [connectedComponentIn_eq hzr, ← compl_eq_univ_sdiff]
  exact hA.subset_connectedComponentIn hzA hAU

/-- Some face is unbounded: the drawn set is bounded, and the complement of a closed ball is
connected. -/
theorem exists_unbounded_face : ∃ r ∈ φ.faces, ¬ Bornology.IsBounded r := by
  obtain ⟨M, hM0, hM⟩ := φ.isCompact_U.isBounded.subset_closedBall_lt 0 0
  have hconn : IsConnected (Metric.closedBall (0 : ℂ) M)ᶜ := by
    refine ⟨?_, isPreconnected_compl_closedBall M hM0.le⟩
    refine ⟨((M + 1 : ℝ) : ℂ), ?_⟩
    have h1 : ‖(((M + 1 : ℝ)) : ℂ)‖ = M + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, h1, not_le]
    linarith
  obtain ⟨z, hz⟩ := hconn.nonempty
  have hzU : z ∉ φ.U := fun h => hz (hM h)
  refine ⟨connectedComponentIn (univ \ φ.U) z, mem_image_of_mem _ ⟨mem_univ _, hzU⟩, ?_⟩
  intro hb
  have hsub : (Metric.closedBall (0 : ℂ) M)ᶜ ⊆ connectedComponentIn (univ \ φ.U) z :=
    hconn.isPreconnected.subset_connectedComponentIn hz fun w hw => ⟨mem_univ _, fun h => hw (hM h)⟩
  refine NormedSpace.unbounded_univ ℝ ℂ ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M)).union
    (hb.subset hsub) |>.subset fun w _ => ?_)
  by_cases hw : w ∈ Metric.closedBall (0 : ℂ) M
  · exact Or.inl hw
  · exact Or.inr hw

/-- A face whose frontier is a closed set `F` drawn inside the drawn set is the component of the
complement of `F` that contains any of its points. The face is open, and it is closed in the
complement of `F`, since its closure adds only its frontier `F`. -/
theorem eq_connectedComponentIn_of_frontier {r F : Set ℂ} (hr : r ∈ φ.faces) (hFU : F ⊆ φ.U)
    (hfr : frontier r = F) {z : ℂ} (hz : z ∈ r) : r = connectedComponentIn Fᶜ z := by
  obtain ⟨hro, hrc, hrU⟩ := φ.isOpen_of_mem_faces hr
  have hrF : r ⊆ Fᶜ := fun w hw hwF => hrU hw (hFU hwF)
  refine Subset.antisymm (hrc.isPreconnected.subset_connectedComponentIn hz hrF) ?_
  refine (isPreconnected_connectedComponentIn).subset_of_closure_inter_subset hro
    ⟨z, mem_connectedComponentIn (hrF hz), hz⟩ ?_
  rintro w ⟨hw1, hw2⟩
  rw [closure_eq_self_union_frontier, hfr] at hw1
  exact hw1.resolve_right (connectedComponentIn_subset _ _ hw2)

/-- A bounded face whose frontier is an `O`-arc `F` drawn inside the drawn set is the inner domain
of `F`. -/
theorem eq_inner_of_frontier {r F : Set ℂ} (J : IsJordanParts F) (hr : r ∈ φ.faces) (hFU : F ⊆ φ.U)
    (hfr : frontier r = F) (hb : Bornology.IsBounded r) : r = inner F := by
  obtain ⟨hro, hrc, hrU⟩ := φ.isOpen_of_mem_faces hr
  obtain ⟨z, hz⟩ := hrc.nonempty
  have hrF : r ⊆ Fᶜ := fun w hw hwF => hrU hw (hFU hwF)
  have hK := φ.eq_connectedComponentIn_of_frontier hr hFU hfr hz
  have hzi : z ∈ inner F := ⟨hrF hz, hK ▸ hb⟩
  refine Subset.antisymm (J.subset_inner hrc.isPreconnected (disjoint_compl_left.mono_left hrF)
    ⟨z, hz, hzi⟩) ?_
  rw [hK]
  exact J.isConnected_inner.isPreconnected.subset_connectedComponentIn hzi (J.inner_subset_compl)

/-- An unbounded face whose frontier is an `O`-arc `F` drawn inside the drawn set is the outer
domain of `F`. -/
theorem eq_outer_of_frontier {r F : Set ℂ} (J : IsJordanParts F) (hr : r ∈ φ.faces) (hFU : F ⊆ φ.U)
    (hfr : frontier r = F) (hb : ¬ Bornology.IsBounded r) : r = outer F := by
  obtain ⟨hro, hrc, hrU⟩ := φ.isOpen_of_mem_faces hr
  obtain ⟨z, hz⟩ := hrc.nonempty
  have hrF : r ⊆ Fᶜ := fun w hw hwF => hrU hw (hFU hwF)
  have hK := φ.eq_connectedComponentIn_of_frontier hr hFU hfr hz
  have hzo : z ∈ outer F := ⟨hrF hz, hK ▸ hb⟩
  refine Subset.antisymm (J.subset_outer hrc.isPreconnected (disjoint_compl_left.mono_left hrF)
    ⟨z, hz, hzo⟩) ?_
  rw [hK]
  exact J.isConnected_outer.isPreconnected.subset_connectedComponentIn hzo (J.outer_subset_compl)

/-! ### Images of paths and cycles -/

/-- The image of a list of vertices `x₁ … x_k`: the union of the lines `x₁x₂, …, x_{k-1}x_k`. -/
def pathImage (l : List V) : Set ℂ :=
  ⋃ p ∈ l.zip l.tail, φ.line p.1 p.2

@[simp] theorem pathImage_nil : φ.pathImage [] = ∅ := by
  simp [pathImage]

@[simp] theorem pathImage_single (x : V) : φ.pathImage [x] = ∅ := by
  simp [pathImage]

theorem pathImage_cons_cons (x y : V) (l : List V) :
    φ.pathImage (x :: y :: l) = φ.line x y ∪ φ.pathImage (y :: l) := by
  simp [pathImage, List.zip_cons_cons]

theorem pathImage_append (a : List V) (y : V) (b : List V) :
    φ.pathImage (a ++ y :: b) = φ.pathImage (a ++ [y]) ∪ φ.pathImage (y :: b) := by
  induction a with
  | nil => simp
  | cons x a ih =>
    cases a with
    | nil => simp [pathImage_cons_cons]
    | cons x' a =>
      simp only [List.cons_append] at ih ⊢
      rw [pathImage_cons_cons, ih, pathImage_cons_cons, union_assoc]

theorem cycleImage_cons (x : V) (t : List V) :
    φ.cycleImage (x :: t) = φ.pathImage (x :: t ++ [x]) := by
  simp only [cycleImage, pathImage, zip_rotate_one_cons]

theorem cycleImage_rotate (C : List V) (k : ℕ) : φ.cycleImage (C.rotate k) = φ.cycleImage C := by
  ext z
  simp only [cycleImage, zip_rotate_rotate, mem_iUnion, List.mem_rotate]

/-- The line of an edge `ab` of a path list lies in the drawn set. -/
theorem pathImage_subset_U {l : List V} (h : IsPathList G R l) : φ.pathImage l ⊆ φ.U := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil => simp
    | cons y l =>
      rw [pathImage_cons_cons]
      refine union_subset (φ.line_subset_U (h.2.2 x (by simp)) (h.2.2 y (by simp)) ?_) (ih h.tail)
      exact (List.isChain_cons_cons.mp h.2.1).1

/-- The points of `R` on the image of a path list are the points of its vertices. -/
theorem mem_of_pt_mem_pathImage {l : List V} (h : IsPathList G R l) {w : V} (hw : w ∈ R)
    (hwl : φ.pt w ∈ φ.pathImage l) : w ∈ l := by
  induction l with
  | nil => simp at hwl
  | cons x l ih =>
    cases l with
    | nil => simp at hwl
    | cons y l =>
      rw [pathImage_cons_cons] at hwl
      rcases hwl with hwl | hwl
      · rcases φ.avoid x (h.2.2 x (by simp)) y (h.2.2 y (by simp))
          (List.isChain_cons_cons.mp h.2.1).1 w hw hwl with rfl | rfl <;> simp
      · exact List.mem_cons_of_mem _ (ih h.tail hwl)

/-- The line of an edge `xy` meets the image of a path list that starts at `y` and avoids `x` only
at the point of `y`. -/
theorem line_inter_pathImage {x y : V} {l : List V} (hx : x ∈ R) (hxy : G.Adj x y)
    (h : IsPathList G R (y :: l)) (hxl : x ∉ y :: l) :
    φ.line x y ∩ φ.pathImage (y :: l) ⊆ {φ.pt y} := by
  have hy := h.2.2 y (by simp)
  rintro z ⟨hz1, hz2⟩
  simp only [pathImage, mem_iUnion] at hz2
  obtain ⟨⟨a, b⟩, hab, hz2⟩ := hz2
  have ha : a ∈ y :: l := List.of_mem_zip hab |>.1
  have hb : b ∈ (y :: l).tail := List.of_mem_zip hab |>.2
  have hb' : b ∈ y :: l := List.mem_of_mem_tail hb
  have hadj : G.Adj a b := isChain_iff_zip.mp h.2.1 _ hab
  have hne : s(x, y) ≠ s(a, b) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hxl ha
    · exact hxl hb'
  obtain ⟨w, ⟨hw1, hw2⟩, rfl⟩ := φ.inter x hx y hy a (h.2.2 a ha) b (h.2.2 b hb') hxy hadj hne
    ⟨hz1, hz2⟩
  rcases hw1 with rfl | rfl
  · rcases hw2 with rfl | rfl
    · exact absurd ha hxl
    · exact absurd hb' hxl
  · rfl

/-- The image of a path list with at least two vertices is a line between the points of its
ends. -/
theorem isLine_pathImage : ∀ {x : V} {l : List V} (hl : l ≠ []), IsPathList G R (x :: l) →
    IsLineWithEnds (φ.pathImage (x :: l)) (φ.pt x) (φ.pt (l.getLast hl))
  | x, [y], _, h => by
    simpa [pathImage_cons_cons] using
      φ.isLine x (h.2.2 x (by simp)) y (h.2.2 y (by simp)) (List.isChain_cons_cons.mp h.2.1).1
  | x, y :: z :: l, _, h => by
    rw [pathImage_cons_cons]
    have hxy := (List.isChain_cons_cons.mp h.2.1).1
    have h1 := φ.isLine x (h.2.2 x (by simp)) y (h.2.2 y (by simp)) hxy
    have h2 := isLine_pathImage (x := y) (l := z :: l) (List.cons_ne_nil _ _) h.tail
    rw [List.getLast_cons (by simp)]
    refine h1.union h2 (Subset.antisymm (φ.line_inter_pathImage (h.2.2 x (by simp)) hxy h.tail
      (List.nodup_cons.mp h.1).1) ?_)
    rintro _ rfl
    exact ⟨h1.right_mem, h2.left_mem⟩

/-- The line of an edge `uv` meets the image of a path list only at the points of the common
vertices, unless `uv` is an edge of the path. -/
theorem line_inter_pathImage_sub {u v : V} {l : List V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v)
    (h : IsPathList G R l) (hne : ∀ p ∈ l.zip l.tail, s(u, v) ≠ s(p.1, p.2)) :
    φ.line u v ∩ φ.pathImage l ⊆ φ.pt '' ({u, v} ∩ {x | x ∈ l}) := by
  rintro z ⟨hz1, hz2⟩
  simp only [pathImage, mem_iUnion] at hz2
  obtain ⟨⟨a, b⟩, hab, hz2⟩ := hz2
  have ha : a ∈ l := (List.of_mem_zip hab).1
  have hb : b ∈ l := List.mem_of_mem_tail (List.of_mem_zip hab).2
  obtain ⟨w, ⟨hw1, hw2⟩, rfl⟩ := φ.inter u hu v hv a (h.2.2 a ha) b (h.2.2 b hb) huv
    (isChain_iff_zip.mp h.2.1 _ hab) (hne _ hab) ⟨hz1, hz2⟩
  refine ⟨w, ⟨hw1, ?_⟩, rfl⟩
  rcases hw2 with rfl | rfl
  · exact ha
  · exact hb

/-- The image of a cycle of `G` on `R` is an `O`-arc. -/
theorem isOArc_cycleImage {C : List V} (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R) :
    Nonempty (Circle ≃ₜ φ.cycleImage C) := by
  obtain ⟨x, t, w, rfl⟩ : ∃ x t w, C = x :: (t ++ [w]) := by
    rcases C with _ | ⟨x, C⟩
    · simp [IsCycleList] at hC
    · rcases List.eq_nil_or_concat C with h | ⟨t, w, rfl⟩
      · subst h; simp [IsCycleList] at hC
      · exact ⟨x, t, w, by simp⟩
  have hP := hC.isPathList hR
  have hlen : 1 ≤ t.length := by have := hC.1; simp at this; omega
  have hxR := hR x (by simp)
  have hwR := hR w (by simp)
  have hadj : G.Adj w x := by
    have := hC.2.2 (w, x) (by
      rw [zip_rotate_one_cons, mem_zip_tail_iff]
      refine ⟨t.length + 1, by simp, by simp, by simp⟩)
    exact this
  rw [cycleImage_cons, show x :: (t ++ [w]) ++ [x] = (x :: t) ++ w :: [x] by simp,
    pathImage_append, pathImage_cons_cons, pathImage_single, union_empty]
  have h1 := φ.isLine_pathImage (x := x) (l := t ++ [w]) (by simp) (by simpa using hP)
  rw [List.getLast_append_singleton] at h1
  have h2 := φ.isLine w hwR x hxR hadj
  have hi : φ.pathImage (x :: t ++ [w]) ∩ φ.line w x = {φ.pt x, φ.pt w} := by
    refine Subset.antisymm ?_ ?_
    · rw [inter_comm]
      refine (φ.line_inter_pathImage_sub hwR hxR hadj (by simpa using hP) ?_).trans ?_
      · rintro ⟨a, b⟩ hab he
        obtain ⟨i, hi, rfl, rfl⟩ := mem_zip_tail_iff.mp hab
        have hnd : (x :: t ++ [w]).Nodup := by simpa using hP.1
        refine not_ends_consecutive hnd (by simp; omega) hi ?_
        rw [Sym2.eq_swap]
        convert he using 2 <;> simp
      · rintro _ ⟨y, ⟨rfl | rfl, -⟩, rfl⟩ <;> simp
    · rintro _ (rfl | rfl)
      · exact ⟨h1.left_mem, h2.right_mem⟩
      · exact ⟨h1.right_mem, h2.left_mem⟩
  obtain ⟨a, ha, hra, ha0, ha1⟩ := h1.exists_arc
  obtain ⟨b, hb, hrb, hb0, hb1⟩ := h2.symm.exists_arc
  have := oArc_of_two_arcs ha hb (by rw [ha0, hb0]) (by rw [ha1, hb1]) (fun s u he => by
    have hz : a s ∈ ({φ.pt x, φ.pt w} : Set ℂ) := by
      rw [← hi]
      exact ⟨hra ▸ mem_range_self s, he ▸ hrb ▸ mem_range_self u⟩
    rcases hz with hz | hz
    · left
      exact ⟨ha.2 (hz.trans ha0.symm), hb.2 ((he.symm.trans hz).trans hb0.symm)⟩
    · right
      exact ⟨ha.2 (hz.trans ha1.symm), hb.2 ((he.symm.trans hz).trans hb1.symm)⟩)
  rwa [hra, hrb] at this

/-- The images of two path lists meet only at the points of common vertices, if no edge of one is an
edge of the other. -/
theorem pathImage_inter_pathImage {l₁ l₂ : List V} (h₁ : IsPathList G R l₁) (h₂ : IsPathList G R l₂)
    (hne : ∀ p ∈ l₁.zip l₁.tail, ∀ q ∈ l₂.zip l₂.tail, s(p.1, p.2) ≠ s(q.1, q.2)) :
    φ.pathImage l₁ ∩ φ.pathImage l₂ ⊆ φ.pt '' {x | x ∈ l₁ ∧ x ∈ l₂} := by
  rintro z ⟨hz1, hz2⟩
  simp only [pathImage, mem_iUnion] at hz1 hz2
  obtain ⟨⟨a, b⟩, hab, hz1⟩ := hz1
  obtain ⟨⟨a', b'⟩, hab', hz2⟩ := hz2
  have ha : a ∈ l₁ := (List.of_mem_zip hab).1
  have hb : b ∈ l₁ := List.mem_of_mem_tail (List.of_mem_zip hab).2
  have ha' : a' ∈ l₂ := (List.of_mem_zip hab').1
  have hb' : b' ∈ l₂ := List.mem_of_mem_tail (List.of_mem_zip hab').2
  obtain ⟨w, ⟨hw1, hw2⟩, rfl⟩ := φ.inter a (h₁.2.2 a ha) b (h₁.2.2 b hb) a' (h₂.2.2 a' ha')
    b' (h₂.2.2 b' hb') (isChain_iff_zip.mp h₁.2.1 _ hab) (isChain_iff_zip.mp h₂.2.1 _ hab')
    (hne _ hab _ hab') ⟨hz1, hz2⟩
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · rcases hw1 with rfl | rfl
    · exact ha
    · exact hb
  · rcases hw2 with rfl | rfl
    · exact ha'
    · exact hb'

/-- The support of a path of `G` through vertices of `R` is a path list. -/
theorem isPathList_support {u v : V} {q : G.Walk u v} (hq : q.IsPath) (hR : ∀ x ∈ q.support, x ∈ R) :
    IsPathList G R q.support :=
  ⟨hq.support_nodup, q.isChain_adj_support, hR⟩

/-- The point of every vertex of a path list with at least two vertices lies on its image. -/
theorem pt_mem_pathImage {l : List V} (h : IsPathList G R l) (h2 : 2 ≤ l.length) {y : V}
    (hy : y ∈ l) : φ.pt y ∈ φ.pathImage l := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
  simp only [pathImage, mem_iUnion]
  by_cases hi1 : i + 1 < l.length
  · refine ⟨(l[i], l[i + 1]), mem_zip_tail_iff.mpr ⟨i, hi1, rfl, rfl⟩, ?_⟩
    exact (φ.isLine _ (h.2.2 _ (List.getElem_mem _)) _ (h.2.2 _ (List.getElem_mem _))
      (List.isChain_iff_getElem.mp h.2.1 i hi1)).left_mem
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    refine ⟨(l[j], l[j + 1]), mem_zip_tail_iff.mpr ⟨j, hi, rfl, rfl⟩, ?_⟩
    exact (φ.isLine _ (h.2.2 _ (List.getElem_mem _)) _ (h.2.2 _ (List.getElem_mem _))
      (List.isChain_iff_getElem.mp h.2.1 j hi)).right_mem

omit φ in
/-- In a cycle `C` of length `n`, closed up as `L = C ++ [C[0]]`, the edges `L[i] L[i+1]` at
different positions `i < j < n` are different. -/
theorem closed_edge_ne {C : List V} (hnd : C.Nodup) (h3 : 3 ≤ C.length) (hne : C ≠ [])
    {i j : ℕ} (hij : i < j) (hj : j < C.length) :
    s((C ++ [C.head hne])[i]'(by simp; omega), (C ++ [C.head hne])[i + 1]'(by simp; omega)) ≠
      s((C ++ [C.head hne])[j]'(by simp; omega), (C ++ [C.head hne])[j + 1]'(by simp; omega)) := by
  intro he
  have hL : ∀ m (hm : m < C.length), (C ++ [C.head hne])[m]'(by simp; omega) = C[m] := fun m hm =>
    List.getElem_append_left hm
  have hinj := fun {a b : ℕ} (ha : a < C.length) (hb : b < C.length) (h : C[a] = C[b]) =>
    (List.Nodup.getElem_inj_iff hnd).mp h
  rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, h2⟩
  · rw [hL i (by omega), hL j hj] at h1
    have := hinj (by omega) hj h1
    omega
  · rw [hL (i + 1) (by omega), hL j hj] at h2
    have := hinj (by omega) hj h2
    by_cases hj1 : j + 1 < C.length
    · rw [hL i (by omega), hL (j + 1) hj1] at h1
      have := hinj (by omega) hj1 h1
      omega
    · have hjn : j + 1 = C.length := by omega
      have hlast : (C ++ [C.head hne])[j + 1]'(by simp; omega) = C[0]'(by omega) := by
        rw [List.getElem_append_right (by omega)]
        simp [hjn, List.head_eq_getElem]
      rw [hL i (by omega), hlast] at h1
      have := hinj (by omega) (by omega) h1
      omega

/-- A cycle of `G` on `R`, closed up as `L = C ++ [C[0]]` and cut at `C[k]` (`0 < k < n`) into the two
arcs `L[0] … L[k]` and `L[k] … L[n]`. Both arcs are path lists, the image of the cycle is the union of
their images, and these images meet only at the points of `C[0]` and `C[k]`. -/
theorem cycleImage_split {C : List V} (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R) (hne : C ≠ [])
    {k : ℕ} (hk0 : 0 < k) (hk : k < C.length) :
    IsPathList G R ((C ++ [C.head hne]).take (k + 1)) ∧ IsPathList G R ((C ++ [C.head hne]).drop k) ∧
    φ.cycleImage C = φ.pathImage ((C ++ [C.head hne]).take (k + 1)) ∪
      φ.pathImage ((C ++ [C.head hne]).drop k) ∧
    φ.pathImage ((C ++ [C.head hne]).take (k + 1)) ∩ φ.pathImage ((C ++ [C.head hne]).drop k) =
      {φ.pt (C.head hne), φ.pt C[k]} := by
  set L := C ++ [C.head hne] with hLdef
  have hn := hC.1
  have hnd := hC.2.1
  have hLlen : L.length = C.length + 1 := by simp [L]
  have hL : ∀ m (hm : m < C.length), L[m]'(by omega) = C[m] := fun m hm =>
    List.getElem_append_left hm
  have hLn : L[C.length]'(by omega) = C.head hne := by
    simp [L, List.getElem_append_right]
  have hhead : C.head hne = C[0]'(by omega) := List.head_eq_getElem hne
  have hchain : L.IsChain G.Adj := by
    obtain ⟨x, t, rfl⟩ : ∃ x t, C = x :: t := by
      cases C with
      | nil => exact absurd rfl hne
      | cons x t => exact ⟨x, t, rfl⟩
    have h := hC.2.2
    rw [zip_rotate_one_cons] at h
    exact isChain_iff_zip.mpr h
  have hinj := fun {a b : ℕ} (ha : a < C.length) (hb : b < C.length) (h : C[a] = C[b]) =>
    (List.Nodup.getElem_inj_iff hnd).mp h
  -- the vertices of `L` at two positions
  have hLinj : ∀ {a b : ℕ} (ha : a ≤ C.length) (hb : b ≤ C.length), a < b →
      L[a]'(by omega) = L[b]'(by omega) → a = 0 ∧ b = C.length := by
    intro a b ha hb hab he
    by_cases hbn : b < C.length
    · rw [hL a (by omega), hL b hbn] at he
      have := hinj (by omega) hbn he
      omega
    · have hbn' : b = C.length := by omega
      subst hbn'
      rw [hL a (by omega), hLn, hhead] at he
      exact ⟨hinj (by omega) (by omega) he, rfl⟩
  have hR' : ∀ y ∈ L, y ∈ R := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hR y hy
    · simp only [List.mem_singleton] at hy
      exact hy ▸ hR _ (List.head_mem hne)
  have hP1 : IsPathList G R (L.take (k + 1)) := by
    refine ⟨?_, hchain.take _, fun y hy => hR' y (List.mem_of_mem_take hy)⟩
    rw [List.nodup_iff_injective_get]
    intro ⟨a, ha⟩ ⟨b, hb⟩ he
    simp only [List.get_eq_getElem, List.getElem_take, List.length_take] at he ha hb
    ext
    simp only
    rcases lt_trichotomy a b with hab | hab | hab
    · have := hLinj (by omega) (by omega) hab he; omega
    · exact hab
    · have := hLinj (by omega) (by omega) hab he.symm; omega
  have hP2 : IsPathList G R (L.drop k) := by
    refine ⟨?_, hchain.drop _, fun y hy => hR' y (List.mem_of_mem_drop hy)⟩
    rw [List.nodup_iff_injective_get]
    intro ⟨a, ha⟩ ⟨b, hb⟩ he
    simp only [List.get_eq_getElem, List.getElem_drop, List.length_drop] at he ha hb
    ext
    simp only
    rcases lt_trichotomy a b with hab | hab | hab
    · have := hLinj (by omega) (by omega) (by omega : k + a < k + b) he; omega
    · exact hab
    · have := hLinj (by omega) (by omega) (by omega : k + b < k + a) he.symm; omega
  refine ⟨hP1, hP2, ?_, ?_⟩
  · obtain ⟨x, t, rfl⟩ : ∃ x t, C = x :: t := by
      cases C with
      | nil => exact absurd rfl hne
      | cons x t => exact ⟨x, t, rfl⟩
    rw [cycleImage_cons]
    have hsplit : x :: t ++ [x] = L.take k ++ L[k]'(by omega) :: L.drop (k + 1) := by
      rw [← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
      rfl
    rw [hsplit, pathImage_append, ← List.take_succ_eq_append_getElem (by omega),
      ← List.drop_eq_getElem_cons (by omega)]
  · refine Subset.antisymm ?_ ?_
    · refine (φ.pathImage_inter_pathImage hP1 hP2 ?_).trans ?_
      · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab'
        obtain ⟨i, hi, rfl, rfl⟩ := mem_zip_tail_iff.mp hab
        obtain ⟨j, hj, rfl, rfl⟩ := mem_zip_tail_iff.mp hab'
        simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_drop] at hi hj ⊢
        have := closed_edge_ne hnd hn hne (i := i) (j := k + j) (by omega) (by omega)
        simpa [L, Nat.add_assoc] using this
      · rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
        obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hy1
        obtain ⟨b, hb, hb'⟩ := List.mem_iff_getElem.mp hy2
        simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_drop] at ha hb hb' ⊢
        rcases lt_trichotomy a (k + b) with hab | hab | hab
        · have := hLinj (by omega) (by omega) hab hb'.symm
          left
          obtain ⟨rfl, -⟩ := this
          rw [hL 0 (by omega), hhead]
        · right
          simp only [hab]
          rw [hL (k + b) (by omega)]
          congr 2
          omega
        · omega
    · have h1 : 2 ≤ (L.take (k + 1)).length := by simp; omega
      have h2 : 2 ≤ (L.drop k).length := by simp; omega
      rintro _ (h | h) <;> rw [h]
      · refine ⟨φ.pt_mem_pathImage hP1 h1 ?_, φ.pt_mem_pathImage hP2 h2 ?_⟩
        · rw [hhead, ← hL 0 (by omega)]
          exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩
        · rw [← hLn]
          exact List.mem_iff_getElem.mpr ⟨C.length - k, by simp; omega, by simp; congr; omega⟩
      · refine ⟨φ.pt_mem_pathImage hP1 h1 ?_, φ.pt_mem_pathImage hP2 h2 ?_⟩
        · rw [← hL k hk]
          exact List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩
        · rw [← hL k hk]
          exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩
