module

public import GraphMinor.HP25.Split
import GraphMinor.HP25.Prop23
import GraphMinor.HP25.Link
import GraphMinor.HP25.RibEdges
import GraphMinor.Surface.Crossing
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.SurfaceGraph
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Basic

/-!
# A rib cut by a path between two frame vertices

Let `φ` be a plane embedding with the faces of a rib with frame `C`, and let `l = a m b` be a path
of the rib between two non-consecutive frame vertices, with no inner vertex on the frame. The path
need not be induced. Its image `c` cuts the closed disc bounded by the image of `C` into two closed
discs, bounded by `F₁` and `F₂` (`IsRibEmbedding.theta`: the theta curve built in the proof of
`IsRibEmbedding.split`, which does not use that the path is induced).

These are the drawing facts of the strip argument for Lemma 5.4 (see `Sec5Strip.lean`):
* `isPathConnected_inner_union`: a Jordan domain together with any part of its frontier is
  path-connected;
* `IsTheta.side_of_arc`: a connected set in the disc that misses the cut and meets the open arc of one
  side lies on that side;
* `IsRibEmbedding.tri_side`: the face of a triangle lies in the inner domain of `F₁` or of `F₂`;
* `tri_side_eq`: the two triangles at an edge that is not an edge of `l` lie on the same side;
* `IsRibEmbedding.exists_tri_at_cut`: at an edge of `l`, some triangle lies on the side `F₁` (and, by
  symmetry, some triangle lies on the side `F₂`);
* `pt_not_mem_side`: a vertex joined to the open arc of `F₁` by a path list that misses `l` is drawn
  outside the closed side of `F₂`.
-/

public section

/-! ### Theta curves -/

namespace GraphMinor.Surface.IsTheta

open Set

variable {F F₁ F₂ A₁ A₂ c : Set ℂ} {p q : ℂ}

/-- A connected set inside `F` that misses the middle arc and meets the open arc `A₁` lies in the
closed inner domain of `F₁`. -/
theorem side_of_arc (h : IsTheta F F₁ F₂ A₁ A₂ c p q) {Y : Set ℂ} (hY : IsPreconnected Y)
    (hYF : Y ⊆ inner F ∪ F) (hYc : Disjoint Y c) {z : ℂ} (hzY : z ∈ Y) (hz : z ∈ A₁ \ {p, q}) :
    Y ⊆ inner F₁ ∪ F₁ := by
  rcases h.sep hY hYF hYc with h1 | h2
  · exact h1
  · exfalso
    have hout : z ∈ outer F₂ := h.symm.open_arc_subset_outer hz
    rcases h2 hzY with h' | h'
    · exact Set.disjoint_left.mp h.parts₂.disjoint h' hout
    · exact hout.1 h'

end GraphMinor.Surface.IsTheta

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-! ### Closed discs -/

/-- A Jordan domain together with part of its frontier is path-connected: the closed domain is a
closed disc, and in a chart it becomes the open unit disc together with part of the unit circle, a
convex set. -/
theorem isPathConnected_inner_union {F S : Set ℂ} (hF : Nonempty (Circle ≃ₜ F)) (hS : S ⊆ F) :
    IsPathConnected (Surface.inner F ∪ S) := by
  obtain ⟨hD, hDb⟩ := isClosedDisc_closedInner hF
  obtain ⟨h, g, hh, hg, hhm, hgm, hgh, hhg, hbd⟩ := hD.exists_chart
  have J := isJordanParts hF.some
  rw [hDb] at hbd
  have hsub : ∀ {z}, z ∈ F → z ∈ closedInner F := fun hz => Or.inr hz
  have hinD : ∀ {z}, z ∈ Surface.inner F → z ∈ closedInner F := fun hz => Or.inl hz
  -- `h` maps the open domain into the open ball
  have hball : ∀ {z}, z ∈ Surface.inner F → h z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have h1 : h z ∈ Metric.closedBall (0 : ℂ) 1 := hhm (hinD hz)
    refine Metric.mem_ball.mpr (lt_of_le_of_ne (Metric.mem_closedBall.mp h1) fun he => ?_)
    have : h z ∈ Metric.sphere (0 : ℂ) 1 := Metric.mem_sphere.mpr (by simpa using he)
    rw [← hbd] at this
    obtain ⟨z', hz', he'⟩ := this
    have := hgh (hsub hz')
    rw [he', hgh (hinD hz)] at this
    exact hz.1 (this ▸ hz')
  set K : Set ℂ := Metric.ball 0 1 ∪ h '' S with hK
  have hKc : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    have hxc : x ∈ Metric.closedBall (0 : ℂ) 1 := by
      rcases hx with hx | ⟨z, hz, rfl⟩
      · exact Metric.ball_subset_closedBall hx
      · exact hhm (hsub (hS hz))
    have hyc : y ∈ Metric.closedBall (0 : ℂ) 1 := by
      rcases hy with hy | ⟨z, hz, rfl⟩
      · exact Metric.ball_subset_closedBall hy
      · exact hhm (hsub (hS hz))
    by_cases hxy : x = y
    · subst hxy
      rw [← add_smul, hab, one_smul]
      exact hx
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hy
    rcases hb.eq_or_lt with rfl | hb'
    · rw [add_zero] at hab
      subst hab
      simpa using hx
    left
    have := (strictConvex_closedBall ℝ (0 : ℂ) 1) hxc hyc hxy ha' hb' hab
    rwa [interior_closedBall _ one_ne_zero] at this
  have hKne : K.Nonempty := ⟨0, Or.inl (Metric.mem_ball_self one_pos)⟩
  have hKp := hKc.isPathConnected hKne
  have hKD : K ⊆ Metric.closedBall 0 1 := by
    rintro x (hx | ⟨z, hz, rfl⟩)
    · exact Metric.ball_subset_closedBall hx
    · exact hhm (hsub (hS hz))
  have himg : g '' K = Surface.inner F ∪ S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with hx | ⟨z, hz, rfl⟩
      · left
        have hgD : g x ∈ closedInner F := hgm (Metric.ball_subset_closedBall hx)
        rcases hgD with h1 | h1
        · exact h1
        · exfalso
          have : h (g x) ∈ Metric.sphere (0 : ℂ) 1 := by rw [← hbd]; exact ⟨g x, h1, rfl⟩
          rw [hhg (Metric.ball_subset_closedBall hx)] at this
          exact (Metric.mem_ball.mp hx).ne (by simpa using Metric.mem_sphere.mp this)
      · right
        rw [hgh (hsub (hS hz))]
        exact hz
    · rintro (hz | hz)
      · exact ⟨h z, Or.inl (hball hz), hgh (hinD hz)⟩
      · exact ⟨h z, Or.inr ⟨z, hz, rfl⟩, hgh (hsub (hS hz))⟩
  rw [← himg]
  exact hKp.image' (hg.mono hKD)

namespace PlaneEmbedding

variable {φ : PlaneEmbedding G R} {C : List V}

/-- **The theta curve of a cut.** Let `C` be, up to rotation, `a A b B`, with `a`, `b` not
consecutive on `C`, and let `a m b` be a path of the rib with no inner vertex on `C`. The images of
`C`, of its two arcs between `a` and `b`, and of the path form a theta curve, and the drawing lies in
the closed inner domain of the image of `C`. The two arcs are paths of the rib. -/
theorem IsRibEmbedding.theta (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {k : ℕ} {a b : V} {A B m : List V}
    (hrot : C.rotate k = a :: A ++ b :: B) (hab : ¬ IsCycleEdge C a b)
    (hl : IsPathList G R (a :: m ++ [b])) (hmC : ∀ v ∈ m, v ∉ C) :
    IsTheta (φ.cycleImage C) (φ.cycleImage (a :: A ++ b :: m.reverse))
      (φ.cycleImage (b :: B ++ a :: m)) (φ.pathImage (a :: A ++ [b]))
      (φ.pathImage (b :: B ++ [a])) (φ.pathImage (a :: m ++ [b])) (φ.pt a) (φ.pt b) ∧
    φ.U ⊆ inner (φ.cycleImage C) ∪ φ.cycleImage C ∧
    IsCycleList G (a :: A ++ b :: m.reverse) ∧ IsCycleList G (b :: B ++ a :: m) ∧
    (∀ x ∈ a :: A ++ b :: m.reverse, x ∈ R) ∧ (∀ x ∈ b :: B ++ a :: m, x ∈ R) ∧
    A ≠ [] ∧ B ≠ [] ∧ IsPathList G R (a :: A ++ [b]) ∧ IsPathList G R (b :: B ++ [a]) := by
  classical
  set l := a :: m ++ [b] with hl_def
  set C' := a :: A ++ b :: B with hC'_def
  have hC' : IsCycleList G C' := hrot ▸ hC.rotate k
  have hmemC : ∀ v, v ∈ C' ↔ v ∈ C := fun v => by rw [← hrot]; exact List.mem_rotate
  have hC'R : ∀ v ∈ C', v ∈ R := fun v hv => hR v ((hmemC v).mp hv)
  have habC' : ¬ IsCycleEdge C' a b := by rw [← hrot, isCycleEdge_rotate]; exact hab
  have hnd := hC'.2.1
  rw [hC'_def, List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd
  have haA : a ∉ A := fun h => hnd.1 (List.mem_append_left _ h)
  have hab' : a ≠ b := fun h => hnd.1 (List.mem_append_right _ (h ▸ List.mem_cons_self))
  have hAB : ∀ v ∈ A, v ∉ B := fun v hv hvB => hnd.2.2.2 v hv v (List.mem_cons_of_mem _ hvB) rfl
  have hbB : b ∉ B := hnd.2.2.1.1
  have hPA : IsPathList G R (a :: A ++ [b]) := by
    have hP := hC'.isPathList hC'R
    rw [show C' = (a :: A ++ [b]) ++ B by simp [hC'_def]] at hP
    exact hP.left_of_append
  have hPB : IsPathList G R (b :: B ++ [a]) := by
    have hP := (hC'.rotate (a :: A).length).isPathList
      (fun v hv => hC'R v (List.mem_rotate.mp hv))
    rw [hC'_def, List.rotate_append_length_eq,
      show b :: B ++ a :: A = (b :: B ++ [a]) ++ A by simp] at hP
    exact hP.left_of_append
  have hnA : ¬ IsListEdge (a :: A ++ [b]) a b := fun h => habC' (by
    refine isCycleEdge_of_isListEdge (x := a) (t := A ++ b :: B) ?_
    rw [show a :: (A ++ b :: B) ++ [a] = (a :: A ++ [b]) ++ (B ++ [a]) by simp]
    exact h.append_left)
  have hnB : ¬ IsListEdge (b :: B ++ [a]) a b := fun h => habC' (by
    refine isCycleEdge_of_isListEdge (x := a) (t := A ++ b :: B) ?_
    rw [show a :: (A ++ b :: B) ++ [a] = (a :: A) ++ (b :: B ++ [a]) by simp]
    exact h.append_right)
  have hA : A ≠ [] := by
    rintro rfl
    exact hnA ⟨(a, b), by simp, rfl⟩
  have hB : B ≠ [] := by
    rintro rfl
    exact hnB ⟨(b, a), by simp, Sym2.eq_swap⟩
  have hmA : ∀ v ∈ A, v ∉ m := fun v hv hvm =>
    hmC v hvm ((hmemC v).mp (by simp [hC'_def, hv]))
  have hmB : ∀ v ∈ B, v ∉ m := fun v hv hvm =>
    hmC v hvm ((hmemC v).mp (by simp [hC'_def, hv]))
  have hcomAB : ∀ v ∈ a :: A ++ [b], v ∈ b :: B ++ [a] → v = a ∨ v = b := by
    intro v h1 h2
    by_contra hne
    push Not at hne
    exact hAB v (by simpa [hne.1, hne.2] using h1) (by simpa [hne.1, hne.2] using h2)
  have hcomAl : ∀ v ∈ a :: A ++ [b], v ∈ l → v = a ∨ v = b := by
    intro v h1 h2
    by_contra hne
    push Not at hne
    exact hmA v (by simpa [hne.1, hne.2] using h1) (by simpa [hl_def, hne.1, hne.2] using h2)
  have hcomBl : ∀ v ∈ b :: B ++ [a], v ∈ l → v = a ∨ v = b := by
    intro v h1 h2
    by_contra hne
    push Not at hne
    exact hmB v (by simpa [hne.1, hne.2] using h1) (by simpa [hl_def, hne.1, hne.2] using h2)
  have hlrev : IsPathList G R (b :: m.reverse ++ [a]) := by
    have := hl.reverse
    simpa [hl_def] using this
  have hC₁ : IsCycleList G (a :: A ++ b :: m.reverse) :=
    isCycleList_of_two_paths hPA hlrev (fun v hv hvm => hmA v hv (List.mem_reverse.mp hvm)) hab'
      (Or.inl hA)
  have hC₂ : IsCycleList G (b :: B ++ a :: m) :=
    isCycleList_of_two_paths hPB hl hmB hab'.symm (Or.inl hB)
  have hC₁R : ∀ x ∈ a :: A ++ b :: m.reverse, x ∈ R := fun x hx =>
    by
      rcases List.mem_append.mp hx with h | h
      · exact hPA.2.2 x (List.mem_append_left _ h)
      · exact hlrev.2.2 x (List.mem_append_left _ h)
  have hC₂R : ∀ x ∈ b :: B ++ a :: m, x ∈ R := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hPB.2.2 x (List.mem_append_left _ h)
    · exact hl.2.2 x (List.mem_append_left _ h)
  have hl2 : 2 ≤ l.length := by simp [hl_def]
  have hFC : φ.cycleImage C = φ.cycleImage C' := by rw [← φ.cycleImage_rotate C k, hrot]
  have J : IsJordanParts (φ.cycleImage C') := isJordanParts (φ.isOArc_cycleImage hC' hC'R).some
  have hUF : φ.U ⊆ Surface.inner (φ.cycleImage C') ∪ φ.cycleImage C' := by
    intro z hz
    by_cases hzF : z ∈ φ.cycleImage C'
    · exact Or.inr hzF
    · have hz' : z ∈ inner (φ.cycleImage C') ∪ outer (φ.cycleImage C') := by
        rw [J.union_eq]; exact hzF
      rcases hz' with h | h
      · exact Or.inl h
      · exact absurd h (Set.disjoint_left.mp (hFC ▸ hφ.disjoint_outer hC hR) hz)
  have hla : a ∈ l := by simp [hl_def]
  have hlb : b ∈ l := by simp [hl_def]
  refine ⟨?_, hFC ▸ hUF, hC₁, hC₂, hC₁R, hC₂R, hA, hB, hPA, hPB⟩
  rw [hFC]
  refine ⟨J, isJordanParts (φ.isOArc_cycleImage hC₁ hC₁R).some,
    isJordanParts (φ.isOArc_cycleImage hC₂ hC₂R).some, φ.cycleImage_two_paths a b A B, ?_,
    φ.cycleImage_two_paths b a B m, φ.pathImage_inter_subset_pair hPA hPB hcomAB hnA,
    ⟨φ.pt_mem_pathImage hl hl2 hla, φ.pt_mem_pathImage hl hl2 hlb⟩, ?_,
    ⟨φ.pt_mem_cycleImage hC' hC'R (by simp [hC'_def]),
      φ.pt_mem_cycleImage hC' hC'R (by simp [hC'_def])⟩,
    (φ.isCompact_isConnected_pathImage hl hl2).2.isPreconnected, ?_, ?_⟩
  · rw [φ.cycleImage_two_paths a b A m.reverse, ← φ.pathImage_reverse l]
    congr 2
    simp [hl_def]
  · rintro z ⟨hzc, hzab⟩
    have hzF : z ∉ φ.cycleImage C' := by
      rw [φ.cycleImage_two_paths a b A B]
      rintro (h | h)
      · exact hzab (φ.pathImage_inter_subset_pair hPA hl hcomAl hnA ⟨h, hzc⟩)
      · exact hzab (φ.pathImage_inter_subset_pair hPB hl hcomBl hnB ⟨h, hzc⟩)
    rcases hUF (φ.pathImage_subset_U hl hzc) with h | h
    · exact h
    · exact absurd h hzF
  · obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil A hA
    have hvR := hPA.2.2 v (by simp [hv])
    refine ⟨φ.pt v, φ.pt_mem_pathImage hPA (by simp) (by simp [hv]), ?_⟩
    rintro (h | h)
    · exact haA (φ.injOn hvR (hPA.2.2 a (by simp)) h ▸ hv)
    · have e := φ.injOn hvR (hPA.2.2 b (by simp)) h
      exact hnd.2.2.2 b (e ▸ hv) b List.mem_cons_self rfl
  · obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B hB
    have hvR := hPB.2.2 v (by simp [hv])
    refine ⟨φ.pt v, φ.pt_mem_pathImage hPB (by simp) (by simp [hv]), ?_⟩
    rintro (h | h)
    · have e := φ.injOn hvR (hPB.2.2 a (by simp)) h
      exact hnd.1 (List.mem_append_right _ (List.mem_cons_of_mem _ (e ▸ hv)))
    · exact hbB (φ.injOn hvR (hPB.2.2 b (by simp)) h ▸ hv)


/-- Two adjacent entries of a path list are vertices of `R` joined by an edge. -/
theorem _root_.GraphMinor.HP25.IsPathList.adj_of_isListEdge {l : List V} (hl : IsPathList G R l) {u v : V}
    (h : IsListEdge l u v) : u ∈ R ∧ v ∈ R ∧ G.Adj u v := by
  obtain ⟨pr, hpr, he⟩ := h
  have hadj := isChain_iff_zip.mp hl.2.1 _ hpr
  have h1 : pr.1 ∈ l := (List.of_mem_zip hpr).1
  have h2 : pr.2 ∈ l := List.mem_of_mem_tail (List.of_mem_zip hpr).2
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hl.2.2 _ h1, hl.2.2 _ h2, hadj⟩
  · exact ⟨hl.2.2 _ h2, hl.2.2 _ h1, hadj.symm⟩

variable {F₁ F₂ A₁ A₂ : Set ℂ} {l : List V} {p q : ℂ}

/-- The face of a triangle lies in the inner domain of the image of the frame. -/
theorem IsRibEmbedding.tri_inner (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {x y z : V} (hT : IsTriangleOn G R x y z) :
    Surface.inner (φ.cycleImage [x, y, z]) ⊆ Surface.inner (φ.cycleImage C) := by
  obtain ⟨hf, hdisj⟩ := hφ.inner_mem_faces hT
  have JT := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
  have J := isJordanParts (φ.isOArc_cycleImage hC hR).some
  have hFU := φ.cycleImage_subset_U hC hR
  intro w hw
  have hwF : w ∉ φ.cycleImage C := fun h => Set.disjoint_left.mp hdisj (hFU h) hw
  have : w ∈ Surface.inner (φ.cycleImage C) ∪ outer (φ.cycleImage C) := by
    rw [J.union_eq]; exact hwF
  refine this.resolve_right fun hwo => ?_
  have he := φ.eq_of_mem_faces hf (hφ.outer_mem_faces hC hR) hw hwo
  exact J.not_isBounded_outer (he ▸ JT.isBounded_inner)

/-- **The face of a triangle lies on one side of the cut.** -/
theorem IsRibEmbedding.tri_side (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {x y z : V} (hT : IsTriangleOn G R x y z) :
    Surface.inner (φ.cycleImage [x, y, z]) ⊆ Surface.inner F₁ ∨
      Surface.inner (φ.cycleImage [x, y, z]) ⊆ Surface.inner F₂ := by
  obtain ⟨hf, hdisj⟩ := hφ.inner_mem_faces hT
  have JT := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
  refine JT.isConnected_inner.isPreconnected.subset_or_subset hθ.parts₁.isOpen_inner
    hθ.parts₂.isOpen_inner hθ.disjoint_inner fun w hw => ?_
  rw [← hθ.inner_sdiff]
  exact ⟨hφ.tri_inner hC hR hT hw,
    fun h => Set.disjoint_left.mp hdisj (φ.pathImage_subset_U hl h) hw⟩

/-- A face cannot lie on both sides. -/
theorem _root_.GraphMinor.Surface.IsTheta.not_both {F F₁ F₂ A₁ A₂ c : Set ℂ} {p q : ℂ}
    (hθ : IsTheta F F₁ F₂ A₁ A₂ c p q) {f : Set ℂ} (hf : f.Nonempty) (h₁ : f ⊆ Surface.inner F₁)
    (h₂ : f ⊆ Surface.inner F₂) : False := by
  obtain ⟨w, hw⟩ := hf
  exact Set.disjoint_left.mp hθ.disjoint_inner (h₁ hw) (h₂ hw)

/-- **Two triangles at an edge off the cut lie on the same side.** A point of the line of the edge,
away from its ends, is on the frontier of both faces and off the cut. -/
theorem tri_side_eq (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {u v w w' : V} (hT : IsTriangleOn G R u v w)
    (hT' : IsTriangleOn G R u v w') (huv : ¬ IsListEdge l u v)
    (h₁ : Surface.inner (φ.cycleImage [u, v, w]) ⊆ Surface.inner F₁)
    (h₂ : Surface.inner (φ.cycleImage [u, v, w']) ⊆ Surface.inner F₂) : False := by
  have JT := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
  obtain ⟨hu, hv, -, hadj, -, -⟩ := hT
  have JT' := isJordanParts (φ.isOArc_cycleImage hT'.isCycleList hT'.mem).some
  obtain ⟨z, hzL, hzu, hzv⟩ := exists_inner_point (φ.isLine u hu v hv hadj)
  have hzT : z ∈ closure (Surface.inner (φ.cycleImage [u, v, w])) := by
    rw [JT.closure_inner, φ.cycleImage_three]; exact Or.inr (Or.inl (Or.inl hzL))
  have hzT' : z ∈ closure (Surface.inner (φ.cycleImage [u, v, w'])) := by
    rw [JT'.closure_inner, φ.cycleImage_three]; exact Or.inr (Or.inl (Or.inl hzL))
  have hz1 : z ∈ Surface.inner F₁ ∪ F₁ := by
    rw [← hθ.parts₁.closure_inner]; exact closure_mono h₁ hzT
  have hz2 : z ∈ Surface.inner F₂ ∪ F₂ := by
    rw [← hθ.parts₂.closure_inner]; exact closure_mono h₂ hzT'
  have hzc := hθ.closedInner_inter ⟨hz1, hz2⟩
  have hne : ∀ pr ∈ l.zip l.tail, s(u, v) ≠ s(pr.1, pr.2) := fun pr hpr he => huv ⟨pr, hpr, he⟩
  obtain ⟨x, ⟨hx, -⟩, rfl⟩ := φ.line_inter_pathImage_sub hu hv hadj hl hne ⟨hzL, hzc⟩
  rcases hx with rfl | rfl
  · exact hzu rfl
  · exact hzv rfl


/-- **At an edge of the cut, some triangle lies on the side `F₁`.** Take a point `z` of the line
away from its ends, and a small ball around `z` that misses the rest of the drawing. Since `z` is on
`F₁`, the ball meets the inner domain of `F₁` at a point `w` off the drawing. The segment from `w` to
`z` leaves the face of `w` at a point of the line, away from its ends, so this face is a triangle at
the edge (`IsRibEmbedding.face_at_inner_edge`), and it lies in the inner domain of `F₁`. -/
theorem IsRibEmbedding.exists_tri_at_cut (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {u v : V} (huv : IsListEdge l u v) (huvC : ¬ IsCycleEdge C u v) :
    ∃ w, w ∈ R ∧ G.Adj u w ∧ G.Adj v w ∧
      Surface.inner (φ.cycleImage [u, v, w]) ⊆ Surface.inner F₁ := by
  obtain ⟨hu, hv, hadj⟩ := hl.adj_of_isListEdge huv
  have hLc : φ.line u v ⊆ F₁ := fun z hz => by
    rw [hθ.eq₁]; exact Or.inr (φ.line_subset_pathImage huv hz)
  obtain ⟨z, hzL, hzu, hzv⟩ := exists_inner_point (φ.isLine u hu v hv hadj)
  have hzr : z ∉ φ.rest u v := fun h => by
    rcases φ.line_inter_rest hu hv hadj ⟨hzL, h⟩ with h | h
    · exact hzu h
    · exact hzv h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (φ.isClosed_rest u v).isOpen_compl z hzr
  have hzcl : z ∈ closure (Surface.inner F₁) := by
    rw [hθ.parts₁.closure_inner]; exact Or.inr (hLc hzL)
  obtain ⟨w, hw, hwz⟩ := Metric.mem_closure_iff.mp hzcl ε hε
  have hwb : w ∈ Metric.ball z ε := by rw [Metric.mem_ball, dist_comm]; exact hwz
  have hUeq := φ.U_eq_rest hu hv hadj
  have hwU : w ∉ φ.U := by
    rw [hUeq]
    rintro (h | h)
    · exact hball hwb h
    · exact hw.1 (hLc h)
  obtain ⟨hf, hwf⟩ := φ.mem_faces_of_notMem hwU
  set f := connectedComponentIn (univ \ φ.U) w with hf_def
  obtain ⟨hfo, hfc, hfU⟩ := φ.isOpen_of_mem_faces hf
  have hF₁U : F₁ ⊆ φ.U := by
    rw [hθ.eq₁]
    refine union_subset ?_ (φ.pathImage_subset_U hl)
    intro x hx
    exact φ.cycleImage_subset_U hC hR (hθ.eq ▸ Or.inl hx)
  have hfin : f ⊆ Surface.inner F₁ :=
    hθ.parts₁.subset_inner hfc.isPreconnected
      (Set.disjoint_left.mpr fun x hx hxF => hfU hx (hF₁U hxF)) ⟨w, hwf, hw⟩
  -- the segment from `w` to `z` meets the frontier of `f`
  have hseg : segment ℝ w z ⊆ Metric.ball z ε :=
    (convex_ball z ε).segment_subset hwb (Metric.mem_ball_self hε)
  have hzf : z ∉ f := fun h => hfU h (φ.line_subset_U hu hv hadj hzL)
  obtain ⟨x, hxs, hxcl, hxf⟩ : ∃ x ∈ segment ℝ w z, x ∈ closure f ∧ x ∉ f := by
    by_contra hno
    push Not at hno
    have hsub : segment ℝ w z ⊆ f ∪ (closure f)ᶜ := fun x hx => by
      by_cases h : x ∈ closure f
      · exact Or.inl (hno x hx h)
      · exact Or.inr h
    have := (convex_segment w z).isPreconnected.subset_left_of_subset_union hfo
      isClosed_closure.isOpen_compl (Set.disjoint_left.mpr fun y hy hy' => hy' (subset_closure hy))
      hsub ⟨w, left_mem_segment ℝ w z, hwf⟩
    exact hzf (this (right_mem_segment ℝ w z))
  have hxU : x ∈ φ.U := by
    by_contra hxU
    obtain ⟨hf', hxf'⟩ := φ.mem_faces_of_notMem hxU
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hxcl _ (φ.isOpen_of_mem_faces hf').1 hxf'
    have := φ.eq_of_mem_faces hf' hf hy1 hy2
    exact hxf (this ▸ hxf')
  have hxr : x ∉ φ.rest u v := hball (hseg hxs)
  have hxL : x ∈ φ.line u v := by
    rw [hUeq] at hxU
    exact hxU.resolve_left hxr
  have hptr : ∀ y ∈ R, φ.pt y ∈ φ.rest u v := fun y hy => Or.inl ⟨y, hy, rfl⟩
  have hxu : x ≠ φ.pt u := fun h => hxr (h ▸ hptr u hu)
  have hxv : x ≠ φ.pt v := fun h => hxr (h ▸ hptr v hv)
  obtain ⟨w', hw', huw', hvw', hfe⟩ :=
    hφ.face_at_inner_edge hC hR hu hv hadj huvC hf hxL hxu hxv hxcl
  exact ⟨w', hw', huw', hvw', hfe ▸ hfin⟩


/-- **A vertex joined to the open arc `A₁` away from the cut is drawn outside the closed side of
`F₂`.** Let `l'` be a path list with no vertex on `l`, through a vertex `u` and a vertex `t` drawn on
`A₁` away from the ends of the cut. The image of `l'` is connected, misses the cut and meets the open
arc `A₁`, so it lies in the closed side of `F₁` (`IsTheta.side_of_arc`), and the point of `u` is off
the cut. -/
theorem pt_not_mem_side (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hUF : φ.U ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C) (hl : IsPathList G R l)
    {l' : List V} (hl' : IsPathList G R l') (hd : l'.Disjoint l) {u t : V} (hu : u ∈ l')
    (ht : t ∈ l') (htA : φ.pt t ∈ A₁ \ {p, q}) :
    φ.pt u ∉ Surface.inner F₂ ∪ F₂ := by
  intro hu2
  by_cases h2 : 2 ≤ l'.length
  · have hY := (φ.isCompact_isConnected_pathImage hl' h2).2.isPreconnected
    have hYc : Disjoint (φ.pathImage l') (φ.pathImage l) := φ.disjoint_pathImage hl' hl hd
    have hsub := hθ.side_of_arc hY ((φ.pathImage_subset_U hl').trans hUF) hYc
      (φ.pt_mem_pathImage hl' h2 ht) htA
    have hu1 := hsub (φ.pt_mem_pathImage hl' h2 hu)
    have huc := hθ.closedInner_inter ⟨hu1, hu2⟩
    exact hd hu (φ.mem_of_pt_mem_pathImage hl (hl'.2.2 u hu) huc)
  · have hlen : l'.length = 1 := by
      have := List.length_pos_of_mem hu
      omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    rw [List.mem_singleton] at hu ht
    subst hu ht
    have hout := hθ.symm.open_arc_subset_outer htA
    rcases hu2 with h | h
    · exact Set.disjoint_left.mp hθ.parts₂.disjoint h hout
    · exact hout.1 h

/-- The vertices of a triangle whose face lies in the inner domain of `F₂` are drawn in the closed
side of `F₂`. -/
theorem pt_mem_side_of_tri {F₂ : Set ℂ} (J : IsJordanParts F₂) {x y z : V}
    (hT : IsTriangleOn G R x y z)
    (h : Surface.inner (φ.cycleImage [x, y, z]) ⊆ Surface.inner F₂) {v : V} (hv : v ∈ [x, y, z]) :
    φ.pt v ∈ Surface.inner F₂ ∪ F₂ := by
  have JT := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
  rw [← J.closure_inner]
  refine closure_mono h ?_
  rw [JT.closure_inner]
  right
  obtain ⟨hx, hy, hz, hxy, hyz, hxz⟩ := hT
  rw [φ.cycleImage_three]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact Or.inl (Or.inl (φ.isLine _ hx _ hy hxy).left_mem)
  · exact Or.inl (Or.inr (φ.isLine _ hy _ hz hyz).left_mem)
  · exact Or.inr (φ.isLine _ hz _ hx hxz.symm).left_mem


/-- The image of a path list with at least two vertices is path-connected: it is an arc. -/
theorem isPathConnected_pathImage {l' : List V} (h : IsPathList G R l') (h2 : 2 ≤ l'.length) :
    IsPathConnected (φ.pathImage l') := by
  obtain ⟨x, l'', rfl⟩ : ∃ x l'', l' = x :: l'' := by
    cases l' with
    | nil => simp at h2
    | cons x l'' => exact ⟨x, l'', rfl⟩
  have hl'' : l'' ≠ [] := by rintro rfl; simp at h2
  obtain ⟨a, ha, hra, -, -⟩ := (φ.isLine_pathImage hl'' h).exists_arc
  have he : range a = (fun r : ℝ => a (Set.projIcc 0 1 zero_le_one r)) '' Icc 0 1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, by simp only [Set.projIcc_val]⟩
    · rintro ⟨r, -, rfl⟩
      exact ⟨_, rfl⟩
  rw [← hra, he]
  exact ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩).image
    (ha.1.comp continuous_projIcc)

end PlaneEmbedding

end GraphMinor.HP25
