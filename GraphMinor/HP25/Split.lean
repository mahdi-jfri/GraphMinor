module

public import GraphMinor.HP25.SplitTools
import GraphMinor.HP25.Prop23
import GraphMinor.Surface.ChartCells
import GraphMinor.Surface.SurfaceGraph

/-!
# Splitting a rib along an induced path

Let `R` be a rib with frame `C = a A b B` (up to rotation), and let `P = a m b` be an induced path
of the rib between the non-consecutive frame vertices `a`, `b`, with no inner vertex on `C`. Then
`P` cuts the rib into two ribs: one with frame `a A b m⁻¹` and one with frame `b B a m`, which share
exactly the vertices of `P` and have no edge between their other vertices
(`IsRibEmbedding.split`).

This is the step of the proof of Proposition 3.6 (page 12): "Considering a plane embedding of the
latter, the path $P$ separates $R$ into two planar graphs whose outer faces are bounded by the two
cycles distinct from $C$ and induced by $C$ and $P$, all their faces are faces of $R$ and hence
triangles, and all their triangles are triangles of $R$ and hence faces: those two planar graphs
are ribs." It is also the end of the proof of Proposition 3.4, with `P` an edge.

The proof. The images of `C`, of the two arcs of `C` between `a` and `b`, and of `P` form a theta
curve (`Surface.IsTheta`). The vertices drawn in the closed inner domain of one side form one part.
A connected set inside the image of `C` that misses the image of `P` stays on one side
(`IsTheta.sep`). Since `P` is induced, an edge between two vertices of a part is drawn inside that
part. Then `PlaneEmbedding.isRibEmbedding_restrict` gives the faces of a rib.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-! ### Lists -/

theorem IsPathList.reverse {l : List V} (h : IsPathList G R l) : IsPathList G R l.reverse :=
  ⟨List.nodup_reverse.mpr h.1, List.isChain_reverse.mpr (h.2.1.imp fun _ _ h => h.symm),
    fun x hx => h.2.2 x (List.mem_reverse.mp hx)⟩

/-- Two paths `x X y` and `y Y x` with disjoint inner vertices form a cycle `x X y Y`. -/
theorem isCycleList_of_two_paths {x y : V} {X Y : List V} (h₁ : IsPathList G R (x :: X ++ [y]))
    (h₂ : IsPathList G R (y :: Y ++ [x])) (hdisj : ∀ v ∈ X, v ∉ Y) (hxy : x ≠ y)
    (h3 : X ≠ [] ∨ Y ≠ []) : IsCycleList G (x :: X ++ y :: Y) := by
  have hn₁ := h₁.1
  have hn₂ := h₂.1
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hn₁ hn₂
  have hxX : x ∉ X := fun h => hn₁.1 (List.mem_append_left _ h)
  have hyX : y ∉ X := fun h => hn₁.2.2.2 y h y (by simp) rfl
  have hyY : y ∉ Y := fun h => hn₂.1 (List.mem_append_left _ h)
  have hxY : x ∉ Y := fun h => hn₂.2.2.2 x h x (by simp) rfl
  refine ⟨?_, ?_, ?_⟩
  · rcases h3 with h | h
    · have := List.length_pos_of_ne_nil h; simp; omega
    · have := List.length_pos_of_ne_nil h; simp; omega
  · rw [List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons]
    refine ⟨fun h => ?_, hn₁.2.1, ⟨hyY, hn₂.2.1⟩, fun u hu v hv huv => ?_⟩
    · rcases List.mem_append.mp h with h | h
      · exact hxX h
      · rcases List.mem_cons.mp h with h | h
        · exact hxy h
        · exact hxY h
    · subst huv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hyX hu
      · exact hdisj u hu hv
  · intro p hp
    have hz := zip_rotate_one_cons x (X ++ y :: Y)
    rw [List.cons_append] at hp
    rw [hz] at hp
    have hch : (x :: (X ++ y :: Y) ++ [x]).IsChain G.Adj := by
      have e : x :: (X ++ y :: Y) ++ [x] = (x :: X) ++ [y] ++ (Y ++ [x]) := by simp
      rw [e]
      refine List.IsChain.append_overlap (by simpa using h₁.2.1) (by simpa using h₂.2.1) (by simp)
    exact isChain_iff_zip.mp hch p hp

namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

/-- The image of the cycle `x X y Y` is the union of the images of the paths `x X y` and
`y Y x`. -/
theorem cycleImage_two_paths (x y : V) (X Y : List V) :
    φ.cycleImage (x :: X ++ y :: Y) = φ.pathImage (x :: X ++ [y]) ∪ φ.pathImage (y :: Y ++ [x]) := by
  rw [List.cons_append, cycleImage_cons]
  have e : x :: (X ++ y :: Y) ++ [x] = (x :: X) ++ y :: (Y ++ [x]) := by simp
  rw [e, pathImage_append]
  simp

end PlaneEmbedding

theorem IsPathList.left_of_append {l₁ l₂ : List V} (h : IsPathList G R (l₁ ++ l₂)) :
    IsPathList G R l₁ :=
  ⟨h.1.sublist (List.sublist_append_left _ _), h.2.1.left_of_append,
    fun x hx => h.2.2 x (List.mem_append_left _ hx)⟩

namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

/-- The line of an edge of a list lies on the image of the list. -/
theorem line_subset_pathImage {l : List V} {u v : V} (h : IsListEdge l u v) :
    φ.line u v ⊆ φ.pathImage l := by
  obtain ⟨p, hp, he⟩ := h
  intro z hz
  simp only [pathImage, mem_iUnion]
  refine ⟨p, hp, ?_⟩
  rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rwa [← e1, ← e2]
  · rwa [← e1, ← e2, φ.line_comm]

/-- If two path lists share only the vertices `a` and `b`, and `ab` is not an edge of the first,
then their images meet only at the points of `a` and `b`. -/
theorem pathImage_inter_subset_pair {l₁ l₂ : List V} (h₁ : IsPathList G R l₁)
    (h₂ : IsPathList G R l₂) {a b : V} (hcom : ∀ v ∈ l₁, v ∈ l₂ → v = a ∨ v = b)
    (hab : ¬ IsListEdge l₁ a b) : φ.pathImage l₁ ∩ φ.pathImage l₂ ⊆ {φ.pt a, φ.pt b} := by
  refine (φ.pathImage_inter_pathImage h₁ h₂ fun p hp q hq he => ?_).trans ?_
  · have hp1 : p.1 ∈ l₁ := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ l₁ := List.mem_of_mem_tail (List.of_mem_zip hp).2
    have hq1 : q.1 ∈ l₂ := (List.of_mem_zip hq).1
    have hq2 : q.2 ∈ l₂ := List.mem_of_mem_tail (List.of_mem_zip hq).2
    have hadj : G.Adj p.1 p.2 := isChain_iff_zip.mp h₁.2.1 p hp
    have hin : ∀ w, w ∈ s(p.1, p.2) → w ∈ l₂ := fun w hw => by
      rw [he] at hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hq1
      · exact hq2
    rcases hcom _ hp1 (hin _ (Sym2.mem_mk_left _ _)) with h1 | h1 <;>
      rcases hcom _ hp2 (hin _ (Sym2.mem_mk_right _ _)) with h2 | h2
    · exact hadj.ne (h1.trans h2.symm)
    · exact hab ⟨p, hp, by rw [h1, h2]⟩
    · exact hab ⟨p, hp, by rw [h1, h2, Sym2.eq_swap]⟩
    · exact hadj.ne (h1.trans h2.symm)
  · rintro _ ⟨v, ⟨hv1, hv2⟩, rfl⟩
    rcases hcom v hv1 hv2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

variable {φ}

/-- Let a theta curve have the image of a path list `l` as its middle arc, inside the closed inner
domain of `F`, which holds the drawing. Then the line of an edge that is not a chord of `l` stays in
the closed inner domain of one side. -/
theorem line_subset_side {F F₁ F₂ A₁ A₂ : Set ℂ} {l : List V} {a b : V}
    (hθ : IsTheta F F₁ F₂ A₁ A₂ (φ.pathImage l) (φ.pt a) (φ.pt b)) (hUF : φ.U ⊆ inner F ∪ F)
    (hl : IsPathList G R l) {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v)
    (hb : ¬ (u ∈ l ∧ v ∈ l)) :
    φ.line u v ⊆ inner F₁ ∪ F₁ ∨ φ.line u v ⊆ inner F₂ ∪ F₂ := by
  have hL := φ.isLine u hu v hv huv
  have hne : ∀ p ∈ l.zip l.tail, s(u, v) ≠ s(p.1, p.2) := fun p hp he => hb (by
    have h1 := (List.of_mem_zip hp).1
    have h2 := List.mem_of_mem_tail (List.of_mem_zip hp).2
    rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ h1, e2 ▸ h2⟩
    · exact ⟨e1 ▸ h2, e2 ▸ h1⟩)
  have hY : Disjoint (φ.line u v \ {φ.pt u, φ.pt v}) (φ.pathImage l) := by
    refine Set.disjoint_left.mpr fun z hz hzl => hz.2 ?_
    obtain ⟨w, ⟨hw1, -⟩, rfl⟩ := φ.line_inter_pathImage_sub hu hv huv hl hne ⟨hz.1, hzl⟩
    rcases hw1 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hYF : φ.line u v \ {φ.pt u, φ.pt v} ⊆ inner F ∪ F :=
    fun z hz => hUF (φ.line_subset_U hu hv huv hz.1)
  rcases hθ.sep hL.isPreconnected_diff hYF hY with h | h
  · exact Or.inl (hL.subset_closure_diff.trans
      (closure_minimal h (IsTheta.isClosed_closedInner hθ.parts₁)))
  · exact Or.inr (hL.subset_closure_diff.trans
      (closure_minimal h (IsTheta.isClosed_closedInner hθ.parts₂)))

/-- One side of a theta curve whose middle arc is the image of an induced path list `l`: the
vertices drawn in the closed inner domain of the side `F₁` form a rib, whose frame is a cycle `C₁`
with image `F₁`. -/
theorem side_rib {C : List V} (hφ : φ.IsRibEmbedding C) {F F₁ F₂ A₁ A₂ : Set ℂ} {l : List V}
    {a b : V} (hθ : IsTheta F F₁ F₂ A₁ A₂ (φ.pathImage l) (φ.pt a) (φ.pt b))
    (hUF : φ.U ⊆ inner F ∪ F) (hl : IsPathList G R l)
    (hind : ∀ u ∈ l, ∀ v ∈ l, G.Adj u v → IsListEdge l u v)
    {C₁ : List V} (hC₁ : IsCycleList G C₁) (hC₁R : ∀ x ∈ C₁, x ∈ R)
    (hF₁ : φ.cycleImage C₁ = F₁) :
    IsRibOn G {v | v ∈ R ∧ φ.pt v ∈ inner F₁ ∪ F₁} C₁ := by
  set R₁ := {v | v ∈ R ∧ φ.pt v ∈ inner F₁ ∪ F₁} with hR₁_def
  have hR₁ : R₁ ⊆ R := fun v hv => hv.1
  have hC₁R₁ : ∀ x ∈ C₁, x ∈ R₁ := fun x hx =>
    ⟨hC₁R x hx, Or.inr (hF₁ ▸ φ.pt_mem_cycleImage hC₁ hC₁R hx)⟩
  have hc : φ.pathImage l ⊆ F₁ := fun z hz => by rw [hθ.eq₁]; exact Or.inr hz
  refine ⟨hC₁, hC₁R₁, φ.restrict hR₁, ?_⟩
  refine φ.isRibEmbedding_restrict hφ hC₁ hR₁ hC₁R₁ (fun v hv h => ⟨hv, hF₁ ▸ h⟩)
    (fun v hv => hF₁ ▸ hv.2) (fun u hu v hv huv => ?_) (fun z hz hzi => ?_)
  · rw [hF₁]
    by_cases hb : u ∈ l ∧ v ∈ l
    · exact (φ.line_subset_pathImage (hind u hb.1 v hb.2 huv)).trans
        (hc.trans subset_union_right)
    · rcases line_subset_side hθ hUF hl hu.1 hv.1 huv hb with h | h
      · exact h
      · exfalso
        have hL := φ.isLine u hu.1 v hv.1 huv
        -- an end of the edge off `l` would be drawn on both sides, so on the image of `l`
        obtain ⟨w, hw, hwl, hwL⟩ : ∃ w ∈ R₁, w ∉ l ∧ φ.pt w ∈ φ.line u v := by
          by_cases hul : u ∈ l
          · exact ⟨v, hv, fun h => hb ⟨hul, h⟩, hL.right_mem⟩
          · exact ⟨u, hu, hul, hL.left_mem⟩
        exact hwl (φ.mem_of_pt_mem_pathImage hl hw.1 (hθ.closedInner_inter ⟨hw.2, h hwL⟩))
  · rw [hF₁] at hzi
    rcases hz with ⟨v, hv, rfl⟩ | hz
    · exact Or.inl ⟨v, ⟨hv, Or.inl hzi⟩, rfl⟩
    · simp only [mem_iUnion] at hz
      obtain ⟨u, hu, v, hv, huv, hz⟩ := hz
      by_cases hb : u ∈ l ∧ v ∈ l
      · exact absurd (hc (φ.line_subset_pathImage (hind u hb.1 v hb.2 huv) hz)) hzi.1
      · have hL := φ.isLine u hu v hv huv
        rcases line_subset_side hθ hUF hl hu hv huv hb with h | h
        · refine Or.inr ?_
          simp only [mem_iUnion]
          exact ⟨u, ⟨hu, h hL.left_mem⟩, v, ⟨hv, h hL.right_mem⟩, huv, hz⟩
        · exact absurd (hc (hθ.closedInner_inter ⟨Or.inl hzi, h hz⟩)) hzi.1

/-- **Splitting a rib along an induced path.** Let `C` be, up to rotation, `a A b B`, with `a`, `b`
not consecutive on `C`, and let `a m b` be an induced path of the rib with no inner vertex on `C`.
Then the rib splits into two ribs on vertex sets `R₁` and `R₂`, with frames `a A b m⁻¹` and
`b B a m`, which meet exactly in the vertices of the path and have no edge between `R₁ \ R₂` and
`R₂ \ R₁`. -/
theorem IsRibEmbedding.split {C : List V} (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {k : ℕ} {a b : V} {A B m : List V}
    (hrot : C.rotate k = a :: A ++ b :: B) (hab : ¬ IsCycleEdge C a b)
    (hl : IsPathList G R (a :: m ++ [b])) (hmC : ∀ v ∈ m, v ∉ C)
    (hind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], G.Adj u v →
      IsListEdge (a :: m ++ [b]) u v) :
    ∃ R₁ R₂ : Set V, R₁ ∪ R₂ = R ∧ R₁ ∩ R₂ = {v | v ∈ a :: m ++ [b]} ∧
      (∀ u ∈ R₁, ∀ v ∈ R₂, G.Adj u v → u ∈ R₂ ∨ v ∈ R₁) ∧
      IsRibOn G R₁ (a :: A ++ b :: m.reverse) ∧ IsRibOn G R₂ (b :: B ++ a :: m) := by
  classical
  set l := a :: m ++ [b] with hl_def
  set C' := a :: A ++ b :: B with hC'_def
  have hC' : IsCycleList G C' := hrot ▸ hC.rotate k
  have hmemC : ∀ v, v ∈ C' ↔ v ∈ C := fun v => by rw [← hrot]; exact List.mem_rotate
  have hC'R : ∀ v ∈ C', v ∈ R := fun v hv => hR v ((hmemC v).mp hv)
  have habC' : ¬ IsCycleEdge C' a b := by rw [← hrot, isCycleEdge_rotate]; exact hab
  -- the shape of `C'`
  have hnd := hC'.2.1
  rw [hC'_def, List.cons_append, List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd
  have haA : a ∉ A := fun h => hnd.1 (List.mem_append_left _ h)
  have hab' : a ≠ b := fun h => hnd.1 (List.mem_append_right _ (h ▸ List.mem_cons_self))
  have hAB : ∀ v ∈ A, v ∉ B := fun v hv hvB => hnd.2.2.2 v hv v (List.mem_cons_of_mem _ hvB) rfl
  have hbB : b ∉ B := hnd.2.2.1.1
  -- the two arcs of `C'` between `a` and `b`
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
  -- common vertices
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
  -- the two new cycles
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
  -- the theta curve formed by the images of `C'`, of its two arcs and of `l`
  have hl2 : 2 ≤ l.length := by simp [hl_def]
  have hFC : φ.cycleImage C = φ.cycleImage C' := by rw [← φ.cycleImage_rotate C k, hrot]
  have J : IsJordanParts (φ.cycleImage C') := isJordanParts (φ.isOArc_cycleImage hC' hC'R).some
  have hUF : φ.U ⊆ inner (φ.cycleImage C') ∪ φ.cycleImage C' := by
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
  have hθ : IsTheta (φ.cycleImage C') (φ.cycleImage (a :: A ++ b :: m.reverse))
      (φ.cycleImage (b :: B ++ a :: m)) (φ.pathImage (a :: A ++ [b]))
      (φ.pathImage (b :: B ++ [a])) (φ.pathImage l) (φ.pt a) (φ.pt b) := by
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
    · -- the image of `l` meets the image of `C'` only at the points of `a` and `b`
      rintro z ⟨hzc, hzab⟩
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
  have hcF₁ : φ.pathImage l ⊆ φ.cycleImage (a :: A ++ b :: m.reverse) := fun z hz => by
    rw [hθ.eq₁]; exact Or.inr hz
  have hcF₂ : φ.pathImage l ⊆ φ.cycleImage (b :: B ++ a :: m) := fun z hz => by
    rw [hθ.eq₂]; exact Or.inr hz
  refine ⟨_, _, ?_, ?_, ?_, side_rib hφ hθ hUF hl hind hC₁ hC₁R rfl,
    side_rib hφ hθ.symm hUF hl hind hC₂ hC₂R rfl⟩
  · ext v
    refine ⟨fun h => h.elim (·.1) (·.1), fun hv => ?_⟩
    rcases hθ.closedInner_subset (hUF (φ.pt_mem_U hv)) with h | h
    · exact Or.inl ⟨hv, h⟩
    · exact Or.inr ⟨hv, h⟩
  · ext v
    refine ⟨fun ⟨⟨hv, h1⟩, _, h2⟩ =>
      φ.mem_of_pt_mem_pathImage hl hv (hθ.closedInner_inter ⟨h1, h2⟩), fun hv => ?_⟩
    have hvR := hl.2.2 v hv
    have hc := φ.pt_mem_pathImage hl hl2 hv
    exact ⟨⟨hvR, Or.inr (hcF₁ hc)⟩, ⟨hvR, Or.inr (hcF₂ hc)⟩⟩
  · intro u hu v hv huv
    have hL := φ.isLine u hu.1 v hv.1 huv
    by_cases hb : u ∈ l ∧ v ∈ l
    · exact Or.inl ⟨hu.1, Or.inr (hcF₂ (φ.pt_mem_pathImage hl hl2 hb.1))⟩
    · rcases line_subset_side hθ hUF hl hu.1 hv.1 huv hb with h | h
      · exact Or.inr ⟨hv.1, h hL.right_mem⟩
      · exact Or.inl ⟨hu.1, h hL.left_mem⟩

end PlaneEmbedding

end GraphMinor.HP25
