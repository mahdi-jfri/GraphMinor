module

public import GraphMinor.Compute.Algorithm77Step76

/-!
# Graph Minors XIII, (7.7), Step (7.5): External Stars to Disjoint Far `H`-Paths

This file implements Step (7.5) of the algorithm of Graph Minors XIII, (7.7) (page 91):
given a wall `W : WallOfHeight h G` (`2 ≤ h`, `Even h`, `W.IsValid`) and `k = p.choose 2`
external `(l, 2 * r)`-stars over `W` with distinct centers `centers a ∉ W.vertexFinset`, where
`l = 2 * k ^ 2 - k + 3`, the induction on `s = 0, ..., k` constructs `k` mutually vertex-disjoint
`H`-paths `Q_1, ..., Q_k` whose `2k` ends are mutually at brick distance `≥ r` in `W`, yielding a
valid `Alg74Input p r`.

The mathematical counterparts are `GM13.lemma_7_5_claim` and `GM13.theorem_7_5_of_theorem_7_4`
in `GraphMinor/GM13/Section7Five.lean`.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor
open GraphMinor.GM09

/-! ### Section 1: Symmetry and Triangle Inequality for `W.brickDist` -/

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

/-- A valid `W : WallOfHeight h G` (`2 ≤ h`, `Even h`) induces a Figure-1 `GM13.DrawnWall` whose
plane wall distance `D.dist u.1 v.1` agrees with `W.brickDist u v` on `W.vertexFinset`. -/
theorem exists_drawnWall_dist_eq_brickDist (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    ∃ D : GM13.DrawnWall ℕ (ℕ × ℕ × ℕ),
      D.IsFigure1 ∧
      ∀ u ∈ W.vertexFinset, ∀ v ∈ W.vertexFinset, D.dist u.1 v.1 = W.brickDist u v := by
  let H := W.toGMWall h2 he hW
  obtain ⟨Γ, hΓ⟩ := H.exists_isFigure1CoordDrawing
  let D : GM13.DrawnWall ℕ (ℕ × ℕ × ℕ) :=
    { H with
      drawingU := Γ.drawing.U
      vertexPoint := GM13.ptV Γ
      vertexPoint_mem := fun x hx => Γ.drawing.V_subset_U (GM13.ptV_mem_V Γ hx)
      vertexPoint_injOn := GM13.ptV_injOn Γ }
  have hDF : D.IsFigure1 :=
    ⟨Homeomorph.refl _, Γ, hΓ, by simp [D], fun x hx => GM13.ptV_of_mem Γ hx⟩
  refine ⟨D, hDF, fun u hu v hv => ?_⟩
  by_cases huv : u = v
  · subst huv
    change GM13.planeWallDist Γ.drawing.U (GM13.ptV Γ u.1) (GM13.ptV Γ u.1) = _
    simp [GM13.planeWallDist_self, brickDist]
  · have hH_height : H.height = h := rfl
    have hD := GM13.drawnOnCells_fig1 hΓ (by omega) H.even_height
    change GM13.planeWallDist Γ.drawing.U (GM13.ptV Γ u.1) (GM13.ptV Γ v.1) = _
    rw [hΓ.drawing_U_eq, GM13.fig1WallSet_eq_cellSet]
    have h1 := drawnOnCells_planeWallDist_eq_fig1CellBrickDist (by omega) hD le_rfl
      (W.vertCell_mem_fig1WallCells h2 he hW hu)
      (W.vertCell_mem_fig1WallCells h2 he hW hv)
      (W.val_mem_toGMWall_elemV_vertCell h2 he hW hu)
      (W.val_mem_toGMWall_elemV_vertCell h2 he hW hv)
      (fun e => huv (Fin.ext e))
    have hU : GM13.fig1WallCells H.height = (GM13.CellWall.fig1 (by omega) H.even_height).𝒰 := rfl
    have hbrick : W.brickDist u v = fig1CellBrickDist h (W.vertCell u) (W.vertCell v) := by
      simp [brickDist, huv]
    rw [hU, h1, hH_height, ← hbrick]

/-- Symmetry of `W.brickDist` on `W.vertexFinset`. -/
theorem brickDist_comm_of_mem (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {u v : Fin n} (hu : u ∈ W.vertexFinset) (hv : v ∈ W.vertexFinset) :
    W.brickDist u v = W.brickDist v u := by
  obtain ⟨D, _, hdist⟩ := W.exists_drawnWall_dist_eq_brickDist h2 he hW
  rw [← hdist u hu v hv, ← hdist v hv u hu, D.dist_comm]

/-- Triangle inequality for `W.brickDist` on `W.vertexFinset` (`GM13.DrawnWall.dist_triangle` via
`GM13.DrawnWall.IsFigure1.isThin`). -/
theorem brickDist_triangle (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {u v w : Fin n} (hu : u ∈ W.vertexFinset) (hv : v ∈ W.vertexFinset) (hw : w ∈ W.vertexFinset) :
    W.brickDist u w ≤ W.brickDist u v + W.brickDist v w := by
  obtain ⟨D, hDF, hdist⟩ := W.exists_drawnWall_dist_eq_brickDist h2 he hW
  rw [← hdist u hu w hw, ← hdist u hu v hv, ← hdist v hv w hw]
  exact D.dist_triangle hDF.isThin u.1 v.1 w.1

/-! ### Section 2: External Star Ray Lists (`IsStarRayList`) and Avoiding a Center -/

/-- A list of rays `rs : List (List (Fin n))` forming an external `(|rs|, m)`-star over `W` with
center `c ∉ W.vertexFinset`. -/
structure IsStarRayList (m : ℕ) (c : Fin n) (rs : List (List (Fin n))) : Prop where
  center_not_mem : c ∉ W.vertexFinset
  rays_valid : ∀ P ∈ rs, W.IsStarRay c P
  rays_meet : rs.Pairwise (fun P₁ P₂ => ∀ v, v ∈ P₁ → v ∈ P₂ → v = c)
  ends_dist : rs.Pairwise (fun P₁ P₂ => ∀ u v,
    P₁.getLast? = some u → P₂.getLast? = some v → m ≤ W.brickDist u v)

/-- Convert a `Fin l`-indexed family of rays into a `List (List (Fin n))` of length `l`. -/
def starRayListOfFin {l : ℕ} (rays : Fin l → List (Fin n)) : List (List (Fin n)) :=
  (List.finRange l).map rays

theorem length_starRayListOfFin {l : ℕ} (rays : Fin l → List (Fin n)) :
    (starRayListOfFin rays).length = l := by
  simp [starRayListOfFin]

theorem isStarRayList_starRayListOfFin {l m : ℕ} {c : Fin n} {rays : Fin l → List (Fin n)}
    (hc : c ∉ W.vertexFinset)
    (hrays : ∀ i : Fin l, W.IsStarRay c (rays i))
    (hmeet : ∀ i j : Fin l, i ≠ j → ∀ v, v ∈ rays i → v ∈ rays j → v = c)
    (hdist : ∀ i j : Fin l, i ≠ j → ∀ u v,
      (rays i).getLast? = some u → (rays j).getLast? = some v → m ≤ W.brickDist u v) :
    W.IsStarRayList m c (starRayListOfFin rays) where
  center_not_mem := hc
  rays_valid := by
    intro P hP
    rw [starRayListOfFin, List.mem_map] at hP
    rcases hP with ⟨i, _, rfl⟩
    exact hrays i
  rays_meet := by
    rw [starRayListOfFin, List.pairwise_map]
    exact (List.nodup_finRange l).imp fun hij => hmeet _ _ hij
  ends_dist := by
    rw [starRayListOfFin, List.pairwise_map]
    exact (List.nodup_finRange l).imp fun hij => hdist _ _ hij

/-- Filter a star's ray list to keep only rays that avoid vertex `w`. -/
def filterAvoidVertex (w : Fin n) (rs : List (List (Fin n))) : List (List (Fin n)) :=
  rs.filter (fun P => decide (w ∉ P))

theorem mem_filterAvoidVertex_iff {w : Fin n} {rs : List (List (Fin n))} {P : List (Fin n)} :
    P ∈ filterAvoidVertex w rs ↔ P ∈ rs ∧ w ∉ P := by
  simp [filterAvoidVertex]

theorem IsStarRayList.filterAvoidVertex {W : WallOfHeight h G} {m : ℕ} {c : Fin n}
    {rs : List (List (Fin n))} (hrs : W.IsStarRayList m c rs) (w : Fin n) :
    W.IsStarRayList m c (filterAvoidVertex w rs) where
  center_not_mem := hrs.center_not_mem
  rays_valid _ hP := hrs.rays_valid _ (mem_filterAvoidVertex_iff.mp hP).1
  rays_meet := hrs.rays_meet.filter _
  ends_dist := hrs.ends_dist.filter _

/-- For any list `rs` with `rs.Pairwise R` where at most one element can fail predicate `p`,
`(rs.filter p).length ≥ rs.length - 1`. -/
theorem length_filter_ge_sub_one {α : Type*} {R : α → α → Prop} {rs : List α}
    (hpw : rs.Pairwise R) (p : α → Bool)
    (hatmost : ∀ x ∈ rs, ∀ y ∈ rs, R x y → p x = false → p y = false → False) :
    rs.length - 1 ≤ (rs.filter p).length := by
  induction rs with
  | nil => simp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hpw
    cases hx : p x
    · have hall : ∀ y ∈ xs, p y = true := by
        intro y hy
        cases hy_p : p y
        · exact False.elim (hatmost x List.mem_cons_self y (List.mem_cons_of_mem x hy)
            (hpw.1 y hy) hx hy_p)
        · rfl
      simp [hx, List.filter_eq_self.mpr hall]
    · have ih' := ih hpw.2 (fun a ha b hb =>
        hatmost a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))
      simp only [List.filter_cons, hx, ↓reduceIte, List.length_cons]
      omega

/-- Filtering out rays containing `w ≠ c` removes at most one ray (`GM13.exists_substar_avoiding_vertex`). -/
theorem IsStarRayList.length_filterAvoidVertex_ge {W : WallOfHeight h G} {m : ℕ} {c w : Fin n}
    {rs : List (List (Fin n))} (hrs : W.IsStarRayList m c rs) (hwc : w ≠ c) :
    rs.length - 1 ≤ (WallOfHeight.filterAvoidVertex w rs).length := by
  apply length_filter_ge_sub_one hrs.rays_meet
  intro P₁ _ P₂ _ h12 hp1 hp2
  simp only [decide_eq_false_iff_not, Decidable.not_not] at hp1 hp2
  exact hwc (h12 w hp1 hp2)

theorem IsStarRayList.nodup {W : WallOfHeight h G} {m : ℕ} {c : Fin n}
    {rs : List (List (Fin n))} (hrs : W.IsStarRayList m c rs) : rs.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  refine hrs.rays_meet.imp_of_mem fun {P₁ P₂} hP₁ _ h12 heq => ?_
  subst heq
  obtain ⟨hne, _, _, _, _, hlast, _, _⟩ := hrs.rays_valid P₁ hP₁
  exact hrs.center_not_mem (h12 _ (List.getLast_mem hne) (List.getLast_mem hne) ▸ hlast)

theorem IsStarRayList.eq_center_of_ne {W : WallOfHeight h G} {m : ℕ} {c : Fin n}
    {rs : List (List (Fin n))} (hrs : W.IsStarRayList m c rs) {P₁ P₂ : List (Fin n)}
    (hP₁ : P₁ ∈ rs) (hP₂ : P₂ ∈ rs) (hne : P₁ ≠ P₂)
    {v : Fin n} (hv₁ : v ∈ P₁) (hv₂ : v ∈ P₂) : v = c := by
  rcases List.mem_iff_getElem.mp hP₁ with ⟨i₁, hi₁, rfl⟩
  rcases List.mem_iff_getElem.mp hP₂ with ⟨i₂, hi₂, rfl⟩
  have hij : i₁ ≠ i₂ := fun e => hne (by subst e; rfl)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact List.pairwise_iff_getElem.mp hrs.rays_meet i₁ i₂ hi₁ hi₂ hlt v hv₁ hv₂
  · exact List.pairwise_iff_getElem.mp hrs.rays_meet i₂ i₁ hi₂ hi₁ hgt v hv₂ hv₁

theorem IsStarRayList.brickDist_ge_of_ne {W : WallOfHeight h G} (h2 : 2 ≤ h) (he : Even h)
    (hW : W.IsValid) {m : ℕ} {c : Fin n} {rs : List (List (Fin n))}
    (hrs : W.IsStarRayList m c rs) {P₁ P₂ : List (Fin n)}
    (hP₁ : P₁ ∈ rs) (hP₂ : P₂ ∈ rs) (hne : P₁ ≠ P₂)
    {u₁ u₂ : Fin n} (hu₁ : P₁.getLast? = some u₁) (hu₂ : P₂.getLast? = some u₂) :
    m ≤ W.brickDist u₁ u₂ := by
  rcases List.mem_iff_getElem.mp hP₁ with ⟨i₁, hi₁, rfl⟩
  rcases List.mem_iff_getElem.mp hP₂ with ⟨i₂, hi₂, rfl⟩
  have hij : i₁ ≠ i₂ := fun e => hne (by subst e; rfl)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact List.pairwise_iff_getElem.mp hrs.ends_dist i₁ i₂ hi₁ hi₂ hlt u₁ u₂ hu₁ hu₂
  · have hrev := List.pairwise_iff_getElem.mp hrs.ends_dist i₂ i₁ hi₂ hi₁ hgt u₂ u₁ hu₂ hu₁
    obtain ⟨hne₁, _, _, _, _, hlast₁, _, _⟩ := hrs.rays_valid _ (List.getElem_mem hi₁)
    obtain ⟨hne₂, _, _, _, _, hlast₂, _, _⟩ := hrs.rays_valid _ (List.getElem_mem hi₂)
    rw [List.getLast?_eq_some_getLast hne₁, Option.some.injEq] at hu₁
    rw [List.getLast?_eq_some_getLast hne₂, Option.some.injEq] at hu₂
    rw [W.brickDist_comm_of_mem h2 he hW (hu₁ ▸ hlast₁) (hu₂ ▸ hlast₂)]
    exact hrev

/-! ### Section 3: Far `H`-Path Lists (`IsFarHPathList`) -/

/-- A list `Qs` of mutually vertex-disjoint `H`-paths in `G` whose ends are mutually at brick
distance `≥ r` in `W`. -/
structure IsFarHPathList (r : ℕ) (Qs : List (List (Fin n))) : Prop where
  paths_valid : ∀ Q ∈ Qs, W.IsHPath Q
  paths_disj : Qs.Pairwise List.Disjoint
  ends_self_dist : ∀ Q ∈ Qs, ∀ a b, Q.head? = some a → Q.getLast? = some b → r ≤ W.brickDist a b
  ends_pair_dist : Qs.Pairwise (fun Q₁ Q₂ => ∀ a₁ b₁ a₂ b₂,
    Q₁.head? = some a₁ → Q₁.getLast? = some b₁ →
    Q₂.head? = some a₂ → Q₂.getLast? = some b₂ →
    r ≤ W.brickDist a₁ a₂ ∧ r ≤ W.brickDist a₁ b₂ ∧
    r ≤ W.brickDist b₁ a₂ ∧ r ≤ W.brickDist b₁ b₂)

theorem isFarHPathList_nil (r : ℕ) : W.IsFarHPathList r [] where
  paths_valid := by simp
  paths_disj := List.Pairwise.nil
  ends_self_dist := by simp
  ends_pair_dist := List.Pairwise.nil

theorem hPathEnd_eq_head?_or_getLast? {k : ℕ} (paths : Fin k → List (Fin n))
    (eb : Fin k × Bool) (u : Fin n) (h : hPathEnd paths eb = some u) :
    (eb.2 = false ∧ (paths eb.1).head? = some u) ∨
    (eb.2 = true ∧ (paths eb.1).getLast? = some u) := by
  unfold hPathEnd at h
  cases hlist : paths eb.1 with
  | nil => simp [hlist] at h
  | cons x xs =>
    rw [hlist] at h
    cases hb : eb.2
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      exact Or.inl ⟨rfl, by simp [h]⟩
    · simp only [hb, ↓reduceIte, Option.some.injEq] at h
      refine Or.inr ⟨rfl, ?_⟩
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil x xs), h]

/-- Convert a list `Qs` of length `p.choose 2` satisfying `W.IsFarHPathList r Qs` into a valid
`Alg74Input p r`. -/
def IsFarHPathList.toAlg74Input {W : WallOfHeight h G} {p r : ℕ}
    (hW_valid : 2 ≤ h ∧ Even h ∧ W.IsValid)
    {Qs : List (List (Fin n))} (hQs : W.IsFarHPathList r Qs) (hlen : Qs.length = p.choose 2) :
    Alg74Input p r where
  n := n
  h := h
  G := G
  W := W
  paths := fun i => Qs[i.1]'(by omega)
  hW_valid := hW_valid
  hpaths_valid := fun i => hQs.paths_valid _ (List.getElem_mem _)
  hpaths_disj := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact List.pairwise_iff_getElem.mp hQs.paths_disj i.1 j.1 (by omega) (by omega) hlt
    · exact (List.pairwise_iff_getElem.mp hQs.paths_disj j.1 i.1 (by omega) (by omega) hgt).symm
  hends_dist := by
    intro e₁ e₂ hne u v hu hv
    have h2 := hW_valid.1
    have he := hW_valid.2.1
    have hW := hW_valid.2.2
    let paths : Fin (p.choose 2) → List (Fin n) := fun i => Qs[i.1]'(by omega)
    have hu' := hPathEnd_eq_head?_or_getLast? paths e₁ u hu
    have hv' := hPathEnd_eq_head?_or_getLast? paths e₂ v hv
    obtain ⟨hne₁, _, _, _, hhead₁_mem, hlast₁_mem, _, _⟩ :=
      hQs.paths_valid (paths e₁.1) (List.getElem_mem _)
    obtain ⟨hne₂, _, _, _, hhead₂_mem, hlast₂_mem, _, _⟩ :=
      hQs.paths_valid (paths e₂.1) (List.getElem_mem _)
    have hhead₁ : (paths e₁.1).head? = some ((paths e₁.1).head hne₁) :=
      List.head?_eq_some_head hne₁
    have hlast₁ : (paths e₁.1).getLast? = some ((paths e₁.1).getLast hne₁) :=
      List.getLast?_eq_some_getLast hne₁
    have hhead₂ : (paths e₂.1).head? = some ((paths e₂.1).head hne₂) :=
      List.head?_eq_some_head hne₂
    have hlast₂ : (paths e₂.1).getLast? = some ((paths e₂.1).getLast hne₂) :=
      List.getLast?_eq_some_getLast hne₂
    by_cases hij : e₁.1 = e₂.1
    · have hb_ne : e₁.2 ≠ e₂.2 := fun hb => hne (Prod.ext hij hb)
      rcases hu' with ⟨hb₁, hu_eq⟩ | ⟨hb₁, hu_eq⟩ <;>
        rcases hv' with ⟨hb₂, hv_eq⟩ | ⟨hb₂, hv_eq⟩
      · exact False.elim (hb_ne (hb₁.trans hb₂.symm))
      · rw [← hij] at hv_eq
        exact hQs.ends_self_dist (paths e₁.1) (List.getElem_mem _) u v hu_eq hv_eq
      · rw [← hij] at hv_eq
        have hself := hQs.ends_self_dist (paths e₁.1) (List.getElem_mem _) v u hv_eq hu_eq
        have hu_mem : u ∈ W.vertexFinset := by
          rw [hlast₁, Option.some.injEq] at hu_eq; exact hu_eq ▸ hlast₁_mem
        have hv_mem : v ∈ W.vertexFinset := by
          rw [hhead₁, Option.some.injEq] at hv_eq; exact hv_eq ▸ hhead₁_mem
        rw [W.brickDist_comm_of_mem h2 he hW hu_mem hv_mem]
        exact hself
      · exact False.elim (hb_ne (hb₁.trans hb₂.symm))
    · have hpair : ∀ a₁ b₁ a₂ b₂,
          (paths e₁.1).head? = some a₁ → (paths e₁.1).getLast? = some b₁ →
          (paths e₂.1).head? = some a₂ → (paths e₂.1).getLast? = some b₂ →
          r ≤ W.brickDist a₁ a₂ ∧ r ≤ W.brickDist a₁ b₂ ∧
          r ≤ W.brickDist b₁ a₂ ∧ r ≤ W.brickDist b₁ b₂ := by
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
        · exact List.pairwise_iff_getElem.mp hQs.ends_pair_dist e₁.1.1 e₂.1.1
            (by omega) (by omega) hlt
        · intro a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂
          have hrev := List.pairwise_iff_getElem.mp hQs.ends_pair_dist e₂.1.1 e₁.1.1
            (by omega) (by omega) hgt a₂ b₂ a₁ b₁ ha₂ hb₂ ha₁ hb₁
          have ha₁_mem : a₁ ∈ W.vertexFinset := by
            rw [hhead₁, Option.some.injEq] at ha₁; exact ha₁ ▸ hhead₁_mem
          have hb₁_mem : b₁ ∈ W.vertexFinset := by
            rw [hlast₁, Option.some.injEq] at hb₁; exact hb₁ ▸ hlast₁_mem
          have ha₂_mem : a₂ ∈ W.vertexFinset := by
            rw [hhead₂, Option.some.injEq] at ha₂; exact ha₂ ▸ hhead₂_mem
          have hb₂_mem : b₂ ∈ W.vertexFinset := by
            rw [hlast₂, Option.some.injEq] at hb₂; exact hb₂ ▸ hlast₂_mem
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [W.brickDist_comm_of_mem h2 he hW ha₁_mem ha₂_mem]; exact hrev.1
          · rw [W.brickDist_comm_of_mem h2 he hW ha₁_mem hb₂_mem]; exact hrev.2.2.1
          · rw [W.brickDist_comm_of_mem h2 he hW hb₁_mem ha₂_mem]; exact hrev.2.1
          · rw [W.brickDist_comm_of_mem h2 he hW hb₁_mem hb₂_mem]; exact hrev.2.2.2
      have hp := hpair _ _ _ _ hhead₁ hlast₁ hhead₂ hlast₂
      rcases hu' with ⟨_, hu_eq⟩ | ⟨_, hu_eq⟩ <;>
        rcases hv' with ⟨_, hv_eq⟩ | ⟨_, hv_eq⟩
      · rw [hhead₁, Option.some.injEq] at hu_eq
        rw [hhead₂, Option.some.injEq] at hv_eq
        rw [← hu_eq, ← hv_eq]; exact hp.1
      · rw [hhead₁, Option.some.injEq] at hu_eq
        rw [hlast₂, Option.some.injEq] at hv_eq
        rw [← hu_eq, ← hv_eq]; exact hp.2.1
      · rw [hlast₁, Option.some.injEq] at hu_eq
        rw [hhead₂, Option.some.injEq] at hv_eq
        rw [← hu_eq, ← hv_eq]; exact hp.2.2.1
      · rw [hlast₁, Option.some.injEq] at hu_eq
        rw [hlast₂, Option.some.injEq] at hv_eq
        rw [← hu_eq, ← hv_eq]; exact hp.2.2.2

end WallOfHeight

/-! ### Section 4: Walk Overlap Concatenation, Ray Hit Prefixes, and Subpaths of `Q` -/

section PrefixSuffixHelpers

variable {α : Type*} [DecidableEq α]

theorem getLast_prefixUntil_mem_of_exists (S : Finset α) :
    ∀ {L : List α} (hne : L ≠ []),
      (∃ y ∈ L, y ∈ S) →
      (prefixUntil S L).getLast (prefixUntil_ne_nil S hne) ∈ S
  | [], hne, _ => False.elim (hne rfl)
  | [x], _, ⟨y, hyL, hyS⟩ => by
    simp only [List.mem_singleton] at hyL
    subst hyL
    simpa [prefixUntil] using hyS
  | x :: y :: xs, _, ⟨z, hzL, hzS⟩ => by
    unfold prefixUntil
    split_ifs with hx
    · exact hx
    · rcases List.mem_cons.mp hzL with rfl | hztl
      · exact False.elim (hx hzS)
      · have hne' : prefixUntil S (y :: xs) ≠ [] := prefixUntil_ne_nil S (List.cons_ne_nil y xs)
        rw [List.getLast_cons hne']
        exact getLast_prefixUntil_mem_of_exists S (List.cons_ne_nil y xs) ⟨z, hztl, hzS⟩

theorem eq_getLast_prefixUntil_of_getLast_mem (S : Finset α) :
    ∀ {L : List α} (hne : L ≠ []),
      L.Nodup →
      L.getLast hne ∈ prefixUntil S L →
      L.getLast hne = (prefixUntil S L).getLast (prefixUntil_ne_nil S hne)
  | [], hne, _, _ => False.elim (hne rfl)
  | [x], _, _, _ => by
    unfold prefixUntil
    split_ifs <;> rfl
  | x :: y :: xs, _, hnd, hmem => by
    have hne' : y :: xs ≠ [] := List.cons_ne_nil y xs
    rw [List.getLast_cons hne'] at hmem ⊢
    have hx_ne : (y :: xs).getLast hne' ≠ x := fun e =>
      (List.nodup_cons.mp hnd).1 (e ▸ List.getLast_mem hne')
    unfold prefixUntil at hmem ⊢
    split_ifs at hmem ⊢ with hx
    · simp only [List.mem_singleton] at hmem
      exact False.elim (hx_ne hmem)
    · rcases List.mem_cons.mp hmem with h1 | htail
      · exact False.elim (hx_ne h1)
      · have hne_pref : prefixUntil S (y :: xs) ≠ [] := prefixUntil_ne_nil S hne'
        rw [List.getLast_cons hne_pref]
        exact eq_getLast_prefixUntil_of_getLast_mem S hne' (List.nodup_cons.mp hnd).2 htail

theorem suffixFrom_getElem_eq_drop :
    ∀ {Q : List α} {i : ℕ} (hi : i < Q.length),
      Q.Nodup → suffixFrom Q[i] Q = Q.drop i
  | [], _, hi, _ => by simp at hi
  | x :: xs, 0, _, _ => by
    simp [suffixFrom]
  | x :: xs, i + 1, hi, hnd => by
    have hi' : i < xs.length := by simp at hi; omega
    have hne : x ≠ xs[i] := fun e => (List.nodup_cons.mp hnd).1 (e ▸ List.getElem_mem hi')
    simp only [List.getElem_cons_succ, suffixFrom, hne, ↓reduceIte, List.drop_succ_cons]
    exact suffixFrom_getElem_eq_drop hi' (List.nodup_cons.mp hnd).2

theorem prefixUntil_singleton_getElem_eq_take :
    ∀ {L : List α} {k : ℕ} (hk : k < L.length),
      L.Nodup → prefixUntil {L[k]} L = L.take (k + 1)
  | [], _, hk, _ => by simp at hk
  | x :: xs, 0, _, _ => by
    simp [prefixUntil]
  | x :: xs, k + 1, hk, hnd => by
    have hk' : k < xs.length := by simp at hk; omega
    have hne : x ∉ ({xs[k]} : Finset α) := by
      rw [Finset.mem_singleton]
      exact fun e => (List.nodup_cons.mp hnd).1 (e ▸ List.getElem_mem hk')
    simp only [List.getElem_cons_succ, prefixUntil, hne, ↓reduceIte, List.take_succ_cons]
    exact congrArg (x :: ·) (prefixUntil_singleton_getElem_eq_take hk' (List.nodup_cons.mp hnd).2)

end PrefixSuffixHelpers

/-- Overlap-concatenation of two non-empty paths `L₁` and `L₂` where `L₁.getLast = L₂.head`. -/
def concatOverlap {α : Type*} (L₁ L₂ : List α) : List α :=
  L₁.dropLast ++ L₂

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

theorem concatOverlap_props {L₁ L₂ : List (Fin n)}
    (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ [])
    (heq : L₁.getLast hne₁ = L₂.head hne₂)
    (hnd₁ : L₁.Nodup) (hnd₂ : L₂.Nodup)
    (hdisj : ∀ x, x ∈ L₁.dropLast → x ∈ L₂ → False)
    (hw₁ : IsSimpleWalkList G L₁) (hw₂ : IsSimpleWalkList G L₂) :
    let L := concatOverlap L₁ L₂
    ∃ hne : L ≠ [],
      L.head hne = L₁.head hne₁ ∧
      L.getLast hne = L₂.getLast hne₂ ∧
      L.length = L₁.length + L₂.length - 1 ∧
      L.Nodup ∧
      IsSimpleWalkList G L ∧
      (∀ x, x ∈ L ↔ x ∈ L₁ ∨ x ∈ L₂) ∧
      (∀ a b, (a, b) ∈ L.zip (L.drop 1) → (a, b) ∈ L₁.zip (L₁.drop 1) ∨ (a, b) ∈ L₂.zip (L₂.drop 1)) := by
  have hne : L₁.dropLast ++ L₂ ≠ [] := List.append_ne_nil_of_right_ne_nil _ hne₂
  have hhead : (L₁.dropLast ++ L₂).head hne = L₁.head hne₁ := by
    by_cases hdrop : L₁.dropLast = []
    · cases L₁ with
      | nil => exact False.elim (hne₁ rfl)
      | cons x xs =>
        cases xs with
        | nil =>
          simp only [List.getLast_singleton] at heq
          simpa using heq.symm
        | cons y ys => simp at hdrop
    · rw [List.head_append_of_ne_nil hdrop, List.head_dropLast hdrop]
  have hlast : (L₁.dropLast ++ L₂).getLast hne = L₂.getLast hne₂ :=
    List.getLast_append_of_ne_nil _ hne₂
  have hlen : (L₁.dropLast ++ L₂).length = L₁.length + L₂.length - 1 := by
    have hpos : 1 ≤ L₁.length := List.length_pos_iff.mpr hne₁
    rw [List.length_append, List.length_dropLast]
    omega
  have hnd : (L₁.dropLast ++ L₂).Nodup := by
    have h1 : L₁.dropLast ++ [L₁.getLast hne₁] = L₁ := List.dropLast_append_getLast hne₁
    have hnd_drop : L₁.dropLast.Nodup := (h1 ▸ hnd₁).of_append_left
    exact hnd_drop.append hnd₂ hdisj
  have hw : IsSimpleWalkList G (L₁.dropLast ++ L₂) :=
    isSimpleWalkList_concat_overlap hne₁ hne₂ hw₁ hw₂ heq
  have hmem : ∀ x, x ∈ L₁.dropLast ++ L₂ ↔ x ∈ L₁ ∨ x ∈ L₂ := by
    intro x
    rw [List.mem_append]
    have h1 : L₁.dropLast ++ [L₁.getLast hne₁] = L₁ := List.dropLast_append_getLast hne₁
    constructor
    · rintro (hx1 | hx2)
      · exact Or.inl (List.dropLast_subset L₁ hx1)
      · exact Or.inr hx2
    · rintro (hx1 | hx2)
      · rw [← h1, List.mem_append, List.mem_singleton] at hx1
        rcases hx1 with hx_drop | rfl
        · exact Or.inl hx_drop
        · rw [heq]
          exact Or.inr (List.head_mem hne₂)
      · exact Or.inr hx2
  exact ⟨hne, hhead, hlast, hlen, hnd, hw, hmem, fun a b hab =>
    mem_zip_concat_overlap hne₁ hne₂ heq hab⟩

theorem IsHPath.not_isWallEdge_of_mem_zip {Q : List (Fin n)} (hQ : W.IsHPath Q) :
    ∀ a b, (a, b) ∈ Q.zip (Q.drop 1) → ¬ W.IsWallEdge a b := by
  obtain ⟨hne, hlen2, hnd, _, _, _, hint, hedge2⟩ := hQ
  intro a b hab hedge
  obtain ⟨haW, hbW⟩ := W.mem_vertexFinset_of_isWallEdge hedge
  have haQ : a ∈ Q := (List.of_mem_zip hab).1
  have hbQ : b ∈ Q := List.mem_of_mem_drop (List.of_mem_zip hab).2
  have ha_end : a = Q.head hne ∨ a = Q.getLast hne := by
    rcases mem_cases_head_or_drop_dropLast_or_getLast hne haQ with h1 | h2 | h3
    · exact Or.inl h1
    · exact False.elim (hint a h2 haW)
    · exact Or.inr h3
  have hb_end : b = Q.head hne ∨ b = Q.getLast hne := by
    rcases mem_cases_head_or_drop_dropLast_or_getLast hne hbQ with h1 | h2 | h3
    · exact Or.inl h1
    · exact False.elim (hint b h2 hbW)
    · exact Or.inr h3
  have hab_ne : a ≠ b := ne_of_mem_zip_of_nodup hnd a b hab
  -- If `Q.length = 2`, `(a, b) = (Q.head hne, Q.getLast hne)`
  -- Wait: if `Q.length > 2`, can `(Q.head hne, Q.getLast hne)` or `(Q.getLast hne, Q.head hne)`
  -- occur in `Q.zip (Q.drop 1)` when `Q.Nodup`?
  -- No! Because in a `Nodup` list `Q = x :: y :: rest`, the pairs in `Q.zip (Q.drop 1)` are
  -- `(Q[i], Q[i+1])` for `i + 1 < Q.length`.
  -- If `a ∈ {Q[0], Q[Q.length - 1]}` and `b ∈ {Q[0], Q[Q.length - 1]}` with `a = Q[i]` and `b = Q[i+1]`,
  -- then by `Q.Nodup`, `{i, i + 1} ⊆ {0, Q.length - 1}`, which implies `Q.length = 2`, `i = 0`,
  -- `a = Q[0] = Q.head hne`, and `b = Q[1] = Q.getLast hne`!
  rcases List.mem_iff_getElem.mp hab with ⟨i, hi, hpair⟩
  simp only [List.length_zip, List.length_drop] at hi
  have hi1 : i < Q.length := by omega
  have hi2 : i + 1 < Q.length := by omega
  have ha_get : Q[i] = a := by
    have := Prod.mk.inj hpair
    simpa using this.1
  have hb_get : Q[i + 1] = b := by
    have := Prod.mk.inj hpair
    simpa [List.getElem_drop] using this.2
  have hhead_get : Q.head hne = Q[0]'(by omega) := List.head_eq_getElem_zero hne
  have hlast_get : Q.getLast hne = Q[Q.length - 1]'(by omega) := List.getLast_eq_getElem hne
  rw [← ha_get, hhead_get, hlast_get, hnd.getElem_inj_iff, hnd.getElem_inj_iff] at ha_end
  rw [← hb_get, hhead_get, hlast_get, hnd.getElem_inj_iff, hnd.getElem_inj_iff] at hb_end
  have hlen_eq : Q.length = 2 := by omega
  have hi0 : i = 0 := by omega
  have ha_eq : a = Q.head hne := by rw [← ha_get, hhead_get]; congr 1
  have hb_eq : b = Q.getLast hne := by
    rw [← hb_get, hlast_get]
    congr 1
    omega
  rw [ha_eq, hb_eq] at hedge
  exact hedge2 hlen_eq hedge

/-- Whether a ray `P` meets a path `Q`. -/
def rayMeetsPath (Q P : List (Fin n)) : Bool :=
  P.any (fun x => decide (x ∈ Q))

/-- The prefix of `P.reverse` (starting from the wall endpoint `P.getLast`) up to and including its
first hit on `Q`. -/
def rayHitPrefix (Q P : List (Fin n)) : List (Fin n) :=
  prefixUntil Q.toFinset P.reverse

theorem mem_drop_one_dropLast_of_mem_of_ne_head_of_ne_getLast {α : Type*} {L : List α}
    (hne : L ≠ []) {x : α} (hx : x ∈ L) (hhead : x ≠ L.head hne) (hlast : x ≠ L.getLast hne) :
    x ∈ (L.drop 1).dropLast := by
  rcases mem_cases_head_or_drop_dropLast_or_getLast hne hx with h1 | h2 | h3
  · exact False.elim (hhead h1)
  · exact h2
  · exact False.elim (hlast h3)

/-- Properties of `A = rayHitPrefix Q P` when `W.IsStarRay c P`, `c ∉ Q`, and `rayMeetsPath Q P`. -/
theorem rayHitPrefix_props {c : Fin n} {Q P : List (Fin n)}
    (hP : W.IsStarRay c P) (hcQ : c ∉ Q) (hmeet : rayMeetsPath Q P = true) :
    let A := rayHitPrefix Q P
    ∃ (hneP : P ≠ []) (hneA : A ≠ []),
      A.head hneA = P.getLast hneP ∧
      A.getLast hneA ∈ Q ∧
      A.getLast hneA ∈ P ∧
      c ∉ A ∧
      (∀ x ∈ A, x ∈ P) ∧
      (∀ x ∈ A.dropLast, x ∉ Q) ∧
      (∀ x ∈ A, x ≠ A.head hneA → x ∉ W.vertexFinset) ∧
      (∀ a b, (a, b) ∈ A.zip (A.drop 1) → ¬ W.IsWallEdge a b) ∧
      A.Nodup ∧
      IsSimpleWalkList G A := by
  intro A
  obtain ⟨hneP, hheadP, _, hndP, hwP, _, hintP, hedgeP⟩ := hP
  have hnePrev : P.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hneP
  have hndPrev : P.reverse.Nodup := List.nodup_reverse.mpr hndP
  have hwPrev : IsSimpleWalkList G P.reverse := isSimpleWalkList_reverse hwP
  have hmeet' : ∃ y ∈ P.reverse, y ∈ Q.toFinset := by
    simp only [rayMeetsPath, List.any_eq_true, decide_eq_true_eq] at hmeet
    rcases hmeet with ⟨y, hyP, hyQ⟩
    exact ⟨y, List.mem_reverse.mpr hyP, List.mem_toFinset.mpr hyQ⟩
  have hneA : A ≠ [] := prefixUntil_ne_nil Q.toFinset hnePrev
  have hA_head : A.head hneA = P.getLast hneP := by
    dsimp only [A, rayHitPrefix]
    rw [head_prefixUntil Q.toFinset hnePrev, List.head_reverse]
  have hA_last_Q : A.getLast hneA ∈ Q := by
    have hmem := getLast_prefixUntil_mem_of_exists Q.toFinset hnePrev hmeet'
    exact List.mem_toFinset.mp hmem
  have hA_in_P : ∀ x ∈ A, x ∈ P := fun x hx =>
    List.mem_reverse.mp (mem_of_mem_prefixUntil Q.toFinset hx)
  have hA_last_P : A.getLast hneA ∈ P := hA_in_P _ (List.getLast_mem hneA)
  have hndA : A.Nodup := nodup_prefixUntil Q.toFinset hndPrev
  have hwA : IsSimpleWalkList G A := isSimpleWalkList_prefixUntil Q.toFinset hwPrev
  have hA_dropLast_not_Q : ∀ x ∈ A.dropLast, x ∉ Q := by
    intro x hx hxQ
    have hxA : x ∈ A := List.dropLast_subset A hx
    have hx_eq : x = A.getLast hneA :=
      eq_getLast_of_mem_prefixUntil Q.toFinset hnePrev hxA (List.mem_toFinset.mpr hxQ)
    exact not_getLast_mem_dropLast_of_nodup hneA hndA (hx_eq ▸ hx)
  have hc_not_A : c ∉ A := by
    intro hcA
    have hlast_rev : P.reverse.getLast hnePrev = c := by
      rw [List.getLast_reverse, hheadP]
    have hc_eq : c = A.getLast hneA := by
      rw [← hlast_rev] at hcA ⊢
      exact eq_getLast_prefixUntil_of_getLast_mem Q.toFinset hnePrev hndPrev hcA
    exact hcQ (hc_eq ▸ hA_last_Q)
  have hA_not_W : ∀ x ∈ A, x ≠ A.head hneA → x ∉ W.vertexFinset := by
    intro x hx hx_ne
    have hxP : x ∈ P := hA_in_P x hx
    have hx_ne_c : x ≠ P.head hneP := by
      rw [hheadP]
      rintro rfl
      exact hc_not_A hx
    have hx_ne_u : x ≠ P.getLast hneP := by
      rwa [← hA_head]
    exact hintP x (mem_drop_one_dropLast_of_mem_of_ne_head_of_ne_getLast hneP hxP hx_ne_c hx_ne_u)
  have hA_no_edge : ∀ a b, (a, b) ∈ A.zip (A.drop 1) → ¬ W.IsWallEdge a b := by
    intro a b hab hedge
    obtain ⟨haW, hbW⟩ := W.mem_vertexFinset_of_isWallEdge hedge
    have haA : a ∈ A := (List.of_mem_zip hab).1
    have hbA : b ∈ A := List.mem_of_mem_drop (List.of_mem_zip hab).2
    have ha_head : a = A.head hneA := by
      by_contra hne
      exact hA_not_W a haA hne haW
    have hb_head : b = A.head hneA := by
      by_contra hne
      exact hA_not_W b hbA hne hbW
    exact ne_of_mem_zip_of_nodup hndA a b hab (ha_head.trans hb_head.symm)
  exact ⟨hneP, hneA, hA_head, hA_last_Q, hA_last_P, hc_not_A, hA_in_P, hA_dropLast_not_Q,
    hA_not_W, hA_no_edge, hndA, hwA⟩

/-- Subpath of `Q` between `z₁` and `z₂`, defined via `prefixUntil {z₂} (suffixFrom z₁ Q)`. -/
def subpathBetween (Q : List (Fin n)) (z₁ z₂ : Fin n) : List (Fin n) :=
  prefixUntil {z₂} (suffixFrom z₁ Q)

theorem subpathBetween_eq_drop_take {Q : List (Fin n)} (hndQ : Q.Nodup)
    {i₁ i₂ : ℕ} (hle : i₁ ≤ i₂) (hi₂ : i₂ < Q.length) :
    subpathBetween Q Q[i₁] Q[i₂] = (Q.drop i₁).take (i₂ - i₁ + 1) := by
  have hi₁ : i₁ < Q.length := by omega
  unfold subpathBetween
  rw [suffixFrom_getElem_eq_drop hi₁ hndQ]
  have hnd_drop : (Q.drop i₁).Nodup := hndQ.sublist (List.drop_sublist i₁ Q)
  have hk : i₂ - i₁ < (Q.drop i₁).length := by simp; omega
  have hget : (Q.drop i₁)[i₂ - i₁] = Q[i₂] := by
    rw [List.getElem_drop]
    congr 1
    omega
  rw [← hget]
  exact prefixUntil_singleton_getElem_eq_take hk hnd_drop

theorem subpathBetween_props {Q : List (Fin n)} (hQ : W.IsHPath Q)
    {i₁ i₂ : ℕ} (hlt : i₁ < i₂) (hi₂ : i₂ < Q.length) :
    let B := subpathBetween Q (Q[i₁]'(by omega)) Q[i₂]
    ∃ hneB : B ≠ [],
      B.head hneB = Q[i₁]'(by omega) ∧
      B.getLast hneB = Q[i₂] ∧
      B.length = i₂ - i₁ + 1 ∧
      B.Nodup ∧
      IsSimpleWalkList G B ∧
      (∀ x, x ∈ B ↔ ∃ m, ∃ hm : m < Q.length, i₁ ≤ m ∧ m ≤ i₂ ∧ Q[m] = x) ∧
      (∀ x ∈ B, x ≠ B.head hneB → x ≠ B.getLast hneB → x ∉ W.vertexFinset) ∧
      (∀ a b, (a, b) ∈ B.zip (B.drop 1) → ¬ W.IsWallEdge a b) := by
  intro B
  obtain ⟨hneQ, _, hndQ, hwQ, _, _, hintQ, _⟩ := id hQ
  have hi₁ : i₁ < Q.length := by omega
  have hB_eq : B = (Q.drop i₁).take (i₂ - i₁ + 1) :=
    subpathBetween_eq_drop_take hndQ (by omega) hi₂
  have hz₁_mem : Q[i₁] ∈ Q := List.getElem_mem hi₁
  have hneS : suffixFrom Q[i₁] Q ≠ [] := suffixFrom_ne_nil hz₁_mem
  have hneB : B ≠ [] := prefixUntil_ne_nil {Q[i₂]} hneS
  have hheadB : B.head hneB = Q[i₁] := by
    dsimp only [B, subpathBetween]
    rw [head_prefixUntil {Q[i₂]} hneS, head_suffixFrom hz₁_mem]
  have hz₂_mem_S : Q[i₂] ∈ suffixFrom Q[i₁] Q := by
    rw [suffixFrom_getElem_eq_drop hi₁ hndQ, List.mem_iff_getElem]
    refine ⟨i₂ - i₁, by simp; omega, ?_⟩
    rw [List.getElem_drop]
    congr 1
    omega
  have hlastB : B.getLast hneB = Q[i₂] := by
    have hmem := getLast_prefixUntil_mem_of_exists {Q[i₂]} hneS
      ⟨Q[i₂], hz₂_mem_S, Finset.mem_singleton_self _⟩
    exact Finset.mem_singleton.mp hmem
  have hlenB : B.length = i₂ - i₁ + 1 := by
    rw [hB_eq, List.length_take, List.length_drop]
    omega
  have hndB : B.Nodup := nodup_prefixUntil {Q[i₂]} (nodup_suffixFrom hndQ)
  have hwB : IsSimpleWalkList G B :=
    isSimpleWalkList_prefixUntil {Q[i₂]} (isSimpleWalkList_suffixFrom hwQ)
  have hmemB : ∀ x, x ∈ B ↔ ∃ m, ∃ hm : m < Q.length, i₁ ≤ m ∧ m ≤ i₂ ∧ Q[m] = x := by
    intro x
    rw [hB_eq, List.mem_iff_getElem]
    constructor
    · rintro ⟨d, hd, hget⟩
      simp only [List.length_take, List.length_drop] at hd
      rw [List.getElem_take, List.getElem_drop] at hget
      exact ⟨i₁ + d, by omega, by omega, by omega, hget⟩
    · rintro ⟨m, hm, hm1, hm2, rfl⟩
      refine ⟨m - i₁, ?_, ?_⟩
      · simp only [List.length_take, List.length_drop]; omega
      · rw [List.getElem_take, List.getElem_drop]
        congr 1
        omega
  have hintB : ∀ x ∈ B, x ≠ B.head hneB → x ≠ B.getLast hneB → x ∉ W.vertexFinset := by
    intro x hx hx_head hx_last
    rw [hheadB] at hx_head
    rw [hlastB] at hx_last
    rcases (hmemB x).mp hx with ⟨m, hm, hm1, hm2, rfl⟩
    have hm_gt : i₁ < m := by
      by_contra hle
      have heq : m = i₁ := by omega
      subst heq
      exact hx_head rfl
    have hm_lt : m < i₂ := by
      by_contra hge
      have heq : m = i₂ := by omega
      subst heq
      exact hx_last rfl
    have hx_ne_qhead : Q[m] ≠ Q.head hneQ := by
      rw [List.head_eq_getElem_zero hneQ, ne_eq, hndQ.getElem_inj_iff]
      omega
    have hx_ne_qlast : Q[m] ≠ Q.getLast hneQ := by
      rw [List.getLast_eq_getElem hneQ, ne_eq, hndQ.getElem_inj_iff]
      omega
    exact hintQ Q[m]
      (mem_drop_one_dropLast_of_mem_of_ne_head_of_ne_getLast hneQ (List.getElem_mem hm)
        hx_ne_qhead hx_ne_qlast)
  have hedgeB : ∀ a b, (a, b) ∈ B.zip (B.drop 1) → ¬ W.IsWallEdge a b := by
    intro a b hab
    exact IsHPath.not_isWallEdge_of_mem_zip W hQ a b
      (mem_zip_of_mem_zip_suffixFrom (mem_zip_of_mem_zip_prefixUntil {Q[i₂]} hab))
  exact ⟨hneB, hheadB, hlastB, hlenB, hndB, hwB, hmemB, hintB, hedgeB⟩

theorem head_getLast_mem_zip_of_length_eq_two {α : Type*} :
    ∀ {L : List α} (hne : L ≠ []), L.length = 2 →
      (L.head hne, L.getLast hne) ∈ L.zip (L.drop 1)
  | [_, _], _, _ => List.mem_cons_self

/-- Join two ray prefixes `A₁ = rayHitPrefix Q P₁` and `A₂ = rayHitPrefix Q P₂` along
`B = subpathBetween Q z₁ z₂`. -/
def joinRaysAlongSubpath (Q P₁ P₂ : List (Fin n)) (z₁ z₂ : Fin n) : List (Fin n) :=
  let A₁ := rayHitPrefix Q P₁
  let A₂ := rayHitPrefix Q P₂
  let B := subpathBetween Q z₁ z₂
  concatOverlap (concatOverlap A₁ B) A₂.reverse

theorem joinRaysAlongSubpath_props {c : Fin n} {Q P₁ P₂ : List (Fin n)}
    (hQ : W.IsHPath Q) (hcQ : c ∉ Q)
    (hP₁ : W.IsStarRay c P₁) (hP₂ : W.IsStarRay c P₂)
    (hmeet₁₂ : ∀ v, v ∈ P₁ → v ∈ P₂ → v = c)
    (hmeet₁ : rayMeetsPath Q P₁ = true) (hmeet₂ : rayMeetsPath Q P₂ = true)
    {i₁ i₂ : ℕ} (hlt : i₁ < i₂) (hi₂ : i₂ < Q.length)
    (hz₁ : (rayHitPrefix Q P₁).getLast? = some (Q[i₁]'(by omega)))
    (hz₂ : (rayHitPrefix Q P₂).getLast? = some Q[i₂]) :
    let R := joinRaysAlongSubpath Q P₁ P₂ (Q[i₁]'(by omega)) Q[i₂]
    ∃ (hneP₁ : P₁ ≠ []) (hneP₂ : P₂ ≠ []) (hneR : R ≠ []),
      R.head hneR = P₁.getLast hneP₁ ∧
      R.getLast hneR = P₂.getLast hneP₂ ∧
      W.IsHPath R ∧
      (∀ x, x ∈ R ↔ x ∈ rayHitPrefix Q P₁ ∨ x ∈ subpathBetween Q (Q[i₁]'(by omega)) Q[i₂] ∨
        x ∈ rayHitPrefix Q P₂) := by
  dsimp only [joinRaysAlongSubpath]
  obtain ⟨hneP₁, hneA₁, hheadA₁, hlastA₁_Q, hlastA₁_P, hc_not_A₁, hA₁_in_P₁, hA₁_drop_not_Q,
    hA₁_not_W, hA₁_no_edge, hndA₁, hwA₁⟩ := W.rayHitPrefix_props hP₁ hcQ hmeet₁
  obtain ⟨hneP₂, hneA₂, hheadA₂, hlastA₂_Q, hlastA₂_P, hc_not_A₂, hA₂_in_P₂, hA₂_drop_not_Q,
    hA₂_not_W, hA₂_no_edge, hndA₂, hwA₂⟩ := W.rayHitPrefix_props hP₂ hcQ hmeet₂
  obtain ⟨hneB, hheadB, hlastB, hlenB, hndB, hwB, hmemB, hintB, hedgeB⟩ :=
    W.subpathBetween_props hQ hlt hi₂
  set A₁ := rayHitPrefix Q P₁
  set A₂ := rayHitPrefix Q P₂
  set B := subpathBetween Q (Q[i₁]'(by omega)) Q[i₂]
  have hlastA₁_eq : A₁.getLast hneA₁ = Q[i₁]'(by omega) := by
    rw [List.getLast?_eq_some_getLast hneA₁, Option.some.injEq] at hz₁
    exact hz₁
  have hlastA₂_eq : A₂.getLast hneA₂ = Q[i₂] := by
    rw [List.getLast?_eq_some_getLast hneA₂, Option.some.injEq] at hz₂
    exact hz₂
  have hB_in_Q : ∀ x ∈ B, x ∈ Q := by
    intro x hx
    rcases (hmemB x).mp hx with ⟨m, hm, _, _, rfl⟩
    exact List.getElem_mem hm
  have hdisj_A₁_B : ∀ x, x ∈ A₁.dropLast → x ∈ B → False :=
    fun x hx₁ hxB => hA₁_drop_not_Q x hx₁ (hB_in_Q x hxB)
  obtain ⟨hneAB, hheadAB, hlastAB, hlenAB, hndAB, hwAB, hmemAB, hzipAB⟩ :=
    concatOverlap_props hneA₁ hneB (hlastA₁_eq.trans hheadB.symm) hndA₁ hndB hdisj_A₁_B hwA₁ hwB
  have hneA₂_rev : A₂.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hneA₂
  have hheadA₂_rev : A₂.reverse.head hneA₂_rev = A₂.getLast hneA₂ := List.head_reverse hneA₂_rev
  have hlastA₂_rev : A₂.reverse.getLast hneA₂_rev = A₂.head hneA₂ := List.getLast_reverse hneA₂_rev
  have hndA₂_rev : A₂.reverse.Nodup := List.nodup_reverse.mpr hndA₂
  have hwA₂_rev : IsSimpleWalkList G A₂.reverse := isSimpleWalkList_reverse hwA₂
  have hA₁_A₂_disj : ∀ x, x ∈ A₁ → x ∈ A₂ → False := by
    intro x hx₁ hx₂
    exact hc_not_A₁ (hmeet₁₂ x (hA₁_in_P₁ x hx₁) (hA₂_in_P₂ x hx₂) ▸ hx₁)
  have hdisj_AB_A₂ : ∀ x, x ∈ (concatOverlap A₁ B).dropLast → x ∈ A₂.reverse → False := by
    intro x hxAB_drop hxA₂_rev
    have hxA₂ : x ∈ A₂ := List.mem_reverse.mp hxA₂_rev
    have hx_ne_z₂ : x ≠ Q[i₂] := by
      rw [← hlastB, ← hlastAB]
      rintro rfl
      exact not_getLast_mem_dropLast_of_nodup hneAB hndAB hxAB_drop
    have hxAB : x ∈ concatOverlap A₁ B := List.dropLast_subset _ hxAB_drop
    rcases (hmemAB x).mp hxAB with hxA₁ | hxB
    · exact hA₁_A₂_disj x hxA₁ hxA₂
    · have hxA₂_drop : x ∈ A₂.dropLast := by
        have h1 : A₂.dropLast ++ [A₂.getLast hneA₂] = A₂ := List.dropLast_append_getLast hneA₂
        rw [← h1, List.mem_append, List.mem_singleton] at hxA₂
        rcases hxA₂ with h | h
        · exact h
        · exact False.elim (hx_ne_z₂ (h.trans hlastA₂_eq))
      exact hA₂_drop_not_Q x hxA₂_drop (hB_in_Q x hxB)
  obtain ⟨hneR, hheadR, hlastR, hlenR, hndR, hwR, hmemR, hzipR⟩ :=
    concatOverlap_props hneAB hneA₂_rev
      (hlastAB.trans (hlastB.trans (hlastA₂_eq.symm.trans hheadA₂_rev.symm)))
      hndAB hndA₂_rev hdisj_AB_A₂ hwAB hwA₂_rev
  have hheadR_eq : (concatOverlap (concatOverlap A₁ B) A₂.reverse).head hneR = P₁.getLast hneP₁ :=
    hheadR.trans (hheadAB.trans hheadA₁)
  have hlastR_eq : (concatOverlap (concatOverlap A₁ B) A₂.reverse).getLast hneR = P₂.getLast hneP₂ :=
    hlastR.trans (hlastA₂_rev.trans hheadA₂)
  have hmemR_iff : ∀ x, x ∈ concatOverlap (concatOverlap A₁ B) A₂.reverse ↔
      x ∈ A₁ ∨ x ∈ B ∨ x ∈ A₂ := by
    intro x
    rw [hmemR, hmemAB, List.mem_reverse, or_assoc]
  have hu₁_W : P₁.getLast hneP₁ ∈ W.vertexFinset := hP₁.choose_spec.2.2.2.2.1
  have hu₂_W : P₂.getLast hneP₂ ∈ W.vertexFinset := hP₂.choose_spec.2.2.2.2.1
  have hPosA₁ : 1 ≤ A₁.length := List.length_pos_iff.mpr hneA₁
  have hPosA₂ : 1 ≤ A₂.reverse.length := List.length_pos_iff.mpr hneA₂_rev
  refine ⟨hneP₁, hneP₂, hneR, hheadR_eq, hlastR_eq,
    ⟨hneR, by omega, hndR, hwR, hheadR_eq.symm ▸ hu₁_W, hlastR_eq.symm ▸ hu₂_W, ?_, ?_⟩,
    hmemR_iff⟩
  · intro v hv hvW
    obtain ⟨hv_ne_head, hv_ne_last⟩ :=
      ne_head_and_ne_getLast_of_mem_drop_dropLast_of_nodup hneR hndR v hv
    rw [hheadR_eq, ← hheadA₁] at hv_ne_head
    rw [hlastR_eq, ← hheadA₂] at hv_ne_last
    have hvR : v ∈ concatOverlap (concatOverlap A₁ B) A₂.reverse :=
      List.mem_of_mem_drop (List.dropLast_subset _ hv)
    rcases (hmemR_iff v).mp hvR with hvA₁ | hvB | hvA₂
    · exact hA₁_not_W v hvA₁ hv_ne_head hvW
    · by_cases hv_z₁ : v = B.head hneB
      · have hvA₁' : v ∈ A₁ := by
          rw [hv_z₁, hheadB, ← hlastA₁_eq]
          exact List.getLast_mem hneA₁
        exact hA₁_not_W v hvA₁' hv_ne_head hvW
      · by_cases hv_z₂ : v = B.getLast hneB
        · have hvA₂' : v ∈ A₂ := by
            rw [hv_z₂, hlastB, ← hlastA₂_eq]
            exact List.getLast_mem hneA₂
          exact hA₂_not_W v hvA₂' hv_ne_last hvW
        · exact hintB v hvB hv_z₁ hv_z₂ hvW
    · exact hA₂_not_W v hvA₂ hv_ne_last hvW
  · intro hlenR2 hedge
    have hmem_zip := head_getLast_mem_zip_of_length_eq_two hneR hlenR2
    rcases hzipR _ _ hmem_zip with h1 | h2
    · rcases hzipAB _ _ h1 with hA₁_z | hB_z
      · exact hA₁_no_edge _ _ hA₁_z hedge
      · exact hedgeB _ _ hB_z hedge
    · have ha_A₂ : (concatOverlap (concatOverlap A₁ B) A₂.reverse).head hneR ∈ A₂ :=
        List.mem_reverse.mp ((List.of_mem_zip h2).1)
      have ha_W : (concatOverlap (concatOverlap A₁ B) A₂.reverse).head hneR ∈ W.vertexFinset :=
        hheadR_eq.symm ▸ hu₁_W
      have ha_eq : (concatOverlap (concatOverlap A₁ B) A₂.reverse).head hneR = A₂.head hneA₂ := by
        by_contra hne
        exact hA₂_not_W _ ha_A₂ hne ha_W
      have hb_eq : (concatOverlap (concatOverlap A₁ B) A₂.reverse).getLast hneR = A₂.head hneA₂ :=
        hlastR_eq.trans hheadA₂.symm
      exact ne_of_mem_zip_of_nodup hndR _ _ hmem_zip (ha_eq.trans hb_eq.symm)

theorem pairwise_filterMap_of_eq {α β : Type*} {R : α → α → Prop} {L : List α}
    (hpw : L.Pairwise R) (f : α → Option β) (g : β → α)
    (hg : ∀ a b, f a = some b → g b = a) :
    (L.filterMap f).Pairwise (fun b₁ b₂ => R (g b₁) (g b₂)) := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    rw [List.pairwise_cons] at hpw
    simp only [List.filterMap_cons]
    cases hfa : f a with
    | none => exact ih hpw.2
    | some b =>
      rw [List.pairwise_cons]
      refine ⟨fun b' hb' => ?_, ih hpw.2⟩
      rw [List.mem_filterMap] at hb'
      rcases hb' with ⟨a', ha', hfa'⟩
      rw [hg a b hfa, hg a' b' hfa']
      exact hpw.1 a' ha'

/-- Find a ray `P ∈ rs` that meets `Q` and has its first hit on `Q` at vertex `z`. -/
def findHitRayAt (rs : List (List (Fin n))) (Q : List (Fin n)) (z : Fin n) :
    Option (List (Fin n)) :=
  rs.find? (fun P => rayMeetsPath Q P && ((rayHitPrefix Q P).getLast? == some z))

/-- Scan `idx = 0, ..., Q.length - 1` along `Q` and collect `(idx, P)` whenever some ray `P ∈ rs`
has its first hit on `Q` at `Q[idx]`. -/
def hitsOnQ (rs : List (List (Fin n))) (Q : List (Fin n)) : List (ℕ × List (Fin n)) :=
  (List.range Q.length).filterMap (fun idx =>
    match Q[idx]? with
    | none => none
    | some z => (findHitRayAt rs Q z).map (fun P => (idx, P)))

theorem hitsOnQ_pairwise_lt (rs : List (List (Fin n))) (Q : List (Fin n)) :
    (hitsOnQ rs Q).Pairwise (fun p₁ p₂ => p₁.1 < p₂.1) := by
  apply pairwise_filterMap_of_eq List.pairwise_lt_range _ Prod.fst
  intro idx b hb
  cases hget : Q[idx]? with
  | none => simp [hget] at hb
  | some z =>
    simp only [hget, Option.map_eq_some_iff] at hb
    rcases hb with ⟨_, _, rfl⟩
    rfl

theorem mem_hitsOnQ {rs : List (List (Fin n))} {Q : List (Fin n)} {p : ℕ × List (Fin n)}
    (hp : p ∈ hitsOnQ rs Q) :
    ∃ hidx : p.1 < Q.length,
      p.2 ∈ rs ∧
      rayMeetsPath Q p.2 = true ∧
      (rayHitPrefix Q p.2).getLast? = some (Q[p.1]'hidx) := by
  rw [hitsOnQ, List.mem_filterMap] at hp
  rcases hp with ⟨idx, hidx_range, hopt⟩
  have hidx : idx < Q.length := List.mem_range.mp hidx_range
  rw [List.getElem?_eq_getElem hidx, Option.map_eq_some_iff] at hopt
  rcases hopt with ⟨P, hfind, rfl⟩
  have hP_mem : P ∈ rs := List.mem_of_find?_eq_some hfind
  have hP_pred := List.find?_some hfind
  simp only [Bool.and_eq_true, beq_iff_eq] at hP_pred
  exact ⟨hidx, hP_mem, hP_pred.1, hP_pred.2⟩

theorem snd_ne_of_fst_ne_of_mem_hitsOnQ {Q : List (Fin n)} (hndQ : Q.Nodup)
    {rs : List (List (Fin n))} {p₁ p₂ : ℕ × List (Fin n)}
    (hp₁ : p₁ ∈ hitsOnQ rs Q) (hp₂ : p₂ ∈ hitsOnQ rs Q) (hne : p₁.1 ≠ p₂.1) :
    p₁.2 ≠ p₂.2 := by
  obtain ⟨hidx₁, _, _, hz₁⟩ := mem_hitsOnQ hp₁
  obtain ⟨hidx₂, _, _, hz₂⟩ := mem_hitsOnQ hp₂
  intro heq
  rw [heq, hz₂, Option.some.injEq, hndQ.getElem_inj_iff] at hz₁
  exact hne hz₁.symm

/-- Every ray `P ∈ rs` that meets `Q` contributes a distinct hit index to `hitsOnQ rs Q`. -/
theorem length_filter_rayMeetsPath_le_length_hitsOnQ {m : ℕ} {c : Fin n}
    {rs : List (List (Fin n))} (hrs : W.IsStarRayList m c rs)
    {Q : List (Fin n)} (hcQ : c ∉ Q) :
    (rs.filter (rayMeetsPath Q)).length ≤ (hitsOnQ rs Q).length := by
  let hitIdx : List (Fin n) → ℕ := fun P =>
    Q.idxOf ((rayHitPrefix Q P).getLast?.getD c)
  have hmem_fst : ∀ P ∈ rs.filter (rayMeetsPath Q),
      hitIdx P ∈ (hitsOnQ rs Q).map Prod.fst := by
    intro P hP
    rw [List.mem_filter] at hP
    obtain ⟨hP_rs, hmeet⟩ := hP
    obtain ⟨_, hneA, _, hlast_Q, _, _, _, _, _, _, _, _⟩ :=
      W.rayHitPrefix_props (hrs.rays_valid P hP_rs) hcQ hmeet
    let z := (rayHitPrefix Q P).getLast hneA
    have hz_opt : (rayHitPrefix Q P).getLast? = some z := List.getLast?_eq_some_getLast hneA
    have hidx_eq : hitIdx P = Q.idxOf z := by
      dsimp [hitIdx]
      rw [hz_opt, Option.getD_some]
    have hidx_lt : Q.idxOf z < Q.length := List.idxOf_lt_length_of_mem hlast_Q
    have hget_idx : Q[Q.idxOf z] = z := List.getElem_idxOf hidx_lt
    have hex_find : ∃ P', findHitRayAt rs Q Q[Q.idxOf z] = some P' := by
      apply Option.ne_none_iff_exists'.mp
      rw [findHitRayAt, ne_eq, List.find?_eq_none]
      intro hall
      have hfalse := hall P hP_rs
      simp [hmeet, hz_opt, hget_idx] at hfalse
    rcases hex_find with ⟨P', hfind⟩
    rw [hidx_eq, List.mem_map]
    refine ⟨(Q.idxOf z, P'), ?_, rfl⟩
    rw [hitsOnQ, List.mem_filterMap]
    refine ⟨Q.idxOf z, List.mem_range.mpr hidx_lt, ?_⟩
    rw [List.getElem?_eq_getElem hidx_lt]
    dsimp only
    rw [hfind, Option.map_some]
  have hnd_map : ((rs.filter (rayMeetsPath Q)).map hitIdx).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    refine (hrs.rays_meet.filter (rayMeetsPath Q)).imp_of_mem ?_
    intro P₁ P₂ hP₁ hP₂ h12 heq_idx
    rw [List.mem_filter] at hP₁ hP₂
    obtain ⟨_, hneA₁, _, hlast₁_Q, hlast₁_P, _, _, _, _, _, _, _⟩ :=
      W.rayHitPrefix_props (hrs.rays_valid P₁ hP₁.1) hcQ hP₁.2
    obtain ⟨_, hneA₂, _, hlast₂_Q, hlast₂_P, _, _, _, _, _, _, _⟩ :=
      W.rayHitPrefix_props (hrs.rays_valid P₂ hP₂.1) hcQ hP₂.2
    have hidx₁ : hitIdx P₁ = Q.idxOf ((rayHitPrefix Q P₁).getLast hneA₁) := by
      dsimp [hitIdx]; rw [List.getLast?_eq_some_getLast hneA₁, Option.getD_some]
    have hidx₂ : hitIdx P₂ = Q.idxOf ((rayHitPrefix Q P₂).getLast hneA₂) := by
      dsimp [hitIdx]; rw [List.getLast?_eq_some_getLast hneA₂, Option.getD_some]
    rw [hidx₁, hidx₂] at heq_idx
    have hz_eq : (rayHitPrefix Q P₁).getLast hneA₁ = (rayHitPrefix Q P₂).getLast hneA₂ := by
      have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hlast₁_Q)
      have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hlast₂_Q)
      rw [← h1, ← h2]
      congr 1
    have hvc : (rayHitPrefix Q P₁).getLast hneA₁ = c :=
      h12 _ hlast₁_P (hz_eq ▸ hlast₂_P)
    exact hcQ (hvc ▸ hlast₁_Q)
  have hsub : ((rs.filter (rayMeetsPath Q)).map hitIdx).toFinset ⊆
      ((hitsOnQ rs Q).map Prod.fst).toFinset := by
    intro idx hidx
    rw [List.mem_toFinset, List.mem_map] at hidx ⊢
    rcases hidx with ⟨P, hP, rfl⟩
    exact List.mem_map.mp (hmem_fst P hP)
  calc (rs.filter (rayMeetsPath Q)).length
      = ((rs.filter (rayMeetsPath Q)).map hitIdx).length := (List.length_map _).symm
    _ = ((rs.filter (rayMeetsPath Q)).map hitIdx).toFinset.card :=
        (List.toFinset_card_of_nodup hnd_map).symm
    _ ≤ ((hitsOnQ rs Q).map Prod.fst).toFinset.card := Finset.card_le_card hsub
    _ ≤ ((hitsOnQ rs Q).map Prod.fst).length := List.toFinset_card_le _
    _ = (hitsOnQ rs Q).length := List.length_map _

/-- Build `k'` disjoint `H`-paths in Case A of (7.5) from the first `2 * k'` hits of `rs` along `Q`. -/
def buildCaseAPaths (k' : ℕ) (rs : List (List (Fin n))) (Q : List (Fin n)) :
    List (List (Fin n)) :=
  let hits := hitsOnQ rs Q
  (List.range k').map (fun t =>
    match hits[2 * t]?, hits[2 * t + 1]? with
    | some p₁, some p₂ =>
      match Q[p₁.1]?, Q[p₂.1]? with
      | some z₁, some z₂ => joinRaysAlongSubpath Q p₁.2 p₂.2 z₁ z₂
      | _, _ => []
    | _, _ => [])

theorem length_buildCaseAPaths (k' : ℕ) (rs : List (List (Fin n))) (Q : List (Fin n)) :
    (buildCaseAPaths k' rs Q).length = k' := by
  simp [buildCaseAPaths]

theorem getElem_buildCaseAPaths {k' t : ℕ} (rs : List (List (Fin n))) (Q : List (Fin n))
    (ht : t < (buildCaseAPaths k' rs Q).length)
    (h0 : 2 * t < (hitsOnQ rs Q).length) (h1 : 2 * t + 1 < (hitsOnQ rs Q).length)
    (hi₁ : ((hitsOnQ rs Q)[2 * t]'h0).1 < Q.length)
    (hi₂ : ((hitsOnQ rs Q)[2 * t + 1]'h1).1 < Q.length) :
    (buildCaseAPaths k' rs Q)[t]'ht =
      joinRaysAlongSubpath Q ((hitsOnQ rs Q)[2 * t]'h0).2 ((hitsOnQ rs Q)[2 * t + 1]'h1).2
        (Q[((hitsOnQ rs Q)[2 * t]'h0).1]'hi₁) (Q[((hitsOnQ rs Q)[2 * t + 1]'h1).1]'hi₂) := by
  simp [buildCaseAPaths, List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]

/-- Specification of `buildCaseAPaths` (Case A of (7.5), `GM13.exists_hPaths_of_rays_meet`). -/
theorem buildCaseAPaths_spec (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {k' r : ℕ} {c : Fin n} {rs : List (List (Fin n))} {Q : List (Fin n)}
    (hrs : W.IsStarRayList (2 * r) c rs) (hQ : W.IsHPath Q) (hcQ : c ∉ Q)
    (hhits : 2 * k' ≤ (hitsOnQ rs Q).length) :
    let Rs := buildCaseAPaths k' rs Q
    Rs.length = k' ∧
    W.IsFarHPathList r Rs ∧
    (∀ R ∈ Rs, ∀ x ∈ R, x ∈ Q ∨ ∃ P ∈ rs, x ∈ P) := by
  intro Rs
  have hndQ : Q.Nodup := hQ.choose_spec.2.1
  let hits := hitsOnQ rs Q
  have hhits' : 2 * k' ≤ hits.length := hhits
  have hlen : Rs.length = k' := length_buildCaseAPaths k' rs Q
  have hpw_hits : hits.Pairwise (fun p₁ p₂ => p₁.1 < p₂.1) := hitsOnQ_pairwise_lt rs Q
  have hget_lt : ∀ j₁ j₂ (hj₁ : j₁ < hits.length) (hj₂ : j₂ < hits.length),
      j₁ < j₂ → (hits[j₁]'hj₁).1 < (hits[j₂]'hj₂).1 :=
    fun j₁ j₂ hj₁ hj₂ hlt => List.pairwise_iff_getElem.mp hpw_hits j₁ j₂ hj₁ hj₂ hlt
  have hget_props : ∀ t (ht : t < k'),
      let h0 : 2 * t < hits.length := by omega
      let h1 : 2 * t + 1 < hits.length := by omega
      let p₁ := hits[2 * t]'h0
      let p₂ := hits[2 * t + 1]'h1
      ∃ (hi₁ : p₁.1 < Q.length) (hi₂ : p₂.1 < Q.length)
        (hneP₁ : p₁.2 ≠ []) (hneP₂ : p₂.2 ≠ []) (hneR : (Rs[t]'(by omega)) ≠ []),
        p₁.1 < p₂.1 ∧
        p₁.2 ∈ rs ∧ p₂.2 ∈ rs ∧
        Rs[t]'(by omega) = joinRaysAlongSubpath Q p₁.2 p₂.2 (Q[p₁.1]'hi₁) (Q[p₂.1]'hi₂) ∧
        (Rs[t]'(by omega)).head hneR = p₁.2.getLast hneP₁ ∧
        (Rs[t]'(by omega)).getLast hneR = p₂.2.getLast hneP₂ ∧
        W.IsHPath (Rs[t]'(by omega)) ∧
        (∀ x, x ∈ Rs[t]'(by omega) ↔
          x ∈ rayHitPrefix Q p₁.2 ∨
          x ∈ subpathBetween Q (Q[p₁.1]'hi₁) (Q[p₂.1]'hi₂) ∨
          x ∈ rayHitPrefix Q p₂.2) := by
    intro t ht h0 h1 p₁ p₂
    have hp₁_mem : p₁ ∈ hits := List.getElem_mem h0
    have hp₂_mem : p₂ ∈ hits := List.getElem_mem h1
    obtain ⟨hi₁, hp₁_rs, hmeet₁, hz₁⟩ := mem_hitsOnQ hp₁_mem
    obtain ⟨hi₂, hp₂_rs, hmeet₂, hz₂⟩ := mem_hitsOnQ hp₂_mem
    have hlt_12 : p₁.1 < p₂.1 := hget_lt (2 * t) (2 * t + 1) h0 h1 (by omega)
    have hne_12 : p₁.2 ≠ p₂.2 :=
      snd_ne_of_fst_ne_of_mem_hitsOnQ hndQ hp₁_mem hp₂_mem (by omega)
    have hmeet_12 : ∀ v, v ∈ p₁.2 → v ∈ p₂.2 → v = c :=
      fun v hv₁ hv₂ => hrs.eq_center_of_ne hp₁_rs hp₂_rs hne_12 hv₁ hv₂
    have hRs_t : Rs[t]'(by omega) =
        joinRaysAlongSubpath Q p₁.2 p₂.2 (Q[p₁.1]'hi₁) (Q[p₂.1]'hi₂) :=
      getElem_buildCaseAPaths rs Q (by rw [length_buildCaseAPaths]; exact ht) h0 h1 hi₁ hi₂
    obtain ⟨hneP₁, hneP₂, hneR, hheadR, hlastR, hpathR, hmemR⟩ :=
      W.joinRaysAlongSubpath_props hQ hcQ (hrs.rays_valid _ hp₁_rs) (hrs.rays_valid _ hp₂_rs)
        hmeet_12 hmeet₁ hmeet₂ hlt_12 hi₂ hz₁ hz₂
    refine ⟨hi₁, hi₂, hneP₁, hneP₂, ?_⟩
    simp only [hRs_t]
    exact ⟨hneR, hlt_12, hp₁_rs, hp₂_rs, trivial, hheadR, hlastR, hpathR, hmemR⟩
  refine ⟨hlen, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro R hR
    rcases List.mem_iff_getElem.mp hR with ⟨t, ht, rfl⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hvalid, _⟩ := hget_props t (by omega)
    exact hvalid
  · rw [List.pairwise_iff_getElem]
    intro t₁ t₂ ht₁ ht₂ hlt_t v hv₁ hv₂
    have ht₁' : t₁ < k' := by omega
    have ht₂' : t₂ < k' := by omega
    have h0_1 : 2 * t₁ < hits.length := by omega
    have h1_1 : 2 * t₁ + 1 < hits.length := by omega
    have h0_2 : 2 * t₂ < hits.length := by omega
    have h1_2 : 2 * t₂ + 1 < hits.length := by omega
    obtain ⟨hi₁, hi₂, _, _, _, hlt_12, hp₁_rs, hp₂_rs, _, _, _, _, hmem₁⟩ := hget_props t₁ ht₁'
    obtain ⟨hi₃, hi₄, _, _, _, hlt_34, hp₃_rs, hp₄_rs, _, _, _, _, hmem₂⟩ := hget_props t₂ ht₂'
    have hlt_23 : (hits[2 * t₁ + 1]'h1_1).1 < (hits[2 * t₂]'h0_2).1 :=
      hget_lt (2 * t₁ + 1) (2 * t₂) h1_1 h0_2 (by omega)
    obtain ⟨_, _, _, _, _, _, hmemB₁, _, _⟩ := W.subpathBetween_props hQ hlt_12 hi₂
    obtain ⟨_, _, _, _, _, _, hmemB₂, _, _⟩ := W.subpathBetween_props hQ hlt_34 hi₄
    -- Helper: if `v ∈ rayHitPrefix Q p.2` and `v ∈ Q`, then `v = Q[p.1]`
    have hhit_in_Q : ∀ (p : ℕ × List (Fin n)) (hp : p ∈ hits) (hi : p.1 < Q.length),
        v ∈ rayHitPrefix Q p.2 → v ∈ Q → v = Q[p.1]'hi := by
      intro p hp hi hvA hvQ
      obtain ⟨_, hp_rs, hmeet_p, hz_p⟩ := mem_hitsOnQ hp
      obtain ⟨_, hneA, _, _, _, _, _, hdrop_not_Q, _, _, _, _⟩ :=
        W.rayHitPrefix_props (hrs.rays_valid _ hp_rs) hcQ hmeet_p
      have h1 : (rayHitPrefix Q p.2).dropLast ++ [(rayHitPrefix Q p.2).getLast hneA] =
          rayHitPrefix Q p.2 := List.dropLast_append_getLast hneA
      rw [← h1, List.mem_append, List.mem_singleton] at hvA
      rcases hvA with hv_drop | rfl
      · exact False.elim (hdrop_not_Q v hv_drop hvQ)
      · rw [List.getLast?_eq_some_getLast hneA, Option.some.injEq] at hz_p
        exact hz_p
    -- Helper: if `v ∈ rayHitPrefix Q p.2` and `v ∈ rayHitPrefix Q p'.2` with `p.1 ≠ p'.1`, False
    have hhit_disj : ∀ (p p' : ℕ × List (Fin n)) (hp : p ∈ hits) (hp' : p' ∈ hits),
        p.1 ≠ p'.1 → v ∈ rayHitPrefix Q p.2 → v ∈ rayHitPrefix Q p'.2 → False := by
      intro p p' hp hp' hne_idx hvA hvA'
      obtain ⟨_, hp_rs, hmeet_p, _⟩ := mem_hitsOnQ hp
      obtain ⟨_, hp'_rs, hmeet_p', _⟩ := mem_hitsOnQ hp'
      obtain ⟨_, _, _, _, _, hc_not_A, hA_in_P, _, _, _, _, _⟩ :=
        W.rayHitPrefix_props (hrs.rays_valid _ hp_rs) hcQ hmeet_p
      obtain ⟨_, _, _, _, _, _, hA'_in_P', _, _, _, _, _⟩ :=
        W.rayHitPrefix_props (hrs.rays_valid _ hp'_rs) hcQ hmeet_p'
      have hne_P : p.2 ≠ p'.2 := snd_ne_of_fst_ne_of_mem_hitsOnQ hndQ hp hp' hne_idx
      have hvc : v = c := hrs.eq_center_of_ne hp_rs hp'_rs hne_P (hA_in_P v hvA) (hA'_in_P' v hvA')
      exact hc_not_A (hvc ▸ hvA)
    rcases (hmem₁ v).mp hv₁ with hvA₁ | hvB₁ | hvA₂ <;>
      rcases (hmem₂ v).mp hv₂ with hvA₃ | hvB₂ | hvA₄
    · exact hhit_disj (hits[2 * t₁]'h0_1) (hits[2 * t₂]'h0_2)
        (List.getElem_mem h0_1) (List.getElem_mem h0_2) (by omega) hvA₁ hvA₃
    · rcases (hmemB₂ v).mp hvB₂ with ⟨m, hm, hm3, hm4, hQm⟩
      have hv_eq := hhit_in_Q (hits[2 * t₁]'h0_1) (List.getElem_mem h0_1) hi₁ hvA₁
        (hQm ▸ List.getElem_mem hm)
      rw [← hQm, hndQ.getElem_inj_iff] at hv_eq
      omega
    · exact hhit_disj (hits[2 * t₁]'h0_1) (hits[2 * t₂ + 1]'h1_2)
        (List.getElem_mem h0_1) (List.getElem_mem h1_2) (by omega) hvA₁ hvA₄
    · rcases (hmemB₁ v).mp hvB₁ with ⟨m, hm, hm1, hm2, hQm⟩
      have hv_eq := hhit_in_Q (hits[2 * t₂]'h0_2) (List.getElem_mem h0_2) hi₃ hvA₃
        (hQm ▸ List.getElem_mem hm)
      rw [← hQm, hndQ.getElem_inj_iff] at hv_eq
      omega
    · rcases (hmemB₁ v).mp hvB₁ with ⟨m₁, hm₁, _, hm₁_le, hQm₁⟩
      rcases (hmemB₂ v).mp hvB₂ with ⟨m₂, hm₂, hm₂_ge, _, hQm₂⟩
      have heq_Q : Q[m₁] = Q[m₂] := hQm₁.trans hQm₂.symm
      rw [hndQ.getElem_inj_iff] at heq_Q
      omega
    · rcases (hmemB₁ v).mp hvB₁ with ⟨m, hm, hm1, hm2, hQm⟩
      have hv_eq := hhit_in_Q (hits[2 * t₂ + 1]'h1_2) (List.getElem_mem h1_2) hi₄ hvA₄
        (hQm ▸ List.getElem_mem hm)
      rw [← hQm, hndQ.getElem_inj_iff] at hv_eq
      omega
    · exact hhit_disj (hits[2 * t₁ + 1]'h1_1) (hits[2 * t₂]'h0_2)
        (List.getElem_mem h1_1) (List.getElem_mem h0_2) (by omega) hvA₂ hvA₃
    · rcases (hmemB₂ v).mp hvB₂ with ⟨m, hm, hm3, hm4, hQm⟩
      have hv_eq := hhit_in_Q (hits[2 * t₁ + 1]'h1_1) (List.getElem_mem h1_1) hi₂ hvA₂
        (hQm ▸ List.getElem_mem hm)
      rw [← hQm, hndQ.getElem_inj_iff] at hv_eq
      omega
    · exact hhit_disj (hits[2 * t₁ + 1]'h1_1) (hits[2 * t₂ + 1]'h1_2)
        (List.getElem_mem h1_1) (List.getElem_mem h1_2) (by omega) hvA₂ hvA₄
  · intro R hR a b ha hb
    rcases List.mem_iff_getElem.mp hR with ⟨t, ht, rfl⟩
    have ht' : t < k' := by omega
    obtain ⟨_, _, hneP₁, hneP₂, hneR, hlt_12, hp₁_rs, hp₂_rs, _, hheadR, hlastR, _, _⟩ :=
      hget_props t ht'
    have h0 : 2 * t < hits.length := by omega
    have h1 : 2 * t + 1 < hits.length := by omega
    have hne_12 : (hits[2 * t]'h0).2 ≠ (hits[2 * t + 1]'h1).2 :=
      snd_ne_of_fst_ne_of_mem_hitsOnQ hndQ (List.getElem_mem h0) (List.getElem_mem h1) (by omega)
    rw [List.head?_eq_some_head hneR, Option.some.injEq] at ha
    rw [List.getLast?_eq_some_getLast hneR, Option.some.injEq] at hb
    have h2r : 2 * r ≤ W.brickDist a b :=
      hrs.brickDist_ge_of_ne h2 he hW hp₁_rs hp₂_rs hne_12
        (by rw [List.getLast?_eq_some_getLast hneP₁, ← hheadR, ha])
        (by rw [List.getLast?_eq_some_getLast hneP₂, ← hlastR, hb])
    omega
  · rw [List.pairwise_iff_getElem]
    intro t₁ t₂ ht₁ ht₂ hlt_t a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂
    have ht₁' : t₁ < k' := by omega
    have ht₂' : t₂ < k' := by omega
    obtain ⟨_, _, hneP₁, hneP₂, hneR₁, hlt_12, hp₁_rs, hp₂_rs, _, hheadR₁, hlastR₁, _, _⟩ :=
      hget_props t₁ ht₁'
    obtain ⟨_, _, hneP₃, hneP₄, hneR₂, hlt_34, hp₃_rs, hp₄_rs, _, hheadR₂, hlastR₂, _, _⟩ :=
      hget_props t₂ ht₂'
    have h0_1 : 2 * t₁ < hits.length := by omega
    have h1_1 : 2 * t₁ + 1 < hits.length := by omega
    have h0_2 : 2 * t₂ < hits.length := by omega
    have h1_2 : 2 * t₂ + 1 < hits.length := by omega
    have hlt_23 : (hits[2 * t₁ + 1]'h1_1).1 < (hits[2 * t₂]'h0_2).1 :=
      hget_lt (2 * t₁ + 1) (2 * t₂) h1_1 h0_2 (by omega)
    rw [List.head?_eq_some_head hneR₁, Option.some.injEq] at ha₁
    rw [List.getLast?_eq_some_getLast hneR₁, Option.some.injEq] at hb₁
    rw [List.head?_eq_some_head hneR₂, Option.some.injEq] at ha₂
    rw [List.getLast?_eq_some_getLast hneR₂, Option.some.injEq] at hb₂
    have hu₁ : (hits[2 * t₁]'h0_1).2.getLast? = some a₁ := by
      rw [List.getLast?_eq_some_getLast hneP₁, ← hheadR₁, ha₁]
    have hu₂ : (hits[2 * t₁ + 1]'h1_1).2.getLast? = some b₁ := by
      rw [List.getLast?_eq_some_getLast hneP₂, ← hlastR₁, hb₁]
    have hu₃ : (hits[2 * t₂]'h0_2).2.getLast? = some a₂ := by
      rw [List.getLast?_eq_some_getLast hneP₃, ← hheadR₂, ha₂]
    have hu₄ : (hits[2 * t₂ + 1]'h1_2).2.getLast? = some b₂ := by
      rw [List.getLast?_eq_some_getLast hneP₄, ← hlastR₂, hb₂]
    have hd13 := hrs.brickDist_ge_of_ne h2 he hW hp₁_rs hp₃_rs
      (snd_ne_of_fst_ne_of_mem_hitsOnQ hndQ (List.getElem_mem h0_1) (List.getElem_mem h0_2) (by omega))
      hu₁ hu₃
    have hd14 := hrs.brickDist_ge_of_ne h2 he hW hp₁_rs hp₄_rs
      (snd_ne_of_fst_ne_of_mem_hitsOnQ hndQ (List.getElem_mem h0_1) (List.getElem_mem h1_2) (by omega))
      hu₁ hu₄
    have hd23 := hrs.brickDist_ge_of_ne h2 he hW hp₂_rs hp₃_rs
      (snd_ne_of_fst_ne_of_mem_hitsOnQ hndQ (List.getElem_mem h1_1) (List.getElem_mem h0_2) (by omega))
      hu₂ hu₃
    have hd24 := hrs.brickDist_ge_of_ne h2 he hW hp₂_rs hp₄_rs
      (snd_ne_of_fst_ne_of_mem_hitsOnQ hndQ (List.getElem_mem h1_1) (List.getElem_mem h1_2) (by omega))
      hu₂ hu₄
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro R hR x hx
    rcases List.mem_iff_getElem.mp hR with ⟨t, ht, rfl⟩
    have ht' : t < k' := by omega
    obtain ⟨hi₁, hi₂, _, _, _, hlt_12, hp₁_rs, hp₂_rs, _, _, _, _, hmemR⟩ := hget_props t ht'
    obtain ⟨_, _, _, _, _, _, hmemB, _, _⟩ := W.subpathBetween_props hQ hlt_12 hi₂
    rcases (hmemR x).mp hx with hxA₁ | hxB | hxA₂
    · exact Or.inr ⟨_, hp₁_rs,
        List.mem_reverse.mp (mem_of_mem_prefixUntil Q.toFinset hxA₁)⟩
    · rcases (hmemB x).mp hxB with ⟨m, hm, _, _, rfl⟩
      exact Or.inl (List.getElem_mem hm)
    · exact Or.inr ⟨_, hp₂_rs,
        List.mem_reverse.mp (mem_of_mem_prefixUntil Q.toFinset hxA₂)⟩

/-! ### Section 5: Case B, Joining Two Good Rays Through Center `c` -/

/-- Whether the wall endpoint of ray `P` has computed brick distance `< r` to vertex `e`. -/
def closeToVert (r : ℕ) (e : Fin n) (P : List (Fin n)) : Bool :=
  match P.getLast? with
  | some u => decide (W.computeBrickDist u e < r)
  | none => false

theorem brickDist_ge_of_not_closeToVert (h2 : 2 ≤ h) (he : Even h)
    {r : ℕ} {e u : Fin n} {P : List (Fin n)} (hu : P.getLast? = some u)
    (hnot : W.closeToVert r e P = false) :
    r ≤ W.brickDist u e := by
  unfold closeToVert at hnot
  rw [hu, decide_eq_false_iff_not, not_lt,
    W.computeBrickDist_eq_brickDist (by omega) he] at hnot
  exact hnot

/-- At most one ray `P ∈ rs` of an external `(l, 2 * r)`-star can have endpoint within brick
distance `< r` of a given vertex `e ∈ W.vertexFinset` (by triangle inequality on `W.brickDist`). -/
theorem length_filter_not_closeToVert_ge (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {r : ℕ} {c e : Fin n} (he_mem : e ∈ W.vertexFinset)
    {rs : List (List (Fin n))} (hrs : W.IsStarRayList (2 * r) c rs) :
    rs.length - 1 ≤ (rs.filter (fun P => !W.closeToVert r e P)).length := by
  refine length_filter_ge_sub_one hrs.ends_dist (fun P => !W.closeToVert r e P) ?_
  intro P₁ hP₁ P₂ hP₂ hdist₁₂ hp₁ hp₂
  simp only [Bool.not_eq_false'] at hp₁ hp₂
  unfold closeToVert at hp₁ hp₂
  obtain ⟨hne₁, _, _, _, _, hlast₁, _, _⟩ := hrs.rays_valid P₁ hP₁
  obtain ⟨hne₂, _, _, _, _, hlast₂, _, _⟩ := hrs.rays_valid P₂ hP₂
  rw [List.getLast?_eq_some_getLast hne₁, decide_eq_true_iff] at hp₁
  rw [List.getLast?_eq_some_getLast hne₂, decide_eq_true_iff] at hp₂
  rw [W.computeBrickDist_eq_brickDist (by omega) he] at hp₁ hp₂
  have h2r : 2 * r ≤ W.brickDist (P₁.getLast hne₁) (P₂.getLast hne₂) :=
    hdist₁₂ _ _ (List.getLast?_eq_some_getLast hne₁) (List.getLast?_eq_some_getLast hne₂)
  have htri : W.brickDist (P₁.getLast hne₁) (P₂.getLast hne₂) ≤
      W.brickDist (P₁.getLast hne₁) e + W.brickDist e (P₂.getLast hne₂) :=
    W.brickDist_triangle h2 he hW hlast₁ he_mem hlast₂
  have hcomm : W.brickDist e (P₂.getLast hne₂) = W.brickDist (P₂.getLast hne₂) e :=
    W.brickDist_comm_of_mem h2 he hW he_mem hlast₂
  omega

/-- Whether the wall endpoint of ray `P` is within brick distance `< r` of the head of `Q`. -/
def closeToHead (r : ℕ) (Q P : List (Fin n)) : Bool :=
  match Q.head? with
  | some a => W.closeToVert r a P
  | none => false

/-- Whether the wall endpoint of ray `P` is within brick distance `< r` of the last vertex of `Q`. -/
def closeToLast (r : ℕ) (Q P : List (Fin n)) : Bool :=
  match Q.getLast? with
  | some b => W.closeToVert r b P
  | none => false

/-- A ray `P` is good for an existing `H`-path `Q` if it is vertex-disjoint from `Q` and its
wall endpoint is at brick distance `≥ r` from both ends of `Q`. -/
def isGoodRayForQ (r : ℕ) (Q P : List (Fin n)) : Bool :=
  !rayMeetsPath Q P && (!W.closeToHead r Q P && !W.closeToLast r Q P)

/-- A ray `P` is good for `Qs` if it is good for every `Q ∈ Qs`. -/
def isGoodRay (r : ℕ) (Qs : List (List (Fin n))) (P : List (Fin n)) : Bool :=
  Qs.all (fun Q => W.isGoodRayForQ r Q P)

theorem length_filter_add_length_filter_not {α : Type*} (p : α → Bool) (L : List α) :
    (L.filter p).length + (L.filter (fun x => !p x)).length = L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    cases hx : p x <;> simp [hx] <;> omega

theorem length_filter_and_ge {α : Type*} (p q : α → Bool) (L : List α) :
    (L.filter p).length + (L.filter q).length - L.length ≤
      (L.filter (fun x => p x && q x)).length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hle_p : (xs.filter p).length ≤ xs.length := List.length_filter_le p xs
    have hle_q : (xs.filter q).length ≤ xs.length := List.length_filter_le q xs
    cases hp : p x <;> cases hq : q x <;> simp [hp, hq] <;> omega

theorem length_filter_all_ge {α β : Type*} (f : β → α → Bool) (B : ℕ)
    (Qs : List β) (L : List α)
    (hQs : ∀ Q ∈ Qs, L.length - B ≤ (L.filter (f Q)).length) :
    L.length - Qs.length * B ≤ (L.filter (fun x => Qs.all (fun Q => f Q x))).length := by
  induction Qs with
  | nil => simp
  | cons Q Qs ih =>
    have hQ : L.length - B ≤ (L.filter (f Q)).length := hQs Q List.mem_cons_self
    have hih : L.length - Qs.length * B ≤
        (L.filter (fun x => Qs.all (fun Q' => f Q' x))).length :=
      ih (fun Q' hQ' => hQs Q' (List.mem_cons_of_mem Q hQ'))
    have hand := length_filter_and_ge (f Q) (fun x => Qs.all (fun Q' => f Q' x)) L
    simp only [List.all_cons, List.length_cons]
    have hmul : (Qs.length + 1) * B = Qs.length * B + B := Nat.succ_mul Qs.length B
    omega

theorem length_filter_isGoodRayForQ_ge (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {r k : ℕ} {c : Fin n} {rs : List (List (Fin n))} (hrs : W.IsStarRayList (2 * r) c rs)
    {Q : List (Fin n)} (hQ : W.IsHPath Q) (hcQ : c ∉ Q)
    (hhits : (hitsOnQ rs Q).length < 2 * (k + 1)) :
    rs.length - (2 * k + 3) ≤ (rs.filter (W.isGoodRayForQ r Q)).length := by
  obtain ⟨hneQ, _, _, _, hheadQ_W, hlastQ_W, _, _⟩ := hQ
  have hmeet_le : (rs.filter (rayMeetsPath Q)).length ≤ (hitsOnQ rs Q).length :=
    W.length_filter_rayMeetsPath_le_length_hitsOnQ hrs hcQ
  have hsum_meet := length_filter_add_length_filter_not (rayMeetsPath Q) rs
  have hnot_meet : rs.length - (2 * k + 1) ≤ (rs.filter (fun P => !rayMeetsPath Q P)).length := by
    omega
  have hhead_eq : (fun P => !W.closeToHead r Q P) =
      (fun P => !W.closeToVert r (Q.head hneQ) P) := by
    funext P
    simp [closeToHead, List.head?_eq_some_head hneQ]
  have hlast_eq : (fun P => !W.closeToLast r Q P) =
      (fun P => !W.closeToVert r (Q.getLast hneQ) P) := by
    funext P
    simp [closeToLast, List.getLast?_eq_some_getLast hneQ]
  have hnot_head : rs.length - 1 ≤ (rs.filter (fun P => !W.closeToHead r Q P)).length := by
    rw [hhead_eq]
    exact W.length_filter_not_closeToVert_ge h2 he hW hheadQ_W hrs
  have hnot_last : rs.length - 1 ≤ (rs.filter (fun P => !W.closeToLast r Q P)).length := by
    rw [hlast_eq]
    exact W.length_filter_not_closeToVert_ge h2 he hW hlastQ_W hrs
  have hand1 := length_filter_and_ge
    (fun P => !W.closeToHead r Q P) (fun P => !W.closeToLast r Q P) rs
  have hand2 := length_filter_and_ge
    (fun P => !rayMeetsPath Q P)
    (fun P => !W.closeToHead r Q P && !W.closeToLast r Q P) rs
  unfold isGoodRayForQ
  omega

theorem two_le_length_filter_isGoodRay (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {r k : ℕ} {c : Fin n} {rs : List (List (Fin n))} (hrs : W.IsStarRayList (2 * r) c rs)
    {Qs : List (List (Fin n))} (hQs : W.IsFarHPathList r Qs) (hlenQs : Qs.length = k)
    (hcQs : ∀ Q ∈ Qs, c ∉ Q)
    (hhits : ∀ Q ∈ Qs, (hitsOnQ rs Q).length < 2 * (k + 1))
    (hl : 2 * (k + 1) ^ 2 - (k + 1) + 3 ≤ rs.length) :
    2 ≤ (rs.filter (W.isGoodRay r Qs)).length := by
  have hall := length_filter_all_ge (fun Q P => W.isGoodRayForQ r Q P) (2 * k + 3) Qs rs
    (fun Q hQ => W.length_filter_isGoodRayForQ_ge h2 he hW hrs
      (hQs.paths_valid Q hQ) (hcQs Q hQ) (hhits Q hQ))
  rw [hlenQs] at hall
  have hk2 : k + 1 ≤ 2 * (k + 1) ^ 2 := by nlinarith
  have halg : k * (2 * k + 3) + 4 = 2 * (k + 1) ^ 2 - (k + 1) + 3 := by
    zify [hk2]
    ring
  unfold isGoodRay
  omega

/-- Join two star rays `P₁, P₂` sharing center `c = P₁.head = P₂.head` into an `H`-path
`P₁.reverse.dropLast ++ P₂` from `P₁.getLast` to `P₂.getLast`. -/
def joinTwoRays (P₁ P₂ : List (Fin n)) : List (Fin n) :=
  concatOverlap P₁.reverse P₂

theorem joinTwoRays_props {c : Fin n} {P₁ P₂ : List (Fin n)}
    (hc : c ∉ W.vertexFinset) (hP₁ : W.IsStarRay c P₁) (hP₂ : W.IsStarRay c P₂)
    (hmeet : ∀ v, v ∈ P₁ → v ∈ P₂ → v = c) :
    let Q := joinTwoRays P₁ P₂
    ∃ (hneP₁ : P₁ ≠ []) (hneP₂ : P₂ ≠ []) (hneQ : Q ≠ []),
      Q.head hneQ = P₁.getLast hneP₁ ∧
      Q.getLast hneQ = P₂.getLast hneP₂ ∧
      W.IsHPath Q ∧
      (∀ x, x ∈ Q ↔ x ∈ P₁ ∨ x ∈ P₂) := by
  dsimp only [joinTwoRays]
  obtain ⟨hneP₁, hheadP₁, hlenP₁, hndP₁, hwP₁, hlastP₁, hintP₁, _⟩ := hP₁
  obtain ⟨hneP₂, hheadP₂, hlenP₂, hndP₂, hwP₂, hlastP₂, hintP₂, _⟩ := hP₂
  have hne₁_rev : P₁.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hneP₁
  have hlast₁_rev : P₁.reverse.getLast hne₁_rev = P₂.head hneP₂ := by
    rw [List.getLast_reverse, hheadP₁, hheadP₂]
  have hnd₁_rev : P₁.reverse.Nodup := List.nodup_reverse.mpr hndP₁
  have hw₁_rev : IsSimpleWalkList G P₁.reverse := isSimpleWalkList_reverse hwP₁
  have hdisj : ∀ x, x ∈ P₁.reverse.dropLast → x ∈ P₂ → False := by
    intro x hx₁ hx₂
    have hxP₁ : x ∈ P₁ := List.mem_reverse.mp (List.dropLast_subset _ hx₁)
    have hxc : x = c := hmeet x hxP₁ hx₂
    have hlast_c : P₁.reverse.getLast hne₁_rev = c := by
      rw [List.getLast_reverse, hheadP₁]
    exact not_getLast_mem_dropLast_of_nodup hne₁_rev hnd₁_rev (hlast_c.symm ▸ hxc ▸ hx₁)
  obtain ⟨hneQ, hheadQ, hlastQ, hlenQ, hndQ, hwQ, hmemQ, _⟩ :=
    concatOverlap_props hne₁_rev hneP₂ hlast₁_rev hnd₁_rev hndP₂ hdisj hw₁_rev hwP₂
  have hheadQ' : (concatOverlap P₁.reverse P₂).head hneQ = P₁.getLast hneP₁ :=
    hheadQ.trans (List.head_reverse hne₁_rev)
  have hmemQ' : ∀ x, x ∈ concatOverlap P₁.reverse P₂ ↔ x ∈ P₁ ∨ x ∈ P₂ := fun x => by
    rw [hmemQ, List.mem_reverse]
  have hlen_rev : P₁.reverse.length = P₁.length := List.length_reverse
  refine ⟨hneP₁, hneP₂, hneQ, hheadQ', hlastQ,
    ⟨hneQ, by omega, hndQ, hwQ, hheadQ'.symm ▸ hlastP₁, hlastQ.symm ▸ hlastP₂, ?_, ?_⟩,
    hmemQ'⟩
  · intro v hv hvW
    obtain ⟨hv_ne_head, hv_ne_last⟩ :=
      ne_head_and_ne_getLast_of_mem_drop_dropLast_of_nodup hneQ hndQ v hv
    rw [hheadQ'] at hv_ne_head
    rw [hlastQ] at hv_ne_last
    have hv_ne_c : v ≠ c := fun h => hc (h ▸ hvW)
    have hvQ : v ∈ concatOverlap P₁.reverse P₂ :=
      List.mem_of_mem_drop (List.dropLast_subset _ hv)
    rcases (hmemQ' v).mp hvQ with hvP₁ | hvP₂
    · exact hintP₁ v (mem_drop_one_dropLast_of_mem_of_ne_head_of_ne_getLast hneP₁ hvP₁
        (hheadP₁.symm ▸ hv_ne_c) hv_ne_head) hvW
    · exact hintP₂ v (mem_drop_one_dropLast_of_mem_of_ne_head_of_ne_getLast hneP₂ hvP₂
        (hheadP₂.symm ▸ hv_ne_c) hv_ne_last) hvW
  · intro hlen2
    omega

theorem headD_eq_getElem_zero {α : Type*} (d : α) :
    ∀ (L : List α) (h0 : 0 < L.length), L.headD d = L[0]'h0
  | _ :: _, _ => rfl

theorem drop_one_headD_eq_getElem_one {α : Type*} (d : α) :
    ∀ (L : List α) (h1 : 1 < L.length), (L.drop 1).headD d = L[1]'h1
  | _ :: _ :: _, _ => rfl

/-- In Case B, appending `joinTwoRays` of the first two rays of `rs.filter (W.isGoodRay r Qs)` to
`Qs` produces `k + 1` far `H`-paths whose vertices lie in `Qs` or `rs`. -/
theorem caseB_spec (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {r k : ℕ} {c : Fin n} {rs : List (List (Fin n))} (hrs : W.IsStarRayList (2 * r) c rs)
    {Qs : List (List (Fin n))} (hQs : W.IsFarHPathList r Qs) (hlenQs : Qs.length = k)
    (hcQs : ∀ Q ∈ Qs, c ∉ Q)
    (hhits : ∀ Q ∈ Qs, (hitsOnQ rs Q).length < 2 * (k + 1))
    (hl : 2 * (k + 1) ^ 2 - (k + 1) + 3 ≤ rs.length) :
    let good := rs.filter (W.isGoodRay r Qs)
    let Q_new := joinTwoRays (good.headD []) ((good.drop 1).headD [])
    let Qs' := Qs ++ [Q_new]
    Qs'.length = k + 1 ∧
      W.IsFarHPathList r Qs' ∧
      (∀ R ∈ Qs', ∀ x ∈ R, (∃ Q ∈ Qs, x ∈ Q) ∨ (∃ P ∈ rs, x ∈ P)) := by
  intro good Q_new Qs'
  have hgood_len : 2 ≤ good.length :=
    W.two_le_length_filter_isGoodRay h2 he hW hrs hQs hlenQs hcQs hhits hl
  have h0 : 0 < good.length := by omega
  have h1 : 1 < good.length := by omega
  have hP₁_eq : good.headD [] = good[0]'h0 := headD_eq_getElem_zero [] good h0
  have hP₂_eq : (good.drop 1).headD [] = good[1]'h1 := drop_one_headD_eq_getElem_one [] good h1
  set P₁ := good.headD []
  set P₂ := (good.drop 1).headD []
  have hP₁_good : P₁ ∈ good := hP₁_eq ▸ List.getElem_mem h0
  have hP₂_good : P₂ ∈ good := hP₂_eq ▸ List.getElem_mem h1
  have hP₁_rs : P₁ ∈ rs := (List.mem_filter.mp hP₁_good).1
  have hP₂_rs : P₂ ∈ rs := (List.mem_filter.mp hP₂_good).1
  have hP₁_pred : W.isGoodRay r Qs P₁ = true := (List.mem_filter.mp hP₁_good).2
  have hP₂_pred : W.isGoodRay r Qs P₂ = true := (List.mem_filter.mp hP₂_good).2
  have hnd_good : good.Nodup := hrs.nodup.filter _
  have hne_12 : P₁ ≠ P₂ := by
    rw [hP₁_eq, hP₂_eq]
    intro heq
    rw [hnd_good.getElem_inj_iff] at heq
    omega
  obtain ⟨hneP₁, hneP₂, hneQ, hheadQ, hlastQ, hQ_new_valid, hmemQ⟩ :=
    W.joinTwoRays_props hrs.center_not_mem
      (hrs.rays_valid P₁ hP₁_rs) (hrs.rays_valid P₂ hP₂_rs)
      (fun v hv₁ hv₂ => hrs.eq_center_of_ne hP₁_rs hP₂_rs hne_12 hv₁ hv₂)
  have hgood_for_Q : ∀ P, W.isGoodRay r Qs P = true → ∀ Q ∈ Qs,
      rayMeetsPath Q P = false ∧ W.closeToHead r Q P = false ∧ W.closeToLast r Q P = false := by
    intro P hP Q hQ
    have hfor : W.isGoodRayForQ r Q P = true := List.all_eq_true.mp hP Q hQ
    unfold isGoodRayForQ at hfor
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hfor
    exact ⟨hfor.1, hfor.2.1, hfor.2.2⟩
  refine ⟨by simp [Qs', hlenQs], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro R hR
    rw [List.mem_append, List.mem_singleton] at hR
    rcases hR with hR | rfl
    · exact hQs.paths_valid R hR
    · exact hQ_new_valid
  · rw [List.pairwise_append]
    refine ⟨hQs.paths_disj, List.pairwise_singleton _ _, ?_⟩
    intro Q hQ R hR v hvQ hvR
    rw [List.mem_singleton] at hR
    subst hR
    rcases (hmemQ v).mp hvR with hvP₁ | hvP₂
    · have hnot_meet := (hgood_for_Q P₁ hP₁_pred Q hQ).1
      simp only [rayMeetsPath, List.any_eq_false, decide_eq_true_eq] at hnot_meet
      exact hnot_meet v hvP₁ hvQ
    · have hnot_meet := (hgood_for_Q P₂ hP₂_pred Q hQ).1
      simp only [rayMeetsPath, List.any_eq_false, decide_eq_true_eq] at hnot_meet
      exact hnot_meet v hvP₂ hvQ
  · intro R hR a b ha hb
    rw [List.mem_append, List.mem_singleton] at hR
    rcases hR with hR | rfl
    · exact hQs.ends_self_dist R hR a b ha hb
    · rw [List.head?_eq_some_head hneQ, Option.some.injEq] at ha
      rw [List.getLast?_eq_some_getLast hneQ, Option.some.injEq] at hb
      have h2r := hrs.brickDist_ge_of_ne h2 he hW hP₁_rs hP₂_rs hne_12
        (by rw [List.getLast?_eq_some_getLast hneP₁, ← hheadQ, ha])
        (by rw [List.getLast?_eq_some_getLast hneP₂, ← hlastQ, hb])
      omega
  · rw [List.pairwise_append]
    refine ⟨hQs.ends_pair_dist, List.pairwise_singleton _ _, ?_⟩
    intro Q hQ R hR a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂
    rw [List.mem_singleton] at hR
    subst hR
    obtain ⟨hne_Q, _, _, _, hheadQ_W, hlastQ_W, _, _⟩ := hQs.paths_valid Q hQ
    obtain ⟨_, _, _, _, hheadR_W, hlastR_W, _, _⟩ := hQ_new_valid
    have ha₁_W : a₁ ∈ W.vertexFinset := by
      rw [List.head?_eq_some_head hne_Q, Option.some.injEq] at ha₁
      exact ha₁ ▸ hheadQ_W
    have hb₁_W : b₁ ∈ W.vertexFinset := by
      rw [List.getLast?_eq_some_getLast hne_Q, Option.some.injEq] at hb₁
      exact hb₁ ▸ hlastQ_W
    have ha₂_W : a₂ ∈ W.vertexFinset := by
      rw [List.head?_eq_some_head hneQ, Option.some.injEq] at ha₂
      exact ha₂ ▸ hheadR_W
    have hb₂_W : b₂ ∈ W.vertexFinset := by
      rw [List.getLast?_eq_some_getLast hneQ, Option.some.injEq] at hb₂
      exact hb₂ ▸ hlastR_W
    have hu₁ : P₁.getLast? = some a₂ := by
      rw [List.head?_eq_some_head hneQ, Option.some.injEq] at ha₂
      rw [List.getLast?_eq_some_getLast hneP₁, ← hheadQ, ha₂]
    have hu₂ : P₂.getLast? = some b₂ := by
      rw [List.getLast?_eq_some_getLast hneQ, Option.some.injEq] at hb₂
      rw [List.getLast?_eq_some_getLast hneP₂, ← hlastQ, hb₂]
    obtain ⟨_, hhead₁, hlast₁⟩ := hgood_for_Q P₁ hP₁_pred Q hQ
    obtain ⟨_, hhead₂, hlast₂⟩ := hgood_for_Q P₂ hP₂_pred Q hQ
    simp only [closeToHead, ha₁] at hhead₁ hhead₂
    simp only [closeToLast, hb₁] at hlast₁ hlast₂
    have hd1 : r ≤ W.brickDist a₂ a₁ := W.brickDist_ge_of_not_closeToVert h2 he hu₁ hhead₁
    have hd2 : r ≤ W.brickDist b₂ a₁ := W.brickDist_ge_of_not_closeToVert h2 he hu₂ hhead₂
    have hd3 : r ≤ W.brickDist a₂ b₁ := W.brickDist_ge_of_not_closeToVert h2 he hu₁ hlast₁
    have hd4 : r ≤ W.brickDist b₂ b₁ := W.brickDist_ge_of_not_closeToVert h2 he hu₂ hlast₂
    rw [W.brickDist_comm_of_mem h2 he hW ha₂_W ha₁_W] at hd1
    rw [W.brickDist_comm_of_mem h2 he hW hb₂_W ha₁_W] at hd2
    rw [W.brickDist_comm_of_mem h2 he hW ha₂_W hb₁_W] at hd3
    rw [W.brickDist_comm_of_mem h2 he hW hb₂_W hb₁_W] at hd4
    exact ⟨hd1, hd2, hd3, hd4⟩
  · intro R hR x hx
    rw [List.mem_append, List.mem_singleton] at hR
    rcases hR with hR | rfl
    · exact Or.inl ⟨R, hR, hx⟩
    · rcases (hmemQ x).mp hx with hxP₁ | hxP₂
      · exact Or.inr ⟨P₁, hP₁_rs, hxP₁⟩
      · exact Or.inr ⟨P₂, hP₂_rs, hxP₂⟩

/-! ### Section 6: Inductive Construction of `k` Disjoint `H`-Paths (GM XIII (7.5)) -/

/-- One inductive step of GM XIII (7.5): given `k` disjoint `H`-paths `Qs` and the rays `rs` of the
`(k + 1)`-st star, either some `Q ∈ Qs` has `2 * (k + 1) ≤ (hitsOnQ rs Q).length` (Case A,
returning `buildCaseAPaths (k + 1) rs Q`) or at least two rays in `rs` are good for `Qs` (Case B,
appending `joinTwoRays` of the first two good rays to `Qs`). -/
def step75Step (r k : ℕ) (Qs : List (List (Fin n))) (rs : List (List (Fin n))) :
    List (List (Fin n)) :=
  match Qs.find? (fun Q => decide (2 * (k + 1) ≤ (hitsOnQ rs Q).length)) with
  | some Q => buildCaseAPaths (k + 1) rs Q
  | none =>
    let good := rs.filter (W.isGoodRay r Qs)
    Qs ++ [joinTwoRays (good.headD []) ((good.drop 1).headD [])]

theorem step75Step_spec (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {r k : ℕ} {c : Fin n} {rs : List (List (Fin n))} (hrs : W.IsStarRayList (2 * r) c rs)
    {Qs : List (List (Fin n))} (hQs : W.IsFarHPathList r Qs) (hlenQs : Qs.length = k)
    (hcQs : ∀ Q ∈ Qs, c ∉ Q)
    (hl : 2 * (k + 1) ^ 2 - (k + 1) + 3 ≤ rs.length) :
    let Qs' := W.step75Step r k Qs rs
    Qs'.length = k + 1 ∧
      W.IsFarHPathList r Qs' ∧
      (∀ R ∈ Qs', ∀ x ∈ R, (∃ Q ∈ Qs, x ∈ Q) ∨ (∃ P ∈ rs, x ∈ P)) := by
  dsimp only [step75Step]
  cases hfind : Qs.find? (fun Q => decide (2 * (k + 1) ≤ (hitsOnQ rs Q).length)) with
  | some Q =>
    have hQ_mem : Q ∈ Qs := List.mem_of_find?_eq_some hfind
    have hQ_hits : 2 * (k + 1) ≤ (hitsOnQ rs Q).length := by
      simpa [decide_eq_true_eq] using List.find?_some hfind
    obtain ⟨hlen, hfar, hmem⟩ := W.buildCaseAPaths_spec h2 he hW hrs
      (hQs.paths_valid Q hQ_mem) (hcQs Q hQ_mem) hQ_hits
    refine ⟨hlen, hfar, fun R hR x hx => ?_⟩
    rcases hmem R hR x hx with hxQ | hxrs
    · exact Or.inl ⟨Q, hQ_mem, hxQ⟩
    · exact Or.inr hxrs
  | none =>
    have hhits : ∀ Q ∈ Qs, (hitsOnQ rs Q).length < 2 * (k + 1) := by
      intro Q hQ
      have hfalse := List.find?_eq_none.mp hfind Q hQ
      simpa [decide_eq_true_eq] using hfalse
    exact W.caseB_spec h2 he hW hrs hQs hlenQs hcQs hhits hl

/-- Recursive implementation of the induction in GM XIII (7.5) (`lemma_7_5_claim`, page 91):
given `k` external `(l, 2 * r)`-stars `S : Fin k → List (List (Fin n))` with distinct centers
`v : Fin k → Fin n` (`l ≥ 2 * k^2 - k + 3`), constructs `k` mutually vertex-disjoint `H`-paths
whose ends have mutual brick distance `≥ r`. -/
def step75Rec (r : ℕ) : ∀ (k : ℕ),
    (Fin k → List (List (Fin n))) → (Fin k → Fin n) → List (List (Fin n))
  | 0, _, _ => []
  | k + 1, S, v =>
    let w := v (Fin.last k)
    let S' : Fin k → List (List (Fin n)) := fun a => filterAvoidVertex w (S a.castSucc)
    let v' : Fin k → Fin n := fun a => v a.castSucc
    let Qs := step75Rec r k S' v'
    W.step75Step r k Qs (S (Fin.last k))

theorem step75Rec_spec (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (r : ℕ) :
    ∀ (k : ℕ) (S : Fin k → List (List (Fin n))) (v : Fin k → Fin n),
      (∀ a : Fin k, W.IsStarRayList (2 * r) (v a) (S a)) →
      (∀ a : Fin k, 2 * k ^ 2 - k + 3 ≤ (S a).length) →
      Function.Injective v →
      let Qs := W.step75Rec r k S v
      Qs.length = k ∧
        W.IsFarHPathList r Qs ∧
        (∀ Q ∈ Qs, ∀ x ∈ Q, ∃ a : Fin k, ∃ P ∈ S a, x ∈ P)
  | 0, _, _, _, _, _ =>
    ⟨rfl, W.isFarHPathList_nil r, by simp [step75Rec]⟩
  | k + 1, S, v, hS, hl, hv => by
    dsimp only [step75Rec]
    set w := v (Fin.last k)
    let S' : Fin k → List (List (Fin n)) := fun a => filterAvoidVertex w (S a.castSucc)
    let v' : Fin k → Fin n := fun a => v a.castSucc
    have hS' : ∀ a : Fin k, W.IsStarRayList (2 * r) (v' a) (S' a) :=
      fun a => (hS a.castSucc).filterAvoidVertex w
    have hwc : ∀ a : Fin k, w ≠ v' a := fun a h =>
      (Fin.castSucc_lt_last a).ne (hv h).symm
    have hk1 : k + 1 ≤ 2 * (k + 1) ^ 2 := by nlinarith
    have hk0 : k ≤ 2 * k ^ 2 := by nlinarith
    have hl_step : 2 * k ^ 2 - k + 3 + 1 ≤ 2 * (k + 1) ^ 2 - (k + 1) + 3 := by
      zify [hk1, hk0]
      nlinarith
    have hl' : ∀ a : Fin k, 2 * k ^ 2 - k + 3 ≤ (S' a).length := by
      intro a
      have hge := (hS a.castSucc).length_filterAvoidVertex_ge (hwc a)
      have hla := hl a.castSucc
      dsimp only [S']
      omega
    have hv' : Function.Injective v' := hv.comp (Fin.castSucc_injective k)
    obtain ⟨hlenQs, hfarQs, hmemQs⟩ :=
      step75Rec_spec h2 he hW r k S' v' hS' hl' hv'
    set Qs := W.step75Rec r k S' v'
    have hw_not_Qs : ∀ Q ∈ Qs, w ∉ Q := by
      intro Q hQ hwQ
      rcases hmemQs Q hQ w hwQ with ⟨a, P, hP, hwP⟩
      exact (mem_filterAvoidVertex_iff.mp hP).2 hwP
    obtain ⟨hlen', hfar', hmem'⟩ :=
      W.step75Step_spec h2 he hW (hS (Fin.last k)) hfarQs hlenQs hw_not_Qs (hl (Fin.last k))
    refine ⟨hlen', hfar', fun R hR x hx => ?_⟩
    rcases hmem' R hR x hx with ⟨Q, hQ, hxQ⟩ | ⟨P, hP, hxP⟩
    · rcases hmemQs Q hQ x hxQ with ⟨a, P, hP, hxP⟩
      exact ⟨a.castSucc, P, (mem_filterAvoidVertex_iff.mp hP).1, hxP⟩
    · exact ⟨Fin.last k, P, hP, hxP⟩

end WallOfHeight

/-- Complete mathematical transformation of GM XIII (7.6) + (7.5): given a valid input
`x : Alg77Input p (2 * (p.choose 2) ^ 2 - p.choose 2 + 3) (2 * r + 4 * p.choose 2)` with `2 ≤ p`
and `2 ≤ r`, runs `runStep76` followed by `step75Rec` to produce a valid `Alg74Input p r` on the
same graph `x.G`. -/
def runStep75 {p r : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r)
    (x : Alg77Input p (2 * (p.choose 2) ^ 2 - p.choose 2 + 3) (2 * r + 4 * p.choose 2)) :
    Alg74Input p r :=
  let k := p.choose 2
  have hl3 : 3 ≤ 2 * k ^ 2 - k + 3 := by
    have : k ≤ 2 * k ^ 2 := by nlinarith
    omega
  have hm3 : 3 ≤ 2 * r := by omega
  let st := runStep76 hp hl3 hm3 x
  have hst := runStep76_spec hp hl3 hm3 x
  let S : Fin k → List (List (Fin x.n)) := fun a => WallOfHeight.starRayListOfFin (st.rays a)
  have hspec := st.W.step75Rec_spec hst.1.1 hst.1.2.1 hst.1.2.2 r k S x.centers
    (fun a => st.W.isStarRayList_starRayListOfFin (hst.2.1 a) (hst.2.2.1 a)
      (hst.2.2.2.1 a) (hst.2.2.2.2 a))
    (fun a => by simp [S, WallOfHeight.length_starRayListOfFin])
    x.hcenters
  hspec.2.1.toAlg74Input hst.1 hspec.1

theorem runStep75_n {p r : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r)
    (x : Alg77Input p (2 * (p.choose 2) ^ 2 - p.choose 2 + 3) (2 * r + 4 * p.choose 2)) :
    (runStep75 hp hr x).n = x.n := rfl

theorem runStep75_G {p r : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r)
    (x : Alg77Input p (2 * (p.choose 2) ^ 2 - p.choose 2 + 3) (2 * r + 4 * p.choose 2)) :
    (runStep75 hp hr x).G = x.G := rfl

theorem isAlg77Output_iff_isAlg74Output_runStep75 {p r : ℕ} (hp : 2 ≤ p) (hr : 2 ≤ r)
    (x : Alg77Input p (2 * (p.choose 2) ^ 2 - p.choose 2 + 3) (2 * r + 4 * p.choose 2))
    (out : List ℕ) :
    IsAlg77Output p x out ↔ IsAlg74Output p r (runStep75 hp hr x) out := Iff.rfl

end GraphMinor.Compute


