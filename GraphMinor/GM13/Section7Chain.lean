module

public import GraphMinor.GM13.Section7ThreeWall

/-!
# Graph Minors XIII, (7.3): chains of steps

(7.3) asks for a wall `H'` of height `h - 2r - 2` inside a wall `H` of height `h`, with
`d' ≥ d - 4r - 4`, and with no vertex `u` of `H'` at distance `≤ r` from a given vertex `v`. We
build `H'` by a *chain* of steps (`Chain`). Each step is a shape (`Shape`) with a realization and
the distance comparison `KI K` for some `K ≥ 2`. The constants `K` of the steps add up.

* `Shape.DepthTestK`: a version of the depth test of `Section7KI.lean` with a parameter, which
  gives `KI (2 K)`. It is used for the translated subwalls of height `h - 2k`.
* `Chain.run`: a chain of steps applied to a wall `W` drawn on the cells of a cell wall `C`
  gives a wall `W' ≤ W`, drawn on the cells of a cell wall `C'`, whose distance on cells is at
  least that of `C` minus the sum of the constants. If `C` is a homeomorphic image of Fig. 1, so
  is `C'`. Every cell of `C'` is a cell of an element of
  `W` that the chain keeps.
* `Chain.Far`: every element that the chain keeps is far from the element `mv` (its faces are at
  face distance at least `k - 2` from the faces at `mv`). For the wall of Fig. 1 this gives
  `d(u, v) ≥ k` for every vertex `u` of the new wall (`le_planeWallDist_fig1_of_far`).
* `exists_induced_of_far_chains`: if for every element there is a chain of the right height and
  constant that is far from it, then (7.3) holds for `r`, with `H'` drawn as its drawing induced
  by `H`, and this drawing is as in Fig. 1.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

/-! ## The depth test with a parameter -/

/-- The comparison of two faces, with a loss `L` on hex distances. -/
theorem faceDist_le_of_depths' {h h' : ℕ} (π : ℤ × ℤ → ℤ × ℤ) (hπ : π outFace = outFace)
    {L : ℤ}
    (hS1 : ∀ F G, IsBrick h F → IsBrick h G → IsBrick h' (π F) → IsBrick h' (π G) →
      hexDist F G ≤ hexDist (π F) (π G) + L)
    {F G : ℤ × ℤ} (hF : IsWallFace h F) (hG : IsWallFace h G) (hF' : IsWallFace h' (π F))
    (hG' : IsWallFace h' (π G)) {a b : ℤ} (hab : L ≤ a + b)
    (ha : faceDepth h F ≤ faceDepth h' (π F) + a) (hb : faceDepth h G ≤ faceDepth h' (π G) + b) :
    faceDist h F G ≤ faceDist h' (π F) (π G) + (a + b) := by
  have hle := faceDist_le_faceDepth h F G
  by_cases hout : π F = outFace ∨ π G = outFace
  · rw [faceDist_eq_faceDepth hout]
    omega
  · push Not at hout
    have hFo : F ≠ outFace := fun e => hout.1 (e ▸ hπ)
    have hGo : G ≠ outFace := fun e => hout.2 (e ▸ hπ)
    have hFb : IsBrick h F := hF.resolve_right hFo
    have hGb : IsBrick h G := hG.resolve_right hGo
    have hFb' : IsBrick h' (π F) := hF'.resolve_right hout.1
    have hGb' : IsBrick h' (π G) := hG'.resolve_right hout.2
    have h1 := hS1 F G hFb hGb hFb' hGb'
    rw [faceDist_of_ne hFo hGo, faceDist_of_ne hout.1 hout.2]
    simp only [faceDepth, hFo, hGo, hout.1, hout.2, ite_false] at ha hb
    omega

namespace Shape

variable {h h' : ℕ} (τ : Shape h h')

/-- The depth test with a parameter `K ≥ 1`: hex distances drop by at most `2K - 2`, depths of
bricks by at most `K`, and every deleted element has a face whose depth drops by at most
`K - 1`. For `K = 2` it is `DepthTest`. -/
structure DepthTestK (K : ℕ) : Prop where
  one_le : 1 ≤ K
  out : τ.π outFace = outFace
  hex : ∀ F G, IsBrick h F → IsBrick h G → IsBrick h' (τ.π F) → IsBrick h' (τ.π G) →
    hexDist F G ≤ hexDist (τ.π F) (τ.π G) + (2 * K - 2 : ℕ)
  brick : ∀ F, IsBrick h F → faceDepth h F ≤ faceDepth h' (τ.π F) + K
  del : ∀ m ∈ fig1WallCells h, τ.own m = none →
    ∃ q ∈ squaresAbove m, faceDepth h (wallFace h q) ≤ faceDepth h' (τ.π (wallFace h q)) + (K - 1 : ℕ)

variable {τ}

/-- At each cell, a face whose depth pays for the cell. -/
theorem DepthTestK.exists_face {K : ℕ} (hT : τ.DepthTestK K) (c : ℤ × ℤ) {q₀ : ℤ × ℤ}
    (hq₀ : q₀ ∈ squaresAbove c) :
    ∃ q ∈ squaresAbove c, τ.π (wallFace h q) = τ.π (wallFace h q₀) ∧
      (cellInd (fig1WallCells h) c : ℤ) - cellInd τ.keptCells c ≤ 1 ∧
      0 ≤ (cellInd (fig1WallCells h) c : ℤ) - cellInd τ.keptCells c ∧
      (cellInd (fig1WallCells h) c : ℤ) - cellInd τ.keptCells c + faceDepth h (wallFace h q) ≤
        faceDepth h' (τ.π (wallFace h q)) + K := by
  have hK := hT.one_le
  have hface := isBrick_or_eq_outFace_wallFace h q₀
  have hgen : faceDepth h (wallFace h q₀) ≤ faceDepth h' (τ.π (wallFace h q₀)) + K := by
    rcases hface with hb | ho
    · exact hT.brick _ hb
    · have := faceDepth_nonneg (τ.π_face _ (Or.inr ho))
      have h0 : faceDepth h (wallFace h q₀) = 0 := by rw [ho]; simp [faceDepth]
      omega
  by_cases hc : c ∈ fig1WallCells h
  · by_cases hown : τ.own c = none
    · obtain ⟨q, hq, hle⟩ := hT.del c hc hown
      have he := τ.del c hc hown _ ⟨q, hq, rfl⟩ _ ⟨q₀, hq₀, rfl⟩
      refine ⟨q, hq, he, ?_, ?_, ?_⟩ <;>
      rw [cellInd_of_mem hc, cellInd_of_not_mem (fun h' : c ∈ τ.keptCells => h'.2 hown)] <;>
      push_cast at hle ⊢ <;> omega
    · refine ⟨q₀, hq₀, rfl, ?_, ?_, ?_⟩ <;>
      rw [cellInd_of_mem hc, cellInd_of_mem (show c ∈ τ.keptCells from ⟨hc, hown⟩)] <;>
      push_cast <;> omega
  · refine ⟨q₀, hq₀, rfl, ?_, ?_, ?_⟩ <;>
    rw [cellInd_of_not_mem hc, cellInd_of_not_mem (fun h' : c ∈ τ.keptCells => hc h'.1)] <;>
    push_cast <;> omega

/-- **The test with parameter `K` gives `KI (2 K)`.** -/
theorem DepthTestK.ki {K : ℕ} (hT : τ.DepthTestK K) : τ.KI (2 * K) := by
  intro c d _ q₀ hq₀ q₀' hq₀'
  obtain ⟨q, hq, e, h1, h0, h2⟩ := hT.exists_face c hq₀
  obtain ⟨q', hq', e', h1', h0', h2'⟩ := hT.exists_face d hq₀'
  refine ⟨q, hq, q', hq', ?_⟩
  have hK := hT.one_le
  have hF := isBrick_or_eq_outFace_wallFace h q
  have hG := isBrick_or_eq_outFace_wallFace h q'
  have hhex : ∀ F G, IsBrick h F → IsBrick h G → IsBrick h' (τ.π F) → IsBrick h' (τ.π G) →
      hexDist F G ≤ hexDist (τ.π F) (τ.π G) + (2 * K - 2 : ℤ) := by
    intro F G a b c' d'
    have := hT.hex F G a b c' d'
    push_cast [Nat.cast_sub (by omega : 2 ≤ 2 * K)] at this
    exact this
  have key := faceDist_le_of_depths' τ.π hT.out hhex hF hG (τ.π_face _ hF) (τ.π_face _ hG)
    (a := K - ((cellInd (fig1WallCells h) c : ℤ) - cellInd τ.keptCells c))
    (b := K - ((cellInd (fig1WallCells h) d : ℤ) - cellInd τ.keptCells d)) (by omega)
    (by omega) (by omega)
  rw [← e, ← e']
  push_cast
  omega

end Shape

/-! ## Chains of steps -/

/-- A step of (7.3): a shape from height `h` to height `h'`, with a realization and the distance
comparison `KI K`. The realization keeps the rays of the side vertices out of the kept cells and
keeps the order of the rows, so that the new cell wall stays a homeomorphic image of Fig. 1
(`CellWall.IsFig1Homeo.transform`). -/
structure Step (h h' K : ℕ) where
  /-- The shape. -/
  τ : Shape h h'
  /-- A realization of the shape by paths. -/
  R : τ.Realization
  ki : τ.KI K
  two_le : 2 ≤ K
  pos : 1 ≤ h'
  even : Even h'
  rayOK : R.RayOK
  rowMono : R.RowMono

/-- A chain of steps from height `h` to height `h'`, whose constants add up to `K`. -/
inductive Chain : ℕ → ℕ → ℕ → Type
  | nil (h : ℕ) : Chain h h 0
  | cons {h h₁ h' K₁ K₂ : ℕ} (s : Step h h₁ K₁) (c : Chain h₁ h' K₂) : Chain h h' (K₁ + K₂)

namespace Chain

/-- The element of the last wall that contains the element `m` of the first wall, if it is kept
by every step. -/
def own : {h h' K : ℕ} → Chain h h' K → ℤ × ℤ → Option (ℤ × ℤ)
  | _, _, _, .nil _, m => some m
  | _, _, _, .cons s c, m => (s.τ.own m).bind c.own

/-- **The chain is far from the element `mv`**: every element that it keeps differs from `mv`,
and its faces are at face distance at least `k - 2` from the faces at `mv`. -/
def Far {h h' K : ℕ} (c : Chain h h' K) (mv : ℤ × ℤ) (k : ℕ) : Prop :=
  ∀ m ∈ fig1WallCells h, c.own m ≠ none → m ≠ mv ∧
    ∀ F ∈ cellFaces h m, ∀ G ∈ cellFaces h mv, (k : ℤ) ≤ faceDist h F G + 2

variable {α : Type u} {β : Type v}

/-- **A chain applied to a wall drawn on cells.** -/
theorem run {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane} :
    ∀ {h h' K : ℕ} (c : Chain h h' K) {W : Wall α β} {C : CellWall W.height},
      DrawnOnCells Γ W C → C.IsFig1Homeo → W.height = h →
      ∃ (W' : Wall α β) (C' : CellWall W'.height), W'.graph ≤ W.graph ∧ W'.height = h' ∧
        DrawnOnCells Γ W' C' ∧ C'.IsFig1Homeo ∧
        DistGeSub (planeWallDist (fig1PlaneEquiv '' cellSet C'.𝒰))
          (planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰)) K ∧
        ∀ c' ∈ C'.𝒰, ∃ m ∈ fig1WallCells h, c' ∈ C.cells m ∧ c.own m ≠ none
  | _, _, _, .nil _, W, C, hD, hC, e => by
    subst e
    refine ⟨W, C, le_rfl, rfl, hD, hC, fun s t => by simp, fun c' hc' => ?_⟩
    obtain ⟨m, hm, hcm⟩ := (C.mem_U_iff).mp hc'
    exact ⟨m, hm, hcm, by simp [own]⟩
  | _, _, _, .cons s c, W, C, hD, hC, e => by
    subst e
    have hD₁ := hD.wall s.R s.pos s.even
    have hC₁ := hC.transform s.R W.two_le_height W.even_height s.pos s.even s.rayOK s.rowMono
    obtain ⟨W', C', hle, hh, hD', hC', hd, hcells⟩ := c.run hD₁ hC₁ rfl
    refine ⟨W', C', hle.trans (s.R.wall_graph_le W s.pos s.even), hh, hD', hC', ?_, ?_⟩
    · intro x y
      have h1 := C.transform_distGeSub s.τ s.pos s.even s.two_le s.ki x y
      have h2 := hd x y
      have h3 := h1.trans (Nat.add_le_add_right h2 _)
      change _ ≤ _ + (_ + _)
      omega
    · intro c' hc'
      obtain ⟨m₁, -, hcm₁, hown₁⟩ := hcells c' hc'
      obtain ⟨m, hm, hown, hcm⟩ := (C.mem_tCells s.τ).mp hcm₁
      refine ⟨m, hm, hcm, ?_⟩
      simp only [own, hown, Option.bind_some]
      exact hown₁

end Chain

/-! ## Far elements of the wall of Fig. 1 -/

/-- If every cell of a set `S` is a far element of the wall of Fig. 1 of height `h`, then every
point in a cell of `S` is at distance at least `k` from every point in the cell `mv`. -/
theorem le_planeWallDist_fig1_of_far {h : ℕ} (hh : 1 ≤ h) (he : Even h) {mv : ℤ × ℤ} {k : ℕ}
    {S : Set (ℤ × ℤ)}
    (hS : ∀ m ∈ S, m ∈ fig1WallCells h ∧ m ≠ mv ∧
      ∀ F ∈ cellFaces h m, ∀ G ∈ cellFaces h mv, (k : ℤ) ≤ faceDist h F G + 2)
    (hmv : mv ∈ fig1WallCells h) {s t : ℝ × ℝ} (hs : cellCode s ∈ S) (ht : cellCode t = mv) :
    k ≤ planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells h)) (fig1PlaneEquiv s)
      (fig1PlaneEquiv t) := by
  obtain ⟨hm, hne, hF⟩ := hS _ hs
  have hst : cellCode s ≠ cellCode t := ht ▸ hne
  obtain ⟨q, hq, q', hq', hle⟩ := (fig1FaceNaming hh he).le_planeWallDist hst
  have h1 := hF _ ⟨q, hq, rfl⟩ _ ⟨q', ht ▸ hq', rfl⟩
  rw [cellInd_of_mem hm, cellInd_of_mem (ht ▸ hmv)] at hle
  have h2 := faceDist_nonneg (isBrick_or_eq_outFace_wallFace h q)
    (isBrick_or_eq_outFace_wallFace h q')
  have h3 : ((faceDist h (wallFace h q) (wallFace h q')).toNat : ℤ) =
      faceDist h (wallFace h q) (wallFace h q') := Int.toNat_of_nonneg h2
  omega

variable {α : Type u} {β : Type v}

/-- **(7.3) from chains.** Let `H` be a wall drawn as in Fig. 1, `v` a vertex of `H` and `r` a
number. If for every element `mv` of the wall of Fig. 1 of the height of `H` there is a chain from
height `h` to height `h - 2r - 2` with constant at most `4r + 4` that is far from `mv` (`Chain.Far mv
(r + 1)`), then there is a wall `H' ≤ H` of height `h - 2r - 2`, drawn with the drawing it gets
from `H`, with `d' ≥ d - 4r - 4` and no vertex `u` with `d(u, v) ≤ r`. This drawing of `H'` is
again as in Fig. 1, since the chain keeps the cell wall a homeomorphic image of Fig. 1
(`Chain.run`, `DrawnWall.isFigure1_of_drawnOnCells`). -/
theorem exists_induced_of_far_chains (H : DrawnWall α β) (v : α) (r : ℕ) (hF : H.IsFigure1)
    (hv : v ∈ V(H.graph))
    (hc : ∀ mv ∈ fig1WallCells H.height,
      ∃ K ≤ 4 * r + 4, ∃ c : Chain H.height (H.height - 2 * r - 2) K, c.Far mv (r + 1)) :
    ∃ H' : DrawnWall α β,
      H'.IsFigure1 ∧
      H'.graph ≤ H.graph ∧ H'.drawingU ⊆ H.drawingU ∧ H'.vertexPoint = H.vertexPoint ∧
      H'.height = H.height - 2 * r - 2 ∧ DistGeSub H'.planeDist H.planeDist (4 * r + 4) ∧
      (∀ u ∈ V(H'.graph), ¬ H.dist u v ≤ r) ∧
      ∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ : GraphDrawing H.graph EuclideanPlane),
        IsFigure1CoordDrawing H.toWall Γ ∧ H.drawingU = φ '' Γ.drawing.U ∧
        (∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1) ∧
        H'.drawingU = φ '' indU Γ H'.toWall := by
  obtain ⟨φ, Γ, hΓ, hU, hP⟩ := hF
  have hh1 : 1 ≤ H.height := by have := H.toWall.two_le_height; omega
  have hD := drawnOnCells_fig1 hΓ hh1 H.even_height
  obtain ⟨mv, hmv, hvm⟩ := H.toWall.exists_mem_elemV hv
  obtain ⟨K, hK, c, hfar⟩ := hc mv hmv
  obtain ⟨W', C', hle, hht, hD', hC', hdist, hcells⟩ :=
    c.run hD (CellWall.isFig1Homeo_fig1 hh1 H.even_height) rfl
  have hP' : ∀ u ∈ V(H.graph), H.vertexPoint u = φ (ptV Γ u) := fun u hu => by
    rw [hP u hu, ptV_of_mem Γ hu]
  have hUH : Γ.drawing.U = fig1PlaneEquiv '' cellSet (CellWall.fig1 hh1 H.even_height).𝒰 := by
    rw [hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
    rfl
  let H' : DrawnWall α β :=
    { W' with
      drawingU := φ '' indU Γ W'
      vertexPoint := H.vertexPoint
      vertexPoint_mem := fun u hu => by
        rw [hP' u (hle.vertexSet_mono hu)]
        exact ⟨ptV Γ u, Or.inl ⟨u, hu, rfl⟩, rfl⟩
      vertexPoint_injOn := H.vertexPoint_injOn.mono hle.vertexSet_mono }
  refine ⟨H', H'.isFigure1_of_drawnOnCells hle hD' hC' φ rfl
    (fun u hu => hP' u (hle.vertexSet_mono hu)), hle, ?_, rfl, hht, ?_, ?_, φ, Γ, hΓ, hU, hP, rfl⟩
  · -- the drawing of `H'` is part of that of `H`
    rw [hU]
    exact image_mono (indU_subset Γ W' hle)
  · -- (i)
    intro s t
    obtain ⟨s₀, rfl⟩ := φ.surjective s
    obtain ⟨t₀, rfl⟩ := φ.surjective t
    change planeWallDist H.drawingU (φ s₀) (φ t₀) ≤
      planeWallDist (φ '' indU Γ W') (φ s₀) (φ t₀) + (4 * r + 4)
    rw [hU, planeWallDist_image_homeomorph, planeWallDist_image_homeomorph, hUH, hD'.indU_eq]
    have := hdist s₀ t₀
    omega
  · -- (ii)
    intro u hu
    have huH := hle.vertexSet_mono hu
    -- the point of `u` lies in a cell of `C'`, the point of `v` in the cell `mv`
    have hu' : ptV Γ u ∈ fig1PlaneEquiv '' cellSet C'.𝒰 := by
      rw [← hD'.indU_eq]
      exact Or.inl ⟨u, hu, rfl⟩
    obtain ⟨s, hs, hs'⟩ := hu'
    have hv' : ptV Γ v ∈ fig1PlaneEquiv '' cellSet ((CellWall.fig1 hh1 H.even_height).cells mv) := by
      rw [← hD mv hmv]
      exact Or.inl ⟨v, hvm, rfl⟩
    obtain ⟨t, ht, ht'⟩ := hv'
    have ht2 : cellCode t = mv := ht
    have hkey := le_planeWallDist_fig1_of_far hh1 H.even_height (k := r + 1)
      (S := {m | m ∈ fig1WallCells H.height ∧ c.own m ≠ none})
      (fun m hm => ⟨hm.1, hfar m hm.1 hm.2⟩) hmv (s := s) (t := t) ?_ ht2
    · rw [DrawnWall.dist, DrawnWall.planeDist, hP' u huH, hP' v hv, hU,
        planeWallDist_image_homeomorph, hUH, ← hs', ← ht']
      change ¬ planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height)) _ _ ≤ r
      omega
    · obtain ⟨m, hm, hcm, hown⟩ := hcells _ hs
      have : cellCode s = m := hcm
      exact ⟨this ▸ hm, this ▸ hown⟩

end GraphMinor.GM13
