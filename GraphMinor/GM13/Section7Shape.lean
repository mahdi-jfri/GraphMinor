module

public import GraphMinor.GM13.Section7Naming

/-!
# Graph Minors XIII, Section 7: walls inside the wall of Fig. 1, on cells

In (7.3) a wall `H'` of height `h'` is found inside a wall `H` of height `h`, and `H'` is drawn
with the drawing it gets from `H`. We follow the cells of the grid through this.

A *cell wall* of height `h` (`CellWall`) records, for each element `m` of the elementary wall of
height `h` (a vertex or an edge, named by its cell in Fig. 1), the set `cells m` of grid cells
that the element occupies in the drawing, together with a naming of the squares by the faces of
the elementary wall (`FaceNaming`). The names around a cell of the element `m` are exactly the
faces at `m`. The wall of Fig. 1 is a cell wall in which every element occupies its own cell
(`CellWall.fig1`).

A *shape* (`Shape`) is the combinatorial part of the passage from `H` to `H'`. It says which
elements of the wall of height `h` are kept, and for each kept element the element of the wall of
height `h'` that contains it (`own`). It also sends each face of the wall of height `h` to the
face of the wall of height `h'` that contains it (`π`). Under local conditions on a shape, a cell
wall gives a new cell wall (`CellWall.transform`).

Finally, the distance comparison (i) of (7.3) for the new cell wall reduces to the same
comparison for the wall of Fig. 1 (`CellWall.transform_distGeSub`), and (ii) reduces to a bound
on faces (`CellWall.transform_le_planeWallDist`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-- The faces of the wall of height `h` at the cell `m`. -/
def cellFaces (h : ℕ) (m : ℤ × ℤ) : Set (ℤ × ℤ) := wallFace h '' squaresAbove m

/-- `F` is a face of the wall of height `h`: a brick or the outer face. -/
def IsWallFace (h : ℕ) (F : ℤ × ℤ) : Prop := IsBrick h F ∨ F = outFace

theorem isWallFace_of_mem_cellFaces {h : ℕ} {m F : ℤ × ℤ} (hF : F ∈ cellFaces h m) :
    IsWallFace h F := by
  obtain ⟨q, -, rfl⟩ := hF
  exact isBrick_or_eq_outFace_wallFace h q

/-! ## Cell walls -/

/-- A wall of height `h` drawn on the cells of the grid. -/
structure CellWall (h : ℕ) where
  /-- The cells of the drawing. -/
  𝒰 : Set (ℤ × ℤ)
  /-- The face of the wall that contains each square. -/
  name : ℤ × ℤ → ℤ × ℤ
  /-- The cells occupied by each element of the elementary wall. -/
  cells : ℤ × ℤ → Set (ℤ × ℤ)
  naming : FaceNaming 𝒰 h name
  U_eq : 𝒰 = ⋃ m ∈ fig1WallCells h, cells m
  disjoint : ∀ m₁ ∈ fig1WallCells h, ∀ m₂ ∈ fig1WallCells h, m₁ ≠ m₂ →
    Disjoint (cells m₁) (cells m₂)
  loc : ∀ m ∈ fig1WallCells h, ∀ c ∈ cells m, name '' squaresAbove c = cellFaces h m
  nonempty : ∀ m ∈ fig1WallCells h, (cells m).Nonempty

namespace CellWall

/-- The wall of Fig. 1 as a cell wall. -/
noncomputable def fig1 {h : ℕ} (hh : 1 ≤ h) (he : Even h) : CellWall h where
  𝒰 := fig1WallCells h
  name := wallFace h
  cells m := {m}
  naming := fig1FaceNaming hh he
  U_eq := by ext c; simp
  disjoint := fun _ _ _ _ hne => disjoint_singleton.mpr hne
  loc := by
    rintro m - c rfl
    rfl
  nonempty := fun m _ => singleton_nonempty m

variable {h : ℕ} (C : CellWall h)

theorem mem_U_iff {c : ℤ × ℤ} : c ∈ C.𝒰 ↔ ∃ m ∈ fig1WallCells h, c ∈ C.cells m := by
  rw [C.U_eq]
  simp

theorem name_mem_cellFaces {m c q : ℤ × ℤ} (hm : m ∈ fig1WallCells h) (hc : c ∈ C.cells m)
    (hq : q ∈ squaresAbove c) : C.name q ∈ cellFaces h m := by
  rw [← C.loc m hm c hc]
  exact ⟨q, hq, rfl⟩

theorem exists_name_eq {m c F : ℤ × ℤ} (hm : m ∈ fig1WallCells h) (hc : c ∈ C.cells m)
    (hF : F ∈ cellFaces h m) : ∃ q ∈ squaresAbove c, C.name q = F := by
  rw [← C.loc m hm c hc] at hF
  exact hF

end CellWall

/-! ## Shapes -/

/-- A step between two faces of the wall of height `h` across an element that is not kept. -/
def DelStep {h : ℕ} (own : ℤ × ℤ → Option (ℤ × ℤ)) (F G : ℤ × ℤ) : Prop :=
  ∃ m ∈ fig1WallCells h, own m = none ∧ F ∈ cellFaces h m ∧ G ∈ cellFaces h m

/-- The combinatorial passage from the wall of height `h` to a wall of height `h'` inside it. -/
structure Shape (h h' : ℕ) where
  /-- The element of the new wall that contains each kept element; `none` if not kept. -/
  own : ℤ × ℤ → Option (ℤ × ℤ)
  /-- The face of the new wall that contains each face. -/
  π : ℤ × ℤ → ℤ × ℤ
  own_mem : ∀ m ∈ fig1WallCells h, ∀ m', own m = some m' → m' ∈ fig1WallCells h'
  own_surj : ∀ m' ∈ fig1WallCells h', ∃ m ∈ fig1WallCells h, own m = some m'
  π_face : ∀ F, IsWallFace h F → IsWallFace h' (π F)
  π_surj : ∀ F', IsWallFace h' F' → ∃ F, IsWallFace h F ∧ π F = F'
  del : ∀ m ∈ fig1WallCells h, own m = none →
    ∀ F ∈ cellFaces h m, ∀ G ∈ cellFaces h m, π F = π G
  keep : ∀ m ∈ fig1WallCells h, ∀ m', own m = some m' → π '' cellFaces h m = cellFaces h' m'
  conn : ∀ F G, IsWallFace h F → IsWallFace h G → π F = π G →
    Relation.ReflTransGen (DelStep (h := h) own) F G

namespace Shape

variable {h h' : ℕ} (τ : Shape h h')

/-- The kept cells of the wall of Fig. 1. -/
def keptCells : Set (ℤ × ℤ) := {m | m ∈ fig1WallCells h ∧ τ.own m ≠ none}

end Shape

/-! ## The new cell wall -/

namespace CellWall

variable {h h' : ℕ} (C : CellWall h) (τ : Shape h h')

/-- The cells of each element of the new wall. -/
def tCells (m' : ℤ × ℤ) : Set (ℤ × ℤ) :=
  ⋃ m ∈ fig1WallCells h, ⋃ (_ : τ.own m = some m'), C.cells m

/-- The cells of the new drawing. -/
def t𝒰 : Set (ℤ × ℤ) := ⋃ m' ∈ fig1WallCells h', C.tCells τ m'

theorem mem_tCells {m' c : ℤ × ℤ} :
    c ∈ C.tCells τ m' ↔ ∃ m ∈ fig1WallCells h, τ.own m = some m' ∧ c ∈ C.cells m := by
  simp only [tCells, mem_iUnion, exists_prop]

theorem mem_t𝒰 {c : ℤ × ℤ} :
    c ∈ C.t𝒰 τ ↔ ∃ m ∈ fig1WallCells h, τ.own m ≠ none ∧ c ∈ C.cells m := by
  simp only [t𝒰, mem_iUnion, mem_tCells, exists_prop]
  constructor
  · rintro ⟨m', -, m, hm, hown, hc⟩
    exact ⟨m, hm, by rw [hown]; simp, hc⟩
  · rintro ⟨m, hm, hown, hc⟩
    obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hown
    exact ⟨m', τ.own_mem m hm m' hm', m, hm, hm', hc⟩

theorem t𝒰_subset : C.t𝒰 τ ⊆ C.𝒰 := by
  intro c hc
  obtain ⟨m, hm, -, hc⟩ := (C.mem_t𝒰 τ).mp hc
  exact (C.mem_U_iff).mpr ⟨m, hm, hc⟩

/-- A cell of an element that is not kept is not in the new drawing. -/
theorem not_mem_t𝒰 {m c : ℤ × ℤ} (hm : m ∈ fig1WallCells h) (hown : τ.own m = none)
    (hc : c ∈ C.cells m) : c ∉ C.t𝒰 τ := by
  intro hc'
  obtain ⟨m₂, hm₂, hown₂, hc₂⟩ := (C.mem_t𝒰 τ).mp hc'
  have hne : m ≠ m₂ := fun e => hown₂ (e ▸ hown)
  exact disjoint_left.mp (C.disjoint m hm m₂ hm₂ hne) hc hc₂

/-- Two faces joined by steps across elements that are not kept name squares at distance zero in
the new drawing. -/
theorem cellDist_eq_zero_of_reflTransGen {F G : ℤ × ℤ}
    (hFG : Relation.ReflTransGen (DelStep (h := h) τ.own) F G) :
    ∀ {r r' : ℤ × ℤ}, IsSquareCell r → IsSquareCell r' → C.name r = F → C.name r' = G →
      cellDist (C.t𝒰 τ) r r' = 0 := by
  induction hFG with
  | refl =>
    intro r r' hr hr' e e'
    have := C.naming.same r r' hr hr' (e.trans e'.symm)
    have := cellDist_mono (C.t𝒰_subset τ) r r'
    omega
  | tail _ hstep ih =>
    rename_i M G
    intro r r' hr hr' e e'
    obtain ⟨m, hm, hown, hM, hG⟩ := hstep
    obtain ⟨c, hc⟩ := C.nonempty m hm
    obtain ⟨a, ha, ea⟩ := C.exists_name_eq hm hc hM
    obtain ⟨b, hb, eb⟩ := C.exists_name_eq hm hc hG
    have h1 := ih hr ha.1 e ea
    have hcU := C.not_mem_t𝒰 τ hm hown hc
    have hbU : b ∉ C.t𝒰 τ := fun hb' => C.naming.not_square b (C.t𝒰_subset τ hb') hb.1
    have h2 := cellDist_le_one_of_common ha hb hbU
    have h2' : cellDist (C.t𝒰 τ) a b = 0 := by
      have s1 := cellDist_le_of_cellRel (C.t𝒰 τ) (Or.inr ha.2 : CellRel a c)
      have s2 := cellDist_le_of_cellRel (C.t𝒰 τ) (Or.inl hb.2 : CellRel c b)
      rw [cellInd_of_not_mem hcU] at s1
      rw [cellInd_of_not_mem hbU] at s2
      have := cellDist_triangle (C.t𝒰 τ) a c b
      omega
    have h3 := C.naming.same b r' hb.1 hr' (eb.trans e'.symm)
    have h3' := cellDist_mono (C.t𝒰_subset τ) b r'
    have t1 := cellDist_triangle (C.t𝒰 τ) r a b
    have t2 := cellDist_triangle (C.t𝒰 τ) r b r'
    omega

/-- The faces of the new wall at a cell of the drawing are equal or touch. -/
theorem eq_or_faceAdj_of_mem_cellFaces {h' : ℕ} {m F G : ℤ × ℤ} (hF : F ∈ cellFaces h' m)
    (hG : G ∈ cellFaces h' m) : F = G ∨ FaceAdj h' F G := by
  obtain ⟨q, hq, rfl⟩ := hF
  obtain ⟨q', hq', rfl⟩ := hG
  exact wallFace_eq_or_adj h' hq hq'

/-- **The new cell wall.** -/
noncomputable def transform (hh' : 1 ≤ h') (he' : Even h') : CellWall h' where
  𝒰 := C.t𝒰 τ
  name := τ.π ∘ C.name
  cells := C.tCells τ
  naming :=
    { not_square := fun c hc => C.naming.not_square c (C.t𝒰_subset τ hc)
      face := fun q => τ.π_face _ (C.naming.face q)
      free := by
        intro c hc q hq q' hq'
        by_cases hcU : c ∈ C.𝒰
        · obtain ⟨m, hm, hcm⟩ := (C.mem_U_iff).mp hcU
          have hown : τ.own m = none := by
            by_contra hne
            exact hc ((C.mem_t𝒰 τ).mpr ⟨m, hm, hne, hcm⟩)
          exact τ.del m hm hown _ (C.name_mem_cellFaces hm hcm hq) _
            (C.name_mem_cellFaces hm hcm hq')
        · show τ.π (C.name q) = τ.π (C.name q')
          rw [C.naming.free c hcU q hq q' hq']
      drawn := by
        intro c hc q hq q' hq'
        obtain ⟨m, hm, hown, hcm⟩ := (C.mem_t𝒰 τ).mp hc
        obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hown
        have hk := τ.keep m hm m' hm'
        have h1 : τ.π (C.name q) ∈ cellFaces h' m' := by
          rw [← hk]; exact mem_image_of_mem _ (C.name_mem_cellFaces hm hcm hq)
        have h2 : τ.π (C.name q') ∈ cellFaces h' m' := by
          rw [← hk]; exact mem_image_of_mem _ (C.name_mem_cellFaces hm hcm hq')
        exact eq_or_faceAdj_of_mem_cellFaces h1 h2
      same := by
        intro q q' hq hq' e
        exact C.cellDist_eq_zero_of_reflTransGen τ
          (τ.conn _ _ (C.naming.face q) (C.naming.face q') e) hq hq' rfl rfl
      adj := by
        intro F' G' hFG
        obtain ⟨x0, y0, x1, y1, m', h1, h2, h3, h4⟩ := exists_common_of_faceAdj hFG
        have hne : F' ≠ G' := by
          rintro rfl
          rcases hFG with ⟨-, -, hd⟩ | ⟨rfl, hb, -⟩ | ⟨rfl, hb, -⟩
          · rw [hexDist_self] at hd; omega
          · exact not_isBrick_outFace h' hb
          · exact not_isBrick_outFace h' hb
        have hm' : m' ∈ fig1WallCells h' := by
          by_contra hn
          exact hne (h1.symm.trans ((wallFace_eq_of_not_mem hh' he' hn h3 h4).trans h2))
        obtain ⟨m, hm, hown⟩ := τ.own_surj m' hm'
        have hk := τ.keep m hm m' hown
        have hF' : F' ∈ τ.π '' cellFaces h m := by
          rw [hk]; exact ⟨_, h3, h1⟩
        have hG' : G' ∈ τ.π '' cellFaces h m := by
          rw [hk]; exact ⟨_, h4, h2⟩
        obtain ⟨F, hF, rfl⟩ := hF'
        obtain ⟨G, hG, rfl⟩ := hG'
        obtain ⟨c, hc⟩ := C.nonempty m hm
        obtain ⟨a, ha, ea⟩ := C.exists_name_eq hm hc hF
        obtain ⟨b, hb, eb⟩ := C.exists_name_eq hm hc hG
        have hbU : b ∉ C.t𝒰 τ := fun hb' => C.naming.not_square b (C.t𝒰_subset τ hb') hb.1
        refine ⟨a, b, ha.1, hb.1, by simp [ea], by simp [eb],
          cellDist_le_one_of_common ha hb hbU⟩
      surj := by
        intro F' hF'
        obtain ⟨F, hF, rfl⟩ := τ.π_surj F' hF'
        obtain ⟨q, hq, e⟩ := C.naming.surj F hF
        exact ⟨q, hq, by simp [e]⟩ }
  U_eq := rfl
  disjoint := by
    intro m₁ hm₁ m₂ hm₂ hne
    rw [disjoint_left]
    intro c hc₁ hc₂
    obtain ⟨a, ha, hown_a, hca⟩ := (C.mem_tCells τ).mp hc₁
    obtain ⟨b, hb, hown_b, hcb⟩ := (C.mem_tCells τ).mp hc₂
    have hab : a ≠ b := by
      rintro rfl
      rw [hown_a] at hown_b
      exact hne (Option.some_injective _ hown_b)
    exact disjoint_left.mp (C.disjoint a ha b hb hab) hca hcb
  loc := by
    intro m' hm' c hc
    obtain ⟨m, hm, hown, hcm⟩ := (C.mem_tCells τ).mp hc
    rw [image_comp, C.loc m hm c hcm, τ.keep m hm m' hown]
  nonempty := by
    intro m' hm'
    obtain ⟨m, hm, hown⟩ := τ.own_surj m' hm'
    obtain ⟨c, hc⟩ := C.nonempty m hm
    exact ⟨c, (C.mem_tCells τ).mpr ⟨m, hm, hown, hc⟩⟩

end CellWall

/-! ## The two parts of (7.3) for the new cell wall -/

theorem faceDist_nonneg {h : ℕ} {F G : ℤ × ℤ} (hF : IsWallFace h F) (hG : IsWallFace h G) :
    0 ≤ faceDist h F G := by
  rcases hF with hb | ho <;> rcases hG with hb' | ho'
  · have h1 := hexDist_nonneg F G
    have h2 := one_le_outDepth hb
    have h3 := one_le_outDepth hb'
    rw [faceDist_of_ne (fun e => not_isBrick_outFace h (e ▸ hb))
      (fun e => not_isBrick_outFace h (e ▸ hb'))]
    exact le_min h1 (by omega)
  · rw [ho', faceDist_out_right (fun e => not_isBrick_outFace h (e ▸ hb))]
    have := one_le_outDepth hb
    omega
  · rw [ho, faceDist_out_left (fun e => not_isBrick_outFace h (e ▸ hb'))]
    have := one_le_outDepth hb'
    omega
  · rw [ho, ho', faceDist_out_out]

theorem squaresAbove_square {q : ℤ × ℤ} (hq : IsSquareCell q) : squaresAbove q = {q} := by
  ext r
  rw [mem_squaresAbove_iff, mem_singleton_iff]
  unfold IsSquareCell at hq
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact Prod.ext (by omega) (by omega)
  · rintro rfl
    exact ⟨hq.1, hq.2, Or.inl rfl, Or.inl rfl⟩

theorem exists_square_wallFace_eq {h : ℕ} {F : ℤ × ℤ} (hF : IsWallFace h F) :
    ∃ r, IsSquareCell r ∧ wallFace h r = F := by
  rcases hF with hF | rfl
  · exact ⟨brickSq F, ⟨by unfold brickSq; simp only; omega, by unfold brickSq; simp only; omega⟩,
      wallFace_brickSq hF⟩
  · exact ⟨outBase, ⟨by decide, by decide⟩, wallFace_outBase⟩

namespace Shape

variable {h h' : ℕ} (τ : Shape h h')

/-- **The distance comparison for the wall of Fig. 1.** For any two distinct cells and any faces
`F'`, `G'` of the new wall at them, there are faces `F`, `G` of the wall of Fig. 1 at them with
`[c] + [d] + D(F, G) ≤ [c]' + [d]' + D'(F', G') + K`. -/
def KI (K : ℕ) : Prop :=
  ∀ c d : ℤ × ℤ, c ≠ d → ∀ q₀ ∈ squaresAbove c, ∀ q₀' ∈ squaresAbove d,
    ∃ q ∈ squaresAbove c, ∃ q' ∈ squaresAbove d,
      (cellInd (fig1WallCells h) c + cellInd (fig1WallCells h) d : ℤ) +
          faceDist h (wallFace h q) (wallFace h q') ≤
        cellInd τ.keptCells c + cellInd τ.keptCells d +
          faceDist h' (τ.π (wallFace h q₀)) (τ.π (wallFace h q₀')) + K

/-- **Far from an element.** Every kept element differs from `mv`, and its faces are at face
distance at least `k - 2` from the faces at `mv`. -/
def Far (mv : ℤ × ℤ) (k : ℕ) : Prop :=
  ∀ m ∈ fig1WallCells h, τ.own m ≠ none → m ≠ mv ∧
    ∀ F ∈ cellFaces h m, ∀ G ∈ cellFaces h mv, (k : ℤ) ≤ faceDist h F G + 2

end Shape

namespace CellWall

variable {h h' : ℕ} (C : CellWall h) (τ : Shape h h')

/-- Each cell of the grid behaves, for both drawings, like a cell of the wall of Fig. 1. -/
theorem exists_fig1Cell (c : ℤ × ℤ) : ∃ κ : ℤ × ℤ,
    cellInd C.𝒰 c = cellInd (fig1WallCells h) κ ∧ cellInd (C.t𝒰 τ) c = cellInd τ.keptCells κ ∧
      C.name '' squaresAbove c = wallFace h '' squaresAbove κ := by
  by_cases hc : c ∈ C.𝒰
  · obtain ⟨m, hm, hcm⟩ := (C.mem_U_iff).mp hc
    refine ⟨m, by rw [cellInd_of_mem hc, cellInd_of_mem hm], ?_, C.loc m hm c hcm⟩
    by_cases hown : τ.own m = none
    · rw [cellInd_of_not_mem (C.not_mem_t𝒰 τ hm hown hcm),
        cellInd_of_not_mem (fun h : m ∈ τ.keptCells => h.2 hown)]
    · rw [cellInd_of_mem ((C.mem_t𝒰 τ).mpr ⟨m, hm, hown, hcm⟩),
        cellInd_of_mem (show m ∈ τ.keptCells from ⟨hm, hown⟩)]
  · have hu := cellUp_mem_squaresAbove c
    obtain ⟨r, hr, er⟩ := exists_square_wallFace_eq (C.naming.face (cellUp c))
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [cellInd_of_not_mem hc, cellInd_of_not_mem (fig1WallCells_not_square h r · hr)]
    · rw [cellInd_of_not_mem (fun h' => hc (C.t𝒰_subset τ h')),
        cellInd_of_not_mem (fun h' : r ∈ τ.keptCells => fig1WallCells_not_square h r h'.1 hr)]
    · rw [squaresAbove_square hr, image_singleton, er]
      ext F
      simp only [mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact C.naming.free c hc q hq _ hu
      · rintro rfl
        exact ⟨_, hu, rfl⟩

/-- **(i) of (7.3) on cells.** If the shape satisfies the distance comparison for the wall of
Fig. 1 with a constant `K ≥ 2`, then the new cell wall satisfies `d' ≥ d - K`. -/
theorem transform_distGeSub (hh' : 1 ≤ h') (he' : Even h') {K : ℕ} (hK : 2 ≤ K)
    (hKI : τ.KI K) :
    DistGeSub (planeWallDist (fig1PlaneEquiv '' cellSet (C.transform τ hh' he').𝒰))
      (planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰)) K := by
  refine C.naming.distGeSub (C.transform τ hh' he').naming K hK ?_
  intro c d hcd q₀ hq₀ q₀' hq₀'
  obtain ⟨κ, i1, i2, e1⟩ := C.exists_fig1Cell τ c
  obtain ⟨κ', i1', i2', e1'⟩ := C.exists_fig1Cell τ d
  have hU : (C.transform τ hh' he').𝒰 = C.t𝒰 τ := rfl
  rw [hU]
  have hn : ∀ q, (C.transform τ hh' he').name q = τ.π (C.name q) := fun _ => rfl
  simp only [hn]
  have hRHS : 0 ≤ faceDist h' (τ.π (C.name q₀)) (τ.π (C.name q₀')) :=
    faceDist_nonneg (τ.π_face _ (C.naming.face _)) (τ.π_face _ (C.naming.face _))
  by_cases hκ : κ = κ'
  · -- the same cell of the wall of Fig. 1: take one face at both ends
    have hu := cellUp_mem_squaresAbove c
    have hmem : C.name (cellUp c) ∈ C.name '' squaresAbove d := by
      rw [e1', ← hκ, ← e1]; exact ⟨_, hu, rfl⟩
    obtain ⟨q', hq', e⟩ := hmem
    refine ⟨cellUp c, hu, q', hq', ?_⟩
    rw [e, faceDist_self (C.naming.face _)]
    have := cellInd_le_one C.𝒰 c
    have := cellInd_le_one C.𝒰 d
    omega
  · have m₀ : C.name q₀ ∈ wallFace h '' squaresAbove κ := by rw [← e1]; exact ⟨_, hq₀, rfl⟩
    have m₀' : C.name q₀' ∈ wallFace h '' squaresAbove κ' := by rw [← e1']; exact ⟨_, hq₀', rfl⟩
    obtain ⟨r₀, hr₀, er₀⟩ := m₀
    obtain ⟨r₀', hr₀', er₀'⟩ := m₀'
    obtain ⟨r, hr, r', hr', hle⟩ := hKI κ κ' hκ r₀ hr₀ r₀' hr₀'
    have mr : wallFace h r ∈ C.name '' squaresAbove c := by rw [e1]; exact ⟨_, hr, rfl⟩
    have mr' : wallFace h r' ∈ C.name '' squaresAbove d := by rw [e1']; exact ⟨_, hr', rfl⟩
    obtain ⟨q, hq, eq⟩ := mr
    obtain ⟨q', hq', eq'⟩ := mr'
    refine ⟨q, hq, q', hq', ?_⟩
    rw [eq, eq', i1, i1', i2, i2', ← er₀, ← er₀']
    exact hle

/-- **(ii) of (7.3) on cells.** If the shape keeps nothing near the element `mv`, then every
point on the new drawing is at distance at least `k` from every point in the cells of `mv`. -/
theorem le_planeWallDist_of_far (hh' : 1 ≤ h') (he' : Even h') {mv : ℤ × ℤ} {k : ℕ}
    (hmv : mv ∈ fig1WallCells h) (hfar : τ.Far mv k) {s t : ℝ × ℝ}
    (hs : cellCode s ∈ (C.transform τ hh' he').𝒰) (ht : cellCode t ∈ C.cells mv) :
    k ≤ planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
  obtain ⟨m, hm, hown, hsm⟩ := (C.mem_t𝒰 τ).mp hs
  obtain ⟨hne, hF⟩ := hfar m hm hown
  have hst : cellCode s ≠ cellCode t := fun e =>
    disjoint_left.mp (C.disjoint m hm mv hmv hne) hsm (e ▸ ht)
  obtain ⟨q, hq, q', hq', hle⟩ := C.naming.le_planeWallDist hst
  have h1 := hF _ (C.name_mem_cellFaces hm hsm hq) _ (C.name_mem_cellFaces hmv ht hq')
  rw [cellInd_of_mem ((C.mem_U_iff).mpr ⟨m, hm, hsm⟩),
    cellInd_of_mem ((C.mem_U_iff).mpr ⟨mv, hmv, ht⟩)] at hle
  have h2 := faceDist_nonneg (C.naming.face q) (C.naming.face q')
  have h3 : ((faceDist h (C.name q) (C.name q')).toNat : ℤ) = faceDist h (C.name q) (C.name q') :=
    Int.toNat_of_nonneg h2
  omega

end CellWall

end GraphMinor.GM13
