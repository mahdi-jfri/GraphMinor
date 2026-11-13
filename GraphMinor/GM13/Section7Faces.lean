module

public import GraphMinor.GM13.Section7Cells

/-!
# Graph Minors XIII, Section 7: lower bounds on the wall distance from faces

The distance `d(s, t)` of a drawing made of cells (`Section7Cells.lean`) counts the points of
the drawing on an arc from `s` to `t`. An arc leaves `s`, runs through faces of the drawing, and
crosses the drawing to go from one face to the next. So a function `ψ` on faces that grows by at
most one between touching faces gives a lower bound for `d`.

Here a face is given by its name `face q` for each open unit square `q`. Two conditions make the
names a face structure: the squares around a cell outside the drawing have the same name, and the
names of the squares around a cell of the drawing are equal or touch (`Adj`). The main result is
`le_planeWallDist_of_faces`: if `ψ` vanishes on the faces at `s`, then
`[s] + [t] + ψ(F) ≤ d(s, t)` for some face `F` at `t`, where `[s]` is one if `s` is on the
drawing and zero otherwise.

The proof turns `ψ` into a potential on cells (`CellWalk.potential_le`), with the value
`[c] + min ψ` at a cell `c`. The start cell gets the value zero.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-- The open unit squares whose closure contains the cell `c`. -/
def squaresAbove (c : ℤ × ℤ) : Set (ℤ × ℤ) := {q | IsSquareCell q ∧ CellLE c q}

theorem cellUp_mem_squaresAbove (c : ℤ × ℤ) : cellUp c ∈ squaresAbove c :=
  ⟨isSquareCell_cellUp c, cellLE_cellUp c⟩

theorem squaresAbove_nonempty (c : ℤ × ℤ) : (squaresAbove c).Nonempty :=
  ⟨_, cellUp_mem_squaresAbove c⟩

/-- A square above `c'` is above every cell in the closure of `c'`. -/
theorem squaresAbove_anti {c c' : ℤ × ℤ} (h : CellLE c c') :
    squaresAbove c' ⊆ squaresAbove c :=
  fun _ hq => ⟨hq.1, h.trans hq.2⟩

/-- **Lower bound by a potential, counting the start.** A potential that grows by at most one
when an arc enters a cell of `𝒰`, and does not grow otherwise, bounds the distance: its value at
the cell of `t`, plus one if `s` is on the drawing, is at most its value at the cell of `s` plus
`d(s, t)`. -/
theorem potential_add_le_planeWallDist_cellSet {𝒰 : Set (ℤ × ℤ)}
    (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c) (φ : ℤ × ℤ → ℤ)
    (hφ : ∀ c c', CellRel c c' → φ c' ≤ φ c + cellInd 𝒰 c') {s t : ℝ × ℝ} (hst : s ≠ t) :
    φ (cellCode t) + cellInd 𝒰 (cellCode s) ≤ φ (cellCode s) +
      planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
  obtain ⟨L, hL, hfin, hcard⟩ := exists_line_ncard_eq_planeWallDist_cellSet h𝒰
    (fig1PlaneEquiv.injective.ne hst)
  obtain ⟨w, hw⟩ : ∃ w : CellWalk (cellCode s) (cellCode t),
      w.cost 𝒰 ≤ (L ∩ fig1PlaneEquiv '' cellSet 𝒰).ncard := by
    have := exists_cellWalk_of_line hL hfin
    rwa [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply] at this
  have h1 := CellWalk.potential_le 𝒰 φ hφ w
  have h2 := CellWalk.cost_eq_ind_add_costTail 𝒰 w
  rw [hcard] at hw
  have h3 : ((w.costTail 𝒰 + cellInd 𝒰 (cellCode s) : ℕ) : ℤ) ≤
      planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
    exact_mod_cast (show w.costTail 𝒰 + cellInd 𝒰 (cellCode s) ≤ _ by omega)
  push_cast at h3
  linarith

/-- The least value of `ψ` on the faces of the squares above `c`. -/
noncomputable def faceMin {Φ : Type*} (face : ℤ × ℤ → Φ) (ψ : Φ → ℕ) (c : ℤ × ℤ) : ℕ :=
  sInf ((fun q => ψ (face q)) '' squaresAbove c)

theorem faceMin_le {Φ : Type*} (face : ℤ × ℤ → Φ) (ψ : Φ → ℕ) {c q : ℤ × ℤ}
    (hq : q ∈ squaresAbove c) : faceMin face ψ c ≤ ψ (face q) :=
  Nat.sInf_le ⟨q, hq, rfl⟩

theorem exists_faceMin_eq {Φ : Type*} (face : ℤ × ℤ → Φ) (ψ : Φ → ℕ) (c : ℤ × ℤ) :
    ∃ q ∈ squaresAbove c, ψ (face q) = faceMin face ψ c := by
  have hne : ((fun q => ψ (face q)) '' squaresAbove c).Nonempty :=
    (squaresAbove_nonempty c).image _
  obtain ⟨q, hq, hq'⟩ := Nat.sInf_mem hne
  exact ⟨q, hq, hq'⟩

/-- **Lower bound on the distance from faces.** Let every open unit square `q` have a face name
`face q`, such that the squares around a cell outside `𝒰` have the same name, and the names of
the squares around a cell of `𝒰` are equal or touch. Let `ψ` grow by at most one between touching
faces and vanish on the faces at `s`. Then for some face `F` at `t`,
`[s] + [t] + ψ(F) ≤ d(s, t)`. -/
theorem le_planeWallDist_of_faces {Φ : Type*} {𝒰 : Set (ℤ × ℤ)}
    (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c) (face : ℤ × ℤ → Φ) (Adj : Φ → Φ → Prop)
    (hfree : ∀ c ∉ 𝒰, ∀ q ∈ squaresAbove c, ∀ q' ∈ squaresAbove c, face q = face q')
    (hdrawn : ∀ c ∈ 𝒰, ∀ q ∈ squaresAbove c, ∀ q' ∈ squaresAbove c,
      face q = face q' ∨ Adj (face q) (face q'))
    (ψ : Φ → ℕ) (hψ : ∀ F G, Adj F G → ψ G ≤ ψ F + 1)
    {s t : ℝ × ℝ} (hst : cellCode s ≠ cellCode t)
    (hs : ∀ q ∈ squaresAbove (cellCode s), ψ (face q) = 0) :
    ∃ q ∈ squaresAbove (cellCode t),
      cellInd 𝒰 (cellCode s) + cellInd 𝒰 (cellCode t) + ψ (face q) ≤
        planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
  classical
  set cs := cellCode s
  set m := faceMin face ψ
  -- The values of `ψ` on two squares above one cell differ by at most one at a drawn cell and
  -- not at all at a free cell.
  have hstep : ∀ c, ∀ q ∈ squaresAbove c, ∀ q' ∈ squaresAbove c,
      ψ (face q') ≤ ψ (face q) + cellInd 𝒰 c := by
    intro c q hq q' hq'
    by_cases hc : c ∈ 𝒰
    · rw [cellInd_of_mem hc]
      rcases hdrawn c hc q hq q' hq' with h | h
      · rw [h]; omega
      · exact hψ _ _ h
    · rw [cellInd_of_not_mem hc, hfree c hc q hq q' hq']
      omega
  -- The minimum at `c'` is at most the minimum at a related cell `c` plus `[c]`.
  have hmin : ∀ c c', CellRel c c' → m c' ≤ m c + cellInd 𝒰 c := by
    intro c c' hrel
    obtain ⟨q, hq, hqm⟩ := exists_faceMin_eq face ψ c
    rcases hrel with hle | hle
    · obtain ⟨q', hq', -⟩ := exists_faceMin_eq face ψ c'
      have h1 := faceMin_le face ψ hq'
      have h2 := hstep c q hq q' (squaresAbove_anti hle hq')
      change m c' ≤ ψ (face q') at h1
      change ψ (face q) = m c at hqm
      omega
    · have h1 := faceMin_le face ψ (squaresAbove_anti hle hq)
      change m c' ≤ ψ (face q) at h1
      change ψ (face q) = m c at hqm
      omega
  have hms : m cs = 0 := by
    obtain ⟨q, hq, hqm⟩ := exists_faceMin_eq face ψ cs
    show faceMin face ψ cs = 0
    rw [← hqm, hs q hq]
  -- The potential: zero at the start cell if it is drawn, `[c] + m c` elsewhere.
  let φ : ℤ × ℤ → ℤ := fun c =>
    if c = cs ∧ cs ∈ 𝒰 then 0 else (cellInd 𝒰 c : ℤ) + m c
  have hφ : ∀ c c', CellRel c c' → φ c' ≤ φ c + cellInd 𝒰 c' := by
    intro c c' hrel
    by_cases h' : c' = cs ∧ cs ∈ 𝒰
    · simp only [φ, h', and_self, ↓reduceIte]
      split_ifs <;> positivity
    · simp only [φ, h', ↓reduceIte]
      by_cases h : c = cs ∧ cs ∈ 𝒰
      · simp only [h, and_self, ↓reduceIte]
        obtain ⟨rfl, -⟩ := h
        have := hmin c' cs hrel.symm
        rw [hms] at this
        have : m c' = 0 := by
          obtain ⟨q, hq, hqm⟩ := exists_faceMin_eq face ψ cs
          rcases hrel with hle | hle
          · obtain ⟨q', hq', -⟩ := exists_faceMin_eq face ψ c'
            have := hs q' (squaresAbove_anti hle hq')
            have := faceMin_le face ψ hq'
            change m c' ≤ ψ (face q') at this
            omega
          · have := faceMin_le face ψ (squaresAbove_anti hle hq)
            change m c' ≤ ψ (face q) at this
            have := hs q hq
            omega
        rw [this]; simp
      · simp only [h, ↓reduceIte]
        have := hmin c c' hrel
        omega
  have hne : s ≠ t := fun h => hst (by simp [cs, h])
  have key := potential_add_le_planeWallDist_cellSet h𝒰 φ hφ hne
  have hφs : φ cs = 0 := by
    by_cases hcs : cs ∈ 𝒰
    · simp [φ, hcs]
    · simp [φ, hcs, hms, cellInd_of_not_mem hcs]
  have hφt : φ (cellCode t) = cellInd 𝒰 (cellCode t) + m (cellCode t) := by
    have : ¬ (cellCode t = cs ∧ cs ∈ 𝒰) := fun h => hst h.1.symm
    simp [φ, this]
  obtain ⟨q, hq, hqm⟩ := exists_faceMin_eq face ψ (cellCode t)
  refine ⟨q, hq, ?_⟩
  rw [hφs, hφt] at key
  change ψ (face q) = m (cellCode t) at hqm
  have : ((cellInd 𝒰 cs + cellInd 𝒰 (cellCode t) + ψ (face q) : ℕ) : ℤ) ≤
      planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
    push_cast; rw [hqm]; linarith
  exact_mod_cast this

end GraphMinor.GM13
