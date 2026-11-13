module

public import GraphMinor.Compute.MultiDigraph
public import GraphMinor.Compute.Bridge13
public import GraphMinor.GM13.Section7Build

/-!
# Shared Elementary Wall and Wall of Height `h` Representation (`GraphMinor/Compute/Wall.lean`)

This file provides the shared Word RAM representation of the elementary wall of height `h` and a
wall of height `h` (`WallOfHeight h G`, GM XIII Sections 7 & 9, pages 88–89, 97) used by the
programs of Algorithms 7.2, 7.4 and 9.8, together with the bridge to
`GraphMinor.GM13`:

1. **Elementary wall coordinates and edges (`elemWallCoords`, `elemWallNumVerts`,
   `isElemWallEdgeCoord`, `elemWallEdges`):**
   Follows GM XIII Section 9 (page 97) and Fig. 1 (page 88), with closed-form row-major index
   lemmas (`elemWallCoords_eq_map`, `elemWallNumVerts_eq`, `getElem_elemWallCoords`,
   `elemWallEdgesFromVert`, `elemWallEdges_eq_flatMap`, `length_elemWallEdges_le`).
2. **Written-out walls (`WallOfHeight`, `WallOfHeight.IsValid`, `WallOfHeight.enc`,
   `WallOfHeight.encList`):**
   Represents a wall of height `h` in `G : MultiDigraph n` by its injective branch-vertex map
   `branchVert : Fin (elemWallNumVerts h) → Fin n` and the internal subdivision vertices
   `internalVerts : Fin (elemWallEdges h).length → List (Fin n)`, with both bitlist (`enc`) and
   linear-size list (`encList`) encodings.
3. **Bridge to `GM13.Wall` (`elemWallCoordEquiv`, `WallOfHeight.toGMWall`,
   `WallOfHeight.isWallIn_toGMWall`, `WallOfHeight.toGMWall_corner`,
   `WallOfHeight.toGMWall_middleVertex₁`, `WallOfHeight.toGMWall_middleVertex₂`):**
   Proves that a valid `W : WallOfHeight h G` (`2 ≤ h`, `Even h`, `W.IsValid`) gives a
   `GM13.Wall ℕ (ℕ × ℕ × ℕ)` of height `h` that is a wall in `G.toGMDigraph.toGraph`
   (`GM13.IsWallIn G.toGMDigraph.toGraph (W.toGMWall h2 he hW)`), whose corners and middle vertices
   are the images under `W.branchVert` of those of the elementary wall.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Elementary Walls and Walls of Height `h` (GM XIII Sections 7 & 9, pages 88, 97) -/

/-- Coordinates `(x, y)` of the vertices of the elementary wall `J` of height `h`
(GM XIII Section 9, page 97):
"Draw $J$ in the plane as in Fig. 1, and let us name the vertices of $J$ by $x, y$-coordinates,
taking the origin in the bottom left of the figure. Thus, $J$ has vertex set
$$\{(x, y) : 0 \le x \le 2h+1, 0 \le y \le h\} - \{(0, 0), (2h+1, h)\}$$
and corners $(1, 0), (2h+1, 0), (0, h), (2h, h)$." -/
def elemWallCoords (h : ℕ) : List (ℕ × ℕ) :=
  ((List.range (h + 1)).flatMap fun y =>
    (List.range (2 * h + 2)).map fun x => (x, y)).filter
    fun p => decide (p ≠ (0, 0) ∧ p ≠ (2 * h + 1, h))

/-- Number of vertices `|V(J)|` of the elementary wall of height `h`. -/
def elemWallNumVerts (h : ℕ) : ℕ :=
  (elemWallCoords h).length

/-- Two coordinate pairs `(x₁, y₁)` and `(x₂, y₂)` in the elementary wall of height `h` are joined
by an undirected brick edge (either a horizontal edge `y₁ = y₂ ∧ x₂ = x₁ + 1` or a vertical edge
`x₁ = x₂ ∧ y₂ = y₁ + 1 ∧ (x₁ + y₁) % 2 = 1`, GM XIII Fig. 1, page 88). -/
def isElemWallEdgeCoord (p₁ p₂ : ℕ × ℕ) : Bool :=
  (p₁.2 == p₂.2 && p₂.1 == p₁.1 + 1) ||
  (p₁.1 == p₂.1 && p₂.2 == p₁.2 + 1 && (p₁.1 + p₁.2) % 2 == 1)

/-- Directed edge list of the elementary wall of height `h` on `Fin (elemWallNumVerts h)`. -/
def elemWallEdges (h : ℕ) : List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)) :=
  (allDirectedPairs (elemWallNumVerts h)).filter fun e =>
    isElemWallEdgeCoord
      ((elemWallCoords h)[e.1.1]'(e.1.2))
      ((elemWallCoords h)[e.2.1]'(e.2.2))

private theorem list_eq_of_pairwise_key_lt {α : Type*} (key : α → ℕ)
    {l₁ l₂ : List α} (hinj : ∀ x y, x ∈ l₁ → y ∈ l₂ → key x = key y → x = y)
    (hp₁ : l₁.Pairwise (fun x y => key x < key y))
    (hp₂ : l₂.Pairwise (fun x y => key x < key y))
    (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b bs =>
      have hb : b ∈ ([] : List α) := (hmem b).mpr List.mem_cons_self
      nomatch hb
  | cons a as ih =>
    cases l₂ with
    | nil =>
      have ha : a ∈ ([] : List α) := (hmem a).mp List.mem_cons_self
      nomatch ha
    | cons b bs =>
      rcases List.pairwise_cons.mp hp₁ with ⟨has, hp₁'⟩
      rcases List.pairwise_cons.mp hp₂ with ⟨hbs, hp₂'⟩
      have ha_in : a ∈ b :: bs := (hmem a).mp List.mem_cons_self
      have hb_in : b ∈ a :: as := (hmem b).mpr List.mem_cons_self
      have hkey_eq : key a = key b := by
        rcases List.mem_cons.mp ha_in with rfl | ha_bs
        · rfl
        · rcases List.mem_cons.mp hb_in with rfl | hb_as
          · rfl
          · have h1 := hbs a ha_bs
            have h2 := has b hb_as
            omega
      have hab : a = b := hinj a b List.mem_cons_self List.mem_cons_self hkey_eq
      subst hab
      congr 1
      apply ih (fun x y hx hy => hinj x y (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem a hy))
        hp₁' hp₂'
      intro x
      constructor
      · intro hx
        have hx_lt : key a < key x := has x hx
        rcases List.mem_cons.mp ((hmem x).mp (List.mem_cons_of_mem a hx)) with rfl | hx_bs
        · omega
        · exact hx_bs
      · intro hx
        have hx_lt : key a < key x := hbs x hx
        rcases List.mem_cons.mp ((hmem x).mpr (List.mem_cons_of_mem a hx)) with rfl | hx_as
        · omega
        · exact hx_as

private theorem pairwise_lt_elemWallCoords (h : ℕ) :
    (elemWallCoords h).Pairwise
      (fun p₁ p₂ => p₁.2 * (2 * h + 2) + p₁.1 < p₂.2 * (2 * h + 2) + p₂.1) := by
  unfold elemWallCoords
  apply List.Pairwise.filter
  rw [List.pairwise_flatMap]
  refine ⟨fun y _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (by intro x₁ x₂ hlt; dsimp; omega)
  · refine List.pairwise_lt_range.imp ?_
    intro y₁ y₂ hlt p₁ hp₁ p₂ hp₂
    simp only [List.mem_map, List.mem_range] at hp₁ hp₂
    rcases hp₁ with ⟨x₁, hx₁, rfl⟩
    rcases hp₂ with ⟨x₂, hx₂, rfl⟩
    dsimp
    have hmul : (y₁ + 1) * (2 * h + 2) ≤ y₂ * (2 * h + 2) :=
      Nat.mul_le_mul_right (2 * h + 2) hlt
    nlinarith

/-- Closed-form row-major characterization of `elemWallCoords h`. -/
theorem elemWallCoords_eq_map (h : ℕ) :
    elemWallCoords h =
      (List.range ((h + 1) * (2 * h + 2) - 2)).map
        (fun u => ((u + 1) % (2 * h + 2), (u + 1) / (2 * h + 2))) := by
  set B := 2 * h + 2
  have hB : 0 < B := by omega
  apply list_eq_of_pairwise_key_lt (fun p : ℕ × ℕ => p.2 * B + p.1)
  · intro p₁ p₂ hp₁ hp₂ heq
    have hx₁ : p₁.1 < B := by
      unfold elemWallCoords at hp₁
      simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map] at hp₁
      rcases hp₁.1 with ⟨y, _, x, hx, rfl⟩
      exact hx
    have hx₂ : p₂.1 < B := by
      simp only [List.mem_map, List.mem_range] at hp₂
      rcases hp₂ with ⟨u, _, rfl⟩
      exact Nat.mod_lt (u + 1) hB
    have h1 := mul_add_inj hx₁ hx₂ heq
    exact Prod.ext h1.2 h1.1
  · exact pairwise_lt_elemWallCoords h
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp ?_
    intro u₁ u₂ hlt
    dsimp
    have hd₁ : (u₁ + 1) / B * B + (u₁ + 1) % B = u₁ + 1 := by
      simpa [Nat.mul_comm] using Nat.div_add_mod (u₁ + 1) B
    have hd₂ : (u₂ + 1) / B * B + (u₂ + 1) % B = u₂ + 1 := by
      simpa [Nat.mul_comm] using Nat.div_add_mod (u₂ + 1) B
    omega
  · intro p
    rcases p with ⟨x, y⟩
    unfold elemWallCoords
    simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map,
      decide_eq_true_eq, ne_eq, Prod.mk.injEq, not_and]
    constructor
    · rintro ⟨⟨y', hy', x', hx', ⟨rfl, rfl⟩⟩, h00, hlast⟩
      have hpos : 0 < y' * B + x' := by
        by_contra hle
        have hy0 : y' = 0 := by nlinarith
        have hx0 : x' = 0 := by omega
        exact h00 hx0 hy0
      have hlt_max : y' * B + x' < (h + 1) * B - 1 := by
        have hle_max : y' * B + x' ≤ h * B + (2 * h + 1) := by
          have hy_le : y' ≤ h := by omega
          have hmul : y' * B ≤ h * B := Nat.mul_le_mul_right B hy_le
          omega
        have hne_max : y' * B + x' ≠ h * B + (2 * h + 1) := by
          intro heq
          have h1 := mul_add_inj hx' (show 2 * h + 1 < B by omega) heq
          exact hlast h1.2 h1.1
        have htot : (h + 1) * B = h * B + (2 * h + 2) := by ring
        omega
      refine ⟨y' * B + x' - 1, by omega, ?_⟩
      have hu : y' * B + x' - 1 + 1 = x' + B * y' := by
        have : y' * B = B * y' := Nat.mul_comm y' B
        omega
      rw [hu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx',
        Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hx', Nat.zero_add]
      exact ⟨rfl, rfl⟩
    · rintro ⟨u, hu, rfl, rfl⟩
      have hdiv_lt : (u + 1) / B < h + 1 := by
        rw [Nat.div_lt_iff_lt_mul hB]
        omega
      have hmod_lt : (u + 1) % B < B := Nat.mod_lt (u + 1) hB
      have hd : B * ((u + 1) / B) + (u + 1) % B = u + 1 := Nat.div_add_mod (u + 1) B
      refine ⟨⟨(u + 1) / B, hdiv_lt, (u + 1) % B, hmod_lt, rfl, rfl⟩, ?_, ?_⟩
      · intro hx0 hy0
        rw [hx0, hy0] at hd
        omega
      · intro hx1 hy1
        rw [hx1, hy1] at hd
        have htot : (h + 1) * B = B * h + (2 * h + 2) := by ring
        omega

/-- Explicit formula for `elemWallNumVerts h = |V(J_h)| = (h + 1) * (2h + 2) - 2`. -/
theorem elemWallNumVerts_eq (h : ℕ) :
    elemWallNumVerts h = (h + 1) * (2 * h + 2) - 2 := by
  unfold elemWallNumVerts
  rw [elemWallCoords_eq_map, List.length_map, List.length_range]

/-- Explicit O(1) coordinate formula for the `u`-th vertex of `elemWallCoords h`. -/
theorem getElem_elemWallCoords (h : ℕ) (u : ℕ) (hu : u < (elemWallCoords h).length) :
    (elemWallCoords h)[u] = ((u + 1) % (2 * h + 2), (u + 1) / (2 * h + 2)) := by
  simp [elemWallCoords_eq_map h]

/-- Outgoing elementary-wall edges `(u, v)` from vertex `u : Fin (elemWallNumVerts h)`:
at most one horizontal edge to `u.1 + 1` and at most one vertical edge to `u.1 + (2h + 2)`. -/
def elemWallEdgesFromVert (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)) :=
  let x := (u.1 + 1) % (2 * h + 2)
  let y := (u.1 + 1) / (2 * h + 2)
  (if h1 : x + 1 < 2 * h + 2 ∧ u.1 + 1 < elemWallNumVerts h then
    [(u, ⟨u.1 + 1, h1.2⟩)]
  else []) ++
  (if h2 : u.1 + (2 * h + 2) < elemWallNumVerts h ∧ (x + y) % 2 = 1 then
    [(u, ⟨u.1 + (2 * h + 2), h2.1⟩)]
  else [])

theorem length_elemWallEdgesFromVert_le (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    (elemWallEdgesFromVert h u).length ≤ 2 := by
  unfold elemWallEdgesFromVert
  dsimp only
  split_ifs <;> simp

private theorem isElemWallEdgeCoord_iff_index (h : ℕ)
    (u v : Fin (elemWallNumVerts h)) :
    isElemWallEdgeCoord ((elemWallCoords h)[u.1]'u.2) ((elemWallCoords h)[v.1]'v.2) = true ↔
      let x := (u.1 + 1) % (2 * h + 2)
      let y := (u.1 + 1) / (2 * h + 2)
      (x + 1 < 2 * h + 2 ∧ v.1 = u.1 + 1) ∨
      (v.1 = u.1 + (2 * h + 2) ∧ (x + y) % 2 = 1) := by
  rw [getElem_elemWallCoords h u.1 u.2, getElem_elemWallCoords h v.1 v.2]
  set B := 2 * h + 2
  have hB : 0 < B := by omega
  have hdu : B * ((u.1 + 1) / B) + (u.1 + 1) % B = u.1 + 1 := Nat.div_add_mod (u.1 + 1) B
  have hdv : B * ((v.1 + 1) / B) + (v.1 + 1) % B = v.1 + 1 := Nat.div_add_mod (v.1 + 1) B
  have hmu : (u.1 + 1) % B < B := Nat.mod_lt (u.1 + 1) hB
  have hmv : (v.1 + 1) % B < B := Nat.mod_lt (v.1 + 1) hB
  unfold isElemWallEdgeCoord
  dsimp only
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro (⟨hy, hx⟩ | ⟨⟨hx, hy⟩, hpar⟩)
    · left
      rw [← hy, hx] at hdv
      exact ⟨by omega, by omega⟩
    · right
      rw [← hx, hy, Nat.mul_add, Nat.mul_one] at hdv
      exact ⟨by omega, hpar⟩
  · rintro (⟨hx_lt, hv_eq⟩ | ⟨hv_eq, hpar⟩)
    · left
      have hv1 : v.1 + 1 = (u.1 + 1) % B + 1 + B * ((u.1 + 1) / B) := by omega
      have hmod : (v.1 + 1) % B = (u.1 + 1) % B + 1 := by
        rw [hv1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx_lt]
      have hdiv : (v.1 + 1) / B = (u.1 + 1) / B := by
        rw [hv1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hx_lt, Nat.zero_add]
      exact ⟨hdiv.symm, hmod⟩
    · right
      have hv1 : v.1 + 1 = (u.1 + 1) % B + B * ((u.1 + 1) / B + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hmod : (v.1 + 1) % B = (u.1 + 1) % B := by
        rw [hv1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmu]
      have hdiv : (v.1 + 1) / B = (u.1 + 1) / B + 1 := by
        rw [hv1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hmu, Nat.zero_add]
      exact ⟨⟨hmod.symm, hdiv⟩, hpar⟩

private theorem flatMap_filter_singleton {α : Type*} (P : α → Bool) (l : List α) :
    l.flatMap (fun e => List.filter P [e]) = l.filter P := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    rw [List.flatMap_cons, ih]
    cases hPe : P e <;> simp [hPe]

private theorem filter_allDirectedPairs_eq_filter_allPairs {n : ℕ}
    (P : Fin n × Fin n → Bool) (hP : ∀ e : Fin n × Fin n, P e = true → e.1.1 < e.2.1) :
    (allDirectedPairs n).filter P = (allPairs n).filter P := by
  have h1 : (allDirectedPairs n).filter P = (upperPairs n).filter P := by
    unfold allDirectedPairs
    rw [List.filter_flatMap]
    have hcongr :
        ∀ e ∈ upperPairs n,
          List.filter P (if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)]) =
            List.filter P [e] := by
      rintro ⟨u, v⟩ he
      rw [mem_upperPairs] at he
      dsimp at he ⊢
      by_cases huv : u = v
      · subst huv
        simp
      · have hvu_false : P (v, u) = false := by
          cases hPvu : P (v, u)
          · rfl
          · have hlt := hP (v, u) hPvu
            dsimp at hlt
            omega
        cases hPuv : P (u, v) <;> simp [huv, hPuv, hvu_false]
    rw [List.flatMap_congr hcongr, flatMap_filter_singleton]
  rw [h1]
  unfold upperPairs
  rw [List.filter_filter]
  apply List.filter_congr
  intro e _
  cases hPe : P e
  · simp
  · have hlt := hP e hPe
    simp [Nat.le_of_lt hlt]

/-- `elemWallEdges h` is the concatenation over `u : Fin (elemWallNumVerts h)` of the `≤ 2`
outgoing edges `elemWallEdgesFromVert h u`. -/
theorem elemWallEdges_eq_flatMap (h : ℕ) :
    elemWallEdges h =
      (List.finRange (elemWallNumVerts h)).flatMap (elemWallEdgesFromVert h) := by
  unfold elemWallEdges
  set P : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h) → Bool := fun e =>
    isElemWallEdgeCoord ((elemWallCoords h)[e.1.1]'(e.1.2)) ((elemWallCoords h)[e.2.1]'(e.2.2))
  have hP_lt : ∀ e, P e = true → e.1.1 < e.2.1 := by
    intro ⟨u, v⟩ hPe
    rcases (isElemWallEdgeCoord_iff_index h u v).mp hPe with ⟨_, hv⟩ | ⟨hv, _⟩ <;>
      (dsimp; omega)
  rw [filter_allDirectedPairs_eq_filter_allPairs P hP_lt]
  unfold allPairs
  rw [List.filter_flatMap]
  apply List.flatMap_congr
  intro u _
  apply list_eq_of_pairwise_key_lt (fun e : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h) => e.2.1)
  · intro e₁ e₂ he₁ he₂ heq
    simp only [List.mem_filter, List.mem_map, List.mem_finRange, true_and] at he₁
    rcases he₁.1 with ⟨v₁, rfl⟩
    unfold elemWallEdgesFromVert at he₂
    dsimp only at he₂
    rw [List.mem_append] at he₂
    rcases he₂ with he₂ | he₂ <;>
      (split_ifs at he₂ <;> simp only [List.mem_singleton, List.not_mem_nil] at he₂)
    · subst he₂
      exact Prod.ext rfl (Fin.ext heq)
    · subst he₂
      exact Prod.ext rfl (Fin.ext heq)
  · apply List.Pairwise.filter
    rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp (fun hlt => hlt)
  · unfold elemWallEdgesFromVert
    dsimp only
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · split_ifs <;> simp
    · split_ifs <;> simp
    · intro a ha b hb
      split_ifs at ha hb <;> simp only [List.mem_singleton, List.not_mem_nil] at ha hb
      subst ha hb
      dsimp
      omega
  · intro ⟨u', v⟩
    simp only [List.mem_filter, List.mem_map, List.mem_finRange, true_and, Prod.mk.injEq]
    unfold elemWallEdgesFromVert
    dsimp only
    rw [List.mem_append]
    constructor
    · rintro ⟨⟨v', rfl, rfl⟩, hPe⟩
      rcases (isElemWallEdgeCoord_iff_index h u v').mp hPe with ⟨hx, hv⟩ | ⟨hv, hpar⟩
      · left
        have hcond : (u.1 + 1) % (2 * h + 2) + 1 < 2 * h + 2 ∧ u.1 + 1 < elemWallNumVerts h :=
          ⟨hx, by omega⟩
        simp only [hcond, and_self, ↓reduceDIte, List.mem_singleton, Prod.mk.injEq, true_and]
        exact Fin.ext hv
      · right
        have hcond : u.1 + (2 * h + 2) < elemWallNumVerts h ∧
            ((u.1 + 1) % (2 * h + 2) + (u.1 + 1) / (2 * h + 2)) % 2 = 1 :=
          ⟨by omega, hpar⟩
        simp only [hcond, and_self, ↓reduceDIte, List.mem_singleton, Prod.mk.injEq, true_and]
        exact Fin.ext hv
    · rintro (hmem | hmem) <;>
        (split_ifs at hmem with hcond <;>
          simp only [List.mem_singleton, List.not_mem_nil, Prod.mk.injEq] at hmem)
      · rcases hmem with ⟨rfl, rfl⟩
        refine ⟨⟨_, rfl, rfl⟩, (isElemWallEdgeCoord_iff_index h u' _).mpr (Or.inl ⟨hcond.1, rfl⟩)⟩
      · rcases hmem with ⟨rfl, rfl⟩
        refine ⟨⟨_, rfl, rfl⟩, (isElemWallEdgeCoord_iff_index h u' _).mpr (Or.inr ⟨rfl, hcond.2⟩)⟩

private theorem sum_map_le_const {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, f x ≤ c) :
    (l.map f).sum ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := h a List.mem_cons_self
    have hrest := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    nlinarith

/-- The elementary wall of height `h` has at most `2 * elemWallNumVerts h` edges. -/
theorem length_elemWallEdges_le (h : ℕ) :
    (elemWallEdges h).length ≤ 2 * elemWallNumVerts h := by
  rw [elemWallEdges_eq_flatMap, List.length_flatMap]
  have hle := sum_map_le_const (List.finRange (elemWallNumVerts h))
    (fun u => (elemWallEdgesFromVert h u).length) 2
    (fun u _ => length_elemWallEdgesFromVert_le h u)
  simpa using hle

/-- A wall of height `h` in a graph `G : MultiDigraph n` (GM XIII Section 7, pages 88–89):
"A *wall of height $h$* (where $h \ge 2$ is even) is a subdivision of an elementary wall of height
$h$. It too therefore has four distinguished vertices, called its *corners*. ...
Let $G$ be a graph. A *wall in* $G$ is a subgraph of $G$ which is a wall." -/
structure WallOfHeight (h : ℕ) {n : ℕ} (G : MultiDigraph n) where
  /-- Injection mapping each vertex `u` of the elementary wall `J_h` to its branch vertex in `G`. -/
  branchVert : Fin (elemWallNumVerts h) → Fin n
  /-- For each edge `e_k = (u_k, v_k)` of `J_h`, the internal vertices of the subdivision path in
  `G` between `branchVert u_k` and `branchVert v_k`. -/
  internalVerts : Fin (elemWallEdges h).length → List (Fin n)

namespace WallOfHeight

/-- Full vertex support `[branchVert u_k] ++ internalVerts k ++ [branchVert v_k]` of the `k`-th
subdivision path of a wall `W`. -/
def subdivPathVerts {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (k : Fin (elemWallEdges h).length) : List (Fin n) :=
  let e := (elemWallEdges h)[k.1]'k.2
  [W.branchVert e.1] ++ W.internalVerts k ++ [W.branchVert e.2]

/-- Successive pairs of vertices in a list `l : List (Fin n)` are adjacent in `G.toSimpleGraph`. -/
def IsSimpleWalkList {n : ℕ} (G : MultiDigraph n) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => G.toSimpleGraph.Adj u v ∧ IsSimpleWalkList G (v :: rest)

/-- Validity of a wall `W : WallOfHeight h G` as a subgraph of `G` that is a subdivision of the
elementary wall of height `h` (GM XIII pages 88–89):
- the branch vertices `W.branchVert u` are pairwise distinct,
- for each edge `e_k` of the elementary wall, `W.subdivPathVerts k` is a simple path in `G`,
- internal vertices of `W.internalVerts k` are disjoint from all branch vertices and from
  `W.internalVerts k'` for `k ≠ k'`. -/
def IsValid {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) : Prop :=
  Function.Injective W.branchVert ∧
  (∀ k : Fin (elemWallEdges h).length,
    (W.subdivPathVerts k).Nodup ∧ IsSimpleWalkList G (W.subdivPathVerts k)) ∧
  (∀ (k : Fin (elemWallEdges h).length) (u : Fin (elemWallNumVerts h)),
    W.branchVert u ∉ W.internalVerts k) ∧
  (∀ k₁ k₂ : Fin (elemWallEdges h).length, k₁ ≠ k₂ →
    List.Disjoint (W.internalVerts k₁) (W.internalVerts k₂))

/-- Vertex set `V(W) ⊆ V(G)` of a wall `W`. -/
def vertexFinset {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) : Finset (Fin n) :=
  Finset.univ.image W.branchVert ∪
  ((List.finRange (elemWallEdges h).length).flatMap W.internalVerts).toFinset

/-- Flat `List ℕ` encoding of a wall `W : WallOfHeight h G`:
`[h, elemWallNumVerts h, (elemWallEdges h).length]` followed by the branch vertices
`(W.branchVert u).1` and, for each `k : Fin (elemWallEdges h).length`, the indicator bitlist of
`W.internalVerts k` of length `n`. -/
def enc {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) : List ℕ :=
  [h, elemWallNumVerts h, (elemWallEdges h).length] ++
  (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1) ++
  (List.finRange (elemWallEdges h).length).flatMap
    (fun k => bitSetList (W.internalVerts k).toFinset)

theorem length_enc {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    W.enc.length = 3 + elemWallNumVerts h + (elemWallEdges h).length * n := by
  unfold enc
  have h2 :
      ((List.finRange (elemWallEdges h).length).flatMap
        (fun k => bitSetList (W.internalVerts k).toFinset)).length =
      (elemWallEdges h).length * n := by
    rw [List.length_flatMap]
    have hmap :
        List.map (fun k => (bitSetList (W.internalVerts k).toFinset).length)
          (List.finRange (elemWallEdges h).length) =
        List.replicate (List.finRange (elemWallEdges h).length).length n := by
      rw [List.map_eq_replicate_iff]
      intro k _
      exact length_bitSetList (W.internalVerts k).toFinset
    rw [hmap, List.length_finRange, List.sum_replicate, smul_eq_mul]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_finRange, h2]

/-- Linear-size flat `List ℕ` encoding of a wall `W : WallOfHeight h G`:
`[h, elemWallNumVerts h, (elemWallEdges h).length]`, then the branch vertices
`(W.branchVert u).1`, then for each `k : Fin (elemWallEdges h).length`,
`(W.internalVerts k).length` followed by `(W.internalVerts k).map Fin.val`. -/
def encList {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) : List ℕ :=
  [h, elemWallNumVerts h, (elemWallEdges h).length] ++
  (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1) ++
  (List.finRange (elemWallEdges h).length).flatMap
    (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)

/-- Number of edges `|E(W)| = |E(J_h)| + ∑_k |internalVerts k|` of the subdivision wall `W`. -/
def numEdges {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) : ℕ :=
  (elemWallEdges h).length +
  ((List.finRange (elemWallEdges h).length).map (fun k => (W.internalVerts k).length)).sum

private theorem sum_map_add_one {α : Type*} (l : List α) (f : α → ℕ) :
    (l.map (fun x => f x + 1)).sum = l.length + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem length_encList {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    W.encList.length =
      3 + elemWallNumVerts h + (elemWallEdges h).length +
        ((List.finRange (elemWallEdges h).length).map
          (fun k => (W.internalVerts k).length)).sum := by
  unfold encList
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_finRange, List.length_flatMap]
  have hsum := sum_map_add_one (List.finRange (elemWallEdges h).length)
    (fun k => (W.internalVerts k).length)
  rw [List.length_finRange] at hsum
  omega

theorem length_encList_eq_numEdges {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    W.encList.length = 3 + elemWallNumVerts h + W.numEdges := by
  rw [length_encList, numEdges]
  omega

theorem nodup_internalVerts_of_isValid {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    (W.internalVerts k).Nodup := by
  have hnodup := (hW.2.1 k).1
  unfold subdivPathVerts at hnodup
  dsimp only at hnodup
  exact ((hnodup.sublist (List.sublist_append_left _ _)).sublist
    (List.sublist_append_right _ _))

theorem card_vertexFinset_of_isValid {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    W.vertexFinset.card =
      elemWallNumVerts h +
        ((List.finRange (elemWallEdges h).length).map
          (fun k => (W.internalVerts k).length)).sum := by
  rcases hW with ⟨hinj, hsubdiv, hnot_br, hdisj_int⟩
  unfold vertexFinset
  have hdisj :
      Disjoint (Finset.univ.image W.branchVert)
        ((List.finRange (elemWallEdges h).length).flatMap W.internalVerts).toFinset := by
    rw [Finset.disjoint_left]
    intro v hv_br hv_int
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv_br
    simp only [List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and] at hv_int
    rcases hv_br with ⟨u, rfl⟩
    rcases hv_int with ⟨k, hk⟩
    exact hnot_br k u hk
  have hnodup_flat :
      ((List.finRange (elemWallEdges h).length).flatMap W.internalVerts).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun k _ => nodup_internalVerts_of_isValid ⟨hinj, hsubdiv, hnot_br, hdisj_int⟩ k, ?_⟩
    exact (List.nodup_finRange _).imp (fun {k₁ k₂} hne => hdisj_int k₁ k₂ hne)
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin, List.toFinset_card_of_nodup hnodup_flat,
    List.length_flatMap]

theorem elemWallNumVerts_le_card_vertexFinset {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    elemWallNumVerts h ≤ W.vertexFinset.card := by
  rw [card_vertexFinset_of_isValid hW]
  omega

theorem card_vertexFinset_le {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G) :
    W.vertexFinset.card ≤ n := by
  simpa using Finset.card_le_univ W.vertexFinset

theorem length_encList_eq_card_vertexFinset_add {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    W.encList.length = 3 + W.vertexFinset.card + (elemWallEdges h).length := by
  rw [length_encList, card_vertexFinset_of_isValid hW]
  omega

theorem length_encList_le_card_vertexFinset_add_numEdges {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    W.encList.length ≤ 3 + W.vertexFinset.card + W.numEdges := by
  rw [length_encList_eq_numEdges]
  have hle := elemWallNumVerts_le_card_vertexFinset hW
  omega

theorem length_encList_le_card_vertexFinset {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    W.encList.length ≤ 3 + 3 * W.vertexFinset.card := by
  rw [length_encList_eq_card_vertexFinset_add hW]
  have h1 := length_elemWallEdges_le h
  have h2 := elemWallNumVerts_le_card_vertexFinset hW
  omega

theorem length_encList_le {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    W.encList.length ≤ 3 + 3 * n := by
  have h1 := length_encList_le_card_vertexFinset hW
  have h2 := W.card_vertexFinset_le
  omega

end WallOfHeight

/-- Existence of a valid wall of height `h` in `G : MultiDigraph n`. -/
def HasWallOfHeight (h : ℕ) {n : ℕ} (G : MultiDigraph n) : Prop :=
  ∃ W : WallOfHeight h G, W.IsValid

/-! ### Section 2: Elementary Wall Coordinate & Edge Equivalence with `GM13.elementaryWall` -/

/-- Membership in `elemWallCoords h` is equivalent to `x ≤ 2h + 1`, `y ≤ h`, `(x, y) ≠ (0, 0)`,
and `(x, y) ≠ (2h + 1, h)`, matching `GM13.elementaryWallVerts h` (`GraphMinor/GM13/Defs.lean`). -/
theorem mem_elemWallCoords_iff (h : ℕ) (p : ℕ × ℕ) :
    p ∈ elemWallCoords h ↔
      p.1 ≤ 2 * h + 1 ∧ p.2 ≤ h ∧ p ≠ (0, 0) ∧ p ≠ (2 * h + 1, h) := by
  unfold elemWallCoords
  simp only [List.mem_filter, List.mem_flatMap, List.mem_range, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨y, hy, x, hx, rfl⟩, hne1, hne2⟩
    exact ⟨by omega, by omega, hne1, hne2⟩
  · rintro ⟨hx, hy, hne1, hne2⟩
    exact ⟨⟨p.2, by omega, p.1, by omega, Prod.mk.eta⟩, hne1, hne2⟩

theorem mem_elemWallCoords_iff_mem_elementaryWallVerts (h : ℕ) (p : ℕ × ℕ) :
    p ∈ elemWallCoords h ↔ p ∈ GM13.elementaryWallVerts h :=
  mem_elemWallCoords_iff h p

theorem nodup_elemWallCoords (h : ℕ) : (elemWallCoords h).Nodup := by
  unfold elemWallCoords
  apply List.Nodup.filter
  rw [List.nodup_flatMap]
  refine ⟨fun y _ => List.Nodup.map (fun x₁ x₂ h => Prod.ext_iff.mp h |>.1) List.nodup_range, ?_⟩
  apply List.Pairwise.imp (R := (· ≠ ·))
  · intro y₁ y₂ hne q hq₁ hq₂
    simp only [List.mem_map, List.mem_range] at hq₁ hq₂
    rcases hq₁ with ⟨x₁, _, rfl⟩
    rcases hq₂ with ⟨x₂, _, heq⟩
    exact hne (Prod.ext_iff.mp heq).2.symm
  · exact List.nodup_range

/-- Coordinate pair `(x, y)` of the `u`-th vertex of `elemWallCoords h`. -/
def elemWallVertCoord (h : ℕ) (u : Fin (elemWallNumVerts h)) : ℕ × ℕ :=
  (elemWallCoords h)[u.1]'u.2

theorem elemWallVertCoord_mem_elemWallCoords (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    elemWallVertCoord h u ∈ elemWallCoords h :=
  List.getElem_mem u.2

theorem elemWallVertCoord_mem_elementaryWallVerts (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    elemWallVertCoord h u ∈ GM13.elementaryWallVerts h :=
  (mem_elemWallCoords_iff_mem_elementaryWallVerts h _).mp (elemWallVertCoord_mem_elemWallCoords h u)

theorem elemWallVertCoord_injective (h : ℕ) : Function.Injective (elemWallVertCoord h) := by
  intro u₁ u₂ heq
  exact Fin.ext ((nodup_elemWallCoords h).getElem_inj_iff.mp heq)

/-- Row-major index `y * (2h + 2) + x - 1` of a coordinate pair `p = (x, y)` in `elemWallCoords h`. -/
def elemWallCoordIdxVal (h : ℕ) (p : ℕ × ℕ) : ℕ :=
  p.2 * (2 * h + 2) + p.1 - 1

theorem elemWallCoordIdxVal_lt (h : ℕ) {p : ℕ × ℕ} (hp : p ∈ GM13.elementaryWallVerts h) :
    elemWallCoordIdxVal h p < elemWallNumVerts h := by
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, h00, hlast⟩
  dsimp at hx hy ⊢
  set B := 2 * h + 2
  have hB : 0 < B := by omega
  have hpos : 0 < y * B + x := by
    by_contra hle
    have hy0 : y = 0 := by nlinarith
    have hx0 : x = 0 := by omega
    exact h00 (Prod.ext hx0 hy0)
  have hle_max : y * B + x ≤ h * B + (2 * h + 1) := by
    have hmul : y * B ≤ h * B := Nat.mul_le_mul_right B hy
    omega
  have hne_max : y * B + x ≠ h * B + (2 * h + 1) := by
    intro heq
    have h1 := mul_add_inj (show x < B by omega) (show 2 * h + 1 < B by omega) heq
    exact hlast (Prod.ext h1.2 h1.1)
  have htot : (h + 1) * B = h * B + (2 * h + 2) := by ring
  rw [elemWallNumVerts_eq, elemWallCoordIdxVal]
  change y * B + x - 1 < (h + 1) * B - 2
  omega

/-- Index `u : Fin (elemWallNumVerts h)` of a coordinate `p ∈ GM13.elementaryWallVerts h`. -/
def elemWallCoordIdx (h : ℕ) (p : ℕ × ℕ) (hp : p ∈ GM13.elementaryWallVerts h) :
    Fin (elemWallNumVerts h) :=
  ⟨elemWallCoordIdxVal h p, elemWallCoordIdxVal_lt h hp⟩

@[simp]
theorem elemWallVertCoord_elemWallCoordIdx (h : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ GM13.elementaryWallVerts h) :
    elemWallVertCoord h (elemWallCoordIdx h p hp) = p := by
  unfold elemWallVertCoord
  rw [getElem_elemWallCoords h (elemWallCoordIdx h p hp).1 (elemWallCoordIdx h p hp).2]
  change ((elemWallCoordIdxVal h p + 1) % (2 * h + 2),
    (elemWallCoordIdxVal h p + 1) / (2 * h + 2)) = p
  unfold elemWallCoordIdxVal
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, h00, _⟩
  dsimp at hx hy ⊢
  set B := 2 * h + 2
  have hB : 0 < B := by omega
  have hpos : 0 < y * B + x := by
    by_contra hle
    have hy0 : y = 0 := by nlinarith
    have hx0 : x = 0 := by omega
    exact h00 (Prod.ext hx0 hy0)
  have hu : y * B + x - 1 + 1 = x + B * y := by
    have : y * B = B * y := Nat.mul_comm y B
    omega
  have hx' : x < B := by omega
  rw [hu, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx',
    Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hx', Nat.zero_add]

@[simp]
theorem elemWallCoordIdx_elemWallVertCoord (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    elemWallCoordIdx h (elemWallVertCoord h u) (elemWallVertCoord_mem_elementaryWallVerts h u) = u :=
  elemWallVertCoord_injective h (elemWallVertCoord_elemWallCoordIdx h _)

/-- Canonical bijection between `Fin (elemWallNumVerts h)` and `GM13.elementaryWallVerts h`. -/
def elemWallCoordEquiv (h : ℕ) : Fin (elemWallNumVerts h) ≃ GM13.elementaryWallVerts h where
  toFun u := ⟨elemWallVertCoord h u, elemWallVertCoord_mem_elementaryWallVerts h u⟩
  invFun p := elemWallCoordIdx h p.1 p.2
  left_inv u := elemWallCoordIdx_elemWallVertCoord h u
  right_inv p := Subtype.ext (elemWallVertCoord_elemWallCoordIdx h p.2)

theorem elementaryWallCorner_mem_elementaryWallVerts {h : ℕ} (h2 : 2 ≤ h) (k : Fin 4) :
    GM13.elementaryWallCorner h k ∈ GM13.elementaryWallVerts h := by
  fin_cases k <;> simp [GM13.elementaryWallCorner, GM13.elementaryWallVerts] <;> omega

theorem elementaryWallMiddle₁_mem_elementaryWallVerts {h : ℕ} (h2 : 2 ≤ h) :
    GM13.elementaryWallMiddle₁ h ∈ GM13.elementaryWallVerts h := by
  dsimp [GM13.elementaryWallMiddle₁, GM13.elementaryWallVerts]
  refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩
  · intro h0; have := congrArg Prod.fst h0; dsimp at this; omega
  · intro h1; have := congrArg Prod.fst h1; dsimp at this; omega

theorem elementaryWallMiddle₂_mem_elementaryWallVerts {h : ℕ} (h2 : 2 ≤ h) :
    GM13.elementaryWallMiddle₂ h ∈ GM13.elementaryWallVerts h := by
  dsimp [GM13.elementaryWallMiddle₂, GM13.elementaryWallVerts]
  refine ⟨by omega, Nat.div_le_self _ _, ?_, ?_⟩
  · intro h0; have := congrArg Prod.fst h0; dsimp at this; omega
  · intro h1; have := congrArg Prod.fst h1; dsimp at this; omega

/-- Index in `Fin (elemWallNumVerts h)` of the `k`-th corner of the elementary wall of height `h`. -/
def elemWallCornerIdx {h : ℕ} (h2 : 2 ≤ h) (k : Fin 4) : Fin (elemWallNumVerts h) :=
  elemWallCoordIdx h (GM13.elementaryWallCorner h k)
    (elementaryWallCorner_mem_elementaryWallVerts h2 k)

/-- Index in `Fin (elemWallNumVerts h)` of the first middle vertex `(h, h / 2)` of the elementary
wall of height `h`. -/
def elemWallMiddle₁Idx {h : ℕ} (h2 : 2 ≤ h) : Fin (elemWallNumVerts h) :=
  elemWallCoordIdx h (GM13.elementaryWallMiddle₁ h)
    (elementaryWallMiddle₁_mem_elementaryWallVerts h2)

/-- Index in `Fin (elemWallNumVerts h)` of the second middle vertex `(h + 1, h / 2)` of the
elementary wall of height `h`. -/
def elemWallMiddle₂Idx {h : ℕ} (h2 : 2 ≤ h) : Fin (elemWallNumVerts h) :=
  elemWallCoordIdx h (GM13.elementaryWallMiddle₂ h)
    (elementaryWallMiddle₂_mem_elementaryWallVerts h2)

theorem nodup_elemWallEdges (h : ℕ) : (elemWallEdges h).Nodup :=
  (nodup_allDirectedPairs _).filter _

theorem mem_elemWallEdges_iff (h : ℕ) (e : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)) :
    e ∈ elemWallEdges h ↔
      isElemWallEdgeCoord (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) = true := by
  simp [elemWallEdges, mem_allDirectedPairs, elemWallVertCoord]

theorem isElemWallEdgeCoord_lt {p q : ℕ × ℕ} (h : isElemWallEdgeCoord p q = true) :
    p.1 + p.2 < q.1 + q.2 := by
  unfold isElemWallEdgeCoord at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hy, hx⟩ | ⟨⟨hx, hy⟩, _⟩ <;> omega

theorem isElemWallEdgeCoord_asymm {p q : ℕ × ℕ}
    (h1 : isElemWallEdgeCoord p q = true) (h2 : isElemWallEdgeCoord q p = true) : False := by
  have hlt1 := isElemWallEdgeCoord_lt h1
  have hlt2 := isElemWallEdgeCoord_lt h2
  omega

/-- Equivalence between `GM13.elementaryWallAdj h p q` and `isElemWallEdgeCoord p q = true ∨
isElemWallEdgeCoord q p = true` on `GM13.elementaryWallVerts h`. -/
theorem elementaryWallAdj_iff_isElemWallEdgeCoord (h : ℕ) (p q : ℕ × ℕ) :
    GM13.elementaryWallAdj h p q ↔
      p ∈ GM13.elementaryWallVerts h ∧ q ∈ GM13.elementaryWallVerts h ∧
      (isElemWallEdgeCoord p q = true ∨ isElemWallEdgeCoord q p = true) := by
  unfold GM13.elementaryWallAdj isElemWallEdgeCoord
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.odd_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro (⟨hy, hx | hx⟩ | ⟨hx, ⟨hy, hpar⟩ | ⟨hy, hpar⟩⟩)
    · exact Or.inl (Or.inl ⟨hy, hx.symm⟩)
    · exact Or.inr (Or.inl ⟨hy.symm, hx.symm⟩)
    · exact Or.inl (Or.inr ⟨⟨hx, hy.symm⟩, hpar⟩)
    · exact Or.inr (Or.inr ⟨⟨hx.symm, hy.symm⟩, hpar⟩)
  · rintro ((⟨hy, hx⟩ | ⟨⟨hx, hy⟩, hpar⟩) | (⟨hy, hx⟩ | ⟨⟨hx, hy⟩, hpar⟩))
    · exact Or.inl ⟨hy, Or.inl hx.symm⟩
    · exact Or.inr ⟨hx, Or.inl ⟨hy.symm, hpar⟩⟩
    · exact Or.inl ⟨hy.symm, Or.inr hx.symm⟩
    · exact Or.inr ⟨hx.symm, Or.inr ⟨hy.symm, hpar⟩⟩

/-- Every vertex of `GM13.elementaryWallVerts h` (`1 ≤ h`) is adjacent to some vertex in
`GM13.elementaryWall h`. -/
theorem exists_elementaryWallAdj_of_mem {h : ℕ} (hh : 1 ≤ h) {p : ℕ × ℕ}
    (hp : p ∈ GM13.elementaryWallVerts h) :
    ∃ q, GM13.elementaryWallAdj h p q := by
  rcases p with ⟨x, y⟩
  have hp' := hp
  rcases hp' with ⟨hx, hy, h00, hlast⟩
  dsimp at hx hy
  by_cases hx0 : x = 0
  · subst hx0
    have hy1 : 1 ≤ y := by
      rcases Nat.eq_zero_or_pos y with rfl | hpos
      · exact False.elim (h00 rfl)
      · exact hpos
    refine ⟨(1, y), hp, ?_, Or.inl ⟨rfl, Or.inl rfl⟩⟩
    refine ⟨by omega, hy, ?_, ?_⟩
    · intro h; injection h with h1 _; omega
    · intro h; injection h with h1 _; omega
  · by_cases h10 : x = 1 ∧ y = 0
    · rcases h10 with ⟨rfl, rfl⟩
      refine ⟨(2, 0), hp, ?_, Or.inl ⟨rfl, Or.inl rfl⟩⟩
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro h; injection h with h1 _; omega
      · intro h; injection h with h1 h2; omega
    · refine ⟨(x - 1, y), hp, ?_, Or.inl ⟨rfl, Or.inr (by omega)⟩⟩
      refine ⟨by omega, hy, ?_, ?_⟩
      · intro h
        injection h with h1 h2
        exact h10 ⟨by omega, h2⟩
      · intro h
        injection h with h1 h2
        omega

/-- Unordered coordinate pair `s(p₁, p₂)` of the `k`-th edge of `elemWallEdges h`. -/
def elemWallEdgeSym2 (h : ℕ) (k : Fin (elemWallEdges h).length) : Sym2 (ℕ × ℕ) :=
  let e := (elemWallEdges h)[k.1]'k.2
  s(elemWallVertCoord h e.1, elemWallVertCoord h e.2)

theorem elemWallEdge_isElemWallEdgeCoord (h : ℕ) (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    isElemWallEdgeCoord (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) = true :=
  (mem_elemWallEdges_iff h _).mp (List.getElem_mem k.2)

theorem elemWallEdge_elementaryWallAdj (h : ℕ) (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    GM13.elementaryWallAdj h (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) := by
  intro e
  rw [elementaryWallAdj_iff_isElemWallEdgeCoord]
  exact ⟨elemWallVertCoord_mem_elementaryWallVerts h e.1,
    elemWallVertCoord_mem_elementaryWallVerts h e.2,
    Or.inl (elemWallEdge_isElemWallEdgeCoord h k)⟩

theorem elemWallEdgeSym2_mem_edgeSet (h : ℕ) (k : Fin (elemWallEdges h).length) :
    elemWallEdgeSym2 h k ∈ E(GM13.elementaryWall h) := by
  let e := (elemWallEdges h)[k.1]'k.2
  exact ⟨elemWallVertCoord h e.1, elemWallVertCoord h e.2, elemWallEdge_elementaryWallAdj h k, rfl⟩

theorem elemWallEdgeSym2_injective (h : ℕ) : Function.Injective (elemWallEdgeSym2 h) := by
  intro k₁ k₂ heq
  let e₁ := (elemWallEdges h)[k₁.1]'k₁.2
  let e₂ := (elemWallEdges h)[k₂.1]'k₂.2
  have h1 : isElemWallEdgeCoord (elemWallVertCoord h e₁.1) (elemWallVertCoord h e₁.2) = true :=
    elemWallEdge_isElemWallEdgeCoord h k₁
  have h2 : isElemWallEdgeCoord (elemWallVertCoord h e₂.1) (elemWallVertCoord h e₂.2) = true :=
    elemWallEdge_isElemWallEdgeCoord h k₂
  change s(elemWallVertCoord h e₁.1, elemWallVertCoord h e₁.2) =
    s(elemWallVertCoord h e₂.1, elemWallVertCoord h e₂.2) at heq
  rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have he_eq : e₁ = e₂ :=
      Prod.ext (elemWallVertCoord_injective h ha) (elemWallVertCoord_injective h hb)
    exact Fin.ext ((nodup_elemWallEdges h).getElem_inj_iff.mp he_eq)
  · rw [ha, hb] at h1
    exact False.elim (isElemWallEdgeCoord_asymm h1 h2)

theorem exists_elemWallEdgeSym2_of_elementaryWallAdj {h : ℕ} {p q : ℕ × ℕ}
    (hpq : GM13.elementaryWallAdj h p q) :
    ∃ k : Fin (elemWallEdges h).length, elemWallEdgeSym2 h k = s(p, q) := by
  obtain ⟨hp, hq, hdir | hrev⟩ := (elementaryWallAdj_iff_isElemWallEdgeCoord h p q).mp hpq
  · let u := elemWallCoordIdx h p hp
    let v := elemWallCoordIdx h q hq
    have hu : elemWallVertCoord h u = p := elemWallVertCoord_elemWallCoordIdx h hp
    have hv : elemWallVertCoord h v = q := elemWallVertCoord_elemWallCoordIdx h hq
    have hmem : (u, v) ∈ elemWallEdges h := by
      rw [mem_elemWallEdges_iff, hu, hv]
      exact hdir
    rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    unfold elemWallEdgeSym2
    dsimp only
    rw [heq, hu, hv]
  · let u := elemWallCoordIdx h q hq
    let v := elemWallCoordIdx h p hp
    have hu : elemWallVertCoord h u = q := elemWallVertCoord_elemWallCoordIdx h hq
    have hv : elemWallVertCoord h v = p := elemWallVertCoord_elemWallCoordIdx h hp
    have hmem : (u, v) ∈ elemWallEdges h := by
      rw [mem_elemWallEdges_iff, hu, hv]
      exact hrev
    rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    unfold elemWallEdgeSym2
    dsimp only
    rw [heq, hu, hv, Sym2.eq_swap]

/-- Find the edge index `k : Fin (elemWallEdges h).length` corresponding to `e : Sym2 (ℕ × ℕ)`. -/
def findElemWallEdgeIdx (h : ℕ) (e : Sym2 (ℕ × ℕ)) : Option (Fin (elemWallEdges h).length) :=
  (List.finRange (elemWallEdges h).length).find? (fun k => decide (elemWallEdgeSym2 h k = e))

@[simp]
theorem findElemWallEdgeIdx_elemWallEdgeSym2 (h : ℕ) (k : Fin (elemWallEdges h).length) :
    findElemWallEdgeIdx h (elemWallEdgeSym2 h k) = some k := by
  unfold findElemWallEdgeIdx
  cases hfind : (List.finRange (elemWallEdges h).length).find?
      (fun k' => decide (elemWallEdgeSym2 h k' = elemWallEdgeSym2 h k)) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind k (List.mem_finRange k)
    simp at hfalse
  | some k' =>
    have heq : elemWallEdgeSym2 h k' = elemWallEdgeSym2 h k := by
      simpa using List.find?_some hfind
    exact congrArg some (elemWallEdgeSym2_injective h heq)

/-! ### Section 3: Lifting `WallOfHeight` to `GM13.Wall` in `G.toGMDigraph.toGraph` -/

/-- Canonical edge triple `(u.1, v.1, 0)` or `(v.1, u.1, 0)` in `G.toGMDigraph.toGraph` for an
adjacent pair `u, v : Fin n` in `G.toSimpleGraph`. -/
def adjEdgeTriple {n : ℕ} (G : MultiDigraph n) (u v : Fin n) : ℕ × ℕ × ℕ :=
  if 0 < G.edgeMult u v then (u.1, v.1, 0) else (v.1, u.1, 0)

theorem isLink_adjEdgeTriple {n : ℕ} {G : MultiDigraph n} {u v : Fin n}
    (hadj : G.toSimpleGraph.Adj u v) :
    G.toGMDigraph.toGraph.IsLink (adjEdgeTriple G u v) u.1 v.1 := by
  rw [MultiDigraph.toSimpleGraph_adj] at hadj
  unfold adjEdgeTriple
  split_ifs with hpos
  · refine ⟨⟨u.2, v.2, hpos⟩, Or.inr ⟨rfl, rfl⟩⟩
  · have hvu : 0 < G.edgeMult v u := by
      rcases hadj.2 with huv | hvu
      · exact False.elim (hpos huv)
      · exact hvu
    refine ⟨⟨v.2, u.2, hvu⟩, Or.inl ⟨rfl, rfl⟩⟩

theorem sym2_ends_adjEdgeTriple {n : ℕ} (G : MultiDigraph n) (u v : Fin n) :
    s((adjEdgeTriple G u v).1, (adjEdgeTriple G u v).2.1) = s(u.1, v.1) := by
  unfold adjEdgeTriple
  split_ifs
  · rfl
  · exact Sym2.eq_swap

/-- Lift a non-empty `IsSimpleWalkList G L` to a `GraphWalk` in `G.toGMDigraph.toGraph`. -/
def toGMGraphWalk {n : ℕ} {G : MultiDigraph n} :
    ∀ {L : List (Fin n)} (hne : L ≠ []),
      WallOfHeight.IsSimpleWalkList G L →
      GraphWalk G.toGMDigraph.toGraph (L.head hne).1 (L.getLast hne).1
  | [], hne, _ => False.elim (hne rfl)
  | [_], _, _ => .nil (Fin.is_lt _)
  | _ :: v :: rest, _, hw =>
    .cons (isLink_adjEdgeTriple hw.1) (toGMGraphWalk (List.cons_ne_nil v rest) hw.2)

@[simp]
theorem support_toGMGraphWalk {n : ℕ} {G : MultiDigraph n} :
    ∀ {L : List (Fin n)} (hne : L ≠ []) (hw : WallOfHeight.IsSimpleWalkList G L),
      (toGMGraphWalk hne hw).support = L.map Fin.val
  | [], hne, _ => False.elim (hne rfl)
  | [_], _, _ => rfl
  | _ :: v :: rest, _, hw => by
    change _ :: (toGMGraphWalk (List.cons_ne_nil v rest) hw.2).support = _
    rw [support_toGMGraphWalk (List.cons_ne_nil v rest) hw.2]
    rfl

theorem isSimple_toGMGraphWalk {n : ℕ} {G : MultiDigraph n} {L : List (Fin n)}
    (hne : L ≠ []) (hw : WallOfHeight.IsSimpleWalkList G L) (hnd : L.Nodup) :
    (toGMGraphWalk hne hw).IsSimple := by
  unfold GraphWalk.IsSimple
  rw [support_toGMGraphWalk]
  exact hnd.map Fin.val_injective

theorem edges_toGMGraphWalk_ne_nil {n : ℕ} {G : MultiDigraph n} :
    ∀ {L : List (Fin n)} (hne : L ≠ []) (hw : WallOfHeight.IsSimpleWalkList G L),
      2 ≤ L.length → (toGMGraphWalk hne hw).edges ≠ []
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, _, hlen => by simp at hlen
  | _ :: _ :: _, _, _, _ => List.cons_ne_nil _ _

theorem exists_mem_of_mem_edges_toGMGraphWalk {n : ℕ} {G : MultiDigraph n} :
    ∀ {L : List (Fin n)} (hne : L ≠ []) (hw : WallOfHeight.IsSimpleWalkList G L)
      {b : ℕ × ℕ × ℕ},
      b ∈ (toGMGraphWalk hne hw).edges →
      ∃ x ∈ L, ∃ y ∈ L, x ≠ y ∧ s(b.1, b.2.1) = s(x.1, y.1)
  | [], hne, _, _, _ => False.elim (hne rfl)
  | [_], _, _, _, hb => by nomatch hb
  | u :: v :: rest, _, hw, b, hb => by
    rcases List.mem_cons.mp hb with rfl | htail
    · refine ⟨u, List.mem_cons_self, v, List.mem_cons_of_mem u List.mem_cons_self, hw.1.ne, ?_⟩
      exact sym2_ends_adjEdgeTriple G u v
    · rcases exists_mem_of_mem_edges_toGMGraphWalk (List.cons_ne_nil v rest) hw.2 htail with
        ⟨x, hx, y, hy, hne_xy, hsym⟩
      exact ⟨x, List.mem_cons_of_mem u hx, y, List.mem_cons_of_mem u hy, hne_xy, hsym⟩

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

theorem subdivPathVerts_ne_nil (k : Fin (elemWallEdges h).length) :
    W.subdivPathVerts k ≠ [] := by
  unfold subdivPathVerts
  simp

theorem two_le_length_subdivPathVerts (k : Fin (elemWallEdges h).length) :
    2 ≤ (W.subdivPathVerts k).length := by
  unfold subdivPathVerts
  simp

theorem head_subdivPathVerts (k : Fin (elemWallEdges h).length) :
    (W.subdivPathVerts k).head (W.subdivPathVerts_ne_nil k) =
      W.branchVert ((elemWallEdges h)[k.1]'k.2).1 := by
  unfold subdivPathVerts
  simp

theorem getLast_subdivPathVerts (k : Fin (elemWallEdges h).length) :
    (W.subdivPathVerts k).getLast (W.subdivPathVerts_ne_nil k) =
      W.branchVert ((elemWallEdges h)[k.1]'k.2).2 := by
  unfold subdivPathVerts
  simp

theorem mem_subdivPathVerts_iff (k : Fin (elemWallEdges h).length) (v : Fin n) :
    v ∈ W.subdivPathVerts k ↔
      v = W.branchVert ((elemWallEdges h)[k.1]'k.2).1 ∨
      v ∈ W.internalVerts k ∨
      v = W.branchVert ((elemWallEdges h)[k.1]'k.2).2 := by
  unfold subdivPathVerts
  simp

/-- The lifted `GraphWalk` in `G.toGMDigraph.toGraph` for the `k`-th subdivision path of `W`. -/
def subdivGraphWalk (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    GraphWalk G.toGMDigraph.toGraph
      ((W.subdivPathVerts k).head (W.subdivPathVerts_ne_nil k)).1
      ((W.subdivPathVerts k).getLast (W.subdivPathVerts_ne_nil k)).1 :=
  toGMGraphWalk (W.subdivPathVerts_ne_nil k) (hW.2.1 k).2

/-- The path subgraph `P_k ≤ G.toGMDigraph.toGraph` of the `k`-th subdivision path of `W`. -/
def subdivPathGraph (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    Graph ℕ (ℕ × ℕ × ℕ) :=
  GM09.walkSubgraph (W.subdivGraphWalk hW k)

theorem subdivPathGraph_le (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    W.subdivPathGraph hW k ≤ G.toGMDigraph.toGraph :=
  GM09.walkSubgraph_le _

theorem isGraphPathWithEnds_subdivPathGraph (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph (W.subdivPathGraph hW k)
      (W.branchVert e.1).1 (W.branchVert e.2).1 := by
  intro e
  have h1 : GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph (W.subdivPathGraph hW k)
      ((W.subdivPathVerts k).head (W.subdivPathVerts_ne_nil k)).1
      ((W.subdivPathVerts k).getLast (W.subdivPathVerts_ne_nil k)).1 :=
    GM09.isGraphPathWithEnds_walkSubgraph
      (isSimple_toGMGraphWalk (W.subdivPathVerts_ne_nil k) (hW.2.1 k).2 (hW.2.1 k).1)
  rwa [W.head_subdivPathVerts k, W.getLast_subdivPathVerts k] at h1

@[simp]
theorem vertexSet_subdivPathGraph (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    V(W.subdivPathGraph hW k) = {x : ℕ | x ∈ (W.subdivPathVerts k).map Fin.val} := by
  unfold subdivPathGraph subdivGraphWalk
  rw [GM09.vertexSet_walkSubgraph, support_toGMGraphWalk]

theorem edgeSet_subdivPathGraph_nonempty (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    E(W.subdivPathGraph hW k).Nonempty := by
  unfold subdivPathGraph subdivGraphWalk
  rw [GM09.edgeSet_walkSubgraph]
  have hne := edges_toGMGraphWalk_ne_nil (W.subdivPathVerts_ne_nil k) (hW.2.1 k).2
    (W.two_le_length_subdivPathVerts k)
  rcases List.exists_cons_of_ne_nil hne with ⟨b, bs, hbs⟩
  exact ⟨b, by simp [hbs]⟩

/-- Branch vertex in `ℕ` at coordinate `p : ℕ × ℕ`. -/
noncomputable def branchVertAtCoord (p : ℕ × ℕ) : ℕ :=
  if hp : p ∈ GM13.elementaryWallVerts h then
    (W.branchVert (elemWallCoordIdx h p hp)).1
  else 0

@[simp]
theorem branchVertAtCoord_of_mem {p : ℕ × ℕ} (hp : p ∈ GM13.elementaryWallVerts h) :
    W.branchVertAtCoord p = (W.branchVert (elemWallCoordIdx h p hp)).1 := by
  simp [branchVertAtCoord, hp]

@[simp]
theorem branchVertAtCoord_elemWallVertCoord (u : Fin (elemWallNumVerts h)) :
    W.branchVertAtCoord (elemWallVertCoord h u) = (W.branchVert u).1 := by
  rw [W.branchVertAtCoord_of_mem (elemWallVertCoord_mem_elementaryWallVerts h u),
    elemWallCoordIdx_elemWallVertCoord]

theorem branchVertAtCoord_injOn (hW : W.IsValid) :
    Set.InjOn W.branchVertAtCoord (GM13.elementaryWallVerts h) := by
  intro p₁ hp₁ p₂ hp₂ heq
  rw [W.branchVertAtCoord_of_mem hp₁, W.branchVertAtCoord_of_mem hp₂] at heq
  have hu_eq : elemWallCoordIdx h p₁ hp₁ = elemWallCoordIdx h p₂ hp₂ :=
    hW.1 (Fin.ext heq)
  have hc := congrArg (elemWallVertCoord h) hu_eq
  rwa [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at hc

theorem image_branchVertAtCoord_eq :
    W.branchVertAtCoord '' GM13.elementaryWallVerts h =
      {x : ℕ | ∃ u : Fin (elemWallNumVerts h), (W.branchVert u).1 = x} := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨elemWallCoordIdx h p hp, (W.branchVertAtCoord_of_mem hp).symm⟩
  · rintro ⟨u, rfl⟩
    exact ⟨elemWallVertCoord h u, elemWallVertCoord_mem_elementaryWallVerts h u,
      W.branchVertAtCoord_elemWallVertCoord u⟩

/-- Label in `ℕ × ℕ × ℕ` assigned to an elementary-wall edge `e : Sym2 (ℕ × ℕ)`. -/
def baseEdgeLabel (h : ℕ) (e : Sym2 (ℕ × ℕ)) : ℕ × ℕ × ℕ :=
  match findElemWallEdgeIdx h e with
  | some k => (k.1, 0, 0)
  | none => (0, 0, 0)

@[simp]
theorem baseEdgeLabel_elemWallEdgeSym2 (h : ℕ) (k : Fin (elemWallEdges h).length) :
    baseEdgeLabel h (elemWallEdgeSym2 h k) = (k.1, 0, 0) := by
  simp [baseEdgeLabel]

theorem baseEdgeLabel_injOn (h : ℕ) :
    Set.InjOn (baseEdgeLabel h) E(GM13.elementaryWall h) := by
  rintro e₁ ⟨p₁, q₁, hpq₁, rfl⟩ e₂ ⟨p₂, q₂, hpq₂, rfl⟩ heq
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq₁ with ⟨k₁, hk₁⟩
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq₂ with ⟨k₂, hk₂⟩
  rw [← hk₁, ← hk₂, baseEdgeLabel_elemWallEdgeSym2, baseEdgeLabel_elemWallEdgeSym2] at heq
  have hk_eq : k₁ = k₂ := Fin.ext (Prod.mk.inj heq).1
  rw [← hk₁, ← hk₂, hk_eq]

/-- Subdivision path subgraph in `G.toGMDigraph.toGraph` indexed by `e : Sym2 (ℕ × ℕ)`. -/
def subdivPathOfSym2 (hW : W.IsValid) (e : Sym2 (ℕ × ℕ)) : Graph ℕ (ℕ × ℕ × ℕ) :=
  match findElemWallEdgeIdx h e with
  | some k => W.subdivPathGraph hW k
  | none => ⊥

@[simp]
theorem subdivPathOfSym2_elemWallEdgeSym2 (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    W.subdivPathOfSym2 hW (elemWallEdgeSym2 h k) = W.subdivPathGraph hW k := by
  simp [subdivPathOfSym2]

theorem subdivPathOfSym2_le (hW : W.IsValid) {e : Sym2 (ℕ × ℕ)}
    (he : e ∈ E(GM13.elementaryWall h)) :
    W.subdivPathOfSym2 hW e ≤ G.toGMDigraph.toGraph := by
  rcases he with ⟨p, q, hpq, rfl⟩
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
  rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k]
  exact W.subdivPathGraph_le hW k

/-- Underlying `Graph ℕ (ℕ × ℕ × ℕ)` of `W` inside `G.toGMDigraph.toGraph`. -/
def toGMGraph (hW : W.IsValid) : Graph ℕ (ℕ × ℕ × ℕ) :=
  GM09.subgraphSUnion G.toGMDigraph.toGraph
    (W.subdivPathOfSym2 hW '' E(GM13.elementaryWall h))

theorem toGMGraph_le (hW : W.IsValid) :
    W.toGMGraph hW ≤ G.toGMDigraph.toGraph := by
  apply GM09.subgraphSUnion_le
  rintro P ⟨e, he, rfl⟩
  exact W.subdivPathOfSym2_le hW he

theorem subdivPathOfSym2_le_toGMGraph (hW : W.IsValid) {e : Sym2 (ℕ × ℕ)}
    (he : e ∈ E(GM13.elementaryWall h)) :
    W.subdivPathOfSym2 hW e ≤ W.toGMGraph hW := by
  apply GM09.le_subgraphSUnion
  · rintro P ⟨e', he', rfl⟩
    exact W.subdivPathOfSym2_le hW he'
  · exact ⟨e, he, rfl⟩

theorem vertexSet_subdivPathGraph_inter_branchVerts (hW : W.IsValid)
    (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    V(W.subdivPathGraph hW k) ∩ (W.branchVertAtCoord '' GM13.elementaryWallVerts h) =
      {(W.branchVert e.1).1, (W.branchVert e.2).1} := by
  intro e
  rw [W.vertexSet_subdivPathGraph hW k, W.image_branchVertAtCoord_eq]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_map, W.mem_subdivPathVerts_iff k,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, ⟨u, hu⟩⟩
    have hvu : v = W.branchVert u := Fin.ext hu.symm
    subst hvu
    rcases hv with heq1 | hint | heq2
    · exact Or.inl (congrArg Fin.val heq1)
    · exact False.elim (hW.2.2.1 k u hint)
    · exact Or.inr (congrArg Fin.val heq2)
  · rintro (rfl | rfl)
    · exact ⟨⟨W.branchVert e.1, Or.inl rfl, rfl⟩, ⟨e.1, rfl⟩⟩
    · exact ⟨⟨W.branchVert e.2, Or.inr (Or.inr rfl), rfl⟩, ⟨e.2, rfl⟩⟩

theorem mem_branchVerts_of_mem_subdivPathVerts_inter (hW : W.IsValid)
    {k₁ k₂ : Fin (elemWallEdges h).length} (hne : k₁ ≠ k₂) {v : Fin n}
    (hv₁ : v ∈ W.subdivPathVerts k₁) (hv₂ : v ∈ W.subdivPathVerts k₂) :
    v = W.branchVert ((elemWallEdges h)[k₁.1]'k₁.2).1 ∨
    v = W.branchVert ((elemWallEdges h)[k₁.1]'k₁.2).2 := by
  rw [W.mem_subdivPathVerts_iff k₁] at hv₁
  rw [W.mem_subdivPathVerts_iff k₂] at hv₂
  rcases hv₁ with rfl | hint₁ | rfl
  · exact Or.inl rfl
  · rcases hv₂ with rfl | hint₂ | rfl
    · exact False.elim (hW.2.2.1 k₁ _ hint₁)
    · exact False.elim (hW.2.2.2 k₁ k₂ hne hint₁ hint₂)
    · exact False.elim (hW.2.2.1 k₁ _ hint₁)
  · exact Or.inr rfl

theorem disjoint_subdivPathGraph (hW : W.IsValid)
    {k₁ k₂ : Fin (elemWallEdges h).length} (hne : k₁ ≠ k₂) :
    Disjoint E(W.subdivPathGraph hW k₁) E(W.subdivPathGraph hW k₂) ∧
    V(W.subdivPathGraph hW k₁) ∩ V(W.subdivPathGraph hW k₂) ⊆
      W.branchVertAtCoord '' GM13.elementaryWallVerts h := by
  constructor
  · rw [Set.disjoint_left]
    intro b hb₁ hb₂
    unfold subdivPathGraph subdivGraphWalk at hb₁ hb₂
    rw [GM09.edgeSet_walkSubgraph, Set.mem_ofPred_eq] at hb₁ hb₂
    rcases exists_mem_of_mem_edges_toGMGraphWalk (W.subdivPathVerts_ne_nil k₁) (hW.2.1 k₁).2 hb₁ with
      ⟨x₁, hx₁, y₁, hy₁, hne₁, hsym₁⟩
    rcases exists_mem_of_mem_edges_toGMGraphWalk (W.subdivPathVerts_ne_nil k₂) (hW.2.1 k₂).2 hb₂ with
      ⟨x₂, hx₂, y₂, hy₂, _, hsym₂⟩
    have hsym_eq : s(x₁, y₁) = s(x₂, y₂) := by
      have hval : s(x₁.1, y₁.1) = s(x₂.1, y₂.1) := hsym₁.symm.trans hsym₂
      rcases Sym2.eq_iff.mp hval with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [Fin.ext h1, Fin.ext h2]
      · rw [Fin.ext h1, Fin.ext h2, Sym2.eq_swap]
    have hx₁_k₂ : x₁ ∈ W.subdivPathVerts k₂ := by
      rcases Sym2.eq_iff.mp hsym_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hx₂
      · exact hy₂
    have hy₁_k₂ : y₁ ∈ W.subdivPathVerts k₂ := by
      rcases Sym2.eq_iff.mp hsym_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hy₂
      · exact hx₂
    let e₁ := (elemWallEdges h)[k₁.1]'k₁.2
    let e₂ := (elemWallEdges h)[k₂.1]'k₂.2
    have hx₁_br₁ := W.mem_branchVerts_of_mem_subdivPathVerts_inter hW hne hx₁ hx₁_k₂
    have hy₁_br₁ := W.mem_branchVerts_of_mem_subdivPathVerts_inter hW hne hy₁ hy₁_k₂
    have hx₁_br₂ := W.mem_branchVerts_of_mem_subdivPathVerts_inter hW hne.symm hx₁_k₂ hx₁
    have hy₁_br₂ := W.mem_branchVerts_of_mem_subdivPathVerts_inter hW hne.symm hy₁_k₂ hy₁
    have hs₁ : s(x₁, y₁) = s(W.branchVert e₁.1, W.branchVert e₁.2) := by
      rcases hx₁_br₁ with rfl | rfl <;> rcases hy₁_br₁ with heq | heq
      · exact False.elim (hne₁ heq.symm)
      · rw [heq]
      · rw [heq, Sym2.eq_swap]
      · exact False.elim (hne₁ heq.symm)
    have hs₂ : s(x₁, y₁) = s(W.branchVert e₂.1, W.branchVert e₂.2) := by
      rcases hx₁_br₂ with rfl | rfl <;> rcases hy₁_br₂ with heq | heq
      · exact False.elim (hne₁ heq.symm)
      · rw [heq]
      · rw [heq, Sym2.eq_swap]
      · exact False.elim (hne₁ heq.symm)
    have hbr_eq : s(W.branchVert e₁.1, W.branchVert e₁.2) =
        s(W.branchVert e₂.1, W.branchVert e₂.2) := hs₁.symm.trans hs₂
    have hsym_edge : elemWallEdgeSym2 h k₁ = elemWallEdgeSym2 h k₂ := by
      unfold elemWallEdgeSym2
      dsimp only
      rcases Sym2.eq_iff.mp hbr_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hW.1 h1, hW.1 h2]
      · rw [hW.1 h1, hW.1 h2, Sym2.eq_swap]
    exact hne (elemWallEdgeSym2_injective h hsym_edge)
  · rw [W.vertexSet_subdivPathGraph hW k₁, W.vertexSet_subdivPathGraph hW k₂,
      W.image_branchVertAtCoord_eq]
    rintro x ⟨hx₁, hx₂⟩
    simp only [Set.mem_ofPred_eq, List.mem_map] at hx₁ hx₂ ⊢
    rcases hx₁ with ⟨v₁, hv₁, rfl⟩
    rcases hx₂ with ⟨v₂, hv₂, heq⟩
    have hv_eq : v₁ = v₂ := Fin.ext heq.symm
    subst hv_eq
    rcases W.mem_branchVerts_of_mem_subdivPathVerts_inter hW hne hv₁ hv₂ with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- `GM13.WallData ℕ (ℕ × ℕ × ℕ) h` constructed from a valid `W : WallOfHeight h G` (`1 ≤ h`). -/
noncomputable def toWallData (hh : 1 ≤ h) (hW : W.IsValid) :
    GM13.WallData ℕ (ℕ × ℕ × ℕ) h where
  graph := W.toGMGraph hW
  c := W.branchVertAtCoord
  lab := baseEdgeLabel h
  P := W.subdivPathOfSym2 hW
  c_injOn := W.branchVertAtCoord_injOn hW
  lab_injOn := baseEdgeLabel_injOn h
  path p q hpq := by
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
    have he_mem : s(p, q) ∈ E(GM13.elementaryWall h) := ⟨p, q, hpq, rfl⟩
    have hsub : W.subdivPathOfSym2 hW s(p, q) ≤ W.toGMGraph hW :=
      W.subdivPathOfSym2_le_toGMGraph hW he_mem
    rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k] at hsub ⊢
    let e := (elemWallEdges h)[k.1]'k.2
    have hpathG := W.isGraphPathWithEnds_subdivPathGraph hW k
    have hpathW : GM09.IsGraphPathWithEnds (W.toGMGraph hW) (W.subdivPathGraph hW k)
        (W.branchVert e.1).1 (W.branchVert e.2).1 :=
      hpathG.of_le hsub
    have hsym : s(elemWallVertCoord h e.1, elemWallVertCoord h e.2) = s(p, q) := hk
    have hcp : W.branchVertAtCoord (elemWallVertCoord h e.1) = (W.branchVert e.1).1 :=
      W.branchVertAtCoord_elemWallVertCoord e.1
    have hcq : W.branchVertAtCoord (elemWallVertCoord h e.2) = (W.branchVert e.2).1 :=
      W.branchVertAtCoord_elemWallVertCoord e.2
    rcases Sym2.eq_iff.mp hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hcp, hcq]
      exact ⟨hpathW, W.edgeSet_subdivPathGraph_nonempty hW k,
        W.vertexSet_subdivPathGraph_inter_branchVerts hW k⟩
    · rw [hcp, hcq, Set.pair_comm]
      exact ⟨hpathW.symm, W.edgeSet_subdivPathGraph_nonempty hW k,
        W.vertexSet_subdivPathGraph_inter_branchVerts hW k⟩
  disjoint := by
    rintro e₁ ⟨p₁, q₁, hpq₁, rfl⟩ e₂ ⟨p₂, q₂, hpq₂, rfl⟩ hne
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq₁ with ⟨k₁, hk₁⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq₂ with ⟨k₂, hk₂⟩
    have hk_ne : k₁ ≠ k₂ := fun h => hne (by rw [← hk₁, ← hk₂, h])
    rw [← hk₁, ← hk₂, W.subdivPathOfSym2_elemWallEdgeSym2 hW k₁,
      W.subdivPathOfSym2_elemWallEdgeSym2 hW k₂]
    exact W.disjoint_subdivPathGraph hW hk_ne
  vertexSet_eq := by
    unfold toGMGraph
    rw [GM09.vertexSet_subgraphSUnion]
    have hiUnion :
        (⋃ P ∈ W.subdivPathOfSym2 hW '' E(GM13.elementaryWall h), V(P)) =
          ⋃ e ∈ E(GM13.elementaryWall h), V(W.subdivPathOfSym2 hW e) := by
      ext x
      simp
    rw [hiUnion]
    symm
    refine Set.union_eq_right.mpr ?_
    rintro x ⟨p, hp, rfl⟩
    rcases exists_elementaryWallAdj_of_mem hh hp with ⟨q, hpq⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
    have he_mem : s(p, q) ∈ E(GM13.elementaryWall h) := ⟨p, q, hpq, rfl⟩
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨s(p, q), he_mem, ?_⟩
    rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k]
    let e := (elemWallEdges h)[k.1]'k.2
    have hinter :
        V(W.subdivPathGraph hW k) ∩ (W.branchVertAtCoord '' GM13.elementaryWallVerts h) =
          {(W.branchVert e.1).1, (W.branchVert e.2).1} :=
      W.vertexSet_subdivPathGraph_inter_branchVerts hW k
    have hcp : W.branchVertAtCoord (elemWallVertCoord h e.1) = (W.branchVert e.1).1 :=
      W.branchVertAtCoord_elemWallVertCoord e.1
    have hcq : W.branchVertAtCoord (elemWallVertCoord h e.2) = (W.branchVert e.2).1 :=
      W.branchVertAtCoord_elemWallVertCoord e.2
    rcases Sym2.eq_iff.mp hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hmem_inter : (W.branchVert e.1).1 ∈
          V(W.subdivPathGraph hW k) ∩ (W.branchVertAtCoord '' GM13.elementaryWallVerts h) := by
        rw [hinter]; exact Or.inl rfl
      rw [hcp]
      exact hmem_inter.1
    · have hmem_inter : (W.branchVert e.2).1 ∈
          V(W.subdivPathGraph hW k) ∩ (W.branchVertAtCoord '' GM13.elementaryWallVerts h) := by
        rw [hinter]; exact Or.inr rfl
      rw [hcq]
      exact hmem_inter.1
  edgeSet_eq := by
    unfold toGMGraph
    rw [GM09.edgeSet_subgraphSUnion]
    · ext b
      simp
    · rintro P ⟨e, he, rfl⟩
      exact W.subdivPathOfSym2_le hW he

/-- Turn a valid `W : WallOfHeight h G` (`2 ≤ h`, `Even h`, `W.IsValid`) into a
`GM13.Wall ℕ (ℕ × ℕ × ℕ)` of height `h` in `G.toGMDigraph.toGraph`. -/
noncomputable def toGMWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    GM13.Wall ℕ (ℕ × ℕ × ℕ) :=
  GM13.Wall.ofData h2 he (W.toWallData (by omega) hW)

@[simp]
theorem toGMWall_height (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toGMWall h2 he hW).height = h := rfl

@[simp]
theorem toGMWall_graph (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toGMWall h2 he hW).graph = W.toGMGraph hW := rfl

/-- `W.toGMWall h2 he hW` is a wall in `G.toGMDigraph.toGraph` (`GM13.IsWallIn`). -/
theorem isWallIn_toGMWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    GM13.IsWallIn G.toGMDigraph.toGraph (W.toGMWall h2 he hW) :=
  W.toGMGraph_le hW

/-- For every coordinate `p ∈ GM13.elementaryWallVerts h`, the branch vertex of `W.toGMWall` at `p`
is `(W.branchVert (elemWallCoordIdx h p hp)).1`. -/
@[simp]
theorem toGMWall_branchVertex (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (p : ℕ × ℕ) (hp : p ∈ GM13.elementaryWallVerts h) :
    (W.toGMWall h2 he hW).branchVertex p hp = (W.branchVert (elemWallCoordIdx h p hp)).1 := by
  change W.branchVertAtCoord p = _
  exact W.branchVertAtCoord_of_mem hp

/-- For every index `u : Fin (elemWallNumVerts h)`, the branch vertex of `W.toGMWall` at
`elemWallVertCoord h u` is `(W.branchVert u).1`. -/
@[simp]
theorem toGMWall_branchVertex_elemWallVertCoord (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (u : Fin (elemWallNumVerts h)) :
    (W.toGMWall h2 he hW).branchVertex (elemWallVertCoord h u)
      (elemWallVertCoord_mem_elementaryWallVerts h u) = (W.branchVert u).1 := by
  rw [W.toGMWall_branchVertex h2 he hW, elemWallCoordIdx_elemWallVertCoord]

/-- Each corner `(W.toGMWall h2 he hW).corner k` (`k : Fin 4`) is the image under `W.branchVert` of
the `k`-th corner `elemWallCornerIdx h2 k` of the elementary wall. -/
@[simp]
theorem toGMWall_corner (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (k : Fin 4) :
    (W.toGMWall h2 he hW).corner k = (W.branchVert (elemWallCornerIdx h2 k)).1 := by
  unfold GM13.Wall.corner elemWallCornerIdx
  exact W.toGMWall_branchVertex h2 he hW (GM13.elementaryWallCorner h k)
    (elementaryWallCorner_mem_elementaryWallVerts h2 k)

/-- The first middle vertex `(W.toGMWall h2 he hW).middleVertex₁` is the image under `W.branchVert`
of the first middle vertex `elemWallMiddle₁Idx h2` of the elementary wall. -/
@[simp]
theorem toGMWall_middleVertex₁ (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toGMWall h2 he hW).middleVertex₁ = (W.branchVert (elemWallMiddle₁Idx h2)).1 := by
  unfold GM13.Wall.middleVertex₁ elemWallMiddle₁Idx
  exact W.toGMWall_branchVertex h2 he hW (GM13.elementaryWallMiddle₁ h)
    (elementaryWallMiddle₁_mem_elementaryWallVerts h2)

/-- The second middle vertex `(W.toGMWall h2 he hW).middleVertex₂` is the image under `W.branchVert`
of the second middle vertex `elemWallMiddle₂Idx h2` of the elementary wall. -/
@[simp]
theorem toGMWall_middleVertex₂ (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toGMWall h2 he hW).middleVertex₂ = (W.branchVert (elemWallMiddle₂Idx h2)).1 := by
  unfold GM13.Wall.middleVertex₂ elemWallMiddle₂Idx
  exact W.toGMWall_branchVertex h2 he hW (GM13.elementaryWallMiddle₂ h)
    (elementaryWallMiddle₂_mem_elementaryWallVerts h2)

end WallOfHeight

end GraphMinor.Compute
