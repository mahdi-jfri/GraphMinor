module

public import GraphMinor.GM13.Section7Realize
public import GraphMinor.GM13.Section7Translate
public import GraphMinor.GM13.Section7Rotate

/-!
# Graph Minors XIII, (7.3): realizations of the moved and the turned subwalls

A realization (`Shape.Realization`, in `Section7Realize.lean`) of a shape gives, inside any wall
`W` of height `h`, a wall of height `h'` whose pieces are the kept elements of `W`. This file
gives realizations of two kinds of shapes used in the proof of (7.3) (Graph Minors XIII,
page 90): the subwall `T(i, 1)` moved by `(i, 1)`, and the turn of a shape by 180 degrees.

* `isWallCell_cases`: every cell of the wall of Fig. 1 is the cell of a vertex or of an edge.
* `transRealization`: the realization of `T(i, 1)`. The vertex `p` goes to `p + (i, 1)`.
* `Shape.Realization.rotate`: a realization of `τ` gives one of `τ.rotate`. The turn of a vertex
  `p` of the elementary wall of height `h` is `rotV h p = (2h + 1 - p.1, h - p.2)`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-! ## The cells of vertices and edges -/

theorem isWallCell_vCell {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    IsWallCell h (vCell p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have h3' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun e => h3 (Prod.ext e.1 e.2)
  have h4' : ¬ (p.1 = 2 * h + 1 ∧ p.2 = h) := fun e => h4 (Prod.ext e.1 e.2)
  unfold IsWallCell vCell
  simp only
  omega

theorem isWallCell_eCell {h : ℕ} (he : Even h) {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    IsWallCell h (eCell p q) := by
  obtain ⟨⟨hp1, hp2, hp3, hp4⟩, ⟨hq1, hq2, hq3, hq4⟩, hadj⟩ := hpq
  have hp3' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun e => hp3 (Prod.ext e.1 e.2)
  have hp4' : ¬ (p.1 = 2 * h + 1 ∧ p.2 = h) := fun e => hp4 (Prod.ext e.1 e.2)
  have hq3' : ¬ (q.1 = 0 ∧ q.2 = 0) := fun e => hq3 (Prod.ext e.1 e.2)
  have hq4' : ¬ (q.1 = 2 * h + 1 ∧ q.2 = h) := fun e => hq4 (Prod.ext e.1 e.2)
  obtain ⟨k, hk⟩ := he
  unfold IsWallCell eCell
  simp only [Nat.odd_iff] at hadj ⊢
  omega

/-- Every cell of the wall is the cell of a vertex or of an edge. -/
theorem isWallCell_cases {h : ℕ} (he : Even h) {c : ℤ × ℤ} (hc : IsWallCell h c) :
    (∃ p ∈ elementaryWallVerts h, c = vCell p) ∨
      ∃ p q, elementaryWallAdj h p q ∧ c = eCell p q := by
  obtain ⟨a, b⟩ := c
  obtain ⟨k, hk⟩ := he
  unfold IsWallCell at hc
  simp only at hc
  obtain ⟨x, hx⟩ : ∃ x : ℕ, (x : ℤ) = a / 2 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨y, hy⟩ : ∃ y : ℕ, (y : ℤ) = b / 2 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
  rcases Int.emod_two_eq_zero_or_one b with hb | hb
  · left
    refine ⟨(x, y), ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · simp only [vCell, Prod.mk.injEq]; omega
  · right
    refine ⟨(x, y), (x, y + 1),
      ⟨⟨by simp only; omega, by simp only; omega, ?_, ?_⟩,
        ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · right; simp only [Nat.odd_iff, true_and]; omega
    · simp only [eCell, Prod.mk.injEq]; omega
  · right
    refine ⟨(x, y), (x + 1, y),
      ⟨⟨by simp only; omega, by simp only; omega, ?_, ?_⟩,
        ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · left; simp
    · simp only [eCell, Prod.mk.injEq]; omega
  · omega

/-- **The moved subwall `T(i, 1)` as a realization.** The vertex `p` goes to `p + (i, 1)`, and each
edge to the edge between the moved ends. -/
def transRealization (h' : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i : ℕ} (hi : i = 1 ∨ i = 3) :
    (transShape1 h' hh' he' (i := (i : ℤ)) (by omega)).Realization where
  vmap p := (p.1 + i, p.2 + 1)
  inner _ _ := []
  vmap_mem p hp := by
    obtain ⟨h1, h2, h3, h4⟩ := hp
    refine ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩ <;>
      intro e <;> simp only [Prod.mk.injEq] at e <;> omega
  inner_symm _ _ _ := rfl
  chain p q hpq := by
    obtain ⟨⟨hp1, hp2, hp3, hp4⟩, ⟨hq1, hq2, hq3, hq4⟩, hadj⟩ := hpq
    simp only [List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true]
    refine ⟨⟨by simp only; omega, by simp only; omega, ?_, ?_⟩,
      ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · simp only [Nat.odd_iff] at hadj ⊢
      omega
  nodup p q hpq := by
    obtain ⟨-, -, hadj⟩ := hpq
    simp only [List.nil_append, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true, Prod.mk.injEq]
    omega
  own_vmap p hp := by
    change transOwn h' i 1 _ = _
    unfold transOwn
    have e : ((vCell (p.1 + i, p.2 + 1)).1 - 2 * (i : ℤ), (vCell (p.1 + i, p.2 + 1)).2 - 2 * 1) =
        vCell p := by
      simp only [vCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    simp only [isWallCell_vCell hp, ↓reduceIte]
  own_inner _ _ _ u hu := absurd hu (List.not_mem_nil)
  own_step p q hpq uw huw := by
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at huw
    subst huw
    change transOwn h' i 1 _ = _
    unfold transOwn
    have e : ((eCell (p.1 + i, p.2 + 1) (q.1 + i, q.2 + 1)).1 - 2 * (i : ℤ),
        (eCell (p.1 + i, p.2 + 1) (q.1 + i, q.2 + 1)).2 - 2 * 1) = eCell p q := by
      simp only [eCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    simp only [isWallCell_eCell he' hpq, ↓reduceIte]
  own_cover m hm hown := by
    obtain ⟨a, b⟩ := m
    change transOwn h' i 1 (a, b) ≠ none at hown
    unfold transOwn at hown
    split_ifs at hown with hc
    · rcases isWallCell_cases he' hc with ⟨p, hp, e⟩ | ⟨p, q, hpq, e⟩
      · left
        refine ⟨p, hp, ?_⟩
        simp only [vCell, Prod.mk.injEq] at e ⊢
        push_cast
        omega
      · right
        refine ⟨p, q, hpq, Or.inr ⟨((p.1 + i, p.2 + 1), (q.1 + i, q.2 + 1)), by simp, ?_⟩⟩
        simp only [eCell, Prod.mk.injEq] at e ⊢
        push_cast
        omega
    · exact absurd rfl hown

/-! ## The turn of a realization -/

/-- The vertex of the elementary wall of height `h` across the centre from `p`. -/
def rotV (h : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (2 * h + 1 - p.1, h - p.2)

theorem rotV_mem {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    rotV h p ∈ elementaryWallVerts h := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have h3' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun e => h3 (Prod.ext e.1 e.2)
  have h4' : ¬ (p.1 = 2 * h + 1 ∧ p.2 = h) := fun e => h4 (Prod.ext e.1 e.2)
  refine ⟨by simp only [rotV]; omega, by simp only [rotV]; omega, ?_, ?_⟩ <;>
    intro e <;> simp only [rotV, Prod.mk.injEq] at e <;> omega

theorem rotV_rotV {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) : rotV h (rotV h p) = p := by
  obtain ⟨h1, h2, -, -⟩ := hp
  simp only [rotV]
  ext <;> simp only <;> omega

theorem adj_rotV {h : ℕ} (he : Even h) {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    elementaryWallAdj h (rotV h p) (rotV h q) := by
  refine ⟨rotV_mem hpq.1, rotV_mem hpq.2.1, ?_⟩
  obtain ⟨⟨hp1, hp2, -, -⟩, ⟨hq1, hq2, -, -⟩, hadj⟩ := hpq
  obtain ⟨k, hk⟩ := he
  simp only [rotV, Nat.odd_iff] at hadj ⊢
  omega

theorem vCell_rotV {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    vCell (rotV h p) = rotC h (vCell p) := by
  obtain ⟨h1, h2, -, -⟩ := hp
  simp only [vCell, rotV, rotC, Prod.mk.injEq]
  omega

theorem eCell_rotV {h : ℕ} {p q : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h)
    (hq : q ∈ elementaryWallVerts h) :
    eCell (rotV h p) (rotV h q) = rotC h (eCell p q) := by
  obtain ⟨h1, h2, -, -⟩ := hp
  obtain ⟨h3, h4, -, -⟩ := hq
  simp only [eCell, rotV, rotC, Prod.mk.injEq]
  omega

/-- The vertices of a list of the elementary wall, each joined to the next, are vertices. -/
theorem mem_verts_of_isChain {h : ℕ} : ∀ {a : ℕ × ℕ} {l : List (ℕ × ℕ)},
    List.IsChain (elementaryWallAdj h) (a :: l) → a ∈ elementaryWallVerts h →
    ∀ u ∈ a :: l, u ∈ elementaryWallVerts h
  | _, [], _, ha, u, hu => by rw [List.mem_singleton.mp hu]; exact ha
  | a, b :: l, hc, ha, u, hu => by
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ha
    · have hab := (List.isChain_cons_cons.mp hc).1
      exact mem_verts_of_isChain (List.isChain_cons_cons.mp hc).2 hab.2.1 u hu

namespace Shape.Realization

variable {h h' : ℕ} {τ : Shape h h'} (R : τ.Realization)

theorem mem_verts_of_mem_full {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) {u : ℕ × ℕ}
    (hu : u ∈ R.full p q) : u ∈ elementaryWallVerts h :=
  mem_verts_of_isChain (R.chain p q hpq) (R.vmap_mem p hpq.1) u hu

/-- **The turn of a realization.** A realization of `τ` gives one of the turned shape: the new
vertex `p` goes to the turn of the old vertex of the turn of `p`. -/
def rotate (hh : 1 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h') :
    (τ.rotate hh he hh' he').Realization where
  vmap p := rotV h (R.vmap (rotV h' p))
  inner p q := (R.inner (rotV h' p) (rotV h' q)).map (rotV h)
  vmap_mem p hp := rotV_mem (R.vmap_mem _ (rotV_mem hp))
  inner_symm p q hpq := by
    rw [R.inner_symm _ _ (adj_rotV he' hpq), List.map_reverse]
  chain p q hpq := by
    have hc := R.chain _ _ (adj_rotV he' hpq)
    have e : rotV h (R.vmap (rotV h' p)) :: ((R.inner (rotV h' p) (rotV h' q)).map (rotV h) ++
        [rotV h (R.vmap (rotV h' q))]) = (R.full (rotV h' p) (rotV h' q)).map (rotV h) := by
      simp [full]
    rw [e, List.isChain_map]
    exact hc.imp fun a b hab => adj_rotV he hab
  nodup p q hpq := by
    have e : rotV h (R.vmap (rotV h' p)) :: ((R.inner (rotV h' p) (rotV h' q)).map (rotV h) ++
        [rotV h (R.vmap (rotV h' q))]) = (R.full (rotV h' p) (rotV h' q)).map (rotV h) := by
      simp [full]
    rw [e]
    refine List.Nodup.map_on ?_ (R.nodup _ _ (adj_rotV he' hpq))
    intro x hx y hy exy
    rw [← rotV_rotV (R.mem_verts_of_mem_full (adj_rotV he' hpq) hx),
      ← rotV_rotV (R.mem_verts_of_mem_full (adj_rotV he' hpq) hy), exy]
  own_vmap p hp := by
    have hp' := rotV_mem hp
    show (τ.own (rotC h (vCell (rotV h (R.vmap (rotV h' p)))))).map (rotC h') = _
    rw [vCell_rotV (R.vmap_mem _ hp'), rotC_rotC, R.own_vmap _ hp', Option.map_some,
      ← vCell_rotV hp', rotV_rotV hp]
  own_inner p q hpq u hu := by
    have hpq' := adj_rotV he' hpq
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu
    have hw' : w ∈ elementaryWallVerts h :=
      R.mem_verts_of_mem_full hpq' (by simp [full, hw])
    show (τ.own (rotC h (vCell (rotV h w)))).map (rotC h') = _
    rw [vCell_rotV hw', rotC_rotC, R.own_inner _ _ hpq' w hw, Option.map_some,
      ← eCell_rotV hpq'.1 hpq'.2.1, rotV_rotV hpq.1, rotV_rotV hpq.2.1]
  own_step p q hpq uw huw := by
    have hpq' := adj_rotV he' hpq
    have e1 : rotV h (R.vmap (rotV h' p)) :: ((R.inner (rotV h' p) (rotV h' q)).map (rotV h) ++
        [rotV h (R.vmap (rotV h' q))]) = (R.full (rotV h' p) (rotV h' q)).map (rotV h) := by
      simp [full]
    have e2 : (R.inner (rotV h' p) (rotV h' q)).map (rotV h) ++ [rotV h (R.vmap (rotV h' q))] =
        (R.inner (rotV h' p) (rotV h' q) ++ [R.vmap (rotV h' q)]).map (rotV h) := by
      simp
    rw [e1, e2, List.zip_map, List.mem_map] at huw
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := huw
    have ha : a ∈ elementaryWallVerts h :=
      R.mem_verts_of_mem_full hpq' (List.of_mem_zip hab).1
    have hb : b ∈ elementaryWallVerts h :=
      R.mem_verts_of_mem_full hpq' (by simpa [full] using Or.inr (List.of_mem_zip hab).2)
    show (τ.own (rotC h (eCell (rotV h a) (rotV h b)))).map (rotC h') = _
    rw [eCell_rotV ha hb, rotC_rotC, R.own_step _ _ hpq' (a, b) hab, Option.map_some,
      ← eCell_rotV hpq'.1 hpq'.2.1, rotV_rotV hpq.1, rotV_rotV hpq.2.1]
  own_cover m hm hown := by
    have hm' := (mem_fig1WallCells_rotC hh he).mpr hm
    have hown' : τ.own (rotC h m) ≠ none := by
      intro e; apply hown; show (τ.own (rotC h m)).map (rotC h') = none; rw [e]; rfl
    rcases R.own_cover _ hm' hown' with ⟨p, hp, e⟩ | ⟨p, q, hpq, ⟨u, hu, e⟩ | ⟨⟨a, b⟩, hab, e⟩⟩
    · refine Or.inl ⟨rotV h' p, rotV_mem hp, ?_⟩
      show m = vCell (rotV h (R.vmap (rotV h' (rotV h' p))))
      rw [rotV_rotV hp, vCell_rotV (R.vmap_mem p hp), ← e, rotC_rotC]
    · have hpq' := adj_rotV he' hpq
      have hu' : u ∈ elementaryWallVerts h := R.mem_verts_of_mem_full hpq (by simp [full, hu])
      refine Or.inr ⟨rotV h' p, rotV h' q, hpq', Or.inl ⟨rotV h u, ?_, ?_⟩⟩
      · show rotV h u ∈ (R.inner (rotV h' (rotV h' p)) (rotV h' (rotV h' q))).map (rotV h)
        rw [rotV_rotV hpq.1, rotV_rotV hpq.2.1]
        exact List.mem_map_of_mem hu
      · rw [vCell_rotV hu', ← e, rotC_rotC]
    · have hpq' := adj_rotV he' hpq
      have ha : a ∈ elementaryWallVerts h :=
        R.mem_verts_of_mem_full hpq (List.of_mem_zip hab).1
      have hb : b ∈ elementaryWallVerts h :=
        R.mem_verts_of_mem_full hpq (by simpa [full] using Or.inr (List.of_mem_zip hab).2)
      refine Or.inr ⟨rotV h' p, rotV h' q, hpq', Or.inr ⟨(rotV h a, rotV h b), ?_, ?_⟩⟩
      · show (rotV h a, rotV h b) ∈ (rotV h (R.vmap (rotV h' (rotV h' p))) ::
          ((R.inner (rotV h' (rotV h' p)) (rotV h' (rotV h' q))).map (rotV h) ++
            [rotV h (R.vmap (rotV h' (rotV h' q)))])).zip
          ((R.inner (rotV h' (rotV h' p)) (rotV h' (rotV h' q))).map (rotV h) ++
            [rotV h (R.vmap (rotV h' (rotV h' q)))])
        rw [rotV_rotV hpq.1, rotV_rotV hpq.2.1]
        have e1 : rotV h (R.vmap p) :: ((R.inner p q).map (rotV h) ++ [rotV h (R.vmap q)]) =
            (R.vmap p :: (R.inner p q ++ [R.vmap q])).map (rotV h) := by simp
        have e2 : (R.inner p q).map (rotV h) ++ [rotV h (R.vmap q)] =
            (R.inner p q ++ [R.vmap q]).map (rotV h) := by simp
        rw [e1, e2, List.zip_map]
        exact List.mem_map_of_mem (f := Prod.map (rotV h) (rotV h)) hab
      · show m = eCell (rotV h a) (rotV h b)
        rw [eCell_rotV ha hb, ← e, rotC_rotC]

end Shape.Realization

end GraphMinor.GM13
