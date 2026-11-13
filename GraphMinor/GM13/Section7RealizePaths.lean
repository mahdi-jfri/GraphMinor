module

public import GraphMinor.GM13.Section7RealizeHole

/-!
# Graph Minors XIII, (7.3): realizations from paths given as functions

A realization (`Shape.Realization`) asks for the old path of each new edge as a list. When the
paths have a length that depends on parameters (as for the hexagonal hole, whose staircases
have `4b + 1` edges), it is easier to give the path of an edge `pq` that goes right or up as a
function `f p q : ℕ → ℕ × ℕ` with a length `n p q`: the path is `f p q 0, …, f p q (n p q)`.
`Shape.Realization.ofPaths` turns such data into a realization; every condition is asked one
index at a time.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

namespace Shape

variable {h h' : ℕ} {τ : Shape h h'}

/-- The inner vertices of the path `f 0, …, f n`. -/
def pathInner (f : ℕ → ℕ × ℕ) (n : ℕ) : List (ℕ × ℕ) := (List.range (n - 1)).map (fun i => f (i + 1))

theorem pathInner_full {f : ℕ → ℕ × ℕ} {n : ℕ} (hn : 1 ≤ n) :
    f 0 :: (pathInner f n ++ [f n]) = (List.range (n + 1)).map f := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold pathInner
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_sub_cancel, List.range_succ,
    List.map_append]
  rfl

theorem mem_pathInner {f : ℕ → ℕ × ℕ} {n : ℕ} {u : ℕ × ℕ} (hu : u ∈ pathInner f n) :
    ∃ i, 1 ≤ i ∧ i < n ∧ u = f i := by
  unfold pathInner at hu
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hu
  rw [List.mem_range] at hi
  exact ⟨i + 1, by omega, by omega, rfl⟩

theorem mem_pathInner_of {f : ℕ → ℕ × ℕ} {n i : ℕ} (h1 : 1 ≤ i) (h2 : i < n) :
    f i ∈ pathInner f n := by
  unfold pathInner
  refine List.mem_map.mpr ⟨i - 1, List.mem_range.mpr (by omega), ?_⟩
  congr 1
  omega

theorem mem_zip_range_map {f : ℕ → ℕ × ℕ} {n i : ℕ} (hi : i < n) :
    (f i, f (i + 1)) ∈ ((List.range (n + 1)).map f).zip ((List.range (n + 1)).map f).tail := by
  rw [List.mem_iff_getElem]
  refine ⟨i, by simp; omega, ?_⟩
  simp

theorem mem_zip_range_map_iff {f : ℕ → ℕ × ℕ} {n : ℕ} {uw : (ℕ × ℕ) × (ℕ × ℕ)}
    (h : uw ∈ ((List.range (n + 1)).map f).zip ((List.range (n + 1)).map f).tail) :
    ∃ i < n, uw = (f i, f (i + 1)) := by
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only [List.length_zip, List.length_map, List.length_range, List.length_tail] at hi
  refine ⟨i, by omega, ?_⟩
  simp

/-- The path of an edge, in both directions: given by `f` for an edge that goes right or up, and
reversed otherwise. -/
def pathsInner (n : ℕ × ℕ → ℕ × ℕ → ℕ) (f : ℕ × ℕ → ℕ × ℕ → ℕ → ℕ × ℕ) (p q : ℕ × ℕ) :
    List (ℕ × ℕ) :=
  if p.1 + p.2 < q.1 + q.2 then pathInner (f p q) (n p q) else (pathInner (f q p) (n q p)).reverse

/-- **A realization from paths given as functions.** For each new edge `pq` that goes right or
up, `f p q` is a path of `n p q ≥ 1` old edges from `vmap p` to `vmap q`; each of its edges and
inner vertices goes to `pq`, and it does not repeat vertices. Every kept old element is the old
vertex of a new vertex, or an inner vertex or an edge of one of these paths. -/
def Realization.ofPaths (vmap : ℕ × ℕ → ℕ × ℕ) (n : ℕ × ℕ → ℕ × ℕ → ℕ)
    (f : ℕ × ℕ → ℕ × ℕ → ℕ → ℕ × ℕ)
    (vmap_mem : ∀ p ∈ elementaryWallVerts h', vmap p ∈ elementaryWallVerts h)
    (hn : ∀ p q, elementaryWallAdj h' p q → p.1 + p.2 < q.1 + q.2 → 1 ≤ n p q)
    (h0 : ∀ p q, elementaryWallAdj h' p q → p.1 + p.2 < q.1 + q.2 → f p q 0 = vmap p)
    (hlast : ∀ p q, elementaryWallAdj h' p q → p.1 + p.2 < q.1 + q.2 → f p q (n p q) = vmap q)
    (step : ∀ p q, elementaryWallAdj h' p q → p.1 + p.2 < q.1 + q.2 → ∀ i < n p q,
      elementaryWallAdj h (f p q i) (f p q (i + 1)) ∧
        τ.own (eCell (f p q i) (f p q (i + 1))) = some (eCell p q))
    (inj : ∀ p q, elementaryWallAdj h' p q → p.1 + p.2 < q.1 + q.2 → ∀ i j, i ≤ n p q →
      j ≤ n p q → f p q i = f p q j → i = j)
    (own_vmap : ∀ p ∈ elementaryWallVerts h', τ.own (vCell (vmap p)) = some (vCell p))
    (own_inner : ∀ p q, elementaryWallAdj h' p q → p.1 + p.2 < q.1 + q.2 → ∀ i, 1 ≤ i →
      i < n p q → τ.own (vCell (f p q i)) = some (eCell p q))
    (own_cover : ∀ m ∈ fig1WallCells h, τ.own m ≠ none →
      (∃ p ∈ elementaryWallVerts h', m = vCell (vmap p)) ∨
      ∃ p q, elementaryWallAdj h' p q ∧ p.1 + p.2 < q.1 + q.2 ∧
        ((∃ i, 1 ≤ i ∧ i < n p q ∧ m = vCell (f p q i)) ∨
          ∃ i < n p q, m = eCell (f p q i) (f p q (i + 1)))) :
    τ.Realization :=
  have full : ∀ p q, elementaryWallAdj h' p q → p.1 + p.2 < q.1 + q.2 →
      vmap p :: (pathsInner n f p q ++ [vmap q]) = (List.range (n p q + 1)).map (f p q) :=
    fun p q hpq hlt => by
      unfold pathsInner
      rw [if_pos hlt, ← h0 p q hpq hlt, ← hlast p q hpq hlt]
      exact pathInner_full (hn p q hpq hlt)
  Realization.ofOriented (fun p q => elementaryWallAdj h' p q ∧ p.1 + p.2 < q.1 + q.2)
    vmap (pathsInner n f)
    (fun p q hpq => by
      have hne : p.1 + p.2 ≠ q.1 + q.2 := by
        obtain ⟨-, -, h | ⟨h1, h | h⟩⟩ := hpq <;> omega
      by_cases h : p.1 + p.2 < q.1 + q.2
      · exact Or.inl ⟨hpq, h⟩
      · exact Or.inr ⟨elementaryWallAdj_symm hpq, by omega⟩)
    (fun _ _ h => h.1)
    vmap_mem
    (fun p q hpq => by
      have hne : p.1 + p.2 ≠ q.1 + q.2 := by
        obtain ⟨-, -, h | ⟨h1, h | h⟩⟩ := hpq <;> omega
      unfold pathsInner
      by_cases h1 : p.1 + p.2 < q.1 + q.2
      · rw [if_neg (by omega), if_pos h1]
      · rw [if_pos (by omega), if_neg h1, List.reverse_reverse])
    (fun p q ⟨hpq, hlt⟩ => by
      rw [full p q hpq hlt, List.isChain_map, ← Nat.succ_eq_add_one, List.isChain_range_succ]
      exact fun i hi => step p q hpq hlt i hi)
    (fun p q ⟨hpq, hlt⟩ => by
      rw [full p q hpq hlt]
      refine List.Nodup.map_on ?_ List.nodup_range
      intro i hi j hj e
      rw [List.mem_range] at hi hj
      exact inj p q hpq hlt i j (by omega) (by omega) e)
    own_vmap
    (fun p q ⟨hpq, hlt⟩ u hu => by
      unfold pathsInner at hu
      rw [if_pos hlt] at hu
      obtain ⟨i, h1, h2, rfl⟩ := mem_pathInner hu
      exact own_inner p q hpq hlt i h1 h2)
    (fun m hm hown => by
      rcases own_cover m hm hown with h | ⟨p, q, hpq, hlt, ⟨i, h1, h2, rfl⟩ | ⟨i, hi, rfl⟩⟩
      · exact Or.inl h
      · refine Or.inr ⟨p, q, hpq, Or.inl ⟨f p q i, ?_, rfl⟩⟩
        unfold pathsInner
        rw [if_pos hlt]
        exact mem_pathInner_of h1 h2
      · refine Or.inr ⟨p, q, hpq, Or.inr ⟨(f p q i, f p q (i + 1)), ?_, rfl⟩⟩
        have e1 := full p q hpq hlt
        have e2 : pathsInner n f p q ++ [vmap q] = ((List.range (n p q + 1)).map (f p q)).tail := by
          rw [← e1]; rfl
        rw [e1, e2]
        exact mem_zip_range_map hi)

end Shape

end GraphMinor.GM13
