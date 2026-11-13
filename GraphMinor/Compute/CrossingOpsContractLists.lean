module

public import GraphMinor.Compute.CrossingOpsLists
public import GraphMinor.Crossing.DefsContract

/-!
# The adjacency lists of a contracted graph

Section 9 of `docs/crossing/crossing_extractor.tex`: "Contract $uv$ to a new vertex $w$, suppressing
loops and duplicate edges." The merged vertex keeps the name `v` (`contractGraph`). This file says
how the program of `CrossingOpsContract.lean` builds the new adjacency lists from the old ones
`lists`, and proves that they are the adjacency lists of `contractGraph G u v`
(`isAdjListFamily_contrList`):
* the list of `u` is empty;
* the list of `v` is the old list of `v` without `u`, followed by the old neighbours of `u` other
  than `v` that are not already neighbours of `v`;
* the list of any other vertex `x` is its old list with `u` replaced by `v`, or with `u` dropped
  when `v` is already a neighbour of `x`.

It also proves the facts about the cycle and the vertex set that the program uses
(`contractCycle_map`, `isSupportedOn_contractGraph`).
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- The old list of the vertex `x`, as a function of numbers. -/
def listOf {N : ℕ} (lists : Fin N → List ℕ) (x : ℕ) : List ℕ :=
  if h : x < N then lists ⟨x, h⟩ else []

theorem listOf_fin {N : ℕ} (lists : Fin N → List ℕ) (x : Fin N) : listOf lists x = lists x := by
  simp [listOf, x.2]

/-- The new list of the vertex `v` after the contraction of `uv`. -/
def contrListV (lu lv : List ℕ) (u v : ℕ) : List ℕ :=
  lv.filter (fun y => y ≠ u) ++ lu.filter (fun y => y ≠ v ∧ y ∉ lv)

/-- The new list of a vertex `x` other than `u` and `v`: `u` is dropped when `v` is already in
the list, and replaced by `v` otherwise. -/
def contrListO (lx : List ℕ) (u v : ℕ) : List ℕ :=
  if v ∈ lx then lx.filter (fun y => y ≠ u) else lx.map (fun y => if y = u then v else y)

/-- What the program emits for the entry `y` of the list of `x`, when `c` says whether `v` is in
the list. -/
def contrEmitO (c : Prop) [Decidable c] (u v y : ℕ) : List ℕ :=
  if y = u then (if c then [] else [v]) else [y]

theorem flatMap_contrEmitO (lx : List ℕ) (u v : ℕ) :
    lx.flatMap (contrEmitO (v ∈ lx) u v) = contrListO lx u v := by
  have key : ∀ (c : Prop) [Decidable c] (l : List ℕ), l.flatMap (contrEmitO c u v) =
      if c then l.filter (fun y => y ≠ u) else l.map (fun y => if y = u then v else y) := by
    intro c _ l
    induction l with
    | nil => split_ifs <;> simp
    | cons a l ih =>
      rw [List.flatMap_cons, ih]
      by_cases hc : c <;> by_cases ha : a = u <;> simp [contrEmitO, hc, ha, List.filter_cons]
  rw [key, contrListO]

/-- **The new adjacency lists** after the contraction of `uv`. -/
def contrList {N : ℕ} (lists : Fin N → List ℕ) (u v : ℕ) (x : ℕ) : List ℕ :=
  if x = u then []
  else if x = v then contrListV (listOf lists u) (listOf lists v) u v
  else contrListO (listOf lists x) u v

theorem mem_contrListO {lx : List ℕ} {u v y : ℕ} :
    y ∈ contrListO lx u v ↔ (y ∈ lx ∧ y ≠ u) ∨ (y = v ∧ u ∈ lx ∧ v ∉ lx) := by
  unfold contrListO
  split_ifs with hv
  · simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · exact Or.inl
    · rintro (h | ⟨rfl, -, h⟩)
      · exact h
      · exact absurd hv h
  · simp only [List.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      split_ifs with hzu
      · exact Or.inr ⟨rfl, hzu ▸ hz, hv⟩
      · exact Or.inl ⟨hz, hzu⟩
    · rintro (⟨hy, hyu⟩ | ⟨rfl, hu, -⟩)
      · exact ⟨y, hy, by simp [hyu]⟩
      · exact ⟨u, hu, by simp⟩

theorem nodup_contrListO {lx : List ℕ} {u v : ℕ} (hnd : lx.Nodup) :
    (contrListO lx u v).Nodup := by
  unfold contrListO
  split_ifs with hv
  · exact hnd.filter _
  · refine hnd.map_on (fun x hx y hy hxy => ?_)
    by_cases hxu : x = u <;> by_cases hyu : y = u <;> simp only [hxu, hyu, if_true, if_false] at hxy
    · rw [hxu, hyu]
    · exact absurd (hxy ▸ hy) hv
    · exact absurd (hxy ▸ hx) hv
    · exact hxy

theorem mem_contrListV {lu lv : List ℕ} {u v y : ℕ} :
    y ∈ contrListV lu lv u v ↔ (y ∈ lv ∧ y ≠ u) ∨ (y ∈ lu ∧ y ≠ v ∧ y ∉ lv) := by
  simp [contrListV]

theorem nodup_contrListV {lu lv : List ℕ} {u v : ℕ} (hu : lu.Nodup) (hv : lv.Nodup) :
    (contrListV lu lv u v).Nodup := by
  unfold contrListV
  refine List.Nodup.append (hv.filter _) (hu.filter _) ?_
  intro y hy1 hy2
  simp only [List.mem_filter, decide_eq_true_eq] at hy1 hy2
  exact hy2.2.2 hy1.1

/-- **The new lists are the adjacency lists of the contracted graph.** -/
theorem isAdjListFamily_contrList {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) {u v : Fin N} (huv : G.Adj u v) :
    IsAdjListFamily (contractGraph G u v) (fun x => contrList lists u v x) := by
  have hne : u.val ≠ v.val := fun e => huv.ne (Fin.ext e)
  have hmem : ∀ (x y : Fin N), y.val ∈ listOf lists x ↔ G.Adj x y := fun x y => by
    rw [listOf_fin]; exact (h x).2.2.2 y
  have hlt : ∀ (x : ℕ), ∀ y ∈ listOf lists x, y < N := fun x y hy => by
    unfold listOf at hy; split_ifs at hy with hx
    · exact (h ⟨x, hx⟩).1 y hy
    · simp at hy
  have hnd : ∀ x, (listOf lists x).Nodup := fun x => by
    unfold listOf; split_ifs with hx
    · exact (h ⟨x, hx⟩).2.1
    · simp
  -- the membership
  have hmemc : ∀ (x y : Fin N), y.val ∈ contrList lists u v x ↔ (contractGraph G u v).Adj x y := by
    intro x y
    simp only [contrList, contractGraph]
    by_cases hxu : x = u
    · subst hxu; simp
    · have hxu' : x.val ≠ u.val := fun e => hxu (Fin.ext e)
      by_cases hxv : x = v
      · subst hxv
        simp only [hxu', if_false, if_true, mem_contrListV, hmem]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
          · exact ⟨h1.ne, hxu, fun e => h2 (e ▸ rfl), Or.inl h1⟩
          · refine ⟨fun e => h2 (e ▸ rfl), hxu, fun e => ?_, Or.inr (Or.inl ⟨by trivial, h1⟩)⟩
            subst e; exact G.loopless.irrefl _ h1
        · rintro ⟨h1, -, h3, h4 | ⟨-, h4⟩ | ⟨h4, -⟩⟩
          · exact Or.inl ⟨h4, fun e => h3 (Fin.ext e)⟩
          · by_cases hy : G.Adj x y
            · exact Or.inl ⟨hy, fun e => h3 (Fin.ext e)⟩
            · exact Or.inr ⟨h4, fun e => h1 (Fin.ext e).symm, hy⟩
          · exact absurd h4.symm h1
      · have hxv' : x.val ≠ v.val := fun e => hxv (Fin.ext e)
        simp only [hxu', hxv', if_false, mem_contrListO]
        rw [hmem x y, hmem x u, hmem x v]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
          · exact ⟨h1.ne, hxu, fun e => h2 (e ▸ rfl), Or.inl h1⟩
          · have hy : y = v := Fin.ext h1
            subst hy
            exact ⟨hxv, hxu, fun e => huv.ne e.symm, Or.inr (Or.inr ⟨rfl, h2.symm⟩)⟩
        · rintro ⟨h1, -, h3, h4 | ⟨h4, -⟩ | ⟨h4, h5⟩⟩
          · exact Or.inl ⟨h4, fun e => h3 (Fin.ext e)⟩
          · exact absurd h4 hxv
          · subst h4
            by_cases hy : G.Adj x y
            · exact Or.inl ⟨hy, fun e => h3 (Fin.ext e)⟩
            · exact Or.inr ⟨rfl, h5.symm, hy⟩
  have hltc : ∀ (x : ℕ), ∀ y ∈ contrList lists u v x, y < N := by
    intro x y hy
    unfold contrList at hy
    split_ifs at hy
    · simp at hy
    · rcases mem_contrListV.mp hy with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hlt _ y h1
      · exact hlt _ y h1
    · rcases mem_contrListO.mp hy with ⟨h1, -⟩ | ⟨rfl, -⟩
      · exact hlt _ y h1
      · exact v.2
  have hndc : ∀ x, (contrList lists u v x).Nodup := by
    intro x
    unfold contrList
    split_ifs
    · simp
    · exact nodup_contrListV (hnd _) (hnd _)
    · exact nodup_contrListO (hnd _)
  intro x
  refine ⟨hltc x, hndc x, length_le_of_nodup_lt (hndc x) (hltc x), fun y => hmemc x y⟩

/-! ### The cycle and the vertex set -/

theorem contractCycle_map {N : ℕ} {D : List (Fin N)} (hD : D.Nodup) (u : Fin N) :
    (contractCycle D u).map Fin.val = (D.map Fin.val).filter (fun y => y ≠ u.val) := by
  unfold contractCycle
  split_ifs with hu
  · rw [hD.erase_eq_filter, List.filter_map]
    congr 1
  · symm
    rw [List.filter_eq_self]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    have : z ≠ u := fun e => hu (e ▸ hz)
    simpa [Fin.ext_iff] using this

theorem isSupportedOn_contractGraph {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    (hS : HP25.IsSupportedOn G (S : Set (Fin N))) {u v : Fin N} (huv : G.Adj u v) :
    HP25.IsSupportedOn (contractGraph G u v) ((S.erase u : Finset (Fin N)) : Set (Fin N)) := by
  intro x y h
  obtain ⟨-, hxu, -, h1 | ⟨rfl, -⟩ | ⟨-, h3⟩⟩ := h
  · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨hS h1, hxu⟩
  · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨hS huv.symm, hxu⟩
  · simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    exact ⟨hS h3.symm, hxu⟩

end GraphMinor.Compute.Crossing
