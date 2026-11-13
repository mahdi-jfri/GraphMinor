module

public import GraphMinor.Wagner.GraphTools

/-!
# Paths that join two of several disjoint vertex sets

Let `A i` be pairwise disjoint vertex sets inside `W`, and suppose that `W` induces a preconnected
subgraph containing vertices of two different sets. Then there is a path of `K` inside `W` that
starts in one set `A i`, ends in another set `A j`, and whose inner vertices lie in no set `A k`
(`exists_hpath`).

The proof walks along a path from the first set to the second and stops at the first vertex that
lies in a set other than the current one.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

/-- A path of `K` inside `W` between two vertices that are joined inside `W`, as a list. -/
theorem exists_pathList_of_reachable {W : Set γ} {x y : γ} (hx : x ∈ W) (hy : y ∈ W)
    (h : (K.induce W).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    ∃ l : List γ, l.Nodup ∧ l.IsChain K.Adj ∧ (∀ z ∈ l, z ∈ W) ∧ l.head? = some x ∧
      l.getLast? = some y := by
  classical
  obtain ⟨w⟩ := h
  let p := w.toPath
  refine ⟨p.1.support.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
  · exact p.2.support_nodup.map Subtype.val_injective
  · exact (List.isChain_map Subtype.val).mpr p.1.isChain_adj_support
  · intro z hz
    obtain ⟨z', -, rfl⟩ := List.mem_map.mp hz
    exact z'.2
  · rw [← Walk.cons_tail_support]
    rfl
  · rw [List.getLast?_map, List.getLast?_eq_some_getLast p.1.support_ne_nil, Walk.getLast_support]
    rfl

/-- A list in which some entry satisfies `P` splits at the first such entry. -/
theorem exists_first (P : γ → Prop) :
    ∀ l : List γ, (∃ z ∈ l, P z) → ∃ mid w rest, l = mid ++ w :: rest ∧ P w ∧ ∀ z ∈ mid, ¬ P z
  | [], ⟨z, hz, _⟩ => (List.not_mem_nil hz).elim
  | a :: l, h => by
    by_cases ha : P a
    · exact ⟨[], a, l, rfl, ha, by simp⟩
    · have h' : ∃ z ∈ l, P z := by
        obtain ⟨z, hz, hPz⟩ := h
        rcases List.mem_cons.mp hz with rfl | hz
        · exact (ha hPz).elim
        · exact ⟨z, hz, hPz⟩
      obtain ⟨mid, w, rest, rfl, hw, hmid⟩ := exists_first P l h'
      refine ⟨a :: mid, w, rest, rfl, hw, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ha
      · exact hmid z hz

variable {ι : Type*}

/-- The conclusion of `exists_hpath`: a path `a :: mid ++ [b]` from a set `A i` to a different set
`A j` whose inner vertices `mid` lie in `W` and in no set `A k`. -/
def HPathConcl (K : SimpleGraph γ) (W : Set γ) (A : ι → Set γ) : Prop :=
  ∃ (i j : ι) (a b : γ) (mid : List γ), i ≠ j ∧ a ∈ A i ∧ b ∈ A j ∧
    (∀ z ∈ mid, z ∈ W ∧ ∀ k, z ∉ A k) ∧ (a :: mid ++ [b]).Nodup ∧
    (a :: mid ++ [b]).IsChain K.Adj

theorem hpath_of_list {W : Set γ} (A : ι → Set γ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    ∀ (n : ℕ) (l : List γ), l.length ≤ n → ∀ (x : γ) (i : ι) (y : γ) (j : ι), l.Nodup →
      l.IsChain K.Adj → (∀ z ∈ l, z ∈ W) → l.head? = some x → l.getLast? = some y →
      x ∈ A i → y ∈ A j → i ≠ j → HPathConcl K W A := by
  intro n
  induction n with
  | zero =>
    intro l hl x i y j _ _ _ hh
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)] at hh
    simp at hh
  | succ n ih =>
    intro l hl x i y j hnd hch hW hh hlast hx hy hij
    rcases l with _ | ⟨x', l'⟩
    · simp at hh
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    -- The last vertex `y` lies in the tail `l'`.
    have hyl : y ∈ x' :: l' := List.mem_of_getLast? hlast
    have hyx : y ≠ x' := by
      rintro rfl
      exact disjoint_left.mp (hdisj i j hij) hx hy
    have hyl' : y ∈ l' := by
      rcases List.mem_cons.mp hyl with h | h
      · exact (hyx h).elim
      · exact h
    obtain ⟨mid, w, rest, rfl, ⟨k, hwk⟩, hmid⟩ :=
      exists_first (fun z => ∃ k, z ∈ A k) l' ⟨y, hyl', j, hy⟩
    have hsplit : x' :: (mid ++ w :: rest) = (x' :: mid ++ [w]) ++ rest := by simp
    by_cases hki : k = i
    · -- Restart from `w`, which lies in the same set as `x'`.
      subst hki
      have hsuf : x' :: (mid ++ w :: rest) = (x' :: mid) ++ (w :: rest) := by simp
      rw [hsuf] at hnd hch hW hlast hl
      refine ih (w :: rest) ?_ w k y j ?_ ?_ ?_ rfl ?_ hwk hy hij
      · simp only [List.length_append, List.length_cons] at hl ⊢
        omega
      · exact (List.nodup_append.mp hnd).2.1
      · exact hch.right_of_append
      · exact fun z hz => hW z (List.mem_append_right _ hz)
      · rw [List.getLast?_append] at hlast
        simpa using hlast
    · refine ⟨i, k, x', w, mid, Ne.symm hki, hx, hwk, ?_, ?_, ?_⟩
      · intro z hz
        refine ⟨hW z (by simp [hz]), fun k' hk' => hmid z hz ⟨k', hk'⟩⟩
      · rw [hsplit] at hnd
        exact (List.nodup_append.mp hnd).1
      · rw [hsplit] at hch
        exact hch.left_of_append

/-- **H-paths.** If `W` induces a preconnected subgraph and contains a vertex of `A i` and a vertex
of `A j` for some `i ≠ j`, where the sets `A k ⊆ W` are pairwise disjoint, then some path inside
`W` goes from one set `A i'` to another set `A j'` with no inner vertex in any set `A k`. -/
theorem exists_hpath {W : Set γ} (hW : (K.induce W).Preconnected) (A : ι → Set γ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hAW : ∀ i, A i ⊆ W) {i j : ι} (hij : i ≠ j)
    {x y : γ} (hx : x ∈ A i) (hy : y ∈ A j) : HPathConcl K W A := by
  obtain ⟨l, hnd, hch, hlW, hh, hl⟩ :=
    exists_pathList_of_reachable (hAW i hx) (hAW j hy) (hW ⟨x, hAW i hx⟩ ⟨y, hAW j hy⟩)
  exact hpath_of_list A hdisj l.length l le_rfl x i y j hnd hch hlW hh hl hx hy hij

end GraphMinor.Wagner
