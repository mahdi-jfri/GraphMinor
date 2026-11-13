module

public import GraphMinor.Compute.TwoPathsLoopSpec
public import GraphMinor.Compute.TwoPathsSearchWalk
public import GraphMinor.Compute.TwoPathsSplit
import GraphMinor.HP25.Sec5Lemma54
import GraphMinor.HP25.Sec5Loop
import GraphMinor.HP25.Sec5StripTools

/-!
# Mathematical lemmas for the loop of Algorithm 5.2

This file proves the graph, walk and list lemmas that connect one iteration of the Word RAM loop
for Algorithm 5.2 (`GraphMinor/Compute/TwoPathsLoop.lean`) to the mathematical theorems of
`GraphMinor/HP25/Sec5Complete.lean`:

* `pairGraph_append_pair` and `isNewEdgeList_append_pair`: appending `[y.1, s.1]` to the flat edge
  list `F` adds `edge y s` to `pairGraph N F` and preserves `IsNewEdgeList`;
* `isOnSide_iff_of_edges_in_path`: when every edge outside `H` has both endpoints on the current
  path `P`, a vertex of `P` is on side `A` (or `B`) in `H ⊔ pairGraph N F` if and only if it is on
  that side in `H`, so the searches of the loop only need the original graph `H`;
* `isOnSide_iff_exists_adj_items`: after a search of `H` from an arc `S` (`A` or `B`) with the rest
  of `C` and `P` forbidden (`labArc`), a vertex of `P` is on side `S` if and only if it has a
  neighbour in `H` that was reached by the search;
* `loop_step_math`: one step of the loop from the index `r` of the first vertex of `P` not on both
  sides and the index `idx_s > r` of the first vertex after `r` on the missing side.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph Set GraphMinor.HP25

variable {N : ℕ}

/-! ### Appending an edge to `F` -/

/-- Appending two entries `y, s` (`y ≠ s`) to an even-length list `F` adds `edge y s` to
`pairGraph N F`. -/
theorem pairGraph_append_pair {F : List ℕ} (hF : Even F.length) {y s : Fin N} (hys : y ≠ s) :
    pairGraph N (F ++ [y.1, s.1]) = pairGraph N F ⊔ edge y s := by
  obtain ⟨k, hk⟩ := hF
  have hk' : F.length = 2 * k := by omega
  ext u v
  simp only [pairGraph, sup_adj, edge_adj]
  constructor
  · rintro ⟨huv, i, hi⟩
    by_cases hik : i < k
    · left
      refine ⟨huv, i, ?_⟩
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)] at hi
      exact hi
    · by_cases heq : i = k
      · right
        subst heq
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
          show 2 * i - F.length = 0 by omega, show 2 * i + 1 - F.length = 1 by omega] at hi
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi
        rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨Or.inl ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩, huv⟩
        · exact ⟨Or.inr ⟨Fin.ext h2.symm, Fin.ext h1.symm⟩, huv⟩
      · exfalso
        have hnone : (F ++ [y.1, s.1])[2 * i]? = none :=
          List.getElem?_eq_none (by simp [hk']; omega)
        rcases hi with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [hnone] at h1
  · rintro (⟨huv, i, hi⟩ | ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, huv⟩)
    · have hik : 2 * i + 1 < F.length := by
        rcases hi with ⟨-, h⟩ | ⟨-, h⟩ <;> exact (List.getElem?_eq_some_iff.mp h).1
      refine ⟨huv, i, ?_⟩
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      exact hi
    · refine ⟨huv, k, Or.inl ?_⟩
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        show 2 * k - F.length = 0 by omega, show 2 * k + 1 - F.length = 1 by omega]
      simp
    · refine ⟨huv, k, Or.inr ?_⟩
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        show 2 * k - F.length = 0 by omega, show 2 * k + 1 - F.length = 1 by omega]
      simp

/-- The empty list is a valid `IsNewEdgeList`. -/
theorem isNewEdgeList_nil (H : SimpleGraph (Fin N)) (Pv : List (Fin N)) :
    IsNewEdgeList H Pv [] :=
  ⟨Even.zero, fun _ h => by simp at h, fun _ _ _ h => by simp at h⟩

/-- Appending a new non-edge `[y.1, s.1]` on `Pv` preserves `IsNewEdgeList`. -/
theorem isNewEdgeList_append_pair {H : SimpleGraph (Fin N)} {Pv : List (Fin N)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) {y s : Fin N} (hys : y ≠ s) (hyP : y ∈ Pv) (hsP : s ∈ Pv)
    (hH : ¬ H.Adj y s) (hdup : ¬ (pairGraph N F).Adj y s) :
    IsNewEdgeList H Pv (F ++ [y.1, s.1]) := by
  obtain ⟨⟨k, hk⟩, hpair, hnodup⟩ := hF
  have hk' : F.length = 2 * k := by omega
  refine ⟨⟨k + 1, by simp [hk]; omega⟩, fun i hi => ?_, fun i j hij hj => ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at hi
    by_cases hik : i < k
    · obtain ⟨u, v, h1, h2, rest⟩ := hpair i (by omega)
      refine ⟨u, v, ?_, ?_, rest⟩
      · rw [List.getElem?_append_left (by omega)]; exact h1
      · rw [List.getElem?_append_left (by omega)]; exact h2
    · have hik' : i = k := by omega
      subst hik'
      refine ⟨y, s, ?_, ?_, hys, hyP, hsP, hH⟩
      · rw [List.getElem?_append_right (by omega), show 2 * i - F.length = 0 by omega]; rfl
      · rw [List.getElem?_append_right (by omega), show 2 * i + 1 - F.length = 1 by omega]; rfl
  · simp only [List.length_append, List.length_cons, List.length_nil] at hj
    have hi0 : (F ++ [y.1, s.1])[2 * i]? = F[2 * i]? := List.getElem?_append_left (by omega)
    have hi1 : (F ++ [y.1, s.1])[2 * i + 1]? = F[2 * i + 1]? := List.getElem?_append_left (by omega)
    rw [hi0, hi1]
    by_cases hjk : j < k
    · have hj0 : (F ++ [y.1, s.1])[2 * j]? = F[2 * j]? := List.getElem?_append_left (by omega)
      have hj1 : (F ++ [y.1, s.1])[2 * j + 1]? = F[2 * j + 1]? :=
        List.getElem?_append_left (by omega)
      rw [hj0, hj1]
      exact hnodup i j hij (by omega)
    · have hjk' : j = k := by omega
      subst hjk'
      have hj0 : (F ++ [y.1, s.1])[2 * j]? = some y.1 := by
        rw [List.getElem?_append_right (by omega), show 2 * j - F.length = 0 by omega]; rfl
      have hj1 : (F ++ [y.1, s.1])[2 * j + 1]? = some s.1 := by
        rw [List.getElem?_append_right (by omega), show 2 * j + 1 - F.length = 1 by omega]; rfl
      rw [hj0, hj1]
      intro h
      exact hdup ⟨hys, i, h⟩

/-- In an induced path `L₁ ++ y :: (t :: N') ++ s :: L₂`, `y` and `s` are distinct and not adjacent. -/
theorem not_adj_of_induced_split {V : Type*} {G : SimpleGraph V} {a b y t s : V}
    {L₁ N' L₂ : List V} {P : G.Walk a b}
    (hsupp : P.support = L₁ ++ y :: (t :: N') ++ s :: L₂) (hnd : P.support.Nodup)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v) :
    y ≠ s ∧ ¬ G.Adj y s := by
  have hnd' : (L₁ ++ y :: t :: (N' ++ s :: L₂)).Nodup := by simpa [hsupp] using hnd
  have hys : y ≠ s := by
    intro h
    subst h
    rw [List.nodup_append, List.nodup_cons] at hnd'
    exact hnd'.2.1.1 (by simp)
  refine ⟨hys, fun hadj => ?_⟩
  have he : IsListEdge (L₁ ++ y :: t :: (N' ++ s :: L₂)) s y := by
    have := (hind y (by rw [hsupp]; simp) s (by rw [hsupp]; simp) hadj).symm
    simpa [hsupp] using this
  have hst : s = t := eq_of_isListEdge_next hnd' he (by simp)
  subst hst
  rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd'
  exact hnd'.2.1.2.1 (by simp)

/-! ### Sides in `H + F` vs sides in `H` -/

/-- A walk of `G` whose edges all lie in `H` lifts to a walk of `H` with the same support. -/
theorem exists_walk_of_not_adj {V : Type*} {H G : SimpleGraph V} :
    ∀ {u v : V} (p : G.Walk u v), (∀ x y, s(x, y) ∈ p.edges → H.Adj x y) →
      ∃ q : H.Walk u v, q.support = p.support
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, .cons hadj p, he => by
    obtain ⟨q, hq⟩ := exists_walk_of_not_adj p (fun x y h => he x y (List.mem_cons_of_mem _ h))
    exact ⟨.cons (he _ _ (List.mem_cons_self ..)) q, by simp [hq]⟩

/-- When every edge of `G` outside `H` has both endpoints in `Pv` and `S` is disjoint from `Pv`,
a vertex of `Pv` is on side `S` in `G` if and only if it is on side `S` in `H`. -/
theorem isOnSide_iff_of_edges_in_path {V : Type*} {H G : SimpleGraph V} (hle : H ≤ G)
    {C Pv S : List V} (hadj : ∀ u v, G.Adj u v → H.Adj u v ∨ (u ∈ Pv ∧ v ∈ Pv))
    (hSP : ∀ x ∈ S, x ∉ Pv) {v : V} (hv : v ∈ Pv) :
    IsOnSide G {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ S} v ↔
      IsOnSide H {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ S} v := by
  refine ⟨fun h => ?_, fun h => IsConnectedAvoiding.mono hle h Subset.rfl⟩
  obtain ⟨u, hu, p, hp, hin⟩ := h
  have hvu : v ≠ u := fun e => hSP u hu (e ▸ hv)
  cases p with
  | nil => exact absurd rfl hvu
  | @cons _ w _ hvw q =>
    have hqP : ∀ z ∈ q.support, z ∉ Pv := fun z hz hzP => by
      have hzv : z ≠ v := fun e => ((Walk.cons_isPath_iff _ _).mp hp).2 (e ▸ hz)
      by_cases hzu : z = u
      · exact hSP u hu (hzu ▸ hzP)
      · exact hin z (List.mem_cons_of_mem _ hz) hzv hzu (Or.inr hzP)
    have hwP : w ∉ Pv := hqP w q.start_mem_support
    have hvwH : H.Adj v w := (hadj v w hvw).resolve_right fun h => hwP h.2
    obtain ⟨qH, hqH⟩ := exists_walk_of_not_adj q fun x y hxy => by
      have hx : x ∈ q.support := Walk.fst_mem_support_of_mem_edges q hxy
      exact (hadj x y (q.adj_of_mem_edges hxy)).resolve_right fun h => hqP x hx h.1
    refine isConnectedAvoiding_of_walk_mem hu (.cons hvwH qH) fun z hz hzX => ?_
    rw [Walk.support_cons, hqH, ← Walk.support_cons hvw] at hz
    by_cases hzv : z = v
    · exact Or.inl hzv
    · by_cases hzu : z = u
      · exact Or.inr hzu
      · exact absurd hzX (hin z hz hzv hzu)

/-! ### Sides from the BFS search -/

/-- The initial label function for the search from an arc `S` of `C`: vertices of `S` and vertices
outside `C ∪ Pv` are free (`0`), and vertices of `(C ∪ Pv) \ S` are forbidden (`2`). -/
def labArc (C Pv S : List (Fin N)) (x : Fin N) : ℕ :=
  if x ∈ S then 0 else if x ∈ Pv then 2 else if x ∈ C then 2 else 0

theorem labArc_le_three (C Pv S : List (Fin N)) (x : Fin N) : labArc C Pv S x ≤ 3 := by
  unfold labArc; split_ifs <;> omega

theorem labArc_eq_zero_iff {C Pv S : List (Fin N)} {x : Fin N} :
    labArc C Pv S x = 0 ↔ x ∈ S ∨ (x ∉ C ∧ x ∉ Pv) := by
  unfold labArc
  by_cases hxS : x ∈ S
  · simp [hxS]
  · by_cases hxP : x ∈ Pv
    · simp [hxS, hxP]
    · by_cases hxC : x ∈ C <;> simp [hxS, hxP, hxC]

/-- **Characterization of `IsOnSide` from the search.** After `searchProg` runs on `H` with labels
`labArc C Pv S` and sources `S.map Fin.val`, a vertex `v ∈ Pv` is on side `S` if and only if some
neighbour of `v` in `H` was reached (`w.1 ∈ items`). -/
theorem isOnSide_iff_exists_adj_items {H : SimpleGraph (Fin N)} {C Pv S : List (Fin N)}
    (hSP : ∀ x ∈ S, x ∉ Pv) {s₀ s : State} {items : List ℕ}
    (hs : SInv H (labArc C Pv S) (S.map Fin.val) s₀ items items.length s)
    {v : Fin N} (hv : v ∈ Pv) :
    IsOnSide H {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ S} v ↔ ∃ w : Fin N, H.Adj v w ∧ w.1 ∈ items := by
  constructor
  · rintro ⟨u, hu, p, hp, hin⟩
    have hvu : v ≠ u := fun e => hSP u hu (e ▸ hv)
    cases p with
    | nil => exact absurd rfl hvu
    | @cons _ w _ hadj q =>
      refine ⟨w, hadj, hs.mem_of_walk (List.mem_map_of_mem hu) q.reverse fun y hy => ?_⟩
      rw [Walk.support_reverse, List.mem_reverse] at hy
      rw [labArc_eq_zero_iff]
      by_cases hyu : y = u
      · exact Or.inl (hyu ▸ hu)
      · have hyv : y ≠ v := fun e => ((Walk.cons_isPath_iff _ _).mp hp).2 (e ▸ hy)
        have hnotX := hin y (List.mem_cons_of_mem _ hy) hyv hyu
        exact Or.inr ⟨fun h => hnotX (Or.inl h), fun h => hnotX (Or.inr h)⟩
  · rintro ⟨w, hadj, hw⟩
    obtain ⟨p, -, hp⟩ := hs.par
    obtain ⟨r, W, -, hr, hall, hns, -⟩ :=
      exists_walk_of_parentOK hp (items.idxOf w.1 + 1) w hw (Nat.lt_succ_self _)
    obtain ⟨r', hr'S, hr'eq⟩ := List.mem_map.mp hr
    have hrr' : r = r' := Fin.ext hr'eq.symm
    subst hrr'
    refine isConnectedAvoiding_of_walk_mem hr'S (.cons hadj W.reverse) fun z hz hzX => ?_
    rw [Walk.support_cons, Walk.support_reverse, List.mem_cons, List.mem_reverse] at hz
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · have hz0 : labArc C Pv S z = 0 := hs.free z (hall z hz).1
      rw [labArc_eq_zero_iff] at hz0
      rcases hz0 with hzS | ⟨hzC, hzP⟩
      · right
        by_contra hzr
        exact hns z hz hzr (List.mem_map_of_mem hzS)
      · exact absurd hzX (by rintro (h | h); exacts [hzC h, hzP h])

/-! ### Splitting a path at two indices -/

/-- Splitting a list `Pv` at indices `r - 1`, `r` and `idx_s` (`0 < r < idx_s < Pv.length`). -/
theorem split_path_at_indices {α : Type*} (Pv : List α) {r idx_s : ℕ}
    (hr0 : 0 < r) (hrs : r < idx_s) (hsL : idx_s < Pv.length) :
    let L₁ := Pv.take (r - 1)
    let y := Pv[r - 1]'(by omega)
    let t := Pv[r]'(by omega)
    let N' := (Pv.take idx_s).drop (r + 1)
    let s := Pv[idx_s]'hsL
    let L₂ := Pv.drop (idx_s + 1)
    Pv = L₁ ++ y :: (t :: N') ++ s :: L₂ ∧
    Pv.take r ++ Pv.drop idx_s = L₁ ++ y :: s :: L₂ ∧
    L₁ ++ [y] = Pv.take r ∧
    (∀ v ∈ L₁ ++ [y], ∃ (i : ℕ) (_ : i < r), v = Pv[i]'(by omega)) ∧
    (∀ v ∈ t :: N', ∃ (i : ℕ) (_ : r ≤ i) (_ : i < idx_s), v = Pv[i]'(by omega)) := by
  intro L₁ y t N' s L₂
  have h1 : L₁ ++ [y] = Pv.take r := by
    dsimp only [L₁, y]
    conv_rhs => rw [show r = (r - 1) + 1 by omega, List.take_add_one,
      List.getElem?_eq_getElem (by omega)]
    rfl
  have h2 : Pv.drop idx_s = s :: L₂ := List.drop_eq_getElem_cons hsL
  have h3 : (Pv.take idx_s).drop r = t :: N' := by
    dsimp only [t, N']
    rw [List.drop_take, show idx_s - r = (idx_s - (r + 1)) + 1 by omega,
      List.drop_eq_getElem_cons (by omega), List.take_succ_cons, ← List.drop_take]
  have hPv : Pv = L₁ ++ y :: (t :: N') ++ s :: L₂ := by
    have h4 : Pv.take idx_s = Pv.take r ++ (Pv.take idx_s).drop r := by
      conv_lhs => rw [← List.take_append_drop r (Pv.take idx_s)]
      rw [List.take_take, Nat.min_eq_left (by omega)]
    calc Pv = Pv.take idx_s ++ Pv.drop idx_s := (List.take_append_drop idx_s Pv).symm
      _ = (Pv.take r ++ (Pv.take idx_s).drop r) ++ (s :: L₂) := by rw [← h4, h2]
      _ = L₁ ++ y :: (t :: N') ++ s :: L₂ := by rw [← h1, h3]; simp
  refine ⟨hPv, by rw [← h1, h2]; simp, h1, ?_, ?_⟩
  · intro v hv
    rw [h1] at hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    rw [List.length_take] at hi
    exact ⟨i, by omega, by simp⟩
  · intro v hv
    rw [← h3] at hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    simp only [List.length_drop, List.length_take] at hi
    exact ⟨r + i, by omega, by omega, by simp⟩

/-! ### One step of the loop -/

/-- **One step of the loop of Algorithm 5.2.** Given a split `P.support = L₁ ++ y :: (t :: N') ++ s :: L₂`
where `L₁ ++ [y]` is on both sides, `t` is not on both sides, and `s` is the first vertex after `t`
on the side that `t` lacks, adding `edge y s` and replacing `P` by `P'` with support
`L₁ ++ y :: s :: L₂` preserves all loop invariants and extends the prefix on both sides to
`L₁ ++ [y, s]`. -/
theorem loop_step_math {V : Type*} [Finite V] {G : SimpleGraph V} {a b y t s : V}
    {A B L₁ N' L₂ : List V} {P : G.Walk a b}
    (hC : IsCycleList G (a :: A ++ b :: B))
    (hP : IsTPath G (a :: A ++ b :: B) P)
    (hsupp : P.support = L₁ ++ y :: (t :: N') ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B})
    (htight : IsTight G (a :: A ++ b :: B) A B P.support)
    (hsided : ∀ v ∈ P.support, IsSided G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} A B v)
    (hpre : ∀ v ∈ L₁ ++ [y],
      IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} v ∧
      IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} v)
    (ht : ¬ (IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} t ∧
      IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} t))
    (hcase :
      (IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} t ∧
        IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} s ∧
        ∀ v ∈ t :: N', ¬ IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} v) ∨
      (IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} t ∧
        IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} s ∧
        ∀ v ∈ t :: N', ¬ IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} v)) :
    IsSafe G (edge y s) (a :: A ++ b :: B) ∧
    ∃ P' : (G ⊔ edge y s).Walk a b,
      P'.support = L₁ ++ y :: s :: L₂ ∧
      IsTPath (G ⊔ edge y s) (a :: A ++ b :: B) P' ∧
      (∀ u ∈ P'.support, ∀ v ∈ P'.support, (G ⊔ edge y s).Adj u v → IsListEdge P'.support u v) ∧
      Separates (G ⊔ edge y s) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
      IsTight (G ⊔ edge y s) (a :: A ++ b :: B) A B P'.support ∧
      (∀ v ∈ P'.support,
        IsSided (G ⊔ edge y s) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} A B v) ∧
      (∀ v ∈ L₁ ++ [y, s],
        IsOnSide (G ⊔ edge y s) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} {x | x ∈ B} v) ∧
      P'.support.Sublist P.support ∧
      (∀ M, M <+: P.support → (∀ v ∈ M,
          IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} v ∧
          IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} v) →
        M <+: L₁ ++ [y]) := by
  have hrot : (a :: A ++ b :: B).rotate 0 = a :: A ++ b :: B := List.rotate_zero _
  have hy := hpre y (by simp)
  have hsub_list : (L₁ ++ y :: s :: L₂).Sublist P.support := by
    rw [hsupp]; exact sublist_collapse
  have hpref : ∀ M, M <+: P.support → (∀ v ∈ M,
      IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ A} v ∧
      IsOnSide G {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} {x | x ∈ B} v) →
      M <+: L₁ ++ [y] := by
    intro M hM hMb
    have hsupp₀ : P.support = (L₁ ++ [y]) ++ t :: (N' ++ s :: L₂) := by rw [hsupp]; simp
    exact prefix_of_not_mem (hsupp₀ ▸ hM) (fun htM => ht (hMb t htM))
  rcases hcase with ⟨htA, hsB, hNB⟩ | ⟨htB, hsA, hNA⟩
  · have hsafe := strip_safe hC hrot hP hsupp hind htight hy.2 hsB hNB
    obtain ⟨P', hP', hP's, hboth⟩ := lemma_5_4_sides hrot hP hsupp hpre
      (Or.inr ⟨t, by simp, htA⟩) (Or.inl hsB)
    obtain ⟨hind', hsep', htight'⟩ := loop_invariant hrot hP hsupp hind htight hsep hNB hP's
    have hsub : P'.support.Sublist P.support := hP's ▸ hsub_list
    refine ⟨hsafe, P', hP's, hP', hind', hsep', htight', fun v hv => ?_, hboth, hsub, hpref⟩
    have hX' : {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} ⊆
        {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} :=
      fun x hx => hx.imp id fun h => hsub.subset h
    exact (hsided v (hsub.subset hv)).imp (fun h => h.mono le_sup_left hX')
      (fun h => h.mono le_sup_left hX')
  · have hsafe := strip_safe_rev hC hrot hP hsupp hind htight hy.1 hsA hNA
    obtain ⟨P', hP', hP's, hboth⟩ := lemma_5_4_sides hrot hP hsupp hpre
      (Or.inl hsA) (Or.inr ⟨t, by simp, htB⟩)
    obtain ⟨hind', hsep', htight'⟩ := loop_invariant_rev hrot hP hsupp hind htight hsep hNA hP's
    have hsub : P'.support.Sublist P.support := hP's ▸ hsub_list
    refine ⟨hsafe, P', hP's, hP', hind', hsep', htight', fun v hv => ?_, hboth, hsub, hpref⟩
    have hX' : {x | x ∈ a :: A ++ b :: B ∨ x ∈ P'.support} ⊆
        {x | x ∈ a :: A ++ b :: B ∨ x ∈ P.support} :=
      fun x hx => hx.imp id fun h => hsub.subset h
    exact (hsided v (hsub.subset hv)).imp (fun h => h.mono le_sup_left hX')
      (fun h => h.mono le_sup_left hX')

end GraphMinor.Compute.TwoPaths
