module

public import GraphMinor.HP25.Alternate
public import GraphMinor.HP25.CrossTools
public import GraphMinor.HP25.Prop51
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Method
import GraphMinor.HP25.Prop52Converse
import GraphMinor.HP25.Sec5Tighten

/-!
# Computable path and crossing search primitives for Section 5.3

This file provides purely computable, choice-free (`Option`-returning) graph-search primitives used
by the crossing extraction of Section 5.3 of Humeau and Pous:

1. `CrossingWalks G T` and `crossingWalksOfAlternate`: explicit pairs of walks witnessing a crossing
   of `T` in `G`, constructed computably from alternating `T`-paths without `Classical.choice`.
2. The walk search is a parameter: an instance of `WalkSearch V`, whose properties are
   `IsWalkSearch` (the walk found lies in `allowed ∪ {u, v}`, it is a path, and a walk is found
   whenever one exists), given by `LawfulWalkSearch V`. `findWalkIn` is one such search
   (`findWalkIn_isWalkSearch`). `findWalkFromTo` and `findWalkBetween` are built on the parameter,
   with soundness (`findWalkBetween_mem_and_support`) and completeness
   (`findWalkBetween_isSome_of_walk`).
3. `searchCrossWalk` and `runCandidateSearches`: computable single-candidate and multi-candidate
   crossing searches in `G - Z` between the two open arcs of `C` cut by the ends of `Z`, with
   soundness (`searchCrossWalk_valid`, `runCandidateSearches_valid`), search-count bounds
   (`searchCrossWalk_searches`, `runCandidateSearches_searches_le`), and completeness whenever a
   walk in `G - Z` connects the two arcs (`searchCrossWalk_isSome_of_walk_avoiding`,
   `searchCrossWalk_isSome_of_not_separates`, `searchCrossWalk_isSome_of_sup_edge_walk`).
4. `transferWalkOption`: computable transfer of a walk from `G'` to `G` when all its edges lie in
   `G`, returning `none` if and only if the walk uses an edge outside `G`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### 1. `CrossingWalks` and computable rotation of crossings -/

/-- A pair of walks `(Q, R)` in `G` with endpoints `(u₁, v₁)` and `(u₂, v₂)` representing a
crossing of `T`. -/
structure CrossingWalks (G : SimpleGraph V) (T : List V) where
  /-- First endpoint of `Q`. -/
  u₁ : V
  /-- Second endpoint of `Q`. -/
  v₁ : V
  /-- First endpoint of `R`. -/
  u₂ : V
  /-- Second endpoint of `R`. -/
  v₂ : V
  /-- First path of the crossing. -/
  Q : G.Walk u₁ v₁
  /-- Second path of the crossing. -/
  R : G.Walk u₂ v₂

/-- `cr` is a valid crossing of `T` in `G`. -/
@[expose] def CrossingWalks.Valid {T : List V} (cr : CrossingWalks G T) : Prop :=
  IsCrossing G T cr.Q cr.R

/-- A valid `CrossingWalks G T` witnesses `IsCrossed G T`. -/
theorem CrossingWalks.isCrossed {T : List V} {cr : CrossingWalks G T} (h : cr.Valid) :
    IsCrossed G T :=
  ⟨cr.u₁, cr.v₁, cr.u₂, cr.v₂, cr.Q, cr.R, h⟩

/-- Extract a `CrossingWalks G T` from `IsCrossed G T` (used only in noncomputable existence
wrappers). -/
@[expose] noncomputable def crossingWalksOfIsCrossed {T : List V} (h : IsCrossed G T) :
    CrossingWalks G T :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose⟩

theorem crossingWalksOfIsCrossed_valid {T : List V} (h : IsCrossed G T) :
    (crossingWalksOfIsCrossed h).Valid :=
  h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

/-- Computable single-step unrotation of a crossing from `t ++ [x]` to `x :: t`, tracking the four
tuple indices `(i, r, j, s)`. -/
@[expose] def rotateOneCrossing {T : List V} (t : List V)
    (cr : CrossingWalks G T) (i r j s : ℕ) :
    CrossingWalks G T × (ℕ × ℕ × ℕ × ℕ) :=
  (if s < t.length then cr else ⟨cr.v₂, cr.u₂, cr.u₁, cr.v₁, cr.R.reverse, cr.Q⟩,
   if s < t.length then (i + 1, r + 1, j + 1, s + 1) else (0, i + 1, r + 1, j + 1))

private def IsIndexedCrossing {T : List V} (L : List V) (cr : CrossingWalks G T)
    (idx : ℕ × ℕ × ℕ × ℕ) : Prop :=
  idx.1 < idx.2.1 ∧ idx.2.1 < idx.2.2.1 ∧ idx.2.2.1 < idx.2.2.2 ∧
    L[idx.1]? = some cr.u₁ ∧ L[idx.2.1]? = some cr.u₂ ∧
    L[idx.2.2.1]? = some cr.v₁ ∧ L[idx.2.2.2]? = some cr.v₂ ∧
    IsTPath G L cr.Q ∧ IsTPath G L cr.R ∧
    cr.Q.support.Disjoint cr.R.support

private theorem rotateOneCrossing_spec {T : List V} {x : V} {t : List V}
    (cr : CrossingWalks G T) (i r j s : ℕ)
    (h : IsIndexedCrossing (t ++ [x]) cr (i, r, j, s)) :
    IsIndexedCrossing (x :: t) (rotateOneCrossing t cr i r j s).1
      (rotateOneCrossing t cr i r j s).2 := by
  obtain ⟨hir, hrj, hjs, ha, hc, hb, hd, hQ, hR, hdisj⟩ := h
  dsimp only at hir hrj hjs ha hc hb hd
  have hmem : ∀ y, y ∈ t ++ [x] ↔ y ∈ x :: t := fun y => by simp [or_comm]
  rw [isTPath_congr hmem] at hQ hR
  have hlt : s ≤ t.length := by
    have := (List.getElem?_eq_some_iff.mp hd).1
    simp at this
    omega
  have hshift : ∀ {m : ℕ} {y : V}, m < t.length → (t ++ [x])[m]? = some y →
      (x :: t)[m + 1]? = some y := fun {m y} hm h => by
    rw [List.getElem?_append_left hm] at h
    simpa using h
  unfold rotateOneCrossing
  dsimp only
  split_ifs with hs
  · dsimp only [IsIndexedCrossing]
    exact ⟨by omega, by omega, by omega,
      hshift (by omega) ha, hshift (by omega) hc, hshift (by omega) hb, hshift hs hd,
      hQ, hR, hdisj⟩
  · dsimp only [IsIndexedCrossing]
    have hseq : s = t.length := by omega
    have hdx : cr.v₂ = x := by
      rw [hseq, List.getElem?_append_right le_rfl] at hd
      simpa using hd.symm
    refine ⟨by omega, by omega, by omega,
      by simp [hdx], hshift (by omega) ha, hshift (by omega) hc, hshift (by omega) hb,
      hR.reverse, hQ, ?_⟩
    rw [Walk.support_reverse]
    exact List.disjoint_reverse_left.mpr hdisj.symm

/-- Computable `k`-step unrotation of a crossing from `T.rotate k` to `T`. -/
@[expose] def rotateCrossing (T : List V) : ℕ →
    CrossingWalks G T → ℕ → ℕ → ℕ → ℕ →
    CrossingWalks G T × (ℕ × ℕ × ℕ × ℕ)
  | 0, cr, i, r, j, s => (cr, (i, r, j, s))
  | k + 1, cr, i, r, j, s =>
    match T.rotate k with
    | [] => rotateCrossing T k cr i r j s
    | _ :: t =>
      let step := rotateOneCrossing t cr i r j s
      rotateCrossing T k step.1 step.2.1 step.2.2.1 step.2.2.2.1 step.2.2.2.2

private theorem rotateCrossing_spec {T : List V} : ∀ (k : ℕ)
    (cr : CrossingWalks G T) (i r j s : ℕ),
    IsIndexedCrossing (T.rotate k) cr (i, r, j, s) →
    IsIndexedCrossing T (rotateCrossing T k cr i r j s).1
      (rotateCrossing T k cr i r j s).2
  | 0, cr, i, r, j, s, h => by
    simpa [rotateCrossing] using h
  | k + 1, cr, i, r, j, s, h => by
    unfold rotateCrossing
    rw [← List.rotate_rotate] at h
    cases hT : T.rotate k with
    | nil =>
      rw [hT, List.rotate_nil] at h
      exact rotateCrossing_spec k cr i r j s (hT.symm ▸ h)
    | cons x t =>
      rw [hT, List.rotate_cons_succ, List.rotate_zero] at h
      have hstep := rotateOneCrossing_spec cr i r j s h
      rw [← hT] at hstep
      exact rotateCrossing_spec k _ _ _ _ _ hstep

/-- **Computable construction of `CrossingWalks G T` from alternating `T`-paths.**
Given `T.rotate k = a :: L₁ ++ b :: L₂` with `c ∈ L₁` and `d ∈ L₂` and disjoint `T`-paths
`Q : G.Walk a b` and `R : G.Walk c d`, computes the resulting `CrossingWalks G T` without
`Classical.choice`. -/
@[expose] def crossingWalksOfAlternate [DecidableEq V] {T : List V} {a b c d : V}
    (k : ℕ) (L₁ L₂ : List V) (Q : G.Walk a b) (R : G.Walk c d) : CrossingWalks G T :=
  let i₁ := L₁.idxOf c
  let i₂ := L₂.idxOf d
  let cr₀ : CrossingWalks G T := ⟨a, b, c, d, Q, R⟩
  (rotateCrossing T k cr₀ 0 (i₁ + 1) (L₁.length + 1) (L₁.length + 2 + i₂)).1

/-- `crossingWalksOfAlternate` produces a valid crossing whenever `T.rotate k = a :: L₁ ++ b :: L₂`,
`c ∈ L₁`, `d ∈ L₂`, and `Q, R` are disjoint `T`-paths. -/
theorem crossingWalksOfAlternate_valid [DecidableEq V] {T : List V} {a b c d : V}
    {k : ℕ} {L₁ L₂ : List V} (hrot : T.rotate k = a :: L₁ ++ b :: L₂)
    (hc : c ∈ L₁) (hd : d ∈ L₂) {Q : G.Walk a b} {R : G.Walk c d}
    (hQ : IsTPath G T Q) (hR : IsTPath G T R) (hdisj : Q.support.Disjoint R.support) :
    (crossingWalksOfAlternate (T := T) k L₁ L₂ Q R).Valid := by
  have hmem : ∀ y, y ∈ T ↔ y ∈ T.rotate k := fun y => List.mem_rotate.symm
  have hQ' : IsTPath G (T.rotate k) Q := (isTPath_congr hmem Q).mp hQ
  have hR' : IsTPath G (T.rotate k) R := (isTPath_congr hmem R).mp hR
  set i₁ := L₁.idxOf c
  set i₂ := L₂.idxOf d
  have hi₁ : i₁ < L₁.length := List.idxOf_lt_length_of_mem hc
  have hi₂ : i₂ < L₂.length := List.idxOf_lt_length_of_mem hd
  have hc_get : L₁[i₁] = c := List.getElem_idxOf hi₁
  have hd_get : L₂[i₂] = d := List.getElem_idxOf hi₂
  have ha_get : (T.rotate k)[0]? = some a := by rw [hrot]; rfl
  have hc_rot : (T.rotate k)[i₁ + 1]? = some c := by
    rw [hrot, List.cons_append, List.getElem?_cons_succ, List.getElem?_append_left hi₁,
      List.getElem?_eq_getElem hi₁, hc_get]
  have hb_rot : (T.rotate k)[L₁.length + 1]? = some b := by
    rw [hrot]
    simp
  have hd_rot : (T.rotate k)[L₁.length + 2 + i₂]? = some d := by
    rw [hrot, show L₁.length + 2 + i₂ = (L₁.length + 1 + i₂) + 1 by omega, List.cons_append,
      List.getElem?_cons_succ, List.getElem?_append_right (by omega),
      show L₁.length + 1 + i₂ - L₁.length = i₂ + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_eq_getElem hi₂, hd_get]
  have hinit : IsIndexedCrossing (T := T) (T.rotate k) ⟨a, b, c, d, Q, R⟩
      (0, i₁ + 1, L₁.length + 1, L₁.length + 2 + i₂) := by
    dsimp only [IsIndexedCrossing]
    exact ⟨by omega, by omega, by omega, ha_get, hc_rot, hb_rot, hd_rot, hQ', hR', hdisj⟩
  have hspec := rotateCrossing_spec (T := T) k ⟨a, b, c, d, Q, R⟩ 0 (i₁ + 1) (L₁.length + 1)
    (L₁.length + 2 + i₂) hinit
  obtain ⟨hir', hrj', hjs', ha', hc', hb', hd', hQ_out, hR_out, hdisj_out⟩ := hspec
  exact ⟨⟨_, _, _, _, hir', hrj', hjs', ha', hc', hb', hd'⟩, hQ_out, hR_out, hdisj_out⟩

/-! ### 2. Computable walk search (`findWalkIn` and `findWalkBetween`) -/

/-- **Computable walk search in an allowed vertex set (`findWalkIn`).**
Searches for a walk in `G` from `u` to `v` whose inner vertices belong to `allowed`. -/
@[expose] def findWalkIn [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    List V → (u v : V) → Option (G.Walk u v)
  | [], u, v =>
    if h : u = v then
      some (h ▸ .nil)
    else if hadj : G.Adj u v then
      some (.cons hadj .nil)
    else
      none
  | w :: rest, u, v =>
    match findWalkIn G rest u v with
    | some p => some p
    | none =>
      match findWalkIn G rest u w, findWalkIn G rest w v with
      | some p₁, some p₂ => some ((p₁.append p₂).bypass)
      | _, _ => none

/-- Every vertex on a walk returned by `findWalkIn G allowed u v` is either `u`, `v`, or in
`allowed`. -/
theorem findWalkIn_support_subset [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {allowed : List V} {u v : V} {p : G.Walk u v}
    (h : findWalkIn G allowed u v = some p) :
    ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed := by
  induction allowed generalizing u v p with
  | nil =>
    simp only [findWalkIn] at h
    split_ifs at h with huv hadj
    · subst huv
      injection h with hp
      subst hp
      intro x hx
      simp only [Walk.support_nil, List.mem_singleton] at hx
      exact Or.inl hx
    · injection h with hp
      subst hp
      intro x hx
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  | cons w rest ih =>
    simp only [findWalkIn] at h
    split at h
    · rename_i p₀ hp₀
      injection h with hp
      subst hp
      intro x hx
      rcases ih hp₀ x hx with rfl | rfl | hx'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hx'))
    · split at h
      · rename_i p₁ p₂ hp₁ hp₂
        injection h with hp
        subst hp
        intro x hx
        have hx' := (p₁.append p₂).support_bypass_subset_support hx
        rw [Walk.mem_support_append_iff] at hx'
        rcases hx' with hx₁ | hx₂
        · rcases ih hp₁ x hx₁ with rfl | rfl | hx_in
          · exact Or.inl rfl
          · exact Or.inr (Or.inr List.mem_cons_self)
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hx_in))
        · rcases ih hp₂ x hx₂ with rfl | rfl | hx_in
          · exact Or.inr (Or.inr List.mem_cons_self)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hx_in))
      · simp at h

/-- **Completeness of `findWalkIn`:** if there exists a walk `q : G.Walk u v` whose inner vertices
lie in `allowed`, then `findWalkIn G allowed u v` returns `some` walk. -/
theorem findWalkIn_isSome_of_walk [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {allowed : List V} {u v : V} (q : G.Walk u v)
    (hq : ∀ x ∈ q.support, x ≠ u → x ≠ v → x ∈ allowed) :
    (findWalkIn G allowed u v).isSome = true := by
  induction allowed generalizing u v q with
  | nil =>
    set p := q.bypass
    have hp_sub : ∀ x ∈ p.support, x ∈ q.support := fun _ hx => q.support_bypass_subset_support hx
    simp only [findWalkIn]
    split_ifs with huv hadj
    · rfl
    · rfl
    · exfalso
      cases hp_eq : p with
      | nil => exact huv rfl
      | cons h₁ p' =>
        rename_i w
        cases hp'_eq : p' with
        | nil => exact hadj h₁
        | cons h₂ p'' =>
          have hwu : w ≠ u := (G.ne_of_adj h₁).symm
          have hwv : w ≠ v := by
            intro e
            subst e
            have hpath : p.IsPath := q.bypass_isPath
            rw [hp_eq, hp'_eq] at hpath
            have hnd := hpath.support_nodup
            simp only [Walk.support_cons, List.nodup_cons] at hnd
            exact hnd.2.1 p''.end_mem_support
          have hw_mem : w ∈ p.support := by rw [hp_eq]; simp
          exact List.not_mem_nil (hq w (hp_sub w hw_mem) hwu hwv)
  | cons w rest ih =>
    set p := q.bypass
    have hp : p.IsPath := q.bypass_isPath
    have hp_sub : ∀ x ∈ p.support, x ∈ q.support := fun _ hx => q.support_bypass_subset_support hx
    simp only [findWalkIn]
    split
    · rfl
    · rename_i hnone
      by_cases hw_in : w ∈ p.support ∧ w ≠ u ∧ w ≠ v
      · obtain ⟨hw, hwu, hwv⟩ := hw_in
        have hp₁ : (findWalkIn G rest u w).isSome = true := by
          refine ih (p.takeUntil w hw) fun x hx hxu hxw => ?_
          have hxv : x ≠ v := fun e =>
            Walk.endpoint_notMem_support_takeUntil hp hw hwv.symm (e ▸ hx)
          have hx_mem := hq x (hp_sub x (p.support_takeUntil_subset_support hw hx)) hxu hxv
          exact (List.mem_cons.mp hx_mem).resolve_left hxw
        have hp₂ : (findWalkIn G rest w v).isSome = true := by
          refine ih (p.dropUntil w hw) fun x hx hxw hxv => ?_
          have hxu : x ≠ u := fun e =>
            start_notMem_support_dropUntil hp hw hwu (e ▸ hx)
          have hx_mem := hq x (hp_sub x (p.support_dropUntil_subset_support hw hx)) hxu hxv
          exact (List.mem_cons.mp hx_mem).resolve_left hxw
        obtain ⟨p₁, hp₁_eq⟩ := Option.isSome_iff_exists.mp hp₁
        obtain ⟨p₂, hp₂_eq⟩ := Option.isSome_iff_exists.mp hp₂
        simp [hp₁_eq, hp₂_eq]
      · have hrest : (findWalkIn G rest u v).isSome = true := by
          refine ih p fun x hx hxu hxv => ?_
          have hxw : x ≠ w := fun e => hw_in ⟨e ▸ hx, e ▸ hxu, e ▸ hxv⟩
          exact (List.mem_cons.mp (hq x (hp_sub x hx) hxu hxv)).resolve_left hxw
        rw [hnone] at hrest
        simp at hrest

/-- Every walk returned by `findWalkIn` is a path. -/
theorem findWalkIn_isPath [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {allowed : List V} {u v : V} {p : G.Walk u v}
    (h : findWalkIn G allowed u v = some p) : p.IsPath := by
  induction allowed generalizing u v p with
  | nil =>
    simp only [findWalkIn] at h
    split_ifs at h with huv hadj
    · subst huv
      injection h with hp
      subst hp
      exact Walk.IsPath.nil
    · injection h with hp
      subst hp
      exact Walk.IsPath.nil.cons (by simpa using G.ne_of_adj hadj)
  | cons w rest ih =>
    simp only [findWalkIn] at h
    split at h
    · rename_i p₀ hp₀
      injection h with hp
      subst hp
      exact ih hp₀
    · split at h
      · injection h with hp
        subst hp
        exact Walk.bypass_isPath _
      · simp at h

/-! ### The search as a parameter

The searches below are written for any walk search `find` of `G`, given as an instance of
`WalkSearch V`. The proofs use only the three properties of `IsWalkSearch`: the walk found has its
vertices in `allowed ∪ {u, v}`, it is a path, and a walk is found whenever one exists. The
search `findWalkIn` has these properties (`findWalkIn_isWalkSearch`). A breadth-first search has
them too, so the theorems also hold for the search that a program runs. -/

/-- The properties of a walk search `find` of `G` that the proofs use. Given a list `allowed` and
two vertices `u`, `v`, the search `find allowed u v` may return a walk of `G` from `u` to `v`. -/
structure IsWalkSearch (G : SimpleGraph V) (find : List V → (u v : V) → Option (G.Walk u v)) :
    Prop where
  /-- Every vertex of a walk found is `u`, `v`, or in `allowed`. -/
  support_subset : ∀ {allowed : List V} {u v : V} {p : G.Walk u v},
    find allowed u v = some p → ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed
  /-- Every walk found is a path. -/
  isPath : ∀ {allowed : List V} {u v : V} {p : G.Walk u v}, find allowed u v = some p → p.IsPath
  /-- A walk is found whenever some walk from `u` to `v` has all its inner vertices in
  `allowed`. -/
  isSome_of_walk : ∀ {allowed : List V} {u v : V} (q : G.Walk u v),
    (∀ x ∈ q.support, x ≠ u → x ≠ v → x ∈ allowed) → (find allowed u v).isSome = true

/-- A walk search, for every graph on `V` with decidable adjacency, passed to the searches of this
section as an instance. -/
class WalkSearch (V : Type*) where
  /-- `find G allowed u v` may return a walk of `G` from `u` to `v` with inner vertices in
  `allowed`. -/
  find : (G : SimpleGraph V) → [DecidableRel G.Adj] → List V → (u v : V) → Option (G.Walk u v)

/-- The walk search has the properties of `IsWalkSearch` on every graph. -/
class LawfulWalkSearch (V : Type*) [WalkSearch V] : Prop where
  /-- The properties of the search. -/
  isWalkSearch : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], IsWalkSearch G (WalkSearch.find G)

/-- `findWalkIn` has the properties of `IsWalkSearch`. -/
theorem findWalkIn_isWalkSearch [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsWalkSearch G (findWalkIn G) :=
  ⟨findWalkIn_support_subset G, findWalkIn_isPath G, findWalkIn_isSome_of_walk G⟩

/-- The search `findWalkIn`, as a `WalkSearch`. -/
@[expose, instance_reducible] def findWalkInSearch [DecidableEq V] : WalkSearch V := ⟨fun G _ => findWalkIn G⟩

theorem findWalkInSearch_lawful [DecidableEq V] :
    @LawfulWalkSearch V findWalkInSearch :=
  @LawfulWalkSearch.mk V findWalkInSearch fun G _ => findWalkIn_isWalkSearch G

theorem WalkSearch.find_support_subset [WalkSearch V] [LawfulWalkSearch V] [DecidableRel G.Adj]
    {allowed : List V} {u v : V} {p : G.Walk u v}
    (h : WalkSearch.find G allowed u v = some p) :
    ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed :=
  (LawfulWalkSearch.isWalkSearch G).support_subset h

theorem WalkSearch.find_isPath [WalkSearch V] [LawfulWalkSearch V] [DecidableRel G.Adj]
    {allowed : List V} {u v : V} {p : G.Walk u v}
    (h : WalkSearch.find G allowed u v = some p) : p.IsPath :=
  (LawfulWalkSearch.isWalkSearch G).isPath h

theorem WalkSearch.find_isSome_of_walk [WalkSearch V] [LawfulWalkSearch V] [DecidableRel G.Adj]
    {allowed : List V} {u v : V} (q : G.Walk u v)
    (hq : ∀ x ∈ q.support, x ≠ u → x ≠ v → x ∈ allowed) :
    (WalkSearch.find G allowed u v).isSome = true :=
  (LawfulWalkSearch.isWalkSearch G).isSome_of_walk q hq

/-- Search for a walk in `G` from a single vertex `u` to any vertex `v ∈ T` with inner vertices in
`allowed`. -/
@[expose] def findWalkFromTo (G : SimpleGraph V) [DecidableRel G.Adj] [WalkSearch V]
    (allowed : List V) (u : V) : List V → Option (Σ v : V, G.Walk u v)
  | [] => none
  | v :: tl =>
    match WalkSearch.find G allowed u v with
    | some p => some ⟨v, p⟩
    | none => findWalkFromTo G allowed u tl

theorem findWalkFromTo_mem_and_support (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {allowed T : List V} {u v : V} {p : G.Walk u v}
    (h : findWalkFromTo G allowed u T = some ⟨v, p⟩) :
    v ∈ T ∧ ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed := by
  induction T with
  | nil => simp [findWalkFromTo] at h
  | cons w tl ih =>
    simp only [findWalkFromTo] at h
    rcases hp₀ : WalkSearch.find G allowed u w with _ | p₀
    · rw [hp₀] at h
      obtain ⟨hmem, hsupp⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hmem, hsupp⟩
    · rw [hp₀] at h
      injection h with h'
      rcases Sigma.mk.inj_iff.mp h' with ⟨rfl, hp_heq⟩
      cases eq_of_heq hp_heq
      exact ⟨List.mem_cons_self, WalkSearch.find_support_subset hp₀⟩

theorem findWalkFromTo_isSome_of_walk (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {allowed T : List V} {u v : V} (hv : v ∈ T) (q : G.Walk u v)
    (hq : ∀ x ∈ q.support, x ≠ u → x ≠ v → x ∈ allowed) :
    (findWalkFromTo G allowed u T).isSome = true := by
  induction T with
  | nil => cases List.not_mem_nil hv
  | cons w tl ih =>
    simp only [findWalkFromTo]
    split
    · rfl
    · rename_i hnone
      rcases List.mem_cons.mp hv with rfl | hv'
      · have hsome := WalkSearch.find_isSome_of_walk q hq
        rw [hnone] at hsome
        simp at hsome
      · exact ih hv'

/-- **Computable walk search between two vertex lists `S` and `T` (`findWalkBetween`).** -/
@[expose] def findWalkBetween (G : SimpleGraph V) [DecidableRel G.Adj] [WalkSearch V]
    (allowed : List V) : List V → List V → Option (Σ u v : V, G.Walk u v)
  | [], _ => none
  | u :: tl, T =>
    match findWalkFromTo G allowed u T with
    | some ⟨v, p⟩ => some ⟨u, v, p⟩
    | none => findWalkBetween G allowed tl T

theorem findWalkBetween_mem_and_support (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {allowed S T : List V} {u v : V} {p : G.Walk u v}
    (h : findWalkBetween G allowed S T = some ⟨u, v, p⟩) :
    u ∈ S ∧ v ∈ T ∧ ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed := by
  induction S with
  | nil => simp [findWalkBetween] at h
  | cons w tl ih =>
    simp only [findWalkBetween] at h
    rcases hres : findWalkFromTo G allowed w T with _ | ⟨v₀, p₀⟩
    · rw [hres] at h
      obtain ⟨hu, hv, hsupp⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hu, hv, hsupp⟩
    · rw [hres] at h
      injection h with h'
      rcases Sigma.mk.inj_iff.mp h' with ⟨rfl, h''⟩
      rcases Sigma.mk.inj_iff.mp (eq_of_heq h'') with ⟨rfl, hp_heq⟩
      cases eq_of_heq hp_heq
      obtain ⟨hv, hsupp⟩ := findWalkFromTo_mem_and_support G hres
      exact ⟨List.mem_cons_self, hv, hsupp⟩

theorem findWalkBetween_isSome_of_walk (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {allowed S T : List V} {u v : V} (hu : u ∈ S) (hv : v ∈ T) (q : G.Walk u v)
    (hq : ∀ x ∈ q.support, x ≠ u → x ≠ v → x ∈ allowed) :
    (findWalkBetween G allowed S T).isSome = true := by
  induction S with
  | nil => cases List.not_mem_nil hu
  | cons w tl ih =>
    simp only [findWalkBetween]
    split
    · rfl
    · rename_i hnone
      rcases List.mem_cons.mp hu with rfl | hu'
      · have hsome := findWalkFromTo_isSome_of_walk G hv q hq
        rw [hnone] at hsome
        simp at hsome
      · exact ih hu'

/-! ### 3. Cycle rotation / splitting helpers and `searchCrossWalk` -/

/-- Find a rotation index `k ∈ ks` such that `C.rotate k = x :: tail`. -/
@[expose] def findRotateHead [DecidableEq V] (x : V) (C : List V) :
    List ℕ → Option (ℕ × List V)
  | [] => none
  | k :: ks =>
    match C.rotate k with
    | z :: tail => if z = x then some (k, tail) else findRotateHead x C ks
    | [] => findRotateHead x C ks

theorem findRotateHead_eq_some [DecidableEq V] {x : V} {C : List V} {ks : List ℕ}
    {k : ℕ} {tail : List V} (h : findRotateHead x C ks = some (k, tail)) :
    C.rotate k = x :: tail := by
  induction ks with
  | nil => simp [findRotateHead] at h
  | cons k₀ ks ih =>
    simp only [findRotateHead] at h
    split at h
    · rename_i z tail₀ hrot
      split_ifs at h with hzx
      · subst hzx
        injection h with h'
        rcases Prod.mk.inj h' with ⟨rfl, rfl⟩
        exact hrot
      · exact ih h
    · exact ih h

theorem findRotateHead_isSome_of_mem_ks [DecidableEq V] {x : V} {C : List V} {ks : List ℕ}
    {k : ℕ} {tail : List V} (hk : k ∈ ks) (hrot : C.rotate k = x :: tail) :
    (findRotateHead x C ks).isSome = true := by
  induction ks with
  | nil => cases List.not_mem_nil hk
  | cons k₀ ks ih =>
    simp only [findRotateHead]
    rcases List.mem_cons.mp hk with rfl | hk'
    · rw [hrot]
      simp
    · split
      · split_ifs
        · rfl
        · exact ih hk'
      · exact ih hk'

theorem findRotateHead_isSome_of_rotate [DecidableEq V] {x : V} {C : List V}
    {k : ℕ} {tail : List V} (hrot : C.rotate k = x :: tail) :
    (findRotateHead x C (List.range C.length)).isSome = true := by
  have hlen : 0 < C.length := by
    have := congrArg List.length hrot
    simp at this
    omega
  have hmod_mem : k % C.length ∈ List.range C.length :=
    List.mem_range.mpr (Nat.mod_lt k hlen)
  have hmod_rot : C.rotate (k % C.length) = x :: tail := by
    rw [List.rotate_mod, hrot]
  exact findRotateHead_isSome_of_mem_ks hmod_mem hmod_rot

/-- Split a list `L` at the first occurrence of `y` into `L = L₁ ++ y :: L₂`. -/
@[expose] def splitAtElem [DecidableEq V] (y : V) : List V → Option (List V × List V)
  | [] => none
  | z :: tl =>
    if z = y then
      some ([], tl)
    else
      match splitAtElem y tl with
      | some (L₁, L₂) => some (z :: L₁, L₂)
      | none => none

theorem splitAtElem_eq_some [DecidableEq V] {y : V} {L L₁ L₂ : List V}
    (h : splitAtElem y L = some (L₁, L₂)) : L = L₁ ++ y :: L₂ := by
  induction L generalizing L₁ L₂ with
  | nil => simp [splitAtElem] at h
  | cons z tl ih =>
    simp only [splitAtElem] at h
    split_ifs at h with hzy
    · subst hzy
      injection h with h'
      rcases Prod.mk.inj h' with ⟨rfl, rfl⟩
      rfl
    · split at h
      · rename_i L₁' L₂' htl
        injection h with h'
        rcases Prod.mk.inj h' with ⟨rfl, rfl⟩
        rw [ih htl]
        rfl
      · simp at h

theorem splitAtElem_isSome_of_mem [DecidableEq V] {y : V} {L : List V} (hy : y ∈ L) :
    (splitAtElem y L).isSome = true := by
  induction L with
  | nil => cases List.not_mem_nil hy
  | cons z tl ih =>
    simp only [splitAtElem]
    split_ifs with hzy
    · rfl
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hzy
      · obtain ⟨⟨L₁, L₂⟩, htl⟩ := Option.isSome_iff_exists.mp (ih hy')
        simp [htl]

/-- **Single-search primitive (`searchCrossWalk`).**
Given a candidate walk `Z : G.Walk x y`, bypasses `Z` to a path `Z' = Z.bypass`, splits the nodup
cycle `C` at `x` and `y` into its two open arcs `A_Z` and `B_Z`, and searches `G - (C ∪ Z')` for a
walk between `A_Z` and `B_Z` using `findWalkBetween`. Returns `some cr` if a crossing is found and
`none` otherwise, at a cost of `1` search. Purely computable (`def`), with no `Classical.choice` or
`IsCrossed`. -/
@[expose] def searchCrossWalk [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V]
    (verts C : List V) {x y : V} (Z : G.Walk x y) : Option (CrossingWalks G C) × ℕ :=
  let Z' := Z.bypass
  if C.Nodup ∧ x ∈ C ∧ y ∈ C ∧ x ≠ y ∧ ∀ w ∈ Z'.support, w ≠ x → w ≠ y → w ∉ C then
    match findRotateHead x C (List.range C.length) with
    | none => (none, 1)
    | some (k, tail) =>
      match splitAtElem y tail with
      | none => (none, 1)
      | some (A_Z, B_Z) =>
        let allowed := verts.filter (fun v => decide (v ∉ Z'.support ∧ v ∉ C))
        match findWalkBetween G allowed A_Z B_Z with
        | none => (none, 1)
        | some ⟨_a', _b', W⟩ =>
          (some (crossingWalksOfAlternate k A_Z B_Z Z' W.bypass), 1)
  else
    (none, 1)

/-- `searchCrossWalk` makes exactly `1` search. -/
@[simp] theorem searchCrossWalk_searches [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V]
    (verts C : List V) {x y : V} (Z : G.Walk x y) :
    (searchCrossWalk G verts C Z).2 = 1 := by
  unfold searchCrossWalk
  dsimp only
  split_ifs
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl

/-- **Soundness of `searchCrossWalk`:** every crossing returned by `searchCrossWalk` is a valid
crossing of `C` in `G`. -/
theorem searchCrossWalk_valid [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C : List V} {x y : V} {Z : G.Walk x y} {cr : CrossingWalks G C}
    (h : (searchCrossWalk G verts C Z).1 = some cr) : cr.Valid := by
  unfold searchCrossWalk at h
  dsimp only at h
  split_ifs at h with hZ
  obtain ⟨hCnd, hxC, hyC, hxy, hZin⟩ := hZ
  rcases hrot_opt : findRotateHead x C (List.range C.length) with _ | ⟨k, tail⟩
  · rw [hrot_opt] at h; simp at h
  rw [hrot_opt] at h
  dsimp only at h
  have hrot_tail := findRotateHead_eq_some hrot_opt
  rcases hsplit_opt : splitAtElem y tail with _ | ⟨A_Z, B_Z⟩
  · rw [hsplit_opt] at h; simp at h
  rw [hsplit_opt] at h
  dsimp only at h
  have hsplit := splitAtElem_eq_some hsplit_opt
  have hrot : C.rotate k = x :: A_Z ++ y :: B_Z := by rw [hrot_tail, hsplit]; simp
  rcases hw_opt :
      findWalkBetween G (verts.filter (fun v => decide (v ∉ Z.bypass.support ∧ v ∉ C))) A_Z B_Z
      with _ | ⟨a', b', W⟩
  · rw [hw_opt] at h; simp at h
  rw [hw_opt] at h
  dsimp only at h
  injection h with hcr_eq
  subst hcr_eq
  obtain ⟨ha', hb', hW_supp⟩ := findWalkBetween_mem_and_support G hw_opt
  set Z' := Z.bypass
  have hZ_path : IsTPath G C Z' := by
    refine ⟨Z.bypass_isPath, hxC, hyC, fun w hw hwx hwy => ?_⟩
    have hwC := hZin w hw hwx hwy
    exact ⟨hwC, hwC⟩
  have ha'C : a' ∈ C := List.mem_rotate.mp (by rw [hrot]; simp [ha'])
  have hb'C : b' ∈ C := List.mem_rotate.mp (by rw [hrot]; simp [hb'])
  have hW_path : IsTPath G C W.bypass := by
    refine ⟨W.bypass_isPath, ha'C, hb'C, fun w hw hwa hwb => ?_⟩
    have hw' := hW_supp w (W.support_bypass_subset_support hw)
    rcases hw' with rfl | rfl | hw_all
    · exact absurd rfl hwa
    · exact absurd rfl hwb
    · simp only [List.mem_filter, decide_eq_true_eq] at hw_all
      exact ⟨hw_all.2.2, hw_all.2.2⟩
  have hrot_nd : (x :: A_Z ++ y :: B_Z).Nodup := hrot ▸ (List.nodup_rotate.mpr hCnd)
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hrot_nd
  have hdisj : Z'.support.Disjoint W.bypass.support := by
    intro w hwZ hwW
    rcases hW_supp w (W.support_bypass_subset_support hwW) with rfl | rfl | hw_all
    · have hwx : w ≠ x := fun e => hrot_nd.1 (e ▸ List.mem_append_left _ ha')
      have hwy : w ≠ y := fun e => hrot_nd.2.2.2 w ha' y List.mem_cons_self e
      exact hZin w hwZ hwx hwy ha'C
    · have hwx : w ≠ x := fun e => hrot_nd.1 (e ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hb'))
      have hwy : w ≠ y := fun e => (List.nodup_cons.mp hrot_nd.2.2.1).1 (e ▸ hb')
      exact hZin w hwZ hwx hwy hb'C
    · simp only [List.mem_filter, decide_eq_true_eq] at hw_all
      exact hw_all.2.1 hwZ
  exact crossingWalksOfAlternate_valid hrot ha' hb' hZ_path hW_path hdisj

/-- **Completeness of `searchCrossWalk` (`searchCrossWalk_isSome_of_walk_avoiding`):**
Whenever `Z.bypass` is a `C`-path from `c` to `d`, `Alternate C a b c d`, and `W : G.Walk a b`
avoids `Z.bypass.support`, `searchCrossWalk G verts C Z` returns `some cr`. -/
theorem searchCrossWalk_isSome_of_walk_avoiding [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {verts C : List V} (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup)
    {a b c d : V} (halt : Alternate C a b c d) {Z : G.Walk c d}
    (hZ : IsTPath G C Z.bypass) (W : G.Walk a b)
    (hW : ∀ v ∈ W.support, v ∉ Z.bypass.support) :
    (searchCrossWalk G verts C Z).1.isSome = true := by
  set Z' := Z.bypass
  have hcd : c ≠ d := halt.ne hCnd
  have hZ_cond : C.Nodup ∧ c ∈ C ∧ d ∈ C ∧ c ≠ d ∧ ∀ w ∈ Z'.support, w ≠ c → w ≠ d → w ∉ C :=
    ⟨hCnd, hZ.2.1, hZ.2.2.1, hcd, fun w hw h1 h2 => (hZ.2.2.2 w hw h1 h2).1⟩
  obtain ⟨k₀, L₁, L₂, hrot₀, hbL₁, haL₂⟩ := halt.comm
  have hrot₀' : C.rotate k₀ = c :: (L₁ ++ d :: L₂) := by rw [hrot₀]; simp
  have hfind_rot := findRotateHead_isSome_of_rotate hrot₀'
  obtain ⟨⟨k, tail⟩, hk_eq⟩ := Option.isSome_iff_exists.mp hfind_rot
  have hrot_k := findRotateHead_eq_some hk_eq
  have htail_eq : tail = L₁ ++ d :: L₂ := rotate_eq_of_head hCnd hrot_k hrot₀'
  have hd_tail : d ∈ tail := by rw [htail_eq]; simp
  obtain ⟨⟨A_Z, B_Z⟩, hsplit_eq⟩ := Option.isSome_iff_exists.mp (splitAtElem_isSome_of_mem hd_tail)
  have hsplit := splitAtElem_eq_some hsplit_eq
  have hrot : C.rotate k = c :: A_Z ++ d :: B_Z := by rw [hrot_k, hsplit]; simp
  obtain ⟨hb_AZ, ha_BZ⟩ := halt.comm.mem_of_rotate hCnd hrot
  -- first vertex `t` of `W` in `A_Z`, then last vertex `r` of `w₁` in `B_Z`
  obtain ⟨t, ht, w₁, hw₁, hw₁A, -⟩ := exists_first_hit {v | v ∈ A_Z} W hb_AZ
  obtain ⟨r, hr, w₂, hw₂, hw₂B, -⟩ := exists_first_hit {v | v ∈ B_Z} w₁.reverse ha_BZ
  have hsub : ∀ v ∈ w₂.support, v ∈ W.support := fun v hv =>
    hw₁ v (by simpa using hw₂ v hv)
  have hin : ∀ v ∈ w₂.support, v ≠ t → v ≠ r →
      v ∈ verts.filter (fun u => decide (u ∉ Z'.support ∧ u ∉ C)) := by
    intro v hv hvt hvr
    have hvW := hsub v hv
    have hvZ : v ∉ Z'.support := hW v hvW
    have hvC : v ∉ C := by
      intro hvC_in
      have hv₁ : v ∈ w₁.support := by simpa using hw₂ v hv
      have hvc : v ≠ c := fun h => hvZ (h ▸ Z'.start_mem_support)
      have hvd : v ≠ d := fun h => hvZ (h ▸ Z'.end_mem_support)
      have hmem_rot : v ∈ c :: A_Z ++ d :: B_Z := hrot ▸ List.mem_rotate.mpr hvC_in
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hmem_rot
      rcases hmem_rot with h | h | h | h
      · exact hvc h
      · exact hw₁A v hv₁ hvt h
      · exact hvd h
      · exact hw₂B v hv hvr h
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hverts v, hvZ, hvC⟩
  have hfind_walk := findWalkBetween_isSome_of_walk G ht hr w₂ hin
  obtain ⟨⟨a', b', W_found⟩, hW_found⟩ := Option.isSome_iff_exists.mp hfind_walk
  unfold searchCrossWalk
  dsimp only
  split_ifs with hcond
  · rw [hk_eq]
    dsimp only
    rw [hsplit_eq]
    dsimp only
    rw [hW_found]
    rfl
  · exact absurd hZ_cond hcond

/-- Corollary of `searchCrossWalk_isSome_of_walk_avoiding`: when `P` is a `C`-path from `a` to `b`
that fails to separate `A` from `B`, `searchCrossWalk G verts C P` returns `some cr`. -/
theorem searchCrossWalk_isSome_of_not_separates [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {verts C A B : List V} {a b : V} {k : ℕ}
    (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B)
    {P : G.Walk a b} (hP : IsTPath G C P)
    (hns : ¬ Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}) :
    (searchCrossWalk G verts C P).1.isSome = true := by
  unfold Separates at hns
  push Not at hns
  obtain ⟨u, hu, w, hw, p, hp⟩ := hns
  have halt₀ : Alternate C a b u w := ⟨k, A, B, hrot, hu, hw⟩
  have halt : Alternate C w u a b := halt₀.comm.swap
  have hP_byp : IsTPath G C P.bypass := by
    refine ⟨P.bypass_isPath, hP.2.1, hP.2.2.1, fun x hx h1 h2 => ?_⟩
    exact hP.2.2.2 x (P.support_bypass_subset_support hx) h1 h2
  refine searchCrossWalk_isSome_of_walk_avoiding hverts hCnd halt hP_byp p.reverse fun v hv hvP => ?_
  rw [Walk.support_reverse, List.mem_reverse] at hv
  exact hp v hv (P.support_bypass_subset_support hvP)

/-- Corollary of `searchCrossWalk_isSome_of_walk_avoiding`: in the setting of
`isCrossed_of_sup_edge_walk`, if a walk `W : G.Walk u v` avoids `R.support`, then
`searchCrossWalk G verts C R` returns `some cr`. -/
theorem searchCrossWalk_isSome_of_sup_edge_walk [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {verts C : List V} (hverts : ∀ v : V, v ∈ verts) (hCnd : C.Nodup)
    {u v a b c d : V} (Q : (G ⊔ edge u v).Walk a b) (R : G.Walk c d) (halt : Alternate C a b c d)
    (hQ : IsTPath (G ⊔ edge u v) C Q) (hQe : s(u, v) ∈ Q.edges) (hR : IsTPath G C R)
    (hdisj : Q.support.Disjoint R.support) (W : G.Walk u v)
    (hW : ∀ x ∈ W.support, x ∉ R.support) :
    (searchCrossWalk G verts C R).1.isSome = true := by
  have hR_byp : IsTPath G C R.bypass := by
    refine ⟨R.bypass_isPath, hR.2.1, hR.2.2.1, fun x hx h1 h2 => ?_⟩
    exact hR.2.2.2 x (R.support_bypass_subset_support hx) h1 h2
  have hhead : Q.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
  have hlast : Q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  obtain ⟨X₁, X₂, h | h⟩ := Walk.exists_split_of_mem_edges hQe
  · have hch := Q.isChain_adj_support
    have hnd := hQ.1.support_nodup
    have hh := hhead
    have hl := hlast
    rw [h] at hch hnd hh hl
    have hnd' := hnd
    rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd'
    have huv : u ≠ v := fun e => hnd'.2.1.1 (by simp [e])
    have hvX₁ : v ∉ X₁ := fun e => hnd'.2.2 v e v (by simp) rfl
    have huX₂ : u ∉ v :: X₂ := hnd'.2.1.1
    have e1 : X₁ ++ u :: v :: X₂ = (X₁ ++ [u]) ++ (v :: X₂) := by simp
    rw [e1] at hch hh hl
    have c1 : (X₁ ++ [u]).IsChain G.Adj := isChain_of_sup_edge hch.left_of_append (by
      simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hvX₁, huv.symm⟩)
    have c2 : (v :: X₂).IsChain G.Adj := by
      rw [edge_comm] at hch
      exact isChain_of_sup_edge hch.right_of_append huX₂
    have hh1 : (X₁ ++ [u]).head? = some a := by cases X₁ <;> simpa using hh
    have hl2 : (v :: X₂).getLast? = some b := by
      rwa [List.getLast?_append_of_ne_nil _ (by simp)] at hl
    obtain ⟨p₁, hp₁⟩ := exists_walk_of_chain (u := a) (v := u) _ c1 hh1 (by simp)
    obtain ⟨p₂, hp₂⟩ := exists_walk_of_chain (u := v) (v := b) _ c2 (by simp) hl2
    refine searchCrossWalk_isSome_of_walk_avoiding hverts hCnd halt hR_byp
      (p₁.append (W.append p₂)) fun x hx hxR => ?_
    have hxR' := R.support_bypass_subset_support hxR
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, hp₁, hp₂] at hx
    rcases hx with hx | hx | hx
    · exact hdisj (h ▸ e1 ▸ List.mem_append_left _ hx) hxR'
    · exact hW x hx hxR'
    · exact hdisj (h ▸ e1 ▸ List.mem_append_right _ hx) hxR'
  · have hch := Q.isChain_adj_support
    have hnd := hQ.1.support_nodup
    have hh := hhead
    have hl := hlast
    rw [h, edge_comm] at hch
    rw [h] at hnd hh hl
    have hnd' := hnd
    rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd'
    have hvu : v ≠ u := fun e => hnd'.2.1.1 (by simp [e])
    have huX₁ : u ∉ X₁ := fun e => hnd'.2.2 u e u (by simp) rfl
    have hvX₂ : v ∉ u :: X₂ := hnd'.2.1.1
    have e1 : X₁ ++ v :: u :: X₂ = (X₁ ++ [v]) ++ (u :: X₂) := by simp
    rw [e1] at hch hh hl
    have c1 : (X₁ ++ [v]).IsChain G.Adj := isChain_of_sup_edge hch.left_of_append (by
      simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨huX₁, hvu.symm⟩)
    have c2 : (u :: X₂).IsChain G.Adj := by
      rw [edge_comm] at hch
      exact isChain_of_sup_edge hch.right_of_append hvX₂
    have hh1 : (X₁ ++ [v]).head? = some a := by cases X₁ <;> simpa using hh
    have hl2 : (u :: X₂).getLast? = some b := by
      rwa [List.getLast?_append_of_ne_nil _ (by simp)] at hl
    obtain ⟨p₁, hp₁⟩ := exists_walk_of_chain (u := a) (v := v) _ c1 hh1 (by simp)
    obtain ⟨p₂, hp₂⟩ := exists_walk_of_chain (u := u) (v := b) _ c2 (by simp) hl2
    refine searchCrossWalk_isSome_of_walk_avoiding hverts hCnd halt hR_byp
      (p₁.append (W.reverse.append p₂)) fun x hx hxR => ?_
    have hxR' := R.support_bypass_subset_support hxR
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse, hp₁, hp₂] at hx
    rcases hx with hx | hx | hx
    · exact hdisj (h ▸ e1 ▸ List.mem_append_left _ hx) hxR'
    · exact hW x hx hxR'
    · exact hdisj (h ▸ e1 ▸ List.mem_append_right _ hx) hxR'

/-! ### 4. `runCandidateSearches` and `transferWalkOption` -/

/-- Run a list of candidate searches in order, stopping at the first search that finds a crossing
and accumulating the number of searches performed. -/
@[expose] def runCandidateSearches [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V]
    (verts C : List V) : List (Σ x y : V, G.Walk x y) → Option (CrossingWalks G C) × ℕ
  | [] => (none, 0)
  | ⟨_, _, Z⟩ :: rest =>
    let res := searchCrossWalk G verts C Z
    match res.1 with
    | some cr => (some cr, res.2)
    | none =>
      let tail := runCandidateSearches G verts C rest
      (tail.1, res.2 + tail.2)

/-- Every crossing returned by `runCandidateSearches` is a valid crossing of `C` in `G`. -/
theorem runCandidateSearches_valid [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C : List V} {cands : List (Σ x y : V, G.Walk x y)} {cr : CrossingWalks G C}
    (h : (runCandidateSearches G verts C cands).1 = some cr) : cr.Valid := by
  induction cands with
  | nil => simp [runCandidateSearches] at h
  | cons hd tl ih =>
    rcases hd with ⟨x, y, Z⟩
    simp only [runCandidateSearches] at h
    split at h
    · rename_i cr' hcr'
      injection h with hEq
      subst hEq
      exact searchCrossWalk_valid hcr'
    · exact ih h

/-- `runCandidateSearches` makes at most `cands.length` searches. -/
theorem runCandidateSearches_searches_le [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [WalkSearch V]
    (verts C : List V) (cands : List (Σ x y : V, G.Walk x y)) :
    (runCandidateSearches G verts C cands).2 ≤ cands.length := by
  induction cands with
  | nil => simp [runCandidateSearches]
  | cons hd tl ih =>
    rcases hd with ⟨x, y, Z⟩
    simp only [runCandidateSearches, List.length_cons]
    split
    · simp [searchCrossWalk_searches]
    · simp only [searchCrossWalk_searches]; omega

/-- If any candidate `cand ∈ cands` succeeds under `searchCrossWalk`, then `runCandidateSearches`
returns `some` valid crossing. -/
theorem runCandidateSearches_isSome_of_mem [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {verts C : List V} {cands : List (Σ x y : V, G.Walk x y)}
    {x y : V} {Z : G.Walk x y} (hmem : (⟨x, y, Z⟩ : Σ u v : V, G.Walk u v) ∈ cands)
    (hsome : (searchCrossWalk G verts C Z).1.isSome = true) :
    (runCandidateSearches G verts C cands).1.isSome = true := by
  induction cands with
  | nil => cases List.not_mem_nil hmem
  | cons hd tl ih =>
    rcases hd with ⟨x₀, y₀, Z₀⟩
    simp only [runCandidateSearches]
    split
    · rfl
    · rename_i hnone
      rcases List.mem_cons.mp hmem with h_eq | htl
      · rcases Sigma.mk.inj_iff.mp h_eq with ⟨rfl, h_eq'⟩
        rcases Sigma.mk.inj_iff.mp (eq_of_heq h_eq') with ⟨rfl, hZ_eq⟩
        cases eq_of_heq hZ_eq
        rw [hnone] at hsome
        simp at hsome
      · exact ih htl

/-- **Computable walk transfer (`transferWalkOption`).**
Transfers a walk `p : G'.Walk u v` to `G` if every edge of `p` lies in `G`, and returns `none`
otherwise. -/
@[expose] def transferWalkOption [DecidableRel G.Adj] {G' : SimpleGraph V} {u v : V} :
    G'.Walk u v → Option (G.Walk u v)
  | .nil => some .nil
  | .cons (u := x) (v := y) _ p =>
    if h : G.Adj x y then
      match transferWalkOption p with
      | some p' => some (.cons h p')
      | none => none
    else
      none

theorem transferWalkOption_support [DecidableRel G.Adj] {G' : SimpleGraph V} {u v : V}
    {p : G'.Walk u v} {q : G.Walk u v} (h : transferWalkOption (G := G) p = some q) :
    q.support = p.support := by
  induction p with
  | nil =>
    simp only [transferWalkOption, Option.some.injEq] at h
    subst h
    rfl
  | cons hadj p ih =>
    simp only [transferWalkOption] at h
    split_ifs at h with hG
    split at h
    · rename_i p' hp'
      injection h with hq
      subst hq
      simp [ih hp']
    · simp at h

theorem transferWalkOption_isPath [DecidableRel G.Adj] {G' : SimpleGraph V} {u v : V}
    {p : G'.Walk u v} {q : G.Walk u v} (h : transferWalkOption (G := G) p = some q)
    (hp : p.IsPath) : q.IsPath := by
  rw [Walk.isPath_def, transferWalkOption_support h]
  exact hp.support_nodup

theorem transferWalkOption_isTPath [DecidableRel G.Adj] {G' : SimpleGraph V} {T : List V}
    {u v : V} {p : G'.Walk u v} {q : G.Walk u v} (h : transferWalkOption (G := G) p = some q)
    (hp : IsTPath G' T p) : IsTPath G T q := by
  refine ⟨transferWalkOption_isPath h hp.1, hp.2.1, hp.2.2.1, ?_⟩
  rw [transferWalkOption_support h]
  exact hp.2.2.2

theorem transferWalkOption_isSome_of_edges [DecidableRel G.Adj] {G' : SimpleGraph V} {u v : V}
    (p : G'.Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    (transferWalkOption (G := G) p).isSome = true := by
  induction p with
  | nil => rfl
  | @cons x w v _ p ih =>
    simp only [transferWalkOption]
    have hG : G.Adj x w := hp s(x, w) (by simp)
    split_ifs
    · have htl := ih fun e he => hp e (by simp [he])
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.mp htl
      simp [hp']

theorem mem_edges_of_transferWalkOption_none [DecidableRel G.Adj] {y s u v : V}
    {p : (G ⊔ edge y s).Walk u v} (h : transferWalkOption (G := G) p = none) :
    s(y, s) ∈ p.edges := by
  induction p with
  | nil => simp [transferWalkOption] at h
  | @cons x w v hadj p ih =>
    simp only [transferWalkOption] at h
    split_ifs at h with hG
    · split at h
      · simp at h
      · rename_i hnone
        exact List.mem_cons_of_mem _ (ih hnone)
    · rcases hadj with hG' | hedge
      · exact absurd hG' hG
      · have hsym : s(x, w) = s(y, s) := hedge.1
        rw [Walk.edges_cons, List.mem_cons]
        exact Or.inl hsym.symm

/-! ### Part 5: Computable chain-to-walk conversion and candidate-chain search -/

/-- Auxiliary computable conversion of a list `rest` starting after `x` into a walk from `x`. -/
@[expose] def walkOfChainAux (G : SimpleGraph V) [DecidableRel G.Adj] :
    (x : V) → List V → Option (Σ v : V, G.Walk x v)
  | x, [] => some ⟨x, .nil⟩
  | x, y :: rest =>
    if h : G.Adj x y then
      match walkOfChainAux G y rest with
      | some ⟨v, p⟩ => some ⟨v, .cons h p⟩
      | none => none
    else
      none

/-- Computably convert a vertex list `X : List V` into `some ⟨u, v, p⟩` if `X` is a non-empty
`G.Adj`-chain, or `none` otherwise (`0` searches, `O(X.length)` adjacency checks). -/
@[expose] def walkOfChainOption (G : SimpleGraph V) [DecidableRel G.Adj] :
    List V → Option (Σ u v : V, G.Walk u v)
  | [] => none
  | x :: rest =>
    match walkOfChainAux G x rest with
    | some ⟨v, p⟩ => some ⟨x, v, p⟩
    | none => none

theorem walkOfChainAux_eq_some_of_isChain [DecidableRel G.Adj] :
    ∀ {rest : List V} {x v : V},
      (x :: rest).IsChain G.Adj → (x :: rest).getLast? = some v →
      ∃ p : G.Walk x v, walkOfChainAux G x rest = some ⟨v, p⟩ ∧ p.support = x :: rest
  | [], x, v, _, hl => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl
    exact ⟨.nil, rfl, rfl⟩
  | y :: rest, x, v, hch, hl => by
    rw [List.isChain_cons_cons] at hch
    rw [List.getLast?_cons_cons] at hl
    obtain ⟨p, hp, hsupp⟩ := walkOfChainAux_eq_some_of_isChain hch.2 hl
    refine ⟨.cons hch.1 p, ?_, by simp [hsupp]⟩
    simp [walkOfChainAux, hch.1, hp]

theorem walkOfChainOption_eq_some_of_isChain [DecidableRel G.Adj] {X : List V} {c d : V}
    (hch : X.IsChain G.Adj) (hh : X.head? = some c) (hl : X.getLast? = some d) :
    ∃ p : G.Walk c d, walkOfChainOption G X = some ⟨c, d, p⟩ ∧ p.support = X := by
  cases X with
  | nil => simp at hh
  | cons x rest =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    obtain ⟨p, hp, hsupp⟩ := walkOfChainAux_eq_some_of_isChain hch hl
    exact ⟨p, by simp [walkOfChainOption, hp], hsupp⟩

/-- **Completeness of `runCandidateSearches` over candidate chains.** If `X ∈ chains` is a `G.Adj`-chain
between `c ∈ C` and `d ∈ C` whose internal vertices avoid `C`, `Alternate C a b c d`, and there is a
walk `W : G.Walk a b` avoiding `X`, then running `runCandidateSearches` on
`chains.filterMap (walkOfChainOption G)` returns `some` crossing of `C` in `G`. -/
theorem runCandidateSearches_isSome_of_chain [DecidableEq V] [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts : List V} (hverts : ∀ v : V, v ∈ verts) {C : List V} (hCnd : C.Nodup)
    {chains : List (List V)} {X : List V} (hX_mem : X ∈ chains)
    (hX_ch : X.IsChain G.Adj) {a b c d : V}
    (hh : X.head? = some c) (hl : X.getLast? = some d)
    (hc : c ∈ C) (hd : d ∈ C) (hin : ∀ w ∈ X, w ∈ C → w = c ∨ w = d)
    (halt : Alternate C a b c d) (W : G.Walk a b) (hW : ∀ w ∈ W.support, w ∉ X) :
    (runCandidateSearches G verts C (chains.filterMap (walkOfChainOption G))).1.isSome = true := by
  obtain ⟨p, hp, hsupp⟩ := walkOfChainOption_eq_some_of_isChain hX_ch hh hl
  have hmem_p : (⟨c, d, p⟩ : Σ u v : V, G.Walk u v) ∈ chains.filterMap (walkOfChainOption G) :=
    List.mem_filterMap.mpr ⟨X, hX_mem, hp⟩
  have hp_tpath : IsTPath G C p.bypass := by
    refine ⟨p.bypass_isPath, hc, hd, fun w hw hwc hwd => ?_⟩
    have hwX : w ∈ X := hsupp ▸ p.support_bypass_subset_support hw
    have hwC : w ∉ C := fun h => (hin w hwX h).elim hwc hwd
    exact ⟨hwC, hwC⟩
  have hsearch : (searchCrossWalk G verts C p).1.isSome = true :=
    searchCrossWalk_isSome_of_walk_avoiding hverts hCnd halt hp_tpath W fun w hw hwb =>
      hW w hw (hsupp ▸ p.support_bypass_subset_support hwb)
  exact runCandidateSearches_isSome_of_mem hmem_p hsearch

/-- Candidate vertex chains for a single oriented subinstance path `X₀` along `P_supp`. -/
@[expose] def figure11ChainsForOne [DecidableEq V] (P_supp X₀ : List V) : List (List V) :=
  let ext := ([P_supp, P_supp.reverse]).map fun lp =>
    match X₀.getLast? with
    | some z => X₀ ++ (lp.take (lp.idxOf z)).reverse
    | none => X₀
  let spl := ([P_supp, P_supp.reverse]).flatMap fun lp =>
    match X₀.head?, X₀.getLast? with
    | some z₁, some z₂ =>
      let s := lp.take (lp.idxOf z₁) ++ X₀ ++ lp.drop (lp.idxOf z₂ + 1)
      [s, s.reverse]
    | _, _ => [X₀, X₀]
  X₀ :: (ext ++ spl)

theorem figure11ChainsForOne_length [DecidableEq V] (P_supp X₀ : List V) :
    (figure11ChainsForOne P_supp X₀).length = 7 := by
  unfold figure11ChainsForOne
  cases X₀.head? <;> cases X₀.getLast? <;> rfl

/-- Candidate vertex chains for lifting a subinstance crossing `(Q, R)` along `P_supp` (`P'.support`)
via the five cases of Figure 11 (`Setting.cross_of_side`, `case4`, `case5`). Purely computable (`0`
searches, `28` chains). -/
@[expose] def figure11CandidateChains [DecidableEq V] (P_supp Q_supp R_supp : List V) :
    List (List V) :=
  ([Q_supp, Q_supp.reverse, R_supp, R_supp.reverse]).flatMap (figure11ChainsForOne P_supp)

theorem figure11CandidateChains_length [DecidableEq V] (P_supp Q_supp R_supp : List V) :
    (figure11CandidateChains P_supp Q_supp R_supp).length ≤ 28 := by
  simp [figure11CandidateChains, List.flatMap_cons, List.flatMap_nil, List.length_append,
    figure11ChainsForOne_length]

/-! ### Part 6: Computable bridge extraction (`bridgeOfList`) -/

/-- Auxiliary scan for `bridgeOfList`: given the most recent pocket vertex `σ ∈ N` and the vertices
`acc` seen since `σ`, scan `rest` until the first vertex `z ∈ out` (returning `some (σ, acc, z)`),
resetting `σ` and `acc` whenever another vertex of `N` is encountered. -/
@[expose] def findBridgeAux [DecidableEq V] (N out : List V) (σ : V) (acc : List V) :
    List V → Option (V × List V × V)
  | [] => none
  | w :: rest =>
    if w ∈ N then
      findBridgeAux N out w [] rest
    else if w ∈ out then
      some (σ, acc, w)
    else
      findBridgeAux N out σ (acc ++ [w]) rest

/-- Computably extract the first bridge `(σ, M, z)` from `N` to `out` (`L₁ ++ L₂`) along a vertex
list `L : List V` (`0` searches, `O(L.length)` steps). -/
@[expose] def bridgeOfList [DecidableEq V] (N out : List V) :
    List V → Option (V × List V × V)
  | [] => none
  | w :: rest =>
    if w ∈ N then
      findBridgeAux N out w [] rest
    else
      bridgeOfList N out rest

theorem findBridgeAux_spec [DecidableEq V] {N out : List V} :
    ∀ {rest : List V} {σ σ' z : V} {acc M : List V},
      σ ∈ N → (∀ x ∈ acc, x ∉ N ∧ x ∉ out) →
      findBridgeAux N out σ acc rest = some (σ', M, z) →
      σ' ∈ N ∧ z ∈ out ∧ (∀ x ∈ M, x ∉ N ∧ x ∉ out) ∧ (σ' :: M ++ [z]) <:+: (σ :: acc ++ rest)
  | [], _, _, _, _, _, _, _, h => by simp [findBridgeAux] at h
  | w :: rest, σ, σ', z, acc, M, hσ, hacc, h => by
    simp only [findBridgeAux] at h
    split_ifs at h with hwN hwOut
    · obtain ⟨hσ', hz, hM, hinf⟩ :=
        findBridgeAux_spec (rest := rest) hwN (fun _ hx => by simp at hx) h
      refine ⟨hσ', hz, hM, hinf.trans ⟨σ :: acc, [], by simp⟩⟩
    · injection h with hEq
      rcases Prod.mk.inj hEq with ⟨rfl, hEq'⟩
      rcases Prod.mk.inj hEq' with ⟨rfl, rfl⟩
      refine ⟨hσ, hwOut, hacc, ⟨[], rest, by simp⟩⟩
    · have hacc' : ∀ x ∈ acc ++ [w], x ∉ N ∧ x ∉ out := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hacc x hx
        · rw [List.mem_singleton.mp hx]; exact ⟨hwN, hwOut⟩
      obtain ⟨hσ', hz, hM, hinf⟩ := findBridgeAux_spec (rest := rest) hσ hacc' h
      refine ⟨hσ', hz, hM, ?_⟩
      simpa using hinf

theorem bridgeOfList_spec [DecidableEq V] {N out L : List V} {σ z : V} {M : List V}
    (h : bridgeOfList N out L = some (σ, M, z)) :
    σ ∈ N ∧ z ∈ out ∧ (∀ x ∈ M, x ∉ N ∧ x ∉ out) ∧ (σ :: M ++ [z]) <:+: L := by
  induction L with
  | nil => simp [bridgeOfList] at h
  | cons w rest ih =>
    simp only [bridgeOfList] at h
    split_ifs at h with hwN
    · simpa using findBridgeAux_spec hwN (fun _ hx => by simp at hx) h
    · obtain ⟨hσ, hz, hM, hinf⟩ := ih h
      exact ⟨hσ, hz, hM, hinf.trans ⟨[w], [], by simp⟩⟩

theorem findBridgeAux_isSome [DecidableEq V] {N out : List V} (hdisj : ∀ x ∈ N, x ∉ out) :
    ∀ {rest : List V} (σ : V) (acc : List V),
      (∃ z₀ ∈ rest, z₀ ∈ out) → (findBridgeAux N out σ acc rest).isSome = true
  | [], _, _, ⟨_, hz, _⟩ => by simp at hz
  | w :: rest, σ, acc, ⟨z₀, hz₀, hzOut⟩ => by
    simp only [findBridgeAux]
    split_ifs with hwN hwOut
    · rcases List.mem_cons.mp hz₀ with rfl | hz₀'
      · exact absurd hzOut (hdisj z₀ hwN)
      · exact findBridgeAux_isSome hdisj w [] ⟨z₀, hz₀', hzOut⟩
    · rfl
    · rcases List.mem_cons.mp hz₀ with rfl | hz₀'
      · exact absurd hzOut hwOut
      · exact findBridgeAux_isSome hdisj σ (acc ++ [w]) ⟨z₀, hz₀', hzOut⟩

theorem bridgeOfList_isSome [DecidableEq V] {N out : List V} (hdisj : ∀ x ∈ N, x ∉ out) :
    ∀ {α β : List V} {v₀ : V},
      v₀ ∈ N → (∃ z₀ ∈ β, z₀ ∈ out) →
      (bridgeOfList N out (α ++ v₀ :: β)).isSome = true
  | [], β, v₀, hv₀, hβ => by
    simp only [List.nil_append, bridgeOfList, hv₀, ↓reduceIte]
    exact findBridgeAux_isSome hdisj v₀ [] hβ
  | w :: α, β, v₀, hv₀, hβ => by
    simp only [List.cons_append, bridgeOfList]
    split_ifs with hwN
    · obtain ⟨z₀, hz₀, hzOut⟩ := hβ
      exact findBridgeAux_isSome hdisj w [] ⟨z₀, by simp [hz₀], hzOut⟩
    · exact bridgeOfList_isSome hdisj hv₀ hβ

/-! ### Part 7: Computable candidate chains for Rules 1 to 4 (`undoEdgeCandidateChains`) -/

/-- Computably find a side walk in `G₀` from `u` to `S` avoiding `C ∪ P_supp` at inner vertices,
bypass it to a simple path, and return its vertex support (or `[]` if none exists). -/
@[expose] def sideWalkSupport (G₀ : SimpleGraph V) [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V]
    (verts C P_supp : List V) (u : V) (S : List V) : List V :=
  let allowed := verts.filter fun x => !decide (x ∈ C) && !decide (x ∈ P_supp)
  match findWalkFromTo G₀ allowed u S with
  | some ⟨_, p⟩ => p.bypass.support
  | none => []

theorem sideWalkSupport_of_isOnSide (G₀ : SimpleGraph V) [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts C P_supp S : List V} (hverts : ∀ v : V, v ∈ verts) {u : V}
    (hu : IsOnSide G₀ {x | x ∈ C ∨ x ∈ P_supp} {x | x ∈ S} u) :
    ∃ b₀ ∈ S, ∃ p : G₀.Walk u b₀, p.IsPath ∧
      (∀ x ∈ p.support, x ≠ u → x ≠ b₀ → x ∉ C ∧ x ∉ P_supp) ∧
      sideWalkSupport G₀ verts C P_supp u S = p.support := by
  obtain ⟨v, hv, q, -, hq⟩ := hu
  set allowed := verts.filter fun x => !decide (x ∈ C) && !decide (x ∈ P_supp)
  have hsome : (findWalkFromTo G₀ allowed u S).isSome = true := by
    refine findWalkFromTo_isSome_of_walk G₀ hv q fun x hx hxu hxv => ?_
    have hx_not := hq x hx hxu hxv
    have hxC : x ∉ C := fun h => hx_not (Or.inl h)
    have hxP : x ∉ P_supp := fun h => hx_not (Or.inr h)
    exact List.mem_filter.mpr ⟨hverts x, by simp [hxC, hxP]⟩
  obtain ⟨⟨b₀, p₀⟩, hp₀⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hb₀, hsupp⟩ := findWalkFromTo_mem_and_support G₀ hp₀
  refine ⟨b₀, hb₀, p₀.bypass, p₀.bypass_isPath, fun x hx hxu hxb => ?_, by
    simp [sideWalkSupport, allowed, hp₀]⟩
  have hx₀ := p₀.support_bypass_subset_support hx
  rcases hsupp x hx₀ with rfl | rfl | hx_al
  · exact absurd rfl hxu
  · exact absurd rfl hxb
  · have hfilt := (List.mem_filter.mp hx_al).2
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hfilt
    exact hfilt

/-- Rule 2 candidate chain: replace the edge `(y, s)` or `(s, y)` in `Q_supp` by the pocket
segment `y :: N ++ [s]` (or its reverse). -/
@[expose] def rule2PocketChain [DecidableEq V] (y s : V) (N Q_supp : List V) : List V :=
  if Q_supp.idxOf y < Q_supp.idxOf s then
    Q_supp.take (Q_supp.idxOf y) ++ (y :: N ++ [s]) ++ Q_supp.drop (Q_supp.idxOf s + 1)
  else
    Q_supp.take (Q_supp.idxOf s) ++ (y :: N ++ [s]).reverse ++ Q_supp.drop (Q_supp.idxOf y + 1)

/-- Rule 3 candidate chain from a bridge `(σ, M, z)`: reroute `P_supp` along `σ :: M ++ [z]`. -/
@[expose] def rule3ChainOfBridge [DecidableEq V] (P_supp L₁ : List V) :
    Option (V × List V × V) → List V
  | some (σ, M, z) =>
    if z ∈ L₁ then
      P_supp.take (P_supp.idxOf z + 1) ++ M.reverse ++ P_supp.drop (P_supp.idxOf σ)
    else
      P_supp.take (P_supp.idxOf σ + 1) ++ M ++ P_supp.drop (P_supp.idxOf z)
  | none => P_supp

/-- Rule 4 candidate chains for a pocket vertex `σ`: splice a side path from `y` or `s` with the
pocket segment to `σ` and either the prefix/suffix of `R_supp` from `σ` or a side path from `σ`. -/
@[expose] def rule4ChainsForSigma [DecidableEq V]
    (N R_supp pBy pBs pAy pAs pAσ pBσ : List V) (σ : V) : List (List V) :=
  let bps := [
    pBy.reverse ++ N.take (N.idxOf σ + 1),
    pBs.reverse ++ (N.drop (N.idxOf σ)).reverse,
    pAy.reverse ++ N.take (N.idxOf σ + 1),
    pAs.reverse ++ (N.drop (N.idxOf σ)).reverse
  ]
  let ats := [
    (R_supp.take (R_supp.idxOf σ)).reverse,
    R_supp.drop (R_supp.idxOf σ + 1),
    pAσ.tail,
    pBσ.tail
  ]
  bps.flatMap fun bp => ats.map fun at_ => bp ++ at_

theorem rule4ChainsForSigma_length [DecidableEq V]
    (N R_supp pBy pBs pAy pAs pAσ pBσ : List V) (σ : V) :
    (rule4ChainsForSigma N R_supp pBy pBs pAy pAs pAσ pBσ σ).length = 16 := rfl

/-- Computably construct all candidate chains of Rules 1 to 4 for undoing one added edge `y s`
from a crossing `(Q, R₀)` where `Q` uses `s(y, s)` and `R₀` is in `G₀`. Performs `8` `findWalkFromTo`
side-path searches and produces `36` candidate chains. -/
@[expose] def undoEdgeCandidateChains (G₀ : SimpleGraph V) [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V]
    (verts C A B P_supp L₁ N L₂ : List V) (y s : V) (Q_supp R_supp : List V) : List (List V) :=
  let pBy := sideWalkSupport G₀ verts C P_supp y B
  let pBs := sideWalkSupport G₀ verts C P_supp s B
  let pAy := sideWalkSupport G₀ verts C P_supp y A
  let pAs := sideWalkSupport G₀ verts C P_supp s A
  let b₁ := bridgeOfList N (L₁ ++ L₂) R_supp
  let b₂ := bridgeOfList N (L₁ ++ L₂) R_supp.reverse
  let σ₁ := match b₁ with | some (σ, _, _) => σ | none => y
  let σ₂ := match b₂ with | some (σ, _, _) => σ | none => y
  let pAσ₁ := sideWalkSupport G₀ verts C P_supp σ₁ A
  let pBσ₁ := sideWalkSupport G₀ verts C P_supp σ₁ B
  let pAσ₂ := sideWalkSupport G₀ verts C P_supp σ₂ A
  let pBσ₂ := sideWalkSupport G₀ verts C P_supp σ₂ B
  let r1 := R_supp
  let r2 := rule2PocketChain y s N Q_supp
  let r3_1 := rule3ChainOfBridge P_supp L₁ b₁
  let r3_2 := rule3ChainOfBridge P_supp L₁ b₂
  let r4_1 := rule4ChainsForSigma N R_supp pBy pBs pAy pAs pAσ₁ pBσ₁ σ₁
  let r4_2 := rule4ChainsForSigma N R_supp pBy pBs pAy pAs pAσ₂ pBσ₂ σ₂
  [r1, r2, r3_1, r3_2] ++ r4_1 ++ r4_2

theorem undoEdgeCandidateChains_length (G₀ : SimpleGraph V) [DecidableEq V] [DecidableRel G₀.Adj]
    [WalkSearch V]
    (verts C A B P_supp L₁ N L₂ : List V) (y s : V) (Q_supp R_supp : List V) :
    (undoEdgeCandidateChains G₀ verts C A B P_supp L₁ N L₂ y s Q_supp R_supp).length = 36 := by
  dsimp only [undoEdgeCandidateChains]
  rw [List.length_append, List.length_append, rule4ChainsForSigma_length, rule4ChainsForSigma_length]
  rfl

end GraphMinor.HP25
