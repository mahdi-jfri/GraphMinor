module

import GraphMinor.HP25.Linkage
import Mathlib.Tactic.FinCases

/-!
# Lemma 5.4 of Humeau and Pous is false as printed

Humeau and Pous, arXiv:2505.16431v2, Lemma 5.4 (page 19) takes a graph `G` with a cycle `C` and a
`C`-path `P = y₁ … y_l` between non-consecutive vertices of `C`, defines indices `j < r ≤ s` from
the `P`-sides of the vertices of `P`, and claims: "Then the edge $y_jy_s$ is safe". An edge is
*safe* (page 15) "if, when $T$ is crossed in $G+F$, then $T$ is crossed in $G$".

The graph `ex54` below has seven vertices. With `a b c d p q r = 0 1 2 3 4 5 6`:
* `C = a b c d` is a 4-cycle of `ex54`, and `P = c p q r a` is a `C`-path between the
  non-consecutive vertices `c` and `a`. The two subpaths of `C` between `c` and `a` have interiors
  `P̊₁ = {d}` and `P̊₂ = {b}`.
* Every vertex is on `C` or on `P`, so a path whose inner vertices avoid `C ∪ P` is a single edge,
  and the `P`-sides are read off the adjacency (`isOnSide_univ_iff`): `c` and `a` are on both sides,
  `p` only on side 2, and `q`, `r` only on side 1.
* So `j = 1` (`y₁ = c`), `r = 2` (`y₂ = p`, side 2 only) and `s = 3` (`y₃ = q`, the first vertex on
  side 1), and the lemma's edge is `c q`.
* `C` is not crossed in `ex54` (`not_isCrossed_ex54`), but it is crossed in `ex54 ⊔ edge c q`
  (`isCrossed_ex54_sup`). So the edge is not safe.

Algorithm 5.1 of the paper, given this `C` and this `P`, therefore answers that `C` is crossed.
-/

namespace GraphMinor.HP25.Ex54

open SimpleGraph

/-- The edges of the example: the cycle `a b c d`, the path `c p q r a`, and `bp, dq, dr, aq, pr`. -/
def ex54Edges : List (Sym2 (Fin 7)) :=
  [s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(2, 4), s(4, 5), s(5, 6), s(6, 0), s(1, 4), s(3, 5),
    s(3, 6), s(0, 5), s(4, 6)]

/-- The graph of the counterexample. -/
def ex54 : SimpleGraph (Fin 7) where
  Adj u v := s(u, v) ∈ ex54Edges
  symm := ⟨fun u v h => by simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨fun u => by revert u; decide⟩

instance : DecidableRel ex54.Adj := fun u v =>
  inferInstanceAs (Decidable (s(u, v) ∈ ex54Edges))

/-- The cycle `C = a b c d`. -/
def C : List (Fin 7) := [0, 1, 2, 3]

/-- The `C`-path `P = c p q r a`. -/
def P : ex54.Walk 2 0 :=
  .cons (by decide : ex54.Adj 2 4) <| .cons (by decide : ex54.Adj 4 5) <|
    .cons (by decide : ex54.Adj 5 6) <| .cons (by decide : ex54.Adj 6 0) .nil

/-- `P` is a `C`-path. -/
theorem isTPath_P : IsTPath ex54 C P := by
  refine ⟨by simp [P, Walk.cons_isPath_iff], by decide, by decide, ?_⟩
  intro x hx hx2 hx0
  simp [P, C] at hx ⊢
  omega

/-- When `X` holds every vertex, `y` is `X`-connected to `A` exactly when `y ∈ A` or `y` has a
neighbour in `A`. -/
theorem isOnSide_univ_iff {V : Type*} {G : SimpleGraph V} {A : Set V} {y : V} :
    IsOnSide G Set.univ A y ↔ ∃ z ∈ A, y = z ∨ G.Adj y z := by
  constructor
  · rintro ⟨z, hz, p, hp, hin⟩
    refine ⟨z, hz, ?_⟩
    cases p with
    | nil => exact Or.inl rfl
    | cons h q =>
      rename_i w
      by_cases hwz : w = z
      · subst hwz; exact Or.inr h
      · have hwy : w ≠ y := fun hwy => by
          subst hwy
          exact (Walk.cons_isPath_iff h q).1 hp |>.2 q.start_mem_support
        exact absurd (Set.mem_univ w)
          (hin w (by simp) hwy hwz)
  · rintro ⟨z, hz, h | h⟩
    · subst h
      exact ⟨y, hz, .nil, Walk.IsPath.nil, fun x hx h1 _ => by simp_all⟩
    · refine ⟨z, hz, .cons h .nil, ?_, fun x hx h1 h2 => ?_⟩
      · simp [Walk.cons_isPath_iff, h.ne]
      · simp at hx; tauto

/-- The `P`-sides of the vertices of `P = c p q r a`, with `P̊₁ = {d}` and `P̊₂ = {b}`, and
`X = C ∪ P`, which is every vertex. -/
theorem sides :
    (IsOnSide ex54 Set.univ {3} 2 ∧ IsOnSide ex54 Set.univ {1} 2) ∧
    (¬ IsOnSide ex54 Set.univ {3} 4 ∧ IsOnSide ex54 Set.univ {1} 4) ∧
    (IsOnSide ex54 Set.univ {3} 5 ∧ ¬ IsOnSide ex54 Set.univ {1} 5) ∧
    (IsOnSide ex54 Set.univ {3} 6 ∧ ¬ IsOnSide ex54 Set.univ {1} 6) ∧
    (IsOnSide ex54 Set.univ {3} 0 ∧ IsOnSide ex54 Set.univ {1} 0) := by
  simp only [isOnSide_univ_iff, Set.mem_singleton_iff, exists_eq_left]
  decide

/-- `C` is not crossed in `ex54`. A crossing would pair a path `a … c` with a path `b … d`; the
last inner vertex of the first and the first inner vertex of the second must both be `p`, the
only neighbour of `c` and of `b` off the other path. -/
theorem not_isCrossed_ex54 : ¬ IsCrossed ex54 C := by
  rw [C, isCrossed_iff_linkage]
  rintro ⟨P₁, P₂, -, -, hdisj⟩
  have nb1 : ∀ w, ex54.Adj 1 w → w = 0 ∨ w = 2 ∨ w = 4 := by decide
  have nb2 : ∀ w, ex54.Adj 2 w → w = 1 ∨ w = 3 ∨ w = 4 := by decide
  have h4₂ : (4 : Fin 7) ∈ P₂.support := by
    cases P₂ with
    | cons h q =>
      rename_i w
      rcases nb1 w h with rfl | rfl | rfl
      · exact absurd q.start_mem_support (fun hq => hdisj P₁.start_mem_support (by simp [hq]))
      · exact absurd q.start_mem_support (fun hq => hdisj P₁.end_mem_support (by simp [hq]))
      · simp
  have h4₁ : (4 : Fin 7) ∈ P₁.support := by
    have hsub : ∀ x ∈ P₁.reverse.support, x ∈ P₁.support := fun x hx => by
      simpa [Walk.support_reverse] using hx
    apply hsub
    generalize P₁.reverse = R at hsub
    cases R with
    | cons h q =>
      rename_i w
      rcases nb2 w h with rfl | rfl | rfl
      · exact absurd (hsub _ (by simp)) (fun h1 => hdisj h1 P₂.start_mem_support)
      · exact absurd (hsub _ (by simp)) (fun h1 => hdisj h1 P₂.end_mem_support)
      · simp
  exact hdisj h4₁ h4₂

/-- `C` is crossed in `ex54` plus the edge `c q`: the paths `a q c` and `b p r d` cross it. -/
theorem isCrossed_ex54_sup : IsCrossed (ex54 ⊔ edge 2 5) C := by
  rw [C, isCrossed_iff_linkage]
  have h05 : (ex54 ⊔ edge 2 5).Adj 0 5 := Or.inl (by decide)
  have h52 : (ex54 ⊔ edge 2 5).Adj 5 2 := Or.inr (by simp [edge_adj])
  have h14 : (ex54 ⊔ edge 2 5).Adj 1 4 := Or.inl (by decide)
  have h46 : (ex54 ⊔ edge 2 5).Adj 4 6 := Or.inl (by decide)
  have h63 : (ex54 ⊔ edge 2 5).Adj 6 3 := Or.inl (by decide)
  refine ⟨.cons h05 (.cons h52 .nil), .cons h14 (.cons h46 (.cons h63 .nil)), ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

/-- The edge `c q` of Lemma 5.4 is not safe for `C` in `ex54`, and it is not already an edge. -/
theorem lemma_5_4_counterexample :
    ¬ ex54.Adj 2 5 ∧ IsCrossed (ex54 ⊔ edge 2 5) C ∧ ¬ IsCrossed ex54 C :=
  ⟨by decide, isCrossed_ex54_sup, not_isCrossed_ex54⟩

end GraphMinor.HP25.Ex54

namespace GraphMinor.HP25

/-!
# Lemma 5.4 is false also for an induced path

A first attempt at a correction of Lemma 5.4 asks the `C`-path `P` to be induced. The graph `G`
below shows that this is not enough. It has nine vertices, `C = 0 1 2 3` is a 4-cycle of `G`, and
`P = 1 4 6 7 3` is an induced `C`-path between the non-consecutive vertices `1` and `3`. The
subpaths of `C` between `1` and `3` have interiors `P̊₁ = {2}` and `P̊₂ = {0}`. The two vertices
`5` and `8` are off `C ∪ P`; they form a component of `G - (C ∪ P)` with neighbours `4, 6, 7, 3` on
`P` and none in `P̊₁ ∪ P̊₂`.
* `P` separates `P̊₁` from `P̊₂` (`separates`).
* The sides (`sides`): `1` and `3` are on both sides, `4` only on side 1, `6` and `7` only on
  side 2. So `j = 1` (`y₁ = 1`), `r = 2` (`y₂ = 4`), `s = 3` (`y₃ = 6`), and the edge of the lemma
  is `1 6`.
* `C` is not crossed in `G` (`not_isCrossed`), but it is crossed in `G ⊔ edge 1 6`
  (`isCrossed_sup`), by the paths `1 6 8 3` and `0 7 5 4 2`.
-/

namespace Ex54b

open SimpleGraph

/-- Along a walk to `z` whose vertices other than `z` are `y` or lie outside `X`, a set `S`
closed under the neighbours of such vertices keeps the walk inside, once it starts inside. -/
theorem mem_of_walk_closed {V : Type*} {G : SimpleGraph V} {X S : Set V} {y z : V}
    (hcl : ∀ u ∈ S, (u = y ∨ u ∉ X) → ∀ w, G.Adj u w → w ∈ S) :
    ∀ {u : V} (q : G.Walk u z), u ∈ S → (∀ x ∈ q.support, x ≠ z → x = y ∨ x ∉ X) → z ∈ S := by
  intro u q
  induction q with
  | nil => exact fun h _ => h
  | cons h q ih =>
    rename_i a b c
    intro ha hq
    by_cases hac : a = c
    · exact hac ▸ ha
    · exact ih (hcl a ha (hq a (by simp) hac) b h)
        (fun x hx => hq x (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hx))

/-- If a set `S` contains `y`, misses `A`, and contains every neighbour of `y` and of each of its
vertices outside `X`, then no path from `y` to `A` has all its inner vertices outside `X`. -/
theorem not_isConnectedAvoiding_of_closed {V : Type*} {G : SimpleGraph V} {X A S : Set V} {y : V}
    (hy : y ∈ S) (hA : ∀ z ∈ A, z ∉ S)
    (hcl : ∀ u ∈ S, (u = y ∨ u ∉ X) → ∀ w, G.Adj u w → w ∈ S) :
    ¬ IsConnectedAvoiding G X y A := by
  rintro ⟨z, hz, p, -, hin⟩
  exact hA z hz (mem_of_walk_closed hcl p hy fun x hx hxz => by
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr (hin x hx hxy hxz))

/-- The edges of the example: the cycle `0 1 2 3`, the path `1 4 6 7 3`, and the edges
`06, 07, 24, 38, 45, 57, 58, 68, 78`. -/
def edges : List (Sym2 (Fin 9)) :=
  [s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(1, 4), s(4, 6), s(6, 7), s(7, 3), s(0, 6), s(0, 7),
    s(2, 4), s(3, 8), s(4, 5), s(5, 7), s(5, 8), s(6, 8), s(7, 8)]

/-- The graph of the counterexample. -/
def G : SimpleGraph (Fin 9) where
  Adj u v := s(u, v) ∈ edges
  symm := ⟨fun u v h => by simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨fun u => by revert u; decide⟩

instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable (s(u, v) ∈ edges))

/-- The cycle `C = 0 1 2 3`. -/
def C : List (Fin 9) := [0, 1, 2, 3]

/-- The `C`-path `P = 1 4 6 7 3`. -/
def P : G.Walk 1 3 :=
  .cons (by decide : G.Adj 1 4) <| .cons (by decide : G.Adj 4 6) <|
    .cons (by decide : G.Adj 6 7) <| .cons (by decide : G.Adj 7 3) .nil

/-- `P` is a `C`-path. -/
theorem isTPath_P : IsTPath G C P := by
  refine ⟨by simp [P, Walk.cons_isPath_iff], by decide, by decide, ?_⟩
  intro x hx hx1 hx3
  simp [P, C] at hx ⊢
  omega

/-- `P` is induced: two vertices of `P` are adjacent only when they are consecutive on `P`. -/
theorem induced_P : ∀ a ∈ ({1, 4, 6, 7, 3} : Finset (Fin 9)), ∀ b ∈ ({1, 4, 6, 7, 3} : Finset (Fin 9)),
    G.Adj a b → s(a, b) ∈ [s(1, 4), s(4, 6), s(6, 7), s(7, 3)] := by
  decide

/-- The vertices of `C ∪ P`. -/
def CP : Finset (Fin 9) := {0, 1, 2, 3, 4, 6, 7}

/-- `P` separates `P̊₁ = {2}` from `P̊₂ = {0}`: no path from `2` to `0` avoids `P`. -/
theorem separates :
    ¬ IsConnectedAvoiding G (↑({1, 4, 6, 7, 3} : Finset (Fin 9))) 2 {0} := by
  refine not_isConnectedAvoiding_of_closed (S := ↑({1, 2, 3, 4} : Finset (Fin 9)))
    (by decide) (by simp) ?_
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  decide

/-- The `P`-sides, with `X = C ∪ P`, `P̊₁ = {2}` and `P̊₂ = {0}`: `1` and `3` are on both sides,
`4` only on side 1, `6` and `7` only on side 2. -/
theorem sides :
    (IsOnSide G ↑CP {2} 1 ∧ IsOnSide G ↑CP {0} 1) ∧
    (IsOnSide G ↑CP {2} 4 ∧ ¬ IsOnSide G ↑CP {0} 4) ∧
    (¬ IsOnSide G ↑CP {2} 6 ∧ IsOnSide G ↑CP {0} 6) ∧
    (¬ IsOnSide G ↑CP {2} 7 ∧ IsOnSide G ↑CP {0} 7) ∧
    (IsOnSide G ↑CP {2} 3 ∧ IsOnSide G ↑CP {0} 3) := by
  have edge_side : ∀ {y z : Fin 9}, G.Adj y z → IsOnSide G ↑CP {z} y := fun {y z} h =>
    ⟨z, rfl, .cons h .nil, by simp [Walk.cons_isPath_iff, h.ne], fun x hx h1 h2 => by
      simp at hx; tauto⟩
  have far : ∀ y : Fin 9, y = 6 ∨ y = 7 → ¬ IsOnSide G ↑CP {2} y := by
    intro y hy
    refine not_isConnectedAvoiding_of_closed (S := ↑({0, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)))
      (by rcases hy with rfl | rfl <;> decide) (by simp) ?_
    simp only [CP, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases hy with rfl | rfl <;> decide
  refine ⟨⟨edge_side (by decide), edge_side (by decide)⟩, ⟨edge_side (by decide), ?_⟩,
    ⟨far 6 (by simp), edge_side (by decide)⟩, ⟨far 7 (by simp), edge_side (by decide)⟩,
    ⟨edge_side (by decide), edge_side (by decide)⟩⟩
  refine not_isConnectedAvoiding_of_closed (S := ↑({1, 2, 3, 4, 5, 6, 7, 8} : Finset (Fin 9)))
    (by decide) (by simp) ?_
  simp only [CP, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  decide

/-- `C` is not crossed in `G`. A crossing pairs a path `0 … 2` with a path `1 … 3`; the second
leaves `1` through `4`, its only neighbour off `C`, and the first enters `2` through `4` for the
same reason. -/
theorem not_isCrossed : ¬ IsCrossed G C := by
  rw [C, isCrossed_iff_linkage]
  rintro ⟨P₁, P₂, -, -, hdisj⟩
  have nb1 : ∀ w, G.Adj 1 w → w = 0 ∨ w = 2 ∨ w = 4 := by decide
  have nb2 : ∀ w, G.Adj 2 w → w = 1 ∨ w = 3 ∨ w = 4 := by decide
  have h4₂ : (4 : Fin 9) ∈ P₂.support := by
    cases P₂ with
    | cons h q =>
      rename_i w
      rcases nb1 w h with rfl | rfl | rfl
      · exact absurd q.start_mem_support (fun hq => hdisj P₁.start_mem_support (by simp [hq]))
      · exact absurd q.start_mem_support (fun hq => hdisj P₁.end_mem_support (by simp [hq]))
      · simp
  have h4₁ : (4 : Fin 9) ∈ P₁.support := by
    have hsub : ∀ x ∈ P₁.reverse.support, x ∈ P₁.support := fun x hx => by
      simpa [Walk.support_reverse] using hx
    apply hsub
    generalize P₁.reverse = R at hsub
    cases R with
    | cons h q =>
      rename_i w
      rcases nb2 w h with rfl | rfl | rfl
      · exact absurd (hsub _ (by simp)) (fun h1 => hdisj h1 P₂.start_mem_support)
      · exact absurd (hsub _ (by simp)) (fun h1 => hdisj h1 P₂.end_mem_support)
      · simp
  exact hdisj h4₁ h4₂

/-- `C` is crossed in `G` plus the edge `1 6`: the paths `0 7 5 4 2` and `1 6 8 3` cross it. -/
theorem isCrossed_sup : IsCrossed (G ⊔ edge 1 6) C := by
  rw [C, isCrossed_iff_linkage]
  have a07 : (G ⊔ edge 1 6).Adj 0 7 := Or.inl (by decide)
  have a75 : (G ⊔ edge 1 6).Adj 7 5 := Or.inl (by decide)
  have a54 : (G ⊔ edge 1 6).Adj 5 4 := Or.inl (by decide)
  have a42 : (G ⊔ edge 1 6).Adj 4 2 := Or.inl (by decide)
  have a16 : (G ⊔ edge 1 6).Adj 1 6 := Or.inr (by simp [edge_adj])
  have a68 : (G ⊔ edge 1 6).Adj 6 8 := Or.inl (by decide)
  have a83 : (G ⊔ edge 1 6).Adj 8 3 := Or.inl (by decide)
  refine ⟨.cons a07 (.cons a75 (.cons a54 (.cons a42 .nil))),
    .cons a16 (.cons a68 (.cons a83 .nil)), ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

/-- The edge `1 6` of Lemma 5.4 is not safe for `C` in `G`, although `P` is induced. -/
theorem lemma_5_4_counterexample :
    ¬ G.Adj 1 6 ∧ IsCrossed (G ⊔ edge 1 6) C ∧ ¬ IsCrossed G C :=
  ⟨by decide, isCrossed_sup, not_isCrossed⟩

end Ex54b

/-!
# The two extraction rules can both fail on an edge of the loop of Algorithm 5.2

A first attempt at the correction of Section 5.3 undoes an added edge `y u` of `H + y u` as follows.
Given a crossing `(Q, R)` of `C` in `H + y u` with `y u` on `Q`, *rule 1* keeps `R` and looks in
`H - R` for a path between the two arcs of `C` cut by the ends of `R`. *Rule 2* replaces `y u` in
`Q` by the part of `P` it skips, giving `Q'`, and looks in `H - Q'` for a path between the two arcs
cut by the ends of `Q'`. The graph `G` below shows that both can fail, for the very edge that the
loop of Algorithm 5.2 (page 23) adds first.

`G` has eleven vertices. `C = 0 1 2 3` is a 4-cycle and `P = 1 4 5 6 7 3` is a `C`-path between the
non-consecutive vertices `1` and `3`, with arc interiors `{2}` and `{0}`.
* `P` is induced (`induced_P`) and separates `{2}` from `{0}` (`separates`).
* The vertices off `C ∪ P` are `8, 9, 10`, and each is joined to `2` away from `C ∪ P`
  (`joined_off`), so no component of `G - (C ∪ P)` misses both arcs and `P` is tight.
* The sides (`sides`): `1, 4, 5, 3` are on both sides, `6` and `7` only on the side of `2`.
  So the loop starts at `y = 5`, the end of the prefix on both sides, and adds the edge `5 3`.
* `(0 4 8 6 7 2, 1 10 9 5 3)` is a crossing of `C` in `G ⊔ edge 5 3`, and the second path uses
  the new edge (`isCrossed_sup`).
* Rule 1 fails: every path from `1` to `3` meets `0 4 8 6 7 2` (`rule_one_fails`).
* Rule 2 fails: `Q' = 1 10 9 5 6 7 3`, and every path from `2` to `0` meets it
  (`rule_two_fails`).
* `C` is crossed in `G` (`isCrossed`), by `0 5 6 7 2` and `1 10 8 3`, so the edge is safe, as the
  strip lemma says, but neither rule finds a crossing of `G` from the given one.
-/

namespace ExR

open SimpleGraph

/-- A walk from a vertex of a set `S` to a vertex outside `S` meets `X`, if every neighbour of a
vertex of `S` outside `X` is in `S` or in `X`. -/
theorem meets_of_closed {V : Type*} {G : SimpleGraph V} {X S : Set V}
    (hcl : ∀ v ∈ S, v ∉ X → ∀ w, G.Adj v w → w ∈ S ∨ w ∈ X) :
    ∀ {u z : V} (p : G.Walk u z), u ∈ S → z ∉ S → ∃ x ∈ p.support, x ∈ X := by
  intro u z p
  induction p with
  | nil => exact fun hu hz => absurd hu hz
  | cons h q ih =>
    rename_i a b c
    intro ha hc
    by_cases hX : a ∈ X
    · exact ⟨a, by simp, hX⟩
    · rcases hcl a ha hX b h with hb | hb
      · obtain ⟨x, hx, hxX⟩ := ih hb hc
        exact ⟨x, by simp [hx], hxX⟩
      · exact ⟨b, by simp, hb⟩

/-- The edges of the example: the cycle `0 1 2 3`, the path `1 4 5 6 7 3`, and the edges
`04, 05, 1 10, 27, 29, 2 10, 38, 48, 59, 68, 6 10, 8 10, 9 10`. -/
def edges : List (Sym2 (Fin 11)) :=
  [s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(1, 4), s(4, 5), s(5, 6), s(6, 7), s(7, 3), s(0, 4),
    s(0, 5), s(1, 10), s(2, 7), s(2, 9), s(2, 10), s(3, 8), s(4, 8), s(5, 9), s(6, 8), s(6, 10),
    s(8, 10), s(9, 10)]

/-- The graph of the example. -/
def G : SimpleGraph (Fin 11) where
  Adj u v := s(u, v) ∈ edges
  symm := ⟨fun u v h => by simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨fun u => by revert u; decide⟩

instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable (s(u, v) ∈ edges))

/-- The cycle `C = 0 1 2 3`. -/
def C : List (Fin 11) := [0, 1, 2, 3]

/-- `P = 1 4 5 6 7 3` is induced: two of its vertices are adjacent only when consecutive on it. -/
theorem induced_P : ∀ a ∈ ({1, 4, 5, 6, 7, 3} : Finset (Fin 11)),
    ∀ b ∈ ({1, 4, 5, 6, 7, 3} : Finset (Fin 11)),
    G.Adj a b → s(a, b) ∈ [s(1, 4), s(4, 5), s(5, 6), s(6, 7), s(7, 3)] := by
  decide

/-- `P` separates `{2}` from `{0}`: no path from `2` to `0` avoids `P`. -/
theorem separates (p : G.Walk 2 0) : ∃ x ∈ p.support, x ∈ ({1, 4, 5, 6, 7, 3} : Finset (Fin 11)) :=
  meets_of_closed (S := ↑({2, 8, 9, 10} : Finset (Fin 11))) (fun v hv hX w h => by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv hX ⊢
    revert w; revert hX; rcases hv with rfl | rfl | rfl | rfl <;> decide) p (by simp) (by simp)

/-- The vertices of `C ∪ P`. -/
def CP : Finset (Fin 11) := {0, 1, 2, 3, 4, 5, 6, 7}

/-- Each vertex off `C ∪ P` is joined to `2` by a path with no inner vertex in `C ∪ P`. -/
theorem joined_off : ∀ u : Fin 11, u ∉ CP → IsConnectedAvoiding G ↑CP u {2} := by
  have a82 : G.Adj 8 10 := by decide
  have a102 : G.Adj 10 2 := by decide
  have a92 : G.Adj 9 2 := by decide
  intro u hu
  have : u = 8 ∨ u = 9 ∨ u = 10 := by revert u; decide
  rcases this with rfl | rfl | rfl
  · exact ⟨2, rfl, .cons a82 (.cons a102 .nil), by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl <;> simp_all [CP]⟩
  · exact ⟨2, rfl, .cons a92 .nil, by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl <;> simp_all⟩
  · exact ⟨2, rfl, .cons a102 .nil, by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl <;> simp_all⟩

/-- The `P`-sides, with `X = C ∪ P` and arc interiors `{2}` and `{0}`: `1, 4, 5, 3` are on both
sides, `6` and `7` only on the side of `2`. -/
theorem sides :
    (∀ y ∈ ({1, 4, 5, 3} : Finset (Fin 11)), IsOnSide G ↑CP {2} y ∧ IsOnSide G ↑CP {0} y) ∧
    (∀ y ∈ ({6, 7} : Finset (Fin 11)), IsOnSide G ↑CP {2} y ∧ ¬ IsOnSide G ↑CP {0} y) := by
  have edge_side : ∀ {y z : Fin 11}, G.Adj y z → IsOnSide G ↑CP {z} y := fun {y z} h =>
    ⟨z, rfl, .cons h .nil, by simp [Walk.cons_isPath_iff, h.ne], fun x hx h1 h2 => by
      simp at hx; tauto⟩
  have s4 : IsOnSide G ↑CP {2} 4 :=
    ⟨2, rfl, .cons (by decide : G.Adj 4 8) (.cons (by decide : G.Adj 8 10)
      (.cons (by decide : G.Adj 10 2) .nil)), by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp_all [CP]⟩
  have s5 : IsOnSide G ↑CP {2} 5 :=
    ⟨2, rfl, .cons (by decide : G.Adj 5 9) (.cons (by decide : G.Adj 9 2) .nil),
      by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl <;> simp_all [CP]⟩
  have s6 : IsOnSide G ↑CP {2} 6 :=
    ⟨2, rfl, .cons (by decide : G.Adj 6 10) (.cons (by decide : G.Adj 10 2) .nil),
      by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl <;> simp_all [CP]⟩
  have far : ∀ y : Fin 11, y = 6 ∨ y = 7 → ¬ IsOnSide G ↑CP {0} y := by
    intro y hy
    refine Ex54b.not_isConnectedAvoiding_of_closed
      (S := ↑({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset (Fin 11)))
      (by rcases hy with rfl | rfl <;> decide) (by simp) ?_
    simp only [CP, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases hy with rfl | rfl <;> decide
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨edge_side (by decide), edge_side (by decide)⟩
    · exact ⟨s4, edge_side (by decide)⟩
    · exact ⟨s5, edge_side (by decide)⟩
    · exact ⟨edge_side (by decide), edge_side (by decide)⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ⟨s6, far 6 (by simp)⟩
    · exact ⟨edge_side (by decide), far 7 (by simp)⟩

/-- `5` and `3` are not adjacent in `G`. -/
theorem not_adj : ¬ G.Adj 5 3 := by decide

/-- `C` is crossed in `G ⊔ edge 5 3`, by `0 4 8 6 7 2` and `1 10 9 5 3`; the second path uses the
new edge. -/
theorem isCrossed_sup : IsCrossed (G ⊔ edge 5 3) C := by
  rw [C, isCrossed_iff_linkage]
  have h : ∀ {u v : Fin 11}, G.Adj u v → (G ⊔ edge 5 3).Adj u v := fun h => Or.inl h
  have a53 : (G ⊔ edge 5 3).Adj 5 3 := Or.inr (by simp [edge_adj])
  refine ⟨.cons (h (by decide : G.Adj 0 4)) (.cons (h (by decide : G.Adj 4 8))
      (.cons (h (by decide : G.Adj 8 6)) (.cons (h (by decide : G.Adj 6 7))
      (.cons (h (by decide : G.Adj 7 2)) .nil)))),
    .cons (h (by decide : G.Adj 1 10)) (.cons (h (by decide : G.Adj 10 9))
      (.cons (h (by decide : G.Adj 9 5)) (.cons a53 .nil))), ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

/-- Rule 1 fails: the ends `0, 2` of `R = 0 4 8 6 7 2` cut `C` into the arcs `{1}` and `{3}`, and
every path of `G` from `1` to `3` meets `R`. -/
theorem rule_one_fails (p : G.Walk 1 3) :
    ∃ x ∈ p.support, x ∈ ({0, 4, 8, 6, 7, 2} : Finset (Fin 11)) :=
  meets_of_closed (S := ↑({1, 5, 9, 10} : Finset (Fin 11))) (fun v hv hX w h => by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv hX ⊢
    revert w; revert hX; rcases hv with rfl | rfl | rfl | rfl <;> decide) p (by simp) (by simp)

/-- Rule 2 fails: `Q' = 1 10 9 5 6 7 3` replaces the edge `5 3` by the part `5 6 7 3` of `P`; its
ends `1, 3` cut `C` into the arcs `{2}` and `{0}`, and every path of `G` from `2` to `0` meets
`Q'`. -/
theorem rule_two_fails (p : G.Walk 2 0) :
    ∃ x ∈ p.support, x ∈ ({1, 10, 9, 5, 6, 7, 3} : Finset (Fin 11)) :=
  meets_of_closed (S := ↑({2} : Finset (Fin 11))) (fun v hv hX w h => by
    simp only [Finset.coe_singleton, Set.mem_singleton_iff, Finset.coe_insert,
      Set.mem_insert_iff] at hv hX ⊢
    subst hv; revert w; revert hX; decide) p (by simp) (by simp)

/-- `C` is crossed in `G`, by `0 5 6 7 2` and `1 10 8 3`. -/
theorem isCrossed : IsCrossed G C := by
  rw [C, isCrossed_iff_linkage]
  refine ⟨.cons (by decide : G.Adj 0 5) (.cons (by decide : G.Adj 5 6)
      (.cons (by decide : G.Adj 6 7) (.cons (by decide : G.Adj 7 2) .nil))),
    .cons (by decide : G.Adj 1 10) (.cons (by decide : G.Adj 10 8)
      (.cons (by decide : G.Adj 8 3) .nil)), ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

/-- Rule 3 succeeds: `R = 0 4 8 6 7 2` contains the bridge `6 8 4` from `6` in the pocket `{6, 7}`
to `4` on the prefix `1 4` of `P = 1 4 5 6 7 3`, with `8` off `C ∪ P`. Rerouting `P` along `4 8 6`
gives `P_new = 1 4 8 6 7 3`, which bypasses `y = 5`, and `0 5 9 2` is a `C`-path of `G - P_new`
that crosses `P_new`. -/
theorem rule_three_succeeds :
    ∃ (Z : G.Walk 0 2) (P_new : G.Walk 1 3),
      Z.support = [0, 5, 9, 2] ∧ P_new.support = [1, 4, 8, 6, 7, 3] ∧
      Z.IsPath ∧ P_new.IsPath ∧ Z.support.Disjoint P_new.support := by
  refine ⟨.cons (by decide : G.Adj 0 5) (.cons (by decide : G.Adj 5 9)
      (.cons (by decide : G.Adj 9 2) .nil)),
    .cons (by decide : G.Adj 1 4) (.cons (by decide : G.Adj 4 8)
      (.cons (by decide : G.Adj 8 6) (.cons (by decide : G.Adj 6 7)
      (.cons (by decide : G.Adj 7 3) .nil)))), rfl, rfl, ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

end ExR

/-! ## 5. A counterexample `ExR3` where Rules 1, 2, and 3 all fail, and Rule 4 succeeds

When both ends `y` and `u` of the added edge are internal vertices of `P`, the bridge `σ :: t :: K ++ [z]`
from `σ ∈ N` to `z ∈ L₁` gives a rerouted path `P_new` that bypasses `y` (putting `y` and `Q₁` in the
`B`-component of `G - P_new`) while keeping `u ∈ P_new.support`. If the side-`A` path from the bridge
vertex `t` reaches `A` through an internal vertex of `Q₂` (on the `u`-side of `Q`) rather than `Q₁`,
`u ∈ P_new.support` blocks `Q₂` from reaching `y` or `B`, so `P_new` still separates `A` from `B` and
Rule 3 fails.

In that case, however, the bridge `z :: K.reverse ++ [t]`, the path from `t` to `Q₂`, and `Q₂` form a
`C`-path from `a` to the `C`-endpoint of `Q₂` that completely avoids `y`, `y`'s side-`B` path, `P[y..σ]`,
and the `A`-side of `R` from `σ`. Thus **Rule 4** extracts a crossing of `C` in `G`: it splices
`y`'s side-`B` path with `P[y..σ]` and the `A`-side of `R` from `σ` to form `R_new`, and searches
`G - R_new`.

The smallest such graph, as it stands after the rerouting stage and the collapse stage of the
completion, has 11 vertices and 22 edges (`C = 0 1 2 3`,
`P = 1 4 5 6 7 3`, added edge `5 7` with pocket `N = [6]`, `Q = 1 9 5 7 10 3`, `R = 0 4 8 6 2`). -/

namespace ExR3

open SimpleGraph

/-- The 22 edges of `ExR3`: the cycle `0 1 2 3`, the path `1 4 5 6 7 3`, and the 13 edges
`04, 07, 09, 19, 59, 48, 58, 68, 8 10, 26, 2 10, 3 10, 7 10`. -/
def edges : List (Sym2 (Fin 11)) :=
  [s(0, 1), s(1, 2), s(2, 3), s(3, 0), s(1, 4), s(4, 5), s(5, 6), s(6, 7), s(7, 3),
    s(0, 4), s(0, 7), s(0, 9), s(1, 9), s(5, 9), s(4, 8), s(5, 8), s(6, 8), s(8, 10), s(2, 6),
    s(2, 10), s(3, 10), s(7, 10)]

/-- The graph of `ExR3`. -/
def G : SimpleGraph (Fin 11) where
  Adj u v := s(u, v) ∈ edges
  symm := ⟨fun u v h => by simpa only [Sym2.eq_swap] using h⟩
  loopless := ⟨fun u => by revert u; decide⟩

instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable (s(u, v) ∈ edges))

/-- The cycle `C = 0 1 2 3`. -/
def C : List (Fin 11) := [0, 1, 2, 3]

/-- `P = 1 4 5 6 7 3` is induced: two of its vertices are adjacent only when consecutive on it. -/
theorem induced_P : ∀ a ∈ ({1, 4, 5, 6, 7, 3} : Finset (Fin 11)),
    ∀ b ∈ ({1, 4, 5, 6, 7, 3} : Finset (Fin 11)),
    G.Adj a b → s(a, b) ∈ [s(1, 4), s(4, 5), s(5, 6), s(6, 7), s(7, 3)] := by
  decide

/-- `P` separates `{2}` from `{0}`: no path from `2` to `0` avoids `P`. -/
theorem separates (p : G.Walk 2 0) :
    ∃ x ∈ p.support, x ∈ ({1, 4, 5, 6, 7, 3} : Finset (Fin 11)) :=
  ExR.meets_of_closed (S := ↑({2, 8, 10} : Finset (Fin 11))) (fun v hv hX w h => by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv hX ⊢
    revert w; revert hX; rcases hv with rfl | rfl | rfl <;> decide) p (by simp) (by simp)

/-- The vertices of `C ∪ P`. -/
def CP : Finset (Fin 11) := {0, 1, 2, 3, 4, 5, 6, 7}

/-- Each vertex off `C ∪ P` is joined to `{2, 0}` by a path with no inner vertex in `C ∪ P`
(`8` and `10` to `2`, `9` to `0`), so `G - (C ∪ P)` has no component of the third kind and `P` is
tight. -/
theorem joined_off : ∀ u : Fin 11, u ∉ CP → IsConnectedAvoiding G ↑CP u {2, 0} := by
  have a810 : G.Adj 8 10 := by decide
  have a102 : G.Adj 10 2 := by decide
  have a90 : G.Adj 9 0 := by decide
  intro u hu
  have : u = 8 ∨ u = 9 ∨ u = 10 := by revert u; decide
  rcases this with rfl | rfl | rfl
  · exact ⟨2, by simp, .cons a810 (.cons a102 .nil), by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl <;> simp_all [CP]⟩
  · exact ⟨0, by simp, .cons a90 .nil, by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl <;> simp_all⟩
  · exact ⟨2, by simp, .cons a102 .nil, by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl <;> simp_all⟩

/-- The `P`-sides, with `X = C ∪ P` and arc interiors `{2}` and `{0}`: `1, 4, 5, 7, 3` are on both
sides, while `6` is only on the side of `2`. Thus the rerouting stage and the collapse stage of the
completion do nothing, and the loop of Algorithm 5.2
adds `5 7` across the pocket `N = [6]`. -/
theorem sides :
    (∀ y ∈ ({1, 4, 5, 7, 3} : Finset (Fin 11)), IsOnSide G ↑CP {2} y ∧ IsOnSide G ↑CP {0} y) ∧
    (IsOnSide G ↑CP {2} 6 ∧ ¬ IsOnSide G ↑CP {0} 6) := by
  have edge_side : ∀ {y z : Fin 11}, G.Adj y z → IsOnSide G ↑CP {z} y := fun {y z} h =>
    ⟨z, rfl, .cons h .nil, by simp [Walk.cons_isPath_iff, h.ne], fun x hx h1 h2 => by
      simp at hx; tauto⟩
  have s4A : IsOnSide G ↑CP {2} 4 :=
    ⟨2, rfl, .cons (by decide : G.Adj 4 8) (.cons (by decide : G.Adj 8 10)
      (.cons (by decide : G.Adj 10 2) .nil)), by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp_all [CP]⟩
  have s5A : IsOnSide G ↑CP {2} 5 :=
    ⟨2, rfl, .cons (by decide : G.Adj 5 8) (.cons (by decide : G.Adj 8 10)
      (.cons (by decide : G.Adj 10 2) .nil)), by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> simp_all [CP]⟩
  have s5B : IsOnSide G ↑CP {0} 5 :=
    ⟨0, rfl, .cons (by decide : G.Adj 5 9) (.cons (by decide : G.Adj 9 0) .nil),
      by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl <;> simp_all [CP]⟩
  have s7A : IsOnSide G ↑CP {2} 7 :=
    ⟨2, rfl, .cons (by decide : G.Adj 7 10) (.cons (by decide : G.Adj 10 2) .nil),
      by simp [Walk.cons_isPath_iff],
      fun x hx h1 h2 => by simp at hx; rcases hx with rfl | rfl | rfl <;> simp_all [CP]⟩
  have far6 : ¬ IsOnSide G ↑CP {0} 6 := by
    refine Ex54b.not_isConnectedAvoiding_of_closed
      (S := ↑({1, 2, 3, 4, 5, 6, 7, 8, 10} : Finset (Fin 11)))
      (by decide) (by simp) ?_
    simp only [CP, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    decide
  refine ⟨fun y hy => ?_, ⟨edge_side (by decide), far6⟩⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact ⟨edge_side (by decide), edge_side (by decide)⟩
  · exact ⟨s4A, edge_side (by decide)⟩
  · exact ⟨s5A, s5B⟩
  · exact ⟨s7A, edge_side (by decide)⟩
  · exact ⟨edge_side (by decide), edge_side (by decide)⟩

/-- `5` and `7` are not adjacent in `G`. -/
theorem not_adj : ¬ G.Adj 5 7 := by decide

/-- `C` is crossed in `G ⊔ edge 5 7`, by `0 4 8 6 2` and `1 9 5 7 10 3`; the second path uses the
new edge `5 7`. -/
theorem isCrossed_sup : IsCrossed (G ⊔ edge 5 7) C := by
  rw [C, isCrossed_iff_linkage]
  have h : ∀ {u v : Fin 11}, G.Adj u v → (G ⊔ edge 5 7).Adj u v := fun h => Or.inl h
  have a57 : (G ⊔ edge 5 7).Adj 5 7 := Or.inr (by simp [edge_adj])
  refine ⟨.cons (h (by decide : G.Adj 0 4)) (.cons (h (by decide : G.Adj 4 8))
      (.cons (h (by decide : G.Adj 8 6)) (.cons (h (by decide : G.Adj 6 2)) .nil))),
    .cons (h (by decide : G.Adj 1 9)) (.cons (h (by decide : G.Adj 9 5))
      (.cons a57 (.cons (h (by decide : G.Adj 7 10))
      (.cons (h (by decide : G.Adj 10 3)) .nil)))), ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

/-- Rule 1 fails: the ends `0, 2` of `R = 0 4 8 6 2` cut `C` into `{1}` and `{3}`, and every path of
`G` from `1` to `3` meets `R`. -/
theorem rule_one_fails (p : G.Walk 1 3) :
    ∃ x ∈ p.support, x ∈ ({0, 4, 8, 6, 2} : Finset (Fin 11)) :=
  ExR.meets_of_closed (S := ↑({1, 5, 9} : Finset (Fin 11))) (fun v hv hX w h => by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv hX ⊢
    revert w; revert hX; rcases hv with rfl | rfl | rfl <;> decide) p (by simp) (by simp)

/-- Rule 2 fails: `Q' = 1 9 5 6 7 10 3` replaces the edge `5 7` by `5 6 7` on `P`; its ends `1, 3`
cut `C` into `{2}` and `{0}`, and every path of `G` from `2` to `0` meets `Q'`. -/
theorem rule_two_fails (p : G.Walk 2 0) :
    ∃ x ∈ p.support, x ∈ ({1, 9, 5, 6, 7, 10, 3} : Finset (Fin 11)) :=
  ExR.meets_of_closed (S := ↑({2} : Finset (Fin 11))) (fun v hv hX w h => by
    simp only [Finset.coe_singleton, Set.mem_singleton_iff, Finset.coe_insert,
      Set.mem_insert_iff] at hv hX ⊢
    subst hv; revert w; revert hX; decide) p (by simp) (by simp)

/-- Rule 3 fails: `R = 0 4 8 6 2` has the unique pocket-to-prefix/suffix bridge `6 8 4` from `6` in
`N = [6]` to `4` in `L₁ = [1, 4]` (with `8` off `C ∪ P`). Rerouting `P = 1 4 5 6 7 3` along `4 8 6`
gives `P_new = 1 4 8 6 7 3`, and every path of `G` from `2` to `0` still meets `P_new` (since `2`
and `10` only have neighbours in `{2, 10} ∪ {1, 3, 6, 7, 8} ⊆ {2, 10} ∪ P_new.support`). -/
theorem rule_three_fails (p : G.Walk 2 0) :
    ∃ x ∈ p.support, x ∈ ({1, 4, 8, 6, 7, 3} : Finset (Fin 11)) :=
  ExR.meets_of_closed (S := ↑({2, 10} : Finset (Fin 11))) (fun v hv hX w h => by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv hX ⊢
    revert w; revert hX; rcases hv with rfl | rfl <;> decide) p (by simp) (by simp)

/-- `C` is crossed in `G`, by `0 9 5 6 2` and `1 4 8 10 3`. -/
theorem isCrossed : IsCrossed G C := by
  rw [C, isCrossed_iff_linkage]
  refine ⟨.cons (by decide : G.Adj 0 9) (.cons (by decide : G.Adj 9 5)
      (.cons (by decide : G.Adj 5 6) (.cons (by decide : G.Adj 6 2) .nil))),
    .cons (by decide : G.Adj 1 4) (.cons (by decide : G.Adj 4 8)
      (.cons (by decide : G.Adj 8 10) (.cons (by decide : G.Adj 10 3) .nil))), ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

/-- Rule 4 succeeds: splicing `y = 5`'s side-`{0}` path `5 9 0` with `P[5..6] = 5 6` and the
`{2}`-side `6 2` of `R` from `σ = 6 ∈ N` gives the `C`-path `R_new = 0 9 5 6 2`, and `1 4 8 10 3`
is a `C`-path of `G - R_new` that crosses `R_new`. -/
theorem rule_four_succeeds :
    ∃ (R_new : G.Walk 0 2) (Z : G.Walk 1 3),
      R_new.support = [0, 9, 5, 6, 2] ∧ Z.support = [1, 4, 8, 10, 3] ∧
      R_new.IsPath ∧ Z.IsPath ∧ R_new.support.Disjoint Z.support := by
  refine ⟨.cons (by decide : G.Adj 0 9) (.cons (by decide : G.Adj 9 5)
      (.cons (by decide : G.Adj 5 6) (.cons (by decide : G.Adj 6 2) .nil))),
    .cons (by decide : G.Adj 1 4) (.cons (by decide : G.Adj 4 8)
      (.cons (by decide : G.Adj 8 10) (.cons (by decide : G.Adj 10 3) .nil))),
    rfl, rfl, ?_, ?_, ?_⟩
  · simp [Walk.cons_isPath_iff]
  · simp [Walk.cons_isPath_iff]
  · simp

end ExR3

end GraphMinor.HP25
