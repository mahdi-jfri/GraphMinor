module

public import GraphMinor.GM13.Section7RealizeMove
public import GraphMinor.GM13.Section7HoleConn
public import GraphMinor.GM13.Section7HoleDepth

/-!
# Graph Minors XIII, (7.3): the realization of the hole

This file gives a realization (`Shape.Realization`) of the hole `Hole(Y0, c0)` of
`Section7Hole.lean`, so that the hole gives a wall of height `h'` inside any wall of height
`h' + 2`, for (7.3) of Graph Minors XIII (page 90).

The old vertex of a new vertex `p` (`Hole.vmap`) is `p` itself left of column `c0` below row
`Y0`, `p + (4, 0)` from column `c0` on below row `Y0`, and `p + (2, 2)` from row `Y0` on. The old
path of a new edge (`Hole.inner`) is one old edge, except for two kinds of edges:
* the edge from `(c0 - 1, y)` to `(c0, y)` below row `Y0` runs along its row over the four removed
  columns;
* an edge from `(x, Y0 - 1)` to `(x, Y0)` becomes a staircase through the two band rows `Y0` and
  `Y0 + 1`: up, one step sideways (right if `x < c0`, left otherwise), up, one more step sideways,
  and up.

Each piece of these paths is checked against `Hole.own` (`chain_horiz`, `chain_vert`,
`own_inner_horiz`, `own_inner_vert`), and every kept element is found on them (`Hole.covered`).
A general constructor `Shape.Realization.ofOriented` lets us give the paths in one direction only.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-- In a list where each element is in relation with the next, so are the two parts of each pair
of the list with its tail. -/
theorem List.rel_of_mem_zip_of_isChain {γ : Type*} {S : γ → γ → Prop} :
    ∀ {a : γ} {l : List γ}, List.IsChain S (a :: l) → ∀ uw ∈ (a :: l).zip l, S uw.1 uw.2
  | _, [], _, uw, huw => by simp at huw
  | a, b :: l, hc, uw, huw => by
    rw [List.zip_cons_cons, List.mem_cons] at huw
    rcases huw with rfl | huw
    · exact (List.isChain_cons_cons.mp hc).1
    · exact List.rel_of_mem_zip_of_isChain (List.isChain_cons_cons.mp hc).2 uw huw

namespace Shape

variable {h h' : ℕ} {τ : Shape h h'}

/-- A realization from its data on one direction of each edge. For an edge `pq` in the direction
`O`, the old path must go from `vmap p` to `vmap q` along edges whose cells go to the cell of
`pq`; the paths of the other direction are the reversed paths. -/
def Realization.ofOriented (O : ℕ × ℕ → ℕ × ℕ → Prop) (vmap : ℕ × ℕ → ℕ × ℕ)
    (inner : ℕ × ℕ → ℕ × ℕ → List (ℕ × ℕ))
    (hO : ∀ p q, elementaryWallAdj h' p q → O p q ∨ O q p)
    (hOadj : ∀ p q, O p q → elementaryWallAdj h' p q)
    (vmap_mem : ∀ p ∈ elementaryWallVerts h', vmap p ∈ elementaryWallVerts h)
    (inner_symm : ∀ p q, elementaryWallAdj h' p q → inner q p = (inner p q).reverse)
    (chain : ∀ p q, O p q → List.IsChain
      (fun u w => elementaryWallAdj h u w ∧ τ.own (eCell u w) = some (eCell p q))
      (vmap p :: (inner p q ++ [vmap q])))
    (nodup : ∀ p q, O p q → (vmap p :: (inner p q ++ [vmap q])).Nodup)
    (own_vmap : ∀ p ∈ elementaryWallVerts h', τ.own (vCell (vmap p)) = some (vCell p))
    (own_inner : ∀ p q, O p q → ∀ u ∈ inner p q, τ.own (vCell u) = some (eCell p q))
    (own_cover : ∀ m ∈ fig1WallCells h, τ.own m ≠ none →
      (∃ p ∈ elementaryWallVerts h', m = vCell (vmap p)) ∨
      ∃ p q, elementaryWallAdj h' p q ∧ ((∃ u ∈ inner p q, m = vCell u) ∨
        ∃ uw ∈ (vmap p :: (inner p q ++ [vmap q])).zip (inner p q ++ [vmap q]),
          m = eCell uw.1 uw.2)) :
    τ.Realization :=
  have rev : ∀ p q, elementaryWallAdj h' p q → vmap p :: (inner p q ++ [vmap q]) =
      (vmap q :: (inner q p ++ [vmap p])).reverse := fun p q hpq => by
    rw [inner_symm p q hpq]; simp
  have chain' : ∀ p q, elementaryWallAdj h' p q → List.IsChain
      (fun u w => elementaryWallAdj h u w ∧ τ.own (eCell u w) = some (eCell p q))
      (vmap p :: (inner p q ++ [vmap q])) := fun p q hpq => by
    rcases hO p q hpq with hpq' | hqp
    · exact chain p q hpq'
    · rw [rev p q hpq, List.isChain_reverse]
      refine (chain q p hqp).imp fun u w huw => ⟨elementaryWallAdj_symm huw.1, ?_⟩
      rw [eCell_comm, huw.2, eCell_comm]
  { vmap := vmap
    inner := inner
    vmap_mem := vmap_mem
    inner_symm := inner_symm
    chain := fun p q hpq => (chain' p q hpq).imp fun _ _ h => h.1
    nodup := fun p q hpq => by
      rcases hO p q hpq with hpq' | hqp
      · exact nodup p q hpq'
      · rw [rev p q hpq]; exact List.nodup_reverse.mpr (nodup q p hqp)
    own_vmap := own_vmap
    own_inner := fun p q hpq u hu => by
      rcases hO p q hpq with hpq' | hqp
      · exact own_inner p q hpq' u hu
      · rw [inner_symm q p (hOadj q p hqp), List.mem_reverse] at hu
        rw [own_inner q p hqp u hu, eCell_comm]
    own_step := fun p q hpq uw huw => (List.rel_of_mem_zip_of_isChain (chain' p q hpq) uw huw).2
    own_cover := own_cover }

end Shape

namespace Hole

variable {h' : ℕ} {Y0 c0 : ℤ}

/-- The old vertex of the new vertex `p`: the same vertex left of column `c0` below row `Y0`, the
vertex four steps right from column `c0` on below row `Y0`, and the vertex moved by `(2, 2)` from
row `Y0` on. -/
def vmap (Y0 c0 : ℤ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if (p.2 : ℤ) < Y0 then (if (p.1 : ℤ) < c0 then p else (p.1 + 4, p.2)) else (p.1 + 2, p.2 + 2)

/-- The inner vertices of the old path of a new edge `pq` that goes right or up. The edge from
column `c0 - 1` to `c0` below row `Y0` runs over the four removed columns. An edge from row
`Y0 - 1` to row `Y0` becomes a staircase through the two band rows. All other paths are single
edges. -/
def innerO (Y0 c0 : ℤ) (p q : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.2 = q.2 then
    (if (p.2 : ℤ) < Y0 ∧ (q.1 : ℤ) = c0 then
      [(q.1, p.2), (q.1 + 1, p.2), (q.1 + 2, p.2), (q.1 + 3, p.2)] else [])
  else if (q.2 : ℤ) = Y0 then
    (if (p.1 : ℤ) < c0 then [(p.1, q.2), (p.1 + 1, q.2), (p.1 + 1, q.2 + 1), (p.1 + 2, q.2 + 1)]
      else [(p.1 + 4, q.2), (p.1 + 3, q.2), (p.1 + 3, q.2 + 1), (p.1 + 2, q.2 + 1)])
  else []

/-- The inner vertices of the old path of the new edge `pq`, in both directions. -/
def inner (Y0 c0 : ℤ) (p q : ℕ × ℕ) : List (ℕ × ℕ) :=
  if p.1 + p.2 < q.1 + q.2 then innerO Y0 c0 p q else (innerO Y0 c0 q p).reverse

theorem own_eq_eCell (he' : Even h') {m : ℤ × ℤ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q)
    (hc : cell Y0 c0 m = eCell p q) : own h' Y0 c0 m = some (eCell p q) := by
  unfold own
  rw [hc]
  simp only [isWallCell_eCell he' hpq, ↓reduceIte]

theorem own_eq_vCell {m : ℤ × ℤ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h')
    (hc : cell Y0 c0 m = vCell p) : own h' Y0 c0 m = some (vCell p) := by
  unfold own
  rw [hc]
  simp only [isWallCell_vCell hp, ↓reduceIte]

theorem cell_vCell (u : ℕ × ℕ) : cell Y0 c0 (vCell u) = vertexCell Y0 c0 u.1 u.2 :=
  cell_vertex _ _ _ _

theorem cell_eCell_h {u w : ℕ × ℕ} (h1 : w.1 = u.1 + 1) (h2 : w.2 = u.2) :
    cell Y0 c0 (eCell u w) = horizCell Y0 c0 u.1 u.2 := by
  rw [← cell_horiz]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

theorem cell_eCell_h' {u w : ℕ × ℕ} (h1 : u.1 = w.1 + 1) (h2 : w.2 = u.2) :
    cell Y0 c0 (eCell u w) = horizCell Y0 c0 w.1 u.2 := by
  rw [← cell_horiz]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

theorem cell_eCell_v {u w : ℕ × ℕ} (h1 : w.1 = u.1) (h2 : w.2 = u.2 + 1) :
    cell Y0 c0 (eCell u w) = vertCell Y0 c0 u.1 u.2 := by
  rw [← cell_vert]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

theorem cell_eCell_v' {u w : ℕ × ℕ} (h1 : w.1 = u.1) (h2 : u.2 = w.2 + 1) :
    cell Y0 c0 (eCell u w) = vertCell Y0 c0 u.1 w.2 := by
  rw [← cell_vert]; congr 1; simp only [eCell, Prod.mk.injEq]; omega

macro "adj_tac" : tactic => `(tactic| (simp only [elementaryWallAdj, elementaryWallVerts,
  Set.mem_ofPred_eq, ne_eq, Prod.mk.injEq, Nat.odd_iff, true_and, and_true, true_or, or_true] at * <;>
  omega))

set_option hygiene false in
macro "step_tac" : tactic => `(tactic| (
  apply own_eq_eCell he' hpq
  first
    | (rw [cell_eCell_h] <;> [skip; (dsimp only <;> omega); (dsimp only <;> omega)])
    | (rw [cell_eCell_h'] <;> [skip; (dsimp only <;> omega); (dsimp only <;> omega)])
    | (rw [cell_eCell_v] <;> [skip; (dsimp only <;> omega); (dsimp only <;> omega)])
    | (rw [cell_eCell_v'] <;> [skip; (dsimp only <;> omega); (dsimp only <;> omega)])
    | rw [cell_vCell]
  simp only [vertexCell, horizCell, vertCell, eCell]
  split_ifs <;> (try simp only [Prod.mk.injEq, and_true, true_and]) <;> omega))

theorem chain_horiz (hp : Params h' Y0 c0) (he' : Even h') {a b : ℕ}
    (hpq : elementaryWallAdj h' (a, b) (a + 1, b)) :
    List.IsChain (fun u w => elementaryWallAdj (h' + 2) u w ∧
      own h' Y0 c0 (eCell u w) = some (eCell (a, b) (a + 1, b)))
      (vmap Y0 c0 (a, b) :: (inner Y0 c0 (a, b) (a + 1, b) ++ [vmap Y0 c0 (a + 1, b)])) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hord : a + b < (a + 1) + b := by omega
  simp only [inner, hord, ↓reduceIte, innerO, vmap]
  split_ifs <;>
  simp only [List.isChain_cons_cons, List.isChain_singleton, List.cons_append, List.nil_append,
    and_true] <;>
  constructorm* _ ∧ _ <;>
  first | adj_tac | step_tac

theorem chain_vert (hp : Params h' Y0 c0) (he' : Even h') {a b : ℕ}
    (hpq : elementaryWallAdj h' (a, b) (a, b + 1)) :
    List.IsChain (fun u w => elementaryWallAdj (h' + 2) u w ∧
      own h' Y0 c0 (eCell u w) = some (eCell (a, b) (a, b + 1)))
      (vmap Y0 c0 (a, b) :: (inner Y0 c0 (a, b) (a, b + 1) ++ [vmap Y0 c0 (a, b + 1)])) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hord : a + b < a + (b + 1) := by omega
  have hodd : (a + b) % 2 = 1 := by
    obtain ⟨-, -, h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩⟩ := hpq
    · omega
    · exact Nat.odd_iff.mp h
    · omega
  simp only [inner, hord, ↓reduceIte, innerO, vmap]
  split_ifs <;>
  simp only [List.isChain_cons_cons, List.isChain_singleton, List.cons_append, List.nil_append,
    and_true] <;>
  constructorm* _ ∧ _ <;>
  first | adj_tac | step_tac

theorem own_inner_horiz (hp : Params h' Y0 c0) (he' : Even h') {a b : ℕ}
    (hpq : elementaryWallAdj h' (a, b) (a + 1, b)) :
    ∀ u ∈ inner Y0 c0 (a, b) (a + 1, b), own h' Y0 c0 (vCell u) = some (eCell (a, b) (a + 1, b)) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hord : a + b < (a + 1) + b := by omega
  simp only [inner, hord, ↓reduceIte, innerO]
  split_ifs <;>
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    IsEmpty.forall_iff, implies_true] <;>
  constructorm* _ ∧ _ <;>
  step_tac

theorem own_inner_vert (hp : Params h' Y0 c0) (he' : Even h') {a b : ℕ}
    (hpq : elementaryWallAdj h' (a, b) (a, b + 1)) :
    ∀ u ∈ inner Y0 c0 (a, b) (a, b + 1), own h' Y0 c0 (vCell u) = some (eCell (a, b) (a, b + 1)) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hord : a + b < a + (b + 1) := by omega
  have hodd : (a + b) % 2 = 1 := by
    obtain ⟨-, -, h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩⟩ := hpq
    · omega
    · exact Nat.odd_iff.mp h
    · omega
  simp only [inner, hord, ↓reduceIte, innerO]
  split_ifs <;>
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    IsEmpty.forall_iff, implies_true] <;>
  constructorm* _ ∧ _ <;>
  step_tac

theorem nodup_horiz (hp : Params h' Y0 c0) {a b : ℕ} :
    (vmap Y0 c0 (a, b) :: (inner Y0 c0 (a, b) (a + 1, b) ++ [vmap Y0 c0 (a + 1, b)])).Nodup := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hord : a + b < (a + 1) + b := by omega
  simp only [inner, hord, ↓reduceIte, innerO, vmap]
  split_ifs <;>
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, Prod.mk.injEq, or_false, not_or, and_true, not_false_eq_true, true_and,
    and_self] <;>
  omega

theorem nodup_vert (hp : Params h' Y0 c0) {a b : ℕ} (hpq : elementaryWallAdj h' (a, b) (a, b + 1)) :
    (vmap Y0 c0 (a, b) :: (inner Y0 c0 (a, b) (a, b + 1) ++ [vmap Y0 c0 (a, b + 1)])).Nodup := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  have hord : a + b < a + (b + 1) := by omega
  have hodd : (a + b) % 2 = 1 := by
    obtain ⟨-, -, h | ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩⟩ := hpq
    · omega
    · exact Nat.odd_iff.mp h
    · omega
  simp only [inner, hord, ↓reduceIte, innerO, vmap]
  split_ifs <;>
  simp only [List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, Prod.mk.injEq, or_false, not_or, and_true, not_false_eq_true, true_and,
    and_self] <;>
  omega

theorem own_vmap (hp : Params h' Y0 c0) {p : ℕ × ℕ} (hp' : p ∈ elementaryWallVerts h') :
    own h' Y0 c0 (vCell (vmap Y0 c0 p)) = some (vCell p) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  apply own_eq_vCell hp'
  rw [cell_vCell]
  obtain ⟨x, y⟩ := p
  simp only [vmap]
  split_ifs <;> simp only [vertexCell, vCell] <;> split_ifs <;>
    (try simp only [Prod.mk.injEq, and_true, true_and]) <;> omega

theorem vmap_mem (hp : Params h' Y0 c0) {p : ℕ × ℕ} (hp' : p ∈ elementaryWallVerts h') :
    vmap Y0 c0 p ∈ elementaryWallVerts (h' + 2) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  obtain ⟨x, y⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have h3' : ¬ (x = 0 ∧ y = 0) := fun e => h3 (Prod.ext e.1 e.2)
  have h4' : ¬ (x = 2 * h' + 1 ∧ y = h') := fun e => h4 (Prod.ext e.1 e.2)
  dsimp only at h1 h2
  simp only [vmap]
  split_ifs <;> refine ⟨by omega, by omega, ?_, ?_⟩ <;>
    intro e <;> (try simp only [Prod.mk.injEq] at e) <;> omega

/-- The kept old element `m` is the old vertex of a new vertex, an inner vertex of the old path
of a new edge, or an edge of that path. -/
def Covered (h' : ℕ) (Y0 c0 : ℤ) (m : ℤ × ℤ) : Prop :=
  (∃ p ∈ elementaryWallVerts h', m = vCell (vmap Y0 c0 p)) ∨
    ∃ p q, elementaryWallAdj h' p q ∧ ((∃ u ∈ inner Y0 c0 p q, m = vCell u) ∨
      ∃ uw ∈ (vmap Y0 c0 p :: (inner Y0 c0 p q ++ [vmap Y0 c0 q])).zip
        (inner Y0 c0 p q ++ [vmap Y0 c0 q]), m = eCell uw.1 uw.2)

theorem covered_vmap {m : ℤ × ℤ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h')
    (e : m = vCell (vmap Y0 c0 p)) : Covered h' Y0 c0 m :=
  Or.inl ⟨p, hp, e⟩

theorem covered_inner {m : ℤ × ℤ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) {u : ℕ × ℕ}
    (hu : u ∈ inner Y0 c0 p q) (e : m = vCell u) : Covered h' Y0 c0 m :=
  Or.inr ⟨p, q, hpq, Or.inl ⟨u, hu, e⟩⟩

theorem covered_step {m : ℤ × ℤ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) {u w : ℕ × ℕ}
    (huw : (u, w) ∈ (vmap Y0 c0 p :: (inner Y0 c0 p q ++ [vmap Y0 c0 q])).zip
      (inner Y0 c0 p q ++ [vmap Y0 c0 q])) (e : m = eCell u w) : Covered h' Y0 c0 m :=
  Or.inr ⟨p, q, hpq, Or.inr ⟨(u, w), huw, e⟩⟩

macro "mem_tac" : tactic => `(tactic| (simp only [inner, innerO, vmap, vCell, eCell] <;>
  (try simp (disch := omega) only [ite_eq_left, ite_eq_right]) <;> (try split_ifs) <;>
  simp only [List.mem_cons, List.mem_reverse, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.zip_cons_cons, List.zip_nil_right, List.singleton_append,
    Prod.mk.injEq, List.not_mem_nil, or_false, and_true, true_and, true_or, or_true] <;> omega))

theorem covered_vertex (hp : Params h' Y0 c0) (he' : Even h') {a b : ℕ}
    (hc : IsWallCell h' (vertexCell Y0 c0 a b)) : Covered h' Y0 c0 (vCell (a, b)) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  obtain ⟨k, hk⟩ := he'
  obtain ⟨c, hcc⟩ : ∃ c : ℕ, (c : ℤ) = c0 - 1 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  unfold vertexCell at hc
  split_ifs at hc <;> simp only [isWallCell_vertex_iff, isWallCell_horiz_iff, isWallCell_vert_iff,
    not_isWallCell_odd_odd] at hc
  · exact covered_vmap (p := (a, b)) (by adj_tac) (by mem_tac)
  · exact covered_vmap (p := (a - 4, b)) (by adj_tac) (by mem_tac)
  · exact covered_inner (p := (c, b)) (q := (c + 1, b)) (u := (a, b)) (by adj_tac) (by mem_tac) (by mem_tac)
  · exact covered_inner (p := (a, b - 1)) (q := (a, b)) (u := (a, b)) (by adj_tac) (by mem_tac) (by mem_tac)
  · exact covered_inner (p := (a - 4, b - 1)) (q := (a - 4, b)) (u := (a, b)) (by adj_tac) (by mem_tac)
      (by mem_tac)
  · exact covered_inner (p := (a - 1, b - 1)) (q := (a - 1, b)) (u := (a, b)) (by adj_tac) (by mem_tac)
      (by mem_tac)
  · exact covered_inner (p := (a - 3, b - 1)) (q := (a - 3, b)) (u := (a, b)) (by adj_tac) (by mem_tac)
      (by mem_tac)
  · exact covered_inner (p := (a - 2, b - 2)) (q := (a - 2, b - 1)) (u := (a, b)) (by adj_tac) (by mem_tac)
      (by mem_tac)
  · exact covered_inner (p := (a - 1, b - 2)) (q := (a - 1, b - 1)) (u := (a, b)) (by adj_tac) (by mem_tac)
      (by mem_tac)
  · exact covered_inner (p := (a - 3, b - 2)) (q := (a - 3, b - 1)) (u := (a, b)) (by adj_tac) (by mem_tac)
      (by mem_tac)
  · exact covered_vmap (p := (a - 2, b - 2)) (by adj_tac) (by mem_tac)

theorem covered_horiz (hp : Params h' Y0 c0) (he' : Even h') {a b : ℕ}
    (hc : IsWallCell h' (horizCell Y0 c0 a b)) : Covered h' Y0 c0 (eCell (a, b) (a + 1, b)) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  obtain ⟨k, hk⟩ := he'
  obtain ⟨c, hcc⟩ : ∃ c : ℕ, (c : ℤ) = c0 - 1 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  unfold horizCell at hc
  split_ifs at hc <;> simp only [isWallCell_horiz_iff, isWallCell_vert_iff, not_isWallCell_odd_odd] at hc
  · exact covered_step (p := (a, b)) (q := (a + 1, b)) (u := (a, b)) (w := (a + 1, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 4, b)) (q := (a - 3, b)) (u := (a, b)) (w := (a + 1, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (c, b)) (q := (c + 1, b)) (u := (a, b)) (w := (a + 1, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a, b - 1)) (q := (a, b)) (u := (a, b)) (w := (a + 1, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 3, b - 1)) (q := (a - 3, b)) (u := (a + 1, b)) (w := (a, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 1, b - 2)) (q := (a - 1, b - 1)) (u := (a, b)) (w := (a + 1, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 2, b - 2)) (q := (a - 2, b - 1)) (u := (a + 1, b)) (w := (a, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 2, b - 2)) (q := (a - 1, b - 2)) (u := (a, b)) (w := (a + 1, b)) (by adj_tac)
      (by mem_tac) (by mem_tac)

set_option maxHeartbeats 1000000 in
theorem covered_vert (hp : Params h' Y0 c0) (he' : Even h') {a b : ℕ}
    (hc : IsWallCell h' (vertCell Y0 c0 a b)) : Covered h' Y0 c0 (eCell (a, b) (a, b + 1)) := by
  obtain ⟨Y1, Y2, c1, c2⟩ := hp
  obtain ⟨k, hk⟩ := he'
  obtain ⟨c, hcc⟩ : ∃ c : ℕ, (c : ℤ) = c0 - 1 := ⟨_, Int.toNat_of_nonneg (by omega)⟩
  unfold vertCell at hc
  split_ifs at hc <;> simp only [isWallCell_vert_iff, not_isWallCell_odd_odd] at hc
  · exact covered_step (p := (a, b)) (q := (a, b + 1)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 4, b)) (q := (a - 4, b + 1)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a, b)) (q := (a, b + 1)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 4, b)) (q := (a - 4, b + 1)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 1, b - 1)) (q := (a - 1, b)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 3, b - 1)) (q := (a - 3, b)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 2, b - 2)) (q := (a - 2, b - 1)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)
  · exact covered_step (p := (a - 2, b - 2)) (q := (a - 2, b - 1)) (u := (a, b)) (w := (a, b + 1)) (by adj_tac)
      (by mem_tac) (by mem_tac)

theorem covered (hp : Params h' Y0 c0) (he' : Even h') {m : ℤ × ℤ}
    (hm : m ∈ fig1WallCells (h' + 2)) (hown : own h' Y0 c0 m ≠ none) : Covered h' Y0 c0 m := by
  have hm' := (mem_fig1WallCells_iff (by omega) (even_succ_succ he') m).mp hm
  have hc : IsWallCell h' (cell Y0 c0 m) := by
    unfold own at hown
    split_ifs at hown with h1
    · exact h1
    · exact absurd rfl hown
  rcases cell_cases hm' with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · rw [isWallCell_vertex_iff] at hm'
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = x := ⟨_, Int.toNat_of_nonneg hm'.1⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, (b : ℤ) = y := ⟨_, Int.toNat_of_nonneg hm'.2.2.1⟩
    rw [cell_vertex] at hc
    exact covered_vertex hp he' hc
  · rw [isWallCell_horiz_iff] at hm'
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = x := ⟨_, Int.toNat_of_nonneg hm'.1⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, (b : ℤ) = y := ⟨_, Int.toNat_of_nonneg hm'.2.2.1⟩
    rw [cell_horiz] at hc
    have e : ((2 * (a : ℤ) + 1, 2 * (b : ℤ)) : ℤ × ℤ) = eCell (a, b) (a + 1, b) := by
      simp only [eCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    exact covered_horiz hp he' hc
  · rw [isWallCell_vert_iff] at hm'
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = x := ⟨_, Int.toNat_of_nonneg hm'.1⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, (b : ℤ) = y := ⟨_, Int.toNat_of_nonneg hm'.2.2.1⟩
    rw [cell_vert] at hc
    have e : ((2 * (a : ℤ), 2 * (b : ℤ) + 1) : ℤ × ℤ) = eCell (a, b) (a, b + 1) := by
      simp only [eCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    exact covered_vert hp he' hc

theorem inner_symm (p q : ℕ × ℕ) (hpq : elementaryWallAdj h' p q) :
    inner Y0 c0 q p = (inner Y0 c0 p q).reverse := by
  have hne : p.1 + p.2 ≠ q.1 + q.2 := by
    obtain ⟨-, -, h | ⟨h1, h | h⟩⟩ := hpq <;> omega
  unfold inner
  by_cases h1 : p.1 + p.2 < q.1 + q.2
  · rw [ite_eq_right (by omega), ite_eq_left h1]
  · rw [ite_eq_left (by omega), ite_eq_right h1, List.reverse_reverse]

theorem oriented_cases {p q : ℕ × ℕ} (hpq : elementaryWallAdj h' p q) (hlt : p.1 + p.2 < q.1 + q.2) :
    q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1) := by
  obtain ⟨-, -, h | ⟨h1, h | h⟩⟩ := hpq
  · left; ext <;> simp only <;> omega
  · right; ext <;> simp only <;> omega
  · omega

/-- **The realization of the hole.** -/
def realization (hp : Params h' Y0 c0) (hh' : 1 ≤ h') (he' : Even h') :
    (shape hp hh' he').Realization :=
  Shape.Realization.ofOriented (fun p q => elementaryWallAdj h' p q ∧ p.1 + p.2 < q.1 + q.2)
    (vmap Y0 c0) (inner Y0 c0)
    (fun p q hpq => by
      have hne : p.1 + p.2 ≠ q.1 + q.2 := by
        obtain ⟨-, -, h | ⟨h1, h | h⟩⟩ := hpq <;> omega
      by_cases h : p.1 + p.2 < q.1 + q.2
      · exact Or.inl ⟨hpq, h⟩
      · exact Or.inr ⟨elementaryWallAdj_symm hpq, by omega⟩)
    (fun _ _ h => h.1)
    (fun _ hp' => vmap_mem hp hp')
    inner_symm
    (fun p q ⟨hpq, hlt⟩ => by
      obtain ⟨a, b⟩ := p
      rcases oriented_cases hpq hlt with rfl | rfl
      · exact chain_horiz hp he' hpq
      · exact chain_vert hp he' hpq)
    (fun p q ⟨hpq, hlt⟩ => by
      obtain ⟨a, b⟩ := p
      rcases oriented_cases hpq hlt with rfl | rfl
      · exact nodup_horiz hp
      · exact nodup_vert hp hpq)
    (fun _ hp' => own_vmap hp hp')
    (fun p q ⟨hpq, hlt⟩ => by
      obtain ⟨a, b⟩ := p
      rcases oriented_cases hpq hlt with rfl | rfl
      · exact own_inner_horiz hp he' hpq
      · exact own_inner_vert hp he' hpq)
    (fun _ hm hown => covered hp he' hm hown)

end Hole

end GraphMinor.GM13
