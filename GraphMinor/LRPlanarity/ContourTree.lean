module

public import GraphMinor.LRPlanarity.Defs

/-!
# The ancestor order of a search forest, and strict returns

This file collects the facts about search forests that Parts III and IV of
`docs/planarity/planarity_test.tex` use without comment.

A parent edge raises the depth by one. So depth grows strictly along the ancestor
relation, and the relation is a partial order. A vertex has at most one parent, so two
ancestors of one vertex are comparable, and a strict descendant of `u` lies below
exactly one child of `u`. Every vertex lies below exactly one root, and every depth is
below the number of vertices.

For strict returns, we show that a return of an outgoing edge at `v` starts below `v`
and ends at a strict ancestor of `v`. We also show that `low` is attained by a return
when it is below the source depth, and that every nonempty return set has a highest
member.
-/

public section

namespace GraphMinor.LRPlanarity.SearchTree

open Relation

variable {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}

/-! ### The ancestor order -/

theorem depth_of_parent (hT : T.IsDFS G) {u v : Fin N} (h : T.parent v = some u) :
    T.depth v = T.depth u + 1 :=
  (hT.2.1 u v h).2

theorem ancestor_refl (v : Fin N) : T.Ancestor v v := ReflTransGen.refl

theorem ancestor_trans {u v w : Fin N} (h₁ : T.Ancestor u v) (h₂ : T.Ancestor v w) :
    T.Ancestor u w :=
  ReflTransGen.trans h₁ h₂

theorem ancestor_of_parent {u v : Fin N} (h : T.parent v = some u) : T.Ancestor u v :=
  ReflTransGen.single h

/-- A vertex is an ancestor of `v` exactly when it is `v` or an ancestor of a child-parent
step above `v`. -/
theorem ancestor_cases_tail {u v : Fin N} (h : T.Ancestor u v) :
    v = u ∨ ∃ p, T.Ancestor u p ∧ T.parent v = some p :=
  ReflTransGen.cases_tail h

/-- A strict descendant of `u` lies below a child of `u`. -/
theorem exists_child_of_ancestor {u x : Fin N} (h : T.Ancestor u x) (hne : u ≠ x) :
    ∃ w, T.parent w = some u ∧ T.Ancestor w x := by
  rcases ReflTransGen.cases_head h with h | ⟨w, hw, hwx⟩
  · exact absurd h hne
  · exact ⟨w, hw, hwx⟩

theorem depth_le_of_ancestor (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v) :
    T.depth u ≤ T.depth v := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => rw [depth_of_parent hT hbc]; omega

/-- An ancestor of the same depth is the vertex itself. -/
theorem eq_of_ancestor_of_depth_le (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v)
    (hd : T.depth v ≤ T.depth u) : u = v := by
  rcases ReflTransGen.cases_head h with h | ⟨w, hw, hwv⟩
  · exact h
  · have h₁ := depth_le_of_ancestor hT hwv
    rw [depth_of_parent hT hw] at h₁
    omega

theorem depth_lt_of_ancestor (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v)
    (hne : u ≠ v) : T.depth u < T.depth v := by
  rcases (depth_le_of_ancestor hT h).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (eq_of_ancestor_of_depth_le hT h h'.ge) hne

theorem ancestor_antisymm (hT : T.IsDFS G) {u v : Fin N} (h₁ : T.Ancestor u v)
    (h₂ : T.Ancestor v u) : u = v :=
  eq_of_ancestor_of_depth_le hT h₁ (depth_le_of_ancestor hT h₂)

/-- Two ancestors of one vertex are comparable, since a vertex has at most one parent. -/
theorem ancestor_total {a b x : Fin N} (ha : T.Ancestor a x) (hb : T.Ancestor b x) :
    T.Ancestor a b ∨ T.Ancestor b a := by
  induction hb generalizing a with
  | refl => exact Or.inl ha
  | @tail y z hby hyz ih =>
    rcases ancestor_cases_tail ha with rfl | ⟨p, hap, hzp⟩
    · exact Or.inr (ancestor_trans hby (ancestor_of_parent hyz))
    · rw [hyz, Option.some_inj] at hzp
      subst hzp
      exact ih hap

/-- The child of `u` above a strict descendant of `u` is unique. -/
theorem child_unique (hT : T.IsDFS G) {u w w' x : Fin N} (hw : T.parent w = some u)
    (hw' : T.parent w' = some u) (hwx : T.Ancestor w x) (hw'x : T.Ancestor w' x) :
    w = w' := by
  have hd : T.depth w = T.depth w' := by
    rw [depth_of_parent hT hw, depth_of_parent hT hw']
  rcases ancestor_total hwx hw'x with h | h
  · exact eq_of_ancestor_of_depth_le hT h hd.ge
  · exact (eq_of_ancestor_of_depth_le hT h hd.le).symm

/-- An ancestor of a child of `u` that is not below `u`'s child is an ancestor of `u`. -/
theorem ancestor_of_ancestor_child {u w a : Fin N} (hw : T.parent w = some u)
    (ha : T.Ancestor a w) (hne : a ≠ w) : T.Ancestor a u := by
  rcases ancestor_cases_tail ha with h | ⟨p, hap, hwp⟩
  · exact absurd h.symm hne
  · rw [hw, Option.some_inj] at hwp
    exact hwp ▸ hap

/-- A vertex whose parent is not defined has no strict ancestor. -/
theorem eq_of_ancestor_root {u r : Fin N} (h : T.Ancestor u r) (hr : T.parent r = none) :
    u = r := by
  rcases ancestor_cases_tail h with h | ⟨p, _, hrp⟩
  · exact h.symm
  · rw [hr] at hrp
    exact absurd hrp (by simp)

/-- Every vertex lies below a root. -/
theorem exists_root_ancestor (hT : T.IsDFS G) (v : Fin N) :
    ∃ r, T.parent r = none ∧ T.Ancestor r v := by
  suffices h : ∀ n, ∀ v, T.depth v ≤ n → ∃ r, T.parent r = none ∧ T.Ancestor r v from
    h _ v le_rfl
  intro n
  induction n with
  | zero =>
    intro v hv
    refine ⟨v, ?_, ancestor_refl v⟩
    cases hp : T.parent v with
    | none => rfl
    | some p => have := depth_of_parent hT hp; omega
  | succ n ih =>
    intro v hv
    cases hp : T.parent v with
    | none => exact ⟨v, hp, ancestor_refl v⟩
    | some p =>
      have hd := depth_of_parent hT hp
      obtain ⟨r, hr, hrp⟩ := ih p (by omega)
      exact ⟨r, hr, ancestor_trans hrp (ancestor_of_parent hp)⟩

/-- Every vertex has an ancestor at each smaller depth. -/
theorem exists_ancestor_of_depth (hT : T.IsDFS G) (v : Fin N) {k : ℕ} (hk : k ≤ T.depth v) :
    ∃ a, T.Ancestor a v ∧ T.depth a = k := by
  suffices h : ∀ n, ∀ v, T.depth v = n → ∀ k ≤ n, ∃ a, T.Ancestor a v ∧ T.depth a = k from
    h _ v rfl k hk
  intro n
  induction n with
  | zero =>
    intro v hv k hk
    exact ⟨v, ancestor_refl v, by omega⟩
  | succ n ih =>
    intro v hv k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · cases hp : T.parent v with
      | none => have := hT.1 v hp; omega
      | some p =>
        have hd := depth_of_parent hT hp
        obtain ⟨a, ha, hak⟩ := ih p (by omega) k (by omega)
        exact ⟨a, ancestor_trans ha (ancestor_of_parent hp), hak⟩
    · exact ⟨v, ancestor_refl v, by omega⟩

/-- Depths are below the number of vertices: the ancestors of `v` have the distinct
depths `0, ..., depth v`. -/
theorem depth_lt (hT : T.IsDFS G) (v : Fin N) : T.depth v < N := by
  choose f hf hfd using fun k : Fin (T.depth v + 1) =>
    exists_ancestor_of_depth hT v (Nat.lt_succ_iff.mp k.2)
  have hinj : Function.Injective f := by
    intro k l hkl
    apply Fin.ext
    rw [← hfd k, ← hfd l, hkl]
  have := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at this
  omega

/-! ### Tree edges and back edges -/

theorem ancestor_of_backEdge {b : Arc N} (hb : T.BackEdge G b) : T.Ancestor b.2 b.1 :=
  hb.2.1

theorem ne_of_backEdge {b : Arc N} (hb : T.BackEdge G b) : b.2 ≠ b.1 := by
  intro h
  have := hb.2.2.1
  rw [h] at this
  exact lt_irrefl _ this

/-- No pair is both a tree edge and a back edge. -/
theorem not_treeEdge_of_backEdge (hT : T.IsDFS G) {b : Arc N} (hb : T.BackEdge G b) :
    ¬ T.TreeEdge b := by
  intro ht
  have := depth_of_parent hT ht
  have := hb.2.2.1
  omega

/-! ### Strict returns -/

/-- A return of an edge leaving `v` starts below `v` and returns above `v`. -/
theorem returns_spec {e b : Arc N} (hb : b ∈ T.returns G e) :
    T.BackEdge G b ∧ T.Ancestor e.1 b.1 ∧ T.depth b.2 < T.depth e.1 := by
  obtain ⟨hbb, ⟨_, rfl⟩ | ⟨he, hab, hd⟩⟩ := hb
  · exact ⟨hbb, ancestor_refl _, hbb.2.2.1⟩
  · exact ⟨hbb, ancestor_trans (ancestor_of_parent he) hab, hd⟩

/-- The head of a return of an edge leaving `v` is a strict ancestor of `v`. -/
theorem head_ancestor_of_returns (hT : T.IsDFS G) {e b : Arc N} (hb : b ∈ T.returns G e) :
    T.Ancestor b.2 e.1 ∧ b.2 ≠ e.1 := by
  obtain ⟨hbb, hab, hd⟩ := returns_spec hb
  refine ⟨?_, fun h => by rw [h] at hd; exact lt_irrefl _ hd⟩
  rcases ancestor_total (ancestor_of_backEdge hbb) hab with h | h
  · exact h
  · have := depth_le_of_ancestor hT h
    omega

theorem low_le_source (e : Arc N) : T.low G e ≤ T.depth e.1 := by
  classical
  unfold Forest.low
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem low_le_of_returns {e b : Arc N} (hb : b ∈ T.returns G e) :
    T.low G e ≤ T.depth b.2 := by
  classical
  unfold Forest.low
  apply Finset.min'_le
  apply Finset.mem_insert_of_mem
  rw [Finset.mem_image]
  exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, rfl⟩

/-- A lowpoint below the source depth is the head depth of a return. -/
theorem exists_returns_of_low_lt {e : Arc N} (h : T.low G e < T.depth e.1) :
    ∃ c ∈ T.returns G e, T.depth c.2 = T.low G e := by
  classical
  revert h
  unfold Forest.low
  intro h
  have hmem := Finset.min'_mem (insert (T.depth e.1) ((Finset.univ.filter
    (fun b => b ∈ T.returns G e)).image (fun b => T.depth b.2))) (by simp)
  rcases Finset.mem_insert.mp hmem with h' | h'
  · rw [h'] at h
    exact absurd h (lt_irrefl _)
  · obtain ⟨c, hc, hcd⟩ := Finset.mem_image.mp h'
    exact ⟨c, (Finset.mem_filter.mp hc).2, hcd⟩

/-- A nonempty return set has a member of greatest head depth. -/
theorem exists_highest {e : Arc N} (h : (T.returns G e).Nonempty) :
    ∃ b ∈ T.returns G e, ∀ c ∈ T.returns G e, T.depth c.2 ≤ T.depth b.2 := by
  classical
  obtain ⟨b₀, hb₀⟩ := h
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun b => b ∈ T.returns G e)) (fun b => T.depth b.2)
    ⟨b₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb₀⟩⟩
  exact ⟨b, (Finset.mem_filter.mp hb).2, fun c hc =>
    hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)⟩

theorem thick_eq_true_iff (e : Arc N) : T.thick G e = true ↔
    ∃ b ∈ T.returns G e, ∃ c ∈ T.returns G e, T.depth b.2 ≠ T.depth c.2 := by
  unfold Forest.thick
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

end GraphMinor.LRPlanarity.SearchTree
