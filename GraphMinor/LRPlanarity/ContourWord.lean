module

public import GraphMinor.LRPlanarity.DefsContour
import GraphMinor.LRPlanarity.ContourTree

/-!
# The contour word of a valid contour order

Part IV, Section 2 of `docs/planarity/planarity_test.tex` replaces each child incidence by the
child's contour and reads off the leaf word. It then uses, without proof, that
"W(w) is a contiguous subword of W for every rooted subtree". This file proves the facts about
the word that Sections 2 to 4 use, for every valid contour order of a depth-first forest.

Attach each port to its *home*: the source of its edge for a source port, the target for a
target port. We show:

* the contour of `v` (`subtreeWord`) is the concatenation of the expansions of the events of
  the local order at `v` (`subtreeWord_eq`);
* it contains exactly the ports of back edges whose home lies below `v` (`mem_subtreeWord`),
  each once;
* the whole word contains each port of each back edge exactly once (`isPortWord`), and the
  contour of each vertex is a contiguous subword of it (`subtreeWord_infix`).

Positions in a list without repetitions are compared by `List.idxOf`. Two list lemmas do this
work: a contiguous subword occupies an interval of positions (`idxOf_of_infix`), and in a
concatenation `l.flatMap f`, the order of two blocks `f a` and `f a'` is the order of `a` and
`a'` in `l` (`idxOf_flatMap_lt`).
-/

public section

namespace GraphMinor.LRPlanarity.ContourWord

open SearchTree

variable {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)} {order : ContourOrder N}

/-! ### Positions in lists -/

section Lists

variable {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]

/-- A contiguous subword of a list without repetitions occupies an interval of positions. -/
theorem idxOf_of_infix {s l : List α} (hnd : l.Nodup) (h : s <:+: l) :
    ∃ off, (∀ x ∈ s, l.idxOf x = off + s.idxOf x) ∧
      (∀ x ∈ l, x ∉ s → l.idxOf x < off ∨ off + s.length ≤ l.idxOf x) := by
  obtain ⟨A, B, rfl⟩ := h
  refine ⟨A.length, fun x hx => ?_, fun x hx hxs => ?_⟩
  · have hxA : x ∉ A := by
      intro hxA
      rw [List.append_assoc] at hnd
      exact List.disjoint_of_nodup_append hnd hxA (List.mem_append_left _ hx)
    rw [List.append_assoc, List.idxOf_append_of_notMem hxA, List.idxOf_append_of_mem hx]
  · by_cases hxA : x ∈ A
    · left
      rw [List.append_assoc, List.idxOf_append_of_mem hxA]
      exact List.idxOf_lt_length_of_mem hxA
    · right
      rw [List.append_assoc, List.idxOf_append_of_notMem hxA,
        List.idxOf_append_of_notMem hxs]
      omega

/-- In a concatenation without repetitions, the blocks appear in the order of the list. -/
theorem idxOf_flatMap_lt {l : List β} {f : β → List α} (hnd : (l.flatMap f).Nodup)
    {a a' : β} (ha : a ∈ l) (ha' : a' ∈ l) (hlt : l.idxOf a < l.idxOf a') {x y : α}
    (hx : x ∈ f a) (hy : y ∈ f a') : (l.flatMap f).idxOf x < (l.flatMap f).idxOf y := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    rw [List.flatMap_cons] at hnd ⊢
    have hdisj := List.disjoint_of_nodup_append hnd
    have hnd' := (List.nodup_append.mp hnd).2.1
    by_cases hca : c = a
    · subst hca
      have hca' : c ≠ a' := by
        rintro rfl
        exact lt_irrefl _ hlt
      have hy' : y ∈ l.flatMap f := List.mem_flatMap.mpr
        ⟨a', (List.mem_cons.mp ha').resolve_left (Ne.symm hca'), hy⟩
      rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem (fun h => hdisj h hy')]
      exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem hx) (Nat.le_add_right _ _)
    · have hca' : c ≠ a' := by
        rintro rfl
        rw [List.idxOf_cons_self] at hlt
        exact Nat.not_lt_zero _ hlt
      have hal : a ∈ l := (List.mem_cons.mp ha).resolve_left (Ne.symm hca)
      have ha'l : a' ∈ l := (List.mem_cons.mp ha').resolve_left (Ne.symm hca')
      rw [List.idxOf_cons_ne _ hca, List.idxOf_cons_ne _ hca'] at hlt
      have hx' : x ∈ l.flatMap f := List.mem_flatMap.mpr ⟨a, hal, hx⟩
      have hy' : y ∈ l.flatMap f := List.mem_flatMap.mpr ⟨a', ha'l, hy⟩
      rw [List.idxOf_append_of_notMem (fun h => hdisj h hx'),
        List.idxOf_append_of_notMem (fun h => hdisj h hy')]
      have := ih hnd' hal ha'l (Nat.lt_of_succ_lt_succ hlt)
      omega

/-- Two distinct members of a list have distinct positions. -/
theorem idxOf_lt_or_gt {l : List α} {a a' : α} (ha : a ∈ l) (hne : a ≠ a') :
    l.idxOf a < l.idxOf a' ∨ l.idxOf a' < l.idxOf a := by
  rcases Nat.lt_trichotomy (l.idxOf a) (l.idxOf a') with h | h | h
  · exact Or.inl h
  · exact absurd ((List.idxOf_inj ha).mp h) hne
  · exact Or.inr h

/-- In a pairwise related list, an earlier member is related to a later one. -/
theorem rel_of_idxOf_lt {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hlt : l.idxOf x < l.idxOf y) : R x y := by
  rw [List.pairwise_iff_getElem] at h
  have := h _ _ (List.idxOf_lt_length_of_mem hx) (List.idxOf_lt_length_of_mem hy) hlt
  rwa [List.getElem_idxOf, List.getElem_idxOf] at this

/-- A partial map that is injective where it is defined keeps the order of positions. -/
theorem idxOf_filterMap_lt_iff {f : α → Option β}
    (hf : ∀ a a' b, f a = some b → f a' = some b → a = a') :
    ∀ {l : List α} {x y : α} {x' y' : β}, x ∈ l → y ∈ l → f x = some x' → f y = some y' →
      (l.idxOf x < l.idxOf y ↔ (l.filterMap f).idxOf x' < (l.filterMap f).idxOf y')
  | [], _, _, _, _, hx, _, _, _ => by simp at hx
  | a :: l, x, y, x', y', hx, hy, hfx, hfy => by
    by_cases hax : a = x
    · subst hax
      rw [List.filterMap_cons_some hfx, List.idxOf_cons_self, List.idxOf_cons_self]
      by_cases hay : a = y
      · subst hay
        rw [hfx, Option.some_inj] at hfy
        subst hfy
        simp
      · have hxy : x' ≠ y' := fun h => hay (hf _ _ _ hfx (h ▸ hfy))
        rw [List.idxOf_cons_ne _ hay, List.idxOf_cons_ne _ hxy]
        simp
    · by_cases hay : a = y
      · subst hay
        rw [List.filterMap_cons_some hfy, List.idxOf_cons_self, List.idxOf_cons_self]
        simp
      · have hxl := (List.mem_cons.mp hx).resolve_left (Ne.symm hax)
        have hyl := (List.mem_cons.mp hy).resolve_left (Ne.symm hay)
        have ih := idxOf_filterMap_lt_iff hf hxl hyl hfx hfy
        rw [List.idxOf_cons_ne _ hax, List.idxOf_cons_ne _ hay, Nat.succ_lt_succ_iff]
        cases hfa : f a with
        | none =>
          rw [List.filterMap_cons_none hfa]
          exact ih
        | some z =>
          rw [List.filterMap_cons_some hfa]
          have hzx : z ≠ x' := fun h => hax (hf _ _ _ hfa (h ▸ hfx))
          have hzy : z ≠ y' := fun h => hay (hf _ _ _ hfa (h ▸ hfy))
          rw [List.idxOf_cons_ne _ hzx, List.idxOf_cons_ne _ hzy, Nat.succ_lt_succ_iff]
          exact ih

end Lists

/-! ### Homes of ports and expansion of events -/

/-- The vertex at which a port is attached: the source of its edge for a source port, and its
target for a target port. -/
@[expose] def portHome (p : Port N) : Fin N := if p.source then p.edge.1 else p.edge.2

@[simp] theorem portHome_source (b : Arc N) : portHome (⟨b, true⟩ : Port N) = b.1 := by
  simp [portHome]

@[simp] theorem portHome_target (b : Arc N) : portHome (⟨b, false⟩ : Port N) = b.2 := by
  simp [portHome]

theorem portHome_iff (p : Port N) (v : Fin N) :
    (if p.source then p.edge.1 = v else p.edge.2 = v) ↔ portHome p = v := by
  unfold portHome
  cases p.source <;> rfl

/-- A port event stands for itself. A child event stands for the contour `F w` of the child. -/
@[expose] def expand (F : Fin N → List (Port N)) : ContourEvent N → List (Port N)
  | .child w => F w
  | .port p => [p]

theorem vertexContour_succ (k : ℕ) (v : Fin N) :
    vertexContour order (k + 1) v = (order v).flatMap (expand (vertexContour order k)) := by
  simp only [vertexContour]
  congr 1

theorem mem_order_child (hO : ValidContourOrder T G order) {v w : Fin N} :
    ContourEvent.child w ∈ order v ↔ T.parent w = some v :=
  (hO v).2 (.child w)

theorem mem_order_port (hO : ValidContourOrder T G order) {v : Fin N} {p : Port N} :
    ContourEvent.port p ∈ order v ↔ T.BackEdge G p.edge ∧ portHome p = v := by
  rw [(hO v).2 (.port p)]
  exact and_congr_right fun _ => portHome_iff p v

/-! ### Contours of subtrees -/

/-- Every port of the contour of `v` belongs to a back edge and has its home below `v`. -/
theorem mem_vertexContour_imp (hO : ValidContourOrder T G order) :
    ∀ (k : ℕ) (v : Fin N) (p : Port N), p ∈ vertexContour order k v →
      T.BackEdge G p.edge ∧ T.Ancestor v (portHome p) := by
  intro k
  induction k with
  | zero => intro v p hp; simp [vertexContour] at hp
  | succ k ih =>
    intro v p hp
    rw [vertexContour_succ, List.mem_flatMap] at hp
    obtain ⟨event, hev, hp⟩ := hp
    cases event with
    | child w =>
      obtain ⟨hb, hw⟩ := ih w p hp
      exact ⟨hb, ancestor_trans (ancestor_of_parent ((mem_order_child hO).mp hev)) hw⟩
    | port q =>
      rw [expand, List.mem_singleton] at hp
      subst hp
      obtain ⟨hb, hv⟩ := (mem_order_port hO).mp hev
      exact ⟨hb, hv ▸ ancestor_refl _⟩

/-- With enough fuel, the contour of `v` contains every port of a back edge whose home lies
below `v`. -/
theorem mem_vertexContour_of (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    ∀ (k : ℕ) (v : Fin N), (∀ y, T.Ancestor v y → T.depth y < T.depth v + k) →
      ∀ p : Port N, T.BackEdge G p.edge → T.Ancestor v (portHome p) →
        p ∈ vertexContour order k v := by
  intro k
  induction k with
  | zero =>
    intro v hk
    have := hk v (ancestor_refl v)
    omega
  | succ k ih =>
    intro v hk p hb hv
    rw [vertexContour_succ, List.mem_flatMap]
    by_cases hpv : v = portHome p
    · exact ⟨.port p, (mem_order_port hO).mpr ⟨hb, hpv.symm⟩, List.mem_singleton_self _⟩
    · obtain ⟨w, hw, hwp⟩ := exists_child_of_ancestor hv hpv
      refine ⟨.child w, (mem_order_child hO).mpr hw, ih w (fun y hy => ?_) p hb hwp⟩
      have := hk y (ancestor_trans (ancestor_of_parent hw) hy)
      rw [depth_of_parent hT hw]
      omega

/-- The contour of a vertex has no repeated port. -/
theorem nodup_vertexContour (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    ∀ (k : ℕ) (v : Fin N), (vertexContour order k v).Nodup := by
  intro k
  induction k with
  | zero => intro v; simp [vertexContour]
  | succ k ih =>
    intro v
    rw [vertexContour_succ, List.nodup_flatMap]
    refine ⟨fun event _ => ?_, (hO v).1.pairwise_of_forall_ne fun ev hev ev' hev' hne => ?_⟩
    · cases event with
      | child w => exact ih w
      | port p => exact List.nodup_singleton p
    · intro p hp hp'
      cases ev with
      | child w =>
        have hw := (mem_order_child hO).mp hev
        have hwp := (mem_vertexContour_imp hO k w p hp).2
        cases ev' with
        | child w' =>
          have hw' := (mem_order_child hO).mp hev'
          have hw'p := (mem_vertexContour_imp hO k w' p hp').2
          exact hne (by rw [child_unique hT hw hw' hwp hw'p])
        | port q =>
          rw [expand, List.mem_singleton] at hp'
          subst hp'
          have hpv := ((mem_order_port hO).mp hev').2
          rw [hpv] at hwp
          have := depth_le_of_ancestor hT hwp
          rw [depth_of_parent hT hw] at this
          omega
      | port q =>
        rw [expand, List.mem_singleton] at hp
        subst hp
        have hpv := ((mem_order_port hO).mp hev).2
        cases ev' with
        | child w' =>
          have hw' := (mem_order_child hO).mp hev'
          have hw'p := (mem_vertexContour_imp hO k w' p hp').2
          rw [hpv] at hw'p
          have := depth_le_of_ancestor hT hw'p
          rw [depth_of_parent hT hw'] at this
          omega
        | port q' =>
          rw [expand, List.mem_singleton] at hp'
          exact hne (by rw [hp'])

/-- Part IV, Section 2: the contour `W(v)` of the subtree at `v`. The fuel is the one that
`contourWord` gives to `v` through the recursion from its root. -/
@[expose] def subtreeWord (T : Forest N) (order : ContourOrder N) (v : Fin N) : List (Port N) :=
  vertexContour order (N + 1 - T.depth v) v

/-- The contour of `v` is the concatenation of the expansions of the local order at `v`. -/
theorem subtreeWord_eq (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (v : Fin N) :
    subtreeWord T order v = (order v).flatMap (expand (subtreeWord T order)) := by
  have hv := depth_lt hT v
  unfold subtreeWord
  rw [show N + 1 - T.depth v = (N - T.depth v) + 1 by omega, vertexContour_succ]
  refine List.flatMap_congr fun event hev => ?_
  cases event with
  | port p => rfl
  | child w =>
    have hw := depth_of_parent hT ((mem_order_child hO).mp hev)
    simp only [expand]
    rw [show N + 1 - T.depth w = N - T.depth v by omega]

theorem mem_subtreeWord (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (v : Fin N)
    (p : Port N) :
    p ∈ subtreeWord T order v ↔ T.BackEdge G p.edge ∧ T.Ancestor v (portHome p) := by
  refine ⟨mem_vertexContour_imp hO _ v p, fun ⟨hb, hv⟩ => ?_⟩
  refine mem_vertexContour_of hT hO _ v (fun y _ => ?_) p hb hv
  have := depth_lt hT y
  have := depth_lt hT v
  omega

theorem nodup_subtreeWord (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (v : Fin N) :
    (subtreeWord T order v).Nodup :=
  nodup_vertexContour hT hO _ v

/-! ### The whole word -/

/-- The roots of the forest in label order, as `contourWord` lists them. -/
noncomputable def roots (T : Forest N) : List (Fin N) :=
  (Finset.univ.filter (fun v => T.parent v = none)).sort (· ≤ ·)

theorem mem_roots {r : Fin N} : r ∈ roots T ↔ T.parent r = none := by
  unfold roots
  rw [Finset.mem_sort, Finset.mem_filter]
  simp

theorem contourWord_eq (hT : T.IsDFS G) :
    contourWord T order = (roots T).flatMap (subtreeWord T order) := by
  unfold contourWord
  refine List.flatMap_congr fun r hr => ?_
  have hr' : T.parent r = none := mem_roots.mp hr
  unfold subtreeWord
  rw [hT.1 r hr']
  rfl

theorem mem_contourWord (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (p : Port N) :
    p ∈ contourWord T order ↔ T.BackEdge G p.edge := by
  rw [contourWord_eq hT, List.mem_flatMap]
  constructor
  · rintro ⟨r, _, hp⟩
    exact ((mem_subtreeWord hT hO r p).mp hp).1
  · intro hb
    obtain ⟨r, hr, hrp⟩ := exists_root_ancestor hT (portHome p)
    exact ⟨r, mem_roots.mpr hr, (mem_subtreeWord hT hO r p).mpr ⟨hb, hrp⟩⟩

theorem nodup_contourWord (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    (contourWord T order).Nodup := by
  rw [contourWord_eq hT, List.nodup_flatMap]
  refine ⟨fun r _ => nodup_subtreeWord hT hO r, ?_⟩
  have hnd : (roots T).Nodup := Finset.sort_nodup _ _
  refine hnd.pairwise_of_forall_ne fun r hr r' hr' hne p hp hp' => hne ?_
  have h₁ := ((mem_subtreeWord hT hO r p).mp hp).2
  have h₂ := ((mem_subtreeWord hT hO r' p).mp hp').2
  rcases ancestor_total h₁ h₂ with h | h
  · exact eq_of_ancestor_root h (mem_roots.mp hr')
  · exact (eq_of_ancestor_root h (mem_roots.mp hr)).symm

/-- Part IV, Section 2: the word of a valid contour order contains one source port and one
target port of every back edge, and nothing else. -/
theorem isPortWord (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    IsPortWord T G (contourWord T order) :=
  ⟨nodup_contourWord hT hO, mem_contourWord hT hO⟩

/-- Part IV, Section 2: "W(w) is a contiguous subword of W for every rooted subtree." -/
theorem subtreeWord_infix (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (v : Fin N) :
    subtreeWord T order v <:+: contourWord T order := by
  suffices h : ∀ n, ∀ v, T.depth v ≤ n → subtreeWord T order v <:+: contourWord T order from
    h _ v le_rfl
  intro n
  induction n with
  | zero =>
    intro v hv
    cases hp : T.parent v with
    | some p => have := depth_of_parent hT hp; omega
    | none =>
      rw [contourWord_eq hT]
      exact List.infix_of_mem_flatten (List.mem_map_of_mem (mem_roots.mpr hp))
  | succ n ih =>
    intro v hv
    cases hp : T.parent v with
    | none =>
      rw [contourWord_eq hT]
      exact List.infix_of_mem_flatten (List.mem_map_of_mem (mem_roots.mpr hp))
    | some p =>
      have hd := depth_of_parent hT hp
      refine List.IsInfix.trans ?_ (ih p (by omega))
      rw [subtreeWord_eq hT hO p]
      exact List.infix_of_mem_flatten
        (List.mem_map_of_mem (f := expand (subtreeWord T order)) ((mem_order_child hO).mpr hp))

/-- Ports from two events of the local order at `u` come in the order of the events. -/
theorem idxOf_lt_of_order (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {u : Fin N}
    {ev ev' : ContourEvent N} (hev : ev ∈ order u) (hev' : ev' ∈ order u)
    (hlt : (order u).idxOf ev < (order u).idxOf ev') {x y : Port N}
    (hx : x ∈ expand (subtreeWord T order) ev) (hy : y ∈ expand (subtreeWord T order) ev') :
    (contourWord T order).idxOf x < (contourWord T order).idxOf y := by
  obtain ⟨off, hin, -⟩ := idxOf_of_infix (nodup_contourWord hT hO) (subtreeWord_infix hT hO u)
  have hS := subtreeWord_eq hT hO u
  have hnd := nodup_subtreeWord hT hO u
  have hxS : x ∈ subtreeWord T order u := hS ▸ List.mem_flatMap.mpr ⟨ev, hev, hx⟩
  have hyS : y ∈ subtreeWord T order u := hS ▸ List.mem_flatMap.mpr ⟨ev', hev', hy⟩
  rw [hin x hxS, hin y hyS, Nat.add_lt_add_iff_left, hS]
  rw [hS] at hnd
  exact idxOf_flatMap_lt hnd hev hev' hlt hx hy

end GraphMinor.LRPlanarity.ContourWord
