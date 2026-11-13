module

public import GraphMinor.LRPlanarity.DefsContour
public import Mathlib.Order.Lattice.Nat

/-!
# The leaf word of the expanded search tree

Part IV, Section 5 of `docs/planarity/planarity_test.tex` draws a rooted ordered tree whose leaves
are ports. It first says: "Add one dummy leaf to each original vertex which otherwise has no
child or port leaf." Then it numbers the leaves along the contour, and gives each vertex the
interval from its smallest to its largest descendant leaf.

This file builds that numbering for a depth-first forest with a valid contour order. We expand
the local orders into a word of leaves (`leafWord`): ports and dummy leaves, in contour order.
The proofs go by induction down the forest. The main facts are these.

* Removing the dummy leaves from `leafWord` gives the contour word (`contourWord_eq`).
* Every leaf occurs once, and a leaf lies below a vertex exactly when it occurs in the block of
  that vertex (`mem_leafContour`, `nodup_leafWord`).
* The descendant leaves of a vertex fill an interval of indices (`descIdx_eq_Icc`). This is the
  remark of Section 2 that "W(w) is a contiguous subword of W for every rooted subtree".
* Intervals of comparable vertices are nested, and intervals of other vertices are disjoint.
* Ports of distinct back edges do not alternate in `leafWord`, since the dummy leaves do not
  change the order of the ports (`not_alternating_leafIdx`).
-/

public section

namespace GraphMinor.LRPlanarity.Drawing

open Relation

variable {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N} {order : ContourOrder N}

/-! ### Depths and ancestors in a depth-first forest -/

theorem depth_child (hT : T.IsDFS G) {u v : Fin N} (h : T.parent v = some u) :
    T.depth v = T.depth u + 1 :=
  (hT.2.1 u v h).2

theorem ancestor_refl (v : Fin N) : T.Ancestor v v := ReflTransGen.refl

theorem ancestor_trans {u v w : Fin N} (h₁ : T.Ancestor u v) (h₂ : T.Ancestor v w) :
    T.Ancestor u w :=
  ReflTransGen.trans h₁ h₂

theorem ancestor_of_parent {u v : Fin N} (h : T.parent v = some u) : T.Ancestor u v :=
  ReflTransGen.single h

/-- A vertex is an ancestor of `w` when it is `w` or an ancestor of a child on the way. -/
theorem ancestor_iff {v w : Fin N} :
    T.Ancestor v w ↔ v = w ∨ ∃ c, T.parent c = some v ∧ T.Ancestor c w :=
  ReflTransGen.cases_head_iff

/-- A strict ancestor has a smaller depth. -/
theorem eq_or_depth_lt (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v) :
    u = v ∨ T.depth u < T.depth v := by
  unfold Forest.Ancestor at h
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hp ih =>
    right
    have := depth_child hT hp
    rcases ih with rfl | h <;> omega

theorem depth_le (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v) :
    T.depth u ≤ T.depth v := by
  rcases eq_or_depth_lt hT h with rfl | h
  · exact le_rfl
  · exact h.le

/-- An ancestor of the same depth is the vertex itself. -/
theorem eq_of_ancestor_of_depth_eq (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v)
    (hd : T.depth u = T.depth v) : u = v := by
  rcases eq_or_depth_lt hT h with h | h
  · exact h
  · omega

/-- The ancestors of one vertex form a chain. -/
theorem ancestor_total {u v x : Fin N} (hu : T.Ancestor u x) (hv : T.Ancestor v x) :
    T.Ancestor u v ∨ T.Ancestor v u := by
  unfold Forest.Ancestor at *
  induction hv generalizing u with
  | refl => exact Or.inl hu
  | @tail c y hvc hcy ih =>
    rcases (ReflTransGen.cases_tail_iff _ _ _).1 hu with rfl | ⟨c', hc', hc'y⟩
    · exact Or.inr (hvc.tail hcy)
    · have hcc : c' = c := Option.some_injective _ (hc'y.symm.trans hcy)
      subst hcc
      exact ih hc'

/-- Each vertex has an ancestor at each smaller depth. -/
private theorem exists_ancestor_depth (hT : T.IsDFS G) :
    ∀ (n : ℕ) (v : Fin N), T.depth v = n → ∀ k ≤ n, ∃ u, T.Ancestor u v ∧ T.depth u = k := by
  intro n
  induction n with
  | zero => intro v _ k hk; exact ⟨v, ancestor_refl v, by omega⟩
  | succ n ih =>
    intro v hv k hk
    rcases hp : T.parent v with _ | p
    · have := hT.1 v hp
      omega
    · have hd := depth_child hT hp
      rcases Nat.lt_or_ge k (n + 1) with hk' | hk'
      · obtain ⟨u, hu, hku⟩ := ih p (by omega) k (by omega)
        exact ⟨u, ancestor_trans hu (ancestor_of_parent hp), hku⟩
      · exact ⟨v, ancestor_refl v, by omega⟩

/-- Depths are smaller than the number of vertices, since the ancestors of a vertex at depth `d`
are `d + 1` distinct vertices. -/
theorem depth_lt (hT : T.IsDFS G) (v : Fin N) : T.depth v < N := by
  have h := exists_ancestor_depth hT (T.depth v) v rfl
  let f : Fin (T.depth v + 1) → Fin N := fun k =>
    Classical.choose (h k.val (Nat.lt_succ_iff.mp k.isLt))
  have hf : Function.Injective f := by
    intro a b hab
    have ha := (Classical.choose_spec (h a.val (Nat.lt_succ_iff.mp a.isLt))).2
    have hb := (Classical.choose_spec (h b.val (Nat.lt_succ_iff.mp b.isLt))).2
    apply Fin.ext
    rw [← ha, ← hb]
    exact congrArg T.depth hab
  have := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at this
  omega

/-- Every vertex lies below a root. -/
theorem exists_root (hT : T.IsDFS G) (v : Fin N) :
    ∃ r, T.parent r = none ∧ T.Ancestor r v := by
  obtain ⟨r, hr, hd⟩ := exists_ancestor_depth hT (T.depth v) v rfl 0 (Nat.zero_le _)
  refine ⟨r, ?_, hr⟩
  rcases hp : T.parent r with _ | p
  · rfl
  · have := depth_child hT hp
    omega

/-! ### Ports and leaves -/

/-- The original vertex at which a port is attached: the source of its back edge for a source
port, and the target for a target port (Part IV, Section 2). -/
def portVertex (p : Port N) : Fin N := if p.source then p.edge.1 else p.edge.2

@[simp] theorem portVertex_source (e : Arc N) : portVertex ⟨e, true⟩ = e.1 := by
  simp [portVertex]

@[simp] theorem portVertex_target (e : Arc N) : portVertex ⟨e, false⟩ = e.2 := by
  simp [portVertex]

/-- Part IV, Section 5: a leaf of the expanded tree is a port, or a dummy leaf added at an
original vertex "which otherwise has no child or port leaf". -/
inductive Leaf (N : ℕ) where
  | port : Port N → Leaf N
  | dummy : Fin N → Leaf N
  deriving DecidableEq

/-- The original vertex to which a leaf is attached. -/
@[expose] def Leaf.vertex : Leaf N → Fin N
  | .port p => portVertex p
  | .dummy v => v

/-- The port of a leaf, if the leaf is not a dummy leaf. -/
@[expose] def Leaf.toPort : Leaf N → Option (Port N)
  | .port p => some p
  | .dummy _ => none

/-- The leaves that occur: ports of back edges, and dummy leaves at vertices with an empty local
order. -/
@[expose] def Leaf.IsLeaf (T : Forest N) (G : SimpleGraph (Fin N)) (order : ContourOrder N) :
    Leaf N → Prop
  | .port p => T.BackEdge G p.edge
  | .dummy v => order v = []

@[simp] theorem Leaf.vertex_port (p : Port N) : (Leaf.port p).vertex = portVertex p := rfl

@[simp] theorem Leaf.vertex_dummy (v : Fin N) : (Leaf.dummy v).vertex = v := rfl

@[simp] theorem Leaf.isLeaf_port (p : Port N) :
    (Leaf.port p).IsLeaf T G order ↔ T.BackEdge G p.edge := Iff.rfl

theorem mem_order_child (hO : ValidContourOrder T G order) {v w : Fin N} :
    ContourEvent.child w ∈ order v ↔ T.parent w = some v :=
  (hO v).2 _

theorem mem_order_port (hO : ValidContourOrder T G order) {v : Fin N} {p : Port N} :
    ContourEvent.port p ∈ order v ↔ T.BackEdge G p.edge ∧ portVertex p = v := by
  rw [(hO v).2]
  obtain ⟨e, s⟩ := p
  unfold portVertex
  cases s <;> simp

/-- Part IV, Section 5: the leaves below a vertex, in contour order. A child incidence is
replaced by the leaves below the child, and an empty local order by one dummy leaf. The fuel
makes the definition total, as in `vertexContour`. -/
def leafContour (order : ContourOrder N) : ℕ → Fin N → List (Leaf N)
  | 0, _ => []
  | f + 1, v => if order v = [] then [.dummy v] else
      (order v).flatMap fun event => match event with
        | .child w => leafContour order f w
        | .port p => [.port p]

/-- The leaf word: the leaf contours of the roots in label order, as in `contourWord`. -/
noncomputable def leafWord (T : Forest N) (order : ContourOrder N) : List (Leaf N) :=
  ((Finset.univ.filter (fun v => T.parent v = none)).sort (· ≤ ·)).flatMap
    (leafContour order (N + 1))

private theorem vertexContour_eq (order : ContourOrder N) :
    ∀ f v, vertexContour order f v = (leafContour order f v).filterMap Leaf.toPort
  | 0, v => by simp [vertexContour, leafContour]
  | f + 1, v => by
    simp only [vertexContour, leafContour]
    split_ifs with h
    · simp [h, Leaf.toPort]
    · rw [List.filterMap_flatMap]
      congr 1
      funext event
      cases event with
      | child w => exact vertexContour_eq order f w
      | port p => simp [Leaf.toPort]

/-- Deleting the dummy leaves from the leaf word gives the contour word. -/
theorem contourWord_eq : contourWord T order = (leafWord T order).filterMap Leaf.toPort := by
  unfold contourWord leafWord
  rw [List.filterMap_flatMap]
  congr 1
  funext v
  exact vertexContour_eq order (N + 1) v

/-- With enough fuel, the leaf contour of `v` holds exactly the leaves attached below `v`. -/
theorem mem_leafContour (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    ∀ (f : ℕ) (v : Fin N) (ℓ : Leaf N), N < T.depth v + f →
      (ℓ ∈ leafContour order f v ↔ ℓ.IsLeaf T G order ∧ T.Ancestor v ℓ.vertex) := by
  intro f
  induction f with
  | zero => intro v ℓ h; have := depth_lt hT v; omega
  | succ f ih =>
    intro v ℓ hf
    rw [ancestor_iff]
    simp only [leafContour]
    split_ifs with h
    · rw [List.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨h, Or.inl rfl⟩
      · rintro ⟨hl, hv | ⟨c, hc, -⟩⟩
        · cases ℓ with
          | port p =>
            have := (mem_order_port hO).2 ⟨hl, hv.symm⟩
            simp [h] at this
          | dummy w => simp only [Leaf.vertex_dummy] at hv; rw [hv]
        · have := (mem_order_child hO).2 hc
          simp [h] at this
    · rw [List.mem_flatMap]
      constructor
      · rintro ⟨event, hev, hℓ⟩
        cases event with
        | child w =>
          have hw := (mem_order_child hO).1 hev
          have hd := depth_child hT hw
          obtain ⟨hl, ha⟩ := (ih w ℓ (by omega)).1 hℓ
          exact ⟨hl, Or.inr ⟨w, hw, ha⟩⟩
        | port p =>
          rw [List.mem_singleton] at hℓ
          subst hℓ
          obtain ⟨hb, hp⟩ := (mem_order_port hO).1 hev
          exact ⟨hb, Or.inl hp.symm⟩
      · rintro ⟨hl, hv | ⟨c, hc, ha⟩⟩
        · cases ℓ with
          | port p => exact ⟨.port p, (mem_order_port hO).2 ⟨hl, hv.symm⟩, by simp⟩
          | dummy w =>
            simp only [Leaf.vertex_dummy] at hv
            subst hv
            exact absurd hl h
        · have hd := depth_child hT hc
          exact ⟨.child c, (mem_order_child hO).2 hc, (ih c ℓ (by omega)).2 ⟨hl, ha⟩⟩

/-- With enough fuel, no leaf occurs twice in a leaf contour. -/
theorem nodup_leafContour (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    ∀ (f : ℕ) (v : Fin N), N < T.depth v + f → (leafContour order f v).Nodup := by
  intro f
  induction f with
  | zero => intro v h; have := depth_lt hT v; omega
  | succ f ih =>
    intro v hf
    simp only [leafContour]
    split_ifs with h
    · simp
    · rw [List.nodup_flatMap]
      refine ⟨fun event hev => ?_, (hO v).1.pairwise_of_forall_ne fun e₁ he₁ e₂ he₂ hne => ?_⟩
      · cases event with
        | child w =>
          have hd := depth_child hT ((mem_order_child hO).1 hev)
          exact ih w (by omega)
        | port p => simp
      · intro ℓ h₁ h₂
        cases e₁ with
        | child w₁ =>
          have hw₁ := (mem_order_child hO).1 he₁
          have hd₁ := depth_child hT hw₁
          have ha₁ := ((mem_leafContour hT hO f w₁ ℓ (by omega)).1 h₁).2
          cases e₂ with
          | child w₂ =>
            have hw₂ := (mem_order_child hO).1 he₂
            have hd₂ := depth_child hT hw₂
            have ha₂ := ((mem_leafContour hT hO f w₂ ℓ (by omega)).1 h₂).2
            apply hne
            rcases ancestor_total ha₁ ha₂ with h' | h'
            · rw [eq_of_ancestor_of_depth_eq hT h' (by omega)]
            · rw [eq_of_ancestor_of_depth_eq hT h' (by omega)]
          | port p =>
            simp only [List.mem_singleton] at h₂
            subst h₂
            have hp := ((mem_order_port hO).1 he₂).2
            simp only [Leaf.vertex_port, hp] at ha₁
            have := depth_le hT ha₁
            omega
        | port p =>
          simp only [List.mem_singleton] at h₁
          subst h₁
          cases e₂ with
          | child w₂ =>
            have hw₂ := (mem_order_child hO).1 he₂
            have hd₂ := depth_child hT hw₂
            have ha₂ := ((mem_leafContour hT hO f w₂ _ (by omega)).1 h₂).2
            have hp := ((mem_order_port hO).1 he₁).2
            simp only [Leaf.vertex_port, hp] at ha₂
            have := depth_le hT ha₂
            omega
          | port q =>
            simp only [List.mem_singleton, Leaf.port.injEq] at h₂
            exact hne (by rw [h₂])

theorem mem_roots {r : Fin N} :
    r ∈ (Finset.univ.filter (fun v => T.parent v = none)).sort (· ≤ ·) ↔ T.parent r = none := by
  simp [Finset.mem_sort]

/-- The leaf word holds exactly the ports of back edges and the dummy leaves. -/
theorem mem_leafWord (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (ℓ : Leaf N) :
    ℓ ∈ leafWord T order ↔ ℓ.IsLeaf T G order := by
  unfold leafWord
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨r, -, hℓ⟩
    exact ((mem_leafContour hT hO (N + 1) r ℓ (by omega)).1 hℓ).1
  · intro hl
    obtain ⟨r, hr, ha⟩ := exists_root hT ℓ.vertex
    exact ⟨r, mem_roots.2 hr, (mem_leafContour hT hO (N + 1) r ℓ (by omega)).2 ⟨hl, ha⟩⟩

/-- No leaf occurs twice in the leaf word. -/
theorem nodup_leafWord (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    (leafWord T order).Nodup := by
  unfold leafWord
  rw [List.nodup_flatMap]
  refine ⟨fun r _ => nodup_leafContour hT hO (N + 1) r (by omega),
    (Finset.sort_nodup _ _).pairwise_of_forall_ne fun r₁ hr₁ r₂ hr₂ hne ℓ h₁ h₂ => ?_⟩
  have ha₁ := ((mem_leafContour hT hO (N + 1) r₁ ℓ (by omega)).1 h₁).2
  have ha₂ := ((mem_leafContour hT hO (N + 1) r₂ ℓ (by omega)).1 h₂).2
  have hd₁ := hT.1 r₁ (mem_roots.1 hr₁)
  have hd₂ := hT.1 r₂ (mem_roots.1 hr₂)
  apply hne
  rcases ancestor_total ha₁ ha₂ with h' | h'
  · exact eq_of_ancestor_of_depth_eq hT h' (by omega)
  · exact (eq_of_ancestor_of_depth_eq hT h' (by omega)).symm

/-- The leaf contour of a vertex is one block of the leaf word. -/
theorem leafWord_split (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    ∀ (n : ℕ) (v : Fin N), T.depth v = n →
      ∃ A B, leafWord T order = A ++ leafContour order (N + 1 - n) v ++ B := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have hr : T.parent v = none := by
      rcases hp : T.parent v with _ | p
      · rfl
      · have := depth_child hT hp
        omega
    obtain ⟨s, t, hst⟩ := List.append_of_mem (mem_roots.2 hr)
    refine ⟨s.flatMap (leafContour order (N + 1)), t.flatMap (leafContour order (N + 1)), ?_⟩
    unfold leafWord
    rw [hst, List.flatMap_append, List.flatMap_cons, List.append_assoc, Nat.sub_zero]
  | succ n ih =>
    intro v hv
    rcases hp : T.parent v with _ | p
    · have := hT.1 v hp
      omega
    · have hd := depth_child hT hp
      have hvN := depth_lt hT v
      obtain ⟨A, B, hAB⟩ := ih p (by omega)
      have hmem : ContourEvent.child v ∈ order p := (mem_order_child hO).2 hp
      have hne : order p ≠ [] := List.ne_nil_of_mem hmem
      obtain ⟨s, t, hst⟩ := List.append_of_mem hmem
      have hfuel : N + 1 - n = (N + 1 - (n + 1)) + 1 := by omega
      rw [hfuel] at hAB
      simp only [leafContour, hne, ↓reduceIte] at hAB
      rw [hst, List.flatMap_append, List.flatMap_cons] at hAB
      let g : ContourEvent N → List (Leaf N) := fun event => match event with
        | .child w => leafContour order (N + 1 - (n + 1)) w
        | .port p => [.port p]
      refine ⟨A ++ s.flatMap g, t.flatMap g ++ B, ?_⟩
      rw [hAB]
      simp only [List.append_assoc]
      rfl

/-- Every vertex has a leaf attached below it: a port, or its dummy leaf. -/
theorem exists_leaf (hT : T.IsDFS G) (hO : ValidContourOrder T G order) :
    ∀ (m : ℕ) (v : Fin N), N - T.depth v = m →
      ∃ ℓ : Leaf N, ℓ.IsLeaf T G order ∧ T.Ancestor v ℓ.vertex := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v hv
    rcases hov : order v with _ | ⟨event, rest⟩
    · exact ⟨.dummy v, hov, ancestor_refl v⟩
    · have hev : event ∈ order v := by rw [hov]; exact List.mem_cons_self
      cases event with
      | child w =>
        have hw := (mem_order_child hO).1 hev
        have hd := depth_child hT hw
        have hwN := depth_lt hT w
        obtain ⟨ℓ, hl, ha⟩ := ih (N - T.depth w) (by omega) w rfl
        exact ⟨ℓ, hl, ancestor_trans (ancestor_of_parent hw) ha⟩
      | port p =>
        obtain ⟨hb, hp⟩ := (mem_order_port hO).1 hev
        exact ⟨.port p, hb, by simp only [Leaf.vertex_port, hp]; exact ancestor_refl v⟩

/-! ### Leaf indices and vertex intervals -/

/-- The number of a leaf: its index in the leaf word, counted from `0`. -/
noncomputable def leafIdx (T : Forest N) (order : ContourOrder N) (ℓ : Leaf N) : ℕ :=
  (leafWord T order).idxOf ℓ

/-- The indices of the leaves attached below a vertex. -/
noncomputable def descIdx (T : Forest N) (order : ContourOrder N) (v : Fin N) : Set ℕ :=
  {k | ∃ ℓ, (leafWord T order)[k]? = some ℓ ∧ T.Ancestor v ℓ.vertex}

/-- Part IV, Section 5: "let L(z) and R(z) be the smallest and largest indices of its
descendant leaves". This is `L(z)`. -/
noncomputable def leftIdx (T : Forest N) (order : ContourOrder N) (v : Fin N) : ℕ :=
  sInf (descIdx T order v)

/-- Part IV, Section 5: the largest index `R(z)` of a descendant leaf. -/
noncomputable def rightIdx (T : Forest N) (order : ContourOrder N) (v : Fin N) : ℕ :=
  sSup (descIdx T order v)

private theorem descIdx_eq_Ico (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (v : Fin N) :
    ∃ a b, a < b ∧ descIdx T order v = Set.Ico a b := by
  obtain ⟨A, B, hW⟩ := leafWord_split hT hO _ v rfl
  have hfuel : N < T.depth v + (N + 1 - T.depth v) := by omega
  have hmemC : ∀ ℓ, ℓ ∈ leafContour order (N + 1 - T.depth v) v ↔
      ℓ.IsLeaf T G order ∧ T.Ancestor v ℓ.vertex := fun ℓ => mem_leafContour hT hO _ v ℓ hfuel
  set C := leafContour order (N + 1 - T.depth v) v
  have hnd : (A ++ (C ++ B)).Nodup := by
    rw [← List.append_assoc, ← hW]
    exact nodup_leafWord hT hO
  have hCne : C ≠ [] := by
    obtain ⟨ℓ, hl, ha⟩ := exists_leaf hT hO _ v rfl
    intro h
    have := (hmemC ℓ).2 ⟨hl, ha⟩
    rw [h] at this
    simp at this
  have hpos := List.length_pos_iff.2 hCne
  refine ⟨A.length, A.length + C.length, by omega, ?_⟩
  ext k
  simp only [descIdx, Set.mem_Ico, Set.mem_ofPred_eq, hW, List.append_assoc]
  constructor
  · rintro ⟨ℓ, hk, ha⟩
    have hℓW : ℓ ∈ leafWord T order := by
      rw [hW, List.append_assoc]
      exact List.mem_of_getElem? hk
    have hℓC : ℓ ∈ C := (hmemC ℓ).2 ⟨(mem_leafWord hT hO ℓ).1 hℓW, ha⟩
    rw [List.nodup_append, List.nodup_append] at hnd
    by_contra hk'
    rcases Nat.lt_or_ge k A.length with h1 | h1
    · rw [List.getElem?_append_left h1] at hk
      exact hnd.2.2 ℓ (List.mem_of_getElem? hk) ℓ (List.mem_append_left _ hℓC) rfl
    · rw [List.getElem?_append_right h1,
        List.getElem?_append_right (by omega : C.length ≤ k - A.length)] at hk
      exact hnd.2.1.2.2 ℓ hℓC ℓ (List.mem_of_getElem? hk) rfl
  · rintro ⟨h1, h2⟩
    rw [List.getElem?_append_right h1, List.getElem?_append_left (by omega)]
    have hlt : k - A.length < C.length := by omega
    refine ⟨C[k - A.length], List.getElem?_eq_getElem hlt, ((hmemC _).1 (List.getElem_mem hlt)).2⟩

/-- Part IV, Section 2: "W(w) is a contiguous subword of W for every rooted subtree." The
descendant leaves of a vertex have exactly the indices from `L` to `R`. -/
theorem descIdx_eq_Icc (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (v : Fin N) :
    descIdx T order v = Set.Icc (leftIdx T order v) (rightIdx T order v) ∧
      leftIdx T order v ≤ rightIdx T order v := by
  obtain ⟨a, b, hab, h⟩ := descIdx_eq_Ico hT hO v
  have hl : leftIdx T order v = a := by
    unfold leftIdx
    rw [h]
    exact IsLeast.csInf_eq ⟨⟨le_rfl, hab⟩, fun x hx => hx.1⟩
  have hr : rightIdx T order v = b - 1 := by
    unfold rightIdx
    rw [h]
    exact IsGreatest.csSup_eq ⟨⟨by omega, by omega⟩, fun x hx => by have := hx.2; omega⟩
  refine ⟨?_, by omega⟩
  rw [h, hl, hr]
  ext x
  simp only [Set.mem_Ico, Set.mem_Icc]
  omega

theorem leftIdx_le_rightIdx (hT : T.IsDFS G) (hO : ValidContourOrder T G order) (v : Fin N) :
    leftIdx T order v ≤ rightIdx T order v :=
  (descIdx_eq_Icc hT hO v).2

/-- A leaf has its index between `L(v)` and `R(v)` exactly when it is attached below `v`. -/
theorem leafIdx_mem_iff (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {ℓ : Leaf N}
    (hℓ : ℓ ∈ leafWord T order) (v : Fin N) :
    (leftIdx T order v ≤ leafIdx T order ℓ ∧ leafIdx T order ℓ ≤ rightIdx T order v) ↔
      T.Ancestor v ℓ.vertex := by
  rw [← Set.mem_Icc, ← (descIdx_eq_Icc hT hO v).1]
  simp only [descIdx, Set.mem_ofPred_eq, leafIdx, List.getElem?_idxOf hℓ, Option.some.injEq]
  constructor
  · rintro ⟨ℓ', rfl, h⟩
    exact h
  · intro h
    exact ⟨ℓ, rfl, h⟩

/-- Each index between `L(v)` and `R(v)` is the index of a leaf attached below `v`. -/
theorem exists_leaf_of_mem (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {v : Fin N}
    {k : ℕ} (h₁ : leftIdx T order v ≤ k) (h₂ : k ≤ rightIdx T order v) :
    ∃ ℓ ∈ leafWord T order, leafIdx T order ℓ = k ∧ T.Ancestor v ℓ.vertex := by
  have hk : k ∈ descIdx T order v := by
    rw [(descIdx_eq_Icc hT hO v).1]
    exact ⟨h₁, h₂⟩
  obtain ⟨ℓ, hℓ, ha⟩ := hk
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hℓ
  exact ⟨_, List.getElem_mem hlt, (nodup_leafWord hT hO).idxOf_getElem k hlt, ha⟩

/-- The interval of a descendant lies inside the interval of its ancestor. -/
theorem interval_mono (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {v w : Fin N}
    (h : T.Ancestor v w) :
    leftIdx T order v ≤ leftIdx T order w ∧ rightIdx T order w ≤ rightIdx T order v := by
  have hw := leftIdx_le_rightIdx hT hO w
  obtain ⟨ℓ₁, h₁, e₁, a₁⟩ := exists_leaf_of_mem hT hO (le_refl (leftIdx T order w)) hw
  obtain ⟨ℓ₂, h₂, e₂, a₂⟩ := exists_leaf_of_mem hT hO hw (le_refl (rightIdx T order w))
  have k₁ := (leafIdx_mem_iff hT hO h₁ v).2 (ancestor_trans h a₁)
  have k₂ := (leafIdx_mem_iff hT hO h₂ v).2 (ancestor_trans h a₂)
  omega

/-- Vertices of which neither lies below the other have disjoint intervals. -/
theorem interval_disjoint (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {v w : Fin N}
    (h₁ : ¬ T.Ancestor v w) (h₂ : ¬ T.Ancestor w v) :
    rightIdx T order v < leftIdx T order w ∨ rightIdx T order w < leftIdx T order v := by
  by_contra hc
  have hv := leftIdx_le_rightIdx hT hO v
  have hw := leftIdx_le_rightIdx hT hO w
  obtain ⟨ℓ, hℓ, e, a⟩ := exists_leaf_of_mem hT hO (v := v)
    (k := max (leftIdx T order v) (leftIdx T order w)) (le_max_left _ _) (by omega)
  have a' := (leafIdx_mem_iff hT hO hℓ w).1 (by omega)
  rcases ancestor_total a a' with h | h
  · exact h₁ h
  · exact h₂ h

/-- Distinct vertices of the same depth have disjoint intervals. -/
theorem interval_disjoint_of_depth_eq (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    {v w : Fin N} (hne : v ≠ w) (hd : T.depth v = T.depth w) :
    rightIdx T order v < leftIdx T order w ∨ rightIdx T order w < leftIdx T order v :=
  interval_disjoint hT hO (fun h => hne (eq_of_ancestor_of_depth_eq hT h hd))
    (fun h => hne (eq_of_ancestor_of_depth_eq hT h hd.symm).symm)

/-- Distinct leaves of the word have distinct indices. -/
theorem leafIdx_injOn {ℓ ℓ' : Leaf N} (hℓ : ℓ ∈ leafWord T order)
    (h : leafIdx T order ℓ = leafIdx T order ℓ') : ℓ = ℓ' :=
  (List.idxOf_inj hℓ).1 h

/-! ### Nonalternation in the leaf word -/

private theorem idxOf_filterMap_lt_iff :
    ∀ (l : List (Leaf N)) {p q : Port N}, Leaf.port p ∈ l → Leaf.port q ∈ l →
      (l.idxOf (.port p) < l.idxOf (.port q) ↔
        (l.filterMap Leaf.toPort).idxOf p < (l.filterMap Leaf.toPort).idxOf q)
  | [], _, _, hp, _ => by simp at hp
  | x :: l, p, q, hp, hq => by
    cases x with
    | dummy w =>
      have hp' : Leaf.port p ∈ l := by simpa using hp
      have hq' : Leaf.port q ∈ l := by simpa using hq
      rw [List.idxOf_cons_ne _ (by simp), List.idxOf_cons_ne _ (by simp)]
      simp only [List.filterMap_cons, Leaf.toPort, Nat.succ_lt_succ_iff]
      exact idxOf_filterMap_lt_iff l hp' hq'
    | port c =>
      simp only [List.filterMap_cons, Leaf.toPort]
      by_cases hpc : c = p
      · subst hpc
        by_cases hqc : c = q
        · subst hqc
          simp
        · rw [List.idxOf_cons_self, List.idxOf_cons_self, List.idxOf_cons_ne _ (by simpa using hqc),
            List.idxOf_cons_ne _ hqc]
          simp
      · have hp' : Leaf.port p ∈ l := by simpa [Ne.symm hpc] using hp
        rw [List.idxOf_cons_ne _ (by simpa using hpc), List.idxOf_cons_ne _ hpc]
        by_cases hqc : c = q
        · subst hqc
          rw [List.idxOf_cons_self, List.idxOf_cons_self]
          simp
        · have hq' : Leaf.port q ∈ l := by simpa [Ne.symm hqc] using hq
          rw [List.idxOf_cons_ne _ (by simpa using hqc), List.idxOf_cons_ne _ hqc,
            Nat.succ_lt_succ_iff, Nat.succ_lt_succ_iff]
          exact idxOf_filterMap_lt_iff l hp' hq'

/-- The index of the port of a back edge in the leaf word. -/
@[expose] noncomputable def portIdx (T : Forest N) (order : ContourOrder N) (p : Port N) : ℕ :=
  leafIdx T order (.port p)

/-- The dummy leaves do not change the order of the ports, so the ports of two distinct back
edges do not alternate in the leaf word. -/
theorem not_alternating_portIdx (hT : T.IsDFS G) (hO : ValidContourOrder T G order)
    (hN : Nonalternating (contourWord T order)) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (hbc : b ≠ c) :
    ¬ AlternatingIndices (portIdx T order ⟨b, true⟩) (portIdx T order ⟨b, false⟩)
      (portIdx T order ⟨c, true⟩) (portIdx T order ⟨c, false⟩) := by
  have key : ∀ p q : Port N, T.BackEdge G p.edge → T.BackEdge G q.edge →
      (portIdx T order p < portIdx T order q ↔
        (contourWord T order).idxOf p < (contourWord T order).idxOf q) := by
    intro p q hp hq
    rw [contourWord_eq]
    exact idxOf_filterMap_lt_iff _ ((mem_leafWord hT hO _).2 hp) ((mem_leafWord hT hO _).2 hq)
  have h1 := key ⟨b, true⟩ ⟨b, false⟩ hb hb
  have h2 := key ⟨b, true⟩ ⟨c, true⟩ hb hc
  have h3 := key ⟨b, true⟩ ⟨c, false⟩ hb hc
  have h4 := key ⟨b, false⟩ ⟨b, true⟩ hb hb
  have h5 := key ⟨b, false⟩ ⟨c, true⟩ hb hc
  have h6 := key ⟨b, false⟩ ⟨c, false⟩ hb hc
  have h7 := key ⟨c, true⟩ ⟨b, true⟩ hc hb
  have h8 := key ⟨c, true⟩ ⟨b, false⟩ hc hb
  have h9 := key ⟨c, true⟩ ⟨c, false⟩ hc hc
  have h10 := key ⟨c, false⟩ ⟨b, true⟩ hc hb
  have h11 := key ⟨c, false⟩ ⟨b, false⟩ hc hb
  have h12 := key ⟨c, false⟩ ⟨c, true⟩ hc hc
  have hn := hN b c hbc
  unfold AlternatingIndices at hn ⊢
  omega

/-- Two distinct ports of back edges have distinct indices. -/
theorem portIdx_ne (hT : T.IsDFS G) (hO : ValidContourOrder T G order) {p q : Port N}
    (hp : T.BackEdge G p.edge) (hpq : p ≠ q) : portIdx T order p ≠ portIdx T order q := by
  intro h
  exact hpq (by simpa using leafIdx_injOn ((mem_leafWord hT hO (.port p)).2 hp) h)

end GraphMinor.LRPlanarity.Drawing
