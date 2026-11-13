module

public import Mathlib.Data.List.TakeWhile
public import Mathlib.Data.List.Infix
import Mathlib.Data.List.Basic

/-!
# Runs of non-nodes in a list (`Algorithm92Runs.lean`)

The algorithm of Graph Minors XIII, (9.2) (page 101) searches for its answer in `H ∪ F`, a graph
whose size is bounded "exept for divalent vertices". To make this search take constant time, we
shorten every long path of `H ∪ F` whose inner vertices have valency `2`. This file holds the list
facts behind that step.

A list `L` stands for a path, and a Boolean predicate `s` marks its *nodes*. A *run* of `L` is a
maximal block of consecutive vertices of `L` that are not nodes. When the first and the last
vertex of `L` are nodes, every run sits between two nodes: `L = A ++ a :: R ++ c :: B` with `a`
and `c` nodes and no node in `R`. The function `run s L y` returns the run that contains `y`.

* `run_eq_of_decomp`: if `L` has no repeated vertex and `L = A ++ a :: R ++ c :: B` as above, then
  `run s L y = R` for every `y ∈ R`. So two runs that share a vertex are equal.
* `exists_decomp`: every vertex `y` of `L` that is not a node lies in such a block `R`.
* `Consec L u v` says that `u` is followed by `v` in `L`; `consec_iff_mem_zip` links it with the
  form `(u, v) ∈ L.zip (L.drop 1)` used in the definition of walls.
-/

public section

namespace GraphMinor.Compute

namespace Alg92

variable {α : Type*}

/-- `u` is followed by `v` somewhere in the list `L`. -/
@[expose] def Consec (L : List α) (u v : α) : Prop :=
  ∃ A B : List α, L = A ++ u :: v :: B

theorem consec_iff_mem_zip {u v : α} :
    ∀ {L : List α}, (u, v) ∈ L.zip (L.drop 1) ↔ Consec L u v
  | [] => by simp [Consec]
  | [a] => by
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_nil_right, List.not_mem_nil,
      false_iff]
    rintro ⟨A, B, h⟩
    cases A with
    | nil => simp at h
    | cons x A => cases A <;> simp at h
  | a :: b :: rest => by
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons,
      Prod.mk.injEq]
    have ih := consec_iff_mem_zip (u := u) (v := v) (L := b :: rest)
    simp only [List.drop_succ_cons, List.drop_zero] at ih
    rw [ih]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨A, B, h⟩)
      · exact ⟨[], rest, rfl⟩
      · exact ⟨a :: A, B, by rw [h]; rfl⟩
    · rintro ⟨A, B, h⟩
      cases A with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        exact Or.inl ⟨h.1.symm, h.2.1.symm⟩
      | cons x A =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact Or.inr ⟨A, B, h.2⟩

theorem Consec.cons {L : List α} {u v : α} (a : α) (h : Consec L u v) : Consec (a :: L) u v := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨a :: A, B, rfl⟩

theorem Consec.append_left {L : List α} {u v : α} (A : List α) (h : Consec L u v) :
    Consec (A ++ L) u v := by
  obtain ⟨A', B, rfl⟩ := h
  exact ⟨A ++ A', B, by simp⟩

theorem Consec.append_right {L : List α} {u v : α} (B : List α) (h : Consec L u v) :
    Consec (L ++ B) u v := by
  obtain ⟨A, B', rfl⟩ := h
  exact ⟨A, B' ++ B, by simp⟩

theorem Consec.infix {L M : List α} {u v : α} (h : Consec L u v) (hLM : L <:+: M) :
    Consec M u v := by
  obtain ⟨A, B, rfl⟩ := hLM
  exact (h.append_left A).append_right B

theorem Consec.mem_left {L : List α} {u v : α} (h : Consec L u v) : u ∈ L := by
  obtain ⟨A, B, rfl⟩ := h
  simp

theorem Consec.mem_right {L : List α} {u v : α} (h : Consec L u v) : v ∈ L := by
  obtain ⟨A, B, rfl⟩ := h
  simp

theorem consec_reverse {L : List α} {u v : α} : Consec L.reverse u v ↔ Consec L v u := by
  constructor
  · rintro ⟨A, B, h⟩
    refine ⟨B.reverse, A.reverse, ?_⟩
    have := congrArg List.reverse h
    simpa using this
  · rintro ⟨A, B, rfl⟩
    exact ⟨B.reverse, A.reverse, by simp⟩

/-- In a list without repeated elements, an element splits the list in only one way. -/
theorem nodup_split_unique [DecidableEq α] {L A B A' B' : List α} {y : α} (hL : L.Nodup)
    (h : L = A ++ y :: B) (h' : L = A' ++ y :: B') : A = A' ∧ B = B' := by
  subst h
  have hyA : y ∉ A := by
    intro hy
    rw [List.nodup_append] at hL
    exact hL.2.2 y hy y List.mem_cons_self rfl
  have hyA' : y ∉ A' := by
    intro hy
    rw [h', List.nodup_append] at hL
    exact hL.2.2 y hy y List.mem_cons_self rfl
  have hlen : A.length = A'.length := by
    have h1 : (A ++ y :: B).idxOf y = A.length := by
      rw [List.idxOf_append_of_notMem hyA]; simp
    have h2 : (A' ++ y :: B').idxOf y = A'.length := by
      rw [List.idxOf_append_of_notMem hyA']; simp
    rw [← h1, h', h2]
  have := List.append_inj h' hlen
  exact ⟨this.1, (List.cons.inj this.2).2⟩

/-- A pair `u, v` that follows each other in a list without repeated elements, when `u` is a
known element `A ++ u :: B`: then `v` is the first element of `B`. -/
theorem Consec.eq_of_split [DecidableEq α] {L A B : List α} {u v : α} (hL : L.Nodup)
    (hc : Consec L u v) (h : L = A ++ u :: B) : B.head? = some v := by
  obtain ⟨A', B', h'⟩ := hc
  have := nodup_split_unique hL h h'
  rw [this.2]
  rfl

/-- In a list without repeated elements, a pair `u, v` that follows each other, when `v` is a known
element `A ++ v :: B`: then `u` is the last element of `A`. -/
theorem Consec.eq_of_split' [DecidableEq α] {L A B : List α} {u v : α} (hL : L.Nodup)
    (hc : Consec L u v) (h : L = A ++ v :: B) : A.getLast? = some u := by
  obtain ⟨A', B', h'⟩ := hc
  have h'' : L = (A' ++ [u]) ++ v :: B' := by rw [h']; simp
  have := nodup_split_unique hL h h''
  rw [this.1]
  simp

variable (s : α → Bool)

/-- The run of `L` that contains `y`: the vertices around `y` up to (and not including) the
nearest nodes on each side. -/
@[expose] def run [DecidableEq α] (L : List α) (y : α) : List α :=
  ((L.take (L.idxOf y)).reverse.takeWhile (fun z => !s z)).reverse ++
    y :: (L.drop (L.idxOf y + 1)).takeWhile (fun z => !s z)

/-- The node before the run of `y` in `L` (or `y` if there is none). -/
@[expose] def runPrev [DecidableEq α] (L : List α) (y : α) : α :=
  (((L.take (L.idxOf y)).reverse.dropWhile (fun z => !s z)).head?).getD y

/-- The node after the run of `y` in `L` (or `y` if there is none). -/
@[expose] def runNext [DecidableEq α] (L : List α) (y : α) : α :=
  (((L.drop (L.idxOf y + 1)).dropWhile (fun z => !s z)).head?).getD y

variable {s}

private theorem take_drop_of_decomp [DecidableEq α] {L A R₁ R₂ B : List α} {a c y : α}
    (hL : L.Nodup) (hdec : L = A ++ a :: (R₁ ++ y :: R₂) ++ c :: B) :
    L.take (L.idxOf y) = A ++ a :: R₁ ∧ L.drop (L.idxOf y + 1) = R₂ ++ c :: B := by
  have hsplit : L = (A ++ a :: R₁) ++ y :: (R₂ ++ c :: B) := by rw [hdec]; simp
  have hyA : y ∉ A ++ a :: R₁ := by
    intro hy'
    rw [hsplit, List.nodup_append] at hL
    exact hL.2.2 y hy' y List.mem_cons_self rfl
  have hidx : L.idxOf y = (A ++ a :: R₁).length := by
    rw [hsplit, List.idxOf_append_of_notMem hyA]; simp
  refine ⟨by rw [hidx, hsplit, List.take_left], ?_⟩
  rw [hidx, hsplit, show (A ++ a :: R₁).length + 1 = ((A ++ a :: R₁) ++ [y]).length by
      simp; omega,
    show (A ++ a :: R₁) ++ y :: (R₂ ++ c :: B) = ((A ++ a :: R₁) ++ [y]) ++ (R₂ ++ c :: B) by
      simp, List.drop_left]

private theorem allNot_of_decomp {R₁ R₂ : List α} {y : α}
    (hR : ∀ z ∈ R₁ ++ y :: R₂, s z = false) :
    (∀ z ∈ R₁.reverse, (!s z) = true) ∧ (∀ z ∈ R₂, (!s z) = true) := by
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [List.mem_reverse] at hz
    simp [hR z (by simp [hz])]
  · simp [hR z (by simp [hz])]

/-- If `L = A ++ a :: R ++ c :: B` has no repeated element, `a` and `c` are nodes and `R` has no
node, then the run of every `y ∈ R` is `R`. -/
theorem run_eq_of_decomp [DecidableEq α] {L A R B : List α} {a c y : α} (hL : L.Nodup)
    (hdec : L = A ++ a :: R ++ c :: B) (ha : s a = true) (hc : s c = true)
    (hR : ∀ z ∈ R, s z = false) (hy : y ∈ R) : run s L y = R := by
  obtain ⟨R₁, R₂, rfl⟩ := List.append_of_mem hy
  obtain ⟨htake, hdrop⟩ := take_drop_of_decomp hL hdec
  obtain ⟨hR₁, hR₂⟩ := allNot_of_decomp hR
  unfold run
  rw [htake, hdrop]
  have e1 : (A ++ a :: R₁).reverse = R₁.reverse ++ a :: A.reverse := by simp
  rw [e1, List.takeWhile_append_of_pos hR₁, List.takeWhile_append_of_pos hR₂]
  simp [ha, hc]

/-- Under the same conditions, the node before the run of `y` is `a`. -/
theorem runPrev_eq_of_decomp [DecidableEq α] {L A R B : List α} {a c y : α} (hL : L.Nodup)
    (hdec : L = A ++ a :: R ++ c :: B) (ha : s a = true)
    (hR : ∀ z ∈ R, s z = false) (hy : y ∈ R) : runPrev s L y = a := by
  obtain ⟨R₁, R₂, rfl⟩ := List.append_of_mem hy
  obtain ⟨htake, -⟩ := take_drop_of_decomp hL hdec
  obtain ⟨hR₁, -⟩ := allNot_of_decomp hR
  unfold runPrev
  rw [htake]
  have e1 : (A ++ a :: R₁).reverse = R₁.reverse ++ a :: A.reverse := by simp
  rw [e1, List.dropWhile_append_of_pos hR₁]
  simp [ha]

/-- Under the same conditions, the node after the run of `y` is `c`. -/
theorem runNext_eq_of_decomp [DecidableEq α] {L A R B : List α} {a c y : α} (hL : L.Nodup)
    (hdec : L = A ++ a :: R ++ c :: B) (hc : s c = true)
    (hR : ∀ z ∈ R, s z = false) (hy : y ∈ R) : runNext s L y = c := by
  obtain ⟨R₁, R₂, rfl⟩ := List.append_of_mem hy
  obtain ⟨-, hdrop⟩ := take_drop_of_decomp hL hdec
  obtain ⟨-, hR₂⟩ := allNot_of_decomp hR
  unfold runNext
  rw [hdrop, List.dropWhile_append_of_pos hR₂]
  simp [hc]

theorem head_of_dropWhile_eq_cons {p : α → Bool} {l D : List α} {a : α}
    (h : l.dropWhile p = a :: D) : p a = false := by
  have h1 := List.head_dropWhile_not p (l := l) (by simp [h])
  simpa only [h, List.head_cons] using h1

/-- Every vertex `y` of `L` that is not a node lies in a block `R` of non-nodes between two nodes,
when the first and the last vertex of `L` are nodes. -/
theorem exists_decomp {L : List α} {y : α} (hy : y ∈ L) (hys : s y = false)
    (hhead : ∀ a, L.head? = some a → s a = true)
    (hlast : ∀ c, L.getLast? = some c → s c = true) :
    ∃ A a R c B, L = A ++ a :: R ++ c :: B ∧ s a = true ∧ s c = true ∧
      (∀ z ∈ R, s z = false) ∧ y ∈ R := by
  obtain ⟨A', B', rfl⟩ := List.append_of_mem hy
  -- the part before `y`
  set T := A'.reverse.takeWhile (fun z => !s z) with hT
  set D := A'.reverse.dropWhile (fun z => !s z) with hD
  have hTD : T ++ D = A'.reverse := List.takeWhile_append_dropWhile
  have hDne : D ≠ [] := by
    intro hD0
    rw [hD0, List.append_nil] at hTD
    have hall : ∀ z ∈ A', s z = false := by
      intro z hz
      have hz' : z ∈ T := by rw [hTD]; simpa using hz
      have := List.mem_takeWhile_imp hz'
      simpa using this
    cases A' with
    | nil => exact absurd (hhead y (by simp)) (by simp [hys])
    | cons x A'' =>
      have := hhead x (by simp)
      rw [hall x (by simp)] at this
      exact Bool.false_ne_true this
  obtain ⟨a, D', hD'⟩ : ∃ a D', D = a :: D' := List.exists_cons_of_ne_nil hDne
  have ha : s a = true := by
    have := head_of_dropWhile_eq_cons (hD.symm.trans hD')
    simpa using this
  -- the part after `y`
  set U := B'.takeWhile (fun z => !s z) with hU
  set E := B'.dropWhile (fun z => !s z) with hE
  have hUE : U ++ E = B' := List.takeWhile_append_dropWhile
  have hEne : E ≠ [] := by
    intro hE0
    rw [hE0, List.append_nil] at hUE
    have hall : ∀ z ∈ B', s z = false := by
      intro z hz
      have hz' : z ∈ U := by rw [hUE]; exact hz
      have := List.mem_takeWhile_imp hz'
      simpa using this
    have hl : (A' ++ y :: B').getLast? = some ((y :: B').getLast (by simp)) := by
      rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_eq_some_getLast]
    have := hlast _ hl
    have hmem : (y :: B').getLast (by simp) ∈ y :: B' := List.getLast_mem _
    rcases List.mem_cons.mp hmem with h | h
    · rw [h, hys] at this; exact Bool.false_ne_true this
    · rw [hall _ h] at this; exact Bool.false_ne_true this
  obtain ⟨c, E', hE'⟩ : ∃ c E', E = c :: E' := List.exists_cons_of_ne_nil hEne
  have hc : s c = true := by
    have := head_of_dropWhile_eq_cons (hE.symm.trans hE')
    simpa using this
  refine ⟨D'.reverse, a, T.reverse ++ y :: U, c, E', ?_, ha, hc, ?_, by simp⟩
  · have hA' : A' = D'.reverse ++ a :: T.reverse := by
      have := congrArg List.reverse hTD
      rw [List.reverse_reverse, hD'] at this
      rw [← this]; simp
    rw [hA', ← hUE, hE']
    simp
  · intro z hz
    simp only [List.mem_append, List.mem_reverse, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · have := List.mem_takeWhile_imp hz; simpa using this
    · exact hys
    · have := List.mem_takeWhile_imp hz; simpa using this

/-- Two consecutive elements that both pass a filter stay consecutive after filtering. -/
theorem Consec.filter {L : List α} {a b : α} (p : α → Bool) (h : Consec L a b) (ha : p a = true)
    (hb : p b = true) : Consec (L.filter p) a b := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨A.filter p, B.filter p, by simp [List.filter_append, ha, hb]⟩

theorem Consec.map {β : Type*} {L : List α} {a b : α} (f : α → β) (h : Consec L a b) :
    Consec (L.map f) (f a) (f b) := by
  obtain ⟨A, B, rfl⟩ := h
  exact ⟨A.map f, B.map f, by simp⟩

theorem exists_of_consec_map {β : Type*} {f : α → β} {i j : β} :
    ∀ {L : List α}, Consec (L.map f) i j → ∃ a b, Consec L a b ∧ f a = i ∧ f b = j
  | [], ⟨A, B, h⟩ => by cases A <;> simp at h
  | [x], ⟨A, B, h⟩ => by
    cases A with
    | nil => simp at h
    | cons y A => cases A <;> simp at h
  | x :: y :: rest, ⟨A, B, h⟩ => by
    cases A with
    | nil =>
      simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
      exact ⟨x, y, ⟨[], rest, rfl⟩, h.1, h.2.1⟩
    | cons z A =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨a, b, hab, ha, hb⟩ :=
        exists_of_consec_map (L := y :: rest) ⟨A, B, by simpa using h.2⟩
      exact ⟨a, b, hab.cons x, ha, hb⟩

/-- The first element of a filtered list: everything before it fails the filter. -/
theorem exists_of_head?_filter {p : α → Bool} {v : α} :
    ∀ {L : List α}, (L.filter p).head? = some v →
      ∃ M Y, L = M ++ v :: Y ∧ ∀ m ∈ M, p m = false
  | [], h => by simp at h
  | x :: L, h => by
    by_cases hx : p x = true
    · simp only [List.filter_cons, hx, ite_true, List.head?_cons, Option.some.injEq] at h
      exact ⟨[], L, by simp [h], by simp⟩
    · simp only [List.filter_cons, hx, ite_false, Bool.false_eq_true] at h
      obtain ⟨M, Y, hL, hM⟩ := exists_of_head?_filter h
      refine ⟨x :: M, Y, by simp [hL], ?_⟩
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · simpa using hx
      · exact hM m hm

/-- Two consecutive elements of a filtered list: everything between them fails the filter. -/
theorem exists_of_consec_filter {p : α → Bool} {u v : α} :
    ∀ {L : List α}, Consec (L.filter p) u v →
      ∃ X M Y, L = X ++ u :: M ++ v :: Y ∧ ∀ m ∈ M, p m = false
  | [], ⟨A, B, h⟩ => by cases A <;> simp at h
  | x :: L, hc => by
    by_cases hx : p x = true
    · have hf : (x :: L).filter p = x :: L.filter p := by simp [hx]
      rw [hf] at hc
      obtain ⟨A, B, h⟩ := hc
      cases A with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, hL⟩ := h
        obtain ⟨M, Y, hLM, hM⟩ := exists_of_head?_filter (p := p) (v := v) (L := L)
          (by rw [hL]; rfl)
        exact ⟨[], M, Y, by simp [hLM], hM⟩
      | cons z A =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨X, M, Y, hL, hM⟩ := exists_of_consec_filter (L := L) ⟨A, B, h.2⟩
        exact ⟨x :: X, M, Y, by simp [hL], hM⟩
    · have hf : (x :: L).filter p = L.filter p := by simp [hx]
      rw [hf] at hc
      obtain ⟨X, M, Y, hL, hM⟩ := exists_of_consec_filter hc
      exact ⟨x :: X, M, Y, by simp [hL], hM⟩

/-! ### Loop erasure -/

/-- Loop erasure: a walk with repeated vertices is shortened to a path with the same ends, by
cutting out the part between two visits of a vertex. -/
@[expose] def loopErase [DecidableEq α] : List α → List α
  | [] => []
  | x :: rest =>
    if x ∈ loopErase rest then (loopErase rest).dropWhile (fun y => decide (y ≠ x))
    else x :: loopErase rest

section LoopErase

variable [DecidableEq α]

theorem dropWhile_ne_eq_cons {x : α} : ∀ {r : List α}, x ∈ r →
    ∃ t, r.dropWhile (fun y => decide (y ≠ x)) = x :: t ∧ x :: t <:+ r
  | [], h => absurd h (List.not_mem_nil)
  | y :: r, h => by
    by_cases hyx : y = x
    · subst hyx
      exact ⟨r, by simp, List.suffix_refl _⟩
    · have hx : x ∈ r := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hyx
        · exact h
      obtain ⟨t, ht, hsuf⟩ := dropWhile_ne_eq_cons hx
      refine ⟨t, ?_, hsuf.trans (List.suffix_cons _ _)⟩
      rw [List.dropWhile_cons_of_pos (by simpa using hyx)]
      exact ht

theorem mem_of_mem_loopErase : ∀ {L : List α} {y : α}, y ∈ loopErase L → y ∈ L
  | [], _, h => by simp [loopErase] at h
  | x :: rest, y, h => by
    unfold loopErase at h
    split_ifs at h with hx
    · obtain ⟨t, ht, hsuf⟩ := dropWhile_ne_eq_cons hx
      rw [ht] at h
      exact List.mem_cons_of_mem _ (mem_of_mem_loopErase (hsuf.subset h))
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_mem_loopErase h)

theorem nodup_loopErase : ∀ L : List α, (loopErase L).Nodup
  | [] => by simp [loopErase]
  | x :: rest => by
    unfold loopErase
    split_ifs with hx
    · obtain ⟨t, ht, hsuf⟩ := dropWhile_ne_eq_cons hx
      rw [ht]
      exact (nodup_loopErase rest).sublist hsuf.sublist
    · exact List.nodup_cons.mpr ⟨hx, nodup_loopErase rest⟩

theorem head?_loopErase : ∀ L : List α, (loopErase L).head? = L.head?
  | [] => by simp [loopErase]
  | x :: rest => by
    unfold loopErase
    split_ifs with hx
    · obtain ⟨t, ht, -⟩ := dropWhile_ne_eq_cons hx
      rw [ht]; rfl
    · rfl

theorem loopErase_eq_nil_iff {L : List α} : loopErase L = [] ↔ L = [] := by
  constructor
  · intro h
    have := head?_loopErase L
    rw [h] at this
    exact List.head?_eq_none_iff.mp this.symm
  · rintro rfl; simp [loopErase]

omit [DecidableEq α] in
theorem getLast?_cons_of_ne_nil {x : α} {L : List α} (h : L ≠ []) :
    (x :: L).getLast? = L.getLast? := by
  obtain ⟨y, L', rfl⟩ := List.exists_cons_of_ne_nil h
  exact List.getLast?_cons_cons

theorem getLast?_loopErase : ∀ L : List α, (loopErase L).getLast? = L.getLast?
  | [] => by simp [loopErase]
  | x :: rest => by
    have ih := getLast?_loopErase rest
    unfold loopErase
    split_ifs with hx
    · obtain ⟨t, ht, hsuf⟩ := dropWhile_ne_eq_cons hx
      rw [ht]
      have hrest : rest ≠ [] := by
        intro h; subst h; simp [loopErase] at hx
      obtain ⟨u, hu⟩ := hsuf
      have e1 : (x :: t).getLast? = (loopErase rest).getLast? := by
        rw [← hu, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rw [e1, ih, getLast?_cons_of_ne_nil hrest]
    · by_cases hrest : rest = []
      · subst hrest; simp [loopErase]
      · have hne : loopErase rest ≠ [] := by rwa [Ne, loopErase_eq_nil_iff]
        rw [getLast?_cons_of_ne_nil hne, ih, getLast?_cons_of_ne_nil hrest]

theorem Consec.of_loopErase : ∀ {L : List α} {u v : α}, Consec (loopErase L) u v → Consec L u v
  | [], u, v, h => by
    obtain ⟨A, B, h⟩ := h; simp [loopErase] at h
  | x :: rest, u, v, h => by
    unfold loopErase at h
    split_ifs at h with hx
    · obtain ⟨t, ht, hsuf⟩ := dropWhile_ne_eq_cons hx
      rw [ht] at h
      exact (Consec.of_loopErase (h.infix hsuf.isInfix)).cons x
    · obtain ⟨A, B, hAB⟩ := h
      cases A with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hAB
        obtain ⟨rfl, hr⟩ := hAB
        have hh := head?_loopErase rest
        rw [hr] at hh
        cases rest with
        | nil => simp at hh
        | cons y rest' =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          exact ⟨[], rest', rfl⟩
      | cons z A =>
        simp only [List.cons_append, List.cons.injEq] at hAB
        exact (Consec.of_loopErase ⟨A, B, hAB.2⟩).cons x

end LoopErase

end Alg92

end GraphMinor.Compute
