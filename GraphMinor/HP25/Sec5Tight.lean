module

public import GraphMinor.HP25.Prop53
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.WebSplit
import GraphMinor.HP25.SplitTools

/-!
# Tight paths and Claim 5.5

Lemma 5.4 of Humeau and Pous (page 19) is false as printed, even for an induced `C`-path `P`
(`Checks/HP25Examples.lean`, namespaces `Ex54` and `Ex54b`). The correction restricts it to *tight*
paths (`IsTight`): every component of `G - (C ∪ P)` with no neighbour in `P̊₁ ∪ P̊₂` has its
neighbours on `P` among two consecutive vertices of `P`.

This file proves the first step of the proof of Lemma 5.4 for such paths, Claim 5.5 (page 19):
"The edge $y_jy_r$ is safe in $G$." The paper's proof reads: "As vertices $y_t$ with $j<t<r$ have no
$P$-sides, $\{y_j,y_r\}$ separates them from $C$. Hence, since $R$ has its endpoints on $C$, $R$ does
not intersect $y_jPy_r$. The pair $(Qy_jPy_rQ,R)$ is a crossing of $C$ in $G$, a contradiction."
The separation step is the one that fails without tightness. With it, we prove:

* `tightZone_closed`: let `Z` be the set of the vertices `y_t` (`j < t < r`) and of the vertices off
  `C ∪ P` joined to one of them by a path with no inner vertex in `C ∪ P`. Every neighbour of a vertex
  of `Z` is in `Z`, or is `y_j` or `y_r`; and `Z` misses `C` (`tightZone_not_mem`);
* `claim_5_5_tight`: the edge `y_j y_r` is safe.

The vertices `y_j` and `y_r` are written `y` and `z`, and the vertices strictly between them on `P`
form the list `N`, so that `P.support = L₁ ++ y :: N ++ z :: L₂`. The claim only uses that the
vertices of `N` are on no side.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- A `C`-path with vertex list `l` (and sides `A`, `B`) is *tight* when every component of
`G - (C ∪ l)` that has no neighbour in `A ∪ B` has all its neighbours on `l` among two consecutive
entries of `l`. A vertex `u` off `C ∪ l` stands for its component: the component has a neighbour in
`A ∪ B` when `u` is joined to `A ∪ B` by a path with no inner vertex in `C ∪ l`, and its neighbours on
`l` are the entries of `l` joined to `u` in this way. This is the condition under which we prove
Lemma 5.4 (page 19), which fails without it. -/
@[expose] def IsTight (G : SimpleGraph V) (C A B l : List V) : Prop :=
  ∀ u, u ∉ C → u ∉ l →
    ¬ IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ l} u {x | x ∈ A ∨ x ∈ B} →
    ∃ v w, IsListEdge l v w ∧
      ∀ p ∈ l, IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ l} u {p} → p = v ∨ p = w

/-- The vertices of `N` and the vertices outside `X` joined to a vertex of `N` by a path with no
inner vertex in `X`. -/
@[expose] def tightZone (G : SimpleGraph V) (X : Set V) (N : List V) : Set V :=
  {v | v ∈ N ∨ (v ∉ X ∧ ∃ m ∈ N, IsConnectedAvoiding G X v {m})}

/-- In a list without repetition `L₁ ++ y :: N ++ z :: L₂`, the entries next to an entry of `N`
lie in `y :: N ++ [z]`. -/
theorem IsListEdge.mem_window [DecidableEq V] {L₁ N L₂ : List V} {y z m w : V}
    (hnd : (L₁ ++ y :: N ++ z :: L₂).Nodup) (hm : m ∈ N)
    (h : IsListEdge (L₁ ++ y :: N ++ z :: L₂) m w) : w ∈ y :: N ++ [z] := by
  set l := L₁ ++ y :: N ++ z :: L₂ with hl
  have hl' : l = L₁ ++ (y :: N ++ [z]) ++ L₂ := by simp [hl]
  have hmL₁ : m ∉ L₁ := fun h' => by
    rw [hl, List.append_assoc] at hnd
    exact List.disjoint_of_nodup_append hnd h' (by simp [hm])
  have hmy : m ≠ y := by
    rintro rfl
    rw [hl, List.append_assoc, List.nodup_append] at hnd
    have := hnd.2.1
    simp only [List.cons_append, List.nodup_cons, List.mem_append, List.mem_cons] at this
    exact this.1 (Or.inl hm)
  have hidx : l.idxOf m = L₁.length + 1 + N.idxOf m := by
    rw [hl, List.append_assoc, List.idxOf_append_of_notMem hmL₁, List.cons_append,
      List.idxOf_cons_ne _ (Ne.symm hmy), List.idxOf_append_of_mem hm]
    omega
  have hNi : N.idxOf m < N.length := List.idxOf_lt_length_of_mem hm
  have hw : w ∈ l := h.mem_right
  have e := h.idxOf hnd
  have hnd' : (L₁ ++ (y :: N ++ [z]) ++ L₂).Nodup := hl' ▸ hnd
  rw [hl'] at hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · -- `w ∈ L₁` has a small index
      have : l.idxOf w = L₁.idxOf w := by
        rw [hl', List.append_assoc, List.idxOf_append_of_mem hw]
      have := List.idxOf_lt_length_of_mem hw
      omega
    · exact hw
  · -- `w ∈ L₂` has a large index
    have hw1 : w ∉ L₁ := fun h' =>
      List.disjoint_of_nodup_append hnd' (List.mem_append_left _ h') hw
    have hw2 : w ∉ y :: N ++ [z] := fun h' =>
      List.disjoint_of_nodup_append hnd' (List.mem_append_right _ h') hw
    have : l.idxOf w = L₁.length + ((y :: N ++ [z]).length + L₂.idxOf w) := by
      rw [hl', List.append_assoc, List.idxOf_append_of_notMem hw1,
        List.idxOf_append_of_notMem hw2]
    simp only [List.cons_append, List.length_cons, List.length_append]
      at this
    omega

variable {C A B L₁ N L₂ : List V} {a b y z : V} {k : ℕ} {P : G.Walk a b}

/-- The membership in `C` read off a rotation `a A b B` of `C`. -/
theorem mem_of_rotate (hrot : C.rotate k = a :: A ++ b :: B) {w : V} (hw : w ∈ C) :
    w = a ∨ w ∈ A ∨ w = b ∨ w ∈ B := by
  have : w ∈ a :: A ++ b :: B := hrot ▸ List.mem_rotate.mpr hw
  simpa using this

/-- An entry of `N` is an inner vertex of `P`, so it is not on `C`. -/
theorem not_mem_C_of_mem_window (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    {m : V} (hm : m ∈ N) : m ∉ C := by
  have hnd : (L₁ ++ y :: N ++ z :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hmP : m ∈ P.support := by rw [hsupp]; simp [hm]
  have hma : m ≠ a := by
    rintro rfl
    have h0 : P.support.head? = some m := by rw [← Walk.cons_tail_support]; rfl
    rw [hsupp] at h0
    cases L₁ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.head?_cons, Option.some.injEq] at h0
      subst h0
      simp only [List.nil_append, List.cons_append, List.nodup_cons, List.mem_append,
        List.mem_cons] at hnd
      exact hnd.1 (Or.inl hm)
    | cons x t =>
      simp only [List.cons_append, List.append_assoc, List.head?_cons, Option.some.injEq] at h0
      subst h0
      simp only [List.cons_append, List.append_assoc, List.nodup_cons, List.mem_append,
        List.mem_cons] at hnd
      exact hnd.1 (Or.inr (Or.inr (Or.inl hm)))
  have hmb : m ≠ b := by
    rintro rfl
    have h0 : P.support.getLast? = some m := by
      rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
    rw [hsupp] at h0
    have e : L₁ ++ y :: N ++ z :: L₂ = (L₁ ++ y :: N) ++ (z :: L₂) := by simp
    rw [e] at hnd h0
    rw [List.getLast?_append_of_ne_nil _ (by simp)] at h0
    have hmz : m ∈ z :: L₂ := List.mem_of_getLast? h0
    exact List.disjoint_of_nodup_append hnd (by simp [hm]) hmz
  exact (hP.2.2.2 m hmP hma hmb).1

/-- The *window condition* for the stretch `y N z` of `P`: a vertex off `C ∪ P` that is joined to
neither `A` nor `B` away from `C ∪ P` (so it lies in a component of the third kind), and is joined to a
vertex of `N` away from `C ∪ P`, is joined away from `C ∪ P` to no vertex of `P` outside `y N z`. -/
@[expose] def WindowClosed (G : SimpleGraph V) (C A B : List V) {a b : V} (P : G.Walk a b)
    (y z : V) (N : List V) : Prop :=
  ∀ w, w ∉ C → w ∉ P.support →
    ¬ IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {x | x ∈ A ∨ x ∈ B} →
    ∀ m ∈ N, IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {m} →
    ∀ p ∈ P.support, IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {p} →
    p ∈ y :: N ++ [z]

/-- A tight, induced path satisfies the window condition for every stretch: the neighbours on `P` of
a component of the third kind lie among two consecutive vertices, and the vertices next to a vertex
of `N` lie in `y N z`. -/
theorem windowClosed_of_tight (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (htight : IsTight G C A B P.support) : WindowClosed G C A B P y z N := by
  classical
  intro w hwC hwP hnAB m hm hwm p hp hwp
  have hnd : (L₁ ++ y :: N ++ z :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  obtain ⟨v', w', he, hall⟩ := htight w hwC hwP hnAB
  have hmP : m ∈ P.support := by rw [hsupp]; simp [hm]
  have h1 := hall m hmP hwm
  have h2 := hall p hp hwp
  by_cases hmp : m = p
  · subst hmp
    simp [hm]
  · have he' : IsListEdge P.support m p := by
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact absurd rfl hmp
      · exact he
      · exact he.symm
      · exact absurd rfl hmp
    rw [hsupp] at he'
    have := IsListEdge.mem_window hnd hm he'
    simpa using this

/-- **The separation step of Claim 5.5.** Let `P` be an induced `C`-path,
`P.support = L₁ ++ y :: N ++ z :: L₂`, let the vertices of `N` be on no side, and let the window
condition hold. Then every neighbour of a vertex of `tightZone G (C ∪ P) N` lies in it, or is `y` or
`z`. -/
theorem tightZone_closed_of (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hwc : WindowClosed G C A B P y z N)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    {v w : V} (hv : v ∈ tightZone G {x | x ∈ C ∨ x ∈ P.support} N) (hvw : G.Adj v w) :
    w ∈ tightZone G {x | x ∈ C ∨ x ∈ P.support} N ∨ w = y ∨ w = z := by
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  have hnd : (L₁ ++ y :: N ++ z :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have haP : a ∈ P.support := P.start_mem_support
  have hbP : b ∈ P.support := P.end_mem_support
  -- a vertex of `C` off `P` is in `A` or `B`
  have hCAB : ∀ {w}, w ∈ C → w ∉ P.support → w ∈ A ∨ w ∈ B := fun {w} hw hwP => by
    rcases mem_of_rotate hrot hw with rfl | h | rfl | h
    · exact absurd haP hwP
    · exact Or.inl h
    · exact absurd hbP hwP
    · exact Or.inr h
  -- a vertex of `N` joined to `A ∪ B` avoiding `X` contradicts `hno`
  have hside : ∀ {m t}, m ∈ N → t ∈ A ∨ t ∈ B → IsConnectedAvoiding G X m {t} → False :=
    fun {m t} hm ht hc => by
      obtain ⟨t', rfl, p, hp, hin⟩ := hc
      rcases ht with ht | ht
      · exact (hno m hm).1 ⟨t', ht, p, hp, hin⟩
      · exact (hno m hm).2 ⟨t', ht, p, hp, hin⟩
  -- the window lemma, on `P.support`
  have hwin : ∀ {m w}, m ∈ N → IsListEdge P.support m w → w ∈ tightZone G X N ∨ w = y ∨ w = z :=
    fun {m w} hm he => by
      rw [hsupp] at he
      have := IsListEdge.mem_window hnd hm he
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
        at this
      rcases this with rfl | h | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inr rfl)
  rcases hv with hm | ⟨hvX, m, hm, hvm⟩
  · -- `v` is a vertex of `N`
    by_cases hwX : w ∈ X
    · rcases hwX with hwC | hwP
      · by_cases hwP : w ∈ P.support
        · exact hwin hm (hind v (by rw [hsupp]; simp [hm]) w hwP hvw)
        · exact (hside hm (hCAB hwC hwP)
            (isConnectedAvoiding_of_walk hvw.toWalk (fun x hx _ => by
              simp at hx; exact hx))).elim
      · exact hwin hm (hind v (by rw [hsupp]; simp [hm]) w hwP hvw)
    · exact Or.inl (Or.inr ⟨hwX, v, hm, isConnectedAvoiding_of_walk hvw.symm.toWalk
        (fun x hx _ => by simp at hx; exact hx)⟩)
  · -- `v` is off `X`, joined to `m ∈ N`
    obtain ⟨m', rfl, p, hp, hpin⟩ := hvm
    -- the walk from `w` through `v` to `m'`
    have hwalk : ∀ x ∈ (Walk.cons hvw.symm p).support, x ∈ X → x = w ∨ x = m' := by
      intro x hx hxX
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · by_cases h1 : x = v
        · exact absurd (h1 ▸ hxX) hvX
        · by_cases h2 : x = m'
          · exact Or.inr h2
          · exact absurd hxX (hpin x hx h1 h2)
    by_cases hwX : w ∈ X
    · by_cases hwP : w ∈ P.support
      · -- the component of `v` is of the third kind, so it is tight
        have hnAB : ¬ IsConnectedAvoiding G X v {x | x ∈ A ∨ x ∈ B} := by
          rintro ⟨t, ht, q, hq, hqin⟩
          refine hside hm ht (isConnectedAvoiding_of_walk (p.reverse.append q) ?_)
          intro x hx hxX
          rw [Walk.support_append, List.mem_append, Walk.support_reverse, List.mem_reverse] at hx
          rcases hx with hx | hx
          · by_cases h1 : x = v
            · exact absurd (h1 ▸ hxX) hvX
            · by_cases h2 : x = m'
              · exact Or.inl h2
              · exact absurd hxX (hpin x hx h1 h2)
          · have hx' : x ∈ q.support := List.mem_of_mem_tail hx
            by_cases h1 : x = v
            · exact absurd (h1 ▸ hxX) hvX
            · by_cases h2 : x = t
              · exact Or.inr h2
              · exact absurd hxX (hqin x hx' h1 h2)
        have hvC : v ∉ C := fun h => hvX (Or.inl h)
        have hvP : v ∉ P.support := fun h => hvX (Or.inr h)
        have hwW := hwc v hvC hvP hnAB m' hm ⟨m', rfl, p, hp, hpin⟩ w hwP
          (isConnectedAvoiding_of_walk hvw.toWalk (fun x hx _ => by simp at hx; exact hx))
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hwW
        rcases hwW with rfl | h | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inr rfl)
      · have hwC : w ∈ C := by
          rcases hwX with h | h
          · exact h
          · exact absurd h hwP
        exact (hside hm (hCAB hwC hwP) (by
          have := isConnectedAvoiding_of_walk (Walk.cons hvw.symm p) hwalk
          exact this.symm')).elim
    · exact Or.inl (Or.inr ⟨hwX, m', hm, isConnectedAvoiding_of_walk _ hwalk⟩)

/-- **The separation step of Claim 5.5 for tight paths.** Let `P` be an induced, tight `C`-path,
`P.support = L₁ ++ y :: N ++ z :: L₂`, and let the vertices of `N` be on no side. Then every
neighbour of a vertex of `tightZone G (C ∪ P) N` lies in it, or is `y` or `z`. -/
theorem tightZone_closed (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    {v w : V} (hv : v ∈ tightZone G {x | x ∈ C ∨ x ∈ P.support} N) (hvw : G.Adj v w) :
    w ∈ tightZone G {x | x ∈ C ∨ x ∈ P.support} N ∨ w = y ∨ w = z :=
  tightZone_closed_of hrot hP hsupp hind (windowClosed_of_tight hP hsupp htight) hno hv hvw

/-- The set `tightZone G (C ∪ P) N` misses `C`. -/
theorem tightZone_not_mem (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    {v : V} (hv : v ∈ tightZone G {x | x ∈ C ∨ x ∈ P.support} N) : v ∉ C := by
  rcases hv with hm | ⟨hvX, -⟩
  · exact not_mem_C_of_mem_window hP hsupp hm
  · exact fun h => hvX (Or.inl h)

/-- A walk that starts in a set `Z` closed up to the two vertices `y` and `z`, and never visits them,
ends in `Z`. -/
theorem mem_of_walk_of_closed {Z : Set V}
    (hcl : ∀ v ∈ Z, ∀ w, G.Adj v w → w ∈ Z ∨ w = y ∨ w = z) :
    ∀ {u v : V} (p : G.Walk u v), u ∈ Z → (∀ t ∈ p.support, t ≠ y ∧ t ≠ z) → v ∈ Z
  | _, _, .nil, hu, _ => hu
  | _, _, .cons h p, hu, ht => by
    have hs : ∀ t ∈ p.support, t ≠ y ∧ t ≠ z := fun t hti =>
      ht t (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hti)
    rcases hcl _ hu _ h with h1 | rfl | rfl
    · exact mem_of_walk_of_closed hcl p h1 hs
    · exact absurd rfl (hs _ p.start_mem_support).1
    · exact absurd rfl (hs _ p.start_mem_support).2

/-- The step "$\{y_j,y_r\}$ separates them from $C$" of the proof of Claim 5.5 (Humeau and Pous,
page 19), under the window condition: a `C`-path that misses `y` and `z` misses `N`. -/
theorem not_mem_window_of_tPath (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hwc : WindowClosed G C A B P y z N)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    {c d : V} (R : G.Walk c d) (hR : IsTPath G C R) (hyR : y ∉ R.support)
    (hzR : z ∉ R.support) : ∀ x ∈ N, x ∉ R.support := by
  classical
  intro x hx hxR
  have hZ : x ∈ tightZone G {w | w ∈ C ∨ w ∈ P.support} N := Or.inl hx
  have hend := mem_of_walk_of_closed
    (fun v hv w hvw => tightZone_closed_of hrot hP hsupp hind hwc hno hv hvw)
    (R.dropUntil x hxR) hZ (fun t ht => by
      have htR : t ∈ R.support := R.support_dropUntil_subset_support hxR ht
      exact ⟨fun h => hyR (h ▸ htR), fun h => hzR (h ▸ htR)⟩)
  exact tightZone_not_mem hP hsupp hend hR.2.2.1

/-- **Claim 5.5 under the window condition** (Humeau and Pous, page 19): "The edge $y_jy_r$ is
safe in $G$." Here `P` is an induced `C`-path from `a` to `b`, `C = a A b B` up to rotation,
`P.support = L₁ ++ y :: N ++ z :: L₂` (so `y = y_j`, `z = y_r`), and the vertices of `N` (the `y_t`
with `j < t < r`) are on no side. The paper's proof needs "$\{y_j,y_r\}$ separates them from $C$",
which holds under the window condition (`tightZone_closed_of`) but not in general. -/
theorem claim_5_5_of (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hwc : WindowClosed G C A B P y z N)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) :
    IsSafe G (edge y z) C := by
  classical
  intro hc
  rcases isCrossed_sup_edge_cases' hc with h | ⟨c₁, c₂, c₃, c₄, Q, R, halt, hQ, hQe, hR, hdisj⟩
  · exact h
  have hyQ : y ∈ Q.support := Q.fst_mem_support_of_mem_edges hQe
  have hzQ : z ∈ Q.support := Q.snd_mem_support_of_mem_edges hQe
  have hch : (L₁ ++ (y :: N ++ [z]) ++ L₂).IsChain G.Adj := by
    have := P.isChain_adj_support
    rw [hsupp] at this
    simpa using this
  have hZch : (y :: N ++ [z]).IsChain G.Adj :=
    hch.infix ⟨L₁, L₂, rfl⟩
  refine reroute_edge Q R halt hQ hQe hR hdisj hZch (by simp) (List.getLast?_concat ..) ?_ ?_
  · intro x hx hxC
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      at hx
    rcases hx with rfl | hx | rfl
    · exact Or.inl rfl
    · exact absurd hxC (not_mem_C_of_mem_window hP hsupp hx)
    · exact Or.inr rfl
  · intro x hx hxR
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      at hx
    rcases hx with rfl | hx | rfl
    · exact hdisj hyQ hxR
    · -- the end of `R` after `x` would lie in the zone, which misses `C`
      have hZ : x ∈ tightZone G {w | w ∈ C ∨ w ∈ P.support} N := Or.inl hx
      have hend := mem_of_walk_of_closed
        (fun v hv w hvw => tightZone_closed_of hrot hP hsupp hind hwc hno hv hvw)
        (R.dropUntil x hxR) hZ (fun t ht => by
          have htR : t ∈ R.support := R.support_dropUntil_subset_support hxR ht
          exact ⟨fun h => hdisj hyQ (h ▸ htR), fun h => hdisj hzQ (h ▸ htR)⟩)
      exact tightZone_not_mem hP hsupp hend hR.2.2.1
    · exact hdisj hzQ hxR

/-- **Claim 5.5 for tight paths** (Humeau and Pous, page 19): "The edge $y_jy_r$ is safe in $G$."
This is `claim_5_5_of` with the window condition of a tight path (`windowClosed_of_tight`). -/
theorem claim_5_5_tight (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ z :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v) :
    IsSafe G (edge y z) C :=
  claim_5_5_of hrot hP hsupp hind (windowClosed_of_tight hP hsupp htight) hno

end GraphMinor.HP25
