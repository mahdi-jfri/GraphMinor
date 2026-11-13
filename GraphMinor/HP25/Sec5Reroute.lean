module

public import GraphMinor.HP25.Sec5Loop
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma33
import GraphMinor.HP25.Method
import GraphMinor.HP25.Sec5StripTools

/-!
# Rerouting a `C`-path through a component of the third kind

Line 5 of Algorithm 5.1 of Humeau and Pous (page 18) asks only for "a C-path between non-consecutive
vertices of C". Our correction of Lemma 5.4 needs more of this path (see the correction to Lemma 5.4
in `corrections/HP25.md`), and this file gives the step that improves it without adding any edge.

Let `C = a A b B` (up to rotation) and let `P` be an induced `C`-path from `a` to `b` that separates
`A` from `B`, with vertex list `L₁ u N v L₂`. Let `W = u M v` be an induced path whose inner vertices
`M` lie off `C ∪ P` and are joined to neither `A` nor `B` by a path with no inner vertex in `C ∪ P`
(they lie in a component of the third kind), and have no neighbour in `L₁` or `L₂`. Let some vertex of
`N` be on a side. The rerouted path `P' = L₁ u M v L₂`:

* is a `C`-path (`exists_reroute_path`) and is induced (`reroute_induced`);
* separates `A` from `B` if no vertex of `N` is on side `B` (`reroute_separates`), and `C` is crossed
  if some vertex of `N` is on side `A` and some vertex of `N` is on side `B` (`reroute_crossed`);
* has a strictly larger *live set* (`liveSet_reroute`): the vertices off the path that are joined to
  `A ∪ B` by a path that misses the path. This is the measure that makes the rerouting stop, as `μ`
  does in the proof of Lemma 4.3 (page 14).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The *live set* of a path with vertex list `l`: the vertices off `l` that are joined to `A ∪ B`
by a path with no inner vertex on `l`, that is, the vertices of the components of `G - l` that meet
`A ∪ B`. -/
@[expose] def liveSet (G : SimpleGraph V) (A B l : List V) : Set V :=
  {v | v ∉ l ∧ IsConnectedAvoiding G {x | x ∈ l} v {x | x ∈ A ∨ x ∈ B}}

/-- In a path, the start does not occur in the part after another vertex. -/
theorem start_not_mem_dropUntil [DecidableEq V] {s z : V} {p : G.Walk s z} (hp : p.IsPath) {x : V}
    (hx : x ∈ p.support) (hxs : x ≠ s) : s ∉ (p.dropUntil x hx).support := by
  intro hs
  have hnd := hp.support_nodup
  rw [← p.take_spec hx, Walk.support_append] at hnd
  have hs' : s ∈ (p.dropUntil x hx).support.tail := by
    rw [← Walk.cons_tail_support (p.dropUntil x hx)] at hs
    rcases List.mem_cons.mp hs with h | h
    · exact absurd h.symm hxs
    · exact h
  exact List.disjoint_of_nodup_append hnd (p.takeUntil x hx).start_mem_support hs'

/-- The part of a path after one of its vertices `x` is a path from `x` whose inner vertices are inner
vertices of the path. -/
theorem isConnectedAvoiding_tail [DecidableEq V] {X S : Set V} {s z : V} {p : G.Walk s z}
    (hp : p.IsPath) (hz : z ∈ S) (hin : ∀ y ∈ p.support, y ≠ s → y ≠ z → y ∉ X) {x : V}
    (hx : x ∈ p.support) (hxs : x ≠ s) : IsConnectedAvoiding G X x S := by
  refine ⟨z, hz, p.dropUntil x hx, hp.dropUntil hx, fun y hy h1 h2 => ?_⟩
  have hys : y ≠ s := fun h => start_not_mem_dropUntil hp hx hxs (h ▸ hy)
  exact hin y (p.support_dropUntil_subset_support hx hy) hys h2

variable {C A B L₁ N L₂ M : List V} {a b u v : V} {k : ℕ} {P : G.Walk a b}

/-- A vertex of `C` off `P` lies in `A` or in `B`. -/
theorem mem_arcs_of_mem_C (hrot : C.rotate k = a :: A ++ b :: B) {x : V} (hx : x ∈ C)
    (hxP : x ∉ P.support) : x ∈ A ∨ x ∈ B := by
  rcases mem_of_rotate hrot hx with rfl | h | rfl | h
  · exact absurd P.start_mem_support hxP
  · exact Or.inl h
  · exact absurd P.end_mem_support hxP
  · exact Or.inr h

/-- **Truncation at `C`.** A vertex off `P` that is joined to `A ∪ B` by a path that misses `P` is
joined to `A ∪ B` by a path with no inner vertex in `C ∪ P`: stop at the first vertex of `A ∪ B`. -/
theorem isConnectedAvoiding_CP_of_P (hrot : C.rotate k = a :: A ++ b :: B) {w : V}
    (h : IsConnectedAvoiding G {x | x ∈ P.support} w {x | x ∈ A ∨ x ∈ B}) :
    IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {x | x ∈ A ∨ x ∈ B} := by
  obtain ⟨z, hz, p, hp, hin⟩ := h
  obtain ⟨s, hs, p', hsub, hinS, hpath⟩ := exists_first_hit {x | x ∈ A ∨ x ∈ B} p hz
  refine ⟨s, hs, p', hpath hp, fun x hx h1 h2 hX => ?_⟩
  have hxS := hinS x hx h2
  have hxz : x ≠ z := fun h => hxS (h ▸ hz)
  have hxP : x ∉ P.support := hin x (hsub x hx) h1 hxz
  rcases hX with hxC | hxP'
  · exact hxS (mem_arcs_of_mem_C hrot hxC hxP)
  · exact hxP hxP'

/-- The hypothesis on the inner vertices `M` of the new piece of the path: they lie off `C ∪ P` and
none is joined to `A ∪ B` by a path with no inner vertex in `C ∪ P`, that is, they lie in components
of the third kind. -/
@[expose] def IsDeadList (G : SimpleGraph V) (C A B : List V) {a b : V} (P : G.Walk a b)
    (M : List V) : Prop :=
  ∀ w ∈ M, w ∉ C ∧ w ∉ P.support ∧
    ¬ IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {x | x ∈ A ∨ x ∈ B}

/-- Replacing the middle part of a list without repetition by a list without repetition whose new
entries are not in the list gives a list without repetition. -/
theorem nodup_replace {l₁ l₂ l₃ m : List V} (h : (l₁ ++ l₂ ++ l₃).Nodup) (hm : m.Nodup)
    (hsub : ∀ x ∈ m, x ∈ l₂ ∨ x ∉ l₁ ++ l₂ ++ l₃) : (l₁ ++ m ++ l₃).Nodup := by
  rw [List.nodup_append, List.nodup_append] at h ⊢
  obtain ⟨⟨h1, h2, h12⟩, h3, h123⟩ := h
  refine ⟨⟨h1, hm, fun x hx y hy hxy => ?_⟩, h3, fun x hx y hy hxy => ?_⟩
  · subst hxy
    rcases hsub x hy with h | h
    · exact h12 x hx x h rfl
    · exact h (by simp [hx])
  · subst hxy
    rcases List.mem_append.mp hx with hx | hx
    · exact h123 x (by simp [hx]) x hy rfl
    · rcases hsub x hx with h | h
      · exact h123 x (by simp [h]) x hy rfl
      · exact h (by simp [hy])

/-- The rerouted list `L₁ u M v L₂` is the support of a `C`-path from `a` to `b`. -/
theorem exists_reroute_path (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ u :: N ++ v :: L₂)
    {W : G.Walk u v} (hWp : W.IsPath) (hW : W.support = u :: M ++ [v])
    (hM : IsDeadList G C A B P M) :
    ∃ P' : G.Walk a b, IsTPath G C P' ∧ P'.support = L₁ ++ u :: M ++ v :: L₂ := by
  have hnd : (L₁ ++ u :: N ++ v :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hch : (L₁ ++ u :: N ++ v :: L₂).IsChain G.Adj := hsupp ▸ P.isChain_adj_support
  have hc₁ : (L₁ ++ [u]).IsChain G.Adj := hch.infix ⟨[], N ++ v :: L₂, by simp⟩
  have hc₂ : ([v] ++ L₂).IsChain G.Adj := hch.infix ⟨L₁ ++ u :: N, [], by simp⟩
  have hcW : ([u] ++ (M ++ [v])).IsChain G.Adj := by
    have := W.isChain_adj_support
    rw [hW] at this
    simpa using this
  have hc : (L₁ ++ u :: M ++ v :: L₂).IsChain G.Adj := by
    have h1 := hc₁.append_overlap hcW (by simp)
    have h2 := List.IsChain.append_overlap (l₁ := L₁ ++ [u] ++ M) (l₂ := [v]) (l₃ := L₂)
      (by simpa using h1) hc₂ (by simp)
    simpa using h2
  have hnd' : (L₁ ++ u :: M ++ v :: L₂).Nodup := by
    have h := nodup_replace (l₁ := L₁) (l₂ := u :: N ++ [v]) (l₃ := L₂) (m := u :: M ++ [v])
      (by simpa using hnd) (hW ▸ hWp.support_nodup) (fun x hx => by
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | hx | rfl
        · exact Or.inl (by simp)
        · exact Or.inr fun h => (hM x hx).2.1 (by rw [hsupp]; simpa using h)
        · exact Or.inl (by simp))
    simpa using h
  have ha : (L₁ ++ u :: M ++ v :: L₂).head? = some a := by
    have h0 : P.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
    rw [hsupp] at h0
    cases L₁ <;> simpa using h0
  have hb : (L₁ ++ u :: M ++ v :: L₂).getLast? = some b := by
    have h0 : P.support.getLast? = some b := by
      rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
    rw [hsupp] at h0
    have e1 : L₁ ++ u :: N ++ v :: L₂ = (L₁ ++ u :: N) ++ (v :: L₂) := by simp
    have e2 : L₁ ++ u :: M ++ v :: L₂ = (L₁ ++ u :: M) ++ (v :: L₂) := by simp
    rw [e1, List.getLast?_append_of_ne_nil _ (by simp)] at h0
    rw [e2, List.getLast?_append_of_ne_nil _ (by simp)]
    exact h0
  obtain ⟨P', hP', hs⟩ := exists_tPath_of_list hc hnd' ha hb hP.2.1 hP.2.2.1 (fun w hw hwC => by
    have hw' : w ∈ P.support ∨ w ∈ M := by
      rw [hsupp]
      simp only [List.mem_append, List.mem_cons] at hw ⊢
      tauto
    rcases hw' with hwP | hwM
    · by_contra hne
      push Not at hne
      exact (hP.2.2.2 w hwP hne.1 hne.2).1 hwC
    · exact absurd hwC (hM w hwM).1)
  exact ⟨P', hP', hs⟩

/-- **The rerouted path is induced.** Let `P` be induced, `N` not empty, `W = u M v` induced, and let
no vertex of `M` have a neighbour in `L₁` or `L₂`. Then the path with vertex list `L₁ u M v L₂` is
induced. -/
theorem reroute_induced (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ u :: N ++ v :: L₂)
    (hind : ∀ x ∈ P.support, ∀ y ∈ P.support, G.Adj x y → IsListEdge P.support x y)
    (hN : N ≠ []) {W : G.Walk u v} (hW : W.support = u :: M ++ [v])
    (hWind : ∀ x ∈ W.support, ∀ y ∈ W.support, G.Adj x y → IsListEdge W.support x y)
    (hspan : ∀ w ∈ M, ∀ p ∈ L₁ ++ L₂, ¬ G.Adj w p) {P' : G.Walk a b}
    (hP' : P'.support = L₁ ++ u :: M ++ v :: L₂) :
    ∀ x ∈ P'.support, ∀ y ∈ P'.support, G.Adj x y → IsListEdge P'.support x y := by
  have hnd : (L₁ ++ u :: N ++ v :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  intro x hx y hy hxy
  rw [hP'] at hx hy ⊢
  -- membership in `W`
  have hinW : ∀ {z w}, z ∈ M → G.Adj z w → w ∈ L₁ ++ u :: M ++ v :: L₂ → w ∈ W.support :=
    fun {z w} hz hzw hw => by
      rw [hW]
      simp only [List.mem_append, List.mem_cons] at hw ⊢
      rcases hw with (h | h | h) | h | h
      · exact absurd hzw (hspan z hz w (by simp [h]))
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · simp [h]
      · exact absurd hzw (hspan z hz w (by simp [h]))
  have hlift : ∀ {z w}, IsListEdge W.support z w → IsListEdge (L₁ ++ u :: M ++ v :: L₂) z w :=
    fun {z w} h => by
      rw [hW] at h
      have e : L₁ ++ u :: M ++ v :: L₂ = (L₁ ++ (u :: M ++ [v])) ++ L₂ := by simp
      rw [e]
      exact (h.append_right (l₁ := L₁)).append_left
  by_cases hxM : x ∈ M
  · have hyW := hinW hxM hxy hy
    exact hlift (hWind x (by rw [hW]; simp [hxM]) y hyW hxy)
  by_cases hyM : y ∈ M
  · have hxW := hinW hyM hxy.symm hx
    exact hlift (hWind x hxW y (by rw [hW]; simp [hyM]) hxy)
  -- both ends on `P`, off `N`
  have hPmem : ∀ {z}, z ∈ L₁ ++ u :: M ++ v :: L₂ → z ∉ M → z ∈ L₁ ++ [u] ∨ z ∈ v :: L₂ :=
    fun {z} hz hzM => by
      simp only [List.mem_append, List.mem_cons] at hz ⊢
      tauto
  have hnotN : ∀ {z}, z ∈ L₁ ++ [u] ∨ z ∈ v :: L₂ → z ∉ N := fun {z} hz hzN => by
    have e : L₁ ++ u :: N ++ v :: L₂ = (L₁ ++ [u]) ++ N ++ (v :: L₂) := by simp
    rw [e, List.nodup_append, List.nodup_append] at hnd
    rcases hz with hz | hz
    · exact hnd.1.2.2 z hz z hzN rfl
    · exact hnd.2.2 z (by simp [hzN]) z hz rfl
  have hx' := hPmem hx hxM
  have hy' := hPmem hy hyM
  have hxP : x ∈ P.support := by
    rw [hsupp]
    simp only [List.mem_append, List.mem_cons] at hx' ⊢
    tauto
  have hyP : y ∈ P.support := by
    rw [hsupp]
    simp only [List.mem_append, List.mem_cons] at hy' ⊢
    tauto
  have he := hind x hxP y hyP hxy
  rw [hsupp, show L₁ ++ u :: N ++ v :: L₂ = (L₁ ++ [u]) ++ N ++ (v :: L₂) by simp] at he
  rcases he.of_append_middle hN (hnotN hx') (hnotN hy') with h | h
  · rw [show L₁ ++ u :: M ++ v :: L₂ = (L₁ ++ [u]) ++ (M ++ v :: L₂) by simp]
    exact h.append_left
  · rw [show L₁ ++ u :: M ++ v :: L₂ = (L₁ ++ u :: M) ++ (v :: L₂) by simp]
    exact h.append_right

/-- **The rerouted path separates.** Let `P` separate `U` from `W'`, where `U` and `W'` lie on `C`
and every vertex of `C` off `P` lies in `U` or `W'`. Let `l'` contain every vertex of `P` outside
`N`, and let no vertex of `N` be joined to `W'` by a path with no inner vertex in `C ∪ P`. Then `l'`
separates `U` from `W'`: the last vertex of `P` on a path from `U` to `W'` that misses `l'` would be a
vertex of `N` joined to `W'`. -/
theorem separates_of_reroute {U W' : Set V} (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ u :: N ++ v :: L₂)
    (hCUW : ∀ x ∈ C, x ∉ P.support → x ∈ U ∨ x ∈ W') (hWC : ∀ x ∈ W', x ∈ C)
    (hsep : Separates G {x | x ∈ P.support} U W')
    (hNW : ∀ t ∈ N, ¬ IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} t W')
    {l' : List V} (hl' : ∀ x ∈ P.support, x ∉ l' → x ∈ N) :
    Separates G {x | x ∈ l'} U W' := by
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  intro α hα β hβ p
  by_contra hcon
  push Not at hcon
  have hNC : ∀ {t}, t ∈ N → t ∉ C := fun ht => not_mem_C_of_mem_window hP hsupp ht
  have hvX : ∀ x ∈ p.support, x ∈ X →
      x ∈ {x | (x ∈ U ∧ x ∉ P.support) ∨ x ∈ N} ∨ x ∈ {x | x ∈ W' ∧ x ∉ P.support} := by
    intro x hx hxX
    by_cases hxP : x ∈ P.support
    · exact Or.inl (Or.inr (hl' x hxP (hcon x hx)))
    · rcases hxX with hxC | hxP'
      · rcases hCUW x hxC hxP with h | h
        · exact Or.inl (Or.inl ⟨h, hxP⟩)
        · exact Or.inr ⟨h, hxP⟩
      · exact absurd hxP' hxP
  have hβ' : β ∉ P.support := fun h =>
    hNC (hl' β h (hcon β p.end_mem_support)) (hWC β hβ)
  have hα' : α ∈ {x | (x ∈ U ∧ x ∉ P.support) ∨ x ∈ N} := by
    by_cases h : α ∈ P.support
    · exact Or.inr (hl' α h (hcon α p.start_mem_support))
    · exact Or.inl ⟨hα, h⟩
  have hβ'' : β ∈ {x | x ∈ W' ∧ x ∉ P.support} := ⟨hβ, hβ'⟩
  obtain ⟨a', ha', b', hb', hc⟩ := exists_connected_of_walk (X := X) p hβ'' hvX α hα'
    Walk.nil (fun x hx h => by simp at hx; exact absurd hx h)
  obtain ⟨t, rfl, r, hr, hrin⟩ := hc
  rcases ha' with ⟨ha'U, ha'P⟩ | ha'N
  · obtain ⟨x, hx, hxP⟩ := hsep a' ha'U t hb'.1 r
    by_cases h1 : x = a'
    · exact ha'P (h1 ▸ hxP)
    · by_cases h2 : x = t
      · exact hb'.2 (h2 ▸ hxP)
      · exact hrin x hx h1 h2 (Or.inr hxP)
  · exact hNW a' ha'N ⟨t, hb'.1, r, hr, hrin⟩

/-- A vertex of a side path of a vertex `t` of `N` other than `t` lies neither on `P` nor in `M`: its
part after it joins it to `A ∪ B` away from `C ∪ P`, which no vertex of `M` is. -/
theorem side_path_avoids [DecidableEq V] (hrot : C.rotate k = a :: A ++ b :: B)
    (hCnd : C.Nodup) (hP : IsTPath G C P) (hM : IsDeadList G C A B P M) {S : Set V}
    (hS : ∀ x ∈ S, x ∈ A ∨ x ∈ B) {t : V}
    (h : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} t S) :
    ∃ z ∈ S, ∃ q : G.Walk t z, ∀ x ∈ q.support, x ≠ t → x ∉ P.support ∧ x ∉ M := by
  obtain ⟨z, hz, q, hq, hin⟩ := h
  refine ⟨z, hz, q, fun x hx hxt => ?_⟩
  by_cases hxz : x = z
  · subst hxz
    exact ⟨notMem_support_of_arc hCnd hrot hP (hS x hz),
      fun hxM => (hM x hxM).1 (List.mem_rotate.mp (by rw [hrot]; rcases hS x hz with h | h <;>
        simp [h]))⟩
  · have hxX := hin x hx hxt hxz
    refine ⟨fun h => hxX (Or.inr h), fun hxM => (hM x hxM).2.2 ?_⟩
    obtain ⟨z', hz', q', hq', hin'⟩ := isConnectedAvoiding_tail (X := {x | x ∈ C ∨ x ∈ P.support})
      hq hz hin hx hxt
    exact ⟨z', hS z' hz', q', hq', hin'⟩

/-- **A vertex on each side inside the span gives a crossing.** If a vertex of `N` is on side `A`
and a vertex of `N` is on side `B`, then `C` is crossed: the rerouted path `L₁ u M v L₂` misses the
walk from `A` along a side path to the first vertex, along `N` to the second, and along a side path
to `B`. -/
theorem reroute_crossed (hrot : C.rotate k = a :: A ++ b :: B) (hCnd : C.Nodup)
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ u :: N ++ v :: L₂)
    {W : G.Walk u v} (hWp : W.IsPath) (hW : W.support = u :: M ++ [v])
    (hM : IsDeadList G C A B P M) {t₁ t₂ : V} (ht₁ : t₁ ∈ N) (ht₂ : t₂ ∈ N)
    (hA : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} t₁)
    (hB : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} t₂) : IsCrossed G C := by
  classical
  have hnd : (L₁ ++ u :: N ++ v :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  obtain ⟨P', hP', hs⟩ := exists_reroute_path hP hsupp hWp hW hM
  refine isCrossed_of_not_separates hrot hP' fun hsep => ?_
  obtain ⟨α, hα, S₁, hS₁⟩ := side_path_avoids hrot hCnd hP hM (fun x hx => Or.inl hx) hA
  obtain ⟨β, hβ, S₂, hS₂⟩ := side_path_avoids hrot hCnd hP hM (fun x hx => Or.inr hx) hB
  have hNch : N.IsChain G.Adj := by
    have := P.isChain_adj_support
    rw [hsupp] at this
    exact this.infix ⟨L₁ ++ [u], v :: L₂, by simp⟩
  obtain ⟨σ, hσ⟩ := exists_walk_of_isChain hNch ht₁ ht₂
  -- a vertex of `N` is not on `P'`
  have hNP' : ∀ {x}, x ∈ N → x ∉ P'.support := fun {x} hx h => by
    rw [hs] at h
    simp only [List.mem_append, List.mem_cons] at h
    have e : L₁ ++ u :: N ++ v :: L₂ = (L₁ ++ [u]) ++ N ++ (v :: L₂) := by simp
    rw [e, List.nodup_append, List.nodup_append] at hnd
    rcases h with (h | h | h) | h | h
    · exact hnd.1.2.2 x (by simp [h]) x hx rfl
    · exact hnd.1.2.2 x (by simp [h]) x hx rfl
    · exact (hM x h).2.1 (by rw [hsupp]; simp [hx])
    · exact hnd.2.2 x (by simp [hx]) x (by simp [h]) rfl
    · exact hnd.2.2 x (by simp [hx]) x (by simp [h]) rfl
  have hoff : ∀ {x}, x ∉ P.support → x ∉ M → x ∉ P'.support := fun {x} h1 h2 h => by
    rw [hs] at h
    have : x ∈ P.support ∨ x ∈ M := by
      rw [hsupp]
      simp only [List.mem_append, List.mem_cons] at h ⊢
      tauto
    tauto
  obtain ⟨y, hy, hyP'⟩ := hsep α hα β hβ (S₁.reverse.append (σ.append S₂))
  rw [Walk.support_append, Walk.support_reverse, List.mem_append, List.mem_reverse] at hy
  rcases hy with hy | hy
  · by_cases hyt : y = t₁
    · exact hNP' (hyt ▸ ht₁) hyP'
    · exact hoff (hS₁ y hy hyt).1 (hS₁ y hy hyt).2 hyP'
  · have hy := List.mem_of_mem_tail hy
    rw [Walk.support_append, List.mem_append] at hy
    rcases hy with hy | hy
    · exact hNP' (hσ y hy) hyP'
    · have hy' := List.mem_of_mem_tail hy
      by_cases hyt : y = t₂
      · exact hNP' (hyt ▸ ht₂) hyP'
      · exact hoff (hS₂ y hy' hyt).1 (hS₂ y hy' hyt).2 hyP'

/-- **The measure grows.** If some vertex `t` of `N` is joined to `A ∪ B` by a path with no inner
vertex in `C ∪ P`, the live set of `L₁ u M v L₂` strictly contains that of `P`: every component of
`G - P` that meets `A ∪ B` misses `M`, and `t` joins the live set. -/
theorem liveSet_reroute (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ u :: N ++ v :: L₂) (hM : IsDeadList G C A B P M) {t : V}
    (ht : t ∈ N)
    (hts : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} t {x | x ∈ A ∨ x ∈ B}) :
    liveSet G A B P.support ⊂ liveSet G A B (L₁ ++ u :: M ++ v :: L₂) := by
  classical
  have hnd : (L₁ ++ u :: N ++ v :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hl' : ∀ x ∈ L₁ ++ u :: M ++ v :: L₂, x ∈ P.support ∨ x ∈ M := fun x hx => by
    rw [hsupp]
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    tauto
  have htP : t ∈ P.support := by rw [hsupp]; simp [ht]
  refine ⟨fun x ⟨hxP, p⟩ => ?_, fun h => (h ⟨?_, ?_⟩).1 (by simpa using htP)⟩
  · obtain ⟨z, hz, p, hp, hin⟩ := p
    have hxM : x ∉ M := fun hxM => (hM x hxM).2.2
      (isConnectedAvoiding_CP_of_P hrot ⟨z, hz, p, hp, hin⟩)
    refine ⟨fun h => (hl' x h).elim hxP hxM, z, hz, p, hp, fun y hy h1 h2 hyl => ?_⟩
    rcases hl' y hyl with hyP | hyM
    · exact hin y hy h1 h2 hyP
    · exact (hM y hyM).2.2 (isConnectedAvoiding_CP_of_P hrot
        (isConnectedAvoiding_tail hp hz hin hy h1))
  · intro htl
    rcases hl' t htl with h | h
    · have e : L₁ ++ u :: N ++ v :: L₂ = (L₁ ++ [u]) ++ N ++ (v :: L₂) := by simp
      rw [e, List.nodup_append, List.nodup_append] at hnd
      simp only [List.mem_append, List.mem_cons] at htl
      rcases htl with (h' | h' | h') | h' | h'
      · exact hnd.1.2.2 t (by simp [h']) t ht rfl
      · exact hnd.1.2.2 t (by simp [h']) t ht rfl
      · exact (hM t h').2.1 htP
      · exact hnd.2.2 t (by simp [ht]) t (by simp [h']) rfl
      · exact hnd.2.2 t (by simp [ht]) t (by simp [h']) rfl
    · exact (hM t h).2.1 htP
  · obtain ⟨z, hz, p, hp, hin⟩ := hts
    refine ⟨z, hz, p, hp, fun y hy h1 h2 hyl => ?_⟩
    rcases hl' y hyl with hyP | hyM
    · exact hin y hy h1 h2 (Or.inr hyP)
    · exact (hM y hyM).2.2 (isConnectedAvoiding_tail hp hz hin hy h1)

end GraphMinor.HP25
