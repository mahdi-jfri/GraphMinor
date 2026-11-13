module

public import GraphMinor.Wagner.TripodDeg3
public import GraphMinor.Wagner.TriangleK5
public import GraphMinor.Wagner.HPath

/-!
# Tripods at a triangle

Let `a`, `b`, `c` be a triangle of `K`, and consider the society whose cyclic permutation is
`(a, b, c)`. We show that a tripod of this society gives a `K_5` minor when `K` is internally
`4`-connected (`hasK5_of_triangle_tripod`).

Let the tripod have ends `u`, `v`, paths `P i`, inner vertices `s i` and redirecting paths
`Q i = s i :: r i`. Split the vertices into the side `U` of `u` (the parts of the paths `P i` before
`s i`), the side `U'` of `v` (the parts after `s i`), the set `S` of the three vertices `s i`, and
the set `T` of the vertices of the paths `r i`. Since the ends of the redirecting paths form the
triangle, the sets `U`, `U'` and `T` each induce a preconnected subgraph.

Internal `4`-connectivity at the cut `S` gives a path outside `S` between two of `U`, `U'`, `T`
whose inner vertices avoid all three. Each of the three kinds of such path gives a `K_5` minor by
`TwoSides.hasK5_of_XY` and `TwoSides.hasK5_of_YR`.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ} {R Ω : Set γ}

namespace Tripod

variable (T : Tripod K R Ω)

theorem eP (i : Fin 3) : T.u :: T.pre i ++ T.s i :: T.post i ++ [T.v] =
    (T.u :: T.pre i) ++ T.s i :: (T.post i ++ [T.v]) := by simp

theorem pre_mem_P {i : Fin 3} {x : γ} (h : x ∈ T.u :: T.pre i) :
    x ∈ T.u :: T.pre i ++ T.s i :: T.post i ++ [T.v] := by
  rw [T.eP]; exact List.mem_append_left _ h

theorem post_mem_P {i : Fin 3} {x : γ} (h : x ∈ T.post i ++ [T.v]) :
    x ∈ T.u :: T.pre i ++ T.s i :: T.post i ++ [T.v] := by
  rw [T.eP]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

theorem s_mem_P (i : Fin 3) : T.s i ∈ T.u :: T.pre i ++ T.s i :: T.post i ++ [T.v] := by
  rw [T.eP]; exact List.mem_append_right _ List.mem_cons_self

theorem u_ne_v_facts (i : Fin 3) : T.u ∉ T.post i ++ [T.v] ∧ T.v ∉ T.u :: T.pre i := by
  have h := nodup_five (T.hp i).1
  refine ⟨?_, ?_⟩
  · simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  · simp only [List.mem_cons, not_or]
    exact ⟨fun e => h.2.2.2.1 e.symm, h.2.2.2.2.2.2.2.1⟩

theorem pre_ne_s {i j : Fin 3} {x : γ} (h : x ∈ T.u :: T.pre i) : x ≠ T.s j := by
  rintro rfl
  by_cases hij : i = j
  · subst hij
    have hnd := (T.hp i).1
    rw [T.eP] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ h _ List.mem_cons_self rfl
  · rcases T.hpp i j hij _ (T.pre_mem_P h) (T.s_mem_P j) with h' | h'
    · exact T.s_ne_u j h'
    · exact T.s_ne_v j h'

theorem post_ne_s {i j : Fin 3} {x : γ} (h : x ∈ T.post i ++ [T.v]) : x ≠ T.s j := by
  rintro rfl
  by_cases hij : i = j
  · subst hij
    have hnd := (T.hp i).1
    rw [T.eP] at hnd
    exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 h
  · rcases T.hpp i j hij _ (T.post_mem_P h) (T.s_mem_P j) with h' | h'
    · exact T.s_ne_u j h'
    · exact T.s_ne_v j h'

theorem pre_not_post {i j : Fin 3} {x : γ} (h : x ∈ T.u :: T.pre i) (h' : x ∈ T.post j ++ [T.v]) :
    False := by
  by_cases hij : i = j
  · subst hij
    have hnd := (T.hp i).1
    rw [T.eP] at hnd
    exact (List.nodup_append.mp hnd).2.2 _ h _ (List.mem_cons_of_mem _ h') rfl
  · rcases T.hpp i j hij _ (T.pre_mem_P h) (T.post_mem_P h') with rfl | rfl
    · exact (T.u_ne_v_facts j).1 h'
    · exact (T.u_ne_v_facts i).2 h

theorem s_inj : Injective T.s := by
  intro i j h
  by_contra hij
  rcases T.hpp i j hij _ (T.s_mem_P i) (h ▸ T.s_mem_P j) with h' | h'
  · exact T.s_ne_u i h'
  · exact T.s_ne_v i h'

/-- The side of `u`. -/
def U : Set γ := {x | ∃ i, x ∈ T.u :: T.pre i}

/-- The side of `v`. -/
def U' : Set γ := {x | ∃ i, x ∈ T.post i ++ [T.v]}

/-- The inner and last vertices of the redirecting paths. -/
def Rs : Set γ := {x | ∃ i, x ∈ T.r i}

theorem pcU : (K.induce T.U).Preconnected := by
  have hc : ∀ i, (K.induce {x | x ∈ T.u :: T.pre i}).Preconnected := by
    intro i
    have h := (T.hp i).2.1
    rw [T.eP] at h
    exact pc_of_isChain h.left_of_append
  have e : T.U = ({x | x ∈ T.u :: T.pre 0} ∪ {x | x ∈ T.u :: T.pre 1}) ∪
      {x | x ∈ T.u :: T.pre 2} := by
    ext x
    simp only [U, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  rw [e]
  exact pc_union_mem (pc_union_mem (hc 0) (hc 1) (x := T.u) List.mem_cons_self
    List.mem_cons_self) (hc 2) (Or.inl List.mem_cons_self) List.mem_cons_self

theorem pcU' : (K.induce T.U').Preconnected := by
  have hv : ∀ i, T.v ∈ T.post i ++ [T.v] := fun i => by simp
  have hc : ∀ i, (K.induce {x | x ∈ T.post i ++ [T.v]}).Preconnected := by
    intro i
    have h := (T.hp i).2.1
    rw [T.eP] at h
    exact pc_of_isChain (h.right_of_append).tail
  have e : T.U' = ({x | x ∈ T.post 0 ++ [T.v]} ∪ {x | x ∈ T.post 1 ++ [T.v]}) ∪
      {x | x ∈ T.post 2 ++ [T.v]} := by
    ext x
    simp only [U', mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  rw [e]
  exact pc_union_mem (pc_union_mem (hc 0) (hc 1) (hv 0) (hv 1)) (hc 2) (Or.inl (hv 0)) (hv 2)

theorem touchU (i : Fin 3) : Touch K T.U {T.s i} := by
  have hch := (T.hp i).2.1
  rw [T.eP] at hch
  have hne : T.u :: T.pre i ≠ [] := List.cons_ne_nil _ _
  have hadj := (List.isChain_append.mp hch).2.2 ((T.u :: T.pre i).getLast hne)
    (by rw [List.getLast?_eq_some_getLast hne]; rfl) (T.s i) rfl
  exact ⟨_, ⟨i, List.getLast_mem hne⟩, T.s i, rfl, hadj⟩

theorem touchU' (i : Fin 3) : Touch K T.U' {T.s i} := by
  have hch := (T.hp i).2.1
  rw [T.eP] at hch
  have hne : T.post i ++ [T.v] ≠ [] := by simp
  have hadj := (List.isChain_cons.mp (List.isChain_append.mp hch).2.1).1
    ((T.post i ++ [T.v]).head hne) (by rw [List.head?_eq_some_head hne]; rfl)
  exact ⟨_, ⟨i, List.head_mem hne⟩, T.s i, rfl, hadj.symm⟩

theorem q_notU {i : Fin 3} {x : γ} (hx : x ∈ T.s i :: T.r i) : x ∉ T.U := by
  rintro ⟨j, hj⟩
  rcases List.mem_cons.mp hx with rfl | h
  · exact T.pre_ne_s hj rfl
  · exact T.hqX i j x h (T.pre_mem_P hj)

theorem q_notU' {i : Fin 3} {x : γ} (hx : x ∈ T.s i :: T.r i) : x ∉ T.U' := by
  rintro ⟨j, hj⟩
  rcases List.mem_cons.mp hx with rfl | h
  · exact T.post_ne_s hj rfl
  · exact T.hqX i j x h (T.post_mem_P hj)

/-- The two sides of a tripod whose redirecting paths end at pairwise adjacent vertices. -/
def twoSides (htt : ∀ i j, i ≠ j → K.Adj (T.t i) (T.t j)) : TwoSides K where
  X := T.U
  Y := T.U'
  s := T.s
  t := T.t
  r := T.r
  hX := T.pcU
  hY := T.pcU'
  hXs := T.touchU
  hYs := T.touchU'
  hXY := disjoint_left.mpr fun _ ⟨_, h⟩ ⟨_, h'⟩ => T.pre_not_post h h'
  hqc i := (T.hq i).2.1
  hqn i := (T.hq i).1
  hlast i := (T.hq i).2.2.2.2
  hXq _ := disjoint_left.mpr fun _ h h' => T.q_notU h' h
  hYq _ := disjoint_left.mpr fun _ h h' => T.q_notU' h' h
  hqq i j h := disjoint_left.mpr fun x hx hx' => T.hqq i j h x hx hx'
  htt := htt

end Tripod

theorem isChain_reverse_path {a b : γ} {mid : List γ} (h : (a :: mid ++ [b]).IsChain K.Adj) :
    (b :: mid.reverse ++ [a]).IsChain K.Adj := by
  have e : b :: mid.reverse ++ [a] = (a :: mid ++ [b]).reverse := by simp
  rw [e]
  exact isChain_reverse_of_symm h

/-- **The triangle case.** A tripod whose redirecting paths end at pairwise adjacent vertices gives
a `K_5` minor, when the three inner vertices `s i` form a cut of the kind allowed by internal
`4`-connectivity. -/
theorem hasK5_of_triangle_tripod (T : Tripod K R Ω)
    (htt : ∀ i j, i ≠ j → K.Adj (T.t i) (T.t j))
    (h4 : (K.induce {y | y ∉ range T.s}).Preconnected ∨
      ((∀ x ∈ range T.s, ∀ y ∈ range T.s, ¬ K.Adj x y) ∧
        ∃ x, x ∉ range T.s ∧ (K.induce {y | y ∉ range T.s ∧ y ≠ x}).Preconnected)) :
    HasK5MinorSimple K := by
  classical
  set D := T.twoSides htt with hD
  let A : Fin 3 → Set γ := ![T.U, T.U', T.Rs]
  have hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    have d01 : Disjoint T.U T.U' := D.hXY
    have d02 : Disjoint T.U T.Rs := disjoint_left.mpr fun x hx ⟨k, hk⟩ =>
      T.q_notU (List.mem_cons_of_mem _ hk) hx
    have d12 : Disjoint T.U' T.Rs := disjoint_left.mpr fun x hx ⟨k, hk⟩ =>
      T.q_notU' (List.mem_cons_of_mem _ hk) hx
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | assumption
      | exact Disjoint.symm (by assumption)
  have hAS : ∀ k, ∀ x ∈ A k, x ∉ range T.s := by
    intro k x hx ⟨j, hj⟩
    subst hj
    fin_cases k
    · obtain ⟨i, hi⟩ := hx
      exact T.pre_ne_s hi rfl
    · obtain ⟨i, hi⟩ := hx
      exact T.post_ne_s hi rfl
    · obtain ⟨i, hi⟩ := hx
      exact T.hqX i j _ hi (T.s_mem_P j)
  have huU : T.u ∈ T.U := ⟨0, List.mem_cons_self⟩
  have hvU' : T.v ∈ T.U' := ⟨0, by simp⟩
  -- A path between two of the sets, with inner vertices outside `S` and outside all three sets.
  have key : ∃ (i j : Fin 3) (a b : γ) (mid : List γ), i ≠ j ∧ a ∈ A i ∧ b ∈ A j ∧
      (∀ z ∈ mid, z ∉ range T.s ∧ ∀ k, z ∉ A k) ∧ (a :: mid ++ [b]).IsChain K.Adj := by
    rcases h4 with hpc | ⟨hind, x, hxS, hpc⟩
    · obtain ⟨i, j, a, b, mid, hij, ha, hb, hmid, -, hch⟩ :=
        exists_hpath hpc A hdisj (fun k y hy => hAS k y hy) (i := 0) (j := 1) (by decide)
          huU hvU'
      exact ⟨i, j, a, b, mid, hij, ha, hb, fun z hz => (hmid z hz), hch⟩
    · let A' : Fin 3 → Set γ := fun k => A k \ {x}
      have hdisj' : ∀ i j, i ≠ j → Disjoint (A' i) (A' j) := fun i j h =>
        (hdisj i j h).mono sdiff_subset sdiff_subset
      have hAW : ∀ k, A' k ⊆ {y | y ∉ range T.s ∧ y ≠ x} := fun k y hy =>
        ⟨hAS k y hy.1, hy.2⟩
      -- Some path `r k` has a vertex: otherwise the three vertices `s i` form a triangle.
      have hRs : T.Rs.Nonempty := by
        by_contra hemp
        have hr : ∀ k, T.r k = [] := by
          intro k
          by_contra hne
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
          exact hemp ⟨y, k, hy⟩
        have hts : ∀ k, T.t k = T.s k := by
          intro k
          have h := (T.hq k).2.2.2.2
          rw [hr k] at h
          simp only [List.getLast?_singleton, Option.some.injEq] at h
          exact h.symm
        exact hind _ ⟨0, rfl⟩ _ ⟨1, rfl⟩ (by rw [← hts 0, ← hts 1]; exact htt 0 1 (by decide))
      obtain ⟨τ, hτ⟩ := hRs
      have conv : HPathConcl K {y | y ∉ range T.s ∧ y ≠ x} A' →
          ∃ (i j : Fin 3) (a b : γ) (mid : List γ), i ≠ j ∧ a ∈ A i ∧ b ∈ A j ∧
            (∀ z ∈ mid, z ∉ range T.s ∧ ∀ k, z ∉ A k) ∧ (a :: mid ++ [b]).IsChain K.Adj := by
        rintro ⟨i, j, a, b, mid, hij, ha, hb, hmid, -, hch⟩
        refine ⟨i, j, a, b, mid, hij, ha.1, hb.1, fun z hz => ⟨(hmid z hz).1.1, fun k hk =>
          (hmid z hz).2 k ⟨hk, (hmid z hz).1.2⟩⟩, hch⟩
      have hτx : ∀ y, y ∈ A 0 ∪ A 1 → y ≠ τ := fun y hy hyτ => by
        subst hyτ
        rcases hy with hy | hy
        · exact disjoint_left.mp (hdisj 0 2 (by decide)) hy hτ
        · exact disjoint_left.mp (hdisj 1 2 (by decide)) hy hτ
      by_cases hxu : x = T.u
      · apply conv
        refine exists_hpath hpc A' hdisj' hAW (i := 1) (j := 2) (by decide)
          (x := T.v) (y := τ) ⟨hvU', ?_⟩ ⟨hτ, ?_⟩
        · rintro rfl
          exact T.huv hxu.symm
        · rintro rfl
          exact hτx _ (Or.inl (hxu ▸ huU)) rfl
      · by_cases hxv : x = T.v
        · apply conv
          refine exists_hpath hpc A' hdisj' hAW (i := 0) (j := 2) (by decide)
            (x := T.u) (y := τ) ⟨huU, ?_⟩ ⟨hτ, ?_⟩
          · rintro rfl
            exact hxu rfl
          · rintro rfl
            exact hτx _ (Or.inr (hxv ▸ hvU')) rfl
        · apply conv
          exact exists_hpath hpc A' hdisj' hAW (i := 0) (j := 1) (by decide)
            (x := T.u) (y := T.v) ⟨huU, fun h => hxu h.symm⟩ ⟨hvU', fun h => hxv h.symm⟩
  obtain ⟨i, j, a, b, mid, hij, ha, hb, hmid, hch⟩ := key
  -- The inner vertices avoid both sides and all redirecting paths.
  have hmid' : ∀ z ∈ mid, z ∉ D.X ∧ z ∉ D.Y ∧ ∀ k, z ∉ D.Q k := by
    intro z hz
    obtain ⟨hzS, hzA⟩ := hmid z hz
    refine ⟨hzA 0, hzA 1, fun k hk => ?_⟩
    rcases List.mem_cons.mp hk with h | h
    · exact hzS ⟨k, h.symm⟩
    · exact hzA 2 ⟨k, h⟩
  have hmid'' : ∀ z ∈ mid.reverse, z ∉ D.X ∧ z ∉ D.Y ∧ ∀ k, z ∉ D.Q k := fun z hz =>
    hmid' z (List.mem_reverse.mp hz)
  have hmidS : ∀ z ∈ mid, z ∉ D.swap.X ∧ z ∉ D.swap.Y ∧ ∀ k, z ∉ D.swap.Q k := fun z hz =>
    ⟨(hmid' z hz).2.1, (hmid' z hz).1, (hmid' z hz).2.2⟩
  have hmidS' : ∀ z ∈ mid.reverse, z ∉ D.swap.X ∧ z ∉ D.swap.Y ∧ ∀ k, z ∉ D.swap.Q k :=
    fun z hz => hmidS z (List.mem_reverse.mp hz)
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact D.hasK5_of_XY ha hb hch hmid'
  · obtain ⟨k, hk⟩ := hb
    exact D.swap.hasK5_of_YR (k := k) ha hk hch hmidS
  · exact D.hasK5_of_XY hb ha (isChain_reverse_path hch) hmid''
  · exact absurd rfl hij
  · obtain ⟨k, hk⟩ := hb
    exact D.hasK5_of_YR (k := k) ha hk hch hmid'
  · obtain ⟨k, hk⟩ := ha
    exact D.swap.hasK5_of_YR (k := k) hb hk (isChain_reverse_path hch) hmidS'
  · obtain ⟨k, hk⟩ := ha
    exact D.hasK5_of_YR (k := k) hb hk (isChain_reverse_path hch) hmid''
  · exact absurd rfl hij

end GraphMinor.Wagner
