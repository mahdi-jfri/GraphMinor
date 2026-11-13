module

public import GraphMinor.Wagner.K33Sub
public import GraphMinor.Wagner.TV8

/-!
# `K_{3,3}` models with extra links give `K_5` minors

A `K_{3,3}` model (`K33M`) is a family of six disjoint, nonempty, preconnected vertex sets
`A 0, A 1, A 2` and `B 0, B 1, B 2`. We do not ask for the edges between `A i` and `B k` in the
structure, since one of them may be missing.

* If all nine edges are there and moreover `A i` is joined to `A j` and `B k` to `B l`, for some
  `i ≠ j` and `k ≠ l`, then `K` has a `K_5` minor (`K33M.hasK5_two_links`). The two joins may run
  through extra sets added to `A i` and `B k`.
* If all edges are there except perhaps the one between `A i₀` and `B k₀`, and a further connected
  set `Z` touches `A i₀`, `A j`, `B k₀` and `B l`, for some `j ≠ i₀` and `l ≠ k₀`, then `K` has a
  `K_5` minor (`K33M.hasK5_hub`).

We also build such models from a subdivision of `K_{3,3}` (`K33Sub.cutModel`). Each inner part
`m i k` goes wholly to `A i` or wholly to `B k`, except that the inner parts of some excluded paths
go to neither.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

/-- Six disjoint, nonempty, preconnected vertex sets of `K`. -/
structure K33M (K : SimpleGraph γ) where
  /-- The sets of the first side. -/
  A : Fin 3 → Set γ
  /-- The sets of the second side. -/
  B : Fin 3 → Set γ
  neA : ∀ i, (A i).Nonempty
  neB : ∀ k, (B k).Nonempty
  pcA : ∀ i, (K.induce (A i)).Preconnected
  pcB : ∀ k, (K.induce (B k)).Preconnected
  dA : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  dB : ∀ k l, k ≠ l → Disjoint (B k) (B l)
  dAB : ∀ i k, Disjoint (A i) (B k)

theorem fin3_third : ∀ i j : Fin 3, i ≠ j → ∃ r, r ≠ i ∧ r ≠ j := by decide

namespace K33M

variable (M : K33M K)

/-- **`K_{3,3}` plus a link on each side has a `K_5` minor.** The five branch sets are `A i ∪ ZA`,
`A j`, `B k ∪ ZB`, `B l` and `A r ∪ B r'`, where `r` and `r'` are the third indices. -/
theorem hasK5_two_links (t : ∀ i k, Touch K (M.A i) (M.B k)) {i j k l : Fin 3} (hij : i ≠ j)
    (hkl : k ≠ l) {ZA ZB : Set γ} (pcA' : (K.induce (M.A i ∪ ZA)).Preconnected)
    (pcB' : (K.induce (M.B k ∪ ZB)).Preconnected) (tA : Touch K (M.A i ∪ ZA) (M.A j))
    (tB : Touch K (M.B k ∪ ZB) (M.B l)) (dZA : ∀ t, Disjoint ZA (M.A t))
    (dZAB : ∀ t, Disjoint ZA (M.B t)) (dZBA : ∀ t, Disjoint ZB (M.A t))
    (dZB : ∀ t, Disjoint ZB (M.B t)) (dZZ : Disjoint ZA ZB) : HasK5MinorSimple K := by
  obtain ⟨r, hri, hrj⟩ := fin3_third i j hij
  obtain ⟨r', hrk, hrl⟩ := fin3_third k l hkl
  refine hasK5_of_sets (M.A i ∪ ZA) (M.A j) (M.B k ∪ ZB) (M.B l) (M.A r ∪ M.B r')
    ((M.neA i).mono subset_union_left) (M.neA j) ((M.neB k).mono subset_union_left) (M.neB l)
    ((M.neA r).mono subset_union_left) pcA' (M.pcA j) pcB' (M.pcB l)
    (pc_union_touch (M.pcA r) (M.pcB r') fun _ _ => t r r')
    (disjoint_union_left.mpr ⟨M.dA i j hij, dZA j⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨M.dAB i k, (dZBA i).symm⟩,
      disjoint_union_right.mpr ⟨dZAB k, dZZ⟩⟩)
    (disjoint_union_left.mpr ⟨M.dAB i l, dZAB l⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨M.dA i r (Ne.symm hri), M.dAB i r'⟩,
      disjoint_union_right.mpr ⟨dZA r, dZAB r'⟩⟩)
    (disjoint_union_right.mpr ⟨M.dAB j k, (dZBA j).symm⟩) (M.dAB j l)
    (disjoint_union_right.mpr ⟨M.dA j r (Ne.symm hrj), M.dAB j r'⟩)
    (disjoint_union_left.mpr ⟨M.dB k l hkl, dZB l⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨(M.dAB r k).symm,
      M.dB k r' (Ne.symm hrk)⟩, disjoint_union_right.mpr ⟨dZBA r, dZB r'⟩⟩)
    (disjoint_union_right.mpr ⟨(M.dAB r l).symm, M.dB l r' (Ne.symm hrl)⟩)
    tA ((t i k).mono subset_union_left subset_union_left)
    ((t i l).mono subset_union_left subset_rfl)
    ((t i r').mono subset_union_left subset_union_right)
    ((t j k).mono subset_rfl subset_union_left) (t j l)
    ((t j r').mono subset_rfl subset_union_right)
    tB ((t r k).symm.mono subset_union_left subset_union_left)
    ((t r l).symm.mono subset_rfl subset_union_left)

/-- **A hub joined to both sides gives a `K_5` minor.** The five branch sets are `A i₀ ∪ B l'`,
`A j`, `A m ∪ B k₀`, `B l` and `Z`, where `m` and `l'` are the third indices. The edge between
`A i₀` and `B k₀` is not used. -/
theorem hasK5_hub {i₀ k₀ : Fin 3} (t : ∀ i k, (i, k) ≠ (i₀, k₀) → Touch K (M.A i) (M.B k))
    {j l : Fin 3} (hj : j ≠ i₀) (hl : l ≠ k₀) {Z : Set γ} (hZne : Z.Nonempty)
    (hZ : (K.induce Z).Preconnected) (dZA : ∀ t, Disjoint Z (M.A t))
    (dZB : ∀ t, Disjoint Z (M.B t)) (t₁ : Touch K Z (M.A i₀)) (t₂ : Touch K Z (M.A j))
    (t₃ : Touch K Z (M.B k₀)) (t₄ : Touch K Z (M.B l)) : HasK5MinorSimple K := by
  obtain ⟨m, hmi, hmj⟩ := fin3_third i₀ j (Ne.symm hj)
  obtain ⟨l', hlk, hll⟩ := fin3_third k₀ l (Ne.symm hl)
  have n1 : ∀ {i k : Fin 3}, i ≠ i₀ → (i, k) ≠ (i₀, k₀) := fun h e => h (Prod.mk.inj e).1
  have n2 : ∀ {i k : Fin 3}, k ≠ k₀ → (i, k) ≠ (i₀, k₀) := fun h e => h (Prod.mk.inj e).2
  refine hasK5_of_sets (M.A i₀ ∪ M.B l') (M.A j) (M.A m ∪ M.B k₀) (M.B l) Z
    ((M.neA i₀).mono subset_union_left) (M.neA j) ((M.neA m).mono subset_union_left) (M.neB l)
    hZne (pc_union_touch (M.pcA i₀) (M.pcB l') fun _ _ => t i₀ l' (n2 hlk)) (M.pcA j)
    (pc_union_touch (M.pcA m) (M.pcB k₀) fun _ _ => t m k₀ (n1 hmi)) (M.pcB l) hZ
    (disjoint_union_left.mpr ⟨M.dA i₀ j (Ne.symm hj), (M.dAB j l').symm⟩)
    (disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨M.dA i₀ m (Ne.symm hmi), M.dAB i₀ k₀⟩,
      disjoint_union_right.mpr ⟨(M.dAB m l').symm, M.dB l' k₀ hlk⟩⟩)
    (disjoint_union_left.mpr ⟨M.dAB i₀ l, M.dB l' l hll⟩)
    (disjoint_union_left.mpr ⟨(dZA i₀).symm, (dZB l').symm⟩)
    (disjoint_union_right.mpr ⟨M.dA j m (Ne.symm hmj), M.dAB j k₀⟩) (M.dAB j l) (dZA j).symm
    (disjoint_union_left.mpr ⟨M.dAB m l, M.dB k₀ l (Ne.symm hl)⟩)
    (disjoint_union_left.mpr ⟨(dZA m).symm, (dZB k₀).symm⟩) (dZB l).symm
    ((t j l' (n1 hj)).symm.mono subset_union_right subset_rfl)
    ((t m l' (n1 hmi)).symm.mono subset_union_right subset_union_left)
    ((t i₀ l (n2 hl)).mono subset_union_left subset_rfl)
    (t₁.symm.mono subset_union_left subset_rfl)
    ((t j k₀ (n1 hj)).mono subset_rfl subset_union_right) (t j l (n1 hj)) t₂.symm
    ((t m l (n1 hmi)).mono subset_union_left subset_rfl)
    (t₃.symm.mono subset_union_right subset_rfl) t₄.symm

end K33M

namespace K33Sub

variable (S : K33Sub K)

/-- The set of the first side: `a i` and the inner parts `m i k` sent to `A`, apart from the
excluded paths. -/
def cutA (toA ex : Fin 3 → Fin 3 → Prop) (i : Fin 3) : Set γ :=
  {x | x = S.a i ∨ ∃ k, toA i k ∧ ¬ ex i k ∧ x ∈ S.m i k}

/-- The set of the second side: `b k` and the inner parts `m i k` sent to `B`, apart from the
excluded paths. -/
def cutB (toA ex : Fin 3 → Fin 3 → Prop) (k : Fin 3) : Set γ :=
  {x | x = S.b k ∨ ∃ i, ¬ toA i k ∧ ¬ ex i k ∧ x ∈ S.m i k}

theorem path_chain_left {a b : γ} {m : List γ} (h : (a :: m ++ [b]).IsChain K.Adj) :
    (a :: m).IsChain K.Adj :=
  h.left_of_append

theorem path_chain_right {a b : γ} {m : List γ} (h : (a :: m ++ [b]).IsChain K.Adj) :
    (m ++ [b]).IsChain K.Adj := by
  have e : a :: m ++ [b] = [a] ++ (m ++ [b]) := rfl
  rw [e] at h
  exact h.right_of_append

/-- The model in which each inner part goes wholly to one side, or to neither side when its path
is excluded. -/
def cutModel (toA ex : Fin 3 → Fin 3 → Prop) : K33M K where
  A := S.cutA toA ex
  B := S.cutB toA ex
  neA i := ⟨S.a i, Or.inl rfl⟩
  neB k := ⟨S.b k, Or.inl rfl⟩
  pcA i := by
    refine pc_of_star (c := S.a i) fun z hz => ?_
    rcases hz with rfl | ⟨k, hk, hex, hz⟩
    · exact ⟨{S.a i}, fun x hx => Or.inl hx, rfl, rfl, pc_singleton _⟩
    · refine ⟨{x | x ∈ S.a i :: S.m i k}, ?_, List.mem_cons_self, List.mem_cons_of_mem _ hz,
        pc_of_isChain (path_chain_left (S.path i k).2)⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, hex, hx⟩
  pcB k := by
    refine pc_of_star (c := S.b k) fun z hz => ?_
    rcases hz with rfl | ⟨i, hi, hex, hz⟩
    · exact ⟨{S.b k}, fun x hx => Or.inl hx, rfl, rfl, pc_singleton _⟩
    · refine ⟨{x | x ∈ S.m i k ++ [S.b k]}, ?_, by simp, by simp [hz],
        pc_of_isChain (path_chain_right (S.path i k).2)⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inr ⟨i, hi, hex, hx⟩
      · exact Or.inl (List.mem_singleton.mp hx)
  dA i j hij := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    rcases hx with rfl | ⟨k, -, -, hk⟩ <;> rcases hx' with h | ⟨k', -, -, hk'⟩
    · exact hij (S.a_inj h)
    · exact S.m_a j k' _ hk' i rfl
    · exact S.m_a i k x hk j h
    · exact S.m_disj i k j k' (fun e => hij (Prod.mk.inj e).1) x hk hk'
  dB k l hkl := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    rcases hx with rfl | ⟨i, -, -, hi⟩ <;> rcases hx' with h | ⟨i', -, -, hi'⟩
    · exact hkl (S.b_inj h)
    · exact S.m_b i' l _ hi' k rfl
    · exact S.m_b i k x hi l h
    · exact S.m_disj i k i' l (fun e => hkl (Prod.mk.inj e).2) x hi hi'
  dAB i k := by
    refine disjoint_left.mpr fun x hx hx' => ?_
    rcases hx with rfl | ⟨k', hA, -, hk'⟩ <;> rcases hx' with h | ⟨i', hB, -, hi'⟩
    · exact S.ab i k h
    · exact S.m_a i' k _ hi' i rfl
    · exact S.m_b i k' x hk' k h
    · by_cases e : (i, k') = (i', k)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
        exact hB hA
      · exact S.m_disj i k' i' k e x hk' hi'

theorem cutModel_A (toA ex : Fin 3 → Fin 3 → Prop) (i : Fin 3) :
    (S.cutModel toA ex).A i = S.cutA toA ex i := rfl

theorem cutModel_B (toA ex : Fin 3 → Fin 3 → Prop) (k : Fin 3) :
    (S.cutModel toA ex).B k = S.cutB toA ex k := rfl

/-- The sets of the two sides are joined along each path that is not excluded. -/
theorem cutModel_touch (toA ex : Fin 3 → Fin 3 → Prop) (i k : Fin 3) (hex : ¬ ex i k) :
    Touch K ((S.cutModel toA ex).A i) ((S.cutModel toA ex).B k) := by
  classical
  have hch := (S.path i k).2
  by_cases hA : toA i k
  · have e : S.a i :: S.m i k ++ [S.b k] = (S.a i :: S.m i k) ++ [S.b k] := rfl
    rw [e] at hch
    have hne : S.a i :: S.m i k ≠ [] := List.cons_ne_nil _ _
    have hadj := (List.isChain_append.mp hch).2.2 _
      (by rw [List.getLast?_eq_some_getLast hne]; rfl) (S.b k) rfl
    refine ⟨_, ?_, _, Or.inl rfl, hadj⟩
    rcases List.mem_cons.mp (List.getLast_mem hne) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨k, hA, hex, h⟩
  · have e : S.a i :: S.m i k ++ [S.b k] = [S.a i] ++ (S.m i k ++ [S.b k]) := rfl
    rw [e] at hch
    have hne : S.m i k ++ [S.b k] ≠ [] := by simp
    have hadj := (List.isChain_append.mp hch).2.2 (S.a i) rfl _
      (by rw [List.head?_eq_some_head hne]; rfl)
    refine ⟨_, Or.inl rfl, _, ?_, hadj⟩
    rcases List.mem_append.mp (List.head_mem hne) with h | h
    · exact Or.inr ⟨i, hA, hex, h⟩
    · exact Or.inl (List.mem_singleton.mp h)

theorem cutA_inH {toA ex : Fin 3 → Fin 3 → Prop} {i : Fin 3} {x : γ} (h : x ∈ S.cutA toA ex i) :
    S.InH x := by
  rcases h with rfl | ⟨k, -, -, h⟩
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr (Or.inr ⟨i, k, h⟩)

theorem cutB_inH {toA ex : Fin 3 → Fin 3 → Prop} {k : Fin 3} {x : γ} (h : x ∈ S.cutB toA ex k) :
    S.InH x := by
  rcases h with rfl | ⟨i, -, -, h⟩
  · exact Or.inr (Or.inl ⟨k, rfl⟩)
  · exact Or.inr (Or.inr ⟨i, k, h⟩)

/-- A set of vertices outside the subdivision misses all sets of a cut model. -/
theorem disj_cutA {Z : Set γ} (hZ : ∀ z ∈ Z, ¬ S.InH z) (toA ex : Fin 3 → Fin 3 → Prop)
    (i : Fin 3) : Disjoint Z ((S.cutModel toA ex).A i) :=
  disjoint_left.mpr fun z hz h => hZ z hz (S.cutA_inH h)

theorem disj_cutB {Z : Set γ} (hZ : ∀ z ∈ Z, ¬ S.InH z) (toA ex : Fin 3 → Fin 3 → Prop)
    (k : Fin 3) : Disjoint Z ((S.cutModel toA ex).B k) :=
  disjoint_left.mpr fun z hz h => hZ z hz (S.cutB_inH h)

/-- The inner part of an excluded path misses all sets of a cut model when it is the only excluded
path. -/
theorem disj_ex_cutA {toA : Fin 3 → Fin 3 → Prop} {i₀ k₀ : Fin 3} (i : Fin 3) :
    Disjoint {x | x ∈ S.m i₀ k₀} ((S.cutModel toA fun i k => (i, k) = (i₀, k₀)).A i) := by
  refine disjoint_left.mpr fun x hx h => ?_
  rcases h with rfl | ⟨k, -, hex, h⟩
  · exact S.m_a i₀ k₀ _ hx i rfl
  · exact S.m_disj i k i₀ k₀ hex x h hx

theorem disj_ex_cutB {toA : Fin 3 → Fin 3 → Prop} {i₀ k₀ : Fin 3} (k : Fin 3) :
    Disjoint {x | x ∈ S.m i₀ k₀} ((S.cutModel toA fun i k => (i, k) = (i₀, k₀)).B k) := by
  refine disjoint_left.mpr fun x hx h => ?_
  rcases h with rfl | ⟨i, -, hex, h⟩
  · exact S.m_b i₀ k₀ _ hx k rfl
  · exact S.m_disj i k i₀ k₀ hex x h hx

end K33Sub

end GraphMinor.Wagner
