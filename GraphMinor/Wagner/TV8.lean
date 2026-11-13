module

public import GraphMinor.Wagner.V8Model
public import GraphMinor.Wagner.HPath

/-!
# Subdivisions of `V_8`

A *subdivision of `V_8`* in `K` (`TV8`) is given by eight distinct branch vertices `w i` and, for each
of the twelve edges `k` of `V_8`, a path `w (v8e1 k) :: I k ++ [w (v8e2 k)]` of `K`, where the inner
parts `I k` are pairwise disjoint and avoid the branch vertices.

Giving each inner part `I k` to one of the two ends of its edge turns the subdivision into a `V_8`
model (`TV8.model`). Adding one more connected set or path to such a model, joining the sets of two
non-adjacent vertices of `V_8`, gives a `K_5` minor (`V8Model.hasK5_of_set`,
`V8Model.hasK5_of_link`).
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

/-- The first ends of the twelve edges of `V_8`: the eight edges of the cycle, then the four
diagonals. -/
def v8e1 : Fin 12 → Fin 8 := ![0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3]

/-- The second ends of the twelve edges of `V_8`. -/
def v8e2 : Fin 12 → Fin 8 := ![1, 2, 3, 4, 5, 6, 7, 0, 4, 5, 6, 7]

theorem v8e_adj : ∀ k, v8.Adj (v8e1 k) (v8e2 k) := by decide

theorem v8_exists_edge : ∀ i j, v8.Adj i j →
    ∃ k, (v8e1 k = i ∧ v8e2 k = j) ∨ (v8e1 k = j ∧ v8e2 k = i) := by decide

theorem v8_choice_vertex : ∀ k r, r ≠ v8e1 k → r ≠ v8e2 k →
    ∃ b : Bool, ¬ v8.Adj (if b then v8e1 k else v8e2 k) r := by decide

theorem v8_choice_edge : ∀ k k', k ≠ k' → ∃ b b' : Bool,
    (if b then v8e1 k else v8e2 k) ≠ (if b' then v8e1 k' else v8e2 k') ∧
      ¬ v8.Adj (if b then v8e1 k else v8e2 k) (if b' then v8e1 k' else v8e2 k') := by decide

theorem v8_third : ∀ k, ∃ r, r ≠ v8e1 k ∧ r ≠ v8e2 k := by decide

theorem v8_tri : ∀ a b c : Fin 8, a ≠ b → b ≠ c → a ≠ c →
    ¬ v8.Adj a b ∨ ¬ v8.Adj b c ∨ ¬ v8.Adj a c := by decide

variable {γ : Type*} {K : SimpleGraph γ}

/-- A set `Y` is preconnected when it has a vertex `c` such that every vertex of `Y` lies with `c`
in a preconnected subset of `Y`. -/
theorem pc_of_star {Y : Set γ} {c : γ}
    (h : ∀ z ∈ Y, ∃ Z ⊆ Y, c ∈ Z ∧ z ∈ Z ∧ (K.induce Z).Preconnected) :
    (K.induce Y).Preconnected := by
  have hr : ∀ z (hz : z ∈ Y), ∃ hc : c ∈ Y, (K.induce Y).Reachable ⟨z, hz⟩ ⟨c, hc⟩ := by
    intro z hz
    obtain ⟨Z, hZY, hcZ, hzZ, hpc⟩ := h z hz
    exact ⟨hZY hcZ, induce_reach_mono hZY (hpc ⟨z, hzZ⟩ ⟨c, hcZ⟩)⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨hc, hu'⟩ := hr u hu
  obtain ⟨hc', hv'⟩ := hr v hv
  exact hu'.trans (Reachable.symm hv')

namespace V8Model

variable (D : V8Model K)

/-- The branch sets after adding `Z` to the set of `p`. -/
def addM (p : Fin 8) (Z : Set γ) (i : Fin 8) : Set γ := if i = p then D.M p ∪ Z else D.M i

theorem addM_self (p : Fin 8) (Z : Set γ) : D.addM p Z p = D.M p ∪ Z := by
  unfold addM; simp

theorem addM_ne {p i : Fin 8} (Z : Set γ) (h : i ≠ p) : D.addM p Z i = D.M i := by
  unfold addM; simp [h]

theorem sub_addM (p : Fin 8) (Z : Set γ) (i : Fin 8) : D.M i ⊆ D.addM p Z i := by
  by_cases h : i = p
  · subst h; rw [addM_self]; exact subset_union_left
  · rw [D.addM_ne Z h]

/-- Add a set `Z` that is disjoint from all branch sets and touches the set of `p` to the set of
`p`. -/
def addTo (p : Fin 8) (Z : Set γ) (hZ : (K.induce Z).Preconnected) (hZp : Touch K Z (D.M p))
    (hZd : ∀ i, Disjoint Z (D.M i)) : V8Model K where
  M := D.addM p Z
  ne i := (D.ne i).mono (D.sub_addM p Z i)
  pc i := by
    by_cases h : i = p
    · subst h
      rw [addM_self]
      exact pc_union_touch (D.pc i) hZ fun _ _ => hZp.symm
    · rw [D.addM_ne Z h]
      exact D.pc i
  disj i j hij := by
    by_cases hi : i = p
    · subst hi
      rw [addM_self, D.addM_ne Z (Ne.symm hij)]
      exact disjoint_union_left.mpr ⟨D.disj _ _ hij, hZd j⟩
    · by_cases hj : j = p
      · subst hj
        rw [addM_self, D.addM_ne Z hi]
        exact disjoint_union_right.mpr ⟨D.disj _ _ hij, (hZd i).symm⟩
      · rw [D.addM_ne Z hi, D.addM_ne Z hj]
        exact D.disj _ _ hij
  touch i j hij := (D.touch i j hij).mono (D.sub_addM p Z i) (D.sub_addM p Z j)

/-- A preconnected set disjoint from all branch sets and touching the sets of two distinct
non-adjacent vertices `p`, `q` of `V_8` gives a `K_5` minor. -/
theorem hasK5_of_set {p q : Fin 8} (hpq : p ≠ q) (hna : ¬ v8.Adj p q) {Z : Set γ}
    (hZ : (K.induce Z).Preconnected) (hZp : Touch K Z (D.M p)) (hZq : Touch K Z (D.M q))
    (hZd : ∀ i, Disjoint Z (D.M i)) : HasK5MinorSimple K := by
  refine (D.addTo p Z hZ hZp hZd).hasK5 hpq hna ?_
  show Touch K (D.addM p Z p) (D.addM p Z q)
  rw [addM_self, D.addM_ne Z (Ne.symm hpq)]
  exact hZq.mono subset_union_right subset_rfl

/-- A path from the set of `p` to the set of `q`, whose inner vertices lie in no branch set, gives a
`K_5` minor when `p ≠ q` are not adjacent in `V_8`. -/
theorem hasK5_of_link {p q : Fin 8} (hpq : p ≠ q) (hna : ¬ v8.Adj p q) {a b : γ}
    {mid : List γ} (ha : a ∈ D.M p) (hb : b ∈ D.M q) (hch : (a :: mid ++ [b]).IsChain K.Adj)
    (hmid : ∀ z ∈ mid, ∀ i, z ∉ D.M i) : HasK5MinorSimple K := by
  rcases mid with _ | ⟨c, mid'⟩
  · have hab : K.Adj a b := by simpa using hch
    exact D.hasK5 hpq hna ⟨a, ha, b, hb, hab⟩
  · have e : a :: (c :: mid') ++ [b] = [a] ++ (c :: mid' ++ [b]) := rfl
    rw [e] at hch
    have hch2 := hch.right_of_append
    have e2 : c :: mid' ++ [b] = (c :: mid') ++ [b] := rfl
    rw [e2] at hch2
    have hne : c :: mid' ≠ [] := List.cons_ne_nil _ _
    refine D.hasK5_of_set hpq hna (Z := {x | x ∈ c :: mid'}) (pc_of_isChain hch2.left_of_append)
      ?_ ?_ ?_
    · have := (List.isChain_append.mp hch).2.2 a rfl c rfl
      exact ⟨c, List.mem_cons_self, a, ha, this.symm⟩
    · have := (List.isChain_append.mp hch2).2.2 ((c :: mid').getLast hne)
        (by rw [List.getLast?_eq_some_getLast hne]; rfl) b rfl
      exact ⟨_, List.getLast_mem hne, b, hb, this⟩
    · intro i
      exact disjoint_left.mpr fun z hz hzi => hmid z hz i hzi

end V8Model

/-- A subdivision of `V_8` in `K`. -/
structure TV8 (K : SimpleGraph γ) where
  /-- The branch vertices. -/
  w : Fin 8 → γ
  /-- The inner vertices of the path of each edge of `V_8`. -/
  I : Fin 12 → List γ
  w_inj : Injective w
  path : ∀ k, (w (v8e1 k) :: I k ++ [w (v8e2 k)]).Nodup ∧
    (w (v8e1 k) :: I k ++ [w (v8e2 k)]).IsChain K.Adj
  I_disj : ∀ k k', k ≠ k' → ∀ x ∈ I k, x ∉ I k'
  I_w : ∀ k x, x ∈ I k → ∀ i, x ≠ w i

namespace TV8

variable (T : TV8 K)

/-- The end of edge `k` that receives the inner vertices of its path. -/
def owner (τ : Fin 12 → Bool) (k : Fin 12) : Fin 8 := if τ k then v8e1 k else v8e2 k

/-- The branch set of `i` when the inner parts are given out by `τ`. -/
def MS (τ : Fin 12 → Bool) (i : Fin 8) : Set γ :=
  {x | x = T.w i ∨ ∃ k, owner τ k = i ∧ x ∈ T.I k}

theorem pc_MS (τ : Fin 12 → Bool) (i : Fin 8) : (K.induce (T.MS τ i)).Preconnected := by
  refine pc_of_star (c := T.w i) fun z hz => ?_
  rcases hz with rfl | ⟨k, hk, hz⟩
  · exact ⟨{T.w i}, fun x hx => Or.inl hx, rfl, rfl, pc_singleton _⟩
  · have hch := (T.path k).2
    by_cases hτ : τ k = true
    · have hi : v8e1 k = i := by simp only [owner, hτ, ite_true] at hk; exact hk
      subst hi
      refine ⟨{x | x ∈ T.w (v8e1 k) :: T.I k}, ?_, List.mem_cons_self,
        List.mem_cons_of_mem _ hz, pc_of_isChain hch.left_of_append⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr ⟨k, hk, hx⟩
    · have hi : v8e2 k = i := by simp only [owner, hτ] at hk; exact hk
      subst hi
      have e : T.w (v8e1 k) :: T.I k ++ [T.w (v8e2 k)] = [T.w (v8e1 k)] ++ (T.I k ++ [T.w (v8e2 k)]) :=
        rfl
      rw [e] at hch
      refine ⟨{x | x ∈ T.I k ++ [T.w (v8e2 k)]}, ?_, by simp, by simp [hz],
        pc_of_isChain hch.right_of_append⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inr ⟨k, hk, hx⟩
      · exact Or.inl (List.mem_singleton.mp hx)

theorem disj_MS (τ : Fin 12 → Bool) (i j : Fin 8) (hij : i ≠ j) :
    Disjoint (T.MS τ i) (T.MS τ j) := by
  refine disjoint_left.mpr fun x hi hj => ?_
  rcases hi with rfl | ⟨k, hk, hx⟩ <;> rcases hj with h | ⟨k', hk', hx'⟩
  · exact hij (T.w_inj h)
  · exact T.I_w k' _ hx' i rfl
  · exact T.I_w k _ hx j h
  · by_cases hkk : k = k'
    · subst hkk
      exact hij (hk.symm.trans hk')
    · exact T.I_disj k k' hkk x hx hx'

theorem touch_MS (τ : Fin 12 → Bool) (k : Fin 12) :
    Touch K (T.MS τ (v8e1 k)) (T.MS τ (v8e2 k)) := by
  have hch := (T.path k).2
  by_cases hτ : τ k = true
  · have e : T.w (v8e1 k) :: T.I k ++ [T.w (v8e2 k)] = (T.w (v8e1 k) :: T.I k) ++ [T.w (v8e2 k)] :=
      rfl
    rw [e] at hch
    have hne : T.w (v8e1 k) :: T.I k ≠ [] := List.cons_ne_nil _ _
    have hadj := (List.isChain_append.mp hch).2.2 _
      (by rw [List.getLast?_eq_some_getLast hne]; rfl) (T.w (v8e2 k)) rfl
    refine ⟨_, ?_, _, Or.inl rfl, hadj⟩
    have hmem := List.getLast_mem hne
    rcases List.mem_cons.mp hmem with h | h
    · exact Or.inl h
    · exact Or.inr ⟨k, by simp [owner, hτ], h⟩
  · have e : T.w (v8e1 k) :: T.I k ++ [T.w (v8e2 k)] = [T.w (v8e1 k)] ++ (T.I k ++ [T.w (v8e2 k)]) :=
      rfl
    rw [e] at hch
    have hne : T.I k ++ [T.w (v8e2 k)] ≠ [] := by simp
    have hadj := (List.isChain_append.mp hch).2.2 (T.w (v8e1 k)) rfl _
      (by rw [List.head?_eq_some_head hne]; rfl)
    refine ⟨_, Or.inl rfl, _, ?_, hadj⟩
    have hmem := List.head_mem hne
    rcases List.mem_append.mp hmem with h | h
    · exact Or.inr ⟨k, by simp [owner, hτ], h⟩
    · exact Or.inl (List.mem_singleton.mp h)

/-- The `V_8` model of a subdivision, with the inner parts given out by `τ`. -/
def model (τ : Fin 12 → Bool) : V8Model K where
  M := T.MS τ
  ne i := ⟨T.w i, Or.inl rfl⟩
  pc := T.pc_MS τ
  disj := T.disj_MS τ
  touch i j hij := by
    obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := v8_exists_edge i j hij
    · exact T.touch_MS τ k
    · exact (T.touch_MS τ k).symm

/-- The vertices of the subdivision. -/
def VS : Set γ := {x | (∃ i, x = T.w i) ∨ ∃ k, x ∈ T.I k}

theorem MS_sub (τ : Fin 12 → Bool) (i : Fin 8) : T.MS τ i ⊆ T.VS := by
  rintro x (rfl | ⟨k, -, hx⟩)
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨k, hx⟩

end TV8

end GraphMinor.Wagner
