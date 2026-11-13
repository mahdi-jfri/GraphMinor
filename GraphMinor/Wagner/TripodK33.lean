module

public import GraphMinor.Wagner.TripodLists
public import GraphMinor.Wagner.ContractibleEdge

/-!
# A subdivision of `K_{3,3}` from three paths and a third branch vertex

Let three paths join `u` to `v`, meeting only at their ends, and let `s i` be an inner vertex of
the `i`-th path. If a vertex `z` off these paths is joined to the three vertices `s i` by paths that
are disjoint except at `z` and avoid the first three paths except at `s i`, then `K` contains a
subdivision of `K_{3,3}` with sides `{u, v, z}` and `{s 0, s 1, s 2}` (`Theta.hasK33Subdiv`).

A tripod of a society whose vertices of `Ω` are all adjacent to a vertex `z` outside `R` gives such
paths (`Tripod.thetaOuter`).
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

/-- The facts we use from a path `u :: pre ++ s :: post ++ [v]` having distinct entries. -/
theorem nodup_five {u s v : γ} {pre post : List γ} (h : (u :: pre ++ s :: post ++ [v]).Nodup) :
    u ∉ pre ∧ u ≠ s ∧ u ∉ post ∧ u ≠ v ∧ s ∉ pre ∧ s ∉ post ∧ s ≠ v ∧ v ∉ pre ∧ v ∉ post ∧
      (∀ x ∈ pre, x ∉ post) := by
  have e : u :: pre ++ s :: post ++ [v] = u :: (pre ++ s :: (post ++ [v])) := by simp
  rw [e, List.nodup_cons, List.nodup_append, List.nodup_cons, List.nodup_append] at h
  obtain ⟨hu, -, ⟨hs, -, -, hpv⟩, hdis⟩ := h
  refine ⟨fun h => hu (by simp [h]), fun h => hu (by simp [h]), fun h => hu (by simp [h]),
    fun h => hu (by simp [h]), fun h => hdis s h s (by simp) rfl, fun h => hs (by simp [h]),
    fun h => hs (by simp [h]), fun h => hdis v h v (by simp) rfl, fun h => hpv v h v (by simp) rfl,
    fun x hx hx' => hdis x hx x (by simp [hx']) rfl⟩

theorem isChain_reverse_of_symm {l : List γ} (h : l.IsChain K.Adj) : l.reverse.IsChain K.Adj :=
  List.isChain_reverse.mpr (h.imp fun _ _ hab => hab.symm)

/-- Three paths `u :: pre i ++ s i :: post i ++ [v]` from `u` to `v` that meet only at their ends,
and three paths `z :: m i ++ [s i]` from a vertex `z` off the first paths to their inner vertices
`s i`, disjoint except at `z` and avoiding the first paths except at `s i`. -/
structure Theta (K : SimpleGraph γ) where
  /-- One end of the first three paths. -/
  u : γ
  /-- The other end of the first three paths. -/
  v : γ
  /-- The common end of the last three paths. -/
  z : γ
  /-- The inner vertices where the last three paths end. -/
  s : Fin 3 → γ
  /-- The part of the `i`-th path between `u` and `s i`. -/
  pre : Fin 3 → List γ
  /-- The part of the `i`-th path between `s i` and `v`. -/
  post : Fin 3 → List γ
  /-- The inner part of the path from `z` to `s i`. -/
  m : Fin 3 → List γ
  huv : u ≠ v
  hP : ∀ i, (u :: pre i ++ s i :: post i ++ [v]).Nodup ∧
    (u :: pre i ++ s i :: post i ++ [v]).IsChain K.Adj
  hPP : ∀ i j, i ≠ j → ∀ x, x ∈ u :: pre i ++ s i :: post i ++ [v] →
    x ∈ u :: pre j ++ s j :: post j ++ [v] → x = u ∨ x = v
  hC : ∀ i, (z :: m i ++ [s i]).Nodup ∧ (z :: m i ++ [s i]).IsChain K.Adj
  hmP : ∀ i j x, x ∈ m i → x ∉ u :: pre j ++ s j :: post j ++ [v]
  hmm : ∀ i j, i ≠ j → ∀ x, x ∈ m i → x ∉ m j
  hzP : ∀ i, z ∉ u :: pre i ++ s i :: post i ++ [v]

namespace Theta

variable (T : Theta K)

/-- The vertex `x` lies on the `k`-th path from `u` to `v`. -/
def InP (k : Fin 3) (x : γ) : Prop :=
  x = T.u ∨ x ∈ T.pre k ∨ x = T.s k ∨ x ∈ T.post k ∨ x = T.v

theorem mem_iff_inP (k : Fin 3) (x : γ) :
    x ∈ T.u :: T.pre k ++ T.s k :: T.post k ++ [T.v] ↔ T.InP k x := by
  simp [InP]

theorem inP_u (k : Fin 3) : T.InP k T.u := Or.inl rfl
theorem inP_v (k : Fin 3) : T.InP k T.v := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
theorem inP_s (k : Fin 3) : T.InP k (T.s k) := Or.inr (Or.inr (Or.inl rfl))
theorem inP_pre {k : Fin 3} {x : γ} (h : x ∈ T.pre k) : T.InP k x := Or.inr (Or.inl h)
theorem inP_post {k : Fin 3} {x : γ} (h : x ∈ T.post k) : T.InP k x :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem nd (k : Fin 3) :
    T.u ∉ T.pre k ∧ T.u ≠ T.s k ∧ T.u ∉ T.post k ∧ T.u ≠ T.v ∧ T.s k ∉ T.pre k ∧
      T.s k ∉ T.post k ∧ T.s k ≠ T.v ∧ T.v ∉ T.pre k ∧ T.v ∉ T.post k ∧
      (∀ x ∈ T.pre k, x ∉ T.post k) :=
  nodup_five (T.hP k).1

theorem cross {k k' : Fin 3} (h : k ≠ k') {x : γ} (hx : T.InP k x) (hx' : T.InP k' x) :
    x = T.u ∨ x = T.v :=
  T.hPP k k' h x ((T.mem_iff_inP k x).mpr hx) ((T.mem_iff_inP k' x).mpr hx')

theorem m_not_inP {i k : Fin 3} {x : γ} (h : x ∈ T.m i) : ¬ T.InP k x := fun h' =>
  T.hmP i k x h ((T.mem_iff_inP k x).mpr h')

theorem z_not_inP (k : Fin 3) : ¬ T.InP k T.z := fun h => T.hzP k ((T.mem_iff_inP k _).mpr h)

theorem s_inj : Injective T.s := by
  intro i j hij
  by_contra hne
  rcases T.cross hne (T.inP_s i) (hij ▸ T.inP_s j) with h | h
  · exact (T.nd i).2.1 h.symm
  · exact (T.nd i).2.2.2.2.2.2.1 h

theorem s_ne_u (k : Fin 3) : T.s k ≠ T.u := fun h => (T.nd k).2.1 h.symm
theorem s_ne_v (k : Fin 3) : T.s k ≠ T.v := (T.nd k).2.2.2.2.2.2.1
theorem z_ne_s (k : Fin 3) : T.z ≠ T.s k := fun h => T.z_not_inP k (h ▸ T.inP_s k)
theorem z_ne_u : T.z ≠ T.u := fun h => T.z_not_inP 0 (h ▸ T.inP_u 0)
theorem z_ne_v : T.z ≠ T.v := fun h => T.z_not_inP 0 (h ▸ T.inP_v 0)
theorem z_not_mem_m (k : Fin 3) : T.z ∉ T.m k := by
  have hnd := (T.hC k).1
  rw [List.cons_append, List.nodup_cons] at hnd
  exact fun h => hnd.1 (List.mem_append_left _ h)

/-- The list `L i j` of the subdivision: from `u`, `v` or `z` to `s j`. -/
def L : Fin 3 → Fin 3 → List γ
  | 0, j => T.u :: T.pre j ++ [T.s j]
  | 1, j => T.v :: (T.post j).reverse ++ [T.s j]
  | 2, j => T.z :: T.m j ++ [T.s j]

theorem mem_L0 (j : Fin 3) (x : γ) : x ∈ T.L 0 j ↔ x = T.u ∨ x ∈ T.pre j ∨ x = T.s j := by
  simp [L]
theorem mem_L1 (j : Fin 3) (x : γ) : x ∈ T.L 1 j ↔ x = T.v ∨ x ∈ T.post j ∨ x = T.s j := by
  simp [L]
theorem mem_L2 (j : Fin 3) (x : γ) : x ∈ T.L 2 j ↔ x = T.z ∨ x ∈ T.m j ∨ x = T.s j := by
  simp [L]

/-- The branch vertices on the first side. -/
def a : Fin 3 → γ := ![T.u, T.v, T.z]

/-- Membership in the list `L i j` puts `x` on the `j`-th path from `u` to `v`, or on the `j`-th
path from `z`. -/
theorem L0_inP {j : Fin 3} {x : γ} (h : x ∈ T.L 0 j) : T.InP j x := by
  rcases (T.mem_L0 j x).mp h with rfl | h | rfl
  · exact T.inP_u j
  · exact T.inP_pre h
  · exact T.inP_s j

theorem L1_inP {j : Fin 3} {x : γ} (h : x ∈ T.L 1 j) : T.InP j x := by
  rcases (T.mem_L1 j x).mp h with rfl | h | rfl
  · exact T.inP_v j
  · exact T.inP_post h
  · exact T.inP_s j

/-- The pairs `(0, j)` and `(0, j')`. -/
theorem disj00 {j j' : Fin 3} (hne : j ≠ j') {x : γ} (hx : x ∈ T.L 0 j) (hx' : x ∈ T.L 0 j') :
    x = T.u := by
  rcases T.cross hne (T.L0_inP hx) (T.L0_inP hx') with h | rfl
  · exact h
  · rcases (T.mem_L0 j _).mp hx with h | h | h
    · exact h
    · exact ((T.nd j).2.2.2.2.2.2.2.1 h).elim
    · exact (T.s_ne_v j h.symm).elim

/-- The pairs `(1, j)` and `(1, j')`. -/
theorem disj11 {j j' : Fin 3} (hne : j ≠ j') {x : γ} (hx : x ∈ T.L 1 j) (hx' : x ∈ T.L 1 j') :
    x = T.v := by
  rcases T.cross hne (T.L1_inP hx) (T.L1_inP hx') with rfl | h
  · rcases (T.mem_L1 j _).mp hx with h | h | h
    · exact h
    · exact ((T.nd j).2.2.1 h).elim
    · exact (T.s_ne_u j h.symm).elim
  · exact h

/-- The pairs `(0, j)` and `(1, j')`. -/
theorem disj01 {j j' : Fin 3} {x : γ} (hx : x ∈ T.L 0 j) (hx' : x ∈ T.L 1 j') :
    j = j' ∧ x = T.s j := by
  by_cases hjj : j = j'
  · subst hjj
    refine ⟨rfl, ?_⟩
    rcases (T.mem_L0 j x).mp hx with rfl | h | h
    · rcases (T.mem_L1 j _).mp hx' with h | h | h
      · exact (T.huv h).elim
      · exact ((T.nd j).2.2.1 h).elim
      · exact (T.s_ne_u j h.symm).elim
    · rcases (T.mem_L1 j x).mp hx' with rfl | h' | h'
      · exact ((T.nd j).2.2.2.2.2.2.2.1 h).elim
      · exact ((T.nd j).2.2.2.2.2.2.2.2.2 x h h').elim
      · exact h'
    · exact h
  · exfalso
    rcases T.cross hjj (T.L0_inP hx) (T.L1_inP hx') with rfl | rfl
    · rcases (T.mem_L1 j' _).mp hx' with h | h | h
      · exact T.huv h
      · exact (T.nd j').2.2.1 h
      · exact T.s_ne_u j' h.symm
    · rcases (T.mem_L0 j _).mp hx with h | h | h
      · exact T.huv h.symm
      · exact (T.nd j).2.2.2.2.2.2.2.1 h
      · exact T.s_ne_v j h.symm

/-- The pairs `(k, j)` and `(2, j')` for a list `L k j` on the `j`-th path from `u` to `v`. -/
theorem disjP2 {j j' : Fin 3} {x : γ} (hx : T.InP j x) (hx' : x ∈ T.L 2 j') :
    j = j' ∧ x = T.s j := by
  rcases (T.mem_L2 j' x).mp hx' with rfl | h' | rfl
  · exact (T.z_not_inP j hx).elim
  · exact (T.m_not_inP h' hx).elim
  · by_cases hjj : j = j'
    · subst hjj
      exact ⟨rfl, rfl⟩
    · exfalso
      rcases T.cross hjj hx (T.inP_s j') with h | h
      · exact T.s_ne_u j' h
      · exact T.s_ne_v j' h

/-- The pairs `(2, j)` and `(2, j')`. -/
theorem disj22 {j j' : Fin 3} (hne : j ≠ j') {x : γ} (hx : x ∈ T.L 2 j) (hx' : x ∈ T.L 2 j') :
    x = T.z := by
  rcases (T.mem_L2 j x).mp hx with h | h | rfl
  · exact h
  · exfalso
    rcases (T.mem_L2 j' x).mp hx' with rfl | h' | rfl
    · exact T.z_not_mem_m j h
    · exact T.hmm j j' hne x h h'
    · exact T.m_not_inP h (T.inP_s j')
  · exfalso
    rcases (T.mem_L2 j' _).mp hx' with h' | h' | h'
    · exact T.z_ne_s j h'.symm
    · exact T.m_not_inP h' (T.inP_s j)
    · exact hne (T.s_inj h')

theorem pathList (i j : Fin 3) : HP25.IsPathList K Set.univ (T.L i j) := by
  refine ⟨?_, ?_, fun _ _ => mem_univ _⟩
  · fin_cases i
    · have h := (T.hP j).1
      have : T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v] =
          (T.u :: T.pre j ++ [T.s j]) ++ (T.post j ++ [T.v]) := by simp
      rw [this] at h
      exact (List.nodup_append.mp h).1
    · have h := (T.hP j).1
      have : T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v] =
          (T.u :: T.pre j) ++ (T.s j :: T.post j ++ [T.v]) := by simp
      rw [this] at h
      have h2 := (List.nodup_append.mp h).2.1
      have : T.L 1 j = (T.s j :: T.post j ++ [T.v]).reverse := by simp [L]
      show (T.L 1 j).Nodup
      rw [this]
      exact List.nodup_reverse.mpr h2
    · exact (T.hC j).1
  · fin_cases i
    · have h := (T.hP j).2
      have : T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v] =
          (T.u :: T.pre j ++ [T.s j]) ++ (T.post j ++ [T.v]) := by simp
      rw [this] at h
      exact h.left_of_append
    · have h := (T.hP j).2
      have : T.u :: T.pre j ++ T.s j :: T.post j ++ [T.v] =
          (T.u :: T.pre j) ++ (T.s j :: T.post j ++ [T.v]) := by simp
      rw [this] at h
      have : T.L 1 j = (T.s j :: T.post j ++ [T.v]).reverse := by simp [L]
      show (T.L 1 j).IsChain K.Adj
      rw [this]
      exact isChain_reverse_of_symm h.right_of_append
    · exact (T.hC j).2

/-- A `Theta` gives a subdivision of `K_{3,3}`. -/
theorem hasK33Subdiv (T : Theta K) : HasK33Subdiv K := by
  refine ⟨T.a, T.s, T.L, ?_, T.s_inj, ?_, T.pathList, ?_, ?_⟩
  · intro i j hij
    have h1 := T.z_ne_u
    have h2 := T.z_ne_v
    have h3 := T.huv
    fin_cases i <;> fin_cases j <;> simp_all [a, eq_comm]
  · intro i j
    fin_cases i
    · exact fun h => T.s_ne_u j h.symm
    · exact fun h => T.s_ne_v j h.symm
    · exact T.z_ne_s j
  · intro i j
    fin_cases i
    · exact ⟨T.pre j, rfl⟩
    · exact ⟨(T.post j).reverse, rfl⟩
    · exact ⟨T.m j, rfl⟩
  · intro i j i' j' hne x hx hx'
    have ha0 : T.a 0 = T.u := rfl
    have ha1 : T.a 1 = T.v := rfl
    have ha2 : T.a 2 = T.z := rfl
    fin_cases i <;> fin_cases i'
    · have hjj : j ≠ j' := fun h => hne (by simp [h])
      exact Or.inl ⟨rfl, T.disj00 hjj hx hx'⟩
    · obtain ⟨rfl, h⟩ := T.disj01 hx hx'
      exact Or.inr ⟨rfl, h⟩
    · obtain ⟨rfl, h⟩ := T.disjP2 (T.L0_inP hx) hx'
      exact Or.inr ⟨rfl, h⟩
    · obtain ⟨rfl, h⟩ := T.disj01 hx' hx
      exact Or.inr ⟨rfl, h⟩
    · have hjj : j ≠ j' := fun h => hne (by simp [h])
      exact Or.inl ⟨rfl, T.disj11 hjj hx hx'⟩
    · obtain ⟨rfl, h⟩ := T.disjP2 (T.L1_inP hx) hx'
      exact Or.inr ⟨rfl, h⟩
    · obtain ⟨rfl, h⟩ := T.disjP2 (T.L0_inP hx') hx
      exact Or.inr ⟨rfl, h⟩
    · obtain ⟨rfl, h⟩ := T.disjP2 (T.L1_inP hx') hx
      exact Or.inr ⟨rfl, h⟩
    · have hjj : j ≠ j' := fun h => hne (by simp [h])
      exact Or.inl ⟨rfl, T.disj22 hjj hx hx'⟩

end Theta

/-- A tripod whose redirecting paths end at neighbours of a vertex `z` outside `R` gives a
`Theta`, with `z` as the third branch vertex. -/
def Tripod.thetaOuter {R Ω : Set γ} (T : Tripod K R Ω) {z : γ} (hzR : z ∉ R)
    (hzt : ∀ i, K.Adj z (T.t i)) : Theta K where
  u := T.u
  v := T.v
  z := z
  s := T.s
  pre := T.pre
  post := T.post
  m := fun i => (T.r i).reverse
  huv := T.huv
  hP i := ⟨(T.hp i).1, (T.hp i).2.1⟩
  hPP := T.hpp
  hC i := by
    have e : z :: (T.r i).reverse ++ [T.s i] = z :: (T.s i :: T.r i).reverse := by simp
    rw [e]
    obtain ⟨hnd, hch, hR, -, hlast⟩ := T.hq i
    refine ⟨List.nodup_cons.mpr ⟨fun h => hzR (hR z (List.mem_reverse.mp h)),
      List.nodup_reverse.mpr hnd⟩, List.isChain_cons.mpr ⟨?_, isChain_reverse_of_symm hch⟩⟩
    intro y hy
    rw [List.head?_reverse, hlast] at hy
    cases hy
    exact hzt i
  hmP i j x hx := T.hqX i j x (List.mem_reverse.mp hx)
  hmm i j hij x hx hx' :=
    T.hqq i j hij x (List.mem_cons_of_mem _ (List.mem_reverse.mp hx))
      (List.mem_cons_of_mem _ (List.mem_reverse.mp hx'))
  hzP i h := hzR ((T.hp i).2.2.1 z h)

end GraphMinor.Wagner
