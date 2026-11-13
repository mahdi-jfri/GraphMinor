module

public import GraphMinor.Compute.Algorithm41Aux3

/-!
# Set-Union Arena, Backward-Sweep Materialization, and Base-Table Step for GM XIII (4.1)

This file develops the second part of the Word RAM implementation of Algorithm (4.1) of Robertson
and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem* (pages 75–76):

1. **Unrolled bounded command sequences (`seqRange`, `Exec.seqRange`) and the set-union arena
   (`evalArena`, `ArenaWF`, `materializeArenaProg`):**
   Represents vertex subsets `V(G_u) ⊆ V(G)` and edge subsets `E(G_u) ⊆ E(G)` of intermediate
   models during the bottom-up dynamic program as pointers into an append-only union-tree arena,
   supporting $O(1)$-time singleton and union allocation and $O(K + N)$-time flat backward-sweep
   materialization into `bitSetList`.
2. **Working table buffers (`ValidPieceBuffer`), canonical local base configurations (`bcfg < 72`),
   and $O(1)$-time base-table initialization (`treeBaseStepProg`, `isoBaseStepProg`):**
   Proves that every base piece `(VA, EA, ZA)` with `|VA| ≤ 2` and `|EA| ≤ 1` is isomorphic via
   `finsetRootFn VA` and `finsetRootFn EA` to `(canonLocDigraph bcfg, canonLocRoots bcfg)` for a
   packed configuration index `bcfg < 72`, and verifies the Word RAM programs initializing Buffer A
   (at a branch-decomposition tree node `x`) and Buffer B (at an isolated vertex `v`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Unrolled Command Sequences (`seqRange`) and Set-Union Arena (`evalArena`) -/

/-- Execute `f 0; f 1; ...; f (K - 1)` in sequence without requiring a Word RAM loop counter. -/
def seqRange : ℕ → (ℕ → Cmd) → Cmd
  | 0, _ => .skip
  | k + 1, f => .seq (seqRange k f) (f k)

theorem Exec.seqRange {w K c : ℕ} {f : ℕ → Cmd} (P : ℕ → State → Prop)
    {s₀ : State} (h0 : P 0 s₀)
    (hstep : ∀ k < K, ∀ s, P k s → ∃ s' t, Exec w (f k) s s' t ∧ t ≤ c ∧ P (k + 1) s') :
    ∃ s' t', Exec w (seqRange K f) s₀ s' t' ∧ t' ≤ 1 + c * K ∧ P K s' := by
  induction K with
  | zero => exact ⟨s₀, 1, .skip s₀, by omega, h0⟩
  | succ k ih =>
    rcases ih (fun i hi => hstep i (by omega)) with ⟨s₁, t₁, hex₁, ht₁, hP₁⟩
    rcases hstep k (Nat.lt_succ_self k) s₁ hP₁ with ⟨s₂, t₂, hex₂, ht₂, hP₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hP₂⟩
    rw [Nat.mul_succ]
    omega

/-- Prefix `{u : Fin N | u.1 < k}` of `Fin N`, used to state invariants of `seqRange N`. -/
def finPrefix (N k : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun u : Fin N => u.1 < k)

@[simp]
theorem finPrefix_zero (N : ℕ) : finPrefix N 0 = ∅ := by
  ext u
  simp [finPrefix]

theorem finPrefix_succ {N k : ℕ} (hk : k < N) :
    finPrefix N (k + 1) = insert ⟨k, hk⟩ (finPrefix N k) := by
  ext u
  simp only [finPrefix, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

@[simp]
theorem finPrefix_self (N : ℕ) : finPrefix N N = Finset.univ := by
  ext u
  simp [finPrefix]

/-- Evaluate pointer `p : ℕ` in a set-union arena `(L_kd, L_v1, L_v2)` over `Fin N`:
- `p = 0` evaluates to `∅`.
- For `p > 0`:
  - `kd = 1` evaluates to `{⟨v1, _⟩}` (if `v1 < N`),
  - `kd = 2` evaluates to `evalArena ... (min v1 (p - 1)) ∪ evalArena ... (min v2 (p - 1))`,
  - any other `kd` evaluates to `∅`. -/
def evalArena (N : ℕ) (L_kd L_v1 L_v2 : List ℕ) : ℕ → Finset (Fin N)
  | 0 => ∅
  | p + 1 =>
    let kd := L_kd.getD (p + 1) 0
    let v1 := L_v1.getD (p + 1) 0
    let v2 := L_v2.getD (p + 1) 0
    if kd = 1 then
      if h : v1 < N then {⟨v1, h⟩} else ∅
    else if kd = 2 then
      evalArena N L_kd L_v1 L_v2 (Nat.min v1 p) ∪ evalArena N L_kd L_v1 L_v2 (Nat.min v2 p)
    else
      ∅
termination_by p => p
decreasing_by
  all_goals exact Nat.lt_succ_of_le (Nat.min_le_right _ p)

@[simp]
theorem evalArena_zero (N : ℕ) (L_kd L_v1 L_v2 : List ℕ) :
    evalArena N L_kd L_v1 L_v2 0 = ∅ := by
  unfold evalArena
  rfl

theorem evalArena_succ (N : ℕ) (L_kd L_v1 L_v2 : List ℕ) (p : ℕ) :
    evalArena N L_kd L_v1 L_v2 (p + 1) =
      let kd := L_kd.getD (p + 1) 0
      let v1 := L_v1.getD (p + 1) 0
      let v2 := L_v2.getD (p + 1) 0
      if kd = 1 then
        if h : v1 < N then {⟨v1, h⟩} else ∅
      else if kd = 2 then
        evalArena N L_kd L_v1 L_v2 (Nat.min v1 p) ∪ evalArena N L_kd L_v1 L_v2 (Nat.min v2 p)
      else
        ∅ := by
  conv_lhs => unfold evalArena

/-- Well-formedness of an arena `(L_kd, L_v1, L_v2)` up to active node count `K`:
- `1 ≤ K` and all three lists have length at least `K`,
- node `0` has `kd = 0`,
- every node `p < K` has `kd ≤ 2`, with `v1 = 0 ∧ v2 = 0` when `kd = 0`, `v1 < N ∧ v2 = 0` when
  `kd = 1`, and `v1 < p ∧ v2 < p` when `kd = 2`. -/
def ArenaWF (N K : ℕ) (L_kd L_v1 L_v2 : List ℕ) : Prop :=
  1 ≤ K ∧
  K ≤ L_kd.length ∧ L_v1.length = L_kd.length ∧ L_v2.length = L_kd.length ∧
  L_kd.getD 0 0 = 0 ∧
  ∀ p < K,
    L_kd.getD p 0 ≤ 2 ∧
    (L_kd.getD p 0 = 0 → L_v1.getD p 0 = 0 ∧ L_v2.getD p 0 = 0) ∧
    (L_kd.getD p 0 = 1 → L_v1.getD p 0 < N ∧ L_v2.getD p 0 = 0) ∧
    (L_kd.getD p 0 = 2 → L_v1.getD p 0 < p ∧ L_v2.getD p 0 < p)

theorem arenaWF_init (N cap : ℕ) (hcap : 1 ≤ cap) :
    ArenaWF N 1 (List.replicate cap 0) (List.replicate cap 0) (List.replicate cap 0) := by
  have hget0 : ∀ (L : List ℕ), L = List.replicate cap 0 → L.getD 0 0 = 0 := by
    intro L hL; subst hL; cases cap <;> rfl
  refine ⟨le_refl 1, by simp [hcap], by simp, by simp,
    hget0 _ rfl, fun p hp => ?_⟩
  have hp0 : p = 0 := by omega
  subst hp0
  rw [hget0 _ rfl]
  omega

private theorem getD_set_ne (L : List ℕ) (k v p : ℕ) (hne : p ≠ k) :
    (L.set k v).getD p 0 = L.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]

private theorem getD_set_eq (L : List ℕ) (k v : ℕ) (hk : k < L.length) :
    (L.set k v).getD k 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk, Option.getD_some]

/-- Writing at index `k` of `(L_kd, L_v1, L_v2)` preserves `evalArena` at all pointers `p < k`. -/
theorem evalArena_set_gt (N : ℕ) (L_kd L_v1 L_v2 : List ℕ) (k kd v1 v2 : ℕ) :
    ∀ p < k,
      evalArena N (L_kd.set k kd) (L_v1.set k v1) (L_v2.set k v2) p =
        evalArena N L_kd L_v1 L_v2 p := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hpk
    cases p with
    | zero => simp [evalArena_zero]
    | succ p' =>
      have hne : p' + 1 ≠ k := by omega
      rw [evalArena_succ, evalArena_succ]
      dsimp only
      rw [getD_set_ne L_kd k kd (p' + 1) hne,
          getD_set_ne L_v1 k v1 (p' + 1) hne,
          getD_set_ne L_v2 k v2 (p' + 1) hne]
      split_ifs with h1 h2
      · rfl
      · rfl
      · rw [ih (Nat.min (L_v1.getD (p' + 1) 0) p')
              (Nat.lt_succ_of_le (Nat.min_le_right _ p'))
              (Nat.lt_of_le_of_lt (Nat.min_le_right _ p') (by omega)),
            ih (Nat.min (L_v2.getD (p' + 1) 0) p')
              (Nat.lt_succ_of_le (Nat.min_le_right _ p'))
              (Nat.lt_of_le_of_lt (Nat.min_le_right _ p') (by omega))]
      · rfl

theorem evalArena_set_empty {N k : ℕ} (hk_pos : 0 < k) (L_kd L_v1 L_v2 : List ℕ)
    (hk_kd : k < L_kd.length) (v1 v2 : ℕ) :
    evalArena N (L_kd.set k 0) (L_v1.set k v1) (L_v2.set k v2) k = ∅ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [evalArena_succ]
  dsimp only
  rw [getD_set_eq L_kd (k' + 1) 0 hk_kd]
  rfl

theorem evalArena_set_singleton {N k : ℕ} (hk_pos : 0 < k) (L_kd L_v1 L_v2 : List ℕ)
    (hk_kd : k < L_kd.length) (hk_v1 : k < L_v1.length) (u : Fin N) (v2 : ℕ) :
    evalArena N (L_kd.set k 1) (L_v1.set k u.1) (L_v2.set k v2) k = {u} := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [evalArena_succ]
  dsimp only
  rw [getD_set_eq L_kd (k' + 1) 1 hk_kd, getD_set_eq L_v1 (k' + 1) u.1 hk_v1]
  simp [u.2]

theorem evalArena_set_union {N k : ℕ} (hk_pos : 0 < k) (L_kd L_v1 L_v2 : List ℕ)
    (hk_kd : k < L_kd.length) (hk_v1 : k < L_v1.length) (hk_v2 : k < L_v2.length)
    {p1 p2 : ℕ} (hp1 : p1 < k) (hp2 : p2 < k) :
    evalArena N (L_kd.set k 2) (L_v1.set k p1) (L_v2.set k p2) k =
      evalArena N L_kd L_v1 L_v2 p1 ∪ evalArena N L_kd L_v1 L_v2 p2 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [evalArena_succ]
  dsimp only
  rw [getD_set_eq L_kd (k' + 1) 2 hk_kd,
      getD_set_eq L_v1 (k' + 1) p1 hk_v1,
      getD_set_eq L_v2 (k' + 1) p2 hk_v2]
  have hmin1 : Nat.min p1 k' = p1 := Nat.min_eq_left (by omega)
  have hmin2 : Nat.min p2 k' = p2 := Nat.min_eq_left (by omega)
  simp only [show ¬(2 = 1) by decide, ↓reduceIte, hmin1, hmin2]
  rw [evalArena_set_gt N L_kd L_v1 L_v2 (k' + 1) 2 p1 p2 p1 hp1,
      evalArena_set_gt N L_kd L_v1 L_v2 (k' + 1) 2 p1 p2 p2 hp2]

theorem arenaWF_step_empty {N K : ℕ} {L_kd L_v1 L_v2 : List ℕ}
    (hwf : ArenaWF N K L_kd L_v1 L_v2) (hK_lt : K < L_kd.length) :
    ArenaWF N (K + 1) (L_kd.set K 0) (L_v1.set K 0) (L_v2.set K 0) := by
  rcases hwf with ⟨hK1, hlen1, hlen2, hlen3, h0, hnodes⟩
  have hK_v1 : K < L_v1.length := by omega
  have hK_v2 : K < L_v2.length := by omega
  refine ⟨by omega, by simp [hK_lt], by simp [hlen2], by simp [hlen3], ?_, fun p hp => ?_⟩
  · rw [getD_set_ne L_kd K 0 0 (by omega)]; exact h0
  · by_cases hpK : p = K
    · subst hpK
      rw [getD_set_eq L_kd p 0 hK_lt, getD_set_eq L_v1 p 0 hK_v1, getD_set_eq L_v2 p 0 hK_v2]
      simp
    · rw [getD_set_ne L_kd K 0 p hpK,
          getD_set_ne L_v1 K 0 p hpK,
          getD_set_ne L_v2 K 0 p hpK]
      exact hnodes p (by omega)

theorem arenaWF_step_singleton {N K : ℕ} {L_kd L_v1 L_v2 : List ℕ}
    (hwf : ArenaWF N K L_kd L_v1 L_v2) (hK_lt : K < L_kd.length)
    {u : ℕ} (hu : u < N) :
    ArenaWF N (K + 1) (L_kd.set K 1) (L_v1.set K u) (L_v2.set K 0) := by
  rcases hwf with ⟨hK1, hlen1, hlen2, hlen3, h0, hnodes⟩
  have hK_v1 : K < L_v1.length := by omega
  have hK_v2 : K < L_v2.length := by omega
  refine ⟨by omega, by simp [hK_lt], by simp [hlen2], by simp [hlen3], ?_, fun p hp => ?_⟩
  · rw [getD_set_ne L_kd K 1 0 (by omega)]; exact h0
  · by_cases hpK : p = K
    · subst hpK
      rw [getD_set_eq L_kd p 1 hK_lt, getD_set_eq L_v1 p u hK_v1, getD_set_eq L_v2 p 0 hK_v2]
      simp [hu]
    · rw [getD_set_ne L_kd K 1 p hpK,
          getD_set_ne L_v1 K u p hpK,
          getD_set_ne L_v2 K 0 p hpK]
      exact hnodes p (by omega)

theorem arenaWF_step_union {N K : ℕ} {L_kd L_v1 L_v2 : List ℕ}
    (hwf : ArenaWF N K L_kd L_v1 L_v2) (hK_lt : K < L_kd.length)
    {p1 p2 : ℕ} (hp1 : p1 < K) (hp2 : p2 < K) :
    ArenaWF N (K + 1) (L_kd.set K 2) (L_v1.set K p1) (L_v2.set K p2) := by
  rcases hwf with ⟨hK1, hlen1, hlen2, hlen3, h0, hnodes⟩
  have hK_v1 : K < L_v1.length := by omega
  have hK_v2 : K < L_v2.length := by omega
  refine ⟨by omega, by simp [hK_lt], by simp [hlen2], by simp [hlen3], ?_, fun p hp => ?_⟩
  · rw [getD_set_ne L_kd K 2 0 (by omega)]; exact h0
  · by_cases hpK : p = K
    · subst hpK
      rw [getD_set_eq L_kd p 2 hK_lt,
          getD_set_eq L_v1 p p1 hK_v1,
          getD_set_eq L_v2 p p2 hK_v2]
      simp [hp1, hp2]
    · rw [getD_set_ne L_kd K 2 p hpK,
          getD_set_ne L_v1 K p1 p hpK,
          getD_set_ne L_v2 K p2 p hpK]
      exact hnodes p (by omega)

/-! ### Section 2: Word RAM Arena Node Allocation Gadgets and Backward-Sweep Materializer -/

/-- Register and array conventions for Pass 2 and Pass 3 of Algorithm (4.1). -/
abbrev r_kv : Reg := 3
abbrev r_ke : Reg := 4
abbrev r_tidA : Reg := 5
abbrev r_qA : Reg := 6
abbrev r_tidB : Reg := 7
abbrev r_qB : Reg := 8

abbrev a_vkd : Arr := 20
abbrev a_vv1 : Arr := 21
abbrev a_vv2 : Arr := 22
abbrev a_ekd : Arr := 23
abbrev a_ev1 : Arr := 24
abbrev a_ev2 : Arr := 25

abbrev a_acc_zV : Arr := 26
abbrev a_acc_zI : Arr := 27
abbrev a_acc_vv : Arr := 28
abbrev a_acc_ve : Arr := 29
abbrev a_acc_em : Arr := 30

abbrev a_rhs_zV : Arr := 31
abbrev a_rhs_zI : Arr := 32
abbrev a_rhs_vv : Arr := 33
abbrev a_rhs_ve : Arr := 34
abbrev a_rhs_em : Arr := 35

abbrev a_out_zV : Arr := 36
abbrev a_out_zI : Arr := 37
abbrev a_out_vv : Arr := 38
abbrev a_out_ve : Arr := 39
abbrev a_out_em : Arr := 40

abbrev a_sub_tid : Arr := 41
abbrev a_sub_q : Arr := 42
abbrev a_sub_zV : Arr := 43
abbrev a_sub_zI : Arr := 44
abbrev a_sub_vv : Arr := 45
abbrev a_sub_ve : Arr := 46
abbrev a_sub_em : Arr := 47

abbrev a_act : Arr := 48
abbrev a_bits : Arr := 49

/-- Word RAM gadget that writes `(kd, v1, v2)` at index `r_k` in `(a_kd, a_v1, a_v2)` and
increments `r_k := r_k + 1`. -/
def pushArenaNodeProg (a_kd a_v1 a_v2 : Arr) (r_k : Reg) (e_kd e_v1 e_v2 : Expr) : Cmd :=
  .seq (.write a_kd (.reg r_k) e_kd)
  (.seq (.write a_v1 (.reg r_k) e_v1)
  (.seq (.write a_v2 (.reg r_k) e_v2)
        (.assign r_k (.op .add (.reg r_k) (.const 1)))))

theorem pushArenaNodeProg_exec {w : ℕ} {a_kd a_v1 a_v2 : Arr} {r_k : Reg}
    {e_kd e_v1 e_v2 : Expr} {s : State} {K kd v1 v2 : ℕ}
    (h12 : a_kd ≠ a_v1) (h13 : a_kd ≠ a_v2) (h23 : a_v1 ≠ a_v2)
    (hw1 : 1 < 2 ^ w) (hK_w : K + 1 < 2 ^ w)
    (hrk : s.regs r_k = K)
    (hK_len1 : K < (s.arrs a_kd).length)
    (hK_len2 : K < (s.arrs a_v1).length)
    (hK_len3 : K < (s.arrs a_v2).length)
    (he_kd : e_kd.eval w s = some kd)
    (he_v1 : e_v1.eval w (s.writeArr a_kd K kd) = some v1)
    (he_v2 : e_v2.eval w ((s.writeArr a_kd K kd).writeArr a_v1 K v1) = some v2) :
    let s' := (((s.writeArr a_kd K kd).writeArr a_v1 K v1).writeArr a_v2 K v2).setReg r_k (K + 1)
    ∃ t_step ≤ 10 + e_kd.cost + e_v1.cost + e_v2.cost,
      Exec w (pushArenaNodeProg a_kd a_v1 a_v2 r_k e_kd e_v1 e_v2) s s' t_step := by
  have hK_w0 : K < 2 ^ w := by omega
  let s₁ := s.writeArr a_kd K kd
  have hex₁ : Exec w (.write a_kd (.reg r_k) e_kd) s s₁ ((Expr.reg r_k).cost + e_kd.cost + 1) :=
    .write (by simp [Expr.eval, checkWord, hrk, hK_w0]) he_kd hK_len1
  let s₂ := s₁.writeArr a_v1 K v1
  have hex₂ : Exec w (.write a_v1 (.reg r_k) e_v1) s₁ s₂ ((Expr.reg r_k).cost + e_v1.cost + 1) :=
    .write (by simp [s₁, Expr.eval, checkWord, hrk, hK_w0])
      he_v1
      (by simp [s₁, h12.symm, hK_len2])
  let s₃ := s₂.writeArr a_v2 K v2
  have hex₃ : Exec w (.write a_v2 (.reg r_k) e_v2) s₂ s₃ ((Expr.reg r_k).cost + e_v2.cost + 1) :=
    .write (by simp [s₂, s₁, Expr.eval, checkWord, hrk, hK_w0])
      he_v2
      (by simp [s₂, s₁, h13.symm, h23.symm, hK_len3])
  let s₄ := s₃.setReg r_k (K + 1)
  have hex₄ : Exec w (.assign r_k (.op .add (.reg r_k) (.const 1))) s₃ s₄ 4 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hw1, hK_w0, hK_w])
  dsimp [Expr.cost] at hex₁ hex₂ hex₃
  refine ⟨(1 + e_kd.cost + 1) + ((1 + e_v1.cost + 1) + ((1 + e_v2.cost + 1) + 4)),
    by omega, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))⟩

/-- Backward-sweep loop body for `materializeArenaProg`:
decrements `r_p := r_p - 1` (where `r_p = 10`), and if `a_act[r_p] == 1`, processes node `r_p`
(`kd == 1` sets `a_bits[v1] := 1`; `kd == 2` sets `a_act[v1] := 1` and `a_act[v2] := 1`). -/
def materializeSweepBody (a_kd a_v1 a_v2 : Arr) : Cmd :=
  -- `r_10 = p`, `r_11 = act`, `r_12 = kd`, `r_13 = v1`, `r_14 = v2`
  .seq (.assign 10 (.op .sub (.reg 10) (.const 1)))
  (.seq (.assign 11 (.read a_act (.reg 10)))
    (.ite (.op .eq (.reg 11) (.const 1))
      (.seq (.assign 12 (.read a_kd (.reg 10)))
      (.seq (.assign 13 (.read a_v1 (.reg 10)))
      (.seq (.assign 14 (.read a_v2 (.reg 10)))
        (.ite (.op .eq (.reg 12) (.const 1))
          (.write a_bits (.reg 13) (.const 1))
          (.ite (.op .eq (.reg 12) (.const 2))
            (.seq (.write a_act (.reg 13) (.const 1))
                  (.write a_act (.reg 14) (.const 1)))
            .skip)))))
      .skip))

/-- Complete backward-sweep loop for `materializeArenaProg`. -/
def materializeSweepLoop (a_kd a_v1 a_v2 : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg 10)) (materializeSweepBody a_kd a_v1 a_v2)

/-- Complete `materializeArenaProg`: given active arena size in `r_K`, target bitset length in
`r_N`, and root pointer `< K` in `r_root` (with `r_K, r_N, r_root < 10`), materializes
`bitSetList (evalArena N L_kd L_v1 L_v2 p_root)` into `a_bits`. -/
def materializeArenaProg (a_kd a_v1 a_v2 : Arr) (r_N r_K r_root : Reg) : Cmd :=
  .seq (.alloc a_act (.reg r_K))
  (.seq (.write a_act (.reg r_root) (.const 1))
  (.seq (.alloc a_bits (.reg r_N))
  (.seq (.assign 10 (.reg r_K))
        (materializeSweepLoop a_kd a_v1 a_v2))))

private theorem filter_lt_succ_eq_insert {K p : ℕ} (hp : p < K) (A : Finset (Fin K))
    (hmem : (⟨p, hp⟩ : Fin K) ∈ A) :
    A.filter (fun q : Fin K => q.1 < p + 1) =
      insert ⟨p, hp⟩ (A.filter (fun q : Fin K => q.1 < p)) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]
  constructor
  · rintro ⟨hqA, hq_lt⟩
    by_cases hqp : q.1 = p
    · exact Or.inl hqp
    · exact Or.inr ⟨hqA, by omega⟩
  · rintro (rfl | ⟨hqA, hq_lt⟩)
    · exact ⟨hmem, Nat.lt_succ_self q.1⟩
    · exact ⟨hqA, by omega⟩

private theorem filter_lt_succ_eq_self {K p : ℕ} (hp : p < K) (A : Finset (Fin K))
    (hnotMem : (⟨p, hp⟩ : Fin K) ∉ A) :
    A.filter (fun q : Fin K => q.1 < p + 1) = A.filter (fun q : Fin K => q.1 < p) := by
  ext q
  simp only [Finset.mem_filter]
  refine and_congr_right fun hqA => ⟨fun hq_lt => ?_, fun hq_lt => by omega⟩
  have hne : q.1 ≠ p := fun h => hnotMem ((Fin.ext h : q = ⟨p, hp⟩) ▸ hqA)
  omega

private theorem evalArena_pos_eq {N p : ℕ} (hp : 0 < p) (L_kd L_v1 L_v2 : List ℕ) :
    evalArena N L_kd L_v1 L_v2 p =
      let kd := L_kd.getD p 0
      let v1 := L_v1.getD p 0
      let v2 := L_v2.getD p 0
      if kd = 1 then
        if h : v1 < N then {⟨v1, h⟩} else ∅
      else if kd = 2 then
        evalArena N L_kd L_v1 L_v2 (Nat.min v1 (p - 1)) ∪
          evalArena N L_kd L_v1 L_v2 (Nat.min v2 (p - 1))
      else
        ∅ := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  exact evalArena_succ N L_kd L_v1 L_v2 p'

theorem materializeSweepLoop_exec {w N K : ℕ} {a_kd a_v1 a_v2 : Arr}
    {L_kd L_v1 L_v2 : List ℕ}
    (hwf : ArenaWF N K L_kd L_v1 L_v2)
    (hw2 : 2 < 2 ^ w) (hN_w : N < 2 ^ w) (hK_w : K < 2 ^ w)
    (h_kd_act : a_kd ≠ a_act) (h_kd_bits : a_kd ≠ a_bits)
    (h_v1_act : a_v1 ≠ a_act) (h_v1_bits : a_v1 ≠ a_bits)
    (h_v2_act : a_v2 ≠ a_act) (h_v2_bits : a_v2 ≠ a_bits)
    (S_target : Finset (Fin N)) :
    ∀ (p : ℕ), p ≤ K →
      ∀ (s : State) (A_set : Finset (Fin K)) (B_set : Finset (Fin N)),
        s.regs 10 = p →
        s.arrs a_kd = L_kd →
        s.arrs a_v1 = L_v1 →
        s.arrs a_v2 = L_v2 →
        s.arrs a_act = bitSetList A_set →
        s.arrs a_bits = bitSetList B_set →
        B_set ∪ (A_set.filter (fun q : Fin K => q.1 < p)).biUnion
          (fun q => evalArena N L_kd L_v1 L_v2 q.1) = S_target →
        ∃ s' t_step,
          Exec w (materializeSweepLoop a_kd a_v1 a_v2) s s' t_step ∧
          t_step ≤ 40 * p + 4 ∧
          s'.arrs a_bits = bitSetList S_target ∧
          (∀ a, a ≠ a_act → a ≠ a_bits → s'.arrs a = s.arrs a) ∧
          (∀ (r : ℕ), r < 10 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  rcases hwf with ⟨hK1, hlen_kd, hlen_v1, hlen_v2, hkd0, hnodes⟩
  intro p
  induction p with
  | zero =>
    intro _ s A_set B_set hr10 _ _ _ _ hbits hinv
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 0 := by
      simp [Expr.eval, hr10, BinOp.eval, BinOp.raw, checkWord, h0_w]
    have hemp : A_set.filter (fun q : Fin K => q.1 < 0) = ∅ := by
      ext q; simp
    rw [hemp, Finset.biUnion_empty, Finset.union_empty] at hinv
    subst hinv
    exact ⟨s, 3, .while_false hcond, by omega, hbits, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ p ih =>
    intro hp_le s A_set B_set hr10 hkd hv1 hv2 hact hbits hinv
    have hp_lt_K : p < K := by omega
    have hp_w : p < 2 ^ w := by omega
    have hp1_w : p + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 10)).eval w s = some 1 := by
      simp [Expr.eval, hr10, BinOp.eval, BinOp.raw, checkWord, h0_w, hw1, hp1_w]
    let s₁ := s.setReg 10 p
    have hex₁ : Exec w (.assign 10 (.op .sub (.reg 10) (.const 1))) s s₁ 4 :=
      .assign (by simp [Expr.eval, hr10, BinOp.eval, BinOp.raw, checkWord, hw1, hp_w, hp1_w])
    let p_fin : Fin K := ⟨p, hp_lt_K⟩
    let act_val : ℕ := if p_fin ∈ A_set then 1 else 0
    have hact_val_w : act_val < 2 ^ w := by dsimp [act_val]; split_ifs <;> omega
    let s₂ := s₁.setReg 11 act_val
    have hex₂ : Exec w (.assign 11 (.read a_act (.reg 10))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hp_w, hact, hp_lt_K, bitSetList, act_val, p_fin, hact_val_w])
    by_cases hp_in : p_fin ∈ A_set
    · have hact_eq1 : act_val = 1 := by simp [act_val, hp_in]
      have hite_act : (Expr.op .eq (.reg 11) (.const 1)).eval w s₂ = some 1 := by
        simp [s₂, hact_eq1, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1]
      have hsplit := filter_lt_succ_eq_insert hp_lt_K A_set hp_in
      rw [hsplit, Finset.biUnion_insert] at hinv
      let kd := L_kd.getD p 0
      let v1 := L_v1.getD p 0
      let v2 := L_v2.getD p 0
      have hp_kd_len : p < L_kd.length := by omega
      have hp_v1_len : p < L_v1.length := by omega
      have hp_v2_len : p < L_v2.length := by omega
      have hget_kd : L_kd[p]'hp_kd_len = kd := by
        simp [kd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp_kd_len]
      have hget_v1 : L_v1[p]'hp_v1_len = v1 := by
        simp [v1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp_v1_len]
      have hget_v2 : L_v2[p]'hp_v2_len = v2 := by
        simp [v2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp_v2_len]
      rcases hnodes p hp_lt_K with ⟨hkd_le2, hkd_eq0, hkd_eq1, hkd_eq2⟩
      have hkd_w : kd < 2 ^ w := by dsimp [kd]; omega
      have hv1_w : v1 < 2 ^ w := by
        dsimp [kd, v1] at hkd_le2 hkd_eq0 hkd_eq1 hkd_eq2 ⊢
        rcases (by omega : kd = 0 ∨ kd = 1 ∨ kd = 2) with h0 | h1 | h2
        · have := (hkd_eq0 h0).1; omega
        · have := (hkd_eq1 h1).1; omega
        · have := (hkd_eq2 h2).1; omega
      have hv2_w : v2 < 2 ^ w := by
        dsimp [kd, v2] at hkd_le2 hkd_eq0 hkd_eq1 hkd_eq2 ⊢
        rcases (by omega : kd = 0 ∨ kd = 1 ∨ kd = 2) with h0 | h1 | h2
        · have := (hkd_eq0 h0).2; omega
        · have := (hkd_eq1 h1).2; omega
        · have := (hkd_eq2 h2).2; omega
      let s₃ := s₂.setReg 12 kd
      have hex₃ : Exec w (.assign 12 (.read a_kd (.reg 10))) s₂ s₃ 3 :=
        .assign (by simp [s₂, s₁, Expr.eval, checkWord, hp_w, hkd, hp_kd_len, hget_kd, hkd_w])
      let s₄ := s₃.setReg 13 v1
      have hex₄ : Exec w (.assign 13 (.read a_v1 (.reg 10))) s₃ s₄ 3 :=
        .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hp_w, hv1, hp_v1_len, hget_v1, hv1_w])
      let s₅ := s₄.setReg 14 v2
      have hex₅ : Exec w (.assign 14 (.read a_v2 (.reg 10))) s₄ s₅ 3 :=
        .assign (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hp_w, hv2, hp_v2_len, hget_v2, hv2_w])
      by_cases hkd1 : kd = 1
      · have hp_pos : 0 < p := by
          by_contra hp0
          have hp0' : p = 0 := by omega
          subst hp0'
          dsimp [kd] at hkd1
          omega
        have hv1_lt_N : v1 < N := (hkd_eq1 hkd1).1
        have hite_kd1 : (Expr.op .eq (.reg 12) (.const 1)).eval w s₅ = some 1 := by
          simp [s₅, s₄, s₃, hkd1, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1]
        let s₆ := s₅.writeArr a_bits v1 1
        have hex₆ : Exec w (.write a_bits (.reg 13) (.const 1)) s₅ s₆ 3 :=
          .write (by simp [s₅, s₄, Expr.eval, checkWord, hv1_w])
                 (by simp [Expr.eval, checkWord, hw1])
                 (by simp [s₅, s₄, s₃, s₂, s₁, hbits, hv1_lt_N])
        have hbits₆ : s₆.arrs a_bits = bitSetList (insert ⟨v1, hv1_lt_N⟩ B_set) := by
          simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hbits]
          exact bitSetList_set_one B_set ⟨v1, hv1_lt_N⟩
        have heval_p : evalArena N L_kd L_v1 L_v2 p = {⟨v1, hv1_lt_N⟩} := by
          rw [evalArena_pos_eq hp_pos]
          have hkd1' : L_kd.getD p 0 = 1 := hkd1
          have hv1' : L_v1.getD p 0 < N := hv1_lt_N
          simp only [hkd1', hv1', ↓reduceIte, ↓reduceDIte]; rfl
        have hinv₆ :
            insert ⟨v1, hv1_lt_N⟩ B_set ∪
              (A_set.filter (fun q : Fin K => q.1 < p)).biUnion
                (fun q => evalArena N L_kd L_v1 L_v2 q.1) = S_target := by
          rw [← hinv, heval_p, Finset.insert_eq, Finset.union_comm {⟨v1, hv1_lt_N⟩} B_set,
              Finset.union_assoc]
        rcases ih (by omega) s₆ A_set (insert ⟨v1, hv1_lt_N⟩ B_set)
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁])
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, h_kd_bits, hkd])
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, h_v1_bits, hv1])
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, h_v2_bits, hv2])
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, show a_act ≠ a_bits by decide, hact])
            hbits₆ hinv₆ with
          ⟨s', t_ih, hex_ih, ht_ih, hbits', harr', hreg'⟩
        have hex_body : Exec w (materializeSweepBody a_kd a_v1 a_v2) s s₆ 25 :=
          .seq hex₁ (.seq hex₂ (.ite_true hite_act (by decide)
            (.seq hex₃ (.seq hex₄ (.seq hex₅ (.ite_true hite_kd1 (by decide) hex₆))))))
        refine ⟨s', 3 + 25 + t_ih, .while_true hcond (by decide) hex_body hex_ih,
          by omega, hbits', fun a ha1 ha2 => ?_, fun r hr => ?_⟩
        · rw [harr' a ha1 ha2]; simp [s₆, s₅, s₄, s₃, s₂, s₁, ha2]
        · rw [hreg' r hr]; simp [s₆, s₅, s₄, s₃, s₂, s₁, show r ≠ 10 by omega,
            show r ≠ 11 by omega, show r ≠ 12 by omega, show r ≠ 13 by omega, show r ≠ 14 by omega]
      · have hite_kd1 : (Expr.op .eq (.reg 12) (.const 1)).eval w s₅ = some 0 := by
          simp [s₅, s₄, s₃, hkd1, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hw1, hkd_w]
        by_cases hkd2 : kd = 2
        · have hp_pos : 0 < p := by
            by_contra hp0
            have hp0' : p = 0 := by omega
            subst hp0'
            dsimp [kd] at hkd2
            omega
          rcases hkd_eq2 hkd2 with ⟨hv1_lt_p, hv2_lt_p⟩
          have hv1_lt_K : v1 < K := by omega
          have hv2_lt_K : v2 < K := by omega
          have hite_kd2 : (Expr.op .eq (.reg 12) (.const 2)).eval w s₅ = some 1 := by
            simp [s₅, s₄, s₃, hkd2, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1, hw2]
          let s₆ := s₅.writeArr a_act v1 1
          have hex₆ : Exec w (.write a_act (.reg 13) (.const 1)) s₅ s₆ 3 :=
            .write (by simp [s₅, s₄, Expr.eval, checkWord, hv1_w])
                   (by simp [Expr.eval, checkWord, hw1])
                   (by simp [s₅, s₄, s₃, s₂, s₁, hact, hv1_lt_K])
          have hact₆ : s₆.arrs a_act = bitSetList (insert ⟨v1, hv1_lt_K⟩ A_set) := by
            simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hact]
            exact bitSetList_set_one A_set ⟨v1, hv1_lt_K⟩
          let s₇ := s₆.writeArr a_act v2 1
          have hex₇ : Exec w (.write a_act (.reg 14) (.const 1)) s₆ s₇ 3 :=
            .write (by simp [s₆, s₅, Expr.eval, checkWord, hv2_w])
                   (by simp [Expr.eval, checkWord, hw1])
                   (by simp [hact₆, hv2_lt_K])
          let A_set' := insert ⟨v2, hv2_lt_K⟩ (insert ⟨v1, hv1_lt_K⟩ A_set)
          have hact₇ : s₇.arrs a_act = bitSetList A_set' := by
            simp only [s₇, State.writeArr_arrs_self, hact₆, A_set']
            exact bitSetList_set_one (insert ⟨v1, hv1_lt_K⟩ A_set) ⟨v2, hv2_lt_K⟩
          have heval_p :
              evalArena N L_kd L_v1 L_v2 p =
                evalArena N L_kd L_v1 L_v2 v1 ∪ evalArena N L_kd L_v1 L_v2 v2 := by
            rw [evalArena_pos_eq hp_pos]
            have hmin1 : Nat.min (L_v1.getD p 0) (p - 1) = v1 := Nat.min_eq_left (by omega)
            have hmin2 : Nat.min (L_v2.getD p 0) (p - 1) = v2 := Nat.min_eq_left (by omega)
            have hkd2' : L_kd.getD p 0 = 2 := hkd2
            simp only [hkd2', hmin1, hmin2, ↓reduceIte]; rfl
          have hfilt_eq :
              A_set'.filter (fun q : Fin K => q.1 < p) =
                insert ⟨v2, hv2_lt_K⟩ (insert ⟨v1, hv1_lt_K⟩
                  (A_set.filter (fun q : Fin K => q.1 < p))) := by
            ext q
            simp only [A_set', Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | rfl | hqA, hqp⟩
              · exact Or.inl rfl
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr ⟨hqA, hqp⟩)
            · rintro (rfl | rfl | ⟨hqA, hqp⟩)
              · exact ⟨Or.inl rfl, hv2_lt_p⟩
              · exact ⟨Or.inr (Or.inl rfl), hv1_lt_p⟩
              · exact ⟨Or.inr (Or.inr hqA), hqp⟩
          have hinv₇ :
              B_set ∪ (A_set'.filter (fun q : Fin K => q.1 < p)).biUnion
                (fun q => evalArena N L_kd L_v1 L_v2 q.1) = S_target := by
            rw [hfilt_eq, Finset.biUnion_insert, Finset.biUnion_insert]
            rw [heval_p] at hinv
            rw [← Finset.union_assoc (evalArena N L_kd L_v1 L_v2 v2),
                Finset.union_comm (evalArena N L_kd L_v1 L_v2 v2), hinv]
          rcases ih (by omega) s₇ A_set' B_set
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁])
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, h_kd_act, hkd])
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, h_v1_act, hv1])
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, h_v2_act, hv2])
              hact₇
              (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, show a_bits ≠ a_act by decide, hbits])
              hinv₇ with
            ⟨s', t_ih, hex_ih, ht_ih, hbits', harr', hreg'⟩
          have hex_body : Exec w (materializeSweepBody a_kd a_v1 a_v2) s s₇ 31 :=
            .seq hex₁ (.seq hex₂ (.ite_true hite_act (by decide)
              (.seq hex₃ (.seq hex₄ (.seq hex₅ (.ite_false hite_kd1
                (.ite_true hite_kd2 (by decide) (.seq hex₆ hex₇))))))))
          refine ⟨s', 3 + 31 + t_ih, .while_true hcond (by decide) hex_body hex_ih,
            by omega, hbits', fun a ha1 ha2 => ?_, fun r hr => ?_⟩
          · rw [harr' a ha1 ha2]; simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha1]
          · rw [hreg' r hr]; simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, show r ≠ 10 by omega,
              show r ≠ 11 by omega, show r ≠ 12 by omega, show r ≠ 13 by omega, show r ≠ 14 by omega]
        · have hite_kd2 : (Expr.op .eq (.reg 12) (.const 2)).eval w s₅ = some 0 := by
            simp [s₅, s₄, s₃, hkd2, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hw2, hkd_w]
          have heval_p : evalArena N L_kd L_v1 L_v2 p = ∅ := by
            cases p with
            | zero => exact evalArena_zero N L_kd L_v1 L_v2
            | succ p' =>
              rw [evalArena_pos_eq (Nat.succ_pos p')]
              have hkd1' : ¬(L_kd.getD (p' + 1) 0 = 1) := hkd1
              have hkd2' : ¬(L_kd.getD (p' + 1) 0 = 2) := hkd2
              simp only [hkd1', hkd2', ↓reduceIte]
          rw [heval_p, Finset.empty_union] at hinv
          rcases ih (by omega) s₅ A_set B_set
              (by simp [s₅, s₄, s₃, s₂, s₁])
              hkd hv1 hv2 hact hbits hinv with
            ⟨s', t_ih, hex_ih, ht_ih, hbits', harr', hreg'⟩
          have hex_body : Exec w (materializeSweepBody a_kd a_v1 a_v2) s s₅ 26 :=
            .seq hex₁ (.seq hex₂ (.ite_true hite_act (by decide)
              (.seq hex₃ (.seq hex₄ (.seq hex₅ (.ite_false hite_kd1
                (.ite_false hite_kd2 (.skip s₅))))))))
          refine ⟨s', 3 + 26 + t_ih, .while_true hcond (by decide) hex_body hex_ih,
            by omega, hbits', fun a ha1 ha2 => harr' a ha1 ha2, fun r hr => ?_⟩
          rw [hreg' r hr]; simp [s₅, s₄, s₃, s₂, s₁, show r ≠ 10 by omega,
            show r ≠ 11 by omega, show r ≠ 12 by omega, show r ≠ 13 by omega, show r ≠ 14 by omega]
    · have hact_eq0 : act_val = 0 := by simp [act_val, hp_in]
      have hite_act : (Expr.op .eq (.reg 11) (.const 1)).eval w s₂ = some 0 := by
        simp [s₂, hact_eq0, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hw1]
      rw [filter_lt_succ_eq_self hp_lt_K A_set hp_in] at hinv
      rcases ih (by omega) s₂ A_set B_set
          (by simp [s₂, s₁])
          hkd hv1 hv2 hact hbits hinv with
        ⟨s', t_ih, hex_ih, ht_ih, hbits', harr', hreg'⟩
      have hex_body : Exec w (materializeSweepBody a_kd a_v1 a_v2) s s₂ 11 :=
        .seq hex₁ (.seq hex₂ (.ite_false hite_act (.skip s₂)))
      refine ⟨s', 3 + 11 + t_ih, .while_true hcond (by decide) hex_body hex_ih,
        by omega, hbits', fun a ha1 ha2 => harr' a ha1 ha2, fun r hr => ?_⟩
      rw [hreg' r hr]; simp [s₂, s₁, show r ≠ 10 by omega, show r ≠ 11 by omega]

theorem materializeArenaProg_exec {w N K p_root : ℕ} {a_kd a_v1 a_v2 : Arr}
    {r_N r_K r_root : Reg} {L_kd L_v1 L_v2 : List ℕ} {s : State}
    (hwf : ArenaWF N K L_kd L_v1 L_v2)
    (hw2 : 2 < 2 ^ w) (hN_w : N < 2 ^ w) (hK_w : K < 2 ^ w)
    (h_kd_act : a_kd ≠ a_act) (h_kd_bits : a_kd ≠ a_bits)
    (h_v1_act : a_v1 ≠ a_act) (h_v1_bits : a_v1 ≠ a_bits)
    (h_v2_act : a_v2 ≠ a_act) (h_v2_bits : a_v2 ≠ a_bits)
    (_hrN_lt : r_N < 10) (_hrK_lt : r_K < 10) (_hrroot_lt : r_root < 10)
    (hroot_lt : p_root < K)
    (hrN : s.regs r_N = N) (hrK : s.regs r_K = K) (hrroot : s.regs r_root = p_root)
    (hkd : s.arrs a_kd = L_kd) (hv1 : s.arrs a_v1 = L_v1) (hv2 : s.arrs a_v2 = L_v2) :
    ∃ s' t_step,
      Exec w (materializeArenaProg a_kd a_v1 a_v2 r_N r_K r_root) s s' t_step ∧
      t_step ≤ 42 * K + N + 15 ∧
      s'.arrs a_bits = bitSetList (evalArena N L_kd L_v1 L_v2 p_root) ∧
      (∀ a, a ≠ a_act → a ≠ a_bits → s'.arrs a = s.arrs a) ∧
      (∀ r < 10, s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hroot_w : p_root < 2 ^ w := by omega
  let s₁ := s.setArr a_act (List.replicate K 0)
  have hex₁ : Exec w (.alloc a_act (.reg r_K)) s s₁ (1 + K) :=
    .alloc (by simp [Expr.eval, checkWord, hrK, hK_w])
  let s₂ := s₁.writeArr a_act p_root 1
  have hex₂ : Exec w (.write a_act (.reg r_root) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hrroot, hroot_w])
           (by simp [Expr.eval, checkWord, hw1])
           (by simp [s₁, hroot_lt])
  have hact₂ : s₂.arrs a_act = bitSetList ({⟨p_root, hroot_lt⟩} : Finset (Fin K)) := by
    simp only [s₂, s₁, State.writeArr_arrs_self, State.setArr_arrs_self, ← bitSetList_empty41 K]
    exact bitSetList_set_one (∅ : Finset (Fin K)) ⟨p_root, hroot_lt⟩
  let s₃ := s₂.setArr a_bits (List.replicate N 0)
  have hex₃ : Exec w (.alloc a_bits (.reg r_N)) s₂ s₃ (1 + N) :=
    .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hrN, hN_w])
  have hbits₃ : s₃.arrs a_bits = bitSetList (∅ : Finset (Fin N)) := by
    simp [s₃]
  let s₄ := s₃.setReg 10 K
  have hex₄ : Exec w (.assign 10 (.reg r_K)) s₃ s₄ 2 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hrK, hK_w])
  have hinv₄ :
      (∅ : Finset (Fin N)) ∪
        (({⟨p_root, hroot_lt⟩} : Finset (Fin K)).filter (fun q : Fin K => q.1 < K)).biUnion
          (fun q => evalArena N L_kd L_v1 L_v2 q.1) =
        evalArena N L_kd L_v1 L_v2 p_root := by
    have hfilt :
        ({⟨p_root, hroot_lt⟩} : Finset (Fin K)).filter (fun q : Fin K => q.1 < K) =
          {⟨p_root, hroot_lt⟩} := by
      ext q; simp
    rw [Finset.empty_union, hfilt]
    simp
  rcases materializeSweepLoop_exec hwf hw2 hN_w hK_w
      h_kd_act h_kd_bits h_v1_act h_v1_bits h_v2_act h_v2_bits
      (evalArena N L_kd L_v1 L_v2 p_root) K (le_refl K)
      s₄ {⟨p_root, hroot_lt⟩} ∅
      (by simp [s₄])
      (by simp [s₄, s₃, s₂, s₁, h_kd_act, h_kd_bits, hkd])
      (by simp [s₄, s₃, s₂, s₁, h_v1_act, h_v1_bits, hv1])
      (by simp [s₄, s₃, s₂, s₁, h_v2_act, h_v2_bits, hv2])
      (by simp [s₄, s₃, show a_act ≠ a_bits by decide, hact₂])
      (by simp [s₄, hbits₃])
      hinv₄ with
    ⟨s', t_loop, hex_loop, ht_loop, hbits', harr', hreg'⟩
  refine ⟨s', (1 + K) + (3 + ((1 + N) + (2 + t_loop))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_loop))),
    by omega, hbits', fun a ha1 ha2 => ?_, fun r hr => ?_⟩
  · rw [harr' a ha1 ha2]; simp [s₄, s₃, s₂, s₁, ha1, ha2]
  · rw [hreg' r hr]
    simp [s₄, s₃, s₂, s₁, Nat.ne_of_lt hr]

/-! ### Section 3: Canonical Local Base Configurations (`bcfg < 72`) and `ValidPieceBuffer` -/

/-- Strict upper bound `Q_max ξ ω + δ + 1` on `H.digraph.numVerts` and `H.digraph.numEdges` for
any `q`-rooted digraph `H` of detail `≤ δ` with `q ≤ Q_max ξ ω`. -/
def V_max (δ ξ ω : ℕ) : ℕ := Q_max ξ ω + δ + 1

/-- Flat table buffer size `C_max δ ξ ω * V_max δ ξ ω` for `vvPtr`, `vePtr`, and `emVal`. -/
def S_tab (δ ξ ω : ℕ) : ℕ := C_max δ ξ ω * V_max δ ξ ω

theorem V_max_pos (δ ξ ω : ℕ) : 0 < V_max δ ξ ω := by
  unfold V_max; omega

theorem numVerts_lt_V_max {q δ ξ ω : ℕ} (hq : q ≤ Q_max ξ ω)
    {H : ComputeRootedDigraph q} (hdet : H.HasDetailLe δ) :
    H.digraph.numVerts < V_max δ ξ ω := by
  have hle := H.numVerts_le_of_hasDetailLe hdet
  unfold V_max
  omega

theorem numEdges_lt_V_max {q δ ξ ω : ℕ}
    {H : ComputeRootedDigraph q} (hdet : H.HasDetailLe δ) :
    H.digraph.numEdges < V_max δ ξ ω := by
  have hle := hdet.1
  unfold V_max
  omega

/-- Register and array IDs of a working piece buffer (`bufA` or `bufB`). -/
structure PieceBufLayout where
  r_tid : Reg
  r_q : Reg
  a_zV : Arr
  a_zI : Arr
  a_vv : Arr
  a_ve : Arr
  a_em : Arr

/-- Buffer A (`acc`): holds the active accumulator table during Pass 2. -/
def bufA : PieceBufLayout where
  r_tid := r_tidA
  r_q := r_qA
  a_zV := a_acc_zV
  a_zI := a_acc_zI
  a_vv := a_acc_vv
  a_ve := a_acc_ve
  a_em := a_acc_em

/-- Buffer B (`rhs`): holds the right-hand table being combined with Buffer A. -/
def bufB : PieceBufLayout where
  r_tid := r_tidB
  r_q := r_qB
  a_zV := a_rhs_zV
  a_zI := a_rhs_zI
  a_vv := a_rhs_vv
  a_ve := a_rhs_ve
  a_em := a_rhs_em

/-- Validity invariant stating that working buffer `buf` in state `s` (together with the arenas
`ArenaV` and `ArenaE`) represents the boundary `(Z_P, E_P)` and the certified raw entry list
`es : List (RawCertEntry G Z_P.card)`. -/
structure ValidPieceBuffer (δ ξ ω : ℕ) (G : ComputeDigraph)
    (Z_P : Finset (Fin G.numVerts)) (E_P : Finset (Fin G.numEdges))
    (es : List (RawCertEntry G Z_P.card)) (buf : PieceBufLayout) (s : State) : Prop where
  hq_le : Z_P.card ≤ Q_max ξ ω
  hlen_le : es.length ≤ (allDetailLeCodes Z_P.card δ).length
  hdet : ∀ e ∈ es, e.H.HasDetailLe δ
  htid : s.regs buf.r_tid = encAbstractTable δ ξ ω ⟨Z_P.card, es.map (·.H)⟩
  hq : s.regs buf.r_q = Z_P.card
  hzV_len : (s.arrs buf.a_zV).length = Q_max ξ ω
  hzI_len : (s.arrs buf.a_zI).length = Q_max ξ ω
  hzV : ∀ i : Fin Z_P.card, (s.arrs buf.a_zV).getD i.1 0 = (finsetRootFn Z_P i).1
  hzI : ∀ i : Fin Z_P.card, (s.arrs buf.a_zI).getD i.1 0 = subInc G E_P (finsetRootFn Z_P i)
  hvv_len : (s.arrs buf.a_vv).length = S_tab δ ξ ω
  hve_len : (s.arrs buf.a_ve).length = S_tab δ ξ ω
  hem_len : (s.arrs buf.a_em).length = S_tab δ ξ ω
  hentries : ∀ idx : Fin es.length,
    let e := es[idx.1]
    let base := idx.1 * V_max δ ξ ω
    (∀ u : Fin e.H.digraph.numVerts,
      let p_vv := (s.arrs buf.a_vv).getD (base + u.1) 0
      let p_ve := (s.arrs buf.a_ve).getD (base + u.1) 0
      p_vv < s.regs r_kv ∧
      evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p_vv = e.vertVerts u ∧
      p_ve < s.regs r_ke ∧
      evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p_ve = e.vertEdges u) ∧
    (∀ d : Fin e.H.digraph.numEdges,
      (s.arrs buf.a_em).getD (base + d.1) 0 = (e.edgeMap d).1)

/-- Canonical local digraph on `n_loc = bcfg % 3 ≤ 2` vertices and
`m_loc = (if n_loc = 0 then 0 else (bcfg / 3) % 2) ≤ 1` edges, with edge orientation coded by
`dir = (bcfg / 6) % 3`:
- `dir = 0`: self-loop `0 → 0`,
- `dir = 1`: edge `1 → 0` (`head = 0, tail = 1`),
- `dir = 2`: edge `0 → 1` (`head = 1, tail = 0`). -/
def canonLocDigraph (bcfg : ℕ) : ComputeDigraph where
  numVerts := bcfg % 3
  numEdges := if bcfg % 3 = 0 then 0 else (bcfg / 3) % 2
  head e :=
    if h : (bcfg / 6) % 3 = 2 ∧ 1 < bcfg % 3 then
      ⟨1, h.2⟩
    else
      ⟨0, by
        have hm := e.2
        split_ifs at hm with h0
        · omega
        · omega⟩
  tail e :=
    if h : (bcfg / 6) % 3 = 1 ∧ 1 < bcfg % 3 then
      ⟨1, h.2⟩
    else
      ⟨0, by
        have hm := e.2
        split_ifs at hm with h0
        · omega
        · omega⟩

/-- Canonical local root subset of `Fin (canonLocDigraph bcfg).numVerts` coded by
`b₀ = (bcfg / 18) % 2` and `b₁ = (bcfg / 36) % 2`. -/
def canonLocRoots (bcfg : ℕ) : Finset (Fin (canonLocDigraph bcfg).numVerts) :=
  Finset.univ.filter (fun i : Fin (canonLocDigraph bcfg).numVerts =>
    (i.1 = 0 ∧ (bcfg / 18) % 2 = 1) ∨ (i.1 = 1 ∧ (bcfg / 36) % 2 = 1))

/-- Purely combinatorial base raw entry list for configuration `bcfg < 72` and detail `δ`. -/
def canonBaseRawList (δ bcfg : ℕ) :
    List (RawCertEntry (canonLocDigraph bcfg) (canonLocRoots bcfg).card) :=
  (baseCertFolioTable (canonLocDigraph bcfg) Finset.univ Finset.univ
    (finsetRootFn (canonLocRoots bcfg)) δ).toRawList

theorem card_canonLocRoots_le_two (ξ ω bcfg : ℕ) :
    (canonLocRoots bcfg).card ≤ 2 ∧ (canonLocRoots bcfg).card ≤ Q_max ξ ω := by
  have hle : (canonLocRoots bcfg).card ≤ bcfg % 3 := by
    calc (canonLocRoots bcfg).card
        ≤ (Finset.univ : Finset (Fin (canonLocDigraph bcfg).numVerts)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = bcfg % 3 := Finset.card_fin _
  have hmod : bcfg % 3 ≤ 2 := by omega
  unfold Q_max
  omega

theorem length_canonBaseRawList_le (δ bcfg : ℕ) :
    (canonBaseRawList δ bcfg).length ≤ (allDetailLeCodes (canonLocRoots bcfg).card δ).length := by
  unfold canonBaseRawList CertFolioTable.toRawList
  rw [List.length_map]
  exact CertFolioTable.length_entries_le _

theorem hasDetailLe_of_mem_canonBaseRawList {δ bcfg : ℕ}
    {e : RawCertEntry (canonLocDigraph bcfg) (canonLocRoots bcfg).card}
    (he : e ∈ canonBaseRawList δ bcfg) :
    e.H.HasDetailLe δ := by
  unfold canonBaseRawList CertFolioTable.toRawList at he
  rcases List.mem_map.mp he with ⟨e₀, _, rfl⟩
  exact e₀.hdet

theorem ComputeDigraph.ext_of_val {G₁ G₂ : ComputeDigraph}
    (hn : G₁.numVerts = G₂.numVerts) (hm : G₁.numEdges = G₂.numEdges)
    (hhead : ∀ e : Fin G₁.numEdges, (G₁.head e).1 = (G₂.head ⟨e.1, hm ▸ e.2⟩).1)
    (htail : ∀ e : Fin G₁.numEdges, (G₁.tail e).1 = (G₂.tail ⟨e.1, hm ▸ e.2⟩).1) :
    G₁ = G₂ := by
  rcases G₁ with ⟨n₁, m₁, hd₁, tl₁⟩
  rcases G₂ with ⟨n₂, m₂, hd₂, tl₂⟩
  dsimp at hn hm hhead htail
  subst hn hm
  congr
  · funext e; exact Fin.ext (hhead e)
  · funext e; exact Fin.ext (htail e)

theorem baseRawList_congr {δ : ℕ} {G₁ G₂ G : ComputeDigraph}
    {Z₁ : Finset (Fin G₁.numVerts)} {Z₂ : Finset (Fin G₂.numVerts)}
    {fV₁ : Fin G₁.numVerts → Fin G.numVerts} {fV₂ : Fin G₂.numVerts → Fin G.numVerts}
    {fE₁ : Fin G₁.numEdges → Fin G.numEdges} {fE₂ : Fin G₂.numEdges → Fin G.numEdges}
    (hG : G₁ = G₂)
    (hZ : ∀ i : Fin G₁.numVerts, i ∈ Z₁ ↔ (⟨i.1, hG ▸ i.2⟩ : Fin G₂.numVerts) ∈ Z₂)
    (hfV : ∀ i : Fin G₁.numVerts, fV₁ i = fV₂ ⟨i.1, hG ▸ i.2⟩)
    (hfE : ∀ e : Fin G₁.numEdges, fE₁ e = fE₂ ⟨e.1, hG ▸ e.2⟩) :
    (⟨Z₁.card,
      (baseCertFolioTable G₁ Finset.univ Finset.univ (finsetRootFn Z₁) δ).toRawList.map
        (RawCertEntry.mapEmb fV₁ fE₁)⟩ : Σ q, List (RawCertEntry G q)) =
    ⟨Z₂.card,
      (baseCertFolioTable G₂ Finset.univ Finset.univ (finsetRootFn Z₂) δ).toRawList.map
        (RawCertEntry.mapEmb fV₂ fE₂)⟩ := by
  cases hG
  have hZ_eq : Z₁ = Z₂ := Finset.ext hZ
  subst hZ_eq
  have hfV_eq : fV₁ = fV₂ := funext hfV
  have hfE_eq : fE₁ = fE₂ := funext hfE
  subst hfV_eq hfE_eq
  rfl

/-- Given a local base configuration `bcfg` and a flat position `pos < S_tab δ ξ ω`,
`baseVVCode δ ξ ω bcfg pos ∈ {0, 1, 2, 3}` is the 2-bit membership mask of `{0, 1}` in
`e_loc.vertVerts u` (where `idx = pos / V_max`, `u = pos % V_max`). -/
def baseVVCode (δ ξ ω bcfg pos : ℕ) : ℕ :=
  let idx := pos / V_max δ ξ ω
  let u := pos % V_max δ ξ ω
  let es := canonBaseRawList δ bcfg
  if h_idx : idx < es.length then
    let e_loc := es[idx]
    if hu : u < e_loc.H.digraph.numVerts then
      let S := e_loc.vertVerts ⟨u, hu⟩
      (if decide (∃ i ∈ S, i.1 = 0) then 1 else 0) +
      (if decide (∃ i ∈ S, i.1 = 1) then 2 else 0)
    else 0
  else 0

/-- Given a local base configuration `bcfg` and a flat position `pos < S_tab δ ξ ω`,
`baseVECode δ ξ ω bcfg pos ∈ {0, 1}` is the 1-bit membership mask of `{0}` in
`e_loc.vertEdges u` (where `idx = pos / V_max`, `u = pos % V_max`). -/
def baseVECode (δ ξ ω bcfg pos : ℕ) : ℕ :=
  let idx := pos / V_max δ ξ ω
  let u := pos % V_max δ ξ ω
  let es := canonBaseRawList δ bcfg
  if h_idx : idx < es.length then
    let e_loc := es[idx]
    if hu : u < e_loc.H.digraph.numVerts then
      let E := e_loc.vertEdges ⟨u, hu⟩
      if decide (∃ d ∈ E, d.1 = 0) then 1 else 0
    else 0
  else 0

/-- Arena pointer value corresponding to `code ∈ {0, 1, 2, 3}` with base pointer `kv₀`. -/
def baseVVVal (kv₀ code : ℕ) : ℕ :=
  if code = 0 then 0
  else if code = 1 then kv₀
  else if code = 2 then kv₀ + 1
  else kv₀ + 2

/-- Arena pointer value corresponding to `code ∈ {0, 1}` with base pointer `ke₀`. -/
def baseVEVal (ke₀ code : ℕ) : ℕ :=
  if code = 0 then 0 else ke₀

/-- Word RAM expression evaluating to `baseVVVal (s.regs 14) code`. -/
def baseVVExpr (code : ℕ) : Expr :=
  if code = 0 then .const 0
  else if code = 1 then .reg 14
  else if code = 2 then .op .add (.reg 14) (.const 1)
  else .op .add (.reg 14) (.const 2)

/-- Word RAM expression evaluating to `baseVEVal (s.regs 15) code`. -/
def baseVEExpr (code : ℕ) : Expr :=
  if code = 0 then .const 0 else .reg 15

/-- Write one flat position `pos < S_tab δ ξ ω` of `buf.a_vv`, `buf.a_ve`, `buf.a_em` for `bcfg`. -/
def basePosWriteProg (δ ξ ω : ℕ) (buf : PieceBufLayout) (bcfg pos : ℕ) : Cmd :=
  .seq (.write buf.a_vv (.const pos) (baseVVExpr (baseVVCode δ ξ ω bcfg pos)))
  (.seq (.write buf.a_ve (.const pos) (baseVEExpr (baseVECode δ ξ ω bcfg pos)))
        (.write buf.a_em (.const pos) (.reg 12)))

/-- Body for branch `bcfg` in `baseTableFillProg`: sets `buf.r_tid` and fills all `pos < S_tab δ ξ ω`
of `buf.a_vv`, `buf.a_ve`, `buf.a_em`. -/
def baseTableBodyProg (δ ξ ω : ℕ) (buf : PieceBufLayout) (bcfg : ℕ) : Cmd :=
  let tid := encAbstractTable δ ξ ω
    ⟨(canonLocRoots bcfg).card, (canonBaseRawList δ bcfg).map (·.H)⟩
  .seq (.assign buf.r_tid (.const tid))
       (seqRange (S_tab δ ξ ω) (basePosWriteProg δ ξ ω buf bcfg))

/-- Shared table-fill gadget for any base piece (`treeBaseStepProg` or `isoBaseStepProg`):
expects `r_10 = v0`, `r_11 = v1`, `r_12 = e0`, `r_13 = bcfg`, `r_16 = kd_v0`, `r_17 = kd_v1`,
`r_18 = kd_e0`, allocates the 3 vertex-arena nodes and 1 edge-arena node, and runs
`branchOnBound 72 13 (baseTableBodyProg δ ξ ω buf)`. -/
def baseTableFillProg (δ ξ ω : ℕ) (buf : PieceBufLayout) : Cmd :=
  .seq (.assign 14 (.reg r_kv))
  (.seq (.assign 15 (.reg r_ke))
  (.seq (pushArenaNodeProg a_vkd a_vv1 a_vv2 r_kv (.reg 16) (.reg 10) (.const 0))
  (.seq (pushArenaNodeProg a_vkd a_vv1 a_vv2 r_kv (.reg 17) (.reg 11) (.const 0))
  (.seq (pushArenaNodeProg a_vkd a_vv1 a_vv2 r_kv (.const 2) (.reg 14) (.op .add (.reg 14) (.const 1)))
  (.seq (pushArenaNodeProg a_ekd a_ev1 a_ev2 r_ke (.reg 18) (.reg 12) (.const 0))
        (branchOnBound 72 13 (baseTableBodyProg δ ξ ω buf)))))))

theorem ValidPieceBuffer.mono_arena {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z_P.card)} {buf : PieceBufLayout} {s s' : State}
    (h : ValidPieceBuffer δ ξ ω G Z_P E_P es buf s)
    (htid : s'.regs buf.r_tid = s.regs buf.r_tid)
    (hq : s'.regs buf.r_q = s.regs buf.r_q)
    (hzV : s'.arrs buf.a_zV = s.arrs buf.a_zV)
    (hzI : s'.arrs buf.a_zI = s.arrs buf.a_zI)
    (hvv : s'.arrs buf.a_vv = s.arrs buf.a_vv)
    (hve : s'.arrs buf.a_ve = s.arrs buf.a_ve)
    (hem : s'.arrs buf.a_em = s.arrs buf.a_em)
    (hkv_le : s.regs r_kv ≤ s'.regs r_kv)
    (hke_le : s.regs r_ke ≤ s'.regs r_ke)
    (hevalV : ∀ p < s.regs r_kv,
      evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
        evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p)
    (hevalE : ∀ p < s.regs r_ke,
      evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
        evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) :
    ValidPieceBuffer δ ξ ω G Z_P E_P es buf s' where
  hq_le := h.hq_le
  hlen_le := h.hlen_le
  hdet := h.hdet
  htid := htid.trans h.htid
  hq := hq.trans h.hq
  hzV_len := by rw [hzV]; exact h.hzV_len
  hzI_len := by rw [hzI]; exact h.hzI_len
  hzV := fun i => by rw [hzV]; exact h.hzV i
  hzI := fun i => by rw [hzI]; exact h.hzI i
  hvv_len := by rw [hvv]; exact h.hvv_len
  hve_len := by rw [hve]; exact h.hve_len
  hem_len := by rw [hem]; exact h.hem_len
  hentries := fun idx => by
    rcases h.hentries idx with ⟨hvert, hedge⟩
    refine ⟨fun u => ?_, fun d => by rw [hem]; exact hedge d⟩
    rcases hvert u with ⟨hp_vv, hev_vv, hp_ve, hev_ve⟩
    rw [hvv, hve]
    exact ⟨Nat.lt_of_lt_of_le hp_vv hkv_le,
      (hevalV _ hp_vv).trans hev_vv,
      Nat.lt_of_lt_of_le hp_ve hke_le,
      (hevalE _ hp_ve).trans hev_ve⟩

theorem evalArena_baseVVVal {n kv₀ bcfg : ℕ} (hkv_pos : 0 < kv₀)
    {L_vkd L_vv1 L_vv2 : List ℕ}
    (hkv_len : kv₀ + 2 < L_vkd.length)
    (hkv_len1 : kv₀ + 2 < L_vv1.length)
    (hkv_len2 : kv₀ + 2 < L_vv2.length)
    (VA : Finset (Fin n)) (hn_loc : VA.card = (canonLocDigraph bcfg).numVerts)
    (S : Finset (Fin (canonLocDigraph bcfg).numVerts)) :
    let kd_v0 := if 0 < VA.card then 1 else 0
    let v0 := if h0 : 0 < VA.card then (finsetRootFn VA ⟨0, h0⟩).1 else 0
    let kd_v1 := if 1 < VA.card then 1 else 0
    let v1 := if h1 : 1 < VA.card then (finsetRootFn VA ⟨1, h1⟩).1 else 0
    let L_vkd' := ((L_vkd.set kv₀ kd_v0).set (kv₀ + 1) kd_v1).set (kv₀ + 2) 2
    let L_vv1' := ((L_vv1.set kv₀ v0).set (kv₀ + 1) v1).set (kv₀ + 2) kv₀
    let L_vv2' := ((L_vv2.set kv₀ 0).set (kv₀ + 1) 0).set (kv₀ + 2) (kv₀ + 1)
    let code := (if decide (∃ i ∈ S, i.1 = 0) then 1 else 0) +
                (if decide (∃ i ∈ S, i.1 = 1) then 2 else 0)
    baseVVVal kv₀ code < kv₀ + 3 ∧
    evalArena n L_vkd' L_vv1' L_vv2' (baseVVVal kv₀ code) =
      S.image (fun i => finsetRootFn VA ⟨i.1, hn_loc.symm ▸ i.2⟩) := by
  intro kd_v0 v0 kd_v1 v1 L_vkd' L_vv1' L_vv2' code
  have hbound : baseVVVal kv₀ code < kv₀ + 3 := by
    unfold baseVVVal; split_ifs <;> omega
  refine ⟨hbound, ?_⟩
  -- Evaluate `kv₀` and `kv₀ + 1` and `kv₀ + 2`
  have hev_0 :
      evalArena n L_vkd' L_vv1' L_vv2' kv₀ =
        if h0 : 0 < VA.card then {finsetRootFn VA ⟨0, h0⟩} else ∅ := by
    dsimp only [L_vkd', L_vv1', L_vv2']
    rw [evalArena_set_gt n _ _ _ (kv₀ + 2) 2 kv₀ (kv₀ + 1) kv₀ (by omega),
        evalArena_set_gt n _ _ _ (kv₀ + 1) kd_v1 v1 0 kv₀ (by omega)]
    dsimp only [kd_v0, v0]
    split_ifs with h0
    · exact evalArena_set_singleton hkv_pos L_vkd L_vv1 L_vv2 (by omega) (by omega)
        (finsetRootFn VA ⟨0, h0⟩) 0
    · exact evalArena_set_empty hkv_pos L_vkd L_vv1 L_vv2 (by omega) 0 0
  have hev_1 :
      evalArena n L_vkd' L_vv1' L_vv2' (kv₀ + 1) =
        if h1 : 1 < VA.card then {finsetRootFn VA ⟨1, h1⟩} else ∅ := by
    dsimp only [L_vkd', L_vv1', L_vv2']
    rw [evalArena_set_gt n _ _ _ (kv₀ + 2) 2 kv₀ (kv₀ + 1) (kv₀ + 1) (by omega)]
    dsimp only [kd_v1, v1]
    split_ifs with h1
    · exact evalArena_set_singleton (by omega) (L_vkd.set kv₀ kd_v0) (L_vv1.set kv₀ v0)
        (L_vv2.set kv₀ 0) (by simp; omega) (by simp; omega) (finsetRootFn VA ⟨1, h1⟩) 0
    · exact evalArena_set_empty (by omega) (L_vkd.set kv₀ kd_v0) (L_vv1.set kv₀ v0)
        (L_vv2.set kv₀ 0) (by simp; omega) 0 0
  have hev_2 :
      evalArena n L_vkd' L_vv1' L_vv2' (kv₀ + 2) =
        evalArena n L_vkd' L_vv1' L_vv2' kv₀ ∪ evalArena n L_vkd' L_vv1' L_vv2' (kv₀ + 1) := by
    dsimp only [L_vkd', L_vv1', L_vv2']
    rw [evalArena_set_union (by omega)
      ((L_vkd.set kv₀ kd_v0).set (kv₀ + 1) kd_v1)
      ((L_vv1.set kv₀ v0).set (kv₀ + 1) v1)
      ((L_vv2.set kv₀ 0).set (kv₀ + 1) 0)
      (by simp; omega) (by simp; omega) (by simp; omega) (by omega) (by omega),
      evalArena_set_gt n _ _ _ (kv₀ + 2) 2 kv₀ (kv₀ + 1) kv₀ (by omega),
      evalArena_set_gt n _ _ _ (kv₀ + 2) 2 kv₀ (kv₀ + 1) (kv₀ + 1) (by omega)]
  have hn_le2 : (canonLocDigraph bcfg).numVerts ≤ 2 := by
    change bcfg % 3 ≤ 2; omega
  have himg_eq :
      S.image (fun i => finsetRootFn VA ⟨i.1, hn_loc.symm ▸ i.2⟩) =
        (if decide (∃ i ∈ S, i.1 = 0) then
          if h0 : 0 < VA.card then {finsetRootFn VA ⟨0, h0⟩} else ∅
         else ∅) ∪
        (if decide (∃ i ∈ S, i.1 = 1) then
          if h1 : 1 < VA.card then {finsetRootFn VA ⟨1, h1⟩} else ∅
         else ∅) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_union]
    constructor
    · rintro ⟨i, hiS, rfl⟩
      have hi_lt2 : i.1 < 2 := Nat.lt_of_lt_of_le i.2 hn_le2
      rcases (by omega : i.1 = 0 ∨ i.1 = 1) with hi0 | hi1
      · left
        have h0_ex : ∃ j ∈ S, j.1 = 0 := ⟨i, hiS, hi0⟩
        have h0_card : 0 < VA.card := by have := i.2; omega
        simp only [decide_eq_true h0_ex, h0_card, ↓reduceIte, ↓reduceDIte, Finset.mem_singleton]
        congr 1
        exact Fin.ext hi0
      · right
        have h1_ex : ∃ j ∈ S, j.1 = 1 := ⟨i, hiS, hi1⟩
        have h1_card : 1 < VA.card := by have := i.2; omega
        simp only [decide_eq_true h1_ex, h1_card, ↓reduceIte, ↓reduceDIte, Finset.mem_singleton]
        congr 1
        exact Fin.ext hi1
    · rintro (hw0 | hw1)
      · split_ifs at hw0 with hex0 h0_card
        · rcases of_decide_eq_true hex0 with ⟨i, hiS, hi0⟩
          rw [Finset.mem_singleton] at hw0
          refine ⟨i, hiS, ?_⟩
          rw [hw0]
          congr 1
          exact Fin.ext hi0
        all_goals simp at hw0
      · split_ifs at hw1 with hex1 h1_card
        · rcases of_decide_eq_true hex1 with ⟨i, hiS, hi1⟩
          rw [Finset.mem_singleton] at hw1
          refine ⟨i, hiS, ?_⟩
          rw [hw1]
          congr 1
          exact Fin.ext hi1
        all_goals simp at hw1
  rw [himg_eq]
  dsimp only [code, baseVVVal]
  cases h_b0 : decide (∃ i ∈ S, i.1 = 0) <;> cases h_b1 : decide (∃ i ∈ S, i.1 = 1)
  · simp
  · simp [hev_1]
  · simp [hev_0]
  · simp [hev_2, hev_0, hev_1]

theorem evalArena_baseVEVal {m ke₀ bcfg : ℕ} (hke_pos : 0 < ke₀)
    {L_ekd L_ev1 L_ev2 : List ℕ}
    (hke_len : ke₀ < L_ekd.length)
    (hke_len1 : ke₀ < L_ev1.length)
    (EA : Finset (Fin m)) (hm_loc : EA.card = (canonLocDigraph bcfg).numEdges)
    (E : Finset (Fin (canonLocDigraph bcfg).numEdges)) :
    let kd_e0 := if 0 < EA.card then 1 else 0
    let e0 := if he : 0 < EA.card then (finsetRootFn EA ⟨0, he⟩).1 else 0
    let L_ekd' := L_ekd.set ke₀ kd_e0
    let L_ev1' := L_ev1.set ke₀ e0
    let L_ev2' := L_ev2.set ke₀ 0
    let code := if decide (∃ d ∈ E, d.1 = 0) then 1 else 0
    baseVEVal ke₀ code < ke₀ + 1 ∧
    evalArena m L_ekd' L_ev1' L_ev2' (baseVEVal ke₀ code) =
      E.image (fun d => finsetRootFn EA ⟨d.1, hm_loc.symm ▸ d.2⟩) := by
  intro kd_e0 e0 L_ekd' L_ev1' L_ev2' code
  have hbound : baseVEVal ke₀ code < ke₀ + 1 := by
    unfold baseVEVal; split_ifs <;> omega
  refine ⟨hbound, ?_⟩
  have hev_0 :
      evalArena m L_ekd' L_ev1' L_ev2' ke₀ =
        if he : 0 < EA.card then {finsetRootFn EA ⟨0, he⟩} else ∅ := by
    dsimp only [L_ekd', L_ev1', L_ev2', kd_e0, e0]
    split_ifs with he
    · exact evalArena_set_singleton hke_pos L_ekd L_ev1 L_ev2 hke_len hke_len1
        (finsetRootFn EA ⟨0, he⟩) 0
    · exact evalArena_set_empty hke_pos L_ekd L_ev1 L_ev2 hke_len 0 0
  have hm_le1 : (canonLocDigraph bcfg).numEdges ≤ 1 := by
    change (if bcfg % 3 = 0 then 0 else (bcfg / 3) % 2) ≤ 1
    split_ifs <;> omega
  have himg_eq :
      E.image (fun d => finsetRootFn EA ⟨d.1, hm_loc.symm ▸ d.2⟩) =
        if decide (∃ d ∈ E, d.1 = 0) then
          if he : 0 < EA.card then {finsetRootFn EA ⟨0, he⟩} else ∅
        else ∅ := by
    ext e
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨d, hdE, rfl⟩
      have hd0 : d.1 = 0 := by have := d.2; omega
      have hex : ∃ d' ∈ E, d'.1 = 0 := ⟨d, hdE, hd0⟩
      have he_card : 0 < EA.card := by have := d.2; omega
      simp only [decide_eq_true hex, he_card, ↓reduceIte, ↓reduceDIte, Finset.mem_singleton]
      congr 1
      exact Fin.ext hd0
    · intro he_mem
      split_ifs at he_mem with hex he_card
      · rcases of_decide_eq_true hex with ⟨d, hdE, hd0⟩
        rw [Finset.mem_singleton] at he_mem
        refine ⟨d, hdE, ?_⟩
        rw [he_mem]
        congr 1
        exact Fin.ext hd0
      all_goals simp at he_mem
  rw [himg_eq]
  dsimp only [code, baseVEVal]
  cases h_b : decide (∃ d ∈ E, d.1 = 0) <;> simp [hev_0]

private theorem eval_baseVVExpr {w kv₀ : ℕ} {s : State} (code : ℕ)
    (hw2 : 2 < 2 ^ w) (hkv_w : kv₀ + 2 < 2 ^ w) (hr14 : s.regs 14 = kv₀) :
    (baseVVExpr code).eval w s = some (baseVVVal kv₀ code) ∧
    (baseVVExpr code).cost ≤ 3 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hkv0_w : kv₀ < 2 ^ w := by omega
  have hkv1_w : kv₀ + 1 < 2 ^ w := by omega
  unfold baseVVExpr baseVVVal
  split_ifs with h0 h1 h2
  · exact ⟨by simp [Expr.eval, checkWord, h0_w], by decide⟩
  · exact ⟨by simp [Expr.eval, checkWord, hr14, hkv0_w], by decide⟩
  · exact ⟨by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr14, hw1, hkv0_w, hkv1_w], by decide⟩
  · exact ⟨by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr14, hw2, hkv0_w, hkv_w], by decide⟩

private theorem eval_baseVEExpr {w ke₀ : ℕ} {s : State} (code : ℕ)
    (hw1 : 1 < 2 ^ w) (hke_w : ke₀ < 2 ^ w) (hr15 : s.regs 15 = ke₀) :
    (baseVEExpr code).eval w s = some (baseVEVal ke₀ code) ∧
    (baseVEExpr code).cost ≤ 1 := by
  have h0_w : 0 < 2 ^ w := by omega
  unfold baseVEExpr baseVEVal
  split_ifs with h0
  · exact ⟨by simp [Expr.eval, checkWord, h0_w], by decide⟩
  · exact ⟨by simp [Expr.eval, checkWord, hr15, hke_w], by decide⟩

private theorem writeBasePos_exec {w pos kv₀ ke₀ e0 : ℕ} {buf : PieceBufLayout} {s : State}
    (c_vv c_ve : ℕ)
    (hvv_ve : buf.a_vv ≠ buf.a_ve) (hvv_em : buf.a_vv ≠ buf.a_em) (hve_em : buf.a_ve ≠ buf.a_em)
    (hw1 : 1 < 2 ^ w) (hw2 : 2 < 2 ^ w) (hpos_w : pos < 2 ^ w)
    (hkv_w : kv₀ + 2 < 2 ^ w) (hke_w : ke₀ < 2 ^ w) (he0_w : e0 < 2 ^ w)
    (hr12 : s.regs 12 = e0) (hr14 : s.regs 14 = kv₀) (hr15 : s.regs 15 = ke₀)
    (hpos_vv : pos < (s.arrs buf.a_vv).length)
    (hpos_ve : pos < (s.arrs buf.a_ve).length)
    (hpos_em : pos < (s.arrs buf.a_em).length) :
    let s' := ((s.writeArr buf.a_vv pos (baseVVVal kv₀ c_vv)).writeArr
                buf.a_ve pos (baseVEVal ke₀ c_ve)).writeArr buf.a_em pos e0
    ∃ t ≤ 15,
      Exec w
        (.seq (.write buf.a_vv (.const pos) (baseVVExpr c_vv))
        (.seq (.write buf.a_ve (.const pos) (baseVEExpr c_ve))
              (.write buf.a_em (.const pos) (.reg 12)))) s s' t := by
  rcases eval_baseVVExpr c_vv hw2 hkv_w hr14 with ⟨hev_vv, hcost_vv⟩
  let s_a := s.writeArr buf.a_vv pos (baseVVVal kv₀ c_vv)
  have hex_a : Exec w (.write buf.a_vv (.const pos) (baseVVExpr c_vv)) s s_a
      ((Expr.const pos).cost + (baseVVExpr c_vv).cost + 1) :=
    .write (by simp [Expr.eval, checkWord, hpos_w]) hev_vv hpos_vv
  have hr15_a : s_a.regs 15 = ke₀ := hr15
  rcases eval_baseVEExpr c_ve hw1 hke_w hr15_a with ⟨hev_ve, hcost_ve⟩
  let s_b := s_a.writeArr buf.a_ve pos (baseVEVal ke₀ c_ve)
  have hex_b : Exec w (.write buf.a_ve (.const pos) (baseVEExpr c_ve)) s_a s_b
      ((Expr.const pos).cost + (baseVEExpr c_ve).cost + 1) :=
    .write (by simp [Expr.eval, checkWord, hpos_w]) hev_ve
           (by simp [s_a, State.writeArr, State.setArr, hvv_ve.symm, hpos_ve])
  let s_c := s_b.writeArr buf.a_em pos e0
  have hex_c : Exec w (.write buf.a_em (.const pos) (.reg 12)) s_b s_c 3 :=
    .write (by simp [Expr.eval, checkWord, hpos_w])
           (by simp [s_b, s_a, Expr.eval, checkWord, hr12, he0_w])
           (by simp [s_b, s_a, State.writeArr, State.setArr, hvv_em.symm, hve_em.symm, hpos_em])
  dsimp [Expr.cost] at hex_a hex_b
  exact ⟨(1 + (baseVVExpr c_vv).cost + 1) + ((1 + (baseVEExpr c_ve).cost + 1) + 3),
    by omega, .seq hex_a (.seq hex_b hex_c)⟩

theorem baseTableBodyProg_exec {w δ ξ ω bcfg kv₀ ke₀ e0 : ℕ} {buf : PieceBufLayout} {s₀ : State}
    (hvv_ve : buf.a_vv ≠ buf.a_ve) (hvv_em : buf.a_vv ≠ buf.a_em) (hve_em : buf.a_ve ≠ buf.a_em)
    (hrt_12 : buf.r_tid ≠ 12) (hrt_14 : buf.r_tid ≠ 14) (hrt_15 : buf.r_tid ≠ 15)
    (hw2 : 2 < 2 ^ w)
    (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hT_w : T_max δ ξ ω < 2 ^ w)
    (hkv_w : kv₀ + 2 < 2 ^ w) (hke_w : ke₀ < 2 ^ w) (he0_w : e0 < 2 ^ w)
    (hr12 : s₀.regs 12 = e0) (hr14 : s₀.regs 14 = kv₀) (hr15 : s₀.regs 15 = ke₀)
    (hvv_len : (s₀.arrs buf.a_vv).length = S_tab δ ξ ω)
    (hve_len : (s₀.arrs buf.a_ve).length = S_tab δ ξ ω)
    (hem_len : (s₀.arrs buf.a_em).length = S_tab δ ξ ω) :
    ∃ s' t_step,
      Exec w (baseTableBodyProg δ ξ ω buf bcfg) s₀ s' t_step ∧
      t_step ≤ 5 + 15 * S_tab δ ξ ω ∧
      s'.regs buf.r_tid = encAbstractTable δ ξ ω
        ⟨(canonLocRoots bcfg).card, (canonBaseRawList δ bcfg).map (·.H)⟩ ∧
      (∀ r, r ≠ buf.r_tid → s'.regs r = s₀.regs r) ∧
      (∀ a, a ≠ buf.a_vv → a ≠ buf.a_ve → a ≠ buf.a_em → s'.arrs a = s₀.arrs a) ∧
      (s'.arrs buf.a_vv).length = S_tab δ ξ ω ∧
      (s'.arrs buf.a_ve).length = S_tab δ ξ ω ∧
      (s'.arrs buf.a_em).length = S_tab δ ξ ω ∧
      (∀ pos < S_tab δ ξ ω,
        (s'.arrs buf.a_vv).getD pos 0 = baseVVVal kv₀ (baseVVCode δ ξ ω bcfg pos) ∧
        (s'.arrs buf.a_ve).getD pos 0 = baseVEVal ke₀ (baseVECode δ ξ ω bcfg pos) ∧
        (s'.arrs buf.a_em).getD pos 0 = e0) := by
  have hw1 : 1 < 2 ^ w := by omega
  let tid := encAbstractTable δ ξ ω
    ⟨(canonLocRoots bcfg).card, (canonBaseRawList δ bcfg).map (·.H)⟩
  have htid_lt : tid < T_max δ ξ ω :=
    encAbstractTable_lt δ ξ ω _ (card_canonLocRoots_le_two ξ ω bcfg).2
      (by simpa using length_canonBaseRawList_le δ bcfg)
  have htid_w : tid < 2 ^ w := by omega
  let s₁ := s₀.setReg buf.r_tid tid
  have hex₁ : Exec w (.assign buf.r_tid (.const tid)) s₀ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, htid_w])
  let P : ℕ → State → Prop := fun k s =>
    s.regs buf.r_tid = tid ∧
    (∀ r, r ≠ buf.r_tid → s.regs r = s₀.regs r) ∧
    (∀ a, a ≠ buf.a_vv → a ≠ buf.a_ve → a ≠ buf.a_em → s.arrs a = s₀.arrs a) ∧
    (s.arrs buf.a_vv).length = S_tab δ ξ ω ∧
    (s.arrs buf.a_ve).length = S_tab δ ξ ω ∧
    (s.arrs buf.a_em).length = S_tab δ ξ ω ∧
    (∀ pos < k,
      (s.arrs buf.a_vv).getD pos 0 = baseVVVal kv₀ (baseVVCode δ ξ ω bcfg pos) ∧
      (s.arrs buf.a_ve).getD pos 0 = baseVEVal ke₀ (baseVECode δ ξ ω bcfg pos) ∧
      (s.arrs buf.a_em).getD pos 0 = e0)
  have hP0 : P 0 s₁ :=
    ⟨by simp [s₁], fun r hr => by simp [s₁, State.setReg, hr],
     fun _ _ _ _ => rfl, hvv_len, hve_len, hem_len, fun _ h => by omega⟩
  have hstep : ∀ pos < S_tab δ ξ ω, ∀ s, P pos s →
      ∃ s' t, Exec w (basePosWriteProg δ ξ ω buf bcfg pos) s s' t ∧ t ≤ 15 ∧ P (pos + 1) s' := by
    intro pos hpos s ⟨htid_s, hreg_s, harr_s, hvv_s, hve_s, hem_s, hprev⟩
    have hpos_w : pos < 2 ^ w := by omega
    have hr12_s : s.regs 12 = e0 := (hreg_s 12 hrt_12.symm).trans hr12
    have hr14_s : s.regs 14 = kv₀ := (hreg_s 14 hrt_14.symm).trans hr14
    have hr15_s : s.regs 15 = ke₀ := (hreg_s 15 hrt_15.symm).trans hr15
    rcases writeBasePos_exec (baseVVCode δ ξ ω bcfg pos) (baseVECode δ ξ ω bcfg pos)
        hvv_ve hvv_em hve_em hw1 hw2 hpos_w hkv_w hke_w he0_w hr12_s hr14_s hr15_s
        (by omega) (by omega) (by omega) with ⟨t, ht, hex_pos⟩
    let s_c := ((s.writeArr buf.a_vv pos (baseVVVal kv₀ (baseVVCode δ ξ ω bcfg pos))).writeArr
                buf.a_ve pos (baseVEVal ke₀ (baseVECode δ ξ ω bcfg pos))).writeArr buf.a_em pos e0
    have hs_c_vv : s_c.arrs buf.a_vv = (s.arrs buf.a_vv).set pos (baseVVVal kv₀ (baseVVCode δ ξ ω bcfg pos)) := by
      simp [s_c, State.writeArr, State.setArr, hvv_ve, hvv_em]
    have hs_c_ve : s_c.arrs buf.a_ve = (s.arrs buf.a_ve).set pos (baseVEVal ke₀ (baseVECode δ ξ ω bcfg pos)) := by
      simp [s_c, State.writeArr, State.setArr, hvv_ve.symm, hve_em]
    have hs_c_em : s_c.arrs buf.a_em = (s.arrs buf.a_em).set pos e0 := by
      simp [s_c, State.writeArr, State.setArr, hvv_em.symm, hve_em.symm]
    refine ⟨s_c, t, hex_pos, ht, htid_s, hreg_s,
      fun a ha1 ha2 ha3 => by
        simp [s_c, State.writeArr, State.setArr, ha1, ha2, ha3, harr_s a ha1 ha2 ha3],
      by rw [hs_c_vv, List.length_set, hvv_s],
      by rw [hs_c_ve, List.length_set, hve_s],
      by rw [hs_c_em, List.length_set, hem_s],
      fun q hq_lt => ?_⟩
    rw [hs_c_vv, hs_c_ve, hs_c_em]
    by_cases hq_pos : q = pos
    · subst hq_pos
      exact ⟨getD_set_eq (s.arrs buf.a_vv) q _ (by omega),
             getD_set_eq (s.arrs buf.a_ve) q _ (by omega),
             getD_set_eq (s.arrs buf.a_em) q _ (by omega)⟩
    · rcases hprev q (by omega) with ⟨h1, h2, h3⟩
      rw [getD_set_ne _ pos _ q hq_pos, getD_set_ne _ pos _ q hq_pos, getD_set_ne _ pos _ q hq_pos]
      exact ⟨h1, h2, h3⟩
  rcases Exec.seqRange P hP0 hstep with ⟨s', t_seq, hex_seq, ht_seq, hP'⟩
  rcases hP' with ⟨htid', hreg', harr', hvv', hve', hem', hpos'⟩
  exact ⟨s', 2 + t_seq, .seq hex₁ hex_seq, by omega,
    htid', hreg', harr', hvv', hve', hem', hpos'⟩

end GraphMinor.Compute
