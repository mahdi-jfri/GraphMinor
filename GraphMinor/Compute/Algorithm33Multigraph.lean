module

public import GraphMinor.Compute.Algorithm33MultiComb

/-!
# Graph Minors XIII, Algorithm (3.3) on a Multigraph in the Word RAM Model

This file completes the Word RAM implementation of Algorithm (3.3) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995),
pages 72–75, on a multigraph `G : MultiDigraph n` (allowing loops and parallel edges):

1. **First step (page 73):**
   "We construct the simple graph $H_1$ underlying $G$, by deleting all loops and multiple edges."
   Implemented via `toSimpleGraphEdgeListProg` from `GraphMinor/Compute/MultiDigraph.lean`.
2. **Core simple-graph recursion (pages 73–74):**
   If $|E(H_1)| \ge 2$, runs `.seq (initAlg33Prog ω) (alg33LoopProg ω)` from
   `GraphMinor/Compute/Algorithm33.lean` (shifted to scratch arrays/registers via `Cmd.shift`).
3. **Last step (page 73):**
   "If $H_2 = H_1$, we convert our branch-decomposition to one for $G$, set $G' = G$, and stop."
   - When $|E(H_1)| < 2$ or ($H_3 = H_2 = H_1$), converts the branch-decomposition of $H_1$ to one
     for $G$ in $O(v^2 + \varepsilon)$ steps by assigning each edge of $G$ to the leaf of its
     underlying simple edge (or an incident edge for loops, or a 2-leaf tree when $|E(H_1)| < 2$)
     and splitting leaves with $> 1$ assigned edge (`pass2SplitProg`).
   - When $H_3 \ne H_1$, lifts $H_3$ to a simple subdigraph $G' = \mathrm{liftSimpleSubgraph}\ G\ H_3 \le G$
     with the same branch-decomposition of width $\le 3\omega$ and branch-width $\ge \omega$
     (`liftSubgraphProg`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

local macro "romega" : tactic => `(tactic| ((try dsimp [Reg, Arr] at *); (try omega)))

/-! ### Section 1: Shifting Array and Register Indices (`Expr.shift`, `Cmd.shift`, `Exec.shift`) -/

/-- Shift all array indices by `a_off` and all register indices by `r_off` in an expression `e`. -/
def Expr.shift (a_off r_off : ℕ) : Expr → Expr
  | .const n => .const n
  | .reg r => .reg (r + r_off)
  | .read a idx => .read (a + a_off) (idx.shift a_off r_off)
  | .readMin a idx cap => .readMin (a + a_off) (idx.shift a_off r_off) (cap.shift a_off r_off)
  | .len a => .len (a + a_off)
  | .op bop e₁ e₂ => .op bop (e₁.shift a_off r_off) (e₂.shift a_off r_off)

@[simp]
theorem Expr.cost_shift (a_off r_off : ℕ) (e : Expr) :
    (e.shift a_off r_off).cost = e.cost := by
  induction e <;> simp [Expr.shift, Expr.cost, *]

/-- Shift all array indices by `a_off` and all register indices by `r_off` in a command `c`. -/
def Cmd.shift (a_off r_off : ℕ) : Cmd → Cmd
  | .skip => .skip
  | .assign r e => .assign (r + r_off) (e.shift a_off r_off)
  | .write a idx val => .write (a + a_off) (idx.shift a_off r_off) (val.shift a_off r_off)
  | .alloc a len => .alloc (a + a_off) (len.shift a_off r_off)
  | .seq c₁ c₂ => .seq (c₁.shift a_off r_off) (c₂.shift a_off r_off)
  | .ite cond c₁ c₂ => .ite (cond.shift a_off r_off) (c₁.shift a_off r_off) (c₂.shift a_off r_off)
  | .while cond body => .while (cond.shift a_off r_off) (body.shift a_off r_off)

/-- View of state `s` shifted down by `(a_off, r_off)`. -/
def State.unshift (a_off r_off : ℕ) (s : State) : State where
  regs r := s.regs (r + r_off)
  arrs a := s.arrs (a + a_off)

@[simp]
theorem State.unshift_regs (a_off r_off : ℕ) (s : State) (r : Reg) :
    (s.unshift a_off r_off).regs r = s.regs (r + r_off) := rfl

@[simp]
theorem State.unshift_arrs (a_off r_off : ℕ) (s : State) (a : Arr) :
    (s.unshift a_off r_off).arrs a = s.arrs (a + a_off) := rfl

/-- Splice a sub-state `s_sub` (at offsets `a_off`, `r_off`) back into `s_orig`. -/
def State.applyShifted (a_off r_off : ℕ) (s_orig s_sub : State) : State where
  regs r := if r_off ≤ r then s_sub.regs (r - r_off) else s_orig.regs r
  arrs a := if a_off ≤ a then s_sub.arrs (a - a_off) else s_orig.arrs a

@[simp]
theorem State.applyShifted_unshift_self (a_off r_off : ℕ) (s : State) :
    s.applyShifted a_off r_off (s.unshift a_off r_off) = s := by
  cases s with | mk regs arrs =>
  dsimp [State.applyShifted, State.unshift, Reg, Arr]
  congr 1
  · funext r
    split_ifs with h
    · congr 1; exact Nat.sub_add_cancel h
    · rfl
  · funext a
    split_ifs with h
    · congr 1; exact Nat.sub_add_cancel h
    · rfl

@[simp]
theorem State.applyShifted_regs_add (a_off r_off : ℕ) (s_orig s_sub : State) (r : ℕ) :
    (s_orig.applyShifted a_off r_off s_sub).regs (r + r_off) = s_sub.regs r := by
  dsimp [State.applyShifted, Reg]
  rw [ite_eq_left_iff.mpr (fun h => False.elim (h (Nat.le_add_left r_off r)))]
  congr 1; exact Nat.add_sub_cancel r r_off

theorem State.applyShifted_regs_add' (a_off r_off : ℕ) (s_orig s_sub : State) (r : ℕ) :
    (s_orig.applyShifted a_off r_off s_sub).regs (r_off + r) = s_sub.regs r := by
  rw [Nat.add_comm r_off r]
  exact State.applyShifted_regs_add a_off r_off s_orig s_sub r

@[simp]
theorem State.applyShifted_arrs_add (a_off r_off : ℕ) (s_orig s_sub : State) (a : ℕ) :
    (s_orig.applyShifted a_off r_off s_sub).arrs (a + a_off) = s_sub.arrs a := by
  dsimp [State.applyShifted, Arr]
  rw [ite_eq_left_iff.mpr (fun h => False.elim (h (Nat.le_add_left a_off a)))]
  congr 1; exact Nat.add_sub_cancel a a_off

theorem State.applyShifted_arrs_add' (a_off r_off : ℕ) (s_orig s_sub : State) (a : ℕ) :
    (s_orig.applyShifted a_off r_off s_sub).arrs (a_off + a) = s_sub.arrs a := by
  rw [Nat.add_comm a_off a]
  exact State.applyShifted_arrs_add a_off r_off s_orig s_sub a

theorem State.applyShifted_regs_lt (a_off r_off : ℕ) (s_orig s_sub : State) {r : ℕ}
    (hr : r < r_off) :
    (s_orig.applyShifted a_off r_off s_sub).regs r = s_orig.regs r := by
  dsimp [State.applyShifted, Reg]
  exact ite_eq_right_iff.mpr (fun h => False.elim (by omega))

theorem State.applyShifted_arrs_lt (a_off r_off : ℕ) (s_orig s_sub : State) {a : ℕ}
    (ha : a < a_off) :
    (s_orig.applyShifted a_off r_off s_sub).arrs a = s_orig.arrs a := by
  dsimp [State.applyShifted, Arr]
  exact ite_eq_right_iff.mpr (fun h => False.elim (by omega))

theorem State.applyShifted_setReg (a_off r_off : ℕ) (s_orig s_sub : State) (r : ℕ) (v : ℕ) :
    (s_orig.applyShifted a_off r_off s_sub).setReg (r + r_off) v =
      s_orig.applyShifted a_off r_off (s_sub.setReg r v) := by
  unfold State.setReg
  dsimp [State.applyShifted, Reg, Arr]
  congr 1
  funext r'
  by_cases h1 : r' = r + r_off
  · subst h1
    have h2 : r_off ≤ r + r_off := Nat.le_add_left r_off r
    simp [Function.update_self, h2]
  · rw [Function.update_of_ne h1]
    split_ifs with h2
    · have h3 : r' - r_off ≠ r := by omega
      rw [Function.update_of_ne h3]
    · rfl

theorem State.applyShifted_setArr (a_off r_off : ℕ) (s_orig s_sub : State) (a : ℕ) (l : List ℕ) :
    (s_orig.applyShifted a_off r_off s_sub).setArr (a + a_off) l =
      s_orig.applyShifted a_off r_off (s_sub.setArr a l) := by
  unfold State.setArr
  dsimp [State.applyShifted, Reg, Arr]
  congr 1
  funext a'
  by_cases h1 : a' = a + a_off
  · subst h1
    have h2 : a_off ≤ a + a_off := Nat.le_add_left a_off a
    simp [Function.update_self, h2]
  · rw [Function.update_of_ne h1]
    split_ifs with h2
    · have h3 : a' - a_off ≠ a := by omega
      rw [Function.update_of_ne h3]
    · rfl

theorem State.applyShifted_writeArr (a_off r_off : ℕ) (s_orig s_sub : State) (a : ℕ) (i v : ℕ) :
    (s_orig.applyShifted a_off r_off s_sub).writeArr (a + a_off) i v =
      s_orig.applyShifted a_off r_off (s_sub.writeArr a i v) := by
  unfold State.writeArr
  rw [State.applyShifted_arrs_add, State.applyShifted_setArr]

@[simp]
theorem Expr.eval_shift (w a_off r_off : ℕ) (s_orig s_sub : State) (e : Expr) :
    (e.shift a_off r_off).eval w (s_orig.applyShifted a_off r_off s_sub) = e.eval w s_sub := by
  induction e with
  | const n => rfl
  | reg r => simp [Expr.shift, Expr.eval]
  | read a idx ih =>
    simp [Expr.shift, Expr.eval, ih]
  | readMin a idx cap ih₁ ih₂ =>
    simp [Expr.shift, Expr.eval, ih₁, ih₂]
  | len a => simp [Expr.shift, Expr.eval]
  | op bop e₁ e₂ ih₁ ih₂ =>
    simp [Expr.shift, Expr.eval, ih₁, ih₂]

/-- Executing `c.shift a_off r_off` from `s_orig.applyShifted a_off r_off s_sub` mirrors executing
`c` from `s_sub` in the exact same step count `t`. -/
theorem Exec.shift {w : ℕ} (a_off r_off : ℕ) (s_orig : State)
    {c : Cmd} {s_sub s_sub' : State} {t : ℕ}
    (h : Exec w c s_sub s_sub' t) :
    Exec w (c.shift a_off r_off)
      (s_orig.applyShifted a_off r_off s_sub)
      (s_orig.applyShifted a_off r_off s_sub') t := by
  induction h with
  | skip s =>
    exact .skip _
  | @assign r e s v he =>
    rw [← State.applyShifted_setReg, ← Expr.cost_shift a_off r_off e]
    exact .assign (by simpa using he)
  | @write a idx val s i v hi hv hbound =>
    rw [← State.applyShifted_writeArr,
        ← Expr.cost_shift a_off r_off idx, ← Expr.cost_shift a_off r_off val]
    exact .write (by simpa using hi) (by simpa using hv) (by simpa using hbound)
  | @alloc a len s m hm =>
    rw [← State.applyShifted_setArr, ← Expr.cost_shift a_off r_off len]
    exact .alloc (by simpa using hm)
  | seq _ _ ih₁ ih₂ =>
    exact .seq ih₁ ih₂
  | @ite_true cond c₁ c₂ s s' v t hcond hv _ ih =>
    rw [← Expr.cost_shift a_off r_off cond]
    exact .ite_true (by simpa using hcond) hv ih
  | @ite_false cond c₁ c₂ s s' t hcond _ ih =>
    rw [← Expr.cost_shift a_off r_off cond]
    exact .ite_false (by simpa using hcond) ih
  | @while_false cond body s hcond =>
    rw [← Expr.cost_shift a_off r_off cond]
    exact .while_false (by simpa using hcond)
  | @while_true cond body s s₁ s₂ v t₁ t₂ hcond hv _ _ ih₁ ih₂ =>
    rw [← Expr.cost_shift a_off r_off cond]
    exact .while_true (by simpa using hcond) hv ih₁ ih₂

theorem Exec.shift_from {w : ℕ} (a_off r_off : ℕ) {c : Cmd} {s s_sub' : State} {t : ℕ}
    (h : Exec w c (s.unshift a_off r_off) s_sub' t) :
    Exec w (c.shift a_off r_off) s (s.applyShifted a_off r_off s_sub') t := by
  have h' := Exec.shift a_off r_off s h
  rwa [State.applyShifted_unshift_self] at h'

/-! ### Section 2: Running the Core Simple-Graph Algorithm (3.3) at Shifted Offsets -/

/-- Core simple-graph recursion of Algorithm (3.3): `initAlg33Prog ω` followed by `alg33LoopProg ω`
(without `writeAlg33OutProg`, leaving the working arrays in place). -/
def alg33CoreProg (ω : ℕ) : Cmd :=
  .seq (initAlg33Prog ω) (alg33LoopProg ω)

/-- Specification for `(alg33CoreProg ω).shift a_sub r_sub` when `s.arrs a_sub` holds
`encGraph G.toSimpleGraph` and `2 ≤ (edgeListOf G.toSimpleGraph).length`. -/
theorem alg33CoreShifted_exec {w n ω : ℕ} (hω : 2 ≤ ω) (G : MultiDigraph n)
    (a_sub r_sub : ℕ)
    (hm₁_ge2 : 2 ≤ (edgeListOf G.toSimpleGraph).length)
    (hw3 : 3 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (h2n_w : 2 * n < 2 ^ w)
    (hm1_w : 2 + 2 * (edgeListOf G.toSimpleGraph).length < 2 ^ w)
    (hB_w : (3 * ω - 2) * n + 2 < 2 ^ w)
    (h3w_w : 3 * ω < 2 ^ w)
    {s : State}
    (hin : s.arrs a_sub = encGraph G.toSimpleGraph) :
    let edges₁ := edgeListOf G.toSimpleGraph
    let m₂ := min edges₁.length (maxEdgesH2 ω n)
    let edges₂ := edges₁.take m₂
    let hloop₂ := take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂
    ∃ (s' : State) (t_core t₀ : ℕ) (ht₀_pos : 0 < t₀)
      (aliveSet : Finset (Fin edges₂.length))
      (step6_flag : ℕ)
      (f_tau : Fin edges₂.length → Fin t₀)
      (p₀ : ℕ → ℕ),
      Exec w ((alg33CoreProg ω).shift a_sub r_sub) s s' t_core ∧
      t_core ≤ (45 * m₂ + n + 60) +
        ((22 * m₂ + 20 * t₀ + 21) +
         (3 + (m₂ - 1) * (iterStepMax ω n m₂ + 30 * m₂ + 12))) ∧
      2 ≤ t₀ ∧
      t₀ ≤ 2 * m₂ ∧
      step6_flag ≤ 1 ∧
      edges₂.length = m₂ ∧
      IsEndpointArrs edges₂ (a_sub + 2) (a_sub + 3) s' ∧
      IsBitSet aliveSet (a_sub + 4) s' ∧
      IsTauArr f_tau (a_sub + 5) s' ∧
      IsParentArr edges₂.length t₀ p₀ (a_sub + 6) s' ∧
      2 * (treeLeaves (parentTree t₀ p₀)).card = t₀ + 2 ∧
      IsBranchDecompOfWidthLe (3 * ω)
        (graphOfAlive edges₂ hloop₂ aliveSet)
        (parentTree t₀ p₀)
        (tauOfArr edges₂ t₀ ht₀_pos f_tau) ∧
      (step6_flag = 0 ∧ m₂ = edges₁.length →
        aliveSet = Finset.univ ∧
        graphOfAlive edges₂ hloop₂ aliveSet = G.toSimpleGraph) ∧
      (¬ (step6_flag = 0 ∧ m₂ = edges₁.length) →
        liftSimpleSubgraph G (graphOfAlive edges₂ hloop₂ aliveSet) ≠ G ∧
        IsAlg33HighWidthCase ω G (liftSimpleSubgraph G (graphOfAlive edges₂ hloop₂ aliveSet))) ∧
      s'.regs r_sub = n ∧
      s'.regs (r_sub + 2) = m₂ ∧
      s'.regs (r_sub + 4) = t₀ ∧
      s'.regs (r_sub + 5) = step6_flag ∧
      (∀ a < a_sub, s'.arrs a = s.arrs a) ∧
      (∀ r < r_sub, s'.regs r = s.regs r) := by
  intro edges₁ m₂ edges₂ hloop₂
  change 2 ≤ edges₁.length at hm₁_ge2
  change 2 + 2 * edges₁.length < 2 ^ w at hm1_w
  have hedges₁ : IsSimpleEdgeList G.toSimpleGraph edges₁ :=
    isSimpleEdgeList_edgeListOf G.toSimpleGraph
  have hm₁_card : G.toSimpleGraph.edgeFinset.card = edges₁.length :=
    (length_edgeListOf_eq_card_edgeFinset G.toSimpleGraph).symm
  have hn_pos : 1 ≤ n :=
    one_le_n_of_two_le_edges G.toSimpleGraph (by omega)
  have hedges₂ : IsSimpleEdgeList (graphOfEdgeList edges₂ hloop₂) edges₂ :=
    isSimpleEdgeList_take hedges₁ m₂
  have hm₂_le1 : m₂ ≤ edges₁.length := Nat.min_le_left _ _
  have hlen_e2 : edges₂.length = m₂ := List.length_take_of_le hm₂_le1
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h2m2_w : 2 + 2 * edges₂.length < 2 ^ w := by omega
  have hm₂_w : edges₂.length < 2 ^ w := by omega
  let s_u0 := s.unshift a_sub r_sub
  have hin_u0 : s_u0.arrs inArr = [n, edges₁.length] ++ flatEdges edges₁ := by
    change s.arrs (0 + a_sub) = [n, edges₁.length] ++ flatEdges edges₁
    rw [Nat.zero_add]
    exact hin
  rcases initAlg33Prog_exec hω G.toSimpleGraph edges₁ hedges₁ hm₁_ge2 hn_pos
      hw2 hn_w hm1_w hB_w hin_u0 with
    ⟨s_u1, t₁, hex₁, ht₁, hr0_1, _, hr2_1, hr3_1, hr4_1, hr5_1, hr6_1,
      hend₁, hal₁, htau₁, hpar₁, hlast_al₁, hlast_Z₁, hpart₁⟩
  rcases findDupLeafProg_exec (Finset.univ : Finset (Fin edges₂.length))
      (initFTau edges₂.length) hw hm₂_w hw2 hal₁ htau₁
      (by rw [hr2_1, hlen_e2]) hr4_1 with
    ⟨s_u2, t₂, hex₂, ht₂, hr7_inv₂, harr₂, hreg₂⟩
  have hG2_le : graphOfEdgeList edges₂ hloop₂ ≤ G.toSimpleGraph :=
    graphOfEdgeList_take_le hedges₁ m₂
  have hcert_init : Step6CertInv ω G.toSimpleGraph edges₂ hloop₂ Finset.univ ∅ ∅ 0 0 :=
    Or.inl ⟨rfl, rfl, rfl⟩
  have hleaves_init : 2 * (treeLeaves (parentTree 2 (fun _ => 0))).card = 2 + 2 := by
    rw [treeLeaves_parentTree_two]
    rfl
  have hpot_init : 2 * (Finset.univ : Finset (Fin edges₂.length)).card ≤ 2 + 2 * (m₂ - 1) := by
    rw [Finset.card_univ, Fintype.card_fin, hlen_e2]
    omega
  have hpar₁' : IsParentArr edges₂.length 2 (fun _ => 0) 6 s_u1 := by
    rwa [hlen_e2]
  rcases alg33While_exec (by omega : 1 ≤ ω) hedges₂ hG2_le hw2 h2n_w h2m2_w h3w_w (m₂ - 1)
      (by decide : 0 < 2) Finset.univ ∅ ∅ 0 0 (initFTau edges₂.length) (fun _ => 0)
      hpart₁ hcert_init hleaves_init hpot_init
      (s := s_u2)
      (hend₁.of_arrs_eq (harr₂ 2 (by decide)) (harr₂ 3 (by decide)))
      (hal₁.of_arr_eq (harr₂ 4 (by decide)))
      (htau₁.of_arr_eq (harr₂ 5 (by decide)))
      (hpar₁'.of_arr_eq (harr₂ 6 (by decide)))
      (hlast_al₁.of_arr_eq (harr₂ 7 (by decide)))
      (hlast_Z₁.of_arr_eq (harr₂ 8 (by decide)))
      (by rw [hreg₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide), hr0_1])
      (by rw [hreg₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide), hr2_1, hlen_e2])
      (by rw [hreg₂ 3 (by decide) (by decide) (by decide) (by decide) (by decide), hr3_1, hlen_e2])
      (by rw [hreg₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4_1])
      (by rw [hreg₂ 5 (by decide) (by decide) (by decide) (by decide) (by decide), hr5_1])
      (by rw [hreg₂ 6 (by decide) (by decide) (by decide) (by decide) (by decide), hr6_1])
      hr7_inv₂ with
    ⟨s_u3, t₃, t₀, ht₀_pos, aliveSet', lastAliveSet', Z_step6', step6_flag', last_g',
      f_tau', p₀, hex₃, ht₃, hend₃, hal₃, htau₃, hpar₃, _, _,
      hpart₃, hcert₃, hleaves_card₃, hinj₃, hr0_3, hr2_3, _, hr4_3, hr5_3, _⟩
  have hex_u : Exec w (alg33CoreProg ω) s_u0 s_u3 (t₁ + (t₂ + t₃)) :=
    .seq hex₁ (.seq hex₂ hex₃)
  have hex_shift : Exec w ((alg33CoreProg ω).shift a_sub r_sub)
      s (s.applyShifted a_sub r_sub s_u3) (t₁ + (t₂ + t₃)) :=
    Exec.shift_from a_sub r_sub hex_u
  let s' := s.applyShifted a_sub r_sub s_u3
  have ht₀_le : t₀ ≤ 2 * m₂ := by rw [← hlen_e2]; exact hpar₃.2.1
  have ht₀_ge2 : 2 ≤ t₀ := by
    rcases hpart₃.2.2.1 with _
    have hcard_pos : 0 < (treeLeaves (parentTree t₀ p₀)).card := by
      by_contra h0
      have hcard0 : (treeLeaves (parentTree t₀ p₀)).card = 0 := by omega
      omega
    by_cases h1 : (treeLeaves (parentTree t₀ p₀)).card = 1
    · omega
    · omega
  -- Prove `IsBranchDecompOfWidthLe (3 * ω)` for `H₃ = graphOfAlive edges₂ hloop₂ aliveSet'`
  have hbd : IsBranchDecompOfWidthLe (3 * ω)
      (graphOfAlive edges₂ hloop₂ aliveSet')
      (parentTree t₀ p₀)
      (tauOfArr edges₂ t₀ ht₀_pos f_tau') := by
    classical
    rcases hpart₃ with ⟨htree, hmaps, hsurj, hord⟩
    refine ⟨htree, ⟨fun e he => hmaps e he, ?_, fun v hv => hsurj v hv⟩, hord⟩
    intro e₁ he₁ e₂ he₂ heq
    rw [Finset.mem_coe] at he₁ he₂
    rw [mem_edgeFinset_graphOfAlive_iff hedges₂] at he₁ he₂
    rcases he₁ with ⟨i, hi_al, rfl⟩
    rcases he₂ with ⟨j, hj_al, rfl⟩
    rw [tauOfArr_symEdgeAt hedges₂, tauOfArr_symEdgeAt hedges₂] at heq
    by_contra hne
    have hij_ne : i ≠ j := fun h => hne (congrArg (symEdgeAt edges₂) h)
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij_ne) with hlt | hgt
    · exact hinj₃ i j hlt hi_al hj_al heq
    · exact hinj₃ j i hgt hj_al hi_al heq.symm
  have hsub_H1 : graphOfAlive edges₂ hloop₂ aliveSet' ≤ G.toSimpleGraph :=
    (graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet').trans
      (graphOfEdgeList_take_le hedges₁ m₂)
  have hflag_le : step6_flag' ≤ 1 := by
    rcases hcert₃ with ⟨rfl, _, _⟩ | ⟨rfl, _⟩ <;> omega
  refine ⟨s', t₁ + (t₂ + t₃), t₀, ht₀_pos, aliveSet', step6_flag', f_tau', p₀,
    hex_shift, ?_, ht₀_ge2, ht₀_le, hflag_le, hlen_e2, ?_, ?_, ?_, ?_, hleaves_card₃, hbd,
    ?_, ?_, ?_, ?_, ?_, ?_,
    fun a ha => State.applyShifted_arrs_lt a_sub r_sub s s_u3 ha,
    fun r hr => State.applyShifted_regs_lt a_sub r_sub s s_u3 hr⟩
  · rw [hlen_e2] at ht₂ ht₃
    have ht₁' : t₁ ≤ 45 * m₂ + n + 60 := ht₁
    have ht₂' : t₂ ≤ 22 * m₂ + 20 * t₀ + 21 := by omega
    exact Nat.add_le_add ht₁' (Nat.add_le_add ht₂' ht₃)
  · rcases hend₃ with ⟨h1, h2, hall⟩
    have ha2 := State.applyShifted_arrs_add' a_sub r_sub s s_u3 2
    have ha3 := State.applyShifted_arrs_add' a_sub r_sub s s_u3 3
    exact ⟨by rw [ha2, h1], by rw [ha3, h2], fun k => by simp only [s', ha2, ha3]; exact hall k⟩
  · rcases hal₃ with ⟨h1, h2, h3⟩
    have ha4 := State.applyShifted_arrs_add' a_sub r_sub s s_u3 4
    exact ⟨by rw [ha4, h1], fun k => by simp only [s', ha4]; exact h2 k,
      fun k => by simp only [s', ha4]; exact h3 k⟩
  · rcases htau₃ with ⟨h1, h2⟩
    have ha5 := State.applyShifted_arrs_add' a_sub r_sub s s_u3 5
    exact ⟨by rw [ha5, h1], fun k => by simp only [s', ha5]; exact h2 k⟩
  · rcases hpar₃ with ⟨h1, h2, h3, h4⟩
    have ha6 := State.applyShifted_arrs_add' a_sub r_sub s s_u3 6
    exact ⟨by rw [ha6, h1], h2, fun z hz => by simp only [s', ha6]; exact h3 z hz, h4⟩
  · rintro ⟨hflag0, hm₂_eq⟩
    rcases hcert₃ with ⟨_, rfl, _⟩ | ⟨hflag1, _⟩
    · refine ⟨rfl, ?_⟩
      rw [graphOfAlive_univ]
      exact graphOfEdgeList_take_eq_of_le hedges₁ (by omega)
    · omega
  · intro hnot
    -- Three-case disjunction + `H₃ ≠ G.toSimpleGraph`
    let g_cert : Sym2 (Fin n) :=
      if hg : last_g' < edges₂.length then symEdgeAt edges₂ ⟨last_g', hg⟩
      else s(⟨0, hn_pos⟩, ⟨0, hn_pos⟩)
    rcases hcert₃ with ⟨hflag0, rfl, _⟩ |
      ⟨hflag1, hg_lt, hG6_le, hg_mem, hZ_card, hal_erase, hno_sep⟩
    · have hm₂_ne : m₂ ≠ edges₁.length := fun h => hnot ⟨hflag0, h⟩
      have hgt : maxEdgesH2 ω n < edges₁.length := by
        by_contra hle
        exact hm₂_ne (Nat.min_eq_left (by omega))
      have hm₂_eq : m₂ = maxEdgesH2 ω n := Nat.min_eq_right (by omega)
      have hcard_H2 : (graphOfEdgeList edges₂ hloop₂).edgeFinset.card = maxEdgesH2 ω n := by
        have h1 := card_edgeFinset_of_isSimpleEdgeList (graphOfEdgeList edges₂ hloop₂) hedges₂
        omega
      have hne_H1 : graphOfAlive edges₂ hloop₂ Finset.univ ≠ G.toSimpleGraph := by
        rw [graphOfAlive_univ]
        intro heq
        have hcards : (graphOfEdgeList edges₂ hloop₂).edgeFinset.card =
            G.toSimpleGraph.edgeFinset.card := by
          congr 1; ext e; simp [heq]
        omega
      apply isAlg33HighWidthCase_liftSimpleSubgraph ω G
        (graphOfAlive edges₂ hloop₂ Finset.univ)
        (graphOfAlive edges₂ hloop₂ lastAliveSet') g_cert Z_step6' hsub_H1 hne_H1
      right; left
      refine ⟨hne_H1, ?_, ?_⟩
      · convert maxEdgesH2_le_rat (by omega : 1 ≤ ω) using 2
        rw [← hcard_H2]
        congr 1; ext e; simp [SimpleGraph.mem_edgeFinset, graphOfAlive_univ]
      · convert maxEdgesH2_gt_rat (by omega : 1 ≤ ω) using 2
        rw [← hcard_H2]
        congr 1; ext e; simp [SimpleGraph.mem_edgeFinset, graphOfAlive_univ]
    · have hg_eq : g_cert = symEdgeAt edges₂ ⟨last_g', hg_lt⟩ :=
        dite_eq_left_of_eq_true (eq_true hg_lt)
      have herase_eq :
          graphOfAlive edges₂ hloop₂ aliveSet' =
            (graphOfAlive edges₂ hloop₂ lastAliveSet').deleteEdges
              {symEdgeAt edges₂ ⟨last_g', hg_lt⟩} := by
        rw [hal_erase]
        exact graphOfAlive_erase_eq_deleteEdges hedges₂ lastAliveSet' ⟨last_g', hg_lt⟩
      have hne_H1 : graphOfAlive edges₂ hloop₂ aliveSet' ≠ G.toSimpleGraph := by
        intro heq
        have hg_in_H1 : symEdgeAt edges₂ ⟨last_g', hg_lt⟩ ∈ G.toSimpleGraph.edgeSet :=
          hG6_le (SimpleGraph.mem_edgeFinset.mp hg_mem)
        rw [← heq, herase_eq, SimpleGraph.edgeSet_deleteEdges] at hg_in_H1
        exact hg_in_H1.2 (Set.mem_singleton _)
      apply isAlg33HighWidthCase_liftSimpleSubgraph ω G
        (graphOfAlive edges₂ hloop₂ aliveSet')
        (graphOfAlive edges₂ hloop₂ lastAliveSet') g_cert Z_step6' hsub_H1 hne_H1
      right; right
      rw [hg_eq]
      refine ⟨hG6_le, by convert hg_mem, hZ_card, ?_, herase_eq, hno_sep⟩
      rw [herase_eq]
  · have h := (State.applyShifted_regs_add' a_sub r_sub s s_u3 0).trans hr0_3
    rwa [Nat.add_zero] at h
  · exact (State.applyShifted_regs_add' a_sub r_sub s s_u3 2).trans (hr2_3.trans hlen_e2)
  · exact (State.applyShifted_regs_add' a_sub r_sub s s_u3 4).trans hr4_3
  · exact (State.applyShifted_regs_add' a_sub r_sub s s_u3 5).trans hr5_3

/-- Step constant for `alg33CoreProg ω` in terms of `(n + 1) ^ 2`. -/
def alg33CoreStepConst (ω : ℕ) : ℕ :=
  let B_fac := 3 * ω
  let K_iter := iterStepMax ω 1 1 + 50
  500 * B_fac + 10 * B_fac * K_iter * B_fac + 500

theorem alg33Core_time_le {n ω m₂ t₀ : ℕ} (hω : 2 ≤ ω)
    (hm₂_leB : m₂ ≤ maxEdgesH2 ω n) (ht₀_le : t₀ ≤ 2 * m₂) :
    (45 * m₂ + n + 60) +
      ((22 * m₂ + 20 * t₀ + 21) +
       (3 + (m₂ - 1) * (iterStepMax ω n m₂ + 30 * m₂ + 12))) ≤
      alg33CoreStepConst ω * (n + 1) ^ 2 := by
  let B_fac := 3 * ω
  let K_iter := iterStepMax ω 1 1 + 50
  have hK_pos : 1 ≤ K_iter := by dsimp [K_iter, iterStepMax]; omega
  have hm₂_le_lin : m₂ ≤ B_fac * (n + 1) := by
    have hmax : maxEdgesH2 ω n ≤ B_fac * (n + 1) := by
      unfold maxEdgesH2
      have h1 : (3 * ω - 2) * n = 3 * ω * n - 2 * n := Nat.sub_mul (3 * ω) 2 n
      have h2 : 2 * n ≤ 3 * ω * n := Nat.mul_le_mul_right n (by omega)
      dsimp [B_fac]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact hm₂_leB.trans hmax
  let S := (n + 1) ^ 2
  have hS_eq : S = (n + 1) * (n + 1) := Nat.pow_two (n + 1)
  have hS_expand : S = n * n + 2 * n + 1 := by
    rw [hS_eq, Nat.add_mul, Nat.mul_add]
    omega
  have h1_S : 1 ≤ S := by omega
  have hn_S : n ≤ S := by omega
  have hn1_S : n + 1 ≤ S := by omega
  have hm₂_BS : m₂ ≤ B_fac * S :=
    hm₂_le_lin.trans (Nat.mul_le_mul_left B_fac hn1_S)
  have hB_pos : 1 ≤ B_fac := by dsimp [B_fac]; omega
  have h1_BS : 1 ≤ B_fac * S := by
    calc 1 = 1 * 1 := rfl
      _ ≤ B_fac * S := Nat.mul_le_mul hB_pos h1_S
  have hiter_le : iterStepMax ω n m₂ + 30 * m₂ + 12 ≤ K_iter * (B_fac * (n + 1)) := by
    have hn_X : n ≤ B_fac * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      have : 1 * n ≤ B_fac * n := Nat.mul_le_mul_right n hB_pos
      omega
    have hm_X : m₂ ≤ B_fac * (n + 1) := hm₂_le_lin
    have h1_X : 1 ≤ B_fac * (n + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact iterStepMax_le_mul ω n m₂ (B_fac * (n + 1)) hn_X hm_X h1_X
  have hloop_le : (m₂ - 1) * (iterStepMax ω n m₂ + 30 * m₂ + 12) ≤
      B_fac * K_iter * (B_fac * S) := by
    have hm₂_le' : m₂ - 1 ≤ B_fac * (n + 1) := by omega
    have hmul := Nat.mul_le_mul hm₂_le' hiter_le
    have hrhs : (B_fac * (n + 1)) * (K_iter * (B_fac * (n + 1))) =
        B_fac * K_iter * (B_fac * S) := by
      dsimp [S]
      rw [Nat.pow_two]
      ac_rfl
    omega
  have hB_ge6 : 6 ≤ B_fac := by dsimp [B_fac]; omega
  have hBS_le_BB : B_fac * S ≤ B_fac * (B_fac * S) := by
    calc B_fac * S = 1 * (B_fac * S) := (Nat.one_mul _).symm
      _ ≤ B_fac * (B_fac * S) := Nat.mul_le_mul_right _ hB_pos
  have hK_le : B_fac * (B_fac * S) ≤ B_fac * K_iter * (B_fac * S) := by
    have : B_fac ≤ B_fac * K_iter := by
      calc B_fac = B_fac * 1 := (Nat.mul_one _).symm
        _ ≤ B_fac * K_iter := Nat.mul_le_mul_left B_fac hK_pos
    exact Nat.mul_le_mul_right (B_fac * S) this
  have hC_expand : alg33CoreStepConst ω * S =
      500 * (B_fac * S) + 10 * (B_fac * K_iter * (B_fac * S)) + 500 * S := by
    dsimp [alg33CoreStepConst, B_fac, K_iter]
    rw [Nat.add_mul, Nat.add_mul]
    ac_rfl
  change _ ≤ alg33CoreStepConst ω * S
  omega

/-! ### Section 3: Summing Edge Multiplicities and Serializing `bdCode` -/

/-- Loop body of `sumEdgeMultProg`: reads the multiplicity word `a_G[2 + 3 * k + 2]` and adds it
to `r_base + 2`. -/
def sumEdgeMultBody (a_G : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 4)
    (.op .add (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3)))) (.const 2)))
    (.seq (.assign (r_base + 5) (.read a_G (.reg (r_base + 4))))
      (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 5)))))

/-- Compute `n = a_G[0]`, `m' = a_G[1] = G.numActivePairs`, and `m = G.numEdges` into registers
`r_base`, `r_base + 1`, and `r_base + 2` in `O(m' + 1)` steps. -/
def sumEdgeMultProg (a_G : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_G (.const 0)))
    (.seq (.assign (r_base + 1) (.read a_G (.const 1)))
      (.seq (.assign (r_base + 2) (.const 0))
        (.seq (.assign (r_base + 3) (.const 0))
          (forUp (r_base + 3) (.reg (r_base + 1)) (sumEdgeMultBody a_G r_base)))))

theorem sumEdgeMultLoop_exec {w n : ℕ} (G : MultiDigraph n)
    (a_G : ℕ) (r_base : ℕ)
    (hw3 : 3 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    (suff : List (Fin n × Fin n)) :
    ∀ (pref : List (Fin n × Fin n)),
      G.activePairsList = pref ++ suff →
      ∀ (m_acc : ℕ),
        m_acc + MultiDigraph.sumEdgeMult G suff = G.numEdges →
        ∀ {s : State},
          s.arrs a_G = G.enc →
          s.regs r_base = n →
          s.regs (r_base + 1) = G.numActivePairs →
          s.regs (r_base + 2) = m_acc →
          s.regs (r_base + 3) = pref.length →
          ∃ s' t,
            Exec w (forUp (r_base + 3) (.reg (r_base + 1)) (sumEdgeMultBody a_G r_base)) s s' t ∧
            t ≤ 3 + 22 * suff.length ∧
            s'.regs r_base = n ∧
            s'.regs (r_base + 1) = G.numActivePairs ∧
            s'.regs (r_base + 2) = G.numEdges ∧
            (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff with
  | nil =>
    intro pref hsplit m_acc hm_acc s hsrc hr0 hr1 hr2 hr3
    have hlen_pref : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 1))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr1, hlen_pref, hm'_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by simp, hr0, hr1, ?_, fun _ => rfl, fun _ _ => rfl⟩
    simp only [MultiDigraph.sumEdgeMult, Nat.add_zero] at hm_acc
    rw [hr2, hm_acc]
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    intro pref hsplit m_acc hm_acc s hsrc hr0 hr1 hr2 hr3
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have h3k_w : 3 * k < 2 ^ w := by omega
    have hidx0_w : 2 + 3 * k < 2 ^ w := by omega
    have hidx_w : 2 + 3 * k + 2 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 1))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr1, k, hk_m', hk_w, hm'_w, hw]
    let s₁ := s.setReg (r_base + 4) (2 + 3 * k + 2)
    have hex₁ : Exec w (.assign (r_base + 4)
        (.op .add (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3)))) (.const 2)))
        s s₁ 8 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, k,
        hw2, hw3, hk_w, h3k_w, hidx0_w, hidx_w])
    have hsrc' : s.arrs a_G = G.enc ++ [] := by simp [hsrc]
    obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G [] hsrc' hk_lt
    rw [hget_k] at hget_m
    let mult := G.edgeMult u v
    change 2 + 3 * k + 2 < (s.arrs a_G).length at hlen_m
    change (s.arrs a_G)[2 + 3 * k + 2]'hlen_m = mult at hget_m
    have hsum_cons : m_acc + (mult + MultiDigraph.sumEdgeMult G ps) = G.numEdges := hm_acc
    have hmult_w : mult < 2 ^ w := by omega
    have hm_acc_w : m_acc < 2 ^ w := by omega
    have hm_next_w : m_acc + mult < 2 ^ w := by omega
    let s₂ := s₁.setReg (r_base + 5) mult
    have hex₂ : Exec w (.assign (r_base + 5) (.read a_G (.reg (r_base + 4)))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hidx_w, hlen_m, hget_m, mult, hmult_w])
    let s₃ := s₂.setReg (r_base + 2) (m_acc + mult)
    have hex₃ : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 5))))
        s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2,
        hm_acc_w, hmult_w, hm_next_w])
    let s₄ := s₃.setReg (r_base + 3) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
        s₃ s₄ 4 :=
      .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, k,
        hk_w, hw, show k + 1 < 2 ^ w by omega])
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    rcases ih (pref ++ [(u, v)]) hsplit' (m_acc + mult) (by omega) (s := s₄)
        (by simp [s₄, s₃, s₂, s₁, hsrc])
        (by simp [s₄, s₃, s₂, s₁, hr0])
        (by simp [s₄, s₃, s₂, s₁, hr1])
        (by simp [s₄, s₃])
        (by simp [s₄, k]) with
      ⟨s₅, t₅, hex₅, ht₅, hr0_5, hr1_5, hr2_5, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((8 + (3 + 4)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex₃)) hex_inc) hex₅,
      by simp only [List.length_cons]; omega,
      hr0_5, hr1_5, hr2_5, harr₅,
      fun r hr => by
        rw [hreg₅ r hr]
        simp [s₄, s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ r_base + 3 by omega,
          show (r : Reg) ≠ r_base + 2 by omega,
          show (r : Reg) ≠ r_base + 5 by omega,
          show (r : Reg) ≠ r_base + 4 by omega]⟩

theorem sumEdgeMultProg_exec {w n : ℕ} (G : MultiDigraph n)
    (a_G : ℕ) (r_base : ℕ)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_G = G.enc) :
    ∃ s' t,
      Exec w (sumEdgeMultProg a_G r_base) s s' t ∧
      t ≤ 22 * G.numActivePairs + 15 ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = G.numActivePairs ∧
      s'.regs (r_base + 2) = G.numEdges ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have hsrc' : s.arrs a_G = G.enc ++ [] := by simp [hsrc]
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G [] hsrc'
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_G (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G [] hsrc'
  let s₂ := s₁.setReg (r_base + 1) G.numActivePairs
  have hex₂ : Exec w (.assign (r_base + 1) (.read a_G (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  let s₃ := s₂.setReg (r_base + 2) 0
  have hex₃ : Exec w (.assign (r_base + 2) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_base + 3) 0
  have hex₄ : Exec w (.assign (r_base + 3) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hsum₀ : 0 + MultiDigraph.sumEdgeMult G G.activePairsList = G.numEdges := by
    rw [Nat.zero_add, MultiDigraph.sumEdgeMult_activePairsList]
  rcases sumEdgeMultLoop_exec G a_G r_base hw3 hm3_w hm_w G.activePairsList [] rfl 0 hsum₀
      (s := s₄)
      (by simp [s₄, s₃, s₂, s₁, hsrc])
      (by simp [s₄, s₃, s₂, s₁])
      (by simp [s₄, s₃, s₂])
      (by simp [s₄, s₃])
      (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hr0_5, hr1_5, hr2_5, harr₅, hreg₅⟩
  have hlen_apl : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_apl] at ht₅
  refine ⟨s₅, 3 + (3 + (2 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hr0_5, hr1_5, hr2_5, harr₅,
    fun r hr => by
      rw [hreg₅ r hr]
      simp [s₄, s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base + 3 by omega,
        show (r : Reg) ≠ r_base + 2 by omega,
        show (r : Reg) ≠ r_base + 1 by omega,
        show (r : Reg) ≠ r_base by omega]⟩

/-- Loop body of `appendArrToDstProg`: writes `a_src[r_base]` to `a_dst[r_base + 1]` and increments
`r_base + 1`. -/
def appendArrToDstBody (a_src a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.write a_dst (.reg (r_base + 1)) (.read a_src (.reg r_base)))
    (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))

/-- Append `a_src[0 .. r_len)` into `a_dst[r_base + 1 .. r_base + 1 + r_len)` using loop index
`r_base`. -/
def appendArrToDstProg (a_src a_dst : Arr) (r_len r_base : Reg) : Cmd :=
  .seq (.assign r_base (.const 0))
    (forUp r_base (.reg r_len) (appendArrToDstBody a_src a_dst r_base))

theorem appendArrToDstLoop_exec {w len rem_out : ℕ} (a_src a_dst : Arr) (r_len r_base : Reg)
    (hne_dst : a_src ≠ a_dst) (hr_len : r_len < r_base)
    (pre mid : List ℕ) (hmid : mid.length = len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hout_w : pre.length + len + rem_out < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = len) {s : State}
    (hsrc : (s.arrs a_src).take len = mid)
    (hdst : s.arrs a_dst = pre ++ mid.take k ++ List.replicate (rem + rem_out) 0)
    (hrlen_val : s.regs r_len = len)
    (hr_k : s.regs r_base = k)
    (hr_pos : s.regs (r_base + 1) = pre.length + k) :
    ∃ s' t_copy,
      Exec w (forUp r_base (.reg r_len) (appendArrToDstBody a_src a_dst r_base)) s s' t_copy ∧
      t_copy ≤ 3 + 15 * rem ∧
      s'.arrs a_dst = (pre ++ mid) ++ List.replicate rem_out 0 ∧
      s'.regs (r_base + 1) = (pre ++ mid).length ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : len < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = len := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_k, hrlen_val, hlen_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · have htake : mid.take k = mid := List.take_of_length_le (by omega)
      simpa [htake] using hdst
    · rw [List.length_append, hmid]
      exact hr_pos
  | succ rem ih =>
    have hk_lt : k < len := by omega
    have hk_w : k < 2 ^ w := by omega
    have hpos_w : pre.length + k < 2 ^ w := by omega
    have hpos1_w : pre.length + k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_k, hrlen_val, hk_w, hlen_w, hk_lt, hw]
    have hk_mid : k < mid.length := by omega
    let val := mid[k]'hk_mid
    have hval_w : val < 2 ^ w := hmid_w val (List.getElem_mem hk_mid)
    have hsrc_len : k < (s.arrs a_src).length := by
      have : ((s.arrs a_src).take len).length = len := by rw [hsrc, hmid]
      rw [List.length_take] at this
      omega
    have hsrc_get : (s.arrs a_src)[k]'hsrc_len = val := by
      have h1 : ((s.arrs a_src).take len)[k]'(by rw [hsrc, hmid]; exact hk_lt) = val := by
        simp only [hsrc]; rfl
      rw [List.getElem_take] at h1
      exact h1
    have hdst_len : pre.length + k < (s.arrs a_dst).length := by
      rw [hdst, List.length_append, List.length_append, List.length_take, List.length_replicate]
      omega
    let s₁ := s.writeArr a_dst (pre.length + k) val
    have hex₁ : Exec w (.write a_dst (.reg (r_base + 1)) (.read a_src (.reg r_base))) s s₁ 4 :=
      .write (by simp [Expr.eval, checkWord, hr_pos, hpos_w])
        (by simp [Expr.eval, checkWord, hr_k, hk_w, hsrc_len, hsrc_get, hval_w])
        hdst_len
    let s₂ := s₁.setReg (r_base + 1) (pre.length + k + 1)
    have hex₂ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_pos, hpos_w, hw, hpos1_w])
    let s₃ := s₂.setReg r_base (k + 1)
    have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr_k, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have hdst₃ : s₃.arrs a_dst = pre ++ mid.take (k + 1) ++ List.replicate (rem + rem_out) 0 := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hdst, List.append_assoc]
      have hlen_take : (mid.take k).length = k := by rw [List.length_take]; omega
      rw [List.set_append_right _ _ (by omega)]
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : pre.length + k - pre.length - (mid.take k).length = 0 := by omega
      have hrep : rem + 1 + rem_out = (rem + rem_out) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      rw [take_add_one_eq_append_getElem mid k hk_mid, List.append_assoc, List.singleton_append]
    rcases ih (k + 1) (by omega) (s := s₃)
        (by simp [s₃, s₂, s₁, hne_dst, hsrc])
        hdst₃
        (by
          dsimp [Reg] at hr_len
          simp [s₃, s₂, s₁, State.setReg,
            show (r_len : Reg) ≠ r_base by dsimp [Reg]; omega,
            show (r_len : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrlen_val])
        (by simp [s₃])
        (by simp [s₃, s₂]; omega) with
      ⟨s₄, t₄, hex₄, ht₄, hdst₄, hrpos_4, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((4 + 4) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hdst₄, hrpos_4,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r hr => by
        dsimp [Reg] at hr
        rw [hreg₄ r hr]
        simp [s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ r_base by dsimp [Reg]; omega,
          show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega]⟩

theorem appendArrToDstProg_exec {w len rem_out : ℕ} (a_src a_dst : Arr) (r_len r_base : Reg)
    (hne_dst : a_src ≠ a_dst) (hr_len : r_len < r_base)
    (pre mid : List ℕ) (hmid : mid.length = len)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hout_w : pre.length + len + rem_out < 2 ^ w)
    {s : State}
    (hsrc : (s.arrs a_src).take len = mid)
    (hdst : s.arrs a_dst = pre ++ List.replicate (len + rem_out) 0)
    (hrlen_val : s.regs r_len = len)
    (hr_pos : s.regs (r_base + 1) = pre.length) :
    ∃ s' t_copy,
      Exec w (appendArrToDstProg a_src a_dst r_len r_base) s s' t_copy ∧
      t_copy ≤ 5 + 15 * len ∧
      s'.arrs a_dst = (pre ++ mid) ++ List.replicate rem_out 0 ∧
      s'.regs (r_base + 1) = (pre ++ mid).length ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_base 0
  have hex₁ : Exec w (.assign r_base (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases appendArrToDstLoop_exec a_src a_dst r_len r_base hne_dst hr_len pre mid hmid hmid_w
      hw hout_w len 0 (by omega) (s := s₁)
      hsrc (by simpa [s₁] using hdst)
      (by
        dsimp [Reg] at hr_len
        simp [s₁, State.setReg, show (r_len : Reg) ≠ r_base by dsimp [Reg]; omega, hrlen_val])
      (by simp [s₁])
      (by simp [s₁, hr_pos]) with
    ⟨s₂, t₂, hex₂, ht₂, hdst₂, hrpos_2, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hdst₂, hrpos_2, harr₂,
    fun r hr => by
      dsimp [Reg] at hr
      rw [hreg₂ r hr]
      simp [s₁, State.setReg, show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

/-- Preamble of `writeBDCodeProg`: sets `a_par[0] := 0`, allocates `a_bd_out` of length `2 + t + m`,
writes `a_bd_out[0] := t` and `a_bd_out[1] := m`, and sets `r_base + 1 := 2`. -/
def initBDCodeOutCmd (a_par a_bd_out : Arr) (r_t r_m r_base : Reg) : Cmd :=
  .seq (.write a_par (.const 0) (.const 0))
    (.seq (.alloc a_bd_out (.op .add (.const 2) (.op .add (.reg r_t) (.reg r_m))))
      (.seq (.write a_bd_out (.const 0) (.reg r_t))
        (.seq (.write a_bd_out (.const 1) (.reg r_m))
          (.assign (r_base + 1) (.const 2)))))

/-- Serialize a branch-decomposition `(parentTree t p, τ)` into `a_bd_out` as
`[t, m] ++ parList ++ tauList`. -/
def writeBDCodeProg (a_par a_tau a_bd_out : Arr) (r_t r_m r_base : Reg) : Cmd :=
  .seq (initBDCodeOutCmd a_par a_bd_out r_t r_m r_base)
    (.seq (appendArrToDstProg a_par a_bd_out r_t r_base)
      (appendArrToDstProg a_tau a_bd_out r_m r_base))

theorem writeBDCodeProg_exec {w n B t : ℕ} (G : MultiDigraph n)
    (p : ℕ → ℕ) (ht_pos : 0 < t) (τ : Fin G.numEdges → Fin t)
    (a_par a_tau a_bd_out : Arr) (r_t r_m r_base : Reg)
    (hne_pb : a_par ≠ a_bd_out) (hne_tb : a_tau ≠ a_bd_out) (hne_pt : a_par ≠ a_tau)
    (hr_t : r_t < r_base) (hr_m : r_m < r_base)
    (hw2 : 2 < 2 ^ w) (hout_w : 2 + t + G.numEdges < 2 ^ w)
    (hm_ge2 : 2 ≤ G.numEdges) (ht_le : t ≤ 2 * G.numEdges)
    (hp : ∀ z, 0 < z → z < t → p z < z)
    (hbd : IsMultiBranchDecompOfWidthLe B G (parentTree t p) τ)
    {s : State}
    (hpar_len : t ≤ (s.arrs a_par).length)
    (hpar_val : ∀ z (hz : z < (s.arrs a_par).length), 0 < z → z < t → (s.arrs a_par)[z]'hz = p z)
    (htau_len : (s.arrs a_tau).length = G.numEdges)
    (htau_val : ∀ e : Fin G.numEdges, (s.arrs a_tau)[e.1]'(by rw [htau_len]; exact e.2) = (τ e).1)
    (hrt : s.regs r_t = t)
    (hrm : s.regs r_m = G.numEdges) :
    ∃ s' t_out,
      Exec w (writeBDCodeProg a_par a_tau a_bd_out r_t r_m r_base) s s' t_out ∧
      t_out ≤ 16 * t + 16 * G.numEdges + 35 ∧
      IsValidBranchDecompCode B G (s'.arrs a_bd_out) ∧
      (∀ a : Arr, a ≠ a_bd_out → a ≠ a_par → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  let m := G.numEdges
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have ht_w : t < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have htm_w : t + m < 2 ^ w := by omega
  have hout_w' : 2 + (t + m) < 2 ^ w := by omega
  have hpar0 : 0 < (s.arrs a_par).length := by omega
  let s_0 := s.writeArr a_par 0 0
  have hex_0 : Exec w (.write a_par (.const 0) (.const 0)) s s_0 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w]) hpar0
  let s_a := s_0.setArr a_bd_out (List.replicate (2 + (t + m)) 0)
  have hex_a : Exec w (.alloc a_bd_out (.op .add (.const 2) (.op .add (.reg r_t) (.reg r_m))))
      s_0 s_a (5 + (2 + (t + m))) :=
    .alloc (by simp [s_0, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hrt, ht_w, hrm, m, hm_w, htm_w, hout_w'])
  let s_b := s_a.writeArr a_bd_out 0 t
  have hex_b : Exec w (.write a_bd_out (.const 0) (.reg r_t)) s_a s_b 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s_a, s_0, Expr.eval, checkWord, hrt, ht_w])
      (by simp [s_a])
  let s_c := s_b.writeArr a_bd_out 1 m
  have hex_c : Exec w (.write a_bd_out (.const 1) (.reg r_m)) s_b s_c 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s_b, s_a, s_0, Expr.eval, checkWord, hrm, m, hm_w])
      (by simp [s_b, s_a]; omega)
  let s₁ := s_c.setReg (r_base + 1) 2
  have hex_d : Exec w (.assign (r_base + 1) (.const 2)) s_c s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  have hex_init : Exec w (initBDCodeOutCmd a_par a_bd_out r_t r_m r_base) s s₁
      (3 + ((5 + (2 + (t + m))) + (3 + (3 + 2)))) :=
    .seq hex_0 (.seq hex_a (.seq hex_b (.seq hex_c hex_d)))
  have hout₁ : s₁.arrs a_bd_out = [t, m] ++ List.replicate (t + m) 0 := by
    simp only [s₁, s_c, s_b, s_a, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self]
    rw [Nat.add_comm 2 (t + m), List.replicate_succ, List.replicate_succ]
    rfl
  have hpar₁_eq : s₁.arrs a_par = (s.arrs a_par).set 0 0 := by
    simp [s₁, s_c, s_b, s_a, s_0, hne_pb]
  let parList := (s₁.arrs a_par).take t
  have hparList_len : parList.length = t := by
    dsimp [parList]
    rw [List.length_take, hpar₁_eq, List.length_set]
    omega
  have hparList_0 : parList[0]'(by rw [hparList_len]; exact ht_pos) = 0 := by
    dsimp [parList]
    rw [List.getElem_take]
    simp [hpar₁_eq]
  have hparList_pos : ∀ z (hz : z < parList.length), 0 < z → parList[z]'hz = p z := by
    intro z hz hz_pos
    have hz_t : z < t := by omega
    dsimp [parList]
    rw [List.getElem_take]
    simp only [hpar₁_eq]
    rw [List.getElem_set_ne (by omega : 0 ≠ z)]
    exact hpar_val z (by omega) hz_pos hz_t
  have hparList_w : ∀ x ∈ parList, x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨z, hz, rfl⟩
    by_cases hz_pos : 0 < z
    · rw [hparList_pos z hz hz_pos]
      have hz_t : z < t := by omega
      have := hp z hz_pos hz_t
      omega
    · have hz0 : z = 0 := by omega
      subst hz0
      rw [hparList_0]; exact h0_w
  let tauList := s.arrs a_tau
  have htauList_w : ∀ x ∈ tauList, x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    have hi_m : i < m := by change i < G.numEdges; rw [← htau_len]; exact hi
    have hval := htau_val ⟨i, hi_m⟩
    dsimp only [tauList]
    rw [hval]
    have := (τ ⟨i, hi_m⟩).2
    omega
  -- 1. appendArrToDstProg a_par a_bd_out r_t r_base
  rcases appendArrToDstProg_exec a_par a_bd_out r_t r_base hne_pb hr_t
      [t, m] parList hparList_len hparList_w hw (rem_out := m) (by simp; omega) (s := s₁)
      rfl hout₁
      (by
        dsimp [Reg] at hr_t
        simp [s₁, s_c, s_b, s_a, s_0, State.setReg,
          show (r_t : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrt])
      (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hrpos_2, harr₂, hreg₂⟩
  -- 2. appendArrToDstProg a_tau a_bd_out r_m r_base
  have htau₂ : s₂.arrs a_tau = tauList := by
    rw [harr₂ a_tau hne_tb]
    simp [s₁, s_c, s_b, s_a, s_0, hne_tb, hne_pt.symm, tauList]
  rcases appendArrToDstProg_exec a_tau a_bd_out r_m r_base hne_tb hr_m
      ([t, m] ++ parList) tauList htau_len htauList_w hw (rem_out := 0)
      (by simp [hparList_len, m]; omega) (s := s₂)
      (by rw [htau₂, List.take_of_length_le (by rw [htau_len])])
      (by rw [Nat.add_zero]; exact hout₂)
      (by
        dsimp [Reg] at hr_m
        rw [hreg₂ r_m hr_m]
        simp [s₁, s_c, s_b, s_a, s_0, State.setReg,
          show (r_m : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrm, m])
      hrpos_2 with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, _, harr₃, hreg₃⟩
  simp only [List.replicate_zero, List.append_nil] at hout₃
  refine ⟨s₃, (3 + ((5 + (2 + (t + m))) + (3 + (3 + 2)))) + (t₂ + t₃),
    .seq hex_init (.seq hex₂ hex₃),
    by omega, ?_,
    fun a ha_bd ha_par => by
      rw [harr₃ a ha_bd, harr₂ a ha_bd]
      simp [s₁, s_c, s_b, s_a, s_0, ha_bd, ha_par],
    fun r hr => by
      dsimp [Reg] at hr
      rw [hreg₃ r hr, hreg₂ r hr]
      simp [s₁, s_c, s_b, s_a, s_0, State.setReg,
        show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega]⟩
  rw [hout₃]
  exact isValidBranchDecompCode_of_ge_two B G parList tauList p τ
    hm_ge2 ht_pos ht_le hparList_len htau_len hparList_0
    (fun z hz_t hz_pos => hparList_pos z (by rw [hparList_len]; exact hz_t) hz_pos)
    hp htau_val hbd

/-- Write the trivial branch-decomposition code `[0, m] ++ List.replicate m 0` into `a_bd_out`
when `m = G.numEdges ≤ 1`. -/
def writeTrivialBDCodeProg (a_bd_out : Arr) (r_m : Reg) : Cmd :=
  .seq (.alloc a_bd_out (.op .add (.const 2) (.reg r_m)))
    (.seq (.write a_bd_out (.const 0) (.const 0))
      (.write a_bd_out (.const 1) (.reg r_m)))

theorem writeTrivialBDCodeProg_exec {w n B : ℕ} (G : MultiDigraph n)
    (a_bd_out : Arr) (r_m : Reg)
    (hw3 : 3 < 2 ^ w) (hm_le1 : G.numEdges ≤ 1)
    {s : State}
    (hrm : s.regs r_m = G.numEdges) :
    ∃ s' t_out,
      Exec w (writeTrivialBDCodeProg a_bd_out r_m) s s' t_out ∧
      t_out ≤ 15 ∧
      IsValidBranchDecompCode B G (s'.arrs a_bd_out) ∧
      (∀ a : Arr, a ≠ a_bd_out → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, s'.regs r = s.regs r) := by
  let m := G.numEdges
  have hm_le1' : m ≤ 1 := hm_le1
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have h2m_w : 2 + m < 2 ^ w := by omega
  let s₁ := s.setArr a_bd_out (List.replicate (2 + m) 0)
  have hex₁ : Exec w (.alloc a_bd_out (.op .add (.const 2) (.reg r_m))) s s₁ (3 + (2 + m)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hrm, m, hm_w, h2m_w])
  let s₂ := s₁.writeArr a_bd_out 0 0
  have hex₂ : Exec w (.write a_bd_out (.const 0) (.const 0)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w]) (by simp [s₁])
  let s₃ := s₂.writeArr a_bd_out 1 m
  have hex₃ : Exec w (.write a_bd_out (.const 1) (.reg r_m)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s₂, s₁, Expr.eval, checkWord, hrm, m, hm_w])
      (by simp [s₂, s₁]; omega)
  have hout₃ : s₃.arrs a_bd_out = [0, m] ++ List.replicate m 0 := by
    simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setArr_arrs_self]
    rw [Nat.add_comm 2 m, List.replicate_succ, List.replicate_succ]
    rfl
  refine ⟨s₃, (3 + (2 + m)) + (3 + 3), .seq hex₁ (.seq hex₂ hex₃), by omega, ?_,
    fun a ha => by simp [s₃, s₂, s₁, ha], fun _ => rfl⟩
  rw [hout₃]
  exact isValidBranchDecompCode_le_one B G hm_le1

/-! ### Section 4: Pass-2 Leaf-Splitting Program (`initPass2AuxProg`, `pass2SplitProg`) -/

/-- Number of edges `e : Fin m` with `e.1 < k` and `σ₀ e = l`. -/
def countBefore {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) (k : ℕ) (l : Fin t₀) : ℕ :=
  (Finset.univ.filter (fun e : Fin m => e.1 < k ∧ σ₀ e = l)).card

theorem countBefore_zero {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) (l : Fin t₀) :
    countBefore σ₀ 0 l = 0 := by
  unfold countBefore
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro e _ ⟨h, _⟩
  omega

theorem countBefore_self {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) (l : Fin t₀) :
    countBefore σ₀ m l = remAfter σ₀ 0 l := by
  unfold countBefore remAfter
  congr 1
  ext e
  simp

theorem countBefore_le {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) (k : ℕ) (l : Fin t₀) :
    countBefore σ₀ k l ≤ m :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem countBefore_step_eq {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) {k : ℕ} (hk : k < m) :
    countBefore σ₀ (k + 1) (σ₀ ⟨k, hk⟩) = countBefore σ₀ k (σ₀ ⟨k, hk⟩) + 1 := by
  unfold countBefore
  let ek : Fin m := ⟨k, hk⟩
  have hnot : ek ∉ Finset.univ.filter (fun e : Fin m => e.1 < k ∧ σ₀ e = σ₀ ek) := by
    simp [ek]
  rw [← Finset.card_insert_of_notMem hnot]
  congr 1
  ext e
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlt, hσ⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | heq
    · exact Or.inr ⟨hlt', hσ⟩
    · exact Or.inl (Fin.ext heq)
  · rintro (rfl | ⟨hlt, hσ⟩)
    · exact ⟨Nat.lt_succ_self k, rfl⟩
    · exact ⟨Nat.lt_succ_of_lt hlt, hσ⟩

theorem countBefore_step_ne {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) {k : ℕ} (hk : k < m)
    {l : Fin t₀} (hne : l ≠ σ₀ ⟨k, hk⟩) :
    countBefore σ₀ (k + 1) l = countBefore σ₀ k l := by
  unfold countBefore
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hlt, hσ⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | heq
    · exact ⟨hlt', hσ⟩
    · exfalso
      have he_eq : e = ⟨k, hk⟩ := Fin.ext heq
      subst he_eq
      exact hne hσ.symm
  · rintro ⟨hlt, hσ⟩
    exact ⟨Nat.lt_succ_of_lt hlt, hσ⟩

/-- Loop body for counting `a_rem[a_sigma[r_base]] += 1`. -/
def countRemBody (a_sigma a_rem : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_sigma (.reg r_base)))
    (.write a_rem (.reg (r_base + 1))
      (.op .add (.read a_rem (.reg (r_base + 1))) (.const 1)))

/-- Initialize `a_par` (length `2 * m`, copying `p₀` on `0 .. t₀ - 1`), `a_cur` (`a_cur[l] = l`),
and `a_rem` (`a_rem[l] = remAfter σ₀ 0 l`) from `a_par0` and `a_sigma`. -/
def initPass2AuxProg (a_par0 a_sigma a_par a_cur a_rem : Arr) (r_m r_t r_base : Reg) : Cmd :=
  .seq (.alloc a_par (.op .mul (.const 2) (.reg r_m)))
    (.seq (.assign (r_base + 1) (.const 0))
      (.seq (appendArrToDstProg a_par0 a_par r_t r_base)
        (.seq (.alloc a_cur (.reg r_t))
          (.seq (.assign r_base (.const 0))
            (.seq (forUp r_base (.reg r_t) (.write a_cur (.reg r_base) (.reg r_base)))
              (.seq (.alloc a_rem (.reg r_t))
                (.seq (.assign r_base (.const 0))
                  (forUp r_base (.reg r_m) (countRemBody a_sigma a_rem r_base)))))))))

theorem initCurLoop_exec {w t₀ : ℕ} (a_cur : Arr) (r_t r_base : Reg)
    (hr_t : r_t < r_base) (hw : 1 < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = t₀) {s : State}
    (hcur_len : (s.arrs a_cur).length = t₀)
    (hcur_val : ∀ l < k, (hl : l < (s.arrs a_cur).length) → (s.arrs a_cur)[l]'hl = l)
    (hrt : s.regs r_t = t₀)
    (hrk : s.regs r_base = k) :
    ∃ s' t_loop,
      Exec w (forUp r_base (.reg r_t) (.write a_cur (.reg r_base) (.reg r_base))) s s' t_loop ∧
      t_loop ≤ 3 + 10 * rem ∧
      (s'.arrs a_cur).length = t₀ ∧
      (∀ l : Fin t₀, (hl : l.1 < (s'.arrs a_cur).length) → (s'.arrs a_cur)[l.1]'hl = l.1) ∧
      (∀ a : Arr, a ≠ a_cur → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = t₀ := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_t)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrt, ht₀_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hcur_len,
      fun l hl => hcur_val l.1 l.2 hl,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < t₀ := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_t)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrt, hk_w, ht₀_w, hk_lt, hw]
    let s₁ := s.writeArr a_cur k k
    have hex₁ : Exec w (.write a_cur (.reg r_base) (.reg r_base)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hrk, hk_w])
        (by simp [Expr.eval, checkWord, hrk, hk_w])
        (by rw [hcur_len]; exact hk_lt)
    let s₂ := s₁.setReg r_base (k + 1)
    have hex₂ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrk, hk_w, hw, show k + 1 < 2 ^ w by omega])
    rcases ih (k + 1) (by omega) (s := s₂)
        (by simp [s₂, s₁, hcur_len])
        (fun l hl hl_len => by
          simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self] at hl_len ⊢
          by_cases hlk : l = k
          · subst hlk; exact List.getElem_set_self hl_len
          · rw [List.getElem_set_ne (by omega)]
            exact hcur_val l (by omega) (by rw [List.length_set] at hl_len; exact hl_len))
        (by
          dsimp [Reg] at hr_t
          simp [s₂, s₁, State.setReg, show (r_t : Reg) ≠ r_base by dsimp [Reg]; omega, hrt])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hlen₃, hval₃, harr₃, hreg₃⟩
    refine ⟨s₃, 3 + (3 + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃,
      by omega, hlen₃, hval₃,
      fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
      fun r hr => by
        dsimp [Reg] at hr
        rw [hreg₃ r hr]
        simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

theorem countRemLoop_exec {w m t₀ : ℕ} (σ₀ : Fin m → Fin t₀)
    (a_sigma a_rem : Arr) (r_m r_base : Reg)
    (hne_sr : a_sigma ≠ a_rem) (hr_m : r_m < r_base)
    (hw : 1 < 2 ^ w) (hm_w : m < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = m) {s : State}
    (hsig_len : (s.arrs a_sigma).length = m)
    (hsig_val : ∀ e : Fin m, (s.arrs a_sigma)[e.1]'(by rw [hsig_len]; exact e.2) = (σ₀ e).1)
    (hrem_len : (s.arrs a_rem).length = t₀)
    (hrem_val : ∀ l : Fin t₀,
      (s.arrs a_rem)[l.1]'(by rw [hrem_len]; exact l.2) = countBefore σ₀ k l)
    (hrm : s.regs r_m = m)
    (hrk : s.regs r_base = k) :
    ∃ s' t_loop,
      Exec w (forUp r_base (.reg r_m) (countRemBody a_sigma a_rem r_base)) s s' t_loop ∧
      t_loop ≤ 3 + 17 * rem ∧
      (s'.arrs a_rem).length = t₀ ∧
      (∀ l : Fin t₀, (hl : l.1 < (s'.arrs a_rem).length) →
        (s'.arrs a_rem)[l.1]'hl = remAfter σ₀ 0 l) ∧
      (∀ a : Arr, a ≠ a_rem → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = m := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hm_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hrem_len,
      fun l _ => by rw [hrem_val l, countBefore_self],
      fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < m := by omega
    have hk_w : k < 2 ^ w := by omega
    let ek : Fin m := ⟨k, hk_lt⟩
    let l₀ : Fin t₀ := σ₀ ek
    have hl₀_w : l₀.1 < 2 ^ w := by have := l₀.2; omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hk_w, hm_w, hk_lt, hw]
    have hsig_k : (s.arrs a_sigma)[k]'(by rw [hsig_len]; exact hk_lt) = l₀.1 := hsig_val ek
    let s₁ := s.setReg (r_base + 1) l₀.1
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_sigma (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrk, hk_w, hsig_len, hk_lt, hsig_k, hl₀_w])
    let c₀ := countBefore σ₀ k l₀
    have hc₀_step : countBefore σ₀ (k + 1) l₀ = c₀ + 1 := countBefore_step_eq σ₀ hk_lt
    have hc1_le : c₀ + 1 ≤ m := by rw [← hc₀_step]; exact countBefore_le σ₀ (k + 1) l₀
    have hc₀_w : c₀ < 2 ^ w := by omega
    have hc1_w : c₀ + 1 < 2 ^ w := by omega
    have hrem_l₀ : (s.arrs a_rem)[l₀.1]'(by rw [hrem_len]; exact l₀.2) = c₀ := hrem_val l₀
    let s₂ := s₁.writeArr a_rem l₀.1 (c₀ + 1)
    have hex₂ : Exec w (.write a_rem (.reg (r_base + 1))
        (.op .add (.read a_rem (.reg (r_base + 1))) (.const 1))) s₁ s₂ 6 :=
      .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hl₀_w])
        (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hl₀_w, hrem_len, l₀.2, hrem_l₀, hc₀_w, hw, hc1_w])
        (by simp [s₁, hrem_len, l₀.2])
    let s₃ := s₂.setReg r_base (k + 1)
    have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrk, hk_w, hw, show k + 1 < 2 ^ w by omega])
    rcases ih (k + 1) (by omega) (s := s₃)
        (by simp [s₃, s₂, s₁, hne_sr, hsig_len])
        (fun e => by simpa [s₃, s₂, s₁, hne_sr] using hsig_val e)
        (by simp [s₃, s₂, s₁, hrem_len])
        (fun l => by
          simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
          by_cases hl : l = l₀
          · subst hl
            rw [List.getElem_set_self (by rw [List.length_set, hrem_len]; exact l₀.2), hc₀_step]
          · have hne_val : l₀.1 ≠ l.1 := fun h => hl (Fin.ext h.symm)
            rw [List.getElem_set_ne hne_val, hrem_val l, countBefore_step_ne σ₀ hk_lt hl])
        (by
          dsimp [Reg] at hr_m
          simp [s₃, s₂, s₁, State.setReg,
            show (r_m : Reg) ≠ r_base by dsimp [Reg]; omega,
            show (r_m : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrm])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hlen₄, hval₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 6) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hlen₄, hval₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r hr => by
        dsimp [Reg] at hr
        rw [hreg₄ r hr]
        simp [s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ r_base by dsimp [Reg]; omega,
          show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega]⟩

theorem initPass2AuxProg_exec {w m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) (p₀ : ℕ → ℕ)
    (a_par0 a_sigma a_par a_cur a_rem : Arr) (r_m r_t r_base : Reg)
    (hne_p0_p : a_par0 ≠ a_par)
    (hne_sig_p : a_sigma ≠ a_par) (hne_sig_c : a_sigma ≠ a_cur) (hne_sig_r : a_sigma ≠ a_rem)
    (hne_pc : a_par ≠ a_cur) (hne_pr : a_par ≠ a_rem) (hne_cr : a_cur ≠ a_rem)
    (hr_m : r_m < r_base) (hr_t : r_t < r_base)
    (hw2 : 2 < 2 ^ w) (h2m_w : 2 * m < 2 ^ w)
    (ht₀_le : t₀ ≤ 2 * m) (hp₀ : ∀ z, 0 < z → z < t₀ → p₀ z < z) (hp₀_0 : p₀ 0 = 0)
    {s : State}
    (hpar0_len : t₀ ≤ (s.arrs a_par0).length)
    (hpar0_val : ∀ z (hz : z < (s.arrs a_par0).length), z < t₀ → (s.arrs a_par0)[z]'hz = p₀ z)
    (hsig_len : (s.arrs a_sigma).length = m)
    (hsig_val : ∀ e : Fin m, (s.arrs a_sigma)[e.1]'(by rw [hsig_len]; exact e.2) = (σ₀ e).1)
    (hrm : s.regs r_m = m)
    (hrt : s.regs r_t = t₀) :
    ∃ s' t_init,
      Exec w (initPass2AuxProg a_par0 a_sigma a_par a_cur a_rem r_m r_t r_base) s s' t_init ∧
      t_init ≤ 27 * t₀ + 20 * m + 30 ∧
      (s'.arrs a_par).length = 2 * m ∧
      (∀ z < t₀, (hz : z < (s'.arrs a_par).length) → (s'.arrs a_par)[z]'hz = p₀ z) ∧
      (s'.arrs a_cur).length = t₀ ∧
      (∀ l : Fin t₀, (hl : l.1 < (s'.arrs a_cur).length) → (s'.arrs a_cur)[l.1]'hl = l.1) ∧
      (s'.arrs a_rem).length = t₀ ∧
      (∀ l : Fin t₀, (hl : l.1 < (s'.arrs a_rem).length) →
        (s'.arrs a_rem)[l.1]'hl = remAfter σ₀ 0 l) ∧
      (∀ a : Arr, a ≠ a_par → a ≠ a_cur → a ≠ a_rem → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have ht₀_w : t₀ < 2 ^ w := by omega
  -- 1. alloc a_par (2 * r_m), r_base + 1 := 0, appendArrToDstProg a_par0 a_par r_t r_base
  let s₁ := s.setArr a_par (List.replicate (2 * m) 0)
  have hex₁ : Exec w (.alloc a_par (.op .mul (.const 2) (.reg r_m))) s s₁ (3 + 2 * m) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hrm, hm_w, h2m_w])
  let s₂ := s₁.setReg (r_base + 1) 0
  have hex₂ : Exec w (.assign (r_base + 1) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let mid_p0 := (s.arrs a_par0).take t₀
  have hmid_len : mid_p0.length = t₀ := by
    dsimp [mid_p0]; rw [List.length_take]; omega
  have hmid_w : ∀ x ∈ mid_p0, x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨z, hz, rfl⟩
    have hz_t : z < t₀ := by omega
    dsimp [mid_p0]
    rw [List.getElem_take, hpar0_val z (by omega) hz_t]
    by_cases hz_pos : 0 < z
    · have := hp₀ z hz_pos hz_t; omega
    · have hz0 : z = 0 := by omega
      subst hz0; rw [hp₀_0]; exact h0_w
  rcases appendArrToDstProg_exec a_par0 a_par r_t r_base hne_p0_p hr_t
      [] mid_p0 hmid_len hmid_w hw (rem_out := 2 * m - t₀) (by simp; omega) (s := s₂)
      (by simp [s₂, s₁, hne_p0_p, mid_p0])
      (by
        simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, List.nil_append]
        congr 1; omega)
      (by
        dsimp [Reg] at hr_t
        simp [s₂, s₁, State.setReg, show (r_t : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrt])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hpar₃, _, harr₃, hreg₃⟩
  have hpar₃_len : (s₃.arrs a_par).length = 2 * m := by
    rw [hpar₃, List.nil_append, List.length_append, hmid_len, List.length_replicate]; omega
  have hpar₃_val : ∀ z (hz : z < t₀), (s₃.arrs a_par)[z]'(by rw [hpar₃_len]; omega) = p₀ z := by
    intro z hz
    simp only [hpar₃, List.nil_append]
    rw [List.getElem_append_left (by rw [hmid_len]; exact hz)]
    dsimp [mid_p0]
    rw [List.getElem_take]
    exact hpar0_val z (by omega) hz
  -- 2. alloc a_cur r_t, r_base := 0, initCurLoop_exec
  have hrt₃ : s₃.regs r_t = t₀ := by
    dsimp [Reg] at hr_t
    rw [hreg₃ r_t hr_t]
    simp [s₂, s₁, State.setReg, show (r_t : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrt]
  let s₄ := s₃.setArr a_cur (List.replicate t₀ 0)
  have hex₄ : Exec w (.alloc a_cur (.reg r_t)) s₃ s₄ (1 + t₀) :=
    .alloc (by simp [Expr.eval, checkWord, hrt₃, ht₀_w])
  let s₅ := s₄.setReg r_base 0
  have hex₅ : Exec w (.assign r_base (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases initCurLoop_exec a_cur r_t r_base hr_t hw ht₀_w t₀ 0 (by omega) (s := s₅)
      (by simp [s₅, s₄])
      (fun _ hl _ => by omega)
      (by
        dsimp [Reg] at hr_t
        simp [s₅, s₄, State.setReg, show (r_t : Reg) ≠ r_base by dsimp [Reg]; omega, hrt₃])
      (by simp [s₅]) with
    ⟨s₆, t₆, hex₆, ht₆, hcur₆_len, hcur₆_val, harr₆, hreg₆⟩
  -- 3. alloc a_rem r_t, r_base := 0, countRemLoop_exec
  have hrt₆ : s₆.regs r_t = t₀ := by
    dsimp [Reg] at hr_t
    rw [hreg₆ r_t hr_t]
    simp [s₅, s₄, State.setReg, show (r_t : Reg) ≠ r_base by dsimp [Reg]; omega, hrt₃]
  have hrm₆ : s₆.regs r_m = m := by
    dsimp [Reg] at hr_m
    rw [hreg₆ r_m hr_m]
    simp only [s₅, s₄, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_m : Reg) ≠ r_base),
      State.setArr_regs]
    rw [hreg₃ r_m hr_m]
    simp [s₂, s₁, State.setReg, show (r_m : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrm]
  let s₇ := s₆.setArr a_rem (List.replicate t₀ 0)
  have hex₇ : Exec w (.alloc a_rem (.reg r_t)) s₆ s₇ (1 + t₀) :=
    .alloc (by simp [Expr.eval, checkWord, hrt₆, ht₀_w])
  let s₈ := s₇.setReg r_base 0
  have hex₈ : Exec w (.assign r_base (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hsig₈ : s₈.arrs a_sigma = s.arrs a_sigma := by
    simp only [s₈, s₇, State.setReg_arrs, State.setArr_arrs_ne _ _ hne_sig_r]
    rw [harr₆ a_sigma hne_sig_c]
    simp only [s₅, s₄, State.setReg_arrs, State.setArr_arrs_ne _ _ hne_sig_c]
    rw [harr₃ a_sigma hne_sig_p]
    simp [s₂, s₁, hne_sig_p]
  rcases countRemLoop_exec σ₀ a_sigma a_rem r_m r_base hne_sig_r hr_m hw hm_w ht₀_w m 0 (by omega)
      (s := s₈)
      (by rw [hsig₈, hsig_len])
      (fun e => by simp only [hsig₈]; exact hsig_val e)
      (by simp [s₈, s₇])
      (fun l => by simp [s₈, s₇, countBefore_zero])
      (by
        dsimp [Reg] at hr_m
        simp [s₈, s₇, State.setReg, show (r_m : Reg) ≠ r_base by dsimp [Reg]; omega, hrm₆])
      (by simp [s₈]) with
    ⟨s₉, t₉, hex₉, ht₉, hrem₉_len, hrem₉_val, harr₉, hreg₉⟩
  have hpar₉ : s₉.arrs a_par = s₃.arrs a_par := by
    rw [harr₉ a_par hne_pr]
    simp only [s₈, s₇, State.setReg_arrs, State.setArr_arrs_ne _ _ hne_pr]
    rw [harr₆ a_par hne_pc]
    simp [s₅, s₄, hne_pc]
  have hcur₉ : s₉.arrs a_cur = s₆.arrs a_cur := by
    rw [harr₉ a_cur hne_cr]
    simp [s₈, s₇, hne_cr]
  refine ⟨s₉,
    (3 + 2 * m) + (2 + (t₃ + ((1 + t₀) + (2 + (t₆ + ((1 + t₀) + (2 + t₉))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉))))))),
    by omega,
    by rw [hpar₉, hpar₃_len],
    fun z hz _ => by simp only [hpar₉]; exact hpar₃_val z hz,
    by rw [hcur₉, hcur₆_len],
    fun l hl => by simp only [hcur₉] at hl ⊢; exact hcur₆_val l hl,
    hrem₉_len,
    hrem₉_val,
    fun a hap hac har => by
      rw [harr₉ a har]
      simp only [s₈, s₇, State.setReg_arrs, State.setArr_arrs_ne _ _ har]
      rw [harr₆ a hac]
      simp only [s₅, s₄, State.setReg_arrs, State.setArr_arrs_ne _ _ hac]
      rw [harr₃ a hap]
      simp [s₂, s₁, hap],
    fun r hr => by
      dsimp [Reg] at hr
      rw [hreg₉ r hr]
      simp only [s₈, s₇, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base),
        State.setArr_regs]
      rw [hreg₆ r hr]
      simp only [s₅, s₄, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base),
        State.setArr_regs]
      rw [hreg₃ r hr]
      simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega]⟩

/-- Loop body of `pass2SplitProg`: processes edge `k = r_base`, splitting `curLeaf (σ₀ k)` if
`remAfter σ₀ k (σ₀ k) > 1` or assigning `curLeaf (σ₀ k)` directly if `remAfter σ₀ k (σ₀ k) ≤ 1`. -/
def pass2SplitBody (a_par a_cur a_rem a_sigma : Arr) (r_t r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_sigma (.reg r_base)))
    (.seq (.assign (r_base + 2) (.read a_rem (.reg (r_base + 1))))
      (.seq (.write a_rem (.reg (r_base + 1)) (.op .sub (.reg (r_base + 2)) (.const 1)))
        (.seq (.assign (r_base + 3) (.read a_cur (.reg (r_base + 1))))
          (.ite (.op .le (.reg (r_base + 2)) (.const 1))
            (.write a_sigma (.reg r_base) (.reg (r_base + 3)))
            (.seq (.write a_par (.reg r_t) (.reg (r_base + 3)))
              (.seq (.write a_par (.op .add (.reg r_t) (.const 1)) (.reg (r_base + 3)))
                (.seq (.write a_sigma (.reg r_base) (.reg r_t))
                  (.seq (.write a_cur (.reg (r_base + 1)) (.op .add (.reg r_t) (.const 1)))
                    (.assign r_t (.op .add (.reg r_t) (.const 2)))))))))))

/-- Pass-2 leaf-splitting loop over `k = 0 .. m - 1`. -/
def pass2SplitProg (a_par a_cur a_rem a_sigma : Arr) (r_m r_t r_base : Reg) : Cmd :=
  .seq (.assign r_base (.const 0))
    (forUp r_base (.reg r_m) (pass2SplitBody a_par a_cur a_rem a_sigma r_t r_base))

theorem remAfter_le {m t₀ : ℕ} (σ₀ : Fin m → Fin t₀) (k : ℕ) (l : Fin t₀) :
    remAfter σ₀ k l ≤ m :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem pass2SplitLoop_exec {w n t₀ ω : ℕ} (G : MultiDigraph n)
    (σ₀ : Fin G.numEdges → Fin t₀) (pairOfLeaf : Fin t₀ → Fin n × Fin n)
    (a_par a_cur a_rem a_sigma : Arr) (r_m r_t r_base : Reg)
    (hne_pc : a_par ≠ a_cur) (hne_pr : a_par ≠ a_rem) (hne_ps : a_par ≠ a_sigma)
    (hne_cr : a_cur ≠ a_rem) (hne_cs : a_cur ≠ a_sigma) (hne_rs : a_rem ≠ a_sigma)
    (hr_m : r_m < r_base) (hr_t : r_t < r_base) (hne_mt : r_m ≠ r_t)
    (hw2 : 2 < 2 ^ w) (h2m_w : 2 * G.numEdges < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (rem k : ℕ) (hrem_eq : k + rem = G.numEdges) :
    ∀ {t : ℕ} {p : ℕ → ℕ} {cur : Fin t₀ → Fin t} {tauDone : Fin G.numEdges → Fin t}
      (_hinv : Pass2CombInv ω G σ₀ pairOfLeaf k t p cur tauDone)
      {s : State}
      (_hpar_len : (s.arrs a_par).length = 2 * G.numEdges)
      (_hpar_val : ∀ z < t, (hz : z < (s.arrs a_par).length) → (s.arrs a_par)[z]'hz = p z)
      (_hcur_len : (s.arrs a_cur).length = t₀)
      (_hcur_val : ∀ l : Fin t₀, (s.arrs a_cur)[l.1]'(by rw [_hcur_len]; exact l.2) = (cur l).1)
      (_hrem_len : (s.arrs a_rem).length = t₀)
      (_hrem_val : ∀ l : Fin t₀,
        (s.arrs a_rem)[l.1]'(by rw [_hrem_len]; exact l.2) = remAfter σ₀ k l)
      (_hsig_len : (s.arrs a_sigma).length = G.numEdges)
      (_hsig_lt : ∀ e : Fin G.numEdges, e.1 < k →
        (s.arrs a_sigma)[e.1]'(by rw [_hsig_len]; exact e.2) = (tauDone e).1)
      (_hsig_ge : ∀ e : Fin G.numEdges, k ≤ e.1 →
        (s.arrs a_sigma)[e.1]'(by rw [_hsig_len]; exact e.2) = (σ₀ e).1)
      (_hrm : s.regs r_m = G.numEdges)
      (_hrt : s.regs r_t = t)
      (_hrk : s.regs r_base = k),
      ∃ (s' : State) (t_loop t' : ℕ) (_ht'_pos : 0 < t')
        (p' : ℕ → ℕ) (tauDone' : Fin G.numEdges → Fin t'),
        Exec w (forUp r_base (.reg r_m)
          (pass2SplitBody a_par a_cur a_rem a_sigma r_t r_base)) s s' t_loop ∧
        t_loop ≤ 3 + 45 * rem ∧
        t' ≤ 2 * G.numEdges ∧
        p' 0 = 0 ∧
        (∀ z, 0 < z → z < t' → p' z < z) ∧
        IsMultiBranchDecompOfWidthLe (3 * ω) G (parentTree t' p') tauDone' ∧
        (s'.arrs a_par).length = 2 * G.numEdges ∧
        (∀ z < t', (hz : z < (s'.arrs a_par).length) → (s'.arrs a_par)[z]'hz = p' z) ∧
        (s'.arrs a_sigma).length = G.numEdges ∧
        (∀ e : Fin G.numEdges, (he : e.1 < (s'.arrs a_sigma).length) →
          (s'.arrs a_sigma)[e.1]'he = (tauDone' e).1) ∧
        s'.regs r_t = t' ∧
        s'.regs r_m = G.numEdges ∧
        (∀ a : Arr, a ≠ a_par → a ≠ a_cur → a ≠ a_rem → a ≠ a_sigma → s'.arrs a = s.arrs a) ∧
        (∀ r < r_base, r ≠ r_t → s'.regs r = s.regs r) := by
  let m := G.numEdges
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  induction rem generalizing k with
  | zero =>
    intro t p cur tauDone hinv s hpar_len hpar_val hcur_len hcur_val hrem_len hrem_val
      hsig_len hsig_lt hsig_ge hrm hrt hrk
    have hk_eq : k = m := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, m, hm_w, h0_w]
    obtain ⟨hbd, ht_le⟩ := hinv.to_branchDecomp_at_end
    have ht_pos : 0 < t := by have := hinv.ht; omega
    refine ⟨s, 3, t, ht_pos, p, tauDone, .while_false hcond, by omega,
      by omega, hinv.hp0, hinv.hp, hbd, hpar_len, hpar_val, hsig_len,
      fun e _ => hsig_lt e e.2, hrt, hrm,
      fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    intro t p cur tauDone hinv s hpar_len hpar_val hcur_len hcur_val hrem_len hrem_val
      hsig_len hsig_lt hsig_ge hrm hrt hrk
    have hk_lt : k < m := by omega
    have hk_w : k < 2 ^ w := by omega
    let ek : Fin m := ⟨k, hk_lt⟩
    let l₀ : Fin t₀ := σ₀ ek
    have ht_pos : 0 < t := by have := hinv.ht; omega
    have ht_le_init : t ≤ 2 * m - 2 := hinv.t_le
    have ht_w : t < 2 ^ w := by omega
    have hl₀_w : l₀.1 < 2 ^ w := Nat.lt_trans l₀.2 ht₀_w
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, m, hk_w, hm_w, hk_lt, hw]
    -- 1. r_base + 1 := a_sigma[r_base]
    have hsig_k : (s.arrs a_sigma)[k]'(by rw [hsig_len]; exact hk_lt) = l₀.1 :=
      hsig_ge ek le_rfl
    let s₁ := s.setReg (r_base + 1) l₀.1
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_sigma (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrk, hk_w, hsig_len, m, hk_lt, hsig_k, hl₀_w])
    -- 2. r_base + 2 := a_rem[r_base + 1]
    let c₀ := remAfter σ₀ k l₀
    let c₁ := remAfter σ₀ (k + 1) l₀
    have hc_step : c₀ = c₁ + 1 := remAfter_step_eq σ₀ hk_lt
    have hc_sub : c₀ - 1 = c₁ := by omega
    have hc₀_le : c₀ ≤ m := remAfter_le σ₀ k l₀
    have hc₀_w : c₀ < 2 ^ w := by omega
    have hc₁_w : c₁ < 2 ^ w := by omega
    have hrem_l₀ : (s.arrs a_rem)[l₀.1]'(by rw [hrem_len]; exact l₀.2) = c₀ := hrem_val l₀
    let s₂ := s₁.setReg (r_base + 2) c₀
    have hex₂ : Exec w (.assign (r_base + 2) (.read a_rem (.reg (r_base + 1)))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hl₀_w, hrem_len, l₀.2, hrem_l₀, hc₀_w])
    -- 3. a_rem[r_base + 1] := (r_base + 2) - 1
    let s₃ := s₂.writeArr a_rem l₀.1 c₁
    have hex₃ : Exec w (.write a_rem (.reg (r_base + 1)) (.op .sub (.reg (r_base + 2)) (.const 1)))
        s₂ s₃ 5 :=
      .write (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hl₀_w])
        (by simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hc₀_w, hw, hc_sub, hc₁_w])
        (by simp [s₂, s₁, hrem_len, l₀.2])
    -- 4. r_base + 3 := a_cur[r_base + 1]
    let v₀ : Fin t := cur l₀
    have hv₀_w : v₀.1 < 2 ^ w := by have := v₀.2; omega
    have hcur₃_eq : s₃.arrs a_cur = s.arrs a_cur := by simp [s₃, s₂, s₁, hne_cr]
    have hcur_l₀ : (s.arrs a_cur)[l₀.1]'(by rw [hcur_len]; exact l₀.2) = v₀.1 := hcur_val l₀
    let s₄ := s₃.setReg (r_base + 3) v₀.1
    have hex₄ : Exec w (.assign (r_base + 3) (.read a_cur (.reg (r_base + 1)))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, State.setReg, hne_cr, Expr.eval, checkWord,
        hl₀_w, hcur_len, l₀.2, hcur_l₀, hv₀_w])
    -- 5. ite (r_base + 2 <= 1)
    by_cases hle1 : c₀ ≤ 1
    · have hite_cond : (Expr.op .le (.reg (r_base + 2)) (.const 1)).eval w s₄ = some 1 := by
        simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hc₀_w, hw, hle1]
      let s₅ := s₄.writeArr a_sigma k v₀.1
      have hex_wr : Exec w (.write a_sigma (.reg r_base) (.reg (r_base + 3))) s₄ s₅ 3 :=
        .write (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hrk, hk_w])
          (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv₀_w])
          (by simp [s₄, s₃, s₂, s₁, hne_rs.symm, hsig_len, m, hk_lt])
      have hex₅ : Exec w (.ite (.op .le (.reg (r_base + 2)) (.const 1))
          (.write a_sigma (.reg r_base) (.reg (r_base + 3)))
          (.seq (.write a_par (.reg r_t) (.reg (r_base + 3)))
            (.seq (.write a_par (.op .add (.reg r_t) (.const 1)) (.reg (r_base + 3)))
              (.seq (.write a_sigma (.reg r_base) (.reg r_t))
                (.seq (.write a_cur (.reg (r_base + 1)) (.op .add (.reg r_t) (.const 1)))
                  (.assign r_t (.op .add (.reg r_t) (.const 2)))))))) s₄ s₅ 6 :=
        .ite_true hite_cond (by omega) hex_wr
      let s₆ := s₅.setReg r_base (k + 1)
      have hex₆ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₅ s₆ 4 :=
        .assign (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw,
          checkWord, hrk, hk_w, hw, show k + 1 < 2 ^ w by omega])
      let tauDone' : Fin m → Fin t := fun e => if e = ek then v₀ else tauDone e
      have hinv' : Pass2CombInv ω G σ₀ pairOfLeaf (k + 1) t p cur tauDone' :=
        hinv.step_le_one hk_lt hle1
          (fun e he => by
            have hne : e ≠ ek := fun h => by have := congrArg Fin.val h; change e.1 = k at this; omega
            simp [tauDone', hne])
          (by simp [tauDone', ek, v₀, l₀])
      have hpar₆ : s₆.arrs a_par = s.arrs a_par := by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_pr, hne_ps]
      have hcur₆ : s₆.arrs a_cur = s.arrs a_cur := by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_cr, hne_cs]
      have hrem₆ : s₆.arrs a_rem = (s.arrs a_rem).set l₀.1 c₁ := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_rs]
      have hsig₆ : s₆.arrs a_sigma = (s.arrs a_sigma).set k v₀.1 := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_rs.symm]
      rcases ih (k + 1) (by omega) hinv' (s := s₆)
          (by rw [hpar₆, hpar_len])
          (fun z hz _ => by simp only [hpar₆]; exact hpar_val z hz (by rw [hpar_len]; omega))
          (by rw [hcur₆, hcur_len])
          (fun l => by simp only [hcur₆]; exact hcur_val l)
          (by rw [hrem₆, List.length_set, hrem_len])
          (fun l => by
            simp only [hrem₆]
            by_cases hl : l = l₀
            · subst hl
              rw [List.getElem_set_self (by rw [List.length_set, hrem_len]; exact l₀.2)]
            · have hne_val : l₀.1 ≠ l.1 := fun h => hl (Fin.ext h.symm)
              rw [List.getElem_set_ne hne_val, hrem_val l, remAfter_step_ne σ₀ hk_lt hl])
          (by rw [hsig₆, List.length_set, hsig_len])
          (fun e he => by
            simp only [hsig₆]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with hlt | heq
            · have hne_e : e ≠ ek := fun h => by
                have := congrArg Fin.val h; change e.1 = k at this; omega
              rw [List.getElem_set_ne (by omega : k ≠ e.1), hsig_lt e hlt]
              simp [tauDone', hne_e]
            · have he_eq : e = ek := Fin.ext heq
              subst he_eq
              rw [List.getElem_set_self (by rw [List.length_set, hsig_len]; exact hk_lt)]
              simp [tauDone', ek])
          (fun e he => by
            simp only [hsig₆]
            rw [List.getElem_set_ne (by omega : k ≠ e.1)]
            exact hsig_ge e (by omega))
          (by
            dsimp [Reg] at hr_m
            simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
              show (r_m : Reg) ≠ r_base by dsimp [Reg]; omega,
              show (r_m : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
              show (r_m : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
              show (r_m : Reg) ≠ r_base + 3 by dsimp [Reg]; omega, hrm])
          (by
            dsimp [Reg] at hr_t
            simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
              show (r_t : Reg) ≠ r_base by dsimp [Reg]; omega,
              show (r_t : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
              show (r_t : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
              show (r_t : Reg) ≠ r_base + 3 by dsimp [Reg]; omega, hrt])
          (by simp [s₆]) with
        ⟨s₇, t₇, t', ht'_pos, p', tauDone'', hex₇, ht₇, ht'_le, hp'0, hp'_lt, hbd',
          hpar₇_len, hpar₇_val, hsig₇_len, hsig₇_val, hrt₇, hrm₇, harr₇, hreg₇⟩
      refine ⟨s₇, 3 + ((3 + (3 + (5 + (3 + 6)))) + 4) + t₇, t', ht'_pos, p', tauDone'',
        .while_true hcond (by omega)
          (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))) hex₆) hex₇,
        by omega, ht'_le, hp'0, hp'_lt, hbd',
        hpar₇_len, hpar₇_val, hsig₇_len, hsig₇_val, hrt₇, hrm₇,
        fun a hap hac har has => by
          rw [harr₇ a hap hac har has]
          simp [s₆, s₅, s₄, s₃, s₂, s₁, har, has],
        fun r hr hrt_ne => by
          dsimp [Reg] at hr
          rw [hreg₇ r hr hrt_ne]
          simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
            show (r : Reg) ≠ r_base by dsimp [Reg]; omega,
            show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
            show (r : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
            show (r : Reg) ≠ r_base + 3 by dsimp [Reg]; omega]⟩
    · have hgt1 : 1 < c₀ := by omega
      let cur' : Fin t₀ → Fin (t + 2) :=
        fun l => if l = l₀ then ⟨t + 1, by omega⟩ else ⟨(cur l).1, by have := (cur l).2; omega⟩
      let tauDone' : Fin m → Fin (t + 2) :=
        fun e => if e = ek then ⟨t, by omega⟩ else ⟨(tauDone e).1, by have := (tauDone e).2; omega⟩
      have hinv' : Pass2CombInv ω G σ₀ pairOfLeaf (k + 1) (t + 2)
          (splitLeafParent p t v₀.1) cur' tauDone' :=
        hinv.step_gt_one hk_lt hgt1
          (by dsimp [cur', l₀, ek]; rw [ite_eq_left_iff.mpr (fun h => False.elim (h rfl))])
          (fun l hl => by dsimp [cur', l₀, ek]; rw [ite_eq_right_iff.mpr (fun h => False.elim (hl h))])
          (fun e he => by
            have hne : e ≠ ek := fun h => by have := congrArg Fin.val h; change e.1 = k at this; omega
            simp [tauDone', hne])
          (by dsimp [tauDone', ek]; rw [ite_eq_left_iff.mpr (fun h => False.elim (h rfl))])
      have ht2_le : t + 2 ≤ 2 * m - 2 := hinv'.t_le
      have ht1_w : t + 1 < 2 ^ w := by omega
      have ht2_w : t + 2 < 2 ^ w := by omega
      have hrt₄ : s₄.regs r_t = t := by
        dsimp [Reg] at hr_t
        simp [s₄, s₃, s₂, s₁, State.setReg,
          show (r_t : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
          show (r_t : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
          show (r_t : Reg) ≠ r_base + 3 by dsimp [Reg]; omega, hrt]
      have hite_cond : (Expr.op .le (.reg (r_base + 2)) (.const 1)).eval w s₄ = some 0 := by
        simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hc₀_w, hw, hle1, h0_w]
      let s₅ := s₄.writeArr a_par t v₀.1
      have hex_e1 : Exec w (.write a_par (.reg r_t) (.reg (r_base + 3))) s₄ s₅ 3 :=
        .write (by simp [Expr.eval, checkWord, hrt₄, ht_w])
          (by simp [s₄, Expr.eval, checkWord, hv₀_w])
          (by simp [s₄, s₃, s₂, s₁, hne_pr, hpar_len]; omega)
      let s₆ := s₅.writeArr a_par (t + 1) v₀.1
      have hex_e2 : Exec w (.write a_par (.op .add (.reg r_t) (.const 1)) (.reg (r_base + 3)))
          s₅ s₆ 5 :=
        .write (by simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrt₄, ht_w, hw, ht1_w])
          (by simp [s₅, s₄, Expr.eval, checkWord, hv₀_w])
          (by simp [s₅, s₄, s₃, s₂, s₁, hne_pr, hpar_len]; omega)
      let s₇ := s₆.writeArr a_sigma k t
      have hex_e3 : Exec w (.write a_sigma (.reg r_base) (.reg r_t)) s₆ s₇ 3 :=
        .write (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hrk, hk_w])
          (by simp [s₆, s₅, Expr.eval, checkWord, hrt₄, ht_w])
          (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_ps.symm, hne_rs.symm, hsig_len, m, hk_lt])
      let s₈ := s₇.writeArr a_cur l₀.1 (t + 1)
      have hex_e4 : Exec w (.write a_cur (.reg (r_base + 1)) (.op .add (.reg r_t) (.const 1)))
          s₇ s₈ 5 :=
        .write (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hl₀_w])
          (by simp [s₇, s₆, s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrt₄, ht_w, hw, ht1_w])
          (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_cs, hne_pc.symm, hne_cr, hcur_len, l₀.2])
      let s₉ := s₈.setReg r_t (t + 2)
      have hex_e5 : Exec w (.assign r_t (.op .add (.reg r_t) (.const 2))) s₈ s₉ 4 :=
        .assign (by simp [s₈, s₇, s₆, s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hrt₄, ht_w, hw2, ht2_w])
      have hex₅ : Exec w (.ite (.op .le (.reg (r_base + 2)) (.const 1))
          (.write a_sigma (.reg r_base) (.reg (r_base + 3)))
          (.seq (.write a_par (.reg r_t) (.reg (r_base + 3)))
            (.seq (.write a_par (.op .add (.reg r_t) (.const 1)) (.reg (r_base + 3)))
              (.seq (.write a_sigma (.reg r_base) (.reg r_t))
                (.seq (.write a_cur (.reg (r_base + 1)) (.op .add (.reg r_t) (.const 1)))
                  (.assign r_t (.op .add (.reg r_t) (.const 2)))))))) s₄ s₉ 23 :=
        .ite_false hite_cond (.seq hex_e1 (.seq hex_e2 (.seq hex_e3 (.seq hex_e4 hex_e5))))
      let s₁₀ := s₉.setReg r_base (k + 1)
      have hex₆ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₉ s₁₀ 4 :=
        .assign (by
          dsimp [Reg] at hr_t
          simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
            show (r_base : Reg) ≠ r_t by dsimp [Reg]; omega,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hk_w, hw,
            show k + 1 < 2 ^ w by omega])
      have hpar₁₀ : s₁₀.arrs a_par = ((s.arrs a_par).set t v₀.1).set (t + 1) v₀.1 := by
        simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_pc, hne_ps, hne_pr]
      have hcur₁₀ : s₁₀.arrs a_cur = (s.arrs a_cur).set l₀.1 (t + 1) := by
        simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_cs, hne_pc.symm, hne_cr]
      have hrem₁₀ : s₁₀.arrs a_rem = (s.arrs a_rem).set l₀.1 c₁ := by
        simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_cr.symm, hne_rs, hne_pr.symm]
      have hsig₁₀ : s₁₀.arrs a_sigma = (s.arrs a_sigma).set k t := by
        simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_cs.symm, hne_ps.symm, hne_rs.symm]
      rcases ih (k + 1) (by omega) hinv' (s := s₁₀)
          (by rw [hpar₁₀, List.length_set, List.length_set, hpar_len])
          (fun z hz _ => by
            simp only [hpar₁₀]
            unfold splitLeafParent
            by_cases hzt1 : z = t + 1
            · subst hzt1
              rw [List.getElem_set_self (by simp [hpar_len]; omega),
                ite_eq_left_iff.mpr (fun h => False.elim (h (Or.inr rfl)))]
            · rw [List.getElem_set_ne (by omega : t + 1 ≠ z)]
              by_cases hzt : z = t
              · subst hzt
                rw [List.getElem_set_self (by simp [hpar_len]; omega),
                  ite_eq_left_iff.mpr (fun h => False.elim (h (Or.inl rfl)))]
              · rw [List.getElem_set_ne (by omega : t ≠ z),
                  ite_eq_right_iff.mpr (fun h => False.elim ((by omega : ¬ (z = t ∨ z = t + 1)) h))]
                exact hpar_val z (by omega) (by rw [hpar_len]; omega))
          (by rw [hcur₁₀, List.length_set, hcur_len])
          (fun l => by
            simp only [hcur₁₀]
            by_cases hl : l = l₀
            · subst hl
              rw [List.getElem_set_self (by rw [List.length_set, hcur_len]; exact l₀.2)]
              simp [cur']
            · have hne_val : l₀.1 ≠ l.1 := fun h => hl (Fin.ext h.symm)
              rw [List.getElem_set_ne hne_val, hcur_val l]
              simp [cur', hl])
          (by rw [hrem₁₀, List.length_set, hrem_len])
          (fun l => by
            simp only [hrem₁₀]
            by_cases hl : l = l₀
            · subst hl
              rw [List.getElem_set_self (by rw [List.length_set, hrem_len]; exact l₀.2)]
            · have hne_val : l₀.1 ≠ l.1 := fun h => hl (Fin.ext h.symm)
              rw [List.getElem_set_ne hne_val, hrem_val l, remAfter_step_ne σ₀ hk_lt hl])
          (by rw [hsig₁₀, List.length_set, hsig_len])
          (fun e he => by
            simp only [hsig₁₀]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with hlt | heq
            · have hne_e : e ≠ ek := fun h => by
                have := congrArg Fin.val h; change e.1 = k at this; omega
              rw [List.getElem_set_ne (by omega : k ≠ e.1), hsig_lt e hlt]
              simp [tauDone', hne_e]
            · have he_eq : e = ek := Fin.ext heq
              subst he_eq
              rw [List.getElem_set_self (by rw [List.length_set, hsig_len]; exact hk_lt)]
              simp [tauDone', ek])
          (fun e he => by
            simp only [hsig₁₀]
            rw [List.getElem_set_ne (by omega : k ≠ e.1)]
            exact hsig_ge e (by omega))
          (by
            dsimp [Reg] at hr_m hne_mt
            simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hne_mt,
              show (r_m : Reg) ≠ r_base by dsimp [Reg]; omega,
              show (r_m : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
              show (r_m : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
              show (r_m : Reg) ≠ r_base + 3 by dsimp [Reg]; omega, hrm])
          (by
            dsimp [Reg] at hr_t
            simp [s₁₀, s₉, State.setReg, show (r_t : Reg) ≠ r_base by dsimp [Reg]; omega])
          (by simp [s₁₀]) with
        ⟨s₁₁, t₁₁, t', ht'_pos, p', tauDone'', hex₁₁, ht₁₁, ht'_le, hp'0, hp'_lt, hbd',
          hpar₁₁_len, hpar₁₁_val, hsig₁₁_len, hsig₁₁_val, hrt₁₁, hrm₁₁, harr₁₁, hreg₁₁⟩
      refine ⟨s₁₁, 3 + ((3 + (3 + (5 + (3 + 23)))) + 4) + t₁₁, t', ht'_pos, p', tauDone'',
        .while_true hcond (by omega)
          (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))) hex₆) hex₁₁,
        by omega, ht'_le, hp'0, hp'_lt, hbd',
        hpar₁₁_len, hpar₁₁_val, hsig₁₁_len, hsig₁₁_val, hrt₁₁, hrm₁₁,
        fun a hap hac har has => by
          rw [harr₁₁ a hap hac har has]
          simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hap, hac, har, has],
        fun r hr hrt_ne => by
          dsimp [Reg] at hr
          rw [hreg₁₁ r hr hrt_ne]
          simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hrt_ne,
            show (r : Reg) ≠ r_base by dsimp [Reg]; omega,
            show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
            show (r : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
            show (r : Reg) ≠ r_base + 3 by dsimp [Reg]; omega]⟩

theorem pass2SplitProg_exec {w n t₀ ω : ℕ} (G : MultiDigraph n)
    (σ₀ : Fin G.numEdges → Fin t₀) (pairOfLeaf : Fin t₀ → Fin n × Fin n) (p₀ : ℕ → ℕ)
    (a_par a_cur a_rem a_sigma : Arr) (r_m r_t r_base : Reg)
    (hne_pc : a_par ≠ a_cur) (hne_pr : a_par ≠ a_rem) (hne_ps : a_par ≠ a_sigma)
    (hne_cr : a_cur ≠ a_rem) (hne_cs : a_cur ≠ a_sigma) (hne_rs : a_rem ≠ a_sigma)
    (hr_m : r_m < r_base) (hr_t : r_t < r_base) (hne_mt : r_m ≠ r_t)
    (hw2 : 2 < 2 ^ w) (h2m_w : 2 * G.numEdges < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (hinv₀ : Pass2CombInv ω G σ₀ pairOfLeaf 0 t₀ p₀ id σ₀)
    {s : State}
    (hpar_len : (s.arrs a_par).length = 2 * G.numEdges)
    (hpar_val : ∀ z < t₀, (hz : z < (s.arrs a_par).length) → (s.arrs a_par)[z]'hz = p₀ z)
    (hcur_len : (s.arrs a_cur).length = t₀)
    (hcur_val : ∀ l : Fin t₀, (s.arrs a_cur)[l.1]'(by rw [hcur_len]; exact l.2) = l.1)
    (hrem_len : (s.arrs a_rem).length = t₀)
    (hrem_val : ∀ l : Fin t₀,
      (s.arrs a_rem)[l.1]'(by rw [hrem_len]; exact l.2) = remAfter σ₀ 0 l)
    (hsig_len : (s.arrs a_sigma).length = G.numEdges)
    (hsig_val : ∀ e : Fin G.numEdges,
      (s.arrs a_sigma)[e.1]'(by rw [hsig_len]; exact e.2) = (σ₀ e).1)
    (hrm : s.regs r_m = G.numEdges)
    (hrt : s.regs r_t = t₀) :
    ∃ (s' : State) (t_pass2 t' : ℕ) (_ht'_pos : 0 < t')
      (p' : ℕ → ℕ) (tauDone' : Fin G.numEdges → Fin t'),
      Exec w (pass2SplitProg a_par a_cur a_rem a_sigma r_m r_t r_base) s s' t_pass2 ∧
      t_pass2 ≤ 45 * G.numEdges + 5 ∧
      t' ≤ 2 * G.numEdges ∧
      p' 0 = 0 ∧
      (∀ z, 0 < z → z < t' → p' z < z) ∧
      IsMultiBranchDecompOfWidthLe (3 * ω) G (parentTree t' p') tauDone' ∧
      (s'.arrs a_par).length = 2 * G.numEdges ∧
      (∀ z < t', (hz : z < (s'.arrs a_par).length) → (s'.arrs a_par)[z]'hz = p' z) ∧
      (s'.arrs a_sigma).length = G.numEdges ∧
      (∀ e : Fin G.numEdges, (he : e.1 < (s'.arrs a_sigma).length) →
        (s'.arrs a_sigma)[e.1]'he = (tauDone' e).1) ∧
      s'.regs r_t = t' ∧
      s'.regs r_m = G.numEdges ∧
      (∀ a : Arr, a ≠ a_par → a ≠ a_cur → a ≠ a_rem → a ≠ a_sigma → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_t → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_base 0
  have hex₁ : Exec w (.assign r_base (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases pass2SplitLoop_exec G σ₀ pairOfLeaf a_par a_cur a_rem a_sigma r_m r_t r_base
      hne_pc hne_pr hne_ps hne_cr hne_cs hne_rs hr_m hr_t hne_mt hw2 h2m_w ht₀_w
      G.numEdges 0 (by omega) hinv₀ (s := s₁)
      hpar_len hpar_val hcur_len hcur_val hrem_len hrem_val hsig_len
      (fun _ he => by omega) (fun e _ => hsig_val e)
      (by
        dsimp [Reg] at hr_m
        simp [s₁, State.setReg, show (r_m : Reg) ≠ r_base by dsimp [Reg]; omega, hrm])
      (by
        dsimp [Reg] at hr_t
        simp [s₁, State.setReg, show (r_t : Reg) ≠ r_base by dsimp [Reg]; omega, hrt])
      (by simp [s₁]) with
    ⟨s₂, t₂, t', ht'_pos, p', tauDone', hex₂, ht₂, ht'_le, hp'0, hp'_lt, hbd',
      hpar₂_len, hpar₂_val, hsig₂_len, hsig₂_val, hrt₂, hrm₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, t', ht'_pos, p', tauDone', .seq hex₁ hex₂, by omega,
    ht'_le, hp'0, hp'_lt, hbd', hpar₂_len, hpar₂_val, hsig₂_len, hsig₂_val, hrt₂, hrm₂,
    fun a hap hac har has => harr₂ a hap hac har has,
    fun r hr hrt_ne => by
      dsimp [Reg] at hr
      rw [hreg₂ r hr hrt_ne]
      simp [s₁, State.setReg, show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

/-! ### Section 5: High-Branch-Width Subgraph Lifting and Pass-2 Leaf Matrix -/

theorem mul_add_lt_sq {n u v : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have h1 : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

theorem mul_add_inj_of_lt {n u₁ v₁ u₂ v₂ : ℕ} (hv₁ : v₁ < n) (hv₂ : v₂ < n)
    (h : u₁ * n + v₁ = u₂ * n + v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  rcases lt_trichotomy u₁ u₂ with hlt | rfl | hgt
  · exfalso
    have h1 : (u₁ + 1) * n ≤ u₂ * n := Nat.mul_le_mul_right n (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  · exact ⟨rfl, by omega⟩
  · exfalso
    have h1 : (u₂ + 1) * n ≤ u₁ * n := Nat.mul_le_mul_right n (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

/-- Allocate `a_arr` of length `r_len` and fill every entry with `r_val` using loop index `r_i`. -/
def fillArrProg (a_arr : Arr) (r_len r_val r_i : Reg) : Cmd :=
  .seq (.alloc a_arr (.reg r_len))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_len) (.write a_arr (.reg r_i) (.reg r_val))))

theorem fillArrLoop_exec {w L val : ℕ} (a_arr : Arr) (r_len r_val r_i : Reg)
    (hne_li : r_len ≠ r_i) (hne_vi : r_val ≠ r_i)
    (hw : 1 < 2 ^ w) (hL_w : L < 2 ^ w) (hval_w : val < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = L) {s : State}
    (harr : s.arrs a_arr = List.replicate k val ++ List.replicate rem 0)
    (hrlen : s.regs r_len = L)
    (hrval : s.regs r_val = val)
    (hri : s.regs r_i = k) :
    ∃ s' t,
      Exec w (forUp r_i (.reg r_len) (.write a_arr (.reg r_i) (.reg r_val))) s s' t ∧
      t ≤ 3 + 10 * rem ∧
      s'.arrs a_arr = List.replicate L val ∧
      (∀ a : Arr, a ≠ a_arr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = L := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrlen, hL_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, by simpa using harr,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < L := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_i) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrlen, hk_w, hL_w, hk_lt, hw]
    have hlen_arr : k < (s.arrs a_arr).length := by simp [harr]
    let s₁ := s.writeArr a_arr k val
    have hex₁ : Exec w (.write a_arr (.reg r_i) (.reg r_val)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hri, hk_w])
        (by simp [Expr.eval, checkWord, hrval, hval_w]) hlen_arr
    let s₂ := s₁.setReg r_i (k + 1)
    have hex₂ : Exec w (.assign r_i (.op .add (.reg r_i) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hri, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have harr₂ : s₂.arrs a_arr = List.replicate (k + 1) val ++ List.replicate rem 0 := by
      simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, harr]
      have hset := set_append_replicate_succ (List.replicate k val) rem val
      rw [List.length_replicate] at hset
      rw [hset, ← List.replicate_succ']
    rcases ih (k + 1) (by omega) (s := s₂) harr₂
        (by simp [s₂, s₁, State.setReg, hne_li, hrlen])
        (by simp [s₂, s₁, State.setReg, hne_vi, hrval])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, harr₃, harr_ne₃, hreg₃⟩
    refine ⟨s₃, 3 + (3 + 4) + t₃, .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃,
      by omega, harr₃,
      fun a ha => by rw [harr_ne₃ a ha]; simp [s₂, s₁, ha],
      fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

theorem fillArrProg_exec {w L val : ℕ} (a_arr : Arr) (r_len r_val r_i : Reg)
    (hne_li : r_len ≠ r_i) (hne_vi : r_val ≠ r_i)
    (hw : 1 < 2 ^ w) (hL_w : L < 2 ^ w) (hval_w : val < 2 ^ w)
    {s : State}
    (hrlen : s.regs r_len = L)
    (hrval : s.regs r_val = val) :
    ∃ s' t,
      Exec w (fillArrProg a_arr r_len r_val r_i) s s' t ∧
      t ≤ 11 * L + 6 ∧
      s'.arrs a_arr = List.replicate L val ∧
      (∀ a : Arr, a ≠ a_arr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_arr (List.replicate L 0)
  have hex₁ : Exec w (.alloc a_arr (.reg r_len)) s s₁ (1 + L) :=
    .alloc (by simp [Expr.eval, checkWord, hrlen, hL_w])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases fillArrLoop_exec a_arr r_len r_val r_i hne_li hne_vi hw hL_w hval_w L 0 (by omega)
      (s := s₂) (by simp [s₂, s₁])
      (by simp [s₂, s₁, State.setReg, hne_li, hrlen])
      (by simp [s₂, s₁, State.setReg, hne_vi, hrval])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, harr₃, harr_ne₃, hreg₃⟩
  refine ⟨s₃, (1 + L) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, harr₃,
    fun a ha => by rw [harr_ne₃ a ha]; simp [s₂, s₁, ha],
    fun r hr => by rw [hreg₃ r hr]; simp [s₂, s₁, State.setReg, hr]⟩

/-- Loop body of `buildDirMatProg`: reads active pair `(u_k, v_k)` from `a_src` and sets
`a_dir[u_k * n + v_k] := 1`. -/
def buildDirMatBody (a_src a_dir : Arr) (r_n r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src r_base (r_base + 1) (r_base + 2) (r_base + 3))
    (.write a_dir
      (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_n)) (.reg (r_base + 3)))
      (.const 1))

/-- Build the `n × n` boolean matrix `a_dir` where `a_dir[u * n + v] = if 0 < G.edgeMult u v then 1 else 0`
in `O(n² + m')` steps. -/
def buildDirMatProg (a_src a_dir : Arr) (r_n r_m' r_base : Reg) : Cmd :=
  .seq (.alloc a_dir (.op .mul (.reg r_n) (.reg r_n)))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_m') (buildDirMatBody a_src a_dir r_n r_base)))

theorem buildDirMatLoop_exec {w n : ℕ} (G : MultiDigraph n)
    (a_src a_dir : Arr) (r_n r_m' r_base : Reg)
    (hne_sd : a_src ≠ a_dir)
    (hr_n : r_n < r_base) (hr_m' : r_m' < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (suff pref : List (Fin n × Fin n))
    (hsplit : G.activePairsList = pref ++ suff)
    {s : State}
    (hsrc : s.arrs a_src = G.enc)
    (hdir_len : (s.arrs a_dir).length = n * n)
    (hdir_val : ∀ u v : Fin n,
      (s.arrs a_dir)[u.1 * n + v.1]'(by rw [hdir_len]; exact mul_add_lt_sq u.2 v.2) =
        if (u, v) ∈ pref then 1 else 0)
    (hrn_val : s.regs r_n = n)
    (hrm'_val : s.regs r_m' = G.numActivePairs)
    (hrk_val : s.regs r_base = pref.length) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_m') (buildDirMatBody a_src a_dir r_n r_base)) s s' t ∧
      t ≤ 3 + 28 * suff.length ∧
      ∃ (hdir'_len : (s'.arrs a_dir).length = n * n),
      (∀ u v : Fin n,
        (s'.arrs a_dir)[u.1 * n + v.1]'(by rw [hdir'_len]; exact mul_add_lt_sq u.2 v.2) =
          if (u, v) ∈ pref ++ suff then 1 else 0) ∧
      (∀ a : Arr, a ≠ a_dir → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff generalizing pref s with
  | nil =>
    have hk_eq : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m')).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm'_val, hk_eq, hm'_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hdir_len, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    intro u v
    simpa using hdir_val u v
  | cons p ps ih =>
    rcases p with ⟨u_k, v_k⟩
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m')).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm'_val, k, hk_m', hk_w, hm'_w, hw]
    have hsrc' : s.arrs a_src = G.enc ++ [] := by simp [hsrc]
    rcases readTripleEndpoints_exec G [] a_src r_base (r_base + 1) (r_base + 2) (r_base + 3)
        k s (by omega) (by omega) (by omega) hw3 hn_w hm3_w hk_m' hsrc' hrk_val with
      ⟨s₁, t₁, hex₁, ht₁, _, hru₁, hrv₁, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u_k := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v_k := congrArg Prod.snd hget_k
    rw [hget_u] at hru₁
    rw [hget_v] at hrv₁
    have hu_w : u_k.1 < 2 ^ w := Nat.lt_trans u_k.2 hn_w
    have hv_w : v_k.1 < 2 ^ w := Nat.lt_trans v_k.2 hn_w
    have hidx_sq : u_k.1 * n + v_k.1 < n * n := mul_add_lt_sq u_k.2 v_k.2
    have hmul_w : u_k.1 * n < 2 ^ w := by omega
    have hidx_w : u_k.1 * n + v_k.1 < 2 ^ w := by omega
    have hrn₁ : s₁.regs r_n = n := by
      dsimp [Reg] at hr_n
      rw [hreg₁ r_n (by omega) (by omega) (by omega)]
      exact hrn_val
    have hlen_dir₁ : u_k.1 * n + v_k.1 < (s₁.arrs a_dir).length := by
      rw [harr₁, hdir_len]; exact hidx_sq
    let s₂ := s₁.writeArr a_dir (u_k.1 * n + v_k.1) 1
    have hex₂ : Exec w (.write a_dir
        (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_n)) (.reg (r_base + 3))) (.const 1))
        s₁ s₂ 7 :=
      .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hrv₁, hrn₁,
        hu_w, hn_w, hmul_w, hv_w, hidx_w])
        (by simp [Expr.eval, checkWord, hw]) hlen_dir₁
    have hrk₂ : s₂.regs r_base = k := by
      simp only [s₂, State.writeArr_regs]
      rw [hreg₁ r_base (by omega) (by omega) (by omega)]
      exact hrk_val
    let s₃ := s₂.setReg r_base (k + 1)
    have hex₃ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega])
    have hsplit' : G.activePairsList = (pref ++ [(u_k, v_k)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    have hdir₃_len : (s₃.arrs a_dir).length = n * n := by
      simp [s₃, s₂, harr₁, hdir_len]
    rcases ih (pref ++ [(u_k, v_k)]) hsplit' (s := s₃)
        (by simp [s₃, s₂, hne_sd, harr₁, hsrc])
        hdir₃_len
        (fun u v => by
          simp only [s₃, s₂, State.setReg_arrs, State.writeArr_arrs_self]
          by_cases huv : (u, v) = (u_k, v_k)
          · rcases Prod.mk.inj huv with ⟨rfl, rfl⟩
            rw [List.getElem_set_self]
            simp
          · have hne_idx : u_k.1 * n + v_k.1 ≠ u.1 * n + v.1 := by
              intro heq
              rcases mul_add_inj_of_lt v_k.2 v.2 heq with ⟨h1, h2⟩
              exact huv (Prod.ext (Fin.ext h1.symm) (Fin.ext h2.symm))
            rw [List.getElem_set_ne hne_idx]
            simp only [harr₁, hdir_val u v, List.mem_append, List.mem_singleton, huv, or_false])
        (by
          dsimp [Reg] at hr_n
          simp [s₃, s₂, State.setReg, show (r_n : Reg) ≠ r_base by dsimp [Reg]; omega, hrn₁])
        (by
          dsimp [Reg] at hr_m'
          simp only [s₃, s₂, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_m' : Reg) ≠ r_base),
            State.writeArr_regs]
          rw [hreg₁ r_m' (by omega) (by omega) (by omega)]
          exact hrm'_val)
        (by simp [s₃, k]) with
      ⟨s₄, t₄, hex₄, ht₄, hdir₄_len, hdir₄_val, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((t₁ + 7) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by simp only [List.length_cons]; omega,
      hdir₄_len,
      fun u v => by simpa [List.append_assoc] using hdir₄_val u v,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, harr₁, ha],
      fun r hr => by
        dsimp [Reg] at hr
        rw [hreg₄ r hr]
        simp only [s₃, s₂, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base),
          State.writeArr_regs]
        exact hreg₁ r (by omega) (by omega) (by omega)⟩

theorem buildDirMatProg_exec {w n : ℕ} (G : MultiDigraph n)
    (a_src a_dir : Arr) (r_n r_m' r_base : Reg)
    (hne_sd : a_src ≠ a_dir)
    (hr_n : r_n < r_base) (hr_m' : r_m' < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc)
    (hrn_val : s.regs r_n = n)
    (hrm'_val : s.regs r_m' = G.numActivePairs) :
    ∃ s' t,
      Exec w (buildDirMatProg a_src a_dir r_n r_m' r_base) s s' t ∧
      t ≤ n * n + 28 * G.numActivePairs + 8 ∧
      ∃ (hdir'_len : (s'.arrs a_dir).length = n * n),
      (∀ u v : Fin n,
        (s'.arrs a_dir)[u.1 * n + v.1]'(by rw [hdir'_len]; exact mul_add_lt_sq u.2 v.2) =
          if 0 < G.edgeMult u v then 1 else 0) ∧
      (∀ a : Arr, a ≠ a_dir → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_dir (List.replicate (n * n) 0)
  have hex₁ : Exec w (.alloc a_dir (.op .mul (.reg r_n) (.reg r_n))) s s₁ (3 + n * n) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn_val, hn_w, hn2_w])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases buildDirMatLoop_exec G a_src a_dir r_n r_m' r_base hne_sd hr_n hr_m'
      hw3 hn_w hn2_w hm3_w G.activePairsList [] rfl (s := s₂)
      (by simp [s₂, s₁, hne_sd, hsrc])
      (by simp [s₂, s₁])
      (fun u v => by simp [s₂, s₁])
      (by
        dsimp [Reg] at hr_n
        simp [s₂, s₁, State.setReg, show (r_n : Reg) ≠ r_base by dsimp [Reg]; omega, hrn_val])
      (by
        dsimp [Reg] at hr_m'
        simp [s₂, s₁, State.setReg, show (r_m' : Reg) ≠ r_base by dsimp [Reg]; omega, hrm'_val])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hdir₃_len, hdir₃_val, harr₃, hreg₃⟩
  have hlen_apl : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_apl] at ht₃
  refine ⟨s₃, (3 + n * n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hdir₃_len,
    fun u v => by
      have h := hdir₃_val u v
      simp only [List.nil_append, G.mem_activePairsList] at h
      exact h,
    fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
    fun r hr => by
      dsimp [Reg] at hr
      rw [hreg₃ r hr]
      simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

theorem aliveIndicesUpTo_eq_take_filter {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) (k : ℕ) :
    aliveIndicesUpTo aliveSet k =
      ((List.finRange m₂).take k).filter (fun j => decide (j ∈ aliveSet)) := by
  apply sublist_eq_of_nodup_of_mem_iff (List.nodup_finRange m₂)
  · exact List.filter_sublist
  · exact List.filter_sublist.trans (List.take_sublist _ _)
  · intro j
    rw [mem_aliveIndicesUpTo, List.mem_filter]
    constructor
    · rintro ⟨hjk, hmem⟩
      refine ⟨?_, decide_eq_true hmem⟩
      rw [List.mem_take_iff_getElem]
      exact ⟨j.1, by simp [j.2, hjk], by simp⟩
    · rintro ⟨htake, hmem⟩
      rw [List.mem_take_iff_getElem] at htake
      rcases htake with ⟨i, hi, hget⟩
      have hij : i = j.1 := by
        have := congrArg Fin.val hget
        simpa using this
      exact ⟨by omega, of_decide_eq_true hmem⟩

@[simp]
theorem aliveIndicesUpTo_zero {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) :
    aliveIndicesUpTo aliveSet 0 = [] := by
  rw [aliveIndicesUpTo_eq_take_filter]
  rfl

theorem aliveIndicesUpTo_succ {m₂ : ℕ} (aliveSet : Finset (Fin m₂)) {k : ℕ} (hk : k < m₂) :
    aliveIndicesUpTo aliveSet (k + 1) =
      aliveIndicesUpTo aliveSet k ++
        (if (⟨k, hk⟩ : Fin m₂) ∈ aliveSet then [⟨k, hk⟩] else []) := by
  rw [aliveIndicesUpTo_eq_take_filter aliveSet (k + 1),
      aliveIndicesUpTo_eq_take_filter aliveSet k]
  have htake : (List.finRange m₂).take (k + 1) = (List.finRange m₂).take k ++ [⟨k, hk⟩] := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi₁ hi₂
      rw [List.getElem_take, List.getElem_finRange]
      have hi_lt : i < k + 1 := by simp at hi₁; omega
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi_lt) with hlt | heq
      · have hi_m2 : i < m₂ := Nat.lt_trans hlt hk
        rw [List.getElem_append_left (by simp [hlt, hi_m2]), List.getElem_take, List.getElem_finRange]
      · subst heq
        have hlen_k : ((List.finRange m₂).take i).length = i := by simp [Nat.le_of_lt hk]
        rw [List.getElem_append_right (by omega)]
        simp [hlen_k]
  rw [htake, List.filter_append]
  simp [List.filter_cons]

/-- Loop body of `liftSubgraphProg`: checks if `a_alive[k] = 1`; if so, reads `(u, v) = (a_eu[k], a_ev[k])`
and `d = a_dir[u * n + v]`, appends `[u, v, 1]` (if `d = 1`) or `[v, u, 1]` (if `d = 0`) to `a_buf`,
appends `a_tau0[k]` to `a_sig_buf`, and increments `r_base + 1`. -/
def liftSubgraphBody (a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf : Arr)
    (r_n r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 4) (.read a_alive (.reg r_base)))
    (.ite (.op .eq (.reg (r_base + 4)) (.const 1))
      (.seq (.assign (r_base + 5) (.read a_eu (.reg r_base)))
        (.seq (.assign (r_base + 6) (.read a_ev (.reg r_base)))
          (.seq (.assign (r_base + 7)
              (.read a_dir
                (.op .add (.op .mul (.reg (r_base + 5)) (.reg r_n)) (.reg (r_base + 6)))))
            (.seq
              (.ite (.op .eq (.reg (r_base + 7)) (.const 1))
                (bufPush3 a_buf (r_base + 2) (r_base + 5) (r_base + 6) (r_base + 3))
                (bufPush3 a_buf (r_base + 2) (r_base + 6) (r_base + 5) (r_base + 3)))
              (.seq (.assign (r_base + 8) (.read a_tau0 (.reg r_base)))
                (.seq (.write a_sig_buf (.reg (r_base + 1)) (.reg (r_base + 8)))
                  (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))))))
      .skip)

/-- Lift the simple subgraph `H₃ = graphOfAlive edges₂ hloop₂ aliveSet` to
`G' = liftSimpleSubgraph G H₃`, writing `G'.enc` into `a_G_out`, the restricted leaf map into
`a_sigma`, and `G'.numEdges` into `r_m_out`. -/
def liftSubgraphProg (a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf a_G_out a_sigma : Arr)
    (r_n r_m2 r_m_out r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 2) (.op .add (.const 2) (.op .mul (.const 3) (.reg r_m2))))
    (.seq (.alloc a_buf (.reg (r_base + 2)))
      (.seq (.write a_buf (.const 0) (.reg r_n))
        (.seq (.alloc a_sig_buf (.reg r_m2))
          (.seq (.assign r_base (.const 0))
            (.seq (.assign (r_base + 1) (.const 0))
              (.seq (.assign (r_base + 2) (.const 2))
                (.seq (.assign (r_base + 3) (.const 1))
                  (.seq (forUp r_base (.reg r_m2)
                      (liftSubgraphBody a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf r_n r_base))
                    (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                      (.seq (.assign r_m_out (.reg (r_base + 1)))
                        (.seq (readSliceProg a_buf (.const 0) a_G_out (.reg (r_base + 2)) (r_base + 4))
                          (readSliceProg a_sig_buf (.const 0) a_sigma (.reg r_m_out) (r_base + 4)))))))))))))

theorem liftSubgraphLoop_exec {w n t₀ : ℕ} (G : MultiDigraph n) (m₂ : ℕ)
    (aliveSet : Finset (Fin ((edgeListOf G.toSimpleGraph).take m₂).length))
    (f_tau : Fin ((edgeListOf G.toSimpleGraph).take m₂).length → Fin t₀)
    (a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf : Arr)
    (r_n r_m2 r_base : Reg)
    (hne_eu_buf : a_eu ≠ a_buf) (hne_eu_sig : a_eu ≠ a_sig_buf)
    (hne_ev_buf : a_ev ≠ a_buf) (hne_ev_sig : a_ev ≠ a_sig_buf)
    (hne_al_buf : a_alive ≠ a_buf) (hne_al_sig : a_alive ≠ a_sig_buf)
    (hne_tau_buf : a_tau0 ≠ a_buf) (hne_tau_sig : a_tau0 ≠ a_sig_buf)
    (hne_dir_buf : a_dir ≠ a_buf) (hne_dir_sig : a_dir ≠ a_sig_buf)
    (hne_buf_sig : a_buf ≠ a_sig_buf)
    (hr_n : r_n < r_base) (hr_m2 : r_m2 < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm2_3_w : 2 + 3 * m₂ < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (hlen_e2 : ((edgeListOf G.toSimpleGraph).take m₂).length = m₂)
    (rem k extra_buf extra_sig : ℕ) (hrem : k + rem = m₂)
    {s : State}
    (hend : IsEndpointArrs ((edgeListOf G.toSimpleGraph).take m₂) a_eu a_ev s)
    (hal : IsBitSet aliveSet a_alive s)
    (htau : IsTauArr f_tau a_tau0 s)
    (hdir_len : (s.arrs a_dir).length = n * n)
    (hdir_val : ∀ u v : Fin n,
      (s.arrs a_dir)[u.1 * n + v.1]'(by rw [hdir_len]; exact mul_add_lt_sq u.2 v.2) =
        if 0 < G.edgeMult u v then 1 else 0)
    (hbuf : s.arrs a_buf =
      ([n, 0] ++
        (liftSimpleSubgraph G
          (graphOfAlive ((edgeListOf G.toSimpleGraph).take m₂)
            (take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)
            aliveSet)).flatTriples
          ((aliveIndicesUpTo aliveSet k).map
            (fun j => liftEdgeDir G (((edgeListOf G.toSimpleGraph).take m₂)[j.1]'j.2)))) ++
        List.replicate (3 * rem + extra_buf) 0)
    (hsig : s.arrs a_sig_buf =
      ((aliveIndicesUpTo aliveSet k).map (fun j => (f_tau j).1)) ++
        List.replicate (rem + extra_sig) 0)
    (hrn_val : s.regs r_n = n)
    (hrm2_val : s.regs r_m2 = m₂)
    (hrk_val : s.regs r_base = k)
    (hrm_acc : s.regs (r_base + 1) = (aliveIndicesUpTo aliveSet k).length)
    (hrpos : s.regs (r_base + 2) = 2 + 3 * (aliveIndicesUpTo aliveSet k).length)
    (hr3 : s.regs (r_base + 3) = 1) :
    let edges₂ := (edgeListOf G.toSimpleGraph).take m₂
    let hloop₂ := take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂
    let H₃ := graphOfAlive edges₂ hloop₂ aliveSet
    let G' := liftSimpleSubgraph G H₃
    let idxList := aliveIndicesUpTo aliveSet m₂
    ∃ s' t extra_buf' extra_sig',
      Exec w (forUp r_base (.reg r_m2)
        (liftSubgraphBody a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf r_n r_base)) s s' t ∧
      t ≤ 3 + 58 * rem ∧
      s'.arrs a_buf =
        ([n, 0] ++ G'.flatTriples (idxList.map (fun j => liftEdgeDir G (edges₂[j.1]'j.2)))) ++
          List.replicate extra_buf' 0 ∧
      s'.arrs a_sig_buf =
        (idxList.map (fun j => (f_tau j).1)) ++ List.replicate extra_sig' 0 ∧
      s'.regs (r_base + 1) = idxList.length ∧
      s'.regs (r_base + 2) = 2 + 3 * idxList.length ∧
      (∀ a : Arr, a ≠ a_buf → a ≠ a_sig_buf → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  intro edges₂ hloop₂ H₃ G' idxList
  change edges₂.length = m₂ at hlen_e2
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm₂_w : m₂ < 2 ^ w := by omega
  have hH₃_le : H₃ ≤ G.toSimpleGraph :=
    (graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet).trans
      (graphOfEdgeList_take_le (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)
  induction rem generalizing k extra_buf extra_sig s with
  | zero =>
    have hk_eq : k = m₂ := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm2_val, hm₂_w, h0_w]
    refine ⟨s, 3, extra_buf, extra_sig, .while_false hcond, by omega,
      by simpa only [Nat.mul_zero, Nat.zero_add] using hbuf,
      by simpa only [Nat.zero_add] using hsig, hrm_acc, hrpos,
      fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < m₂ := by omega
    have hk_e2 : k < edges₂.length := by omega
    have hk_w : k < 2 ^ w := by omega
    let jk : Fin edges₂.length := ⟨k, hk_e2⟩
    let idxs := aliveIndicesUpTo aliveSet k
    have hid_le : idxs.length ≤ k := by
      dsimp [idxs]
      rw [aliveIndicesUpTo_eq_take_filter]
      calc (((List.finRange edges₂.length).take k).filter _).length
        _ ≤ ((List.finRange edges₂.length).take k).length := List.length_filter_le _ _
        _ ≤ k := List.length_take_le k _
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm2_val, hk_w, hm₂_w, hk_lt, hw]
    -- 1. r_base + 4 := a_alive[r_base]
    let al_k := if jk ∈ aliveSet then 1 else 0
    have hal_w : al_k < 2 ^ w := by dsimp [al_k]; split_ifs <;> omega
    have hal_len : k < (s.arrs a_alive).length := by rw [hal.1]; exact hk_e2
    have hal_get : (s.arrs a_alive)[k]'hal_len = al_k := hal.getElem_eq_ite jk
    let s₁ := s.setReg (r_base + 4) al_k
    have hex₁ : Exec w (.assign (r_base + 4) (.read a_alive (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrk_val, hk_w, hal_len, hal_get, hal_w])
    by_cases hmem : jk ∈ aliveSet
    · have hal_eq1 : al_k = 1 := ite_eq_left_iff.mpr (fun hn => absurd hmem hn)
      have hcond_al : (Expr.op .eq (.reg (r_base + 4)) (.const 1)).eval w s₁ = some 1 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hal_eq1, hw]
      let u := (edges₂[k]'hk_e2).1
      let v := (edges₂[k]'hk_e2).2
      have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
      have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
      -- 2. r_base + 5 := a_eu[r_base]
      have heu_len : k < (s.arrs a_eu).length := by rw [hend.1]; exact hk_e2
      have heu_get : (s.arrs a_eu)[k]'heu_len = u.1 := (hend.2.2 jk).1
      let s₂ := s₁.setReg (r_base + 5) u.1
      have hex₂ : Exec w (.assign (r_base + 5) (.read a_eu (.reg r_base))) s₁ s₂ 3 :=
        .assign (by simp [s₁, Expr.eval, checkWord, hrk_val, hk_w, heu_len, heu_get, hu_w])
      -- 3. r_base + 6 := a_ev[r_base]
      have hev_len : k < (s.arrs a_ev).length := by rw [hend.2.1]; exact hk_e2
      have hev_get : (s.arrs a_ev)[k]'hev_len = v.1 := (hend.2.2 jk).2
      let s₃ := s₂.setReg (r_base + 6) v.1
      have hex₃ : Exec w (.assign (r_base + 6) (.read a_ev (.reg r_base))) s₂ s₃ 3 :=
        .assign (by simp [s₂, s₁, Expr.eval, checkWord, hrk_val, hk_w, hev_len, hev_get, hv_w])
      -- 4. r_base + 7 := a_dir[u * n + v]
      let d := if 0 < G.edgeMult u v then 1 else 0
      have hd_w : d < 2 ^ w := by dsimp [d]; split_ifs <;> omega
      have hidx_sq : u.1 * n + v.1 < n * n := mul_add_lt_sq u.2 v.2
      have hmul_w : u.1 * n < 2 ^ w := by omega
      have hidx_w : u.1 * n + v.1 < 2 ^ w := by omega
      have hdir_len₀ : u.1 * n + v.1 < (s.arrs a_dir).length := by
        rw [hdir_len]; exact hidx_sq
      have hdir_get₀ : (s.arrs a_dir)[u.1 * n + v.1]'hdir_len₀ = d := hdir_val u v
      have hrn₃ : s₃.regs r_n = n := by
        simp [s₃, s₂, s₁,
          show r_n ≠ r_base + 6 by romega,
          show r_n ≠ r_base + 5 by romega,
          show r_n ≠ r_base + 4 by romega, hrn_val]
      let s₄ := s₃.setReg (r_base + 7) d
      have hex₄ : Exec w (.assign (r_base + 7)
          (.read a_dir (.op .add (.op .mul (.reg (r_base + 5)) (.reg r_n)) (.reg (r_base + 6)))))
          s₃ s₄ 7 :=
        .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn₃,
          hu_w, hn_w, hmul_w, hv_w, hidx_w, hdir_len₀, hdir_get₀, hd_w])
      -- 5. ite on d = 1 to bufPush3
      let p_dir := liftEdgeDir G (edges₂[k]'hk_e2)
      let pfx := [n, 0] ++ G'.flatTriples (idxs.map (fun j => liftEdgeDir G (edges₂[j.1]'j.2)))
      have hpfx_len : pfx.length = 2 + 3 * idxs.length := by
        simp [pfx, MultiDigraph.length_flatTriples]; omega
      have hpos_w : pfx.length + 3 < 2 ^ w := by omega
      have hbuf₄ : s₄.arrs a_buf = pfx ++ List.replicate ((3 * rem + extra_buf) + 3) 0 := by
        have hlen_eq : 3 * (rem + 1) + extra_buf = (3 * rem + extra_buf) + 3 := by omega
        simp only [s₄, s₃, s₂, s₁, State.setReg_arrs]
        rw [← hlen_eq]
        exact hbuf
      have hrpos₄ : s₄.regs (r_base + 2) = pfx.length := by
        simp [s₄, s₃, s₂, s₁, hrpos, hpfx_len, idxs]
      have hr3_4 : s₄.regs (r_base + 3) = 1 := by simp [s₄, s₃, s₂, s₁, hr3]
      have hr5_4 : s₄.regs (r_base + 5) = u.1 := by simp [s₄, s₃, s₂]
      have hr6_4 : s₄.regs (r_base + 6) = v.1 := by simp [s₄, s₃]
      have hex_push :
          ∃ s₅ t_push,
            Exec w
              (.ite (.op .eq (.reg (r_base + 7)) (.const 1))
                (bufPush3 a_buf (r_base + 2) (r_base + 5) (r_base + 6) (r_base + 3))
                (bufPush3 a_buf (r_base + 2) (r_base + 6) (r_base + 5) (r_base + 3)))
              s₄ s₅ t_push ∧
            t_push ≤ 22 ∧
            s₅.arrs a_buf = (pfx ++ [p_dir.1.1, p_dir.2.1, 1]) ++
              List.replicate (3 * rem + extra_buf) 0 ∧
            s₅.regs (r_base + 2) = (pfx ++ [p_dir.1.1, p_dir.2.1, 1]).length ∧
            (∀ a : Arr, a ≠ a_buf → s₅.arrs a = s₄.arrs a) ∧
            (∀ r : Reg, r ≠ r_base + 2 → s₅.regs r = s₄.regs r) := by
        by_cases hmult : 0 < G.edgeMult u v
        · have hd1 : d = 1 := ite_eq_left_iff.mpr (fun hn => absurd hmult hn)
          have hp_dir : p_dir = (u, v) := by
            change liftEdgeDir G (u, v) = (u, v)
            simp [liftEdgeDir, hmult]
          have hcond_d : (Expr.op .eq (.reg (r_base + 7)) (.const 1)).eval w s₄ = some 1 := by
            simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hd1, hw]
          rcases bufPush3_exec a_buf (r_base + 2) (r_base + 5) (r_base + 6) (r_base + 3)
              pfx (3 * rem + extra_buf) u.1 v.1 1 hw3 hpos_w hu_w hv_w hw
              hbuf₄ hrpos₄ hr5_4 hr6_4 hr3_4 with
            ⟨s₅, t₅, hex₅, ht₅, hbuf₅, hrpos₅, harr₅, hreg₅⟩
          exact ⟨s₅, 3 + t₅, .ite_true hcond_d (by omega) hex₅, by omega,
            by simpa [hp_dir] using hbuf₅, by simpa [hp_dir] using hrpos₅, harr₅, hreg₅⟩
        · have hd0 : d = 0 := ite_eq_right_iff.mpr (fun hp => absurd hp hmult)
          have hp_dir : p_dir = (v, u) := by
            change liftEdgeDir G (u, v) = (v, u)
            simp [liftEdgeDir, hmult]
          have hcond_d : (Expr.op .eq (.reg (r_base + 7)) (.const 1)).eval w s₄ = some 0 := by
            simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hd0, h0_w, hw]
          rcases bufPush3_exec a_buf (r_base + 2) (r_base + 6) (r_base + 5) (r_base + 3)
              pfx (3 * rem + extra_buf) v.1 u.1 1 hw3 hpos_w hv_w hu_w hw
              hbuf₄ hrpos₄ hr6_4 hr5_4 hr3_4 with
            ⟨s₅, t₅, hex₅, ht₅, hbuf₅, hrpos₅, harr₅, hreg₅⟩
          exact ⟨s₅, 3 + t₅, .ite_false hcond_d hex₅, by omega,
            by simpa [hp_dir] using hbuf₅, by simpa [hp_dir] using hrpos₅, harr₅, hreg₅⟩
      rcases hex_push with ⟨s₅, t_push, hex₅, ht_push, hbuf₅, hrpos₅, harr₅, hreg₅⟩
      -- 6. r_base + 8 := a_tau0[r_base]
      let l_k := (f_tau jk).1
      have hlk_w : l_k < 2 ^ w := Nat.lt_trans (f_tau jk).2 ht₀_w
      have htau_len₅ : k < (s₅.arrs a_tau0).length := by
        rw [harr₅ a_tau0 hne_tau_buf]
        simp only [s₄, s₃, s₂, s₁, State.setReg_arrs]
        rw [htau.1]; exact hk_e2
      have htau_get₅ : (s₅.arrs a_tau0)[k]'htau_len₅ = l_k := by
        simp only [harr₅ a_tau0 hne_tau_buf, s₄, s₃, s₂, s₁, State.setReg_arrs]
        exact htau.2 jk
      have hrk₅ : s₅.regs r_base = k := by
        rw [hreg₅ r_base (by romega)]; simp [s₄, s₃, s₂, s₁, hrk_val]
      let s₆ := s₅.setReg (r_base + 8) l_k
      have hex₆ : Exec w (.assign (r_base + 8) (.read a_tau0 (.reg r_base))) s₅ s₆ 3 :=
        .assign (by simp [Expr.eval, checkWord, hrk₅, hk_w, htau_len₅, htau_get₅, hlk_w])
      -- 7. write a_sig_buf (r_base + 1) (r_base + 8)
      have hrm_acc₆ : s₆.regs (r_base + 1) = idxs.length := by
        simp only [s₆, State.setReg_regs_ne _ _ (by romega : r_base + 1 ≠ r_base + 8)]
        rw [hreg₅ (r_base + 1) (by romega)]
        simp [s₄, s₃, s₂, s₁, hrm_acc, idxs]
      have hid_w : idxs.length < 2 ^ w := by omega
      have hid_succ_w : idxs.length + 1 < 2 ^ w := by omega
      have hsig₆ : s₆.arrs a_sig_buf =
          (idxs.map (fun j => (f_tau j).1)) ++ List.replicate ((rem + extra_sig) + 1) 0 := by
        simp only [s₆, State.setReg_arrs]
        rw [harr₅ a_sig_buf hne_buf_sig.symm]
        have hlen_eq : rem + 1 + extra_sig = (rem + extra_sig) + 1 := by omega
        simp only [s₄, s₃, s₂, s₁, State.setReg_arrs]
        rw [← hlen_eq]
        exact hsig
      have hlen_sig₆ : idxs.length < (s₆.arrs a_sig_buf).length := by simp [hsig₆]
      let s₇ := s₆.writeArr a_sig_buf idxs.length l_k
      have hex₇ : Exec w (.write a_sig_buf (.reg (r_base + 1)) (.reg (r_base + 8))) s₆ s₇ 3 :=
        .write (by simp [Expr.eval, checkWord, hrm_acc₆, hid_w])
          (by simp [s₆, Expr.eval, checkWord, hlk_w]) hlen_sig₆
      -- 8. r_base + 1 := r_base + 1 + 1
      let s₈ := s₇.setReg (r_base + 1) (idxs.length + 1)
      have hex₈ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₇ s₈ 4 :=
        .assign (by simp [s₇, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm_acc₆,
          hid_w, hw, hid_succ_w])
      -- 9. loop increment r_base := r_base + 1
      have hrk₈ : s₈.regs r_base = k := by
        simp [s₈, s₇, s₆, hrk₅]
      let s₉ := s₈.setReg r_base (k + 1)
      have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₈ s₉ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₈, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hex_body : Exec w
          (liftSubgraphBody a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf r_n r_base)
          s s₈ (3 + (3 + (3 + (3 + (7 + (t_push + (3 + (3 + 4)))))))) :=
        .seq hex₁ (.ite_true hcond_al (by omega)
          (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))))
      -- Prove that `[p_dir.1.1, p_dir.2.1, 1] = G'.flatTriples [p_dir]`
      have hp_in_H₃ : edges₂[k]'hk_e2 ∈ edgeListOf H₃ := by
        rw [edgeListOf_graphOfAlive_eq, List.mem_map]
        exact ⟨jk, (mem_aliveIndicesUpTo aliveSet edges₂.length jk).mpr ⟨hk_e2, hmem⟩, rfl⟩
      have hp_dir_in : p_dir ∈ G'.activePairsList := by
        rw [activePairsList_liftSimpleSubgraph G H₃ hH₃_le, List.mem_map]
        exact ⟨edges₂[k]'hk_e2, hp_in_H₃, rfl⟩
      have hmult_G' : G'.edgeMult p_dir.1 p_dir.2 = 1 :=
        edgeMult_eq_one_of_mem_activePairsList_liftSimpleSubgraph G H₃ hH₃_le hp_dir_in
      have hflat_one : [p_dir.1.1, p_dir.2.1, 1] = G'.flatTriples [p_dir] := by
        simp [MultiDigraph.flatTriples, hmult_G']
      have hid_succ : aliveIndicesUpTo aliveSet (k + 1) = idxs ++ [jk] := by
        rw [aliveIndicesUpTo_succ aliveSet hk_e2,
            ite_eq_left_iff.mpr (fun hn => absurd hmem hn)]
      have hbuf₉ : s₉.arrs a_buf =
          ([n, 0] ++ G'.flatTriples
            ((aliveIndicesUpTo aliveSet (k + 1)).map (fun j => liftEdgeDir G (edges₂[j.1]'j.2)))) ++
            List.replicate (3 * rem + extra_buf) 0 := by
        simp only [s₉, s₈, s₇, s₆, State.setReg_arrs,
          State.writeArr_arrs_ne _ _ _ hne_buf_sig, hbuf₅]
        rw [hid_succ, List.map_append, List.map_singleton, G'.flatTriples_append, ← hflat_one]
        simp [pfx, List.append_assoc]
      have hsig₉ : s₉.arrs a_sig_buf =
          ((aliveIndicesUpTo aliveSet (k + 1)).map (fun j => (f_tau j).1)) ++
            List.replicate (rem + extra_sig) 0 := by
        simp only [s₉, s₈, s₇, State.setReg_arrs, State.writeArr_arrs_self, hsig₆]
        have hlen_map : (idxs.map (fun j => (f_tau j).1)).length = idxs.length := by simp
        rw [← hlen_map, set_append_replicate_succ (idxs.map (fun j => (f_tau j).1)) (rem + extra_sig) l_k,
            hid_succ, List.map_append, List.map_singleton]
      have harr₉ : ∀ a : Arr, a ≠ a_buf → a ≠ a_sig_buf → s₉.arrs a = s.arrs a := by
        intro a hab has
        simp only [s₉, s₈, s₇, s₆, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ has]
        rw [harr₅ a hab]
        simp [s₄, s₃, s₂, s₁]
      rcases ih (k + 1) extra_buf extra_sig (by omega) (s := s₉)
          (hend.of_arrs_eq (harr₉ a_eu hne_eu_buf hne_eu_sig) (harr₉ a_ev hne_ev_buf hne_ev_sig))
          (hal.of_arr_eq (harr₉ a_alive hne_al_buf hne_al_sig))
          (htau.of_arr_eq (harr₉ a_tau0 hne_tau_buf hne_tau_sig))
          (by rw [harr₉ a_dir hne_dir_buf hne_dir_sig, hdir_len])
          (fun u v => by simp only [harr₉ a_dir hne_dir_buf hne_dir_sig]; exact hdir_val u v)
          hbuf₉ hsig₉
          (by
            simp only [s₉, s₈, s₇, s₆,
              State.setReg_regs_ne _ _ (by romega : r_n ≠ r_base),
              State.setReg_regs_ne _ _ (by romega : r_n ≠ r_base + 1),
              State.setReg_regs_ne _ _ (by romega : r_n ≠ r_base + 8),
              State.writeArr_regs]
            rw [hreg₅ r_n (by romega)]
            simp [s₄, show r_n ≠ r_base + 7 by romega, hrn₃])
          (by
            simp only [s₉, s₈, s₇, s₆,
              State.setReg_regs_ne _ _ (by romega : r_m2 ≠ r_base),
              State.setReg_regs_ne _ _ (by romega : r_m2 ≠ r_base + 1),
              State.setReg_regs_ne _ _ (by romega : r_m2 ≠ r_base + 8),
              State.writeArr_regs]
            rw [hreg₅ r_m2 (by romega)]
            simp [s₄, s₃, s₂, s₁,
              show r_m2 ≠ r_base + 7 by romega,
              show r_m2 ≠ r_base + 6 by romega,
              show r_m2 ≠ r_base + 5 by romega,
              show r_m2 ≠ r_base + 4 by romega, hrm2_val])
          (by simp [s₉])
          (by simp [s₉, s₈, hid_succ])
          (by
            simp only [s₉, s₈, s₇, s₆,
              State.setReg_regs_ne _ _ (by romega : r_base + 2 ≠ r_base),
              State.setReg_regs_ne _ _ (by romega : r_base + 2 ≠ r_base + 1),
              State.setReg_regs_ne _ _ (by romega : r_base + 2 ≠ r_base + 8),
              State.writeArr_regs, hrpos₅]
            rw [hid_succ]
            simp [pfx, MultiDigraph.length_flatTriples]; omega)
          (by
            simp only [s₉, s₈, s₇, s₆,
              State.setReg_regs_ne _ _ (by romega : r_base + 3 ≠ r_base),
              State.setReg_regs_ne _ _ (by romega : r_base + 3 ≠ r_base + 1),
              State.setReg_regs_ne _ _ (by romega : r_base + 3 ≠ r_base + 8),
              State.writeArr_regs]
            rw [hreg₅ (r_base + 3) (by romega)]
            exact hr3_4) with
        ⟨s₁₀, t₁₀, extra_buf', extra_sig', hex₁₀, ht₁₀, hbuf₁₀, hsig₁₀, hrm₁₀, hrpos₁₀, harr₁₀, hreg₁₀⟩
      refine ⟨s₁₀, 3 + ((3 + (3 + (3 + (3 + (7 + (t_push + (3 + (3 + 4)))))))) + 4) + t₁₀,
        extra_buf', extra_sig',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₁₀,
        by omega, hbuf₁₀, hsig₁₀, hrm₁₀, hrpos₁₀,
        fun a hab has => (harr₁₀ a hab has).trans (harr₉ a hab has),
        fun r hr => by
          rw [hreg₁₀ r hr]
          simp only [s₉, s₈, s₇, s₆,
            State.setReg_regs_ne _ _ (by romega : r ≠ r_base),
            State.setReg_regs_ne _ _ (by romega : r ≠ r_base + 1),
            State.setReg_regs_ne _ _ (by romega : r ≠ r_base + 8),
            State.writeArr_regs]
          rw [hreg₅ r (by romega)]
          simp [s₄, s₃, s₂, s₁,
            show r ≠ r_base + 7 by romega,
            show r ≠ r_base + 6 by romega,
            show r ≠ r_base + 5 by romega,
            show r ≠ r_base + 4 by romega]⟩
    · have hal_eq0 : al_k = 0 := ite_eq_right_iff.mpr (fun hp => absurd hp hmem)
      have hcond_al : (Expr.op .eq (.reg (r_base + 4)) (.const 1)).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hal_eq0, h0_w, hw]
      have hex_body : Exec w
          (liftSubgraphBody a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf r_n r_base)
          s s₁ (3 + (3 + 1)) :=
        .seq hex₁ (.ite_false hcond_al (.skip s₁))
      let s₂ := s₁.setReg r_base (k + 1)
      have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₁ s₂ 4 :=
        .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hid_succ : aliveIndicesUpTo aliveSet (k + 1) = idxs := by
        rw [aliveIndicesUpTo_succ aliveSet hk_e2,
            ite_eq_right_iff.mpr (fun hp => absurd hp hmem), List.append_nil]
      have hbuf₂ : s₂.arrs a_buf =
          ([n, 0] ++ G'.flatTriples
            ((aliveIndicesUpTo aliveSet (k + 1)).map (fun j => liftEdgeDir G (edges₂[j.1]'j.2)))) ++
            List.replicate (3 * rem + (extra_buf + 3)) 0 := by
        have hlen_eq : 3 * (rem + 1) + extra_buf = 3 * rem + (extra_buf + 3) := by omega
        simp only [s₂, s₁, State.setReg_arrs]
        rw [hid_succ, ← hlen_eq]
        exact hbuf
      have hsig₂ : s₂.arrs a_sig_buf =
          ((aliveIndicesUpTo aliveSet (k + 1)).map (fun j => (f_tau j).1)) ++
            List.replicate (rem + (extra_sig + 1)) 0 := by
        have hlen_eq : (rem + 1) + extra_sig = rem + (extra_sig + 1) := by omega
        simp only [s₂, s₁, State.setReg_arrs]
        rw [hid_succ, ← hlen_eq]
        exact hsig
      rcases ih (k + 1) (extra_buf + 3) (extra_sig + 1) (by omega) (s := s₂)
          (hend.of_arrs_eq rfl rfl)
          (hal.of_arr_eq rfl)
          (htau.of_arr_eq rfl)
          hdir_len hdir_val hbuf₂ hsig₂
          (by
            dsimp [Reg] at hr_n
            simp [s₂, s₁, State.setReg,
              show (r_n : Reg) ≠ r_base by dsimp [Reg]; omega,
              show (r_n : Reg) ≠ r_base + 4 by dsimp [Reg]; omega, hrn_val])
          (by
            dsimp [Reg] at hr_m2
            simp [s₂, s₁, State.setReg,
              show (r_m2 : Reg) ≠ r_base by dsimp [Reg]; omega,
              show (r_m2 : Reg) ≠ r_base + 4 by dsimp [Reg]; omega, hrm2_val])
          (by simp [s₂])
          (by rw [hid_succ]; simp [s₂, s₁, hrm_acc, idxs])
          (by rw [hid_succ]; simp [s₂, s₁, hrpos, idxs])
          (by simp [s₂, s₁, hr3]) with
        ⟨s₃, t₃, extra_buf', extra_sig', hex₃, ht₃, hbuf₃, hsig₃, hrm₃, hrpos₃, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + ((3 + (3 + 1)) + 4) + t₃, extra_buf', extra_sig',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by omega, hbuf₃, hsig₃, hrm₃, hrpos₃,
        fun a hab has => harr₃ a hab has,
        fun r hr => by
          dsimp [Reg] at hr
          rw [hreg₃ r hr]
          simp [s₂, s₁, State.setReg,
            show (r : Reg) ≠ r_base by dsimp [Reg]; omega,
            show (r : Reg) ≠ r_base + 4 by dsimp [Reg]; omega]⟩

theorem liftSubgraphProg_exec {w n t₀ : ℕ} (G : MultiDigraph n) (m₂ : ℕ)
    (aliveSet : Finset (Fin ((edgeListOf G.toSimpleGraph).take m₂).length))
    (f_tau : Fin ((edgeListOf G.toSimpleGraph).take m₂).length → Fin t₀)
    (a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf a_G_out a_sigma : Arr)
    (r_n r_m2 r_m_out r_base : Reg)
    (hne_eu_buf : a_eu ≠ a_buf) (hne_eu_sig : a_eu ≠ a_sig_buf)
    (hne_ev_buf : a_ev ≠ a_buf) (hne_ev_sig : a_ev ≠ a_sig_buf)
    (hne_al_buf : a_alive ≠ a_buf) (hne_al_sig : a_alive ≠ a_sig_buf)
    (hne_tau_buf : a_tau0 ≠ a_buf) (hne_tau_sig : a_tau0 ≠ a_sig_buf)
    (hne_dir_buf : a_dir ≠ a_buf) (hne_dir_sig : a_dir ≠ a_sig_buf)
    (hne_buf_sig : a_buf ≠ a_sig_buf)
    (hne_buf_G : a_buf ≠ a_G_out) (hne_sig_G : a_sig_buf ≠ a_G_out)
    (hne_sig_out : a_sig_buf ≠ a_sigma) (hne_G_sig : a_G_out ≠ a_sigma)
    (hr_n : r_n < r_base) (hr_m2 : r_m2 < r_base) (hr_m_out : r_m_out < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm2_3_w : 2 + 3 * m₂ < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (hlen_e2 : ((edgeListOf G.toSimpleGraph).take m₂).length = m₂)
    {s : State}
    (hend : IsEndpointArrs ((edgeListOf G.toSimpleGraph).take m₂) a_eu a_ev s)
    (hal : IsBitSet aliveSet a_alive s)
    (htau : IsTauArr f_tau a_tau0 s)
    (hdir_len : (s.arrs a_dir).length = n * n)
    (hdir_val : ∀ u v : Fin n,
      (s.arrs a_dir)[u.1 * n + v.1]'(by rw [hdir_len]; exact mul_add_lt_sq u.2 v.2) =
        if 0 < G.edgeMult u v then 1 else 0)
    (hrn_val : s.regs r_n = n)
    (hrm2_val : s.regs r_m2 = m₂) :
    let edges₂ := (edgeListOf G.toSimpleGraph).take m₂
    let hloop₂ := take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂
    let H₃ := graphOfAlive edges₂ hloop₂ aliveSet
    let G' := liftSimpleSubgraph G H₃
    let idxList := aliveIndicesUpTo aliveSet edges₂.length
    have hlen_G' : G'.numEdges = idxList.length := by
      rw [numEdges_liftSimpleSubgraph G H₃
            ((graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet).trans
              (graphOfEdgeList_take_le (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)),
          edgeListOf_graphOfAlive_eq, List.length_map]
    ∃ s' t,
      Exec w (liftSubgraphProg a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf a_G_out a_sigma
        r_n r_m2 r_m_out r_base) s s' t ∧
      t ≤ 130 * m₂ + 90 ∧
      s'.arrs a_G_out = G'.enc ∧
      (s'.arrs a_sigma).length = G'.numEdges ∧
      (∀ e : Fin G'.numEdges, (he : e.1 < (s'.arrs a_sigma).length) →
        (s'.arrs a_sigma)[e.1]'he = (f_tau (idxList[e.1]'(by rw [← hlen_G']; exact e.2))).1) ∧
      s'.regs r_m_out = G'.numEdges ∧
      (∀ a : Arr, a ≠ a_buf → a ≠ a_sig_buf → a ≠ a_G_out → a ≠ a_sigma →
        s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_m_out → s'.regs r = s.regs r) := by
  intro edges₂ hloop₂ H₃ G' idxList hlen_G'
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm₂_w : m₂ < 2 ^ w := by omega
  have h3m₂_w : 3 * m₂ < 2 ^ w := by omega
  have hH₃_le : H₃ ≤ G.toSimpleGraph :=
    (graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet).trans
      (graphOfEdgeList_take_le (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)
  -- 1. r_base + 2 := 2 + 3 * r_m2
  let s₁ := s.setReg (r_base + 2) (2 + 3 * m₂)
  have hex₁ : Exec w (.assign (r_base + 2) (.op .add (.const 2) (.op .mul (.const 3) (.reg r_m2))))
      s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm2_val,
      hw2, hw3, hm₂_w, h3m₂_w, hm2_3_w])
  -- 2. alloc a_buf (r_base + 2)
  let s₂ := s₁.setArr a_buf (List.replicate (2 + 3 * m₂) 0)
  have hex₂ : Exec w (.alloc a_buf (.reg (r_base + 2))) s₁ s₂ (1 + (2 + 3 * m₂)) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hm2_3_w])
  -- 3. write a_buf 0 r_n
  have hrn₂ : s₂.regs r_n = n := by
    dsimp [Reg] at hr_n
    simp [s₂, s₁, State.setReg, show (r_n : Reg) ≠ r_base + 2 by dsimp [Reg]; omega, hrn_val]
  let s₃ := s₂.writeArr a_buf 0 n
  have hex₃ : Exec w (.write a_buf (.const 0) (.reg r_n)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hrn₂, hn_w])
      (by simp [s₂])
  -- 4. alloc a_sig_buf r_m2
  have hrm2_3 : s₃.regs r_m2 = m₂ := by
    dsimp [Reg] at hr_m2
    simp [s₃, s₂, s₁, State.setReg, show (r_m2 : Reg) ≠ r_base + 2 by dsimp [Reg]; omega, hrm2_val]
  let s₄ := s₃.setArr a_sig_buf (List.replicate m₂ 0)
  have hex₄ : Exec w (.alloc a_sig_buf (.reg r_m2)) s₃ s₄ (1 + m₂) :=
    .alloc (by simp [Expr.eval, checkWord, hrm2_3, hm₂_w])
  -- 5..8. assign r_base := 0, r_base + 1 := 0, r_base + 2 := 2, r_base + 3 := 1
  let s₅ := s₄.setReg r_base 0
  have hex₅ : Exec w (.assign r_base (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg (r_base + 1) 0
  have hex₆ : Exec w (.assign (r_base + 1) (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₇ := s₆.setReg (r_base + 2) 2
  have hex₇ : Exec w (.assign (r_base + 2) (.const 2)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  let s₈ := s₇.setReg (r_base + 3) 1
  have hex₈ : Exec w (.assign (r_base + 3) (.const 1)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  -- 9. liftSubgraphLoop_exec
  have harr₈ : ∀ a : Arr, a ≠ a_buf → a ≠ a_sig_buf → s₈.arrs a = s.arrs a := by
    intro a hab has
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hab, has]
  have hbuf₈ : s₈.arrs a_buf =
      ([n, 0] ++ G'.flatTriples
        ((aliveIndicesUpTo aliveSet 0).map (fun j => liftEdgeDir G (edges₂[j.1]'j.2)))) ++
        List.replicate (3 * m₂ + 0) 0 := by
    simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂,
      State.setReg_arrs, State.setArr_arrs_ne _ _ hne_buf_sig,
      State.writeArr_arrs_self, State.setArr_arrs_self,
      aliveIndicesUpTo_zero, List.map_nil,
      MultiDigraph.flatTriples, List.append_nil, Nat.add_zero]
    have hrep : 2 + 3 * m₂ = 1 + (1 + 3 * m₂) := by omega
    rw [hrep, List.replicate_add, List.replicate_add]
    rfl
  have hsig₈ : s₈.arrs a_sig_buf =
      ((aliveIndicesUpTo aliveSet 0).map (fun j => (f_tau j).1)) ++ List.replicate (m₂ + 0) 0 := by
    simp [s₈, s₇, s₆, s₅, s₄]
  rcases liftSubgraphLoop_exec G m₂ aliveSet f_tau a_eu a_ev a_alive a_tau0 a_dir a_buf a_sig_buf
      r_n r_m2 r_base hne_eu_buf hne_eu_sig hne_ev_buf hne_ev_sig hne_al_buf hne_al_sig
      hne_tau_buf hne_tau_sig hne_dir_buf hne_dir_sig hne_buf_sig hr_n hr_m2
      hw3 hn_w hn2_w hm2_3_w ht₀_w hlen_e2 m₂ 0 0 0 (by omega) (s := s₈)
      (hend.of_arrs_eq (harr₈ a_eu hne_eu_buf hne_eu_sig) (harr₈ a_ev hne_ev_buf hne_ev_sig))
      (hal.of_arr_eq (harr₈ a_alive hne_al_buf hne_al_sig))
      (htau.of_arr_eq (harr₈ a_tau0 hne_tau_buf hne_tau_sig))
      (by rw [harr₈ a_dir hne_dir_buf hne_dir_sig, hdir_len])
      (fun u v => by simp only [harr₈ a_dir hne_dir_buf hne_dir_sig]; exact hdir_val u v)
      hbuf₈ hsig₈
      (by
        dsimp [Reg] at hr_n
        simp [s₈, s₇, s₆, s₅, s₄, s₃, State.setReg,
          show (r_n : Reg) ≠ r_base + 3 by dsimp [Reg]; omega,
          show (r_n : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
          show (r_n : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
          show (r_n : Reg) ≠ r_base by dsimp [Reg]; omega, hrn₂])
      (by
        dsimp [Reg] at hr_m2
        simp [s₈, s₇, s₆, s₅, s₄, State.setReg,
          show (r_m2 : Reg) ≠ r_base + 3 by dsimp [Reg]; omega,
          show (r_m2 : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
          show (r_m2 : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
          show (r_m2 : Reg) ≠ r_base by dsimp [Reg]; omega, hrm2_3])
      (by simp [s₈, s₇, s₆, s₅])
      (by simp [s₈, s₇, s₆])
      (by simp [s₈, s₇])
      (by simp [s₈]) with
    ⟨s₉, t₉, extra_buf', extra_sig', hex₉, ht₉, hbuf₉, hsig₉, hrm₉, hrpos₉, harr₉, hreg₉⟩
  -- Relate `aliveIndicesUpTo aliveSet m₂` to `idxList` and `G'.activePairsList`
  have hidx_eq : aliveIndicesUpTo aliveSet m₂ = idxList :=
    congrArg (aliveIndicesUpTo aliveSet) hlen_e2.symm
  rw [hidx_eq] at hbuf₉ hsig₉ hrm₉ hrpos₉
  have hapl_G' : idxList.map (fun j => liftEdgeDir G (edges₂[j.1]'j.2)) = G'.activePairsList := by
    rw [activePairsList_liftSimpleSubgraph G H₃ hH₃_le,
        edgeListOf_graphOfAlive_eq G.toSimpleGraph m₂ aliveSet, List.map_map]
    rfl
  have hm'_G' : G'.numActivePairs = idxList.length := by
    unfold MultiDigraph.numActivePairs
    rw [← hapl_G', List.length_map]
  have hid_le_m2 : idxList.length ≤ m₂ := by
    rw [← hidx_eq, aliveIndicesUpTo_eq_take_filter]
    calc (((List.finRange edges₂.length).take m₂).filter _).length
      _ ≤ ((List.finRange edges₂.length).take m₂).length := List.length_filter_le _ _
      _ ≤ m₂ := List.length_take_le m₂ _
  have hid_w : idxList.length < 2 ^ w := by omega
  -- 10. write a_buf 1 (r_base + 1)
  let s₁₀ := s₉.writeArr a_buf 1 idxList.length
  have hex₁₀ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₉ s₁₀ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hrm₉, hid_w])
      (by simp [hbuf₉])
  have hbuf₉' : s₉.arrs a_buf =
      ([n, 0] ++ G'.flatTriples G'.activePairsList) ++ List.replicate extra_buf' 0 := by
    rw [← hapl_G']
    exact hbuf₉
  have hbuf₁₀ : s₁₀.arrs a_buf = [] ++ G'.enc ++ List.replicate extra_buf' 0 := by
    simp only [s₁₀, State.writeArr_arrs_self, hbuf₉', ← hm'_G', MultiDigraph.enc]
    rfl
  -- 11. assign r_m_out (r_base + 1)
  let s₁₁ := s₁₀.setReg r_m_out idxList.length
  have hex₁₁ : Exec w (.assign r_m_out (.reg (r_base + 1))) s₁₀ s₁₁ 2 :=
    .assign (by simp [s₁₀, Expr.eval, checkWord, hrm₉, hid_w])
  have hbuf₁₁ : s₁₁.arrs a_buf = [] ++ G'.enc ++ List.replicate extra_buf' 0 := hbuf₁₀
  -- 12. readSliceProg a_buf 0 a_G_out (r_base + 2) (r_base + 4)
  have hlen_enc_G' : G'.enc.length = 2 + 3 * idxList.length := by
    rw [G'.length_enc, hm'_G']
  have hrpos₁₁ : s₁₁.regs (r_base + 2) = G'.enc.length := by
    dsimp [Reg] at hr_m_out
    simp [s₁₁, s₁₀, State.setReg,
      show (r_base + 2 : Reg) ≠ r_m_out by dsimp [Reg]; omega, hrpos₉, hlen_enc_G']
  have henc_G'_w : ∀ x ∈ G'.enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · rw [hm'_G']; exact hid_w
    · exact all_lt_flatTriples G' G'.activePairsList hn_w
        (fun p hp => by
          rw [edgeMult_eq_one_of_mem_activePairsList_liftSimpleSubgraph G H₃ hH₃_le hp]
          exact hw) x hx
  rcases readSliceProg_exec a_buf a_G_out (.const 0) (r_base + 2) (r_base + 4)
      hne_buf_G (by omega) [] G'.enc (List.replicate extra_buf' 0)
      rfl rfl henc_G'_w hw (by simp [hlen_enc_G']; omega)
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₁₁ hrpos₁₁ with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hG_out₁₂, harr₁₂, hreg₁₂⟩
  -- 13. readSliceProg a_sig_buf 0 a_sigma r_m_out (r_base + 4)
  let sigList := idxList.map (fun j => (f_tau j).1)
  have hsig_len : sigList.length = idxList.length := by simp [sigList]
  have hsig_w : ∀ x ∈ sigList, x < 2 ^ w := by
    intro x hx
    rw [List.mem_map] at hx
    rcases hx with ⟨j, _, rfl⟩
    exact Nat.lt_trans (f_tau j).2 ht₀_w
  have hsig₁₂ : s₁₂.arrs a_sig_buf = [] ++ sigList ++ List.replicate extra_sig' 0 := by
    rw [harr₁₂ a_sig_buf hne_sig_G]
    simp [s₁₁, s₁₀, hne_buf_sig.symm, hsig₉, sigList]
  have hrm_out₁₂ : s₁₂.regs r_m_out = sigList.length := by
    dsimp [Reg] at hr_m_out
    rw [hreg₁₂ r_m_out (by omega)]
    simp [s₁₁, hsig_len]
  rcases readSliceProg_exec a_sig_buf a_sigma (.const 0) r_m_out (r_base + 4)
      hne_sig_out (by dsimp [Reg] at hr_m_out ⊢; omega) [] sigList (List.replicate extra_sig' 0)
      rfl rfl hsig_w hw (by simp [hsig_len]; omega)
      (by simp [Expr.eval, checkWord, h0_w])
      hsig₁₂ hrm_out₁₂ with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hsig_out₁₃, harr₁₃, hreg₁₃⟩
  dsimp only [Expr.cost] at ht₁₂ ht₁₃
  rw [hlen_enc_G'] at ht₁₂
  rw [hsig_len] at ht₁₃
  refine ⟨s₁₃, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
      (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ hex₁₃))))))))))),
    by omega,
    by rw [harr₁₃ a_G_out hne_G_sig, hG_out₁₂],
    by rw [hsig_out₁₃, hsig_len, hlen_G'],
    fun e he => by
      simp only [hsig_out₁₃, sigList, List.getElem_map],
    by
      dsimp [Reg] at hr_m_out
      rw [hreg₁₃ r_m_out (by omega), hrm_out₁₂, hsig_len, hlen_G'],
    fun a hab has hag hasig => by
      rw [harr₁₃ a hasig, harr₁₂ a hag]
      change (s₉.writeArr a_buf 1 idxList.length).arrs a = s.arrs a
      rw [State.writeArr_arrs_ne _ _ _ hab]
      exact (harr₉ a hab has).trans (harr₈ a hab has),
    fun r hr hr_ne => by
      dsimp [Reg] at hr hr_ne
      rw [hreg₁₃ r (by omega), hreg₁₂ r (by omega)]
      change ((s₉.writeArr a_buf 1 idxList.length).setReg r_m_out idxList.length).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ hr_ne, State.writeArr_regs, hreg₉ r hr]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base + 3 by dsimp [Reg]; omega,
        show (r : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
        show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
        show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

/-! ### Section 5.3: Small Simple Graph Pass-2 Initialization and Parent Copy -/

/-- Initialize `a_par` of length `2 * m` (`[0, 0, ...]`), `a_sigma` of length `m` representing
`smallInitSigma m` (`[0, 1, 1, ...]`), and `r_t := 2` for the small-simple-graph case
(`m₁ ≤ 1` and `2 ≤ m`). -/
def initSmallPass2Prog (a_par a_sigma : Arr) (r_m r_t r_base : Reg) : Cmd :=
  .seq (.alloc a_par (.op .mul (.const 2) (.reg r_m)))
    (.seq (.assign r_base (.const 1))
      (.seq (fillArrProg a_sigma r_m r_base (r_base + 1))
        (.seq (.write a_sigma (.const 0) (.const 0))
          (.assign r_t (.const 2)))))

theorem initSmallPass2Prog_exec {w m : ℕ} (a_par a_sigma : Arr) (r_m r_t r_base : Reg)
    (hne_ps : a_par ≠ a_sigma)
    (hr_m : r_m < r_base) (_hr_t : r_t < r_base) (hne_mt : r_m ≠ r_t)
    (hm_ge2 : 2 ≤ m) (hw2 : 2 < 2 ^ w) (h2m_w : 2 * m < 2 ^ w)
    {s : State}
    (hrm : s.regs r_m = m) :
    ∃ s' t,
      Exec w (initSmallPass2Prog a_par a_sigma r_m r_t r_base) s s' t ∧
      t ≤ 13 * m + 16 ∧
      (s'.arrs a_par).length = 2 * m ∧
      (∀ z < 2, (hz : z < (s'.arrs a_par).length) → (s'.arrs a_par)[z]'hz = 0) ∧
      ∃ (hsig'_len : (s'.arrs a_sigma).length = m),
      (∀ e : Fin m, (s'.arrs a_sigma)[e.1]'(by rw [hsig'_len]; exact e.2) =
        (smallInitSigma m e).1) ∧
      s'.regs r_t = 2 ∧
      s'.regs r_m = m ∧
      (∀ a : Arr, a ≠ a_par → a ≠ a_sigma → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_t → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  -- 1. alloc a_par (2 * r_m)
  let s₁ := s.setArr a_par (List.replicate (2 * m) 0)
  have hex₁ : Exec w (.alloc a_par (.op .mul (.const 2) (.reg r_m))) s s₁ (3 + 2 * m) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, hw2, hm_w, h2m_w])
  -- 2. r_base := 1
  let s₂ := s₁.setReg r_base 1
  have hex₂ : Exec w (.assign r_base (.const 1)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  -- 3. fillArrProg a_sigma r_m r_base (r_base + 1)
  have hrm₂ : s₂.regs r_m = m := by
    dsimp [Reg] at hr_m
    simp [s₂, s₁, State.setReg, show (r_m : Reg) ≠ r_base by dsimp [Reg]; omega, hrm]
  rcases fillArrProg_exec a_sigma r_m r_base (r_base + 1)
      (by romega) (by romega) hw hm_w hw (s := s₂)
      hrm₂ (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hsig₃, harr₃, hreg₃⟩
  -- 4. write a_sigma 0 0
  have hlen_sig₃ : 0 < (s₃.arrs a_sigma).length := by rw [hsig₃, List.length_replicate]; omega
  let s₄ := s₃.writeArr a_sigma 0 0
  have hex₄ : Exec w (.write a_sigma (.const 0) (.const 0)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w]) hlen_sig₃
  -- 5. assign r_t 2
  let s₅ := s₄.setReg r_t 2
  have hex₅ : Exec w (.assign r_t (.const 2)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  have hpar₅ : s₅.arrs a_par = List.replicate (2 * m) 0 := by
    simp only [s₅, s₄, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ hne_ps]
    rw [harr₃ a_par hne_ps]
    simp [s₂, s₁]
  have hsig₅_len : (s₅.arrs a_sigma).length = m := by
    simp [s₅, s₄, hsig₃]
  refine ⟨s₅, (3 + 2 * m) + (2 + (t₃ + (3 + 2))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    by rw [hpar₅, List.length_replicate],
    fun z _ hz => by simp [hpar₅],
    hsig₅_len,
    fun e => by
      simp only [s₅, s₄, State.setReg_arrs, State.writeArr_arrs_self, hsig₃, smallInitSigma]
      by_cases he0 : e.1 = 0
      · simp [he0]
      · rw [List.getElem_set_ne (by omega : 0 ≠ e.1)]
        simp [he0],
    by simp [s₅],
    by
      dsimp [Reg] at hr_m hne_mt
      simp only [s₅, s₄, State.setReg_regs_ne _ _ hne_mt, State.writeArr_regs]
      rw [hreg₃ r_m (by dsimp [Reg]; omega)]
      exact hrm₂,
    fun a hap has => by
      simp only [s₅, s₄, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ has]
      rw [harr₃ a has]
      simp [s₂, s₁, hap],
    fun r hr hrt_ne => by
      dsimp [Reg] at hr hrt_ne
      simp only [s₅, s₄, State.setReg_regs_ne _ _ hrt_ne, State.writeArr_regs]
      rw [hreg₃ r (by dsimp [Reg]; omega)]
      simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

/-! ### Section 5.4: `buildLeafMatProg` and `expandSigmaProg` -/

/-- Loop invariant for `buildLeafMatLoop` after `k` simple edges of `edges₁` have been processed. -/
def LeafMatLoopInv {n t₀ : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (edges₁ : List (Fin n × Fin n)) (ht₀_pos : 0 < t₀)
    (f_tau : Fin edges₁.length → Fin t₀) (k : ℕ) (lmat : Fin n → Fin n → Fin t₀) : Prop :=
  let τ₀ := tauOfArr edges₁ t₀ ht₀_pos f_tau
  (∀ i : Fin edges₁.length, i.1 < k →
    lmat (edges₁[i.1]'i.2).1 (edges₁[i.1]'i.2).2 = f_tau i ∧
    lmat (edges₁[i.1]'i.2).2 (edges₁[i.1]'i.2).1 = f_tau i) ∧
  (∀ u : Fin n,
    (∃ i : Fin edges₁.length, i.1 < k ∧ (u = (edges₁[i.1]'i.2).1 ∨ u = (edges₁[i.1]'i.2).2)) →
      ∃ y : Fin n, H.Adj u y ∧ lmat u u = τ₀ s(u, y)) ∧
  (∀ u : Fin n, ∃ g ∈ H.edgeFinset, lmat u u = τ₀ g)

/-- Update `lmat` at `(u_k, v_k)`, `(v_k, u_k)`, `(u_k, u_k)`, `(v_k, v_k)` with `l_k`. -/
def updateLeafMat {n t₀ : ℕ} (lmat : Fin n → Fin n → Fin t₀)
    (u_k v_k : Fin n) (l_k : Fin t₀) (x y : Fin n) : Fin t₀ :=
  if (x = u_k ∧ y = v_k) ∨ (x = v_k ∧ y = u_k) ∨ (x = u_k ∧ y = u_k) ∨ (x = v_k ∧ y = v_k) then
    l_k
  else
    lmat x y

theorem leafMatLoopInv_zero {n t₀ : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    {edges₁ : List (Fin n × Fin n)} (hedges₁ : IsSimpleEdgeList H edges₁)
    (hm₁ : 0 < edges₁.length) (ht₀_pos : 0 < t₀)
    (f_tau : Fin edges₁.length → Fin t₀) :
    LeafMatLoopInv H edges₁ ht₀_pos f_tau 0 (fun _ _ => f_tau ⟨0, hm₁⟩) := by
  refine ⟨fun _ hi => False.elim (Nat.not_lt_zero _ hi),
    fun _ ⟨_, hi, _⟩ => False.elim (Nat.not_lt_zero _ hi),
    fun _ => ?_⟩
  let i₀ : Fin edges₁.length := ⟨0, hm₁⟩
  have hadj₀ : H.Adj (edges₁[0]'hm₁).1 (edges₁[0]'hm₁).2 :=
    (hedges₁.2.2 (edges₁[0]'hm₁).1 (edges₁[0]'hm₁).2).mpr ⟨0, hm₁, Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨symEdgeAt edges₁ i₀, SimpleGraph.mem_edgeFinset.mpr hadj₀, ?_⟩
  exact (tauOfArr_symEdgeAt hedges₁ t₀ ht₀_pos f_tau i₀).symm

theorem leafMatLoopInv_step {n t₀ : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    {edges₁ : List (Fin n × Fin n)} (hedges₁ : IsSimpleEdgeList H edges₁)
    (ht₀_pos : 0 < t₀) (f_tau : Fin edges₁.length → Fin t₀)
    {k : ℕ} (hk : k < edges₁.length) {lmat : Fin n → Fin n → Fin t₀}
    (hinv : LeafMatLoopInv H edges₁ ht₀_pos f_tau k lmat) :
    let ik : Fin edges₁.length := ⟨k, hk⟩
    let u_k := (edges₁[k]'hk).1
    let v_k := (edges₁[k]'hk).2
    LeafMatLoopInv H edges₁ ht₀_pos f_tau (k + 1) (updateLeafMat lmat u_k v_k (f_tau ik)) := by
  intro ik u_k v_k
  let τ₀ := tauOfArr edges₁ t₀ ht₀_pos f_tau
  have huv_ne : u_k ≠ v_k := hedges₁.1 k hk
  have hadj_k : H.Adj u_k v_k := (hedges₁.2.2 u_k v_k).mpr ⟨k, hk, Or.inl ⟨rfl, rfl⟩⟩
  have htau_k : τ₀ s(u_k, v_k) = f_tau ik := tauOfArr_symEdgeAt hedges₁ t₀ ht₀_pos f_tau ik
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
    · have hne_i : i ≠ ik := fun h => by have := congrArg Fin.val h; change i.1 = k at this; omega
      let u_i := (edges₁[i.1]'i.2).1
      let v_i := (edges₁[i.1]'i.2).2
      have huivi_ne : u_i ≠ v_i := hedges₁.1 i.1 i.2
      have hnot_sym : ¬ ((u_i = u_k ∧ v_i = v_k) ∨ (u_i = v_k ∧ v_i = u_k)) := by
        intro hsym
        have h_eq : symEdgeAt edges₁ i = symEdgeAt edges₁ ik := by
          unfold symEdgeAt
          rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact congrArg₂ (fun a b => s(a, b)) h1 h2
          · rw [Sym2.eq_swap]; exact congrArg₂ (fun a b => s(a, b)) h2 h1
        exact hne_i (symEdgeAt_injective hedges₁ h_eq)
      have hcond1 : ¬ ((u_i = u_k ∧ v_i = v_k) ∨ (u_i = v_k ∧ v_i = u_k) ∨
          (u_i = u_k ∧ v_i = u_k) ∨ (u_i = v_k ∧ v_i = v_k)) := by
        rintro (h1 | h2 | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hnot_sym (Or.inl h1)
        · exact hnot_sym (Or.inr h2)
        · exact huivi_ne (h1.trans h2.symm)
        · exact huivi_ne (h1.trans h2.symm)
      have hcond2 : ¬ ((v_i = u_k ∧ u_i = v_k) ∨ (v_i = v_k ∧ u_i = u_k) ∨
          (v_i = u_k ∧ u_i = u_k) ∨ (v_i = v_k ∧ u_i = v_k)) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hnot_sym (Or.inr ⟨h2, h1⟩)
        · exact hnot_sym (Or.inl ⟨h2, h1⟩)
        · exact huivi_ne (h2.trans h1.symm)
        · exact huivi_ne (h2.trans h1.symm)
      have h1 : updateLeafMat lmat u_k v_k (f_tau ik) u_i v_i = lmat u_i v_i := by
        unfold updateLeafMat; exact ite_eq_right_iff.mpr (fun hp => absurd hp hcond1)
      have h2 : updateLeafMat lmat u_k v_k (f_tau ik) v_i u_i = lmat v_i u_i := by
        unfold updateLeafMat; exact ite_eq_right_iff.mpr (fun hp => absurd hp hcond2)
      rw [h1, h2]
      exact hinv.1 i hlt
    · have hi_eq : i = ik := Fin.ext heq
      subst hi_eq
      change updateLeafMat lmat u_k v_k (f_tau ik) u_k v_k = f_tau ik ∧
             updateLeafMat lmat u_k v_k (f_tau ik) v_k u_k = f_tau ik
      unfold updateLeafMat
      simp
  · intro u ⟨i, hi, hu_in⟩
    by_cases hu_uk : u = u_k
    · subst hu_uk
      refine ⟨v_k, hadj_k, ?_⟩
      change updateLeafMat lmat u_k v_k (f_tau ik) u_k u_k = τ₀ s(u_k, v_k)
      unfold updateLeafMat
      rw [htau_k]
      simp
    · by_cases hu_vk : u = v_k
      · subst hu_vk
        refine ⟨u_k, hadj_k.symm, ?_⟩
        change updateLeafMat lmat u_k v_k (f_tau ik) v_k v_k = τ₀ s(v_k, u_k)
        unfold updateLeafMat
        rw [Sym2.eq_swap, htau_k]
        simp
      · have hilt : i.1 < k := by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
          · exact hlt
          · exfalso
            have hi_eq : i = ik := Fin.ext heq
            subst hi_eq
            rcases hu_in with h1 | h2
            · exact hu_uk h1
            · exact hu_vk h2
        have hdiag : updateLeafMat lmat u_k v_k (f_tau ik) u u = lmat u u := by
          unfold updateLeafMat
          simp [hu_uk, hu_vk]
        rw [hdiag]
        exact hinv.2.1 u ⟨i, hilt, hu_in⟩
  · intro u
    by_cases hu : u = u_k ∨ u = v_k
    · refine ⟨s(u_k, v_k), SimpleGraph.mem_edgeFinset.mpr hadj_k, ?_⟩
      dsimp [τ₀] at htau_k
      rw [htau_k]
      unfold updateLeafMat
      rcases hu with rfl | rfl <;> simp
    · push Not at hu
      have hdiag : updateLeafMat lmat u_k v_k (f_tau ik) u u = lmat u u := by
        unfold updateLeafMat
        simp [hu.1, hu.2]
      rw [hdiag]
      exact hinv.2.2 u

theorem LeafMatLoopInv.to_isValidLeafLookupMat {n t₀ : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] {edges₁ : List (Fin n × Fin n)} (hedges₁ : IsSimpleEdgeList H edges₁)
    (ht₀_pos : 0 < t₀) (f_tau : Fin edges₁.length → Fin t₀) {lmat : Fin n → Fin n → Fin t₀}
    (hinv : LeafMatLoopInv H edges₁ ht₀_pos f_tau edges₁.length lmat) :
    IsValidLeafLookupMat H (tauOfArr edges₁ t₀ ht₀_pos f_tau) lmat := by
  refine ⟨?_, ?_, hinv.2.2⟩
  · intro u v hadj
    rcases (hedges₁.2.2 u v).mp hadj with ⟨i, hi, ⟨hu, hv⟩ | ⟨hu, hv⟩⟩
    · let idx : Fin edges₁.length := ⟨i, hi⟩
      have h1 := (hinv.1 idx hi).1
      have htau := tauOfArr_symEdgeAt hedges₁ t₀ ht₀_pos f_tau idx
      unfold symEdgeAt at htau
      dsimp [idx] at h1 htau
      rw [hu, hv] at h1 htau
      exact h1.trans htau.symm
    · let idx : Fin edges₁.length := ⟨i, hi⟩
      have h2 := (hinv.1 idx hi).2
      have htau := tauOfArr_symEdgeAt hedges₁ t₀ ht₀_pos f_tau idx
      unfold symEdgeAt at htau
      dsimp [idx] at h2 htau
      rw [hu, hv] at h2 htau
      rw [Sym2.eq_swap] at htau
      exact h2.trans htau.symm
  · intro u ⟨y, hadj⟩
    rcases (hedges₁.2.2 u y).mp hadj with ⟨i, hi, ⟨hu, _⟩ | ⟨_, hv⟩⟩
    · exact hinv.2.1 u ⟨⟨i, hi⟩, hi, Or.inl hu.symm⟩
    · exact hinv.2.1 u ⟨⟨i, hi⟩, hi, Or.inr hv.symm⟩

/-- Loop body of `buildLeafMatProg`: for edge `k < m₁`, reads `u = a_eu[k]`, `v = a_ev[k]`,
`l = a_tau0[k]`, and writes `l` to `a_lmat[u * n + v]`, `a_lmat[v * n + u]`, `a_lmat[u * n + u]`,
and `a_lmat[v * n + v]`. -/
def buildLeafMatBody (a_eu a_ev a_tau0 a_lmat : Arr) (r_n r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_eu (.reg r_base)))
    (.seq (.assign (r_base + 2) (.read a_ev (.reg r_base)))
      (.seq (.assign (r_base + 3) (.read a_tau0 (.reg r_base)))
        (.seq (.write a_lmat
            (.op .add (.op .mul (.reg (r_base + 1)) (.reg r_n)) (.reg (r_base + 2)))
            (.reg (r_base + 3)))
          (.seq (.write a_lmat
              (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_n)) (.reg (r_base + 1)))
              (.reg (r_base + 3)))
            (.seq (.write a_lmat
                (.op .add (.op .mul (.reg (r_base + 1)) (.reg r_n)) (.reg (r_base + 1)))
                (.reg (r_base + 3)))
              (.write a_lmat
                (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_n)) (.reg (r_base + 2)))
                (.reg (r_base + 3))))))))

/-- Build the `n × n` leaf-lookup matrix `a_lmat` satisfying
`IsValidLeafLookupMat G.toSimpleGraph (tauOfArr edges₁ t₀ ht₀_pos f_tau) lmat` in `O(n² + m₁)` steps. -/
def buildLeafMatProg (a_eu a_ev a_tau0 a_lmat : Arr) (r_n r_m1 r_base : Reg) : Cmd :=
  .seq (.assign r_base (.op .mul (.reg r_n) (.reg r_n)))
    (.seq (.assign (r_base + 1) (.read a_tau0 (.const 0)))
      (.seq (fillArrProg a_lmat r_base (r_base + 1) (r_base + 2))
        (.seq (.assign r_base (.const 0))
          (forUp r_base (.reg r_m1) (buildLeafMatBody a_eu a_ev a_tau0 a_lmat r_n r_base)))))

theorem buildLeafMatLoop_exec {w n t₀ : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    {edges₁ : List (Fin n × Fin n)} (hedges₁ : IsSimpleEdgeList H edges₁)
    (ht₀_pos : 0 < t₀) (f_tau : Fin edges₁.length → Fin t₀)
    (a_eu a_ev a_tau0 a_lmat : Arr) (r_n r_m1 r_base : Reg)
    (hne_eu_lm : a_eu ≠ a_lmat) (hne_ev_lm : a_ev ≠ a_lmat) (hne_tau_lm : a_tau0 ≠ a_lmat)
    (hr_n : r_n < r_base) (hr_m1 : r_m1 < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm₁_w : edges₁.length < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges₁.length)
    (lmat : Fin n → Fin n → Fin t₀)
    (hinv : LeafMatLoopInv H edges₁ ht₀_pos f_tau k lmat)
    {s : State}
    (hend : IsEndpointArrs edges₁ a_eu a_ev s)
    (htau : IsTauArr f_tau a_tau0 s)
    (hlm_len : (s.arrs a_lmat).length = n * n)
    (hlm_val : ∀ x y : Fin n,
      (s.arrs a_lmat)[x.1 * n + y.1]'(by rw [hlm_len]; exact mul_add_lt_sq x.2 y.2) = (lmat x y).1)
    (hrn_val : s.regs r_n = n)
    (hrm1_val : s.regs r_m1 = edges₁.length)
    (hrk_val : s.regs r_base = k) :
    ∃ (s' : State) (t : ℕ) (lmat' : Fin n → Fin n → Fin t₀),
      Exec w (forUp r_base (.reg r_m1) (buildLeafMatBody a_eu a_ev a_tau0 a_lmat r_n r_base)) s s' t ∧
      t ≤ 3 + 44 * rem ∧
      IsValidLeafLookupMat H (tauOfArr edges₁ t₀ ht₀_pos f_tau) lmat' ∧
      ∃ (hlm'_len : (s'.arrs a_lmat).length = n * n),
      (∀ x y : Fin n,
        (s'.arrs a_lmat)[x.1 * n + y.1]'(by rw [hlm'_len]; exact mul_add_lt_sq x.2 y.2) =
          (lmat' x y).1) ∧
      (∀ a : Arr, a ≠ a_lmat → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k lmat s with
  | zero =>
    have hk_eq : k = edges₁.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm1_val, hm₁_w, h0_w]
    exact ⟨s, 3, lmat, .while_false hcond, by omega,
      hinv.to_isValidLeafLookupMat H hedges₁ ht₀_pos f_tau,
      hlm_len, hlm_val, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges₁.length := by omega
    have hk_w : k < 2 ^ w := by omega
    let ik : Fin edges₁.length := ⟨k, hk_lt⟩
    let u_k := (edges₁[k]'hk_lt).1
    let v_k := (edges₁[k]'hk_lt).2
    let l_k := f_tau ik
    have hu_w : u_k.1 < 2 ^ w := Nat.lt_trans u_k.2 hn_w
    have hv_w : v_k.1 < 2 ^ w := Nat.lt_trans v_k.2 hn_w
    have hlk_w : l_k.1 < 2 ^ w := Nat.lt_trans l_k.2 ht₀_w
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm1_val, hk_w, hm₁_w, hk_lt, hw]
    -- 1. r_base + 1 := a_eu[k]
    have heu_len : k < (s.arrs a_eu).length := by rw [hend.1]; exact hk_lt
    have heu_get : (s.arrs a_eu)[k]'heu_len = u_k.1 := (hend.2.2 ik).1
    let s₁ := s.setReg (r_base + 1) u_k.1
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_eu (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrk_val, hk_w, heu_len, heu_get, hu_w])
    -- 2. r_base + 2 := a_ev[k]
    have hev_len : k < (s.arrs a_ev).length := by rw [hend.2.1]; exact hk_lt
    have hev_get : (s.arrs a_ev)[k]'hev_len = v_k.1 := (hend.2.2 ik).2
    let s₂ := s₁.setReg (r_base + 2) v_k.1
    have hex₂ : Exec w (.assign (r_base + 2) (.read a_ev (.reg r_base))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hrk_val, hk_w, hev_len, hev_get, hv_w])
    -- 3. r_base + 3 := a_tau0[k]
    have htau_len : k < (s.arrs a_tau0).length := by rw [htau.1]; exact hk_lt
    have htau_get : (s.arrs a_tau0)[k]'htau_len = l_k.1 := htau.2 ik
    let s₃ := s₂.setReg (r_base + 3) l_k.1
    have hex₃ : Exec w (.assign (r_base + 3) (.read a_tau0 (.reg r_base))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, Expr.eval, checkWord, hrk_val, hk_w, htau_len, htau_get, hlk_w])
    -- 4..7. four writes to a_lmat
    have hrn₃ : s₃.regs r_n = n := by
      dsimp [Reg] at hr_n
      simp [s₃, s₂, s₁, State.setReg,
        show (r_n : Reg) ≠ r_base + 3 by dsimp [Reg]; omega,
        show (r_n : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
        show (r_n : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrn_val]
    have h_uv_sq : u_k.1 * n + v_k.1 < n * n := mul_add_lt_sq u_k.2 v_k.2
    have h_vu_sq : v_k.1 * n + u_k.1 < n * n := mul_add_lt_sq v_k.2 u_k.2
    have h_uu_sq : u_k.1 * n + u_k.1 < n * n := mul_add_lt_sq u_k.2 u_k.2
    have h_vv_sq : v_k.1 * n + v_k.1 < n * n := mul_add_lt_sq v_k.2 v_k.2
    have h_un_w : u_k.1 * n < 2 ^ w := by omega
    have h_vn_w : v_k.1 * n < 2 ^ w := by omega
    have h_uv_w : u_k.1 * n + v_k.1 < 2 ^ w := by omega
    have h_vu_w : v_k.1 * n + u_k.1 < 2 ^ w := by omega
    have h_uu_w : u_k.1 * n + u_k.1 < 2 ^ w := by omega
    have h_vv_w : v_k.1 * n + v_k.1 < 2 ^ w := by omega
    let s₄ := s₃.writeArr a_lmat (u_k.1 * n + v_k.1) l_k.1
    have hex₄ : Exec w (.write a_lmat
        (.op .add (.op .mul (.reg (r_base + 1)) (.reg r_n)) (.reg (r_base + 2)))
        (.reg (r_base + 3))) s₃ s₄ 7 :=
      .write (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrn₃, hu_w, hn_w, h_un_w, hv_w, h_uv_w])
        (by simp [s₃, Expr.eval, checkWord, hlk_w])
        (by simp [s₃, s₂, s₁, hlm_len, h_uv_sq])
    let s₅ := s₄.writeArr a_lmat (v_k.1 * n + u_k.1) l_k.1
    have hex₅ : Exec w (.write a_lmat
        (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_n)) (.reg (r_base + 1)))
        (.reg (r_base + 3))) s₄ s₅ 7 :=
      .write (by simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrn₃, hv_w, hn_w, h_vn_w, hu_w, h_vu_w])
        (by simp [s₄, s₃, Expr.eval, checkWord, hlk_w])
        (by simp [s₄, s₃, s₂, s₁, hlm_len, h_vu_sq])
    let s₆ := s₅.writeArr a_lmat (u_k.1 * n + u_k.1) l_k.1
    have hex₆ : Exec w (.write a_lmat
        (.op .add (.op .mul (.reg (r_base + 1)) (.reg r_n)) (.reg (r_base + 1)))
        (.reg (r_base + 3))) s₅ s₆ 7 :=
      .write (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrn₃, hu_w, hn_w, h_un_w, h_uu_w])
        (by simp [s₅, s₄, s₃, Expr.eval, checkWord, hlk_w])
        (by simp [s₅, s₄, s₃, s₂, s₁, hlm_len, h_uu_sq])
    let s₇ := s₆.writeArr a_lmat (v_k.1 * n + v_k.1) l_k.1
    have hex₇ : Exec w (.write a_lmat
        (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_n)) (.reg (r_base + 2)))
        (.reg (r_base + 3))) s₆ s₇ 7 :=
      .write (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrn₃, hv_w, hn_w, h_vn_w, h_vv_w])
        (by simp [s₆, s₅, s₄, s₃, Expr.eval, checkWord, hlk_w])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hlm_len, h_vv_sq])
    let s₈ := s₇.setReg r_base (k + 1)
    have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₇ s₈ 4 :=
      .assign (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrk_val, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have hex_body : Exec w (buildLeafMatBody a_eu a_ev a_tau0 a_lmat r_n r_base) s s₇
        (3 + (3 + (3 + (7 + (7 + (7 + 7)))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
    let lmat' := updateLeafMat lmat u_k v_k l_k
    have hinv' : LeafMatLoopInv H edges₁ ht₀_pos f_tau (k + 1) lmat' :=
      leafMatLoopInv_step H hedges₁ ht₀_pos f_tau hk_lt hinv
    have hlm₈_len : (s₈.arrs a_lmat).length = n * n := by
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hlm_len]
    have hlm₈_eq : s₈.arrs a_lmat =
        ((((s.arrs a_lmat).set (u_k.1 * n + v_k.1) l_k.1).set
          (v_k.1 * n + u_k.1) l_k.1).set
          (u_k.1 * n + u_k.1) l_k.1).set
          (v_k.1 * n + v_k.1) l_k.1 := by
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁]
    have hlm₈_val : ∀ x y : Fin n,
        (s₈.arrs a_lmat)[x.1 * n + y.1]'(by rw [hlm₈_len]; exact mul_add_lt_sq x.2 y.2) =
          (lmat' x y).1 := by
      intro x y
      simp only [hlm₈_eq, List.getElem_set, hlm_val x y, lmat', updateLeafMat]
      have h_xy_vv : v_k.1 * n + v_k.1 = x.1 * n + y.1 ↔ (x = v_k ∧ y = v_k) := by
        constructor
        · intro h; rcases mul_add_inj_of_lt v_k.2 y.2 h with ⟨h1, h2⟩
          exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩
        · rintro ⟨rfl, rfl⟩; rfl
      have h_xy_uu : u_k.1 * n + u_k.1 = x.1 * n + y.1 ↔ (x = u_k ∧ y = u_k) := by
        constructor
        · intro h; rcases mul_add_inj_of_lt u_k.2 y.2 h with ⟨h1, h2⟩
          exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩
        · rintro ⟨rfl, rfl⟩; rfl
      have h_xy_vu : v_k.1 * n + u_k.1 = x.1 * n + y.1 ↔ (x = v_k ∧ y = u_k) := by
        constructor
        · intro h; rcases mul_add_inj_of_lt u_k.2 y.2 h with ⟨h1, h2⟩
          exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩
        · rintro ⟨rfl, rfl⟩; rfl
      have h_xy_uv : u_k.1 * n + v_k.1 = x.1 * n + y.1 ↔ (x = u_k ∧ y = v_k) := by
        constructor
        · intro h; rcases mul_add_inj_of_lt v_k.2 y.2 h with ⟨h1, h2⟩
          exact ⟨Fin.ext h1.symm, Fin.ext h2.symm⟩
        · rintro ⟨rfl, rfl⟩; rfl
      simp only [h_xy_vv, h_xy_uu, h_xy_vu, h_xy_uv]
      by_cases hvv : x = v_k ∧ y = v_k <;>
        by_cases huu : x = u_k ∧ y = u_k <;>
        by_cases hvu : x = v_k ∧ y = u_k <;>
        by_cases huv : x = u_k ∧ y = v_k <;>
        simp [hvv, huu, hvu, huv]
    have harr₈ : ∀ a : Arr, a ≠ a_lmat → s₈.arrs a = s.arrs a := by
      intro a ha
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha]
    rcases ih (k + 1) (by omega) lmat' hinv' (s := s₈)
        (hend.of_arrs_eq (harr₈ a_eu hne_eu_lm) (harr₈ a_ev hne_ev_lm))
        (htau.of_arr_eq (harr₈ a_tau0 hne_tau_lm))
        hlm₈_len hlm₈_val
        (by
          dsimp [Reg] at hr_n
          simp [s₈, s₇, s₆, s₅, s₄, State.setReg,
            show (r_n : Reg) ≠ r_base by dsimp [Reg]; omega, hrn₃])
        (by
          dsimp [Reg] at hr_m1
          simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
            show (r_m1 : Reg) ≠ r_base by dsimp [Reg]; omega,
            show (r_m1 : Reg) ≠ r_base + 3 by dsimp [Reg]; omega,
            show (r_m1 : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
            show (r_m1 : Reg) ≠ r_base + 1 by dsimp [Reg]; omega, hrm1_val])
        (by simp [s₈]) with
      ⟨s₉, t₉, lmat'', hex₉, ht₉, hvalid₉, hlm₉_len, hlm₉_val, harr₉, hreg₉⟩
    refine ⟨s₉, 3 + ((3 + (3 + (3 + (7 + (7 + (7 + 7)))))) + 4) + t₉, lmat'',
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex₉,
      by omega, hvalid₉, hlm₉_len, hlm₉_val,
      fun a ha => (harr₉ a ha).trans (harr₈ a ha),
      fun r hr => by
        dsimp [Reg] at hr
        rw [hreg₉ r hr]
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
          show (r : Reg) ≠ r_base by dsimp [Reg]; omega,
          show (r : Reg) ≠ r_base + 3 by dsimp [Reg]; omega,
          show (r : Reg) ≠ r_base + 2 by dsimp [Reg]; omega,
          show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega]⟩

theorem buildLeafMatProg_exec {w n t₀ : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    {edges₁ : List (Fin n × Fin n)} (hedges₁ : IsSimpleEdgeList H edges₁)
    (hm₁_pos : 0 < edges₁.length)
    (ht₀_pos : 0 < t₀) (f_tau : Fin edges₁.length → Fin t₀)
    (a_eu a_ev a_tau0 a_lmat : Arr) (r_n r_m1 r_base : Reg)
    (hne_eu_lm : a_eu ≠ a_lmat) (hne_ev_lm : a_ev ≠ a_lmat) (hne_tau_lm : a_tau0 ≠ a_lmat)
    (hr_n : r_n < r_base) (hr_m1 : r_m1 < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm₁_w : edges₁.length < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    {s : State}
    (hend : IsEndpointArrs edges₁ a_eu a_ev s)
    (htau : IsTauArr f_tau a_tau0 s)
    (hrn_val : s.regs r_n = n)
    (hrm1_val : s.regs r_m1 = edges₁.length) :
    ∃ (s' : State) (t : ℕ) (lmat : Fin n → Fin n → Fin t₀),
      Exec w (buildLeafMatProg a_eu a_ev a_tau0 a_lmat r_n r_m1 r_base) s s' t ∧
      t ≤ 11 * (n * n) + 44 * edges₁.length + 20 ∧
      IsValidLeafLookupMat H (tauOfArr edges₁ t₀ ht₀_pos f_tau) lmat ∧
      ∃ (hlm'_len : (s'.arrs a_lmat).length = n * n),
      (∀ x y : Fin n,
        (s'.arrs a_lmat)[x.1 * n + y.1]'(by rw [hlm'_len]; exact mul_add_lt_sq x.2 y.2) =
          (lmat x y).1) ∧
      (∀ a : Arr, a ≠ a_lmat → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let i₀ : Fin edges₁.length := ⟨0, hm₁_pos⟩
  let l₀ := f_tau i₀
  have hl₀_w : l₀.1 < 2 ^ w := Nat.lt_trans l₀.2 ht₀_w
  -- 1. r_base := r_n * r_n
  let s₁ := s.setReg r_base (n * n)
  have hex₁ : Exec w (.assign r_base (.op .mul (.reg r_n) (.reg r_n))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn_val, hn_w, hn2_w])
  -- 2. r_base + 1 := a_tau0[0]
  have htau_len₀ : 0 < (s.arrs a_tau0).length := by rw [htau.1]; exact hm₁_pos
  have htau_get₀ : (s.arrs a_tau0)[0]'htau_len₀ = l₀.1 := htau.2 i₀
  let s₂ := s₁.setReg (r_base + 1) l₀.1
  have hex₂ : Exec w (.assign (r_base + 1) (.read a_tau0 (.const 0))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, h0_w, htau_len₀, htau_get₀, hl₀_w])
  -- 3. fillArrProg a_lmat r_base (r_base + 1) (r_base + 2)
  rcases fillArrProg_exec a_lmat r_base (r_base + 1) (r_base + 2)
      (by romega) (by romega) hw hn2_w hl₀_w (s := s₂)
      (by simp [s₂, s₁]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hlm₃, harr₃, hreg₃⟩
  -- 4. r_base := 0
  let s₄ := s₃.setReg r_base 0
  have hex₄ : Exec w (.assign r_base (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. buildLeafMatLoop_exec
  have harr₄ : ∀ a : Arr, a ≠ a_lmat → s₄.arrs a = s.arrs a := by
    intro a ha; simp [s₄]; rw [harr₃ a ha]; simp [s₂, s₁]
  have hlm₄_len : (s₄.arrs a_lmat).length = n * n := by simp [s₄, hlm₃]
  have hinv₀ : LeafMatLoopInv H edges₁ ht₀_pos f_tau 0 (fun _ _ => l₀) :=
    leafMatLoopInv_zero H hedges₁ hm₁_pos ht₀_pos f_tau
  rcases buildLeafMatLoop_exec H hedges₁ ht₀_pos f_tau a_eu a_ev a_tau0 a_lmat r_n r_m1 r_base
      hne_eu_lm hne_ev_lm hne_tau_lm hr_n hr_m1 hw hn_w hn2_w hm₁_w ht₀_w
      edges₁.length 0 (by omega) (fun _ _ => l₀) hinv₀ (s := s₄)
      (hend.of_arrs_eq (harr₄ a_eu hne_eu_lm) (harr₄ a_ev hne_ev_lm))
      (htau.of_arr_eq (harr₄ a_tau0 hne_tau_lm))
      hlm₄_len
      (fun x y => by simp [s₄, hlm₃])
      (by
        dsimp [Reg] at hr_n
        simp only [s₄, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_n : Reg) ≠ r_base)]
        rw [hreg₃ r_n (by dsimp [Reg]; omega)]
        simp [s₂, s₁, State.setReg,
          show (r_n : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
          show (r_n : Reg) ≠ r_base by dsimp [Reg]; omega, hrn_val])
      (by
        dsimp [Reg] at hr_m1
        simp only [s₄, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_m1 : Reg) ≠ r_base)]
        rw [hreg₃ r_m1 (by dsimp [Reg]; omega)]
        simp [s₂, s₁, State.setReg,
          show (r_m1 : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
          show (r_m1 : Reg) ≠ r_base by dsimp [Reg]; omega, hrm1_val])
      (by simp [s₄]) with
    ⟨s₅, t₅, lmat', hex₅, ht₅, hvalid₅, hlm₅_len, hlm₅_val, harr₅, hreg₅⟩
  refine ⟨s₅, 4 + (3 + (t₃ + (2 + t₅))),
    lmat', .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hvalid₅, hlm₅_len, hlm₅_val,
    fun a ha => (harr₅ a ha).trans (harr₄ a ha),
    fun r hr => by
      dsimp [Reg] at hr
      rw [hreg₅ r hr]
      simp only [s₄, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base)]
      rw [hreg₃ r (by dsimp [Reg]; omega)]
      simp [s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
        show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

/-- Inner loop body of `expandSigmaProg`: writes `r_base + 6` (`l`) at `a_sigma[r_base + 1]` and
increments `r_base + 1`. -/
def expandSigmaInnerBody (a_sigma : Arr) (r_base : Reg) : Cmd :=
  .seq (.write a_sigma (.reg (r_base + 1)) (.reg (r_base + 6)))
    (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))

/-- Outer loop body of `expandSigmaProg`: for active pair `k < m'`, reads `(u, v, mult)` from `a_src`,
reads `l = a_lmat[u * n + v]`, and appends `mult` copies of `l` into `a_sigma`. -/
def expandSigmaBody (a_src a_lmat a_sigma : Arr) (r_n r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src r_base (r_base + 2) (r_base + 3) (r_base + 4))
    (.seq (.assign (r_base + 5) (.read a_src (.op .add (.reg (r_base + 2)) (.const 2))))
      (.seq (.assign (r_base + 6)
          (.read a_lmat
            (.op .add (.op .mul (.reg (r_base + 3)) (.reg r_n)) (.reg (r_base + 4)))))
        (.seq (.assign (r_base + 7) (.const 0))
          (forUp (r_base + 7) (.reg (r_base + 5)) (expandSigmaInnerBody a_sigma r_base)))))

/-- Construct the initial edge-to-leaf array `a_sigma` of length `G.numEdges` representing
`sigmaFromLeafMat G lmat` in `O(m' + m)` steps. -/
def expandSigmaProg (a_src a_lmat a_sigma : Arr) (r_n r_m' r_m r_base : Reg) : Cmd :=
  .seq (.alloc a_sigma (.reg r_m))
    (.seq (.assign r_base (.const 0))
      (.seq (.assign (r_base + 1) (.const 0))
        (forUp r_base (.reg r_m') (expandSigmaBody a_src a_lmat a_sigma r_n r_base))))

theorem expandSigmaInnerLoop_exec {w mult val rem_after : ℕ} (a_sigma : Arr) (r_base : Reg)
    (pfx : List ℕ)
    (hw : 1 < 2 ^ w) (hpos_w : pfx.length + mult < 2 ^ w)
    (hmult_w : mult < 2 ^ w) (hval_w : val < 2 ^ w)
    (rem j : ℕ) (hrem : j + rem = mult) {s : State}
    (hsig : s.arrs a_sigma =
      (pfx ++ List.replicate j val) ++ List.replicate (rem + rem_after) 0)
    (hrpos : s.regs (r_base + 1) = pfx.length + j)
    (hrmult : s.regs (r_base + 5) = mult)
    (hrval : s.regs (r_base + 6) = val)
    (hrj : s.regs (r_base + 7) = j) :
    ∃ s' t,
      Exec w (forUp (r_base + 7) (.reg (r_base + 5)) (expandSigmaInnerBody a_sigma r_base)) s s' t ∧
      t ≤ 3 + 14 * rem ∧
      s'.arrs a_sigma = (pfx ++ List.replicate mult val) ++ List.replicate rem_after 0 ∧
      s'.regs (r_base + 1) = pfx.length + mult ∧
      (∀ a : Arr, a ≠ a_sigma → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_base + 1 → r ≠ r_base + 7 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing j s with
  | zero =>
    have hj_eq : j = mult := by omega
    subst hj_eq
    have hcond : (Expr.op .lt (.reg (r_base + 7)) (.reg (r_base + 5))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrmult, hmult_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, by simpa using hsig, hrpos,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hj_lt : j < mult := by omega
    have hj_w : j < 2 ^ w := by omega
    have hcur_w : pfx.length + j < 2 ^ w := by omega
    have hcur1_w : pfx.length + j + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 7)) (.reg (r_base + 5))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrmult, hj_w, hmult_w, hj_lt, hw]
    have hlen_sig : pfx.length + j < (s.arrs a_sigma).length := by simp [hsig]
    let s₁ := s.writeArr a_sigma (pfx.length + j) val
    have hex₁ : Exec w (.write a_sigma (.reg (r_base + 1)) (.reg (r_base + 6))) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hrpos, hcur_w])
        (by simp [Expr.eval, checkWord, hrval, hval_w]) hlen_sig
    let s₂ := s₁.setReg (r_base + 1) (pfx.length + j + 1)
    have hex₂ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hcur_w, hw, hcur1_w])
    let s₃ := s₂.setReg (r_base + 7) (j + 1)
    have hex₃ : Exec w (.assign (r_base + 7) (.op .add (.reg (r_base + 7)) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrj, hj_w, hw, show j + 1 < 2 ^ w by omega])
    have hsig₃ : s₃.arrs a_sigma =
        (pfx ++ List.replicate (j + 1) val) ++ List.replicate (rem + rem_after) 0 := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hsig]
      have hlen_pj : (pfx ++ List.replicate j val).length = pfx.length + j := by simp
      have hrep : rem + 1 + rem_after = (rem + rem_after) + 1 := by omega
      rw [hrep, ← hlen_pj,
          set_append_replicate_succ (pfx ++ List.replicate j val) (rem + rem_after) val,
          List.append_assoc pfx (List.replicate j val) [val], ← List.replicate_succ']
    rcases ih (j + 1) (by omega) (s := s₃) hsig₃
        (by simp [s₃, s₂]; omega)
        (by simp [s₃, s₂, s₁, hrmult])
        (by simp [s₃, s₂, s₁, hrval])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hsig₄, hrpos₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 4) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hsig₄, hrpos₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r hr1 hr7 => by rw [hreg₄ r hr1 hr7]; simp [s₃, s₂, s₁, State.setReg, hr1, hr7]⟩

theorem expandSigmaLoop_exec {w n t₀ : ℕ} (G : MultiDigraph n)
    (lmat : Fin n → Fin n → Fin t₀)
    (a_src a_lmat a_sigma : Arr) (r_n r_m' r_base : Reg)
    (hne_ss : a_src ≠ a_sigma) (hne_ls : a_lmat ≠ a_sigma)
    (hr_n : r_n < r_base) (hr_m' : r_m' < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    (suff pref : List (Fin n × Fin n))
    (hsplit : G.activePairsList = pref ++ suff)
    (pfx : List ℕ)
    (hpfx_sum : pfx.length + MultiDigraph.sumEdgeMult G suff = G.numEdges)
    {s : State}
    (hsrc : s.arrs a_src = G.enc)
    (hlm_len : (s.arrs a_lmat).length = n * n)
    (hlm_val : ∀ x y : Fin n,
      (s.arrs a_lmat)[x.1 * n + y.1]'(by rw [hlm_len]; exact mul_add_lt_sq x.2 y.2) =
        (lmat x y).1)
    (hsig : s.arrs a_sigma = pfx ++ List.replicate (MultiDigraph.sumEdgeMult G suff) 0)
    (hrn_val : s.regs r_n = n)
    (hrm'_val : s.regs r_m' = G.numActivePairs)
    (hrk_val : s.regs r_base = pref.length)
    (hrpos_val : s.regs (r_base + 1) = pfx.length) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_m') (expandSigmaBody a_src a_lmat a_sigma r_n r_base)) s s' t ∧
      t ≤ 3 + 38 * suff.length + 14 * MultiDigraph.sumEdgeMult G suff ∧
      s'.arrs a_sigma =
        pfx ++ suff.flatMap (fun p => List.replicate (G.edgeMult p.1 p.2) (lmat p.1 p.2).1) ∧
      (∀ a : Arr, a ≠ a_sigma → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff generalizing pref pfx s with
  | nil =>
    have hk_eq : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m')).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm'_val, hk_eq, hm'_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by simp,
      by simpa [MultiDigraph.sumEdgeMult] using hsig,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons p ps ih =>
    rcases p with ⟨u_k, v_k⟩
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_m')).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_val, hrm'_val, k, hk_m', hk_w, hm'_w, hw]
    -- 1. readTripleEndpoints a_src r_base (r_base + 2) (r_base + 3) (r_base + 4)
    have hsrc' : s.arrs a_src = G.enc ++ [] := by simp [hsrc]
    rcases readTripleEndpoints_exec G [] a_src r_base (r_base + 2) (r_base + 3) (r_base + 4)
        k s (by omega) (by omega) (by omega) hw3 hn_w hm3_w hk_m' hsrc' hrk_val with
      ⟨s₁, t₁, hex₁, ht₁, hr2_1, hr3_1, hr4_1, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u_k := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v_k := congrArg Prod.snd hget_k
    rw [hget_u] at hr3_1
    rw [hget_v] at hr4_1
    -- 2. r_base + 5 := a_src[r_base + 2 + 2] (mult)
    let mult := G.edgeMult u_k v_k
    have hsum_cons : MultiDigraph.sumEdgeMult G ((u_k, v_k) :: ps) =
        mult + MultiDigraph.sumEdgeMult G ps := rfl
    have hmult_w : mult < 2 ^ w := by omega
    have hidx_w : 2 + 3 * k < 2 ^ w := by omega
    have hidx2_w : 2 + 3 * k + 2 < 2 ^ w := by omega
    obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G [] hsrc' hk_m'
    rw [hget_u, hget_v] at hget_m
    have hlen_m₁ : 2 + 3 * k + 2 < (s₁.arrs a_src).length := by rw [harr₁]; exact hlen_m
    have hget_m₁ : (s₁.arrs a_src)[2 + 3 * k + 2]'hlen_m₁ = mult := by
      simp only [harr₁]; exact hget_m
    let s₂ := s₁.setReg (r_base + 5) mult
    have hex₂ : Exec w (.assign (r_base + 5) (.read a_src (.op .add (.reg (r_base + 2)) (.const 2))))
        s₁ s₂ 5 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_1, hidx_w, hw2, hidx2_w,
        hlen_m₁, hget_m₁, hmult_w])
    -- 3. r_base + 6 := a_lmat[u_k * n + v_k]
    let val := (lmat u_k v_k).1
    have hval_w : val < 2 ^ w := Nat.lt_trans (lmat u_k v_k).2 ht₀_w
    have hu_w : u_k.1 < 2 ^ w := Nat.lt_trans u_k.2 hn_w
    have hv_w : v_k.1 < 2 ^ w := Nat.lt_trans v_k.2 hn_w
    have h_uv_sq : u_k.1 * n + v_k.1 < n * n := mul_add_lt_sq u_k.2 v_k.2
    have h_un_w : u_k.1 * n < 2 ^ w := by omega
    have h_uv_w : u_k.1 * n + v_k.1 < 2 ^ w := by omega
    have hrn₂ : s₂.regs r_n = n := by
      dsimp [Reg] at hr_n
      simp only [s₂, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_n : Reg) ≠ r_base + 5)]
      rw [hreg₁ r_n (by omega) (by omega) (by omega)]
      exact hrn_val
    have hlm_len₂ : u_k.1 * n + v_k.1 < (s₂.arrs a_lmat).length := by
      simp [s₂, harr₁, hlm_len, h_uv_sq]
    have hlm_get₂ : (s₂.arrs a_lmat)[u_k.1 * n + v_k.1]'hlm_len₂ = val := by
      simp only [s₂, State.setReg_arrs, harr₁]; exact hlm_val u_k v_k
    have hr3_2 : s₂.regs (r_base + 3) = u_k.1 := by
      simp [s₂, hr3_1]
    have hr4_2 : s₂.regs (r_base + 4) = v_k.1 := by
      simp [s₂, hr4_1]
    let s₃ := s₂.setReg (r_base + 6) val
    have hex₃ : Exec w (.assign (r_base + 6)
        (.read a_lmat (.op .add (.op .mul (.reg (r_base + 3)) (.reg r_n)) (.reg (r_base + 4)))))
        s₂ s₃ 7 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr3_2, hr4_2, hrn₂, hu_w, hn_w, h_un_w, hv_w, h_uv_w, hlm_len₂, hlm_get₂, hval_w])
    -- 4. r_base + 7 := 0
    let s₄ := s₃.setReg (r_base + 7) 0
    have hex₄ : Exec w (.assign (r_base + 7) (.const 0)) s₃ s₄ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    -- 5. expandSigmaInnerLoop_exec
    have hsig₄ : s₄.arrs a_sigma =
        (pfx ++ List.replicate 0 val) ++ List.replicate (mult + MultiDigraph.sumEdgeMult G ps) 0 := by
      simp only [s₄, s₃, s₂, State.setReg_arrs, harr₁, hsig, hsum_cons, List.replicate_zero,
        List.append_nil]
    have hrpos₄ : s₄.regs (r_base + 1) = pfx.length + 0 := by
      simp only [s₄, s₃, s₂,
        State.setReg_regs_ne _ _ (by romega : (r_base + 1 : Reg) ≠ r_base + 7),
        State.setReg_regs_ne _ _ (by romega : (r_base + 1 : Reg) ≠ r_base + 6),
        State.setReg_regs_ne _ _ (by romega : (r_base + 1 : Reg) ≠ r_base + 5)]
      rw [hreg₁ (r_base + 1) (by romega) (by romega) (by romega)]
      simp [hrpos_val]
    rcases expandSigmaInnerLoop_exec a_sigma r_base pfx hw (by omega) hmult_w hval_w
        mult 0 (by omega) (s := s₄) hsig₄ hrpos₄
        (by simp [s₄, s₃, s₂]) (by simp [s₄, s₃]) (by simp [s₄]) with
      ⟨s₅, t₅, hex₅, ht₅, hsig₅, hrpos₅, harr₅, hreg₅⟩
    -- 6. increment r_base := k + 1
    have hrk₅ : s₅.regs r_base = k := by
      rw [hreg₅ r_base (by romega) (by romega)]
      change (((s₁.setReg (r_base + 5) mult).setReg (r_base + 6) val).setReg (r_base + 7) 0).regs r_base = k
      rw [State.setReg_regs_ne _ _ (by romega : (r_base : Reg) ≠ r_base + 7),
          State.setReg_regs_ne _ _ (by romega : (r_base : Reg) ≠ r_base + 6),
          State.setReg_regs_ne _ _ (by romega : (r_base : Reg) ≠ r_base + 5),
          hreg₁ r_base (by romega) (by romega) (by romega)]
      exact hrk_val
    let s₆ := s₅.setReg r_base (k + 1)
    have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₅, hk_w, hw,
        show k + 1 < 2 ^ w by omega])
    have hex_body : Exec w (expandSigmaBody a_src a_lmat a_sigma r_n r_base) s s₅
        (t₁ + (5 + (7 + (2 + t₅)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    have hsplit' : G.activePairsList = (pref ++ [(u_k, v_k)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    have harr₆ : ∀ a : Arr, a ≠ a_sigma → s₆.arrs a = s.arrs a := by
      intro a ha
      simp only [s₆, State.setReg_arrs]
      rw [harr₅ a ha]
      simp [s₄, s₃, s₂, harr₁]
    rcases ih (pref ++ [(u_k, v_k)]) hsplit' (pfx ++ List.replicate mult val)
        (by simp [List.length_replicate]; omega) (s := s₆)
        (by rw [harr₆ a_src hne_ss, hsrc])
        (by rw [harr₆ a_lmat hne_ls, hlm_len])
        (fun x y => by simp only [harr₆ a_lmat hne_ls]; exact hlm_val x y)
        (by simpa [s₆] using hsig₅)
        (by
          dsimp [Reg] at hr_n
          simp only [s₆, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_n : Reg) ≠ r_base)]
          rw [hreg₅ r_n (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
          change ((s₂.setReg (r_base + 6) val).setReg (r_base + 7) 0).regs r_n = n
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_n : Reg) ≠ r_base + 7),
              State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_n : Reg) ≠ r_base + 6)]
          exact hrn₂)
        (by
          dsimp [Reg] at hr_m'
          simp only [s₆, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_m' : Reg) ≠ r_base)]
          rw [hreg₅ r_m' (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
          change (((s₁.setReg (r_base + 5) mult).setReg (r_base + 6) val).setReg (r_base + 7) 0).regs r_m' =
            G.numActivePairs
          rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_m' : Reg) ≠ r_base + 7),
              State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_m' : Reg) ≠ r_base + 6),
              State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r_m' : Reg) ≠ r_base + 5),
              hreg₁ r_m' (by omega) (by omega) (by omega)]
          exact hrm'_val)
        (by simp [s₆, k])
        (by simp [s₆, hrpos₅]) with
      ⟨s₇, t₇, hex₇, ht₇, hsig₇, harr₇, hreg₇⟩
    refine ⟨s₇, 3 + ((t₁ + (5 + (7 + (2 + t₅)))) + 4) + t₇,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex₇,
      by simp only [List.length_cons, hsum_cons]; omega,
      by simpa [List.flatMap_cons, List.append_assoc] using hsig₇,
      fun a ha => (harr₇ a ha).trans (harr₆ a ha),
      fun r hr => by
        dsimp [Reg] at hr
        rw [hreg₇ r hr]
        simp only [s₆, State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base)]
        rw [hreg₅ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]
        change (((s₁.setReg (r_base + 5) mult).setReg (r_base + 6) val).setReg (r_base + 7) 0).regs r =
          s.regs r
        rw [State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base + 7),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base + 6),
            State.setReg_regs_ne _ _ (by dsimp [Reg]; omega : (r : Reg) ≠ r_base + 5)]
        exact hreg₁ r (by omega) (by omega) (by omega)⟩

theorem expandSigmaProg_exec {w n t₀ : ℕ} (G : MultiDigraph n)
    (lmat : Fin n → Fin n → Fin t₀)
    (a_src a_lmat a_sigma : Arr) (r_n r_m' r_m r_base : Reg)
    (hne_ss : a_src ≠ a_sigma) (hne_ls : a_lmat ≠ a_sigma)
    (hr_n : r_n < r_base) (hr_m' : r_m' < r_base) (_hr_m : r_m < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w) (ht₀_w : t₀ < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc)
    (hlm_len : (s.arrs a_lmat).length = n * n)
    (hlm_val : ∀ x y : Fin n,
      (s.arrs a_lmat)[x.1 * n + y.1]'(by rw [hlm_len]; exact mul_add_lt_sq x.2 y.2) =
        (lmat x y).1)
    (hrn_val : s.regs r_n = n)
    (hrm'_val : s.regs r_m' = G.numActivePairs)
    (hrm_val : s.regs r_m = G.numEdges) :
    ∃ s' t,
      Exec w (expandSigmaProg a_src a_lmat a_sigma r_n r_m' r_m r_base) s s' t ∧
      t ≤ 38 * G.numActivePairs + 15 * G.numEdges + 10 ∧
      (s'.arrs a_sigma).length = G.numEdges ∧
      (∀ e : Fin G.numEdges, (he : e.1 < (s'.arrs a_sigma).length) →
        (s'.arrs a_sigma)[e.1]'he = (sigmaFromLeafMat G lmat e).1) ∧
      (∀ a : Arr, a ≠ a_sigma → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  -- 1. alloc a_sigma r_m
  let s₁ := s.setArr a_sigma (List.replicate G.numEdges 0)
  have hex₁ : Exec w (.alloc a_sigma (.reg r_m)) s s₁ (1 + G.numEdges) :=
    .alloc (by simp [Expr.eval, checkWord, hrm_val, hm_w])
  -- 2. r_base := 0
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. expandSigmaLoop_exec
  have hsum_all : MultiDigraph.sumEdgeMult G G.activePairsList = G.numEdges :=
    G.sumEdgeMult_activePairsList
  have hsig₃ : s₃.arrs a_sigma = ([] : List ℕ) ++ List.replicate (MultiDigraph.sumEdgeMult G G.activePairsList) 0 := by
    simp [s₃, s₂, s₁, hsum_all]
  rcases expandSigmaLoop_exec G lmat a_src a_lmat a_sigma r_n r_m' r_base
      hne_ss hne_ls hr_n hr_m' hw3 hn_w hn2_w hm3_w hm_w ht₀_w
      G.activePairsList [] rfl [] (by simp [hsum_all]) (s := s₃)
      (by simp [s₃, s₂, s₁, hne_ss, hsrc])
      (by simp [s₃, s₂, s₁, hne_ls, hlm_len])
      (fun x y => by simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hne_ls]; exact hlm_val x y)
      hsig₃
      (by
        dsimp [Reg] at hr_n
        simp [s₃, s₂, s₁, State.setReg,
          show (r_n : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
          show (r_n : Reg) ≠ r_base by dsimp [Reg]; omega, hrn_val])
      (by
        dsimp [Reg] at hr_m'
        simp [s₃, s₂, s₁, State.setReg,
          show (r_m' : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
          show (r_m' : Reg) ≠ r_base by dsimp [Reg]; omega, hrm'_val])
      (by simp [s₃, s₂])
      (by simp [s₃]) with
    ⟨s₄, t₄, hex₄, ht₄, hsig₄, harr₄, hreg₄⟩
  have hlen_apl : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_apl, hsum_all] at ht₄
  have hsig_eq_map :
      s₄.arrs a_sigma = G.edgeListWithMult.map (fun p => (lmat p.1 p.2).1) := by
    rw [hsig₄, List.nil_append]
    unfold MultiDigraph.edgeListWithMult
    rw [List.map_flatMap]
    refine List.flatMap_congr fun p _ => ?_
    simp [List.map_replicate]
  have hsig₄_len : (s₄.arrs a_sigma).length = G.numEdges := by
    rw [hsig_eq_map, List.length_map, G.length_edgeListWithMult]
  refine ⟨s₄, (1 + G.numEdges) + (2 + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hsig₄_len,
    fun e _ => by
      simp only [hsig_eq_map, List.getElem_map]
      rfl,
    fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
    fun r hr => by
      dsimp [Reg] at hr
      rw [hreg₄ r hr]
      simp [s₃, s₂, s₁, State.setReg,
        show (r : Reg) ≠ r_base + 1 by dsimp [Reg]; omega,
        show (r : Reg) ≠ r_base by dsimp [Reg]; omega]⟩

/-! ### Section 6: Top-Level Multigraph Algorithm (3.3) (`alg33MultiProg`) -/

/-- Preamble of `alg33MultiProg`: computes `n = r_base + 1`, `m' = r_base + 2`, `m = r_base + 3`,
writes `encGraph G.toSimpleGraph` into `a_base`, sets `r_base + 4 = m₁` and
`r_base + 5 = 2 + 3 * m'`. -/
def alg33MultiPreambleProg (a_in a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (sumEdgeMultProg a_in (r_base + 1))
    (.seq (toSimpleGraphEdgeListProg a_in (a_base + 1) a_base (r_base + 4))
      (.seq (.assign (r_base + 4) (.reg (r_base + 5)))
        (.assign (r_base + 5) (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 2)))))))

theorem alg33MultiPreambleProg_exec {w n : ℕ} (G : MultiDigraph n)
    (a_in a_base : Arr) (r_base : Reg)
    (ha_in : a_in < a_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    {s : State}
    (hin : s.arrs a_in = G.enc) :
    ∃ s' t,
      Exec w (alg33MultiPreambleProg a_in a_base r_base) s s' t ∧
      t ≤ 118 * G.numActivePairs + 105 ∧
      s'.arrs a_base = encGraph G.toSimpleGraph ∧
      s'.regs (r_base + 1) = n ∧
      s'.regs (r_base + 2) = G.numActivePairs ∧
      s'.regs (r_base + 3) = G.numEdges ∧
      s'.regs (r_base + 4) = (edgeListOf G.toSimpleGraph).length ∧
      s'.regs (r_base + 5) = 2 + 3 * G.numActivePairs ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw2 : 2 < 2 ^ w := by romega
  have hm'_w : G.numActivePairs < 2 ^ w := by romega
  have h3m'_w : 3 * G.numActivePairs < 2 ^ w := by romega
  have hm₁_le : (edgeListOf G.toSimpleGraph).length ≤ G.numEdges :=
    card_edgeFinset_toSimpleGraph_le_numEdges G
  have hm₁_w : (edgeListOf G.toSimpleGraph).length < 2 ^ w := by romega
  -- 1. sumEdgeMultProg
  rcases sumEdgeMultProg_exec G a_in (r_base + 1) hw3 hn_w hm3_w hm_w hin with
    ⟨s₁, t₁, hex₁, ht₁, hr1_1, hr2_1, hr3_1, harr₁, hreg₁⟩
  rw [show (r_base + 1 + 1 : Reg) = r_base + 2 by romega] at hr2_1
  rw [show (r_base + 1 + 2 : Reg) = r_base + 3 by romega] at hr3_1
  -- 2. toSimpleGraphEdgeListProg
  have hin₁ : s₁.arrs a_in = G.enc ++ [] := by simp [harr₁, hin]
  rcases toSimpleGraphEdgeListProg_exec G [] a_in (a_base + 1) a_base (r_base + 4)
      (by romega) (by romega) hw3 hn_w hm3_w hin₁ with
    ⟨s₂, t₂, hex₂, ht₂, hdst₂, hr4_2, hr5_2, harr₂, hreg₂⟩
  rw [show (r_base + 4 + 1 : Reg) = r_base + 5 by romega] at hr5_2
  -- 3. r_base + 4 := r_base + 5
  let s₃ := s₂.setReg (r_base + 4) (edgeListOf G.toSimpleGraph).length
  have hex₃ : Exec w (.assign (r_base + 4) (.reg (r_base + 5))) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr5_2, hm₁_w])
  -- 4. r_base + 5 := 2 + 3 * (r_base + 2)
  have hr2_3 : s₃.regs (r_base + 2) = G.numActivePairs := by
    simp only [s₃, State.setReg_regs_ne _ _ (by romega : (r_base + 2 : Reg) ≠ r_base + 4)]
    rw [hreg₂ (r_base + 2) (by romega)]
    exact hr2_1
  let s₄ := s₃.setReg (r_base + 5) (2 + 3 * G.numActivePairs)
  have hex₄ : Exec w (.assign (r_base + 5)
      (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 2))))) s₃ s₄ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_3,
      hw2, hw3, hm'_w, h3m'_w, hm3_w])
  refine ⟨s₄, t₁ + (t₂ + (2 + 6)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by romega,
    by simp [s₄, s₃, hdst₂],
    by
      simp only [s₄, s₃,
        State.setReg_regs_ne _ _ (by romega : (r_base + 1 : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by romega : (r_base + 1 : Reg) ≠ r_base + 4)]
      rw [hreg₂ (r_base + 1) (by romega)]
      exact hr1_1,
    by
      simp only [s₄, State.setReg_regs_ne _ _ (by romega : (r_base + 2 : Reg) ≠ r_base + 5)]
      exact hr2_3,
    by
      simp only [s₄, s₃,
        State.setReg_regs_ne _ _ (by romega : (r_base + 3 : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by romega : (r_base + 3 : Reg) ≠ r_base + 4)]
      rw [hreg₂ (r_base + 3) (by romega)]
      exact hr3_1,
    by simp [s₄, s₃],
    by simp [s₄],
    fun a ha => by
      simp only [s₄, s₃, State.setReg_arrs]
      rw [harr₂ a (by romega) (by romega), harr₁],
    fun r hr => by
      simp only [s₄, s₃,
        State.setReg_regs_ne _ _ (by romega : (r : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by romega : (r : Reg) ≠ r_base + 4)]
      rw [hreg₂ r (by romega), hreg₁ r (by romega)]⟩

/-- Case 1 post-processing (`2 ≤ m₁` and `¬(step6_flag = 0 ∧ m₂ = m₁)`, that is,
`G' = liftSimpleSubgraph G H₃ ≠ G`). -/
def alg33Case1Prog (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.const 0))
    (.seq (buildDirMatProg a_in (a_base + 20) (r_base + 1) (r_base + 2) (r_base + 16))
      (.seq (liftSubgraphProg (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 5)
          (a_base + 20) (a_base + 21) (a_base + 22) a_G_out (a_base + 23)
          (r_base + 1) (r_base + 10) (r_base + 7) (r_base + 16))
        (.ite (.op .le (.const 2) (.reg (r_base + 7)))
          (writeBDCodeProg (a_base + 6) (a_base + 23) a_bd_out
            (r_base + 12) (r_base + 7) (r_base + 16))
          (writeTrivialBDCodeProg a_bd_out (r_base + 7)))))

theorem alg33Case1Prog_exec {w n t₀ ω : ℕ} (G : MultiDigraph n) (m₂ : ℕ)
    (ht₀_pos : 0 < t₀)
    (aliveSet : Finset (Fin ((edgeListOf G.toSimpleGraph).take m₂).length))
    (f_tau : Fin ((edgeListOf G.toSimpleGraph).take m₂).length → Fin t₀)
    (p₀ : ℕ → ℕ)
    (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (_hne_in_G : a_in ≠ a_G_out) (_hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm2_3_w : 2 + 3 * m₂ < 2 ^ w)
    (_hbd_w : 2 + 2 * G.numEdges + G.numEdges < 2 ^ w)
    (hlen_e2 : ((edgeListOf G.toSimpleGraph).take m₂).length = m₂)
    (ht₀_le : t₀ ≤ 2 * m₂)
    (hleaves_card : 2 * (treeLeaves (parentTree t₀ p₀)).card = t₀ + 2)
    (hbd₀ : IsBranchDecompOfWidthLe (3 * ω)
      (graphOfAlive ((edgeListOf G.toSimpleGraph).take m₂)
        (take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)
        aliveSet)
      (parentTree t₀ p₀)
      (tauOfArr ((edgeListOf G.toSimpleGraph).take m₂) t₀ ht₀_pos f_tau))
    {s : State}
    (hin : s.arrs a_in = G.enc)
    (hend : IsEndpointArrs ((edgeListOf G.toSimpleGraph).take m₂) (a_base + 2) (a_base + 3) s)
    (hal : IsBitSet aliveSet (a_base + 4) s)
    (htau : IsTauArr f_tau (a_base + 5) s)
    (hpar : IsParentArr m₂ t₀ p₀ (a_base + 6) s)
    (hr1 : s.regs (r_base + 1) = n)
    (hr2 : s.regs (r_base + 2) = G.numActivePairs)
    (hr10 : s.regs (r_base + 10) = m₂)
    (hr12 : s.regs (r_base + 12) = t₀) :
    let edges₂ := (edgeListOf G.toSimpleGraph).take m₂
    let hloop₂ := take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂
    let H₃ := graphOfAlive edges₂ hloop₂ aliveSet
    let G' := liftSimpleSubgraph G H₃
    ∃ s' t bdCode,
      Exec w (alg33Case1Prog a_in a_G_out a_bd_out a_base r_base) s s' t ∧
      t ≤ n * n + 28 * G.numActivePairs + 210 * m₂ + 160 ∧
      IsValidBranchDecompCode (3 * ω) G' bdCode ∧
      s'.arrs a_G_out = G'.enc ∧
      s'.arrs a_bd_out = bdCode ∧
      s'.regs r_base = 0 ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a) := by
  intro edges₂ hloop₂ H₃ G'
  have hw : 1 < 2 ^ w := by romega
  have hw2 : 2 < 2 ^ w := by romega
  have h0_w : 0 < 2 ^ w := by romega
  have hm₁_le : (edgeListOf G.toSimpleGraph).length ≤ G.numEdges :=
    card_edgeFinset_toSimpleGraph_le_numEdges G
  have hm₂_le_m : m₂ ≤ G.numEdges := by
    have : ((edgeListOf G.toSimpleGraph).take m₂).length ≤ (edgeListOf G.toSimpleGraph).length :=
      List.Sublist.length_le (List.take_sublist m₂ (edgeListOf G.toSimpleGraph))
    romega
  have ht₀_w : t₀ < 2 ^ w := by romega
  -- 1. r_base := 0
  let s₁ := s.setReg r_base 0
  have hex₁ : Exec w (.assign r_base (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 2. buildDirMatProg
  rcases buildDirMatProg_exec G a_in (a_base + 20) (r_base + 1) (r_base + 2) (r_base + 16)
      (by romega) (by romega) (by romega)
      hw3 hn_w hn2_w hm3_w (s := s₁)
      (by simp [s₁, hin])
      (by simp [s₁, State.setReg, hr1])
      (by simp [s₁, State.setReg, hr2]) with
    ⟨s₂, t₂, hex₂, ht₂, hdir_len₂, hdir_val₂, harr₂, hreg₂⟩
  -- 3. liftSubgraphProg
  have harr₂_ne : ∀ a : Arr, a ≠ a_base + 20 → s₂.arrs a = s.arrs a := harr₂
  rcases liftSubgraphProg_exec G m₂ aliveSet f_tau
      (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 5)
      (a_base + 20) (a_base + 21) (a_base + 22) a_G_out (a_base + 23)
      (r_base + 1) (r_base + 10) (r_base + 7) (r_base + 16)
      (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
      (by romega) (by romega) (by romega) (by romega) (by romega)
      (by romega) (by romega) (by romega) (by romega)
      (by romega) (by romega) (by romega)
      hw3 hn_w hn2_w hm2_3_w ht₀_w hlen_e2 (s := s₂)
      (hend.of_arrs_eq (harr₂_ne (a_base + 2) (by romega)) (harr₂_ne (a_base + 3) (by romega)))
      (hal.of_arr_eq (harr₂_ne (a_base + 4) (by romega)))
      (htau.of_arr_eq (harr₂_ne (a_base + 5) (by romega)))
      hdir_len₂ hdir_val₂
      (by rw [hreg₂ (r_base + 1) (by romega)]; simp [s₁, State.setReg, hr1])
      (by rw [hreg₂ (r_base + 10) (by romega)]; simp [s₁, State.setReg, hr10]) with
    ⟨s₃, t₃, hex₃, ht₃, hG_out₃, hsig_len₃, hsig_val₃, hr7_3, harr₃, hreg₃⟩
  let idxList := aliveIndicesUpTo aliveSet edges₂.length
  have hH₃_le : H₃ ≤ G.toSimpleGraph :=
    (graphOfAlive_le_graphOfEdgeList edges₂ hloop₂ aliveSet).trans
      (graphOfEdgeList_take_le (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)
  have hlen_G' : G'.numEdges = idxList.length := by
    rw [numEdges_liftSimpleSubgraph G H₃ hH₃_le, edgeListOf_graphOfAlive_eq, List.length_map]
  have hm_G'_le : G'.numEdges ≤ m₂ := by
    rw [hlen_G', show idxList = aliveIndicesUpTo aliveSet edges₂.length from rfl,
        aliveIndicesUpTo_eq_take_filter]
    calc (((List.finRange edges₂.length).take edges₂.length).filter _).length
      _ ≤ ((List.finRange edges₂.length).take edges₂.length).length := List.length_filter_le _ _
      _ ≤ edges₂.length := List.length_take_le _ _
      _ = m₂ := hlen_e2
  have hm_G'_w : G'.numEdges < 2 ^ w := by romega
  change s₃.regs (r_base + 7) = G'.numEdges at hr7_3
  -- 4. ite on 2 ≤ G'.numEdges
  by_cases hge2 : 2 ≤ G'.numEdges
  · have hcond : (Expr.op .le (.const 2) (.reg (r_base + 7))).eval w s₃ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7_3, hw2, hm_G'_w, hge2, hw]
    -- Prove t₀ ≤ 2 * G'.numEdges from 2 * (treeLeaves T₀).card = t₀ + 2 and bijection with H₃.edgeFinset
    have hcard_leaves :
        H₃.edgeFinset.card = (treeLeaves (parentTree t₀ p₀)).card :=
      Finset.card_bij (fun e _ => tauOfArr edges₂ t₀ ht₀_pos f_tau e)
        (fun e he => hbd₀.2.1.1 he)
        (fun e₁ he₁ e₂ he₂ h => hbd₀.2.1.2.1 he₁ he₂ h)
        (fun v hv => by
          rcases hbd₀.2.1.2.2 hv with ⟨e, he, rfl⟩
          exact ⟨e, he, rfl⟩)
    have hcard_H₃ : H₃.edgeFinset.card = G'.numEdges := by
      rw [numEdges_liftSimpleSubgraph G H₃ hH₃_le, length_edgeListOf_eq_card_edgeFinset]
    have ht₀_le_G' : t₀ ≤ 2 * G'.numEdges := by romega
    have hbd_G' : IsMultiBranchDecompOfWidthLe (3 * ω) G' (parentTree t₀ p₀)
        (fun e : Fin G'.numEdges => f_tau (idxList[e.1]'(by rw [← hlen_G']; exact e.2))) :=
      isMultiBranchDecompOfWidthLe_liftSimpleSubgraph (3 * ω) G m₂ ht₀_pos aliveSet f_tau
        (parentTree t₀ p₀) hbd₀
    have ha6_3 : s₃.arrs (a_base + 6) = s.arrs (a_base + 6) := by
      rw [harr₃ (a_base + 6) (by romega) (by romega) (by romega) (by romega),
          harr₂_ne (a_base + 6) (by romega)]
    have hr12_3 : s₃.regs (r_base + 12) = t₀ := by
      rw [hreg₃ (r_base + 12) (by romega) (by romega), hreg₂ (r_base + 12) (by romega)]
      simp [s₁, State.setReg, hr12]
    rcases writeBDCodeProg_exec G' p₀ ht₀_pos
        (fun e : Fin G'.numEdges => f_tau (idxList[e.1]'(by rw [← hlen_G']; exact e.2)))
        (a_base + 6) (a_base + 23) a_bd_out (r_base + 12) (r_base + 7) (r_base + 16)
        (by romega) (by romega) (by romega)
        (by romega) (by romega)
        hw2 (by romega) hge2 ht₀_le_G' hpar.2.2.2 hbd_G'
        (by rw [ha6_3, hpar.1]; exact hpar.2.1)
        (fun z hz _ hz_t => by simp only [ha6_3]; exact hpar.2.2.1 z hz_t)
        hsig_len₃ (fun e => hsig_val₃ e (by rw [hsig_len₃]; exact e.2)) hr12_3 hr7_3 with
      ⟨s₄, t₄, hex₄, ht₄, hbd_code₄, harr₄, hreg₄⟩
    refine ⟨s₄, 2 + (t₂ + (t₃ + (3 + t₄))), s₄.arrs a_bd_out,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.ite_true hcond (by romega) hex₄))),
      by romega, hbd_code₄,
      by rw [harr₄ a_G_out hne_G_bd (by romega), hG_out₃],
      rfl,
      by rw [hreg₄ r_base (by romega), hreg₃ r_base (by romega) (by romega), hreg₂ r_base (by romega)]; simp [s₁],
      fun r hr => by
        rw [hreg₄ r (by romega), hreg₃ r (by romega) (by romega), hreg₂ r (by romega)]
        simp [s₁, State.setReg, show (r : Reg) ≠ r_base by romega],
      fun a ha haG habd => by
        rw [harr₄ a habd (by romega),
            harr₃ a (by romega) (by romega) haG (by romega),
            harr₂_ne a (by romega)]⟩
  · have hle1 : G'.numEdges ≤ 1 := by romega
    have hcond : (Expr.op .le (.const 2) (.reg (r_base + 7))).eval w s₃ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7_3, hw2, hm_G'_w, hge2, h0_w]
    rcases writeTrivialBDCodeProg_exec (B := 3 * ω) G' a_bd_out (r_base + 7)
        hw3 hle1 hr7_3 with
      ⟨s₄, t₄, hex₄, ht₄, hbd_code₄, harr₄, hreg₄⟩
    refine ⟨s₄, 2 + (t₂ + (t₃ + (3 + t₄))), s₄.arrs a_bd_out,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.ite_false hcond hex₄))),
      by romega, hbd_code₄,
      by rw [harr₄ a_G_out hne_G_bd, hG_out₃],
      rfl,
      by rw [hreg₄ r_base, hreg₃ r_base (by romega) (by romega), hreg₂ r_base (by romega)]; simp [s₁],
      fun r hr => by
        rw [hreg₄ r, hreg₃ r (by romega) (by romega), hreg₂ r (by romega)]
        simp [s₁, State.setReg, show (r : Reg) ≠ r_base by romega],
      fun a ha haG habd => by
        rw [harr₄ a habd,
            harr₃ a (by romega) (by romega) haG (by romega),
            harr₂_ne a (by romega)]⟩

/-- Case 2c post-processing (`2 ≤ m₁`, `step6_flag = 0`, `m₂ = m₁`, so `H₃ = G.toSimpleGraph` and `G' = G`). -/
def alg33Case2cProg (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.const 1))
    (.seq (readSliceProg a_in (.const 0) a_G_out (.reg (r_base + 5)) (r_base + 16))
      (.seq (.assign (r_base + 6) (.reg (r_base + 12)))
        (.seq (.write (a_base + 6) (.const 0) (.const 0))
          (.seq (buildLeafMatProg (a_base + 2) (a_base + 3) (a_base + 5) (a_base + 20)
              (r_base + 1) (r_base + 4) (r_base + 16))
            (.seq (expandSigmaProg a_in (a_base + 20) (a_base + 23)
                (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 16))
              (.seq (initPass2AuxProg (a_base + 6) (a_base + 23) (a_base + 24)
                  (a_base + 25) (a_base + 26) (r_base + 3) (r_base + 6) (r_base + 16))
                (.seq (pass2SplitProg (a_base + 24) (a_base + 25) (a_base + 26) (a_base + 23)
                    (r_base + 3) (r_base + 6) (r_base + 16))
                  (writeBDCodeProg (a_base + 24) (a_base + 23) a_bd_out
                    (r_base + 6) (r_base + 3) (r_base + 16)))))))))

theorem isBranchDecompOfWidthLe_congr_tree {n t : ℕ} (B : ℕ)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    {T₁ T₂ : SimpleGraph (Fin t)} [DecidableRel T₁.Adj] [DecidableRel T₂.Adj]
    (heq : T₁ = T₂) (τ : Sym2 (Fin n) → Fin t)
    (h : IsBranchDecompOfWidthLe B H T₂ τ) :
    IsBranchDecompOfWidthLe B H T₁ τ := by
  subst heq
  convert h

theorem alg33Case2cProg_exec {w n t₀ ω : ℕ} (hω : 1 ≤ ω) (G : MultiDigraph n)
    (hm₁_ge2 : 2 ≤ (edgeListOf G.toSimpleGraph).length)
    (ht₀_ge2 : 2 ≤ t₀) (ht₀_pos : 0 < t₀)
    (f_tau : Fin ((edgeListOf G.toSimpleGraph).take (edgeListOf G.toSimpleGraph).length).length → Fin t₀)
    (p₀ : ℕ → ℕ)
    (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (_hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hbd_w : 2 + 2 * G.numEdges + G.numEdges < 2 ^ w)
    (hmult_w : ∀ p ∈ G.activePairsList, G.edgeMult p.1 p.2 < 2 ^ w)
    (hleaves_card : 2 * (treeLeaves (parentTree t₀ p₀)).card = t₀ + 2)
    (hbd₀ : IsBranchDecompOfWidthLe (3 * ω) G.toSimpleGraph (parentTree t₀ p₀)
      (tauOfArr ((edgeListOf G.toSimpleGraph).take (edgeListOf G.toSimpleGraph).length) t₀ ht₀_pos f_tau))
    {s : State}
    (hin : s.arrs a_in = G.enc)
    (hend : IsEndpointArrs ((edgeListOf G.toSimpleGraph).take (edgeListOf G.toSimpleGraph).length)
      (a_base + 2) (a_base + 3) s)
    (htau : IsTauArr f_tau (a_base + 5) s)
    (hpar : IsParentArr (edgeListOf G.toSimpleGraph).length t₀ p₀ (a_base + 6) s)
    (hr1 : s.regs (r_base + 1) = n)
    (hr2 : s.regs (r_base + 2) = G.numActivePairs)
    (hr3 : s.regs (r_base + 3) = G.numEdges)
    (hr4 : s.regs (r_base + 4) = (edgeListOf G.toSimpleGraph).length)
    (hr5 : s.regs (r_base + 5) = 2 + 3 * G.numActivePairs)
    (hr12 : s.regs (r_base + 12) = t₀) :
    ∃ s' t bdCode,
      Exec w (alg33Case2cProg a_in a_G_out a_bd_out a_base r_base) s s' t ∧
      t ≤ 11 * (n * n) + 86 * G.numActivePairs + 240 * G.numEdges + 150 ∧
      IsValidBranchDecompCode (3 * ω) G bdCode ∧
      s'.arrs a_G_out = G.enc ∧
      s'.arrs a_bd_out = bdCode ∧
      s'.regs r_base = 1 ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a) := by
  let edges₁ := edgeListOf G.toSimpleGraph
  let m₁ := edges₁.length
  change 2 ≤ m₁ at hm₁_ge2
  have htake_eq : edges₁.take m₁ = edges₁ := List.take_length
  have hedges₁ : IsSimpleEdgeList G.toSimpleGraph (edges₁.take m₁) := by
    rw [htake_eq]; exact isSimpleEdgeList_edgeListOf G.toSimpleGraph
  have hm₁_le : m₁ ≤ G.numEdges := card_edgeFinset_toSimpleGraph_le_numEdges G
  have hm_ge2 : 2 ≤ G.numEdges := le_trans hm₁_ge2 hm₁_le
  have hw : 1 < 2 ^ w := by romega
  have hw2 : 2 < 2 ^ w := by romega
  have h0_w : 0 < 2 ^ w := by romega
  have hm_w : G.numEdges < 2 ^ w := by romega
  have h2m_w : 2 * G.numEdges < 2 ^ w := by romega
  have hm₁_w : m₁ < 2 ^ w := by romega
  have ht₀_le_m1 : t₀ ≤ 2 * m₁ := hpar.2.1
  have ht₀_le_2m : t₀ ≤ 2 * G.numEdges := by omega
  have ht₀_w : t₀ < 2 ^ w := by omega
  let p₀' : ℕ → ℕ := fun z => if z = 0 then 0 else p₀ z
  have hp₀'_0 : p₀' 0 = 0 := rfl
  have hp₀'_lt : ∀ z, 0 < z → z < t₀ → p₀' z < z := by
    intro z hz_pos hz_lt
    dsimp [p₀']
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    exact hpar.2.2.2 z hz_pos hz_lt
  have htree_eq : parentTree t₀ p₀' = parentTree t₀ p₀ := by
    apply parentTree_congr
    intro z hz _
    exact ite_eq_right_iff.mpr (fun h => absurd h (by omega))
  -- 1. r_base := 1
  let s₁ := s.setReg r_base 1
  have hex₁ : Exec w (.assign r_base (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  -- 2. readSliceProg a_in 0 a_G_out (r_base + 5) (r_base + 16)
  have henc_w : ∀ x ∈ G.enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · romega
    · exact all_lt_flatTriples G G.activePairsList hn_w hmult_w x hx
  have hin₁ : s₁.arrs a_in = ([] : List ℕ) ++ G.enc ++ [] := by simp [s₁, hin]
  have hr5_1 : s₁.regs (r_base + 5) = G.enc.length := by
    simp [s₁, State.setReg, hr5, G.length_enc]
  rcases readSliceProg_exec a_in a_G_out (.const 0) (r_base + 5) (r_base + 16)
      hne_in_G (by romega) [] G.enc [] rfl rfl henc_w hw (by rw [G.length_enc]; romega)
      (by simp [Expr.eval, checkWord, h0_w]) hin₁ hr5_1 with
    ⟨s₂, t₂, hex₂, ht₂, hG_out₂, harr₂, hreg₂⟩
  -- 3. r_base + 6 := r_base + 12 (t₀)
  have hr12_2 : s₂.regs (r_base + 12) = t₀ := by
    rw [hreg₂ (r_base + 12) (by romega)]; simp [s₁, State.setReg, hr12]
  let s₃ := s₂.setReg (r_base + 6) t₀
  have hex₃ : Exec w (.assign (r_base + 6) (.reg (r_base + 12))) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr12_2, ht₀_w])
  -- 4. write (a_base + 6) 0 0
  have ha6_3 : s₃.arrs (a_base + 6) = s.arrs (a_base + 6) := by
    simp only [s₃, State.setReg_arrs]
    exact harr₂ (a_base + 6) (by romega)
  have ha6_len3 : 0 < (s₃.arrs (a_base + 6)).length := by
    rw [ha6_3, hpar.1]; change 0 < 2 * m₁; omega
  let s₄ := s₃.writeArr (a_base + 6) 0 0
  have hex₄ : Exec w (.write (a_base + 6) (.const 0) (.const 0)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w]) ha6_len3
  -- 5. buildLeafMatProg
  have hlen_take : (edges₁.take m₁).length = m₁ := by rw [htake_eq]
  have hm₁_pos' : 0 < (edges₁.take m₁).length := by rw [hlen_take]; romega
  have harr₄_base : ∀ a : Arr, a ≠ a_G_out → a ≠ a_base + 6 → s₄.arrs a = s.arrs a := by
    intro a haG ha6
    simp only [s₄, s₃, State.writeArr_arrs_ne _ _ _ ha6, State.setReg_arrs]
    exact harr₂ a haG
  rcases buildLeafMatProg_exec G.toSimpleGraph hedges₁ hm₁_pos' ht₀_pos f_tau
      (a_base + 2) (a_base + 3) (a_base + 5) (a_base + 20)
      (r_base + 1) (r_base + 4) (r_base + 16)
      (by romega) (by romega) (by romega) (by romega) (by romega)
      hw hn_w hn2_w (by rw [hlen_take]; exact hm₁_w) ht₀_w (s := s₄)
      (hend.of_arrs_eq
        (harr₄_base (a_base + 2) (by romega) (by romega))
        (harr₄_base (a_base + 3) (by romega) (by romega)))
      (htau.of_arr_eq
        (harr₄_base (a_base + 5) (by romega) (by romega)))
      (by
        simp only [s₄, s₃, State.writeArr_regs,
          State.setReg_regs_ne _ _ (by romega : (r_base + 1 : Reg) ≠ r_base + 6)]
        rw [hreg₂ (r_base + 1) (by romega)]; simp [s₁, State.setReg, hr1])
      (by
        simp only [s₄, s₃, State.writeArr_regs,
          State.setReg_regs_ne _ _ (by romega : (r_base + 4 : Reg) ≠ r_base + 6)]
        rw [hreg₂ (r_base + 4) (by romega)]; simp [s₁, State.setReg, hr4, m₁]; rfl) with
    ⟨s₅, t₅, lmat, hex₅, ht₅, hlmat_valid, hlm_len₅, hlm_val₅, harr₅, hreg₅⟩
  -- 6. expandSigmaProg
  have hin₅ : s₅.arrs a_in = G.enc := by
    rw [harr₅ a_in (by romega),
        harr₄_base a_in hne_in_G (by romega), hin]
  have hr1_5 : s₅.regs (r_base + 1) = n := by
    rw [hreg₅ (r_base + 1) (by romega)]
    simp only [s₄, s₃, State.writeArr_regs,
      State.setReg_regs_ne _ _ (by romega : (r_base + 1 : Reg) ≠ r_base + 6)]
    rw [hreg₂ (r_base + 1) (by romega)]; simp [s₁, State.setReg, hr1]
  have hr2_5 : s₅.regs (r_base + 2) = G.numActivePairs := by
    rw [hreg₅ (r_base + 2) (by romega)]
    simp only [s₄, s₃, State.writeArr_regs,
      State.setReg_regs_ne _ _ (by romega : (r_base + 2 : Reg) ≠ r_base + 6)]
    rw [hreg₂ (r_base + 2) (by romega)]; simp [s₁, State.setReg, hr2]
  have hr3_5 : s₅.regs (r_base + 3) = G.numEdges := by
    rw [hreg₅ (r_base + 3) (by romega)]
    simp only [s₄, s₃, State.writeArr_regs,
      State.setReg_regs_ne _ _ (by romega : (r_base + 3 : Reg) ≠ r_base + 6)]
    rw [hreg₂ (r_base + 3) (by romega)]; simp [s₁, State.setReg, hr3]
  rcases expandSigmaProg_exec G lmat a_in (a_base + 20) (a_base + 23)
      (r_base + 1) (r_base + 2) (r_base + 3) (r_base + 16)
      (by romega) (by romega)
      (by romega) (by romega) (by romega)
      hw3 hn_w hn2_w hm3_w hm_w ht₀_w (s := s₅)
      hin₅ hlm_len₅ hlm_val₅ hr1_5 hr2_5 hr3_5 with
    ⟨s₆, t₆, hex₆, ht₆, hsig_len₆, hsig_val₆, harr₆, hreg₆⟩
  -- 7. initPass2AuxProg
  have hr3_6 : s₆.regs (r_base + 3) = G.numEdges := by
    rw [hreg₆ (r_base + 3) (by romega)]; exact hr3_5
  have hr6_6 : s₆.regs (r_base + 6) = t₀ := by
    rw [hreg₆ (r_base + 6) (by romega), hreg₅ (r_base + 6) (by romega)]
    simp [s₄, s₃]
  have ha6_6 : s₆.arrs (a_base + 6) = (s.arrs (a_base + 6)).set 0 0 := by
    rw [harr₆ (a_base + 6) (by romega), harr₅ (a_base + 6) (by romega)]
    simp [s₄, ha6_3]
  rcases initPass2AuxProg_exec (sigmaFromLeafMat G lmat) p₀'
      (a_base + 6) (a_base + 23) (a_base + 24) (a_base + 25) (a_base + 26)
      (r_base + 3) (r_base + 6) (r_base + 16)
      (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
      (by romega) (by romega)
      hw2 h2m_w ht₀_le_2m hp₀'_lt hp₀'_0 (s := s₆)
      (by rw [ha6_6, List.length_set, hpar.1]; exact ht₀_le_m1)
      (fun z hz hz_t => by
        simp only [ha6_6]
        dsimp [p₀']
        by_cases hz0 : z = 0
        · subst hz0; exact List.getElem_set_self (by rw [ha6_6] at hz; exact hz)
        · simp only [hz0, ↓reduceIte]
          rw [List.getElem_set_ne (by romega : 0 ≠ z)]
          exact hpar.2.2.1 z hz_t)
      hsig_len₆ (fun e => hsig_val₆ e (by rw [hsig_len₆]; exact e.2)) hr3_6 hr6_6 with
    ⟨s₇, t₇, hex₇, ht₇, hpar_len₇, hpar_val₇, hcur_len₇, hcur_val₇, hrem_len₇, hrem_val₇, harr₇, hreg₇⟩
  -- 8. pass2SplitProg
  have hcard_leaves :
      G.toSimpleGraph.edgeFinset.card = (treeLeaves (parentTree t₀ p₀)).card :=
    Finset.card_bij (fun e _ => tauOfArr (edges₁.take m₁) t₀ ht₀_pos f_tau e)
      (fun e he => hbd₀.2.1.1 he)
      (fun e₁ he₁ e₂ he₂ h => hbd₀.2.1.2.1 he₁ he₂ h)
      (fun v hv => by
        rcases hbd₀.2.1.2.2 hv with ⟨e, he, rfl⟩
        exact ⟨e, he, rfl⟩)
  have ht₀_le_sub2 : t₀ ≤ 2 * G.toSimpleGraph.edgeFinset.card - 2 := by romega
  have hbd₀' : IsBranchDecompOfWidthLe (3 * ω) G.toSimpleGraph (parentTree t₀ p₀')
      (tauOfArr (edges₁.take m₁) t₀ ht₀_pos f_tau) :=
    isBranchDecompOfWidthLe_congr_tree (3 * ω) G.toSimpleGraph htree_eq _ hbd₀
  rcases pass2CombInv_init_from_simple hω G hm_ge2 ht₀_ge2 hp₀'_0 hp₀'_lt
      ht₀_le_sub2 hbd₀' hlmat_valid with
    ⟨pairOfLeaf, hinv₀⟩
  have hsig₇_eq : s₇.arrs (a_base + 23) = s₆.arrs (a_base + 23) :=
    harr₇ (a_base + 23) (by romega) (by romega) (by romega)
  rcases pass2SplitProg_exec G (sigmaFromLeafMat G lmat) pairOfLeaf p₀'
      (a_base + 24) (a_base + 25) (a_base + 26) (a_base + 23)
      (r_base + 3) (r_base + 6) (r_base + 16)
      (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
      (by romega) (by romega) (by romega)
      hw2 h2m_w ht₀_w hinv₀ (s := s₇)
      hpar_len₇ hpar_val₇ hcur_len₇ (fun l => hcur_val₇ l (by rw [hcur_len₇]; exact l.2))
      hrem_len₇ (fun l => hrem_val₇ l (by rw [hrem_len₇]; exact l.2))
      (by rw [hsig₇_eq, hsig_len₆])
      (fun e => by simp only [hsig₇_eq]; exact hsig_val₆ e (by rw [hsig_len₆]; exact e.2))
      (by rw [hreg₇ (r_base + 3) (by romega)]; exact hr3_6)
      (by rw [hreg₇ (r_base + 6) (by romega)]; exact hr6_6) with
    ⟨s₈, t₈, t', ht'_pos, p', tauDone', hex₈, ht₈, ht'_le, hp'0, hp'_lt, hbd',
      hpar₈_len, hpar₈_val, hsig₈_len, hsig₈_val, hr6_8, hr3_8, harr₈, hreg₈⟩
  -- 9. writeBDCodeProg
  rcases writeBDCodeProg_exec G p' ht'_pos tauDone'
      (a_base + 24) (a_base + 23) a_bd_out (r_base + 6) (r_base + 3) (r_base + 16)
      (by romega) (by romega) (by romega)
      (by romega) (by romega)
      hw2 (by romega) hm_ge2 ht'_le hp'_lt hbd'
      (by rw [hpar₈_len]; exact ht'_le)
      (fun z hz _ hz_t => hpar₈_val z hz_t hz)
      hsig₈_len (fun e => hsig₈_val e (by rw [hsig₈_len]; exact e.2)) hr6_8 hr3_8 with
    ⟨s₉, t₉, hex₉, ht₉, hbd_code₉, harr₉, hreg₉⟩
  dsimp only [Expr.cost] at ht₂
  rw [G.length_enc] at ht₂
  rw [hlen_take] at ht₅
  refine ⟨s₉, _, s₉.arrs a_bd_out,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ hex₉))))))),
    by romega, hbd_code₉,
    by
      rw [harr₉ a_G_out hne_G_bd (by romega),
          harr₈ a_G_out (by romega) (by romega) (by romega) (by romega),
          harr₇ a_G_out (by romega) (by romega) (by romega),
          harr₆ a_G_out (by romega),
          harr₅ a_G_out (by romega)]
      simp only [s₄, s₃, State.writeArr_arrs_ne _ _ _ (by romega : a_G_out ≠ a_base + 6),
        State.setReg_arrs]
      exact hG_out₂,
    rfl,
    by
      rw [hreg₉ r_base (by romega), hreg₈ r_base (by romega) (by romega),
          hreg₇ r_base (by romega), hreg₆ r_base (by romega),
          hreg₅ r_base (by romega)]
      simp only [s₄, s₃, State.writeArr_regs,
        State.setReg_regs_ne _ _ (by romega : (r_base : Reg) ≠ r_base + 6)]
      rw [hreg₂ r_base (by romega)]
      simp [s₁],
    fun r hr => by
      rw [hreg₉ r (by romega), hreg₈ r (by romega) (by romega),
          hreg₇ r (by romega), hreg₆ r (by romega),
          hreg₅ r (by romega)]
      simp only [s₄, s₃, State.writeArr_regs,
        State.setReg_regs_ne _ _ (by romega : (r : Reg) ≠ r_base + 6)]
      rw [hreg₂ r (by romega)]
      simp [s₁, State.setReg, show (r : Reg) ≠ r_base by romega],
    fun a ha haG habd => by
      rw [harr₉ a habd (by romega),
          harr₈ a (by romega) (by romega) (by romega) (by romega),
          harr₇ a (by romega) (by romega) (by romega),
          harr₆ a (by romega),
          harr₅ a (by romega),
          harr₄_base a haG (by romega)]⟩

theorem alg33Case2cProg_exec' {w n t₀ ω m₂ : ℕ} (hω : 1 ≤ ω) (G : MultiDigraph n)
    (hm₂_eq : m₂ = (edgeListOf G.toSimpleGraph).length)
    (hm₁_ge2 : 2 ≤ (edgeListOf G.toSimpleGraph).length)
    (ht₀_ge2 : 2 ≤ t₀) (ht₀_pos : 0 < t₀)
    (f_tau : Fin ((edgeListOf G.toSimpleGraph).take m₂).length → Fin t₀)
    (p₀ : ℕ → ℕ)
    (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hn2_w : n * n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hbd_w : 2 + 2 * G.numEdges + G.numEdges < 2 ^ w)
    (hmult_w : ∀ p ∈ G.activePairsList, G.edgeMult p.1 p.2 < 2 ^ w)
    (hleaves_card : 2 * (treeLeaves (parentTree t₀ p₀)).card = t₀ + 2)
    (hbd₀ : IsBranchDecompOfWidthLe (3 * ω) G.toSimpleGraph (parentTree t₀ p₀)
      (tauOfArr ((edgeListOf G.toSimpleGraph).take m₂) t₀ ht₀_pos f_tau))
    {s : State}
    (hin : s.arrs a_in = G.enc)
    (hend : IsEndpointArrs ((edgeListOf G.toSimpleGraph).take m₂)
      (a_base + 2) (a_base + 3) s)
    (htau : IsTauArr f_tau (a_base + 5) s)
    (hpar : IsParentArr ((edgeListOf G.toSimpleGraph).take m₂).length t₀ p₀ (a_base + 6) s)
    (hr1 : s.regs (r_base + 1) = n)
    (hr2 : s.regs (r_base + 2) = G.numActivePairs)
    (hr3 : s.regs (r_base + 3) = G.numEdges)
    (hr4 : s.regs (r_base + 4) = (edgeListOf G.toSimpleGraph).length)
    (hr5 : s.regs (r_base + 5) = 2 + 3 * G.numActivePairs)
    (hr12 : s.regs (r_base + 12) = t₀) :
    ∃ s' t bdCode,
      Exec w (alg33Case2cProg a_in a_G_out a_bd_out a_base r_base) s s' t ∧
      t ≤ 11 * (n * n) + 86 * G.numActivePairs + 240 * G.numEdges + 150 ∧
      IsValidBranchDecompCode (3 * ω) G bdCode ∧
      s'.arrs a_G_out = G.enc ∧
      s'.arrs a_bd_out = bdCode ∧
      s'.regs r_base = 1 ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a) := by
  subst hm₂_eq
  rw [List.length_take_of_le (le_refl _)] at hpar
  exact alg33Case2cProg_exec hω G hm₁_ge2 ht₀_ge2 ht₀_pos f_tau p₀
    a_in a_G_out a_bd_out a_base r_base ha_in ha_G ha_bd
    hne_in_G hne_in_bd hne_G_bd hw3 hn_w hn2_w hm3_w hbd_w hmult_w
    hleaves_card hbd₀ hin hend htau hpar hr1 hr2 hr3 hr4 hr5 hr12

/-- Case 2ab post-processing (`m₁ < 2`, so `G' = G`). -/
def alg33Case2abProg (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.const 1))
    (.seq (readSliceProg a_in (.const 0) a_G_out (.reg (r_base + 5)) (r_base + 16))
      (.ite (.op .le (.const 2) (.reg (r_base + 3)))
        (.seq (initSmallPass2Prog (a_base + 6) (a_base + 23)
            (r_base + 3) (r_base + 6) (r_base + 16))
          (.seq (initPass2AuxProg (a_base + 6) (a_base + 23) (a_base + 24)
              (a_base + 25) (a_base + 26) (r_base + 3) (r_base + 6) (r_base + 16))
            (.seq (pass2SplitProg (a_base + 24) (a_base + 25) (a_base + 26) (a_base + 23)
                (r_base + 3) (r_base + 6) (r_base + 16))
              (writeBDCodeProg (a_base + 24) (a_base + 23) a_bd_out
                (r_base + 6) (r_base + 3) (r_base + 16)))))
        (writeTrivialBDCodeProg a_bd_out (r_base + 3))))

theorem alg33Case2abProg_exec {w n ω : ℕ} (hω : 1 ≤ ω) (G : MultiDigraph n)
    (hm₁_lt2 : (edgeListOf G.toSimpleGraph).length < 2)
    (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg)
    (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (hne_G_bd : a_G_out ≠ a_bd_out)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hbd_w : 2 + 2 * G.numEdges + G.numEdges < 2 ^ w)
    (hmult_w : ∀ p ∈ G.activePairsList, G.edgeMult p.1 p.2 < 2 ^ w)
    {s : State}
    (hin : s.arrs a_in = G.enc)
    (hr3 : s.regs (r_base + 3) = G.numEdges)
    (hr5 : s.regs (r_base + 5) = 2 + 3 * G.numActivePairs) :
    ∃ s' t bdCode,
      Exec w (alg33Case2abProg a_in a_G_out a_bd_out a_base r_base) s s' t ∧
      t ≤ 48 * G.numActivePairs + 150 * G.numEdges + 200 ∧
      IsValidBranchDecompCode (3 * ω) G bdCode ∧
      s'.arrs a_G_out = G.enc ∧
      s'.arrs a_bd_out = bdCode ∧
      s'.regs r_base = 1 ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a) := by
  have hw2 : 2 < 2 ^ w := by romega
  have hw : 1 < 2 ^ w := by romega
  have h0_w : 0 < 2 ^ w := by romega
  have hm_w : G.numEdges < 2 ^ w := by romega
  have h2m_w : 2 * G.numEdges < 2 ^ w := by romega
  -- 1. r_base := 1
  let s₁ := s.setReg r_base 1
  have hex₁ : Exec w (.assign r_base (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  -- 2. readSliceProg a_in 0 a_G_out (r_base + 5) (r_base + 16)
  have henc_w : ∀ x ∈ G.enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · romega
    · exact all_lt_flatTriples G G.activePairsList hn_w hmult_w x hx
  have hin₁ : s₁.arrs a_in = ([] : List ℕ) ++ G.enc ++ [] := by simp [s₁, hin]
  have hr5_1 : s₁.regs (r_base + 5) = G.enc.length := by
    simp [s₁, State.setReg, hr5, G.length_enc]
  rcases readSliceProg_exec a_in a_G_out (.const 0) (r_base + 5) (r_base + 16)
      hne_in_G (by romega) [] G.enc [] rfl rfl henc_w hw (by rw [G.length_enc]; romega)
      (by simp [Expr.eval, checkWord, h0_w]) hin₁ hr5_1 with
    ⟨s₂, t₂, hex₂, ht₂, hG_out₂, harr₂, hreg₂⟩
  dsimp only [Expr.cost] at ht₂
  rw [G.length_enc] at ht₂
  have hr3_2 : s₂.regs (r_base + 3) = G.numEdges := by
    rw [hreg₂ (r_base + 3) (by romega)]; simp [s₁, State.setReg, hr3]
  -- 3. ite on 2 ≤ G.numEdges
  by_cases hge2 : 2 ≤ G.numEdges
  · have hcond : (Expr.op .le (.const 2) (.reg (r_base + 3))).eval w s₂ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_2, hw2, hm_w, hge2, hw]
    -- 3a. initSmallPass2Prog
    rcases initSmallPass2Prog_exec (a_base + 6) (a_base + 23)
        (r_base + 3) (r_base + 6) (r_base + 16)
        (by romega) (by romega) (by romega) (by romega) hge2 hw2 h2m_w hr3_2 with
      ⟨s₃, t₃, hex₃, ht₃, hpar_len₃, hpar_val₃, hsig_len₃, hsig_val₃, hr6_3, hr3_3, harr₃, hreg₃⟩
    -- 3b. initPass2AuxProg
    rcases initPass2AuxProg_exec (smallInitSigma G.numEdges) (fun _ => 0)
        (a_base + 6) (a_base + 23) (a_base + 24) (a_base + 25) (a_base + 26)
        (r_base + 3) (r_base + 6) (r_base + 16)
        (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
        (by romega) (by romega)
        hw2 h2m_w (by romega) (fun z hz _ => by romega) rfl (s := s₃)
        (by rw [hpar_len₃]; romega)
        (fun z hz hz_lt => hpar_val₃ z hz_lt hz)
        hsig_len₃ hsig_val₃ hr3_3 hr6_3 with
      ⟨s₄, t₄, hex₄, ht₄, hpar_len₄, hpar_val₄, hcur_len₄, hcur_val₄, hrem_len₄, hrem_val₄, harr₄, hreg₄⟩
    -- 3c. pass2SplitProg
    have hcard_sim : G.toSimpleGraph.edgeFinset.card ≤ 1 := by
      rw [← length_edgeListOf_eq_card_edgeFinset]; romega
    rcases pass2CombInv_init_small hω G hcard_sim hge2 with ⟨pairOfLeaf, hinv₀⟩
    have hsig₄_eq : s₄.arrs (a_base + 23) = s₃.arrs (a_base + 23) :=
      harr₄ (a_base + 23) (by romega) (by romega) (by romega)
    rcases pass2SplitProg_exec G (smallInitSigma G.numEdges) pairOfLeaf (fun _ => 0)
        (a_base + 24) (a_base + 25) (a_base + 26) (a_base + 23)
        (r_base + 3) (r_base + 6) (r_base + 16)
        (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
        (by romega) (by romega) (by romega)
        hw2 h2m_w hw2 hinv₀ (s := s₄)
        hpar_len₄ hpar_val₄
        hcur_len₄ (fun l => hcur_val₄ l (by rw [hcur_len₄]; exact l.2))
        hrem_len₄ (fun l => hrem_val₄ l (by rw [hrem_len₄]; exact l.2))
        (by rw [hsig₄_eq, hsig_len₃])
        (fun e => by simp only [hsig₄_eq]; exact hsig_val₃ e)
        (by rw [hreg₄ (r_base + 3) (by romega)]; exact hr3_3)
        (by rw [hreg₄ (r_base + 6) (by romega)]; exact hr6_3) with
      ⟨s₅, t₅, t', ht'_pos, p', tauDone', hex₅, ht₅, ht'_le, hp'0, hp'_lt, hbd',
        hpar₅_len, hpar₅_val, hsig₅_len, hsig₅_val, hr6_5, hr3_5, harr₅, hreg₅⟩
    -- 3d. writeBDCodeProg
    rcases writeBDCodeProg_exec G p' ht'_pos tauDone'
        (a_base + 24) (a_base + 23) a_bd_out (r_base + 6) (r_base + 3) (r_base + 16)
        (by romega) (by romega) (by romega)
        (by romega) (by romega)
        hw2 (by romega) hge2 ht'_le hp'_lt hbd'
        (by rw [hpar₅_len]; exact ht'_le)
        (fun z hz _ hz_t => hpar₅_val z hz_t hz)
        hsig₅_len (fun e => hsig₅_val e (by rw [hsig₅_len]; exact e.2)) hr6_5 hr3_5 with
      ⟨s₆, t₆, hex₆, ht₆, hbd_code₆, harr₆, hreg₆⟩
    refine ⟨s₆, 2 + (t₂ + (3 + (t₃ + (t₄ + (t₅ + t₆))))), s₆.arrs a_bd_out,
      .seq hex₁ (.seq hex₂ (.ite_true hcond (by romega) (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))),
      by romega, hbd_code₆,
      by
        rw [harr₆ a_G_out hne_G_bd (by romega),
            harr₅ a_G_out (by romega) (by romega) (by romega) (by romega),
            harr₄ a_G_out (by romega) (by romega) (by romega),
            harr₃ a_G_out (by romega) (by romega)]
        exact hG_out₂,
      rfl,
      by
        rw [hreg₆ r_base (by romega), hreg₅ r_base (by romega) (by romega),
            hreg₄ r_base (by romega), hreg₃ r_base (by romega) (by romega), hreg₂ r_base (by romega)]
        simp [s₁],
      fun r hr => by
        rw [hreg₆ r (by romega), hreg₅ r (by romega) (by romega),
            hreg₄ r (by romega), hreg₃ r (by romega) (by romega), hreg₂ r (by romega)]
        simp [s₁, State.setReg, show (r : Reg) ≠ r_base by romega],
      fun a ha haG habd => by
        rw [harr₆ a habd (by romega),
            harr₅ a (by romega) (by romega) (by romega) (by romega),
            harr₄ a (by romega) (by romega) (by romega),
            harr₃ a (by romega) (by romega),
            harr₂ a haG]
        rfl⟩
  · have hle1 : G.numEdges ≤ 1 := by romega
    have hcond : (Expr.op .le (.const 2) (.reg (r_base + 3))).eval w s₂ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_2, hw2, hm_w, hge2, h0_w]
    rcases writeTrivialBDCodeProg_exec (B := 3 * ω) G a_bd_out (r_base + 3)
        hw3 hle1 hr3_2 with
      ⟨s₃, t₃, hex₃, ht₃, hbd_code₃, harr₃, hreg₃⟩
    refine ⟨s₃, 2 + (t₂ + (3 + t₃)), s₃.arrs a_bd_out,
      .seq hex₁ (.seq hex₂ (.ite_false hcond hex₃)),
      by romega, hbd_code₃,
      by rw [harr₃ a_G_out hne_G_bd, hG_out₂],
      rfl,
      by rw [hreg₃ r_base, hreg₂ r_base (by romega)]; simp [s₁],
      fun r hr => by
        rw [hreg₃ r, hreg₂ r (by romega)]
        simp [s₁, State.setReg, show (r : Reg) ≠ r_base by romega],
      fun a _ haG habd => by
        rw [harr₃ a habd, harr₂ a haG]
        rfl⟩

/-- **Top-level Word RAM program for GM XIII Algorithm (3.3) on a multigraph `G : MultiDigraph n`**.
Follows the paper's full description on pages 72–73:
1. Constructs the simple graph `H₁ = G.toSimpleGraph` (`alg33MultiPreambleProg`).
2. If `|E(H₁)| ≥ 2`, runs the core simple-graph algorithm `(alg33CoreProg ω).shift a_base (r_base + 8)`.
   - If `H₃ = H₁` (`step6_flag = 0` and `m₂ = m₁`), converts the branch-decomposition of `H₁` to one
     for `G` (`alg33Case2cProg`), sets `G' = G`, and sets `r_base := 1`.
   - If `H₃ ≠ H₁`, lifts `H₃` to `G' = liftSimpleSubgraph G H₃ ≤ G` (`alg33Case1Prog`), outputs its
     branch-decomposition of width `≤ 3ω`, and sets `r_base := 0`.
3. If `|E(H₁)| < 2`, sets `G' = G` (`alg33Case2abProg`), constructs a branch-decomposition of `G`
   of width `0 ≤ 3ω`, and sets `r_base := 1`. -/
def alg33MultiProg (ω : ℕ) (a_in a_G_out a_bd_out a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (alg33MultiPreambleProg a_in a_base r_base)
    (.ite (.op .le (.const 2) (.reg (r_base + 4)))
      (.seq ((alg33CoreProg ω).shift a_base (r_base + 8))
        (.ite (.op .mul (.op .eq (.reg (r_base + 13)) (.const 0))
                        (.op .eq (.reg (r_base + 10)) (.reg (r_base + 4))))
          (alg33Case2cProg a_in a_G_out a_bd_out a_base r_base)
          (alg33Case1Prog a_in a_G_out a_bd_out a_base r_base)))
      (alg33Case2abProg a_in a_G_out a_bd_out a_base r_base))

theorem edgeMult_le_sumEdgeMult {n : ℕ} (G : MultiDigraph n) (l : List (Fin n × Fin n))
    {p : Fin n × Fin n} (hp : p ∈ l) :
    G.edgeMult p.1 p.2 ≤ G.sumEdgeMult l := by
  induction l with
  | nil => cases hp
  | cons q qs ih =>
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [MultiDigraph.sumEdgeMult]
    · have := ih hp
      simp only [MultiDigraph.sumEdgeMult]
      omega

theorem edgeMult_le_numEdges_of_mem_activePairsList {n : ℕ} (G : MultiDigraph n)
    {p : Fin n × Fin n} (hp : p ∈ G.activePairsList) :
    G.edgeMult p.1 p.2 ≤ G.numEdges := by
  rw [← G.sumEdgeMult_activePairsList]
  exact edgeMult_le_sumEdgeMult G G.activePairsList hp

/-- Word-size exponent constant for `alg33MultiProg ω`. -/
def alg33MultiWordConst (ω : ℕ) : ℕ :=
  16 * ω + 4

/-- Step-count constant for `alg33MultiProg ω`. -/
def alg33MultiStepConst (ω : ℕ) : ℕ :=
  alg33CoreStepConst ω + 1000

theorem alg33MultiProg_word_bounds {w n ω : ℕ} (G : MultiDigraph n)
    (hw_size : wordSize (alg33MultiWordConst ω) ((n + 1) ^ 2 + G.numEdges) ≤ w) :
    3 < 2 ^ w ∧
    n < 2 ^ w ∧
    2 * n < 2 ^ w ∧
    n * n < 2 ^ w ∧
    G.numEdges < 2 ^ w ∧
    2 + 3 * G.numActivePairs < 2 ^ w ∧
    2 + 2 * G.numEdges + G.numEdges < 2 ^ w ∧
    2 + 2 * (edgeListOf G.toSimpleGraph).length < 2 ^ w ∧
    (3 * ω - 2) * n + 2 < 2 ^ w ∧
    3 * ω < 2 ^ w ∧
    (∀ p ∈ G.activePairsList, G.edgeMult p.1 p.2 < 2 ^ w) := by
  let N := (n + 1) ^ 2 + G.numEdges
  let c_word := alg33MultiWordConst ω
  have hN_expand : N = n * n + 2 * n + 1 + G.numEdges := by
    dsimp [N]
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add]
    omega
  have hc_pos : 0 < c_word := by dsimp [c_word, alg33MultiWordConst]; omega
  have hpow_w0 : (N + 2) ^ c_word < 2 ^ (wordSize c_word N) :=
    pow_lt_two_pow_wordSize hc_pos N
  have hpow_mono : 2 ^ (wordSize c_word N) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by omega : 0 < 2) hw_size
  have hpow_w : (N + 2) ^ c_word < 2 ^ w := lt_of_lt_of_le hpow_w0 hpow_mono
  have hpow3_le : (N + 2) ^ 3 ≤ (N + 2) ^ c_word :=
    Nat.pow_le_pow_right (by omega) (by dsimp [c_word, alg33MultiWordConst]; omega)
  have hpow3_expand : 2 + 3 * N < (N + 2) ^ 3 := by
    have hcube : (N + 2) ^ 3 = (N + 2) * ((N + 2) * (N + 2)) := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, Nat.pow_succ, Nat.pow_two, Nat.mul_comm]
    have hge3 : 3 * ((N + 2) * (N + 2)) ≤ (N + 2) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_right _ (by omega : 3 ≤ N + 2)
    have hsq : N + 4 ≤ (N + 2) * (N + 2) := by
      rw [Nat.add_mul, Nat.mul_add]
      omega
    omega
  have hm₁_le : (edgeListOf G.toSimpleGraph).length ≤ G.numEdges :=
    card_edgeFinset_toSimpleGraph_le_numEdges G
  have hm'_le : G.numActivePairs ≤ n * n := G.numActivePairs_le_sq
  have hpow_lin : (16 * ω + 3) * (N + 2) < 2 ^ w := by
    have h1 : 16 * ω + 3 ≤ 2 ^ (16 * ω + 3) := by
      have := Nat.lt_two_pow_self (n := 16 * ω + 3)
      omega
    have h2 : 2 ^ (16 * ω + 3) ≤ (N + 2) ^ (16 * ω + 3) :=
      Nat.pow_le_pow_left (by omega : 2 ≤ N + 2) (16 * ω + 3)
    have h3 : (N + 2) ^ (16 * ω + 3) * (N + 2) = (N + 2) ^ c_word := by
      dsimp [c_word, alg33MultiWordConst]
      rw [← Nat.pow_succ]
    have h4 : (16 * ω + 3) * (N + 2) ≤ (N + 2) ^ (16 * ω + 3) * (N + 2) :=
      Nat.mul_le_mul_right (N + 2) (h1.trans h2)
    omega
  have h3w_N : 3 * ω * n + 3 * ω + 2 ≤ (16 * ω + 3) * (N + 2) := by
    have hn_le_N : n + 1 ≤ N + 2 := by omega
    calc 3 * ω * n + 3 * ω + 2
        ≤ (3 * ω + 2) * (n + 1) := by
          rw [Nat.add_mul, Nat.mul_add]
          omega
      _ ≤ (16 * ω + 3) * (N + 2) :=
          Nat.mul_le_mul (by omega) hn_le_N
  have hB_le_lin : (3 * ω - 2) * n ≤ 3 * ω * n :=
    Nat.mul_le_mul_right n (by omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, fun p hp => ?_⟩
  have := edgeMult_le_numEdges_of_mem_activePairsList G hp
  omega

theorem isBranchDecompOfWidthLe_congr_graph {n t : ℕ} (B : ℕ)
    {H₁ H₂ : SimpleGraph (Fin n)} [DecidableRel H₁.Adj] [DecidableRel H₂.Adj]
    (heq : H₁ = H₂) (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Sym2 (Fin n) → Fin t)
    (h : IsBranchDecompOfWidthLe B H₁ T τ) :
    IsBranchDecompOfWidthLe B H₂ T τ := by
  subst heq
  convert h

/-- Full Word RAM execution theorem for `alg33MultiProg` on a multigraph `G : MultiDigraph n`. -/
theorem alg33MultiProg_exec {w n ω : ℕ} (hω : 2 ≤ ω) (G : MultiDigraph n)
    (a_in a_G_out a_bd_out a_base r_base : ℕ)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out)
    (hw_size : wordSize (alg33MultiWordConst ω) ((n + 1) ^ 2 + G.numEdges) ≤ w)
    {s : State}
    (hin : s.arrs a_in = G.enc) :
    open Classical in
    ∃ (s' : State) (t : ℕ) (G' : MultiDigraph n) (bdCode : List ℕ),
      Exec w (alg33MultiProg ω a_in a_G_out a_bd_out a_base r_base) s s' t ∧
      t ≤ alg33MultiStepConst ω * ((n + 1) ^ 2 + G.numEdges) ∧
      G' ≤ G ∧
      IsValidBranchDecompCode (3 * ω) G' bdCode ∧
      (G' = G ∨ (G' ≠ G ∧ IsAlg33HighWidthCase ω G G')) ∧
      s'.arrs a_G_out = G'.enc ∧
      s'.arrs a_bd_out = bdCode ∧
      s'.regs r_base = (if G' = G then 1 else 0) ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a) := by
  classical
  obtain ⟨hw3, hn_w, h2n_w, hn2_w, hm_w, hm3_w, hbd_w, hm1_w, hB_w, h3w_w, hmult_w⟩ :=
    alg33MultiProg_word_bounds G hw_size
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm₁_le : (edgeListOf G.toSimpleGraph).length ≤ G.numEdges :=
    card_edgeFinset_toSimpleGraph_le_numEdges G
  have hm'_le : G.numActivePairs ≤ n * n := G.numActivePairs_le_sq
  have hS_expand : (n + 1) ^ 2 = n * n + 2 * n + 1 := by
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add]
    omega
  -- Step 1: preamble
  rcases alg33MultiPreambleProg_exec G a_in a_base r_base ha_in
      hw3 hn_w hm3_w hm_w hin with
    ⟨s₁, t_pre, hex_pre, ht_pre, ha_base₁, hr1_1, hr2_1, hr3_1, hr4_1, hr5_1, harr₁, hreg₁⟩
  let edges₁ := edgeListOf G.toSimpleGraph
  let m₁ := edges₁.length
  have hm₁_w : m₁ < 2 ^ w := by change (edgeListOf G.toSimpleGraph).length < 2 ^ w; omega
  -- Step 2: branch on 2 ≤ m₁
  by_cases hm₁_ge2 : 2 ≤ m₁
  · have hcond_m1 : (Expr.op .le (.const 2) (.reg (r_base + 4))).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_1, m₁, edges₁, hw2, hm₁_w, hm₁_ge2, hw]
    -- Step 2a: run core shifted program
    rcases alg33CoreShifted_exec hω G a_base (r_base + 8) hm₁_ge2
        hw3 hn_w h2n_w hm1_w hB_w h3w_w ha_base₁ with
      ⟨s₂, t_core, t₀, ht₀_pos, aliveSet, step6_flag, f_tau, p₀,
        hex_core, ht_core_raw, ht₀_ge2, ht₀_le, hflag_le, hlen_e2,
        hend₂, hal₂, htau₂, hpar₂, hleaves₂, hbd₂,
        hcase2c_imp, hcase1_imp, hr8_2, hr10_2, hr12_2, hr13_2, harr₂, hreg₂⟩
    let m₂ := min m₁ (maxEdgesH2 ω n)
    have hm₂_leB : m₂ ≤ maxEdgesH2 ω n := Nat.min_le_right _ _
    have ht_core : t_core ≤ alg33CoreStepConst ω * (n + 1) ^ 2 :=
      ht_core_raw.trans (alg33Core_time_le hω hm₂_leB ht₀_le)
    have hm₂_le1 : m₂ ≤ m₁ := Nat.min_le_left _ _
    have hm₂_le_m : m₂ ≤ G.numEdges := hm₂_le1.trans hm₁_le
    have hm₂_w : m₂ < 2 ^ w := by omega
    have hflag_w : step6_flag < 2 ^ w := by omega
    have hin₂ : s₂.arrs a_in = G.enc := by
      rw [harr₂ a_in ha_in, harr₁ a_in ha_in, hin]
    have hr1_2 : s₂.regs (r_base + 1) = n := by
      rw [hreg₂ (r_base + 1) (by omega)]; exact hr1_1
    have hr2_2 : s₂.regs (r_base + 2) = G.numActivePairs := by
      rw [hreg₂ (r_base + 2) (by omega)]; exact hr2_1
    have hr3_2 : s₂.regs (r_base + 3) = G.numEdges := by
      rw [hreg₂ (r_base + 3) (by omega)]; exact hr3_1
    have hr4_2 : s₂.regs (r_base + 4) = m₁ := by
      rw [hreg₂ (r_base + 4) (by omega)]; exact hr4_1
    have hr5_2 : s₂.regs (r_base + 5) = 2 + 3 * G.numActivePairs := by
      rw [hreg₂ (r_base + 5) (by omega)]; exact hr5_1
    have hr10_2' : s₂.regs (r_base + 10) = m₂ := by
      have : r_base + 8 + 2 = r_base + 10 := by omega
      rw [← this]; exact hr10_2
    have hr12_2' : s₂.regs (r_base + 12) = t₀ := by
      have : r_base + 8 + 4 = r_base + 12 := by omega
      rw [← this]; exact hr12_2
    have hr13_2' : s₂.regs (r_base + 13) = step6_flag := by
      have : r_base + 8 + 5 = r_base + 13 := by omega
      rw [← this]; exact hr13_2
    -- Step 2b: branch on step6_flag = 0 ∧ m₂ = m₁
    by_cases h2c : step6_flag = 0 ∧ m₂ = m₁
    · rcases h2c with ⟨hflag0, hm₂_eq⟩
      obtain ⟨_, hH3_eq⟩ := hcase2c_imp ⟨hflag0, hm₂_eq⟩
      have hcond_2c :
          (Expr.op .mul (.op .eq (.reg (r_base + 13)) (.const 0))
                        (.op .eq (.reg (r_base + 10)) (.reg (r_base + 4)))).eval w s₂ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr13_2', hr10_2', hr4_2, hflag0, hm₂_eq, h0_w, hm₁_w, hw]
      have hbd₂_G : IsBranchDecompOfWidthLe (3 * ω) G.toSimpleGraph (parentTree t₀ p₀)
          (tauOfArr (edges₁.take m₂) t₀ ht₀_pos f_tau) :=
        isBranchDecompOfWidthLe_congr_graph (3 * ω) hH3_eq (parentTree t₀ p₀) _ hbd₂
      rcases alg33Case2cProg_exec' (by omega : 1 ≤ ω) G hm₂_eq hm₁_ge2 ht₀_ge2 ht₀_pos f_tau p₀
          a_in a_G_out a_bd_out a_base r_base ha_in ha_G ha_bd
          hne_in_G hne_in_bd hne_G_bd hw3 hn_w hn2_w hm3_w hbd_w hmult_w
          hleaves₂ hbd₂_G hin₂ hend₂ htau₂ hpar₂
          hr1_2 hr2_2 hr3_2 hr4_2 hr5_2 hr12_2' with
        ⟨s₃, t_post, bdCode, hex_post, ht_post, hbd_code, hG_out, hbd_out, hr0_3, hreg₃, harr₃⟩
      refine ⟨s₃, _, G, bdCode,
        .seq hex_pre (.ite_true hcond_m1 (by omega)
          (.seq hex_core (.ite_true hcond_2c (by omega) hex_post))),
        by
          dsimp only [Expr.cost, alg33MultiStepConst]
          rw [Nat.add_mul, Nat.mul_add (alg33CoreStepConst ω), Nat.mul_add 1000]
          omega,
        le_rfl, hbd_code, Or.inl rfl, hG_out, hbd_out,
        by simp [hr0_3],
        fun r hr => by
          rw [hreg₃ r hr, hreg₂ r (by omega), hreg₁ r hr],
        fun a ha haG habd => by
          rw [harr₃ a ha haG habd, harr₂ a ha, harr₁ a ha]⟩
    · have hcond_2c :
          (Expr.op .mul (.op .eq (.reg (r_base + 13)) (.const 0))
                        (.op .eq (.reg (r_base + 10)) (.reg (r_base + 4)))).eval w s₂ = some 0 := by
        by_cases hflag0 : step6_flag = 0
        · have hm₂_ne : m₂ ≠ m₁ := fun h => h2c ⟨hflag0, h⟩
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hr13_2', hr10_2', hr4_2, hflag0, hm₂_ne, hm₂_w, hm₁_w, h0_w, hw]
        · by_cases hm₂_eq : m₂ = m₁
          · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr13_2', hr10_2', hr4_2, hflag0, hm₂_eq, hflag_w, hm₁_w, h0_w, hw]
          · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr13_2', hr10_2', hr4_2, hflag0, hm₂_eq, hflag_w, hm₂_w, hm₁_w, h0_w]
      obtain ⟨hG'_ne, hhigh⟩ := hcase1_imp h2c
      have hpar₂' : IsParentArr m₂ t₀ p₀ (a_base + 6) s₂ := by
        rwa [hlen_e2] at hpar₂
      rcases alg33Case1Prog_exec G m₂ ht₀_pos aliveSet f_tau p₀
          a_in a_G_out a_bd_out a_base r_base ha_in ha_G ha_bd hne_in_G hne_in_bd hne_G_bd
          hw3 hn_w hn2_w hm3_w (by omega) hbd_w
          hlen_e2 ht₀_le hleaves₂ hbd₂ hin₂ hend₂ hal₂ htau₂ hpar₂'
          hr1_2 hr2_2 hr10_2' hr12_2' with
        ⟨s₃, t_post, bdCode, hex_post, ht_post, hbd_code, hG_out, hbd_out, hr0_3, hreg₃, harr₃⟩
      let G' := liftSimpleSubgraph G
        (graphOfAlive (edges₁.take m₂)
          (take_loopless_of_isSimpleEdgeList (isSimpleEdgeList_edgeListOf G.toSimpleGraph) m₂)
          aliveSet)
      refine ⟨s₃, _, G', bdCode,
        .seq hex_pre (.ite_true hcond_m1 (by omega)
          (.seq hex_core (.ite_false hcond_2c hex_post))),
        by
          dsimp only [Expr.cost, alg33MultiStepConst]
          rw [Nat.add_mul, Nat.mul_add (alg33CoreStepConst ω), Nat.mul_add 1000]
          omega,
        liftSimpleSubgraph_le G _, hbd_code, Or.inr ⟨hG'_ne, hhigh⟩,
        hG_out, hbd_out,
        by simp [hr0_3]; exact hG'_ne,
        fun r hr => by
          rw [hreg₃ r hr, hreg₂ r (by omega), hreg₁ r hr],
        fun a ha haG habd => by
          rw [harr₃ a ha haG habd, harr₂ a ha, harr₁ a ha]⟩
  · have hm₁_lt2 : (edgeListOf G.toSimpleGraph).length < 2 := by
      change ¬ 2 ≤ m₁ at hm₁_ge2
      dsimp [m₁, edges₁] at hm₁_ge2
      omega
    have hcond_m1 : (Expr.op .le (.const 2) (.reg (r_base + 4))).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_1, m₁, edges₁, hw2, hm₁_w, hm₁_ge2, h0_w]
    have hin₁ : s₁.arrs a_in = G.enc := by
      rw [harr₁ a_in ha_in, hin]
    rcases alg33Case2abProg_exec (by omega : 1 ≤ ω) G hm₁_lt2
        a_in a_G_out a_bd_out a_base r_base ha_G ha_bd hne_in_G hne_G_bd
        hw3 hn_w hm3_w hbd_w hmult_w hin₁ hr3_1 hr5_1 with
      ⟨s₂, t_post, bdCode, hex_post, ht_post, hbd_code, hG_out, hbd_out, hr0_2, hreg₂, harr₂⟩
    refine ⟨s₂, _, G, bdCode,
      .seq hex_pre (.ite_false hcond_m1 hex_post),
      by
        dsimp only [Expr.cost, alg33MultiStepConst]
        rw [Nat.add_mul, Nat.mul_add (alg33CoreStepConst ω), Nat.mul_add 1000]
        omega,
      le_rfl, hbd_code, Or.inl rfl, hG_out, hbd_out,
      by simp [hr0_2],
      fun r hr => by
        rw [hreg₂ r hr, hreg₁ r hr],
      fun a ha haG habd => by
        rw [harr₂ a ha haG habd, harr₁ a ha]⟩

/-- **GM XIII (3.3) on a multigraph, with case certificate (`IsAlg33HighWidthCase`)** (Robertson
and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, pages 72–73):
For every fixed integer `ω ≥ 2`, `alg33MultiProg ω` computes on a multigraph `G : MultiDigraph n` in
`O(v² + ε)` time on the Word RAM (`≤ alg33MultiStepConst ω * ((n + 1) ^ 2 + G.numEdges)` steps)
a subdigraph `G' ≤ G` and a serialized branch-decomposition `bdCode` of `G'` of width `≤ 3ω`, such
that either `G' = G` or `G' ≠ G ∧ IsAlg33HighWidthCase ω G G'`. -/
theorem algorithm_3_3_multigraph_cases (ω : ℕ) (hω : 2 ≤ ω)
    (a_in a_G_out a_bd_out a_base r_base : ℕ)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out) :
    open Classical in
    ∃ (C₃₃ c_w : ℕ), 0 < C₃₃ ∧ 0 < c_w ∧
      ∀ (n : ℕ) (G : MultiDigraph n) (w : ℕ),
        wordSize c_w ((n + 1) ^ 2 + G.numEdges) ≤ w →
        ∀ (s : State),
          s.arrs a_in = G.enc →
          ∃ (s' : State) (t : ℕ) (G' : MultiDigraph n) (bdCode : List ℕ),
            Exec w (alg33MultiProg ω a_in a_G_out a_bd_out a_base r_base) s s' t ∧
            t ≤ C₃₃ * ((n + 1) ^ 2 + G.numEdges) ∧
            G' ≤ G ∧
            IsValidBranchDecompCode (3 * ω) G' bdCode ∧
            (G' = G ∨ (G' ≠ G ∧ IsAlg33HighWidthCase ω G G')) ∧
            s'.arrs a_G_out = G'.enc ∧
            s'.arrs a_bd_out = bdCode ∧
            s'.regs r_base = (if G' = G then 1 else 0) ∧
            (∀ r < r_base, s'.regs r = s.regs r) ∧
            (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a) := by
  classical
  refine ⟨alg33MultiStepConst ω, alg33MultiWordConst ω,
    by dsimp [alg33MultiStepConst, alg33CoreStepConst]; omega,
    by dsimp [alg33MultiWordConst]; omega,
    fun n G w hw_size s hin =>
      alg33MultiProg_exec hω G a_in a_G_out a_bd_out a_base r_base
        ha_in ha_G ha_bd hne_in_G hne_in_bd hne_G_bd hw_size hin⟩

/-- **GM XIII (3.3) on a multigraph** (Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths
Problem*, pages 72–73):
"Let $\omega \ge 2$ be some integer.
(3.3) Algorithm.
*Input:* A graph $G$ with $|E(G)| \ge 2$.
*Output:* A subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of width $\le 3\omega$, such that
either $G' = G$ or $G'$ has branch-width $\ge \omega$.
*Running time:* $O(v^2 + \varepsilon)$."

For every fixed integer `ω ≥ 2`, `alg33MultiProg ω` computes on a multigraph `G : MultiDigraph n` in
`O(v² + ε)` time on the Word RAM (`≤ alg33MultiStepConst ω * ((n + 1) ^ 2 + G.numEdges)` steps)
a subdigraph `G' ≤ G` and a serialized branch-decomposition `bdCode` of `G'` of width `≤ 3ω`, such
that either `G' = G` or `G'` has branch-width `≥ ω` in `GM13`'s terms
(`¬ GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph (ω - 1)`), proved from `IsAlg33HighWidthCase` via
`GM13.theorem_3_2_proof`, `GM13.theorem_3_1_proof`, and `GM13.algorithm_3_3_step_6_deleteEdge`
(`IsAlg33HighWidthCase.not_graphBranchWidthLE`). -/
theorem algorithm_3_3_multigraph (ω : ℕ) (hω : 2 ≤ ω)
    (a_in a_G_out a_bd_out a_base r_base : ℕ)
    (ha_in : a_in < a_base) (ha_G : a_G_out < a_base) (ha_bd : a_bd_out < a_base)
    (hne_in_G : a_in ≠ a_G_out) (hne_in_bd : a_in ≠ a_bd_out) (hne_G_bd : a_G_out ≠ a_bd_out) :
    open Classical in
    ∃ (C₃₃ c_w : ℕ), 0 < C₃₃ ∧ 0 < c_w ∧
      ∀ (n : ℕ) (G : MultiDigraph n) (w : ℕ),
        wordSize c_w ((n + 1) ^ 2 + G.numEdges) ≤ w →
        ∀ (s : State),
          s.arrs a_in = G.enc →
          ∃ (s' : State) (t : ℕ) (G' : MultiDigraph n) (bdCode : List ℕ),
            Exec w (alg33MultiProg ω a_in a_G_out a_bd_out a_base r_base) s s' t ∧
            t ≤ C₃₃ * ((n + 1) ^ 2 + G.numEdges) ∧
            G' ≤ G ∧
            IsValidBranchDecompCode (3 * ω) G' bdCode ∧
            (G' = G ∨ ¬ GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph (ω - 1)) ∧
            s'.arrs a_G_out = G'.enc ∧
            s'.arrs a_bd_out = bdCode ∧
            s'.regs r_base = (if G' = G then 1 else 0) ∧
            (∀ r < r_base, s'.regs r = s.regs r) ∧
            (∀ a < a_base, a ≠ a_G_out → a ≠ a_bd_out → s'.arrs a = s.arrs a) := by
  classical
  rcases algorithm_3_3_multigraph_cases ω hω a_in a_G_out a_bd_out a_base r_base
      ha_in ha_G ha_bd hne_in_G hne_in_bd hne_G_bd with
    ⟨C₃₃, c_w, hC, hcw, hexec⟩
  refine ⟨C₃₃, c_w, hC, hcw, fun n G w hw_size s hin => ?_⟩
  rcases hexec n G w hw_size s hin with
    ⟨s', t, G', bdCode, hex, ht, hle, hbd, hcases, hG_out, hbd_out, hr0, hreg, harr⟩
  refine ⟨s', t, G', bdCode, hex, ht, hle, hbd, ?_, hG_out, hbd_out, hr0, hreg, harr⟩
  rcases hcases with heq | ⟨_, hhigh⟩
  · exact Or.inl heq
  · exact Or.inr (hhigh.not_graphBranchWidthLE hω)

end GraphMinor.Compute
