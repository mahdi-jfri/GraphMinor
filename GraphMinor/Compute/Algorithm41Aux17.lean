module

public import GraphMinor.Compute.Algorithm41Aux16

/-!
# Initializing the Core Memory for GM XIII (4.1)

After reading the input and numbering the tree, the algorithm allocates its
working tables and set-union arenas. The capacity below reserves space for all
tree combinations and isolated vertices, as well as every table buffer.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Fixed coefficient for the workspace capacity. -/
def arena41Coeff (δ ξ ω : ℕ) : ℕ :=
  2 + K_node δ ξ ω + K_iso δ ξ ω + Q_max ξ ω + S_tab δ ξ ω

/-- Capacity shared by the vertex and edge set-union arenas. -/
def arena41Capacity (δ ξ ω n t : ℕ) : ℕ :=
  1 + (n + t + 1) * arena41Coeff δ ξ ω

/-- The capacity covers the working buffers and both DP passes. -/
theorem arena41Capacity_bounds (δ ξ ω n t : ℕ) :
    let cap := arena41Capacity δ ξ ω n t
    1 ≤ cap ∧ Q_max ξ ω ≤ cap ∧ S_tab δ ξ ω ≤ cap ∧ t ≤ cap ∧
      t * Q_max ξ ω ≤ cap ∧ t * S_tab δ ξ ω ≤ cap ∧
      1 + t * K_node δ ξ ω + n * K_iso δ ξ ω ≤ cap := by
  have hC : 1 ≤ arena41Coeff δ ξ ω := by unfold arena41Coeff; omega
  have hQ : Q_max ξ ω ≤ arena41Coeff δ ξ ω := by unfold arena41Coeff; omega
  have hS : S_tab δ ξ ω ≤ arena41Coeff δ ξ ω := by unfold arena41Coeff; omega
  have hK : K_node δ ξ ω ≤ arena41Coeff δ ξ ω := by unfold arena41Coeff; omega
  have hI : K_iso δ ξ ω ≤ arena41Coeff δ ξ ω := by unfold arena41Coeff; omega
  have hCcap : arena41Coeff δ ξ ω ≤ (n + t + 1) * arena41Coeff δ ξ ω := by
    calc
      arena41Coeff δ ξ ω = 1 * arena41Coeff δ ξ ω := by omega
      _ ≤ (n + t + 1) * arena41Coeff δ ξ ω := Nat.mul_le_mul_right _ (by omega)
  have hsum : n + t + 1 ≤ (n + t + 1) * arena41Coeff δ ξ ω := by
    calc
      n + t + 1 = (n + t + 1) * 1 := by omega
      _ ≤ (n + t + 1) * arena41Coeff δ ξ ω := Nat.mul_le_mul_left _ hC
  have htQ := Nat.mul_le_mul (show t ≤ n + t + 1 by omega) hQ
  have htS := Nat.mul_le_mul (show t ≤ n + t + 1 by omega) hS
  have htK := Nat.mul_le_mul_left t hK
  have hnI := Nat.mul_le_mul_left n hI
  dsimp only [arena41Capacity]
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hCcap hsum htQ htS ⊢
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · exact htQ.trans (Nat.le_add_left _ _)
  constructor
  · exact htS.trans (Nat.le_add_left _ _)
  · omega

/-- Compute arena capacity from the input vertex count in `r_0` and tree size in `r_2`. -/
def arena41CapacityExpr (δ ξ ω : ℕ) : Expr :=
  .op .add (.const 1)
    (.op .mul (.op .add (.op .add (.reg 0) (.reg 2)) (.const 1)) (.const (arena41Coeff δ ξ ω)))

private theorem arena41CapacityExpr_eval {w δ ξ ω n t : ℕ} {s : State}
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (ht : t < 2 ^ w)
    (hcap : arena41Capacity δ ξ ω n t < 2 ^ w)
    (hr0 : s.regs 0 = n) (hr2 : s.regs 2 = t) :
    (arena41CapacityExpr δ ξ ω).eval w s = some (arena41Capacity δ ξ ω n t) := by
  have hC : 1 ≤ arena41Coeff δ ξ ω := by unfold arena41Coeff; omega
  have hsum : n + t + 1 ≤ (n + t + 1) * arena41Coeff δ ξ ω := by
    calc
      n + t + 1 = (n + t + 1) * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hC
  have hcoeff : arena41Coeff δ ξ ω ≤ (n + t + 1) * arena41Coeff δ ξ ω := by
    calc
      arena41Coeff δ ξ ω = 1 * arena41Coeff δ ξ ω := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hprod : (n + t + 1) * arena41Coeff δ ξ ω < 2 ^ w := by unfold arena41Capacity at hcap; omega
  have hcoeff_w : arena41Coeff δ ξ ω < 2 ^ w := hcoeff.trans_lt hprod
  have hsum_w : n + t + 1 < 2 ^ w := hsum.trans_lt hprod
  have hnt_w : n + t < 2 ^ w := by omega
  change 1 + (n + t + 1) * arena41Coeff δ ξ ω < 2 ^ w at hcap
  unfold arena41CapacityExpr
  simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0, hr2, hn, ht, hw, hcoeff_w,
    hsum_w, hnt_w, hprod, arena41Capacity, hcap]

/-- Read the input, allocate all working memory, and initialize the two arena cursors. -/
def alg41InitProg (δ ξ ω : ℕ) : Cmd :=
  .seq alg41PreprocProg
    (.seq (.assign 18 (arena41CapacityExpr δ ξ ω))
      (.seq (alloc41WorkProg δ ξ ω)
        (.seq (.assign r_kv (.const 1)) (.assign r_ke (.const 1)))))


/-- Preprocessing and allocation establish the concrete memory invariants needed by the DP.
The execution starts with only the encoded input in `inArr`. -/
theorem alg41InitProg_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw3 : 3 < 2 ^ w) (hsz : 7 * alg41CoreSize inp < 2 ^ w)
    (hcap : arena41Capacity δ ξ ω inp.G.numVerts inp.t < 2 ^ w)
    {s₀ : State} (hinput : s₀.arrs inArr = encAlg41CoreIn inp) :
    ∃ s' time, Exec w (alg41InitProg δ ξ ω) s₀ s' time ∧
      time ≤ 250 * alg41CoreSize inp + 28 * (3 + arena41Capacity δ ξ ω inp.G.numVerts inp.t) + 20 ∧
      TreeDPStateInv δ ξ ω inp s' ∧ ArenaStateInv inp.G 1 1 s' ∧
      (s'.arrs a_vkd).length = arena41Capacity δ ξ ω inp.G.numVerts inp.t ∧
      (s'.arrs a_ekd).length = arena41Capacity δ ξ ω inp.G.numVerts inp.t := by
  let cap := arena41Capacity δ ξ ω inp.G.numVerts inp.t
  have hn : inp.G.numVerts < 2 ^ w := by unfold alg41CoreSize at hsz; omega
  have ht : inp.t < 2 ^ w := by have := inp.ht_le; unfold alg41CoreSize at hsz; omega
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨hcap1, hQ, hS, htcap, htQ, htS, _⟩ := arena41Capacity_bounds δ ξ ω inp.G.numVerts inp.t
  rcases alg41PreprocProg_exec inp hw3 hsz hinput with
    ⟨s₁, t₁, hex₁, htime₁, hr0, hr1, hr2, hhead, htail, hZ, _, _, htot, hedge, hcapArr, hdegC, hch⟩
  let s₂ := s₁.setReg 18 cap
  have hex₂ : Exec w (.assign 18 (arena41CapacityExpr δ ξ ω)) s₁ s₂ 10 := by
    have h := arena41CapacityExpr_eval hw1 hn ht hcap hr0 hr2
    exact .assign h
  rcases alloc41WorkProg_exec hcap hQ hS htcap htQ htS
      (show s₂.regs 2 = inp.t from hr2) (State.setReg_regs_self s₁ 18 cap) with
    ⟨s₃, t₃, hex₃, htime₃, hreg₃, hwork₃, hframe₃⟩
  let s₄ := s₃.setReg r_kv 1
  have hex₄ : Exec w (.assign r_kv (.const 1)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  let s₅ := s₄.setReg r_ke 1
  have hex₅ : Exec w (.assign r_ke (.const 1)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  have hlow : ∀ r : ℕ, r < 3 → s₅.regs r = s₁.regs r := by
    intro r hr
    simp only [s₅, s₄, State.setReg_regs_ne _ _ (show r ≠ r_ke by change r ≠ (4 : ℕ); omega),
      State.setReg_regs_ne _ _ (show r ≠ r_kv by change r ≠ (3 : ℕ); omega)]
    rw [hreg₃ r]
    exact State.setReg_regs_ne _ _ (show r ≠ 18 by omega)
  have hsmall : ∀ a : ℕ, a < 20 → s₅.arrs a = s₁.arrs a := by
    intro a ha
    exact hframe₃ a (Or.inl ha)
  have hwork : ∀ a : ℕ, 20 ≤ a → a < 48 →
      s₅.arrs a = List.replicate (work41Length δ ξ ω inp.t cap a) 0 := hwork₃
  have hlength : ∀ a : ℕ, 20 ≤ a → a < 48 →
      (s₅.arrs a).length = work41Length δ ξ ω inp.t cap a := by
    intro a ha hb
    rw [hwork a ha hb, List.length_replicate]
  have hinv : TreeDPStateInv δ ξ ω inp s₅ := by
    refine ⟨(hlow 0 (by decide)).trans hr0, (hlow 1 (by decide)).trans hr1,
      (hlow 2 (by decide)).trans hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hsmall a_head (by decide)).trans hhead
    · exact (hsmall a_tail (by decide)).trans htail
    · exact (hsmall a_Z (by decide)).trans hZ
    · exact (hsmall a_tot (by decide)).trans htot
    · exact (hsmall a_edge (by decide)).trans hedge
    · exact (hsmall a_cap (by decide)).trans hcapArr
    · exact (hsmall a_degC (by decide)).trans hdegC
    · exact (hsmall a_ch (by decide)).trans hch
    · simpa [work41Length, a_acc_zV] using hlength a_acc_zV (by decide) (by decide)
    · simpa [work41Length, a_acc_zI] using hlength a_acc_zI (by decide) (by decide)
    · simpa [work41Length, a_acc_vv] using hlength a_acc_vv (by decide) (by decide)
    · simpa [work41Length, a_acc_ve] using hlength a_acc_ve (by decide) (by decide)
    · simpa [work41Length, a_acc_em] using hlength a_acc_em (by decide) (by decide)
    · simpa [work41Length, a_rhs_zV] using hlength a_rhs_zV (by decide) (by decide)
    · simpa [work41Length, a_rhs_zI] using hlength a_rhs_zI (by decide) (by decide)
    · simpa [work41Length, a_rhs_vv] using hlength a_rhs_vv (by decide) (by decide)
    · simpa [work41Length, a_rhs_ve] using hlength a_rhs_ve (by decide) (by decide)
    · simpa [work41Length, a_rhs_em] using hlength a_rhs_em (by decide) (by decide)
    · simpa [work41Length, a_out_zV] using hlength a_out_zV (by decide) (by decide)
    · simpa [work41Length, a_out_zI] using hlength a_out_zI (by decide) (by decide)
    · simpa [work41Length, a_out_vv] using hlength a_out_vv (by decide) (by decide)
    · simpa [work41Length, a_out_ve] using hlength a_out_ve (by decide) (by decide)
    · simpa [work41Length, a_out_em] using hlength a_out_em (by decide) (by decide)
    · simpa [work41Length, a_sub_tid] using hlength a_sub_tid (by decide) (by decide)
    · simpa [work41Length, a_sub_q] using hlength a_sub_q (by decide) (by decide)
    · simpa [work41Length, a_sub_zV] using hlength a_sub_zV (by decide) (by decide)
    · simpa [work41Length, a_sub_zI] using hlength a_sub_zI (by decide) (by decide)
    · simpa [work41Length, a_sub_vv] using hlength a_sub_vv (by decide) (by decide)
    · simpa [work41Length, a_sub_ve] using hlength a_sub_ve (by decide) (by decide)
    · simpa [work41Length, a_sub_em] using hlength a_sub_em (by decide) (by decide)
  have hV : s₅.arrs a_vkd = List.replicate cap 0 := by
    simpa [work41Length, a_vkd] using hwork a_vkd (by decide) (by decide)
  have hV1 : s₅.arrs a_vv1 = List.replicate cap 0 := by
    simpa [work41Length, a_vv1] using hwork a_vv1 (by decide) (by decide)
  have hV2 : s₅.arrs a_vv2 = List.replicate cap 0 := by
    simpa [work41Length, a_vv2] using hwork a_vv2 (by decide) (by decide)
  have hE : s₅.arrs a_ekd = List.replicate cap 0 := by
    simpa [work41Length, a_ekd] using hwork a_ekd (by decide) (by decide)
  have hE1 : s₅.arrs a_ev1 = List.replicate cap 0 := by
    simpa [work41Length, a_ev1] using hwork a_ev1 (by decide) (by decide)
  have hE2 : s₅.arrs a_ev2 = List.replicate cap 0 := by
    simpa [work41Length, a_ev2] using hwork a_ev2 (by decide) (by decide)
  have har : ArenaStateInv inp.G 1 1 s₅ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [s₅, s₄]
    · exact State.setReg_regs_self ..
    · rw [hV, hV1, hV2]
      exact arenaWF_init inp.G.numVerts cap hcap1
    · rw [hE, hE1, hE2]
      exact arenaWF_init inp.G.numEdges cap hcap1
  refine ⟨s₅, t₁ + (10 + (t₃ + (2 + 2))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, hinv, har, ?_, ?_⟩
  · rw [Nat.mul_comm 28]
    omega
  · rw [hV, List.length_replicate]
  · rw [hE, List.length_replicate]

end GraphMinor.Compute
