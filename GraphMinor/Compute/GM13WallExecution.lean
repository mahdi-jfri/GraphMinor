module

public import GraphMinor.Compute.GM13WallRounding

/-!
# The two search parameters of Graph Minors XIII, (7.1)

The wall test uses the ceiling of the threshold and the decomposition search
uses its floor. The same program as (7.2) works with these two subroutines.
-/

public section
namespace GraphMinor.Compute
open GraphMinor GM13

/-- Execution of the program in XIII (7.1), page 89, with separate integer
parameters for the wall test and the decomposition search. -/
theorem alg71Prog_exec (h ω₀ k : ℕ) (hh : 1 ≤ h) (hω₀ : 2 ≤ ω₀)
    (hk : 2 ≤ k) (hkle : k ≤ ω₀)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ω₀)
    (hwidth : ∀ {n} (G : MultiDigraph n), ¬ HasDigraphModel (elemWallEdges h) G →
      GraphMinor.GM13.GraphBranchWidthLE G.toGMDigraph.toGraph k)
    (a_in a_out a_scratch a_base r_base : ℕ)
    (P33_44 P41_44 P33_G : Cmd)
    (hP33_44 : Alg33Spec ω₀ (a_scratch + 1) (a_scratch + 2) (a_scratch + 3) a_base r_base P33_44)
    (hP41_44 : Alg41Spec 0 ((elemWallEdges h).length + elemWallNumVerts h) (3 * ω₀)
      (a_scratch + 2) (a_scratch + 4) (a_scratch + 3) (a_scratch + 5) (a_scratch + 6)
      a_base r_base P41_44)
    (hP33_G : Alg33Spec k a_in (a_scratch + 7) (a_scratch + 8) a_base r_base P33_G)
    (ha_in_out : a_in ≠ a_out)
    (ha_in_lt : a_in < a_scratch)
    (ha_out_lt : a_out < a_scratch)
    (ha_sc_lt : a_scratch + 8 < a_base) :
    ∃ (C₇₂ c_w : ℕ), 0 < C₇₂ ∧ 0 < c_w ∧
      ∀ (n : ℕ) (G : MultiDigraph n) (w : ℕ),
        wordSize c_w ((n + 1) ^ 2 + (G.numEdges + n + 1)) ≤ w →
        ∀ (s : State),
          s.arrs a_in = G.enc →
          ∃ (s' : State) (t : ℕ),
            Exec w (alg72Prog h hh a_in a_out a_scratch r_base P33_44 P41_44 P33_G) s s' t ∧
            t ≤ C₇₂ * ((n + 1) ^ 2 + (G.numEdges + n + 1)) ∧
            IsAlg72Output h k ⟨n, G⟩ (s'.arrs a_out) ∧
            (∀ r < r_base, s'.regs r = s.regs r) ∧
            (∀ a < a_scratch, a ≠ a_out → s'.arrs a = s.arrs a) := by
  rcases alg44Prog_exec (elemWallEdges h) ω₀ hω₀ h71 a_in a_out a_scratch a_base r_base
      P33_44 P41_44 hP33_44 hP41_44 (by omega) (Or.inl ha_out_lt) (by omega) with
    ⟨C₄₄, c_w44, hC44_pos, hcw44_pos, h44_exec⟩
  rcases hP33_G with ⟨C₃₃, c_w33, hC33_pos, hcw33_pos, h33_exec⟩
  let C₇₂ := alg72TimeConst h C₄₄ C₃₃
  let c_w := alg72WordConst h ω₀ c_w44 c_w33
  have hC72_pos : 0 < C₇₂ := by unfold C₇₂ alg72TimeConst; dsimp only; omega
  have hcw_pos : 0 < c_w := by unfold c_w alg72WordConst; dsimp only; omega
  refine ⟨C₇₂, c_w, hC72_pos, hcw_pos, fun n G w hw s hin => ?_⟩
  have h_prod_lt : c_w * ((n + 1) ^ 2 + (G.numEdges + n + 1)) < 2 ^ w :=
    mul_lt_two_pow_of_wordSize_le hcw_pos hw
  have hm_act_le : G.numActivePairs ≤ n * n := G.numActivePairs_le_sq
  rcases alg72_word_bounds hm_act_le h_prod_lt with
    ⟨hw3, h3ω_w, he_w, hG_w, hnn_w, henc_w, hbuf_w⟩
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  -- Step (1): Execute alg44Prog on G:
  have hw_44 : wordSize c_w44 ((n + 1) ^ 2) ≤ w := by
    refine le_trans (wordSize_mono_left (c₂ := c_w) (by unfold c_w alg72WordConst; dsimp only; omega) _) ?_
    exact le_trans (wordSize_mono_right c_w (by omega)) hw
  rcases h44_exec n G w hw_44 s hin with
    ⟨s₁, t₁, hex₁, ht₁, h44_out, hreg₁, harr₁⟩
  have ha_in_s1 : s₁.arrs a_in = G.enc := by
    rw [harr₁ a_in ha_in_lt ha_in_out, hin]
  -- Case split on the output of alg44Prog:
  rcases h44_out with ⟨M, hM_valid, hout_M⟩ | ⟨hnoG, hout_0⟩
  · -- Case 1: alg44Prog found a model M of the elementary wall of height h in G:
    have hlen_pos : 0 < (s₁.arrs a_out).length := by simp [hout_M]
    have hget0 : (s₁.arrs a_out)[0]'hlen_pos = 1 := by simp [hout_M]
    have heval_rd : (Expr.read a_out (.const 0)).eval w s₁ = some 1 := by
      simp [Expr.eval, checkWord, hw0, hw1, hlen_pos, hget0]
    let s₂ := s₁.setReg r_base 1
    have hex_rd : Exec w (.assign r_base (.read a_out (.const 0))) s₁ s₂ 3 := .assign heval_rd
    have hcond : (Expr.op .eq (.reg r_base) (.const 1)).eval w s₂ = some 1 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1]
    have ha_in_s2 : s₂.arrs a_in = G.enc := by simpa [s₂] using ha_in_s1
    have hout_s2 : s₂.arrs a_out = [1] ++ M.enc := by simpa [s₂] using hout_M
    rcases modelToWallProg_exec hh G M hM_valid a_in a_out a_scratch r_base
        ha_in_lt ha_out_lt ha_in_out hw3 hG_w hnn_w henc_w hbuf_w
        ha_in_s2 hout_s2 with
      ⟨s₃, t_wall, hex_wall, ht_wall, hW_valid, hout_wall, harr_wall, hreg_wall⟩
    have hex_ite :
        Exec w (.ite (.op .eq (.reg r_base) (.const 1))
          (modelToWallProg h hh a_in a_out a_scratch r_base)
          (.seq P33_G (prependZeroProg (a_scratch + 8) a_out r_base))) s₂ s₃ (3 + t_wall) :=
      .ite_true hcond (by omega) hex_wall
    refine ⟨s₃, t₁ + (3 + (3 + t_wall)), .seq hex₁ (.seq hex_rd hex_ite),
      alg72_time_bound_true hm_act_le ht₁ ht_wall,
      Or.inr ⟨modelToWall hh M, hW_valid, hout_wall⟩, ?_, ?_⟩
    · intro r hr
      have hr_ne : (r : Reg) ≠ r_base := by omega
      rw [hreg_wall r hr]
      simp [s₂, hr_ne, hreg₁ r hr]
    · intro a ha ha_out
      rw [harr_wall a ha ha_out]
      simpa [s₂] using harr₁ a ha ha_out
  · -- Case 2: alg44Prog reported no model of the elementary wall of height h in G:
    have hlen_pos : 0 < (s₁.arrs a_out).length := by simp [hout_0]
    have hget0 : (s₁.arrs a_out)[0]'hlen_pos = 0 := by simp [hout_0]
    have heval_rd : (Expr.read a_out (.const 0)).eval w s₁ = some 0 := by
      simp [Expr.eval, checkWord, hw0, hlen_pos, hget0]
    let s₂ := s₁.setReg r_base 0
    have hex_rd : Exec w (.assign r_base (.read a_out (.const 0))) s₁ s₂ 3 := .assign heval_rd
    have hcond : (Expr.op .eq (.reg r_base) (.const 1)).eval w s₂ = some 0 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw0, hw1]
    have hw_33 : wordSize c_w33 ((n + 1) ^ 2 + G.numEdges) ≤ w := by
      refine le_trans (wordSize_mono_left (c₂ := c_w) (by unfold c_w alg72WordConst; dsimp only; omega) _) ?_
      exact le_trans (wordSize_mono_right c_w (by omega)) hw
    have hmult_w : ∀ pair ∈ G.activePairsList, G.edgeMult pair.1 pair.2 < 2 ^ w := by
      intro pair _
      have hle : G.edgeMult pair.1 pair.2 ≤ G.numEdges := edgeMult_le_numEdges G pair.1 pair.2
      have h1_le_c : 1 ≤ c_w := hcw_pos
      have h_e_lt : G.numEdges < c_w * ((n + 1) ^ 2 + (G.numEdges + n + 1)) := by nlinarith
      omega
    have ha_in_s2 : s₂.arrs a_in = G.enc := by simpa [s₂] using ha_in_s1
    have h3k_w : 3 * k < 2 ^ w := lt_of_le_of_lt (Nat.mul_le_mul_left 3 hkle) h3ω_w
    rcases h33_exec n G w hw_33 h3k_w hmult_w s₂ ha_in_s2 with
      ⟨s₃, t₂, G', bdCode, hex_33, ht₂, hG'_le, hG'_bd, hG'_or_raw, _, ha_bd, _, hreg₃, harr₃⟩
    have hEq : G' = G := by
      rcases hG'_or_raw with heq | ⟨_, hhigh⟩
      · exact heq
      · exact False.elim ((not_width_original_of_high71 hk hG'_le hhigh) (hwidth G hnoG))
    rw [hEq] at hG'_bd
    rcases hG'_bd.length_and_words_le with ⟨hbd_len, hbd_words⟩
    have hbd_len_w : bdCode.length + 1 < 2 ^ w := by omega
    have hbd_code_w : ∀ x ∈ bdCode, x < 2 ^ w := by
      intro x hx
      have := hbd_words x hx
      omega
    rcases prependZeroProg_exec (a_scratch + 8) a_out r_base (by omega) hw1
        bdCode hbd_len_w hbd_code_w ha_bd with
      ⟨s₄, t_prep, hex_prep, ht_prep, hout_s4, harr_prep, hreg_prep⟩
    have hex_ite :
        Exec w (.ite (.op .eq (.reg r_base) (.const 1))
          (modelToWallProg h hh a_in a_out a_scratch r_base)
          (.seq P33_G (prependZeroProg (a_scratch + 8) a_out r_base))) s₂ s₄
          (3 + (t₂ + t_prep)) :=
      .ite_false hcond (.seq hex_33 hex_prep)
    have hout_72 : IsAlg72Output h k ⟨n, G⟩ (s₄.arrs a_out) := by
      rw [hout_s4]
      exact Or.inl ⟨bdCode, rfl, hG'_bd⟩
    refine ⟨s₄, t₁ + (3 + (3 + (t₂ + t_prep))), .seq hex₁ (.seq hex_rd hex_ite),
      alg72_time_bound_false ht₁ ht₂ (by omega), hout_72, ?_, ?_⟩
    · intro r hr
      have hr_ne : (r : Reg) ≠ r_base := by omega
      rw [hreg_prep r hr, hreg₃ r hr]
      simp [s₂, hr_ne, hreg₁ r hr]
    · intro a ha ha_out
      have ha_lt_base : a < a_base := by omega
      rw [harr_prep a ha_out, harr₃ a ha_lt_base (by omega) (by omega)]
      simpa [s₂] using harr₁ a ha ha_out


end GraphMinor.Compute
