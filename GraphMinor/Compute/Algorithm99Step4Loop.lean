module

public import GraphMinor.Compute.Algorithm99Step4Iter

/-!
# Step (4) of Algorithm (9.9): the scan of the subwalls

Step (4) of Algorithm (9.9) (Graph Minors XIII, pages 104–105) chooses, among the subwalls
`H^1, …, H^s` given by (9.7), one whose compass passes the test `Alg99Step4Pass`. The program
runs the step `alg99Step4Iter` of `Algorithm99Step4Iter` once for each subwall, with the loop
index in register `R` (`alg99Step4Loop`). At the end either no subwall passed and the flag in
register `R + 4` is `0`, or some subwall `H^b` passed, the flag is `1`, and the code and the
compass of `H^b` are in `a_W` and array `33` (`alg99Step4Loop_exec`).
-/

@[expose] public section

namespace GraphMinor.Compute

open WallOfHeight

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

variable {n h h' s : ℕ}

/-- The scan of step (4): one step for each of the `s` subwalls, loop index in register `R`. -/
def alg99Step4Loop (h : ℕ) (h2 : 2 ≤ h) (a_W R s : ℕ) : Cmd :=
  forUp R (.const s) (alg99Step4Iter h h2 a_W R)

/-- What the scan knows after `i` steps: the flag is `0` and none of the first `i` subwalls
passed, or the flag is `1` and `a_W` and array `33` hold the code and the compass of one of the
first `i` subwalls that passed. -/
def Alg99Step4Found {Gi : MultiDigraph n} (Hi : WallOfHeight h' Gi) (X Z : Finset (Fin n))
    (W_flat : Fin s → WallOfHeight h Gi) (a_W R i : ℕ) (st : State) : Prop :=
  (st.regs (R + 4) = 0 ∧ ∀ b : Fin s, b.1 < i →
      ¬ Alg99Step4Pass Gi X Z ((W_flat b).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset) ∨
    (st.regs (R + 4) = 1 ∧ ∃ b : Fin s, b.1 < i ∧
      Alg99Step4Pass Gi X Z ((W_flat b).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset ∧
      st.arrs a_W = (W_flat b).encList ∧
      st.arrs 33 = bitSetList ((W_flat b).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset)

/-- **The scan of step (4) of (9.9)** (Graph Minors XIII, page 105). Started with the loop index
`0` in register `R`, the start of the code of `H^0` in register `R + 3` and the flag `0`, the
loop ends with `Alg99Step4Found` for all `s` subwalls. -/
theorem alg99Step4Loop_exec {w : ℕ} {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi}
    (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h') (h2 : 2 ≤ h)
    {X Z : Finset (Fin n)} {W_flat : Fin s → WallOfHeight h Gi}
    (hsub : ∀ a, (W_flat a).IsSubwallOf Hi)
    (hVX : ∀ a, Disjoint ((W_flat a).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset X)
    (a_W R : ℕ) (ha_W : 38 < a_W) (hR : 14 < R)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w) (hm3_w : 2 + 3 * Gi.numActivePairs < 2 ^ w)
    (hbig : 4 * (Gi.numEdges + n + 1) < 2 ^ w) (hs_w : s < 2 ^ w)
    (hh_w : h < 2 ^ w) (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    {st₀ : State} (hc : Alg99Step4Ctx Gi Hi X Z W_flat R st₀)
    (hcap_w : (st₀.arrs 22).length < 2 ^ w) (hout_w : (st₀.arrs outArr).length < 2 ^ w)
    (hR0 : st₀.regs R = 0) (hpos : st₀.regs (R + 3) = (alg97OutPrefix X W_flat 0).length)
    (hflag : st₀.regs (R + 4) = 0) :
    ∃ st' t, Exec w (alg99Step4Loop h h2 a_W R s) st₀ st' t ∧
      t ≤ 3 + s * (parseWallCost h n +
        alg99Step4CheckCost h' n (st₀.arrs 22).length Gi.numActivePairs + 17) ∧
      Alg99Step4Ctx Gi Hi X Z W_flat R st' ∧
      Alg99Step4Found Hi X Z W_flat a_W R s st' ∧
      (∀ x : ℕ, x ≠ 27 → x ≠ 28 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 →
        x ≠ 38 → x ≠ a_W → st'.arrs x = st₀.arrs x) ∧
      (∀ q : ℕ, (q < 3 ∨ 14 < q) → q < R → st'.regs q = st₀.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  let Inv (i : ℕ) (st : State) : Prop :=
    Alg99Step4Ctx Gi Hi X Z W_flat R st ∧ st.regs R = i ∧
      st.regs (R + 3) = (alg97OutPrefix X W_flat i).length ∧
      Alg99Step4Found Hi X Z W_flat a_W R i st ∧
      (∀ x : ℕ, x ≠ 27 → x ≠ 28 → x ≠ 29 → x ≠ 31 → x ≠ 32 → x ≠ 33 → x ≠ 36 → x ≠ 37 →
        x ≠ 38 → x ≠ a_W → st.arrs x = st₀.arrs x) ∧
      (∀ q : ℕ, (q < 3 ∨ 14 < q) → q < R → st.regs q = st₀.regs q)
  have hloop : ⦃Inv 0⦄[w] alg99Step4Loop h h2 a_W R s ⦃Inv s⦄ ≤
      fun _ => ((Expr.const s).cost + 2) + s * ((Expr.const s).cost + 6 +
        (parseWallCost h n + alg99Step4CheckCost h' n (st₀.arrs 22).length Gi.numActivePairs +
          10)) := by
    apply Triple.forUp_const Inv s _ hw1 hs_w
    · intro i _ st hI
      exact ⟨hI.2.1, by simp [Expr.eval, checkWord, hs_w]⟩
    · intro i hi st ⟨hc_i, hR_i, hpos_i, hfound_i, harr_i, hreg_i⟩
      have h22 : st.arrs 22 = st₀.arrs 22 :=
        harr_i 22 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
      have h1 : st.arrs outArr = st₀.arrs outArr :=
        harr_i 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
      have hflag_i : st.regs (R + 4) = 0 ∨ st.regs (R + 4) = 1 := by
        rcases hfound_i with ⟨h0, -⟩ | ⟨h1, -⟩
        · exact Or.inl h0
        · exact Or.inr h1
      obtain ⟨st', t, hex, ht, hc', hpos', hkeep, hnew, harr', hreg'⟩ :=
        alg99Step4Iter_exec hHi h2' he' h2 hsub ⟨i, hi⟩ (hVX _) a_W R ha_W hR hw3 hn1_w hm3_w hbig
          hh_w hc2_w hc_i (by rw [h22]; exact hcap_w) (by rw [h1]; exact hout_w) hpos_i hflag_i
      refine ⟨st', t, hex, by rw [h22] at ht; exact ht, ⟨?_, by simp, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact hc'.of_eq (fun _ _ => rfl) (fun q hq => by
          rw [State.setReg_regs_ne _ _ (show (q : Reg) ≠ R by romega)])
      · rw [State.setReg_regs_ne _ _ (show (R + 3 : Reg) ≠ R by romega)]; exact hpos'
      · have hf : (st'.setReg R (i + 1)).regs (R + 4) = st'.regs (R + 4) :=
          State.setReg_regs_ne _ _ (show (R + 4 : Reg) ≠ R by romega)
        change (_ ∧ _) ∨ (_ ∧ ∃ b : Fin s, b.1 < i + 1 ∧ _ ∧ st'.arrs a_W = _ ∧ st'.arrs 33 = _)
        rw [hf]
        rcases hfound_i with ⟨h0, hnone⟩ | ⟨h1', b, hb, hpass, hW, h33⟩
        · obtain ⟨hyes, hno⟩ := hnew h0
          by_cases hP : Alg99Step4Pass Gi X Z
              ((W_flat ⟨i, hi⟩).castGraph (wallUnionMultiDigraph Gi X Hi)).compassFinset
          · obtain ⟨hf1, hW, h33⟩ := hyes hP
            exact Or.inr ⟨hf1, ⟨i, hi⟩, by simp, hP, hW, h33⟩
          · refine Or.inl ⟨hno hP, fun b hb => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb' | hb'
            · exact hnone b hb'
            · have : b = ⟨i, hi⟩ := Fin.ext hb'
              rw [this]; exact hP
        · obtain ⟨hf1, hW', h33'⟩ := hkeep h1'
          exact Or.inr ⟨hf1, b, by omega, hpass, hW'.trans hW, h33'.trans h33⟩
      · intro x h27 h28 h29 h31 h32 h33 h36 h37 h38 hW
        rw [show (st'.setReg R (i + 1)).arrs x = st'.arrs x from rfl,
          harr' x h27 h28 h29 h31 h32 h33 h36 h37 h38 hW]
        exact harr_i x h27 h28 h29 h31 h32 h33 h36 h37 h38 hW
      · intro q hq hqR
        rw [State.setReg_regs_ne _ _ (show (q : Reg) ≠ R by romega), hreg' q hq (by omega)]
        exact hreg_i q hq hqR
      · rw [hreg' R (by omega) (by omega)]; exact hR_i
  have hInv₀ : Inv 0 st₀ :=
    ⟨hc, hR0, hpos, Or.inl ⟨hflag, fun b hb => absurd hb (Nat.not_lt_zero _)⟩,
      fun _ _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨st', t, hex, ht, hc', -, -, hfound, harr', hreg'⟩ := hloop st₀ hInv₀
  refine ⟨st', t, hex, ?_, hc', hfound, harr', hreg'⟩
  simp only [Expr.cost] at ht
  have : s * (1 + 6 + (parseWallCost h n +
      alg99Step4CheckCost h' n (st₀.arrs 22).length Gi.numActivePairs + 10)) =
      s * (parseWallCost h n + alg99Step4CheckCost h' n (st₀.arrs 22).length Gi.numActivePairs +
        17) := by ring_nf
  omega

end GraphMinor.Compute
