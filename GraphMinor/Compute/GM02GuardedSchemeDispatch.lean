module

public import GraphMinor.Compute.GM02ReadSchemeDispatch
public import GraphMinor.Compute.GM02CatalogueBit

/-!
# Guarding fixed scheme branches by the computed catalogue

Each fixed code is tested against the computed catalogue. An absent
code leaves the state unchanged. For a present code, set the dispatch
register and expand its six data arrays. The guard reads no feasibility
answer and the selected template is determined by the catalogue code.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02 GraphMinor.Compute.Crossing TwoPaths

/-- Skip absent codes and expand a present fixed code. -/
noncomputable def gm02GuardedSchemeDispatchProg (N : ℕ) (orig a : Arr) (i : ℕ) : Cmd :=
  .ite (gm02CatalogueBitExpr i)
    (.seq (.assign 346 (.const i)) (gm02ReadSchemeDispatchProg N orig a)) .skip

/-- An absent code executes only its catalogue guard and leaves every datum unchanged. -/
theorem gm02GuardedSchemeDispatchProg_absent {w N : ℕ} (B : GM02BoundaryInput)
    (orig a : Arr) (i : Fin (gm02BoundarySchemeCodeBound N)) (s : State)
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode N B)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w) (hw : 2 < 2 ^ w)
    (hi : ¬∃ C : B.schemes, gm02BoundarySchemeCode B C = i.val) :
    Exec w (gm02GuardedSchemeDispatchProg N orig a i.val) s s 6 := by
  exact Exec.ite_false (gm02CatalogueBitExpr_invalid B i s hcat hcodes hw hi) (Exec.skip s)

/-- A present scheme code expands its exact data arrays with uniformly bounded overhead. -/
theorem gm02GuardedSchemeDispatchProg_exec {n w N : ℕ} (B : GM02BoundaryInput) (C : B.schemes)
    (f : Fin B.n → Fin n) (orig a : Arr) (hoa : orig < a) (s : State)
    (hB : B.n ≤ N) (hn : n < 2 ^ w) (hNW : N + 1 < 2 ^ w)
    (hCW : gm02BoundarySchemeCodeBound N + 1 < 2 ^ w)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) (hcount : s.regs 40 = n)
    (hcat : s.regs 330 = gm02BoundarySchemeSetCode N B)
    (hcodes : 2 ^ gm02BoundarySchemeCodeBound N ≤ 2 ^ w) :
    ∃ s' t, Exec w (gm02GuardedSchemeDispatchProg N orig a (gm02BoundarySchemeCode B C)) s s' t ∧
      t ≤ 53 + 42 * N + n * (60 + 28 * N) +
        4 * (gm02BoundarySchemeCodeBound N + 1) + 4 * (N + 1) ∧
      s'.arrs (a + 1) = (gm02TemplatePairIndices C.left.pairs).map (fun i => (f i).val) ∧
      s'.arrs (a + 2) = bitSetList ((gm02TemplatePairIndices C.left.pairs).toFinset.image f) ∧
      s'.arrs (a + 3) = (gm02TemplatePairIndices C.right.pairs).map (fun i => (f i).val) ∧
      s'.arrs (a + 4) = bitSetList ((gm02TemplatePairIndices C.right.pairs).toFinset.image f) ∧
      s'.arrs (a + 5) = bitSetList (C.reservedLeft.toFinset.image f) ∧
      s'.arrs (a + 6) = bitSetList (C.reservedRight.toFinset.image f) ∧
      Keeps [343, 342, 340, 344, 346] [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] s s' := by
  have hw : 2 < 2 ^ w := by
    have hpos : 0 < gm02BoundarySchemeCodeBound N :=
      Nat.zero_lt_of_lt (gm02BoundarySchemeCode_lt_bound B hB C)
    have hpow : 2 ≤ 2 ^ gm02BoundarySchemeCodeBound N :=
      Nat.le_trans (by decide : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hpos)
    omega
  have hi := gm02BoundarySchemeCode_lt_bound B hB C
  have hiw : gm02BoundarySchemeCode B C < 2 ^ w := by omega
  let i : Fin (gm02BoundarySchemeCodeBound N) := ⟨gm02BoundarySchemeCode B C, hi⟩
  have hbit : (gm02CatalogueBitExpr i.val).eval w s = some 1 :=
    (gm02CatalogueBitExpr_valid B i s hcat hcodes hw).mpr ⟨C, rfl⟩
  let s₁ := s.setReg 346 i.val
  have he₁ : Exec w (.assign 346 (.const i.val)) s s₁ 2 :=
    Exec.assign (checkWord_of_lt hiw)
  obtain ⟨s', t, he₂, ht, hL, hLS, hR, hRS, hZ, hZ', hk⟩ :=
    gm02ReadSchemeDispatchProg_exec B C f orig a hoa s₁ hB hn hNW hCW horig
      (by simpa only [s₁, State.setReg_regs_ne (r := 346) (r' := 40) _ _ (by decide)] using hcount)
      (by simp [s₁, i])
  have he : Exec w (gm02GuardedSchemeDispatchProg N orig a i.val) s s' (5 + (2 + t)) :=
    Exec.ite_true (v := 1) hbit (by decide) (Exec.seq he₁ he₂)
  have hk₁ : Keeps [343, 342, 340, 344, 346]
      [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] s s₁ :=
    (Keeps.refl _ _ s).setReg (by decide) i.val
  have hk' := hk.mono (R' := [343, 342, 340, 344, 346]) (by decide) (fun _ h => h)
  exact ⟨s', 5 + (2 + t), he, by omega, hL, hLS, hR, hRS, hZ, hZ',
    hk₁.trans hk' (fun _ h => h) (fun _ h => h)⟩

end GraphMinor.Compute
