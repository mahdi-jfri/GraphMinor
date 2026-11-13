module

public import GraphMinor.Compute.GM02SchemeDispatchBound

/-!
# Dispatching a valid scheme from computed boundary data

Read the boundary size from the inverse-name array, then dispatch on
that size and the selected catalogue code. Matching lengths and the
code range are bounded by the fixed boundary limit, so neither size
metadata nor template fields are added to the input relation.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02 GraphMinor.Compute.Crossing TwoPaths

/-- Read boundary size 344 from the old-name array and expand selected code 346. -/
noncomputable def gm02ReadSchemeDispatchProg (N : ℕ) (orig a : Arr) : Cmd :=
  .seq (.assign 344 (.len orig)) (gm02SchemeDispatchProg N orig a)

/-- A selected valid catalogue code produces all six fields with a uniform linear bound. -/
theorem gm02ReadSchemeDispatchProg_exec {n w N : ℕ} (B : GM02BoundaryInput) (C : B.schemes)
    (f : Fin B.n → Fin n) (orig a : Arr) (hoa : orig < a) (s : State)
    (hB : B.n ≤ N) (hn : n < 2 ^ w) (hNW : N + 1 < 2 ^ w)
    (hCW : gm02BoundarySchemeCodeBound N + 1 < 2 ^ w)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) (hcount : s.regs 40 = n)
    (hcode : s.regs 346 = gm02BoundarySchemeCode B C) :
    ∃ s' t, Exec w (gm02ReadSchemeDispatchProg N orig a) s s' t ∧
      t ≤ 46 + 42 * N + n * (60 + 28 * N) +
        4 * (gm02BoundarySchemeCodeBound N + 1) + 4 * (N + 1) ∧
      s'.arrs (a + 1) = (gm02TemplatePairIndices C.left.pairs).map (fun i => (f i).val) ∧
      s'.arrs (a + 2) = bitSetList ((gm02TemplatePairIndices C.left.pairs).toFinset.image f) ∧
      s'.arrs (a + 3) = (gm02TemplatePairIndices C.right.pairs).map (fun i => (f i).val) ∧
      s'.arrs (a + 4) = bitSetList ((gm02TemplatePairIndices C.right.pairs).toFinset.image f) ∧
      s'.arrs (a + 5) = bitSetList (C.reservedLeft.toFinset.image f) ∧
      s'.arrs (a + 6) = bitSetList (C.reservedRight.toFinset.image f) ∧
      Keeps [343, 342, 340, 344] [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] s s' := by
  have hw : 1 < 2 ^ w := by omega
  have hb : B.n < 2 ^ w := by omega
  have hc := gm02BoundarySchemeData_card_le_bound hB
  let s₁ := s.setReg 344 B.n
  have he₁ : Exec w (.assign 344 (.len orig)) s s₁ 2 :=
    Exec.assign (by simp [Expr.eval, horig, checkWord_of_lt hb])
  obtain ⟨s', t, he, ht, hL, hLS, hR, hRS, hZ, hZ', hk⟩ :=
    gm02SchemeDispatchProg_exec (gm02BoundarySchemeData B C) f orig a N hB hoa s₁ hw hn hb
      ((gm02TemplatePairIndices_length_le C.left).trans_lt hb)
      ((gm02TemplatePairIndices_length_le C.right).trans_lt hb) hNW (by omega)
      (by simp [s₁]) (by simpa only [s₁, State.setReg_regs_ne (r := 344) (r' := 346) _ _ (by decide),
        gm02BoundarySchemeCode] using hcode)
      horig (by simpa only [s₁, State.setReg_regs_ne (r := 344) (r' := 40) _ _ (by decide)] using hcount)
  have ht' := ht.trans (gm02SchemeDispatchCost_le B C N n hB)
  have hk₁ : Keeps [343, 342, 340, 344]
      [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] s s₁ :=
    (Keeps.refl _ _ s).setReg (by decide) B.n
  have hk' := hk.mono (R' := [343, 342, 340, 344]) (by decide) (fun _ h => h)
  exact ⟨s', 2 + t, Exec.seq he₁ he, by omega, hL, hLS, hR, hRS, hZ, hZ',
    hk₁.trans hk' (fun _ h => h) (fun _ h => h)⟩

end GraphMinor.Compute
