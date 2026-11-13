module

public import GraphMinor.Compute.GM02SchemeTemplate
public import GraphMinor.Compute.Algorithm101Defs

/-!
# Selecting a fixed scheme template by its bounded code

Dispatch first on the boundary size and then on the finite data code.
Every branch contains a fixed template, decoded when constructing the
program. At run time the branch only reads the size and code registers
and expands that template using the stored old-name array.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- The fixed template branch for one size and possible data code. -/
noncomputable def gm02SchemeCodeBranch (b code : ℕ) (orig a : Arr) : Cmd :=
  if h : code < Fintype.card (GM02BoundarySchemeData b) then
    gm02SchemeTemplateProg (gm02DecodeBoundarySchemeData b ⟨code, h⟩) orig a
  else .skip

/-- Select a fixed template by boundary size 344 and data code 346. -/
noncomputable def gm02SchemeDispatchProg (N : ℕ) (orig a : Arr) : Cmd :=
  branchValProg 344 (fun b => branchValProg 346
    (fun code => gm02SchemeCodeBranch b code orig a)
    (Fintype.card (GM02BoundarySchemeData b))) N

/-- Bounded dispatch emits exactly the six fields of the selected finite data. -/
theorem gm02SchemeDispatchProg_exec {n b w : ℕ} (D : GM02BoundarySchemeData b)
    (f : Fin b → Fin n) (orig a : Arr) (N : ℕ) (hNb : b ≤ N) (hoa : orig < a) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b < 2 ^ w)
    (hl : (gm02TemplatePairIndices D.1).length < 2 ^ w)
    (hr : (gm02TemplatePairIndices D.2.1).length < 2 ^ w)
    (hNW : N + 1 < 2 ^ w)
    (hCW : Fintype.card (GM02BoundarySchemeData b) + 1 < 2 ^ w)
    (hsize : s.regs 344 = b)
    (hcode : s.regs 346 = (Fintype.equivFin (GM02BoundarySchemeData b) D).val)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) (hcount : s.regs 40 = n) :
    ∃ s' t, Exec w (gm02SchemeDispatchProg N orig a) s s' t ∧
      t ≤ 44 + 21 * ((gm02TemplatePairIndices D.1).length +
        (gm02TemplatePairIndices D.2.1).length) +
        n * (60 + 7 * ((gm02TemplatePairIndices D.1).length +
          (gm02TemplatePairIndices D.2.1).length + D.2.2.1.card + D.2.2.2.card)) +
        4 * (Fintype.card (GM02BoundarySchemeData b) + 1) + 4 * (N + 1) ∧
      s'.arrs (a + 1) = (gm02TemplatePairIndices D.1).map (fun i => (f i).val) ∧
      s'.arrs (a + 2) = bitSetList ((gm02TemplatePairIndices D.1).toFinset.image f) ∧
      s'.arrs (a + 3) = (gm02TemplatePairIndices D.2.1).map (fun i => (f i).val) ∧
      s'.arrs (a + 4) = bitSetList ((gm02TemplatePairIndices D.2.1).toFinset.image f) ∧
      s'.arrs (a + 5) = bitSetList (D.2.2.1.image f) ∧
      s'.arrs (a + 6) = bitSetList (D.2.2.2.image f) ∧
      Keeps [343, 342, 340] [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] s s' := by
  obtain ⟨s', t, he, ht, hL, hLS, hR, hRS, hZ, hZ', hk⟩ :=
    gm02SchemeTemplateProg_exec D f orig a hoa s hw hn hb hl hr horig hcount
  have hc : (Fintype.equivFin (GM02BoundarySchemeData b) D).val <
      Fintype.card (GM02BoundarySchemeData b) :=
    (Fintype.equivFin (GM02BoundarySchemeData b) D).isLt
  have hbexec : Exec w (gm02SchemeCodeBranch b (s.regs 346) orig a) s s' t := by
    unfold gm02SchemeCodeBranch
    simp only [hcode, dite_eq_left hc]
    have hd : gm02DecodeBoundarySchemeData b
        ⟨(Fintype.equivFin (GM02BoundarySchemeData b) D).val, hc⟩ = D :=
      (Fintype.equivFin (GM02BoundarySchemeData b)).symm_apply_apply D
    rw [hd]
    exact he
  obtain ⟨t₁, he₁, ht₁⟩ := branchValProg_exec 346
    (fun code => gm02SchemeCodeBranch b code orig a)
    (Fintype.card (GM02BoundarySchemeData b)) (by omega) hCW hbexec
  have hbexec' : Exec w (branchValProg 346
      (fun code => gm02SchemeCodeBranch (s.regs 344) code orig a)
      (Fintype.card (GM02BoundarySchemeData (s.regs 344)))) s s' t₁ := by
    simpa only [hsize] using he₁
  obtain ⟨t₂, he₂, ht₂⟩ := branchValProg_exec 344
    (fun j => branchValProg 346 (fun code => gm02SchemeCodeBranch j code orig a)
      (Fintype.card (GM02BoundarySchemeData j))) N (by omega) hNW hbexec'
  exact ⟨s', t₂, he₂, by omega, hL, hLS, hR, hRS, hZ, hZ', hk⟩

end GraphMinor.Compute
