module

public import GraphMinor.Compute.GM06FindLabel

/-!
# Exact last-label search for directed path recovery

Sections 12--13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) retain
ordinary directed edges for the returned path. When several parallel
edges have the same ends, a deterministic label scan selects the last
one. This file gives the exact list function for the existing RAM
label-search program. The length sentinel means that no label matches.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- The result after scanning the first `count` entries of a label row. -/
def gm06LabelIndexPrefix (xs : List ℕ) (needle count : ℕ) : ℕ :=
  (List.range count).foldl (fun result i => if xs[i]?.getD 0 = needle then i else result) xs.length

/-- Last matching position, with row length when the label is absent. -/
def gm06LabelIndex (xs : List ℕ) (needle : ℕ) : ℕ :=
  gm06LabelIndexPrefix xs needle xs.length

/-- One scan position replaces the result exactly when it matches. -/
theorem gm06LabelIndexPrefix_succ (xs : List ℕ) (needle i : ℕ) :
    gm06LabelIndexPrefix xs needle (i + 1) =
      if xs[i]?.getD 0 = needle then i else gm06LabelIndexPrefix xs needle i := by
  simp only [gm06LabelIndexPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The scan result is either a genuine matching position or its length
sentinel, in which case all processed entries differ from the needle. -/
theorem gm06LabelIndexPrefix_spec (xs : List ℕ) (needle i : ℕ) (hi : i ≤ xs.length) :
    (gm06LabelIndexPrefix xs needle i = xs.length ∧
      ∀ q (hq : q < xs.length), q < i → xs[q] ≠ needle) ∨
    ∃ q, q < i ∧ q < xs.length ∧ gm06LabelIndexPrefix xs needle i = q ∧ xs[q]?.getD 0 = needle := by
  induction i with
  | zero => exact Or.inl ⟨rfl, by intro q _ hq; omega⟩
  | succ i ih =>
    have hi' : i < xs.length := by omega
    rw [gm06LabelIndexPrefix_succ]
    by_cases he : xs[i]?.getD 0 = needle
    · exact Or.inr ⟨i, by omega, hi', by simp only [he, ↓reduceIte], he⟩
    · simp only [he, ↓reduceIte]
      rcases ih (by omega) with hz | ⟨q, hqi, hq, hres, heq⟩
      · refine Or.inl ⟨hz.1, ?_⟩
        intro q hq hqi
        by_cases hqi' : q = i
        · subst q
          simpa only [List.getElem?_eq_getElem hi', Option.getD_some] using he
        · exact hz.2 q hq (by omega)
      · exact Or.inr ⟨q, by omega, hq, hres, heq⟩

/-- A present label is found at a valid matching position. -/
theorem gm06LabelIndex_of_mem (xs : List ℕ) (needle : ℕ) (h : needle ∈ xs) :
    gm06LabelIndex xs needle < xs.length ∧ xs[gm06LabelIndex xs needle]?.getD 0 = needle := by
  rcases gm06LabelIndexPrefix_spec xs needle xs.length le_rfl with hz | ⟨q, _, hq, hres, heq⟩
  · obtain ⟨q, hq, heq⟩ := List.mem_iff_getElem.mp h
    exact False.elim (hz.2 q hq hq heq)
  · change gm06LabelIndexPrefix xs needle xs.length < xs.length ∧
      xs[gm06LabelIndexPrefix xs needle xs.length]?.getD 0 = needle
    rw [hres]
    exact ⟨hq, heq⟩

/-- The length sentinel occurs exactly when no label matches. -/
theorem gm06LabelIndex_eq_length_iff (xs : List ℕ) (needle : ℕ) :
    gm06LabelIndex xs needle = xs.length ↔ needle ∉ xs := by
  constructor
  · intro he hmem
    have hi := (gm06LabelIndex_of_mem xs needle hmem).1
    omega
  · intro hnot
    rcases gm06LabelIndexPrefix_spec xs needle xs.length le_rfl with hz | ⟨q, _, hq, _, heq⟩
    · exact hz.1
    · have he : xs[q] = needle := by
        simpa only [List.getElem?_eq_getElem hq, Option.getD_some] using heq
      exact False.elim (hnot (he ▸ List.getElem_mem hq))

/-- The existing label-search RAM program computes the exact last
matching position, including repeated labels and absent needles. -/
theorem gm06FindLabelProg_exec_exact {w : ℕ} (a needle idx res : ℕ)
    (hir : idx ≠ res) (hni : needle ≠ idx) (hnr : needle ≠ res)
    (xs : List ℕ) (value : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hv : value < 2 ^ w)
    (ha : s.arrs a = xs) (hr : s.regs needle = value) :
    ∃ sf t, Exec w (gm06FindLabelProg a needle idx res) s sf t ∧ t ≤ 7 + 13 * xs.length ∧
      Keeps [idx, res] [] s sf ∧ sf.regs res = gm06LabelIndex xs value := by
  let Inv := fun i st => st.regs idx = i ∧ Keeps [idx, res] [] s st ∧
    st.regs res = gm06LabelIndexPrefix xs value i
  let s₁ := s.setReg res xs.length
  let s₂ := s₁.setReg idx 0
  have he₁ : Exec w (.assign res (.len a)) s s₁ 2 := .assign (eval_len ha hn)
  have he₂ : Exec w (.assign idx (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have hinit : Inv 0 s₂ := ⟨by simp [s₂],
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _,
    by simp only [s₂, s₁, State.setReg_regs_ne _ _ hir.symm, State.setReg_regs_self,
      gm06LabelIndexPrefix, List.range_zero, List.foldl_nil]⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := forUp_exec'
    (r_i := idx) (hi := .len a)
    (body := .ite (.op .eq (.read a (.reg idx)) (.reg needle)) (.assign res (.reg idx)) .skip)
    Inv xs.length 6 hw hn
    (fun _ _ st h => ⟨h.1, eval_len ((h.2.1.2 a (by simp)).trans ha) hn⟩)
    (fun i hi st h => by
      have ha' := (h.2.1.2 a (by simp)).trans ha
      have hv' := (h.2.1.1 needle (by simp [hni, hnr])).trans hr
      have hread := eval_read (a := a) (eval_reg h.1 (hi.trans hn))
        (by simpa only [ha'] using hi) (by simpa only [ha'] using hx _ (List.getElem_mem hi))
      have hcond := eval_eq hread (eval_reg hv' hv) hw
      have hp : xs[i]?.getD 0 = xs[i] := by simp only [List.getElem?_eq_getElem hi, Option.getD_some]
      by_cases heq : xs[i] = value
      · let st' := st.setReg res i
        refine ⟨st', 6, .ite_true (by simpa only [ha', heq, ↓reduceIte] using hcond) (by decide)
          (.assign (eval_reg h.1 (hi.trans hn))), le_rfl,
          ⟨by simp, (h.2.1.setReg (by simp) _).setReg (by simp) _, ?_⟩, ?_⟩
        · simp only [State.setReg_regs_ne _ _ hir.symm, st', State.setReg_regs_self,
            gm06LabelIndexPrefix_succ, hp, heq, ↓reduceIte]
        · simpa only [st', State.setReg_regs_ne _ _ hir] using h.1
      · refine ⟨st, 5, .ite_false (by simpa only [ha', heq, ↓reduceIte] using hcond) (.skip st),
          by decide, ⟨by simp, h.2.1.setReg (by simp) _, ?_⟩, h.1⟩
        simpa only [State.setReg_regs_ne _ _ hir.symm, gm06LabelIndexPrefix_succ, hp, heq, ↓reduceIte]
          using h.2.2) s₂ hinit
  refine ⟨sf, 2 + (2 + tf), .seq he₁ (.seq he₂ hef), ?_, hIf.2.1, hIf.2.2⟩
  simp only [Expr.cost] at htf
  omega

end GraphMinor.Compute
