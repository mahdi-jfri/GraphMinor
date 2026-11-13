module

public import GraphMinor.Compute.GM06CandidateEdgeProgram

/-!
# Preparing ordinary flags and interpreting computed face incidence

Sections 10 and 12 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
build the candidate graph from the selected face and exclude every auxiliary
cuff edge. Ordinary copied edges occupy the first twice-original-edge
slots. This file computes those flags directly from the original edge
count and proves that a nonzero computed face-incidence entry refers
to both ends of a genuine edge in the paired rotation encoding.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Ordinary status of every permanent copied edge slot. -/
def gm06CandidateOrdinary (m original : ℕ) : List Bool :=
  (List.range m).map (fun e => decide (e < 2 * original))

/-- The ordinary table has one flag for every permanent edge. -/
theorem gm06CandidateOrdinary_length (m original : ℕ) :
    (gm06CandidateOrdinary m original).length = m := by
  simp only [gm06CandidateOrdinary, List.length_map, List.length_range]

/-- An in-range edge is ordinary exactly before the cuff-edge block. -/
theorem gm06CandidateOrdinary_get {m original e : ℕ} (he : e < m) :
    (gm06CandidateOrdinary m original)[e]?.getD false = decide (e < 2 * original) := by
  have hi : e < (gm06CandidateOrdinary m original).length := by
    simpa only [gm06CandidateOrdinary_length] using he
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.getD_some, gm06CandidateOrdinary, List.getElem_map, List.getElem_range]

/-- Each side copy of an original ordinary directed edge is ordinary. -/
theorem gm06CandidateOrdinary_cutDart {m original d tag : ℕ}
    (hm : 2 * original ≤ m) (hd : d < 2 * original) (htag : tag ≤ 1) :
    (gm06CandidateOrdinary m original)[gm06CutDart d tag / 2]?.getD false = true := by
  have hmod := Nat.mod_lt d (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div d 2
  have hb : gm06CutDart d tag / 2 < 2 * original := by unfold gm06CutDart; omega
  rw [gm06CandidateOrdinary_get (hb.trans_le hm), decide_eq_true_eq]
  exact hb

/-- Tabulate ordinary flags from original count 670 and copied count 649. -/
def gm06CandidateOrdinaryProg : Cmd :=
  gm13TabulateProg 650 (.reg 649) (exprLt (.reg 650) (.op .mul (.const 2) (.reg 670))) 624

/-- The RAM constructs the ordinary-edge table from counts, with no
supplied ordinary-status answer. Every cuff-edge slot receives zero. -/
theorem gm06CandidateOrdinaryProg_exec {w m original : ℕ} (s : State)
    (hw : 2 < 2 ^ w) (hm : m < 2 ^ w) (horiginal : 2 * original < 2 ^ w)
    (h649 : s.regs 649 = m) (h670 : s.regs 670 = original) :
    ∃ sf t, Exec w gm06CandidateOrdinaryProg s sf t ∧ t ≤ 6 + 17 * m ∧
      Keeps [650] [624] s sf ∧ sf.arrs 624 = (gm06CandidateOrdinary m original).map Bool.toNat := by
  let out := (gm06CandidateOrdinary m original).map Bool.toNat
  have hlen : out.length = m := by simp only [out, List.length_map, gm06CandidateOrdinary_length]
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec 650 (.reg 649)
    (exprLt (.reg 650) (.op .mul (.const 2) (.reg 670))) 624 out s (by omega) (hlen ▸ hm)
    (fun st hk => by
      rw [hlen]
      exact GraphMinor.Compute.Crossing.eval_reg ((hk.1 649 (by decide)).trans h649) hm)
    (fun st i hi hk hr => by
      have hi' : i < m := hlen ▸ hi
      have he := eval_exprLt (by omega : 1 < 2 ^ w)
        (GraphMinor.Compute.Crossing.eval_reg hr (hi'.trans hm))
        (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
          (GraphMinor.Compute.Crossing.eval_reg ((hk.1 670 (by decide)).trans h670) (by omega)) horiginal)
      have hget : out[i] = (if i < 2 * original then 1 else 0) := by
        simp only [out, gm06CandidateOrdinary, List.getElem_map, List.getElem_range]
        by_cases hh : i < 2 * original <;> simp only [hh, decide_true, decide_false] <;> rfl
      simpa only [hget] using he)
  exact ⟨sf, t, he, by simpa only [Expr.cost, exprLt, hlen, Nat.mul_comm] using ht, hk, hd⟩

/-- Nonzero incidence computed from a genuine face row identifies
both ends of an edge in the paired rotation encoding. This discharges
the candidate CSR input condition from the actual incidence definition. -/
theorem gm06IncE_complete_pair {m e : ℕ} (face : List ℕ) (rotations : List (List ℕ))
    (he : e < m) (hface : ∀ d ∈ face, d ∈ rotations.flatten)
    (hmate : ∀ d ∈ rotations.flatten, gm06DartMate d ∈ rotations.flatten)
    (hinc : (gm06IncE m face)[e]?.getD 0 ≠ 0) :
    2 * e ∈ rotations.flatten ∧ 2 * e + 1 ∈ rotations.flatten := by
  have hget : (gm06IncE m face)[e]?.getD 0 = (if e ∈ gm06FaceEdges face then 1 else 0) := by
    simp only [gm06IncE, gm06IncidenceBits, List.getElem?_ofFn, he, ↓reduceDIte, Option.getD_some]
  have hmem : e ∈ gm06FaceEdges face := by
    by_contra hh
    simp only [hget, hh, ↓reduceIte, ne_eq, not_true_eq_false] at hinc
  obtain ⟨d, hd, hde⟩ := List.mem_map.mp hmem
  have hdf := hface d hd
  have hdm := hmate d hdf
  change d / 2 = e at hde
  rw [← hde]
  rcases gm06DartMate_end_cases d with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact ⟨ht ▸ hdf, hh ▸ hdm⟩
  · exact ⟨hh ▸ hdm, ht ▸ hdf⟩

end GraphMinor.Compute
