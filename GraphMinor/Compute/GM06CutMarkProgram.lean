module

public import GraphMinor.Compute.GM06CutLinkageMarks
public import GraphMinor.Compute.GM06CutCuffMarks

/-!
# Constructing all cut-position tables on the RAM

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) begins by
locating the linkage ends and both signed cuff ends. This program
initializes four dense tables, scans every supplied linkage row,
and scans both cuffs at their original permanent edge-label bases.
The execution theorem identifies all four tables with the pure
function computed from those inputs. No position table is supplied.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Initialize the four cut-position arrays with zero sentinels. -/
def gm06CutZeroTablesProg : Cmd :=
  .seq (.alloc 620 (.reg 648))
    (.seq (.alloc 621 (.reg 648))
      (.seq (.alloc 623 (.reg 648)) (.alloc 624 (.reg 648))))

/-- The initialization allocates exactly four n-word zero arrays. -/
theorem gm06CutZeroTablesProg_exec {w n : ℕ} (s : State)
    (hn : n < 2 ^ w) (h648 : s.regs 648 = n) :
    ∃ sf, Exec w gm06CutZeroTablesProg s sf (4 + 4 * n) ∧
      Keeps [] [620, 621, 623, 624] s sf ∧
      sf.arrs 620 = List.replicate n 0 ∧ sf.arrs 621 = List.replicate n 0 ∧
      sf.arrs 623 = List.replicate n 0 ∧ sf.arrs 624 = List.replicate n 0 := by
  let s₁ := s.setArr 620 (List.replicate n 0)
  let s₂ := s₁.setArr 621 (List.replicate n 0)
  let s₃ := s₂.setArr 623 (List.replicate n 0)
  let s₄ := s₃.setArr 624 (List.replicate n 0)
  have he₁ : Exec w (.alloc 620 (.reg 648)) s s₁ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg h648 hn)
  have he₂ : Exec w (.alloc 621 (.reg 648)) s₁ s₂ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁] using h648) hn)
  have he₃ : Exec w (.alloc 623 (.reg 648)) s₂ s₃ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂, s₁] using h648) hn)
  have he₄ : Exec w (.alloc 624 (.reg 648)) s₃ s₄ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₃, s₂, s₁] using h648) hn)
  refine ⟨s₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he := Exec.seq he₁ (.seq he₂ (.seq he₃ he₄))
    have ht : (1 + n) + ((1 + n) + ((1 + n) + (1 + n))) = 4 + 4 * n := by omega
    rw [ht] at he
    exact he
  · exact ((((Keeps.refl _ _ s).setArr (by simp) _).setArr (by simp) _).setArr
      (by simp) _).setArr (by simp) _
  all_goals simp [s₄, s₃, s₂, s₁]

/-- Registers changed by construction of all four cut-position tables. -/
def gm06CutMarkRegs : List ℕ := gm06CutLinkageRegs ++ [653]

/-- Construct the path and both cuff marks. Inputs are origins 601,
encoded paths 608, inner order 609, outer order 610, n in 648 and
original ordinary edge count m in 649. The four outputs are
incoming 620, outgoing 621, positive cuff 623 and negative cuff 624. -/
def gm06CutMarkProg : Cmd :=
  .seq gm06CutZeroTablesProg
    (.seq (.assign 661 (.const 1))
      (.seq (.assign 665 (.read 608 (.const 0)))
        (.seq gm06CutLinkageMarksLoop
          (.seq (.assign 653 (.reg 649))
            (.seq (gm06CutCuffMarkProg 609)
              (.seq (.assign 653 (.op .add (.reg 649) (.len 609))) (gm06CutCuffMarkProg 610)))))))

/-- Exact construction of all Section-9 cut positions. The word
bounds cover the encoded linkage and both cuff label ranges. -/
theorem gm06CutMarkProg_exec {w n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w)
    (hsize : 2 * (m + inner.length + outer.length) + 1 < 2 ^ w)
    (horig : origins.length = 2 * m) (hv : ∀ v ∈ origins, v < n)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m)
    (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n)
    (hcode : (gm06EncodeRows paths).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (h601 : s.arrs 601 = origins) (h608 : s.arrs 608 = gm06EncodeRows paths)
    (h609 : s.arrs 609 = inner) (h610 : s.arrs 610 = outer)
    (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) :
    ∃ sf t, Exec w gm06CutMarkProg s sf t ∧
      t ≤ 26 + 4 * n + 23 * paths.length + 56 * paths.flatten.length +
        31 * (inner.length + outer.length) ∧
      Keeps gm06CutMarkRegs [611, 620, 621, 623, 624] s sf ∧
      sf.arrs 620 = (gm06BuildCutTables n m origins paths inner outer).incoming ∧
      sf.arrs 621 = (gm06BuildCutTables n m origins paths inner outer).outgoing ∧
      sf.arrs 623 = (gm06BuildCutTables n m origins paths inner outer).cuffPositive ∧
      sf.arrs 624 = (gm06BuildCutTables n m origins paths inner outer).cuffNegative := by
  have hw1 : 1 < 2 ^ w := by omega
  have hm : 2 * m < 2 ^ w := by omega
  obtain ⟨s₀, he₀, hk₀, hi₀, ho₀, hp₀, hn₀⟩ := gm06CutZeroTablesProg_exec s hn h648
  let s₁ := s₀.setReg 661 1
  let s₂ := s₁.setReg 665 paths.length
  have hsrc : s₁.arrs 608 = gm06EncodeRows paths := (hk₀.2 608 (by decide)).trans h608
  have hcw : paths.length < 2 ^ w := hwords _ (by simp [gm06EncodeRows])
  have he₁ : Exec w (.assign 661 (.const 1)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const hw1)
  have he₂ : Exec w (.assign 665 (.read 608 (.const 0))) s₁ s₂ 3 :=
    .assign (by
      have hi : 0 < (s₁.arrs 608).length := by simp [hsrc, gm06EncodeRows]
      have hget : (s₁.arrs 608)[0]'hi = paths.length := by simp [hsrc, gm06EncodeRows]
      have he := GraphMinor.Compute.Crossing.eval_read (a := 608)
        (GraphMinor.Compute.Crossing.eval_const (c := 0) (Nat.two_pow_pos w)) hi
        (by rw [hget]; exact hcw)
      simpa only [hget] using he)
  have hk₀₂ : Keeps gm06CutMarkRegs [611, 620, 621, 623, 624] s s₂ :=
    ((hk₀.mono (by simp) (by simp)).setReg (by simp [gm06CutMarkRegs, gm06CutLinkageRegs]) _).setReg
      (by simp [gm06CutMarkRegs, gm06CutLinkageRegs]) _
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hi₃, ho₃, _, _⟩ := gm06CutLinkageMarksLoop_exec
    paths [paths.length] [] origins (List.replicate n 0) (List.replicate n 0) s₂
    hw hn hm hcw
    (by simp [s₂, hsrc, gm06EncodeRows])
    (by simpa [s₂, hsrc] using hcode) (by simpa [s₂, hsrc] using hwords)
    horig hv hd (by simp) (by simp) (by simp [s₂, s₁]) (by simp [s₂])
    ((hk₀₂.2 601 (by decide)).trans h601) hi₀ ho₀
  have hk₀₃ : Keeps gm06CutMarkRegs [611, 620, 621, 623, 624] s s₃ :=
    hk₀₂.trans hk₃ (by simp [gm06CutMarkRegs, gm06CutLinkageRegs]) (by simp)
  let s₄ := s₃.setReg 653 m
  have he₄ : Exec w (.assign 653 (.reg 649)) s₃ s₄ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg ((hk₀₃.1 649 (by decide)).trans h649) (by omega))
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, hp₅, hn₅⟩ := gm06CutCuffMarkProg_exec
    (base := m) (src := 609) (by decide) (by decide) inner (List.replicate n 0) (List.replicate n 0) s₄
    hw hn (by omega) hci (by simp) (by simp)
    ((hk₀₃.2 609 (by decide)).trans h609) (by simp [s₄])
    (by rw [show s₄.arrs 623 = s₀.arrs 623 from hk₃.2 623 (by decide)]; exact hp₀)
    (by rw [show s₄.arrs 624 = s₀.arrs 624 from hk₃.2 624 (by decide)]; exact hn₀)
  have hk₀₅ : Keeps gm06CutMarkRegs [611, 620, 621, 623, 624] s s₅ :=
    (hk₀₃.setReg (by simp [gm06CutMarkRegs]) _).trans hk₅
      (by simp [gm06CutMarkRegs, gm06CutLinkageRegs]) (by simp)
  let s₆ := s₅.setReg 653 (m + inner.length)
  have he₆ : Exec w (.assign 653 (.op .add (.reg 649) (.len 609))) s₅ s₆ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg ((hk₀₅.1 649 (by decide)).trans h649) (by omega))
      (GraphMinor.Compute.Crossing.eval_len ((hk₀₅.2 609 (by decide)).trans h609) (by omega)) (by omega))
  obtain ⟨sf, tf, hef, htf, hkf, hpf, hnf⟩ := gm06CutCuffMarkProg_exec
    (base := m + inner.length) (src := 610) (by decide) (by decide) outer
    (gm06Scatter (gm06CutCuffPairs m inner true) (List.replicate n 0))
    (gm06Scatter (gm06CutCuffPairs m inner false) (List.replicate n 0)) s₆ hw hn hsize
    hco (by simp [gm06Scatter_length]) (by simp [gm06Scatter_length])
    ((hk₀₅.2 610 (by decide)).trans h610) (by simp [s₆]) hp₅ hn₅
  refine ⟨sf, (4 + 4 * n) + (2 + (3 + (t₃ + (2 + (t₅ + (4 + tf)))))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ hef)))))), ?_,
    (hk₀₅.setReg (by simp [gm06CutMarkRegs]) _).trans hkf
      (by simp [gm06CutMarkRegs, gm06CutLinkageRegs]) (by simp), ?_, ?_, ?_, ?_⟩
  · omega
  · exact (hkf.2 620 (by decide)).trans ((hk₅.2 620 (by decide)).trans hi₃)
  · exact (hkf.2 621 (by decide)).trans ((hk₅.2 621 (by decide)).trans ho₃)
  · simpa only [gm06BuildCutTables, gm06Scatter_append] using hpf
  · simpa only [gm06BuildCutTables, gm06Scatter_append] using hnf

end GraphMinor.Compute
