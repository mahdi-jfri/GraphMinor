module

public import GraphMinor.Compute.GM06PhaseRows
public import GraphMinor.Compute.GM06CutOutput
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading stored cut-component records

The cut program for VI (5.7), page 133, writes one complete rotation
record for each inner cuff gap. This pass reads those records using
their stored row counts and row lengths. It copies the selected
record into a separate array and preserves the source. The output
contains the same length prefixes required by the face program.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy a slice whose start and length are in registers 690 and 691. -/
def gm06PhaseCopySliceProg (src dst : ℕ) : Cmd :=
  gm13TabulateProg 650 (.reg 691) (.read src (.op .add (.reg 690) (.reg 650))) dst

/-- Exact slice copying, including a physical buffer's unused tail. -/
theorem gm06PhaseCopySliceProg_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (pre xs tail : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (ha : s.arrs src = pre ++ xs ++ tail) (hn : (s.arrs src).length < 2 ^ w)
    (hwords : ∀ a ∈ xs, a < 2 ^ w) (h690 : s.regs 690 = pre.length) (h691 : s.regs 691 = xs.length) :
    ∃ sf t, Exec w (gm06PhaseCopySliceProg src dst) s sf t ∧
      t ≤ 6 + 16 * xs.length ∧ Keeps [650] [dst] s sf ∧ sf.arrs dst = xs := by
  have hlen : pre.length + xs.length ≤ (s.arrs src).length := by rw [ha]; simp only [List.length_append]; omega
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec 650 (.reg 691)
    (.read src (.op .add (.reg 690) (.reg 650))) dst xs s hw (by omega)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 691 (by decide)).trans h691) (by omega))
    (fun st i hi hk hr => by
      have hsrc := (hk.2 src (by simpa using hne)).trans ha
      have hbound : pre.length + i < (st.arrs src).length := by rw [hk.2 src (by simpa using hne)]; omega
      have hget : (st.arrs src)[pre.length + i]'hbound = xs[i] := by
        simp only [hsrc, List.getElem_append_left (show pre.length + i < (pre ++ xs).length by simp; omega),
          List.getElem_append_right (show pre.length ≤ pre.length + i by omega), Nat.add_sub_cancel_left]
      simpa only [hget] using GraphMinor.Compute.Crossing.eval_read (a := src)
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg ((hk.1 690 (by decide)).trans h690) (by omega))
          (GraphMinor.Compute.Crossing.eval_reg hr (by omega)) (by omega)) hbound
        (by rw [hget]; exact hwords _ (List.getElem_mem hi)))
  exact ⟨sf, t, he, by simpa only [Expr.cost, Nat.mul_comm] using ht, hk, hd⟩

/-- Read one full rotation record at cursor 661. -/
def gm06PhaseReadRecordProg (src dst : ℕ) : Cmd :=
  .seq (.assign 690 (.reg 661))
    (.seq (.assign 665 (.read src (.reg 661)))
      (.seq (.assign 661 (.op .add (.reg 661) (.const 1)))
        (.seq (gm06PhaseSkipRowsProg src dst)
          (.seq (.assign 691 (.op .sub (.reg 661) (.reg 690))) (gm06PhaseCopySliceProg src dst)))))

/-- Registers changed when reading a complete component record. -/
def gm06PhaseReadRecordRegs : List ℕ := [650, 660, 661, 662, 664, 665, 690, 691]

/-- Read exactly the encoded rotation rows and advance to the next
component, deriving every address from the input record itself. -/
theorem gm06PhaseReadRecordProg_exec {w : ℕ} (src dst : ℕ)
    (hs : 600 ≤ src) (hs' : src < 660) (hd : 600 ≤ dst) (hd' : dst < 660) (hne : src ≠ dst)
    (pre tail : List ℕ) (rows : List (List ℕ)) (s : State) (hw : 1 < 2 ^ w)
    (ha : s.arrs src = pre ++ gm06EncodeRows rows ++ tail)
    (hn : (s.arrs src).length < 2 ^ w) (hwords : ∀ a ∈ s.arrs src, a < 2 ^ w)
    (h661 : s.regs 661 = pre.length) :
    ∃ sf t, Exec w (gm06PhaseReadRecordProg src dst) s sf t ∧
      t ≤ 30 + 40 * (gm06EncodeRows rows).length ∧
      Keeps gm06PhaseReadRecordRegs [dst] s sf ∧ sf.arrs dst = gm06EncodeRows rows ∧
      sf.regs 661 = pre.length + (gm06EncodeRows rows).length := by
  have hcode := gm06FaceCode_length rows
  have hlen : pre.length + (gm06EncodeRows rows).length + tail.length = (s.arrs src).length := by
    rw [ha]; simp only [List.length_append]
  have hrowCount : rows.length < 2 ^ w := by omega
  have hheadBound : pre.length < (s.arrs src).length := by omega
  have hhead : (s.arrs src)[pre.length]'hheadBound = rows.length := by
    have hh : (s.arrs src)[pre.length]? = some rows.length := by
      rw [ha]
      simp only [gm06EncodeRows, List.append_assoc, List.cons_append]
      rw [List.getElem?_append_right (le_refl _)]
      simp
    simpa only [List.getElem?_eq_getElem hheadBound, Option.some.injEq] using hh
  let s₀ := s.setReg 690 pre.length
  let s₁ := s₀.setReg 665 rows.length
  let s₂ := s₁.setReg 661 (pre.length + 1)
  have he₀ : Exec w (.assign 690 (.reg 661)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h661 (by omega))
  have he₁ : Exec w (.assign 665 (.read src (.reg 661))) s₀ s₁ 3 :=
    .assign (by
      have hh := GraphMinor.Compute.Crossing.eval_read (a := src)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) (s := s₀) (r := 661) (by simpa [s₀] using h661) (by omega))
        (show pre.length < (s₀.arrs src).length from hheadBound)
        (by simpa only [s₀, State.setReg_arrs, hhead] using hrowCount)
      simpa only [s₀, State.setReg_arrs, hhead] using hh)
  have he₂ : Exec w (.assign 661 (.op .add (.reg 661) (.const 1))) s₁ s₂ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁, s₀] using h661) (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) (by omega))
  have hk₂ : Keeps gm06PhaseReadRecordRegs [dst] s s₂ :=
    (((Keeps.refl _ _ s).setReg (by simp [gm06PhaseReadRecordRegs]) _).setReg
      (by simp [gm06PhaseReadRecordRegs]) _).setReg (by simp [gm06PhaseReadRecordRegs]) _
  let pre' := pre ++ [rows.length]
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hp₃, _⟩ := gm06PhaseSkipRowsProg_exec src dst hs hs' hd hd' hne
    rows pre' tail s₂ hw hrowCount
    (by rw [hk₂.2 src (by simpa using hne), ha]; simp [pre', gm06EncodeRows, List.append_assoc])
    (by rw [hk₂.2 src (by simpa using hne)]; exact hn)
    (by rw [hk₂.2 src (by simpa using hne)]; exact hwords)
    (by simp [s₂, pre']) (by simp [s₂, s₁])
  have hpos : s₃.regs 661 = pre.length + (gm06EncodeRows rows).length := by
    simpa only [pre', List.length_append, List.length_singleton, gm06EncodeRows, List.length_cons, List.length_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.zero_add] using hp₃
  have hstart : s₃.regs 690 = pre.length := (hk₃.1 690 (by decide)).trans (by simp [s₂, s₁, s₀])
  let s₄ := s₃.setReg 691 (gm06EncodeRows rows).length
  have he₄ : Exec w (.assign 691 (.op .sub (.reg 661) (.reg 690))) s₃ s₄ 4 :=
    .assign (by
      have hh := GraphMinor.Compute.Crossing.eval_sub (w := w)
        (GraphMinor.Compute.Crossing.eval_reg hpos (by omega))
        (GraphMinor.Compute.Crossing.eval_reg hstart (by omega))
      simpa only [Nat.add_sub_cancel_left] using hh)
  have hk₄ : Keeps gm06PhaseReadRecordRegs [dst] s s₄ :=
    (hk₂.trans hk₃ (by simp [gm06PhaseReadRecordRegs]) (fun _ h => h)).setReg (by simp [gm06PhaseReadRecordRegs]) _
  have hsource : s₄.arrs src = s.arrs src := hk₄.2 src (by simpa using hne)
  have hcodeWords : ∀ a ∈ gm06EncodeRows rows, a < 2 ^ w := by
    intro a ha'
    apply hwords a
    rw [ha]
    exact List.mem_append_left _ (List.mem_append_right _ ha')
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06PhaseCopySliceProg_exec src dst hne pre (gm06EncodeRows rows) tail s₄ hw
    (hsource.trans ha) (by rw [hsource]; exact hn) hcodeWords
    (by simpa [s₄] using hstart) (by simp [s₄])
  refine ⟨sf, 2 + (3 + (4 + (t₃ + (4 + tf)))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef)))),
    ?_, hk₄.trans hkf (by simp [gm06PhaseReadRecordRegs]) (fun _ h => h), hdf, ?_⟩
  · omega
  · exact (hkf.1 661 (by decide)).trans (by simpa [s₄] using hpos)

end GraphMinor.Compute
