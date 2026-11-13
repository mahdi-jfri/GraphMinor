module

public import GraphMinor.Compute.GM06CutMaterializeLoop
public import GraphMinor.Compute.GM06CutComponentRowProgram
import GraphMinor.Compute.GM06FaceBuffers

/-!
# Initialized materialization of all cut-component rotations

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns the
induced component graphs after its cuff-indexed searches. This pass
allocates output space from the actual common rotation-buffer length
and cuff count. It reads the computed membership rows and returns
exactly the sequence of induced rotation records. The remaining
origin table is shared by these records and retains every edge label.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Allocate the component rotation buffer and initialize the mask reader. -/
def gm06CutMaterializeInitProg : Cmd :=
  .seq (.alloc 601 (.op .add (.const 1) (.op .mul (.len 609) (.len 625))))
    (.seq (.write 601 (.const 0) (.len 609))
      (.seq (.assign 655 (.const 1))
        (.seq (.assign 661 (.const 1)) (.assign 668 (.len 609)))))

/-- Exact materialization buffer initialization from runtime list lengths. -/
theorem gm06CutMaterializeInitProg_exec {w : ℕ} (inner : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hk : inner.length < 2 ^ w) (hcode : (s.arrs 625).length < 2 ^ w)
    (hfit : 3 + inner.length * (s.arrs 625).length < 2 ^ w) (h609 : s.arrs 609 = inner) :
    ∃ sf t, Exec w gm06CutMaterializeInitProg s sf t ∧ t = 15 + inner.length * (s.arrs 625).length ∧
      Keeps [655, 661, 668] [601] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 601 655 [inner.length] (inner.length * (s.arrs 625).length) sf ∧
      sf.regs 661 = 1 ∧ sf.regs 668 = inner.length := by
  let cap := inner.length * (s.arrs 625).length
  have hcap : cap < 2 ^ w := by dsimp only [cap]; omega
  let s₀ := s.setArr 601 (List.replicate (1 + cap) 0)
  let s₁ := s₀.writeArr 601 0 inner.length
  let s₂ := s₁.setReg 655 1
  let s₃ := s₂.setReg 661 1
  let sf := s₃.setReg 668 inner.length
  have he₀ : Exec w (.alloc 601 (.op .add (.const 1) (.op .mul (.len 609) (.len 625)))) s s₀ (5 + (1 + cap)) :=
    .alloc (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_const hw)
      (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_len h609 hk)
        (GraphMinor.Compute.Crossing.eval_len rfl hcode) hcap) (by omega))
  have he₁ : Exec w (.write 601 (.const 0) (.len 609)) s₀ s₁ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_len (by simpa [s₀] using h609) hk) (by simp [s₀])
  have he₂ : Exec w (.assign 655 (.const 1)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have he₃ : Exec w (.assign 661 (.const 1)) s₂ s₃ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have he₄ : Exec w (.assign 668 (.len 609)) s₃ sf 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_len (by simpa [s₃, s₂, s₁, s₀, State.writeArr] using h609) hk)
  refine ⟨sf, (5 + (1 + cap)) + (3 + (2 + (2 + 2))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))),
    by dsimp only [cap]; omega, ?_, ?_, by simp [sf, s₃], by simp [sf]⟩
  · exact (((((Keeps.refl _ _ s).setArr (by simp) _).writeArr (by simp) _ _).setReg (by simp) _).setReg
      (by simp) _).setReg (by simp) _
  · have hrep : List.replicate (1 + cap) 0 = 0 :: List.replicate cap 0 := by
      rw [Nat.add_comm, List.replicate_succ]
    simp [GraphMinor.Compute.Crossing.IsBuf, sf, s₃, s₂, s₁, s₀, State.writeArr, hrep, cap]

/-- Initialize output storage and materialize all component rotation records. -/
def gm06CutMaterializeProg : Cmd := .seq gm06CutMaterializeInitProg gm06CutMaterializeLoop

/-- Encoded output prefix containing the component count and every rotation record. -/
def gm06CutMaterializeResult (s : State) : List ℕ := (s.arrs 601).take (s.regs 655)

/-- Complete physical materialization from computed masks and common
cut graph lists, with polynomial storage and time. -/
theorem gm06CutMaterializeProg_exec {w n m : ℕ} (data : GM06CutData) (masks : List (List ℕ))
    (inner tail padding : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hlen : data.rotations.length = n) (horgLen : data.origins.length = 2 * m)
    (hvalues : ∀ v ∈ data.origins, v < n) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hmasksLen : masks.length = inner.length) (hmaskLen : ∀ mask ∈ masks, mask.length = n)
    (hmaskBits : ∀ mask ∈ masks, ∀ x ∈ mask, x = 0 ∨ x = 1)
    (h600 : s.arrs 600 = gm06EncodeRows masks ++ tail)
    (hcode600 : (s.arrs 600).length < 2 ^ w) (hwords600 : ∀ x ∈ s.arrs 600, x < 2 ^ w)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode625 : (s.arrs 625).length < 2 ^ w) (hwords625 : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) data.activeDarts)
    (h609 : s.arrs 609 = inner) (h620 : s.regs 620 = n)
    (hfit : 3 + inner.length * (s.arrs 625).length < 2 ^ w) :
    ∃ sf t, Exec w gm06CutMaterializeProg s sf t ∧
      t ≤ 16 + inner.length * ((s.arrs 625).length + 40 + 2200 * n + 2200 * data.rotations.flatten.length) ∧
      Keeps gm06CutMaterializeRegs [601, 611, 615, 616, 630] s sf ∧
      gm06CutMaterializeResult sf = inner.length :: gm06CutMaterializedPayload n data masks := by
  have hw1 : 1 < 2 ^ w := by omega
  have hk : inner.length < 2 ^ w := by
    have hl : (s.arrs 600).length = 1 + masks.length + masks.flatten.length + tail.length := by
      rw [h600]
      simp only [List.length_append, gm06FaceCode_length]
    omega
  have hspace : 1 + n + data.rotations.flatten.length ≤ (s.arrs 625).length := by
    rw [h625, List.length_append, gm06FaceCode_length, hlen]
    omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hb₁, hp₁, hc₁⟩ := gm06CutMaterializeInitProg_exec inner s hw1 hk hcode625 hfit h609
  have hsource : s₁.arrs 600 = [inner.length] ++ gm06EncodeRowsPayload masks ++ tail := by
    rw [hk₁.2 600 (by decide), h600]
    simp only [gm06EncodeRows, hmasksLen, List.singleton_append]
  obtain ⟨sf, tf, hef, htf, hkf, hbf, _, _⟩ := gm06CutMaterializeLoop_exec
    (cap := inner.length * (s.arrs 625).length) data masks [inner.length] tail padding [inner.length] s₁
    hw hn hm hlen horgLen hvalues hkeys hmaskLen hmaskBits
    (by rw [hmasksLen]; exact Nat.mul_le_mul_left inner.length hspace)
    (by simp only [List.length_singleton]; omega) (by simpa only [hmasksLen] using hk)
    hsource (by rw [hk₁.2 600 (by decide)]; exact hcode600)
    (by rw [hk₁.2 600 (by decide)]; exact hwords600)
    ((hk₁.2 625 (by decide)).trans h625) (by rw [hk₁.2 625 (by decide)]; exact hcode625)
    (by rw [hk₁.2 625 (by decide)]; exact hwords625)
    ((hk₁.2 626 (by decide)).trans h626) ((hk₁.2 627 (by decide)).trans h627)
    ((hk₁.1 620 (by decide)).trans h620) (by simpa using hp₁) (by simpa only [hmasksLen] using hc₁) hb₁
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_,
    (hk₁.mono (by simp [gm06CutMaterializeRegs, gm06CutComponentRotationsRegs]) (by simp)).trans hkf
      (fun _ h => h) (fun _ h => h), ?_⟩
  · rw [hmasksLen] at htf
    nlinarith only [ht₁, htf]
  · rw [gm06CutMaterializeResult, hbf.2, hbf.1, List.take_left]
    rfl

/-- The computed membership buffer has fixed physical length and word
entries, without any initial bound on that reused scratch array. -/
theorem gm06CutComponentRowsProg_output_bounds {w n : ℕ} (inner : List ℕ) (s sf : State) (t : ℕ)
    (hw : 1 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (hfit : 3 + inner.length * (n + 1) < 2 ^ w)
    (h609 : s.arrs 609 = inner) (h620 : s.regs 620 = n)
    (he : Exec w gm06CutComponentRowsProg s sf t) :
    (sf.arrs 600).length = 1 + inner.length * (n + 1) ∧ ∀ x ∈ sf.arrs 600, x < 2 ^ w := by
  cases he with
  | @seq _ _ _ sm _ _ _ hi hl =>
    obtain ⟨si, _, hei, _, _, hb, _, _⟩ := gm06CutComponentRowsInitProg_exec inner s hw hn hfit h609 h620
    have heq := (hei.deterministic hi).1
    subst si
    have hlen : (sm.arrs 600).length = 1 + inner.length * (n + 1) := by
      rw [hb.1]
      simp only [List.length_append, List.length_singleton, List.length_replicate]
    have hwords : ∀ x ∈ sm.arrs 600, x < 2 ^ w := by
      intro x hx
      rw [hb.1] at hx
      rcases List.mem_append.mp hx with hx | hx
      · have heq : x = inner.length := by simpa only [List.mem_singleton] using hx
        have hle : inner.length ≤ inner.length * (n + 1) := by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left inner.length (by omega : 1 ≤ n + 1)
        omega
      · have heq := (List.mem_replicate.mp hx).2
        simpa only [heq] using Nat.two_pow_pos w
    exact ⟨(gm06Exec_length_eq hl 600 (by decide)).trans hlen, hl.arrs_lt 600 hwords⟩

end GraphMinor.Compute
