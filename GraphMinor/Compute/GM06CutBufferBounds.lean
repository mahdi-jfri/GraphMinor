module

public import GraphMinor.Compute.GM06CutRotationProgram
public import GraphMinor.Compute.WhileRounds
import GraphMinor.Compute.Graph
import GraphMinor.Compute.GM06FaceBuffers

/-!
# Bounds on the computed cut-rotation buffer

The origin pass of Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) reads the cut-rotation buffer including its unused zero
padding. The initialized row program fixes this buffer's size, and no later
command reallocates it. Word-RAM expression evaluation bounds every
written entry. These lemmas recover those physical buffer facts from
any actual execution, alongside the existing exact prefix theorem.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Arrays allocated by a finite command tree. Writes do not reallocate. -/
def gm06AllocTargets : Cmd → List ℕ
  | .skip | .assign _ _ | .write _ _ _ => []
  | .alloc a _ => [a]
  | .seq a b | .ite _ a b => gm06AllocTargets a ++ gm06AllocTargets b
  | .while _ body => gm06AllocTargets body

/-- Array length is preserved when a command never reallocates that array. -/
theorem gm06Exec_length_eq {w : ℕ} {c : Cmd} {s sf : State} {t : ℕ}
    (he : Exec w c s sf t) (a : ℕ) (hnot : a ∉ gm06AllocTargets c) :
    (sf.arrs a).length = (s.arrs a).length := by
  induction he with
  | skip => rfl
  | assign => rfl
  | write => exact State.writeArr_arrs_length _ _ _ _ _
  | @alloc a' len s m hm =>
    have hne : a ≠ a' := by simpa only [gm06AllocTargets, List.mem_singleton] using hnot
    rw [State.setArr_arrs_ne _ _ hne]
  | seq h₁ h₂ ih₁ ih₂ =>
    simp only [gm06AllocTargets, List.mem_append, not_or] at hnot
    exact (ih₂ hnot.2).trans (ih₁ hnot.1)
  | ite_true _ _ _ ih =>
    simp only [gm06AllocTargets, List.mem_append, not_or] at hnot
    exact ih hnot.1
  | ite_false _ _ ih =>
    simp only [gm06AllocTargets, List.mem_append, not_or] at hnot
    exact ih hnot.2
  | while_false => rfl
  | while_true _ _ _ _ ih₁ ih₂ => exact (ih₂ hnot).trans (ih₁ hnot)

/-- Every execution of the initialized copied-row program has the
fixed physical buffer length and only word-sized entries. -/
theorem gm06CutRowsProg_output_bounds {w : ℕ} (rows : List (List ℕ)) (s sf : State) (t : ℕ)
    (hw : 2 < 2 ^ w) (h600 : s.arrs 600 = gm06EncodeRows rows)
    (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (he : Exec w gm06CutRowsProg s sf t) :
    (sf.arrs 625).length = 1 + 2 * (gm06EncodeRows rows).length ∧
      ∀ x ∈ sf.arrs 625, x < 2 ^ w := by
  change Exec w (.seq gm06CutInitRowsProg gm06CutSplitRowsLoop) s sf t at he
  cases he with
  | @seq _ _ _ sm _ _ _ hi hl =>
    obtain ⟨si, ti, hei, _, _, hbuf, _, _, _⟩ := gm06CutInitRowsProg_exec rows s hw hfit h600
    have hsame := (hei.deterministic hi).1
    subst si
    have hlen : (sm.arrs 625).length = 1 + 2 * (gm06EncodeRows rows).length := by
      rw [hbuf.1]
      simp only [List.length_append, List.length_singleton, List.length_replicate]
    have hwords : ∀ x ∈ sm.arrs 625, x < 2 ^ w := by
      intro x hx
      rw [hbuf.1] at hx
      rcases List.mem_append.mp hx with hx | hx
      · have heq : x = 2 * rows.length := by simpa using hx
        have hL := gm06FaceCode_length rows
        omega
      · have heq := (List.mem_replicate.mp hx).2
        simpa only [heq] using Nat.two_pow_pos w
    exact ⟨(gm06Exec_length_eq hl 625 (by decide)).trans hlen, hl.arrs_lt 625 hwords⟩

/-- The input-to-cut-rotation pipeline has the same fixed word buffer.
Its earlier mark and size passes preserve the original rotation source. -/
theorem gm06CutRotationProg_output_bounds {w : ℕ} (rows : List (List ℕ)) (s sf : State) (t : ℕ)
    (hw : 2 < 2 ^ w) (h600 : s.arrs 600 = gm06EncodeRows rows)
    (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (he : Exec w gm06CutRotationProg s sf t) :
    (sf.arrs 625).length = 1 + 2 * (gm06EncodeRows rows).length ∧
      ∀ x ∈ sf.arrs 625, x < 2 ^ w := by
  change Exec w (.seq gm06CutMarkProg (.seq _ gm06CutRowsProg)) s sf t at he
  cases he with
  | seq hm hr =>
    cases hr with
    | seq ha hp =>
      have hsource := hm.arrs_eq_of_not_mem_writtenArrs (a := 600) (by decide)
      cases ha
      apply gm06CutRowsProg_output_bounds rows _ sf _ hw _ hfit hp
      exact hsource.trans h600

end GraphMinor.Compute
