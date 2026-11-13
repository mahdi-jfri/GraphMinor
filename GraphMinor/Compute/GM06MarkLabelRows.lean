module

public import GraphMinor.Compute.GM06MarkLabelRowsLoop
import GraphMinor.Compute.Algorithm91Parse
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing the directed-edge mask of the given linkage

The linkage supplied to VI (5.7), page 133, is a list of rows.
Allocate an empty mask and scan that list once, reading both row
counts and row lengths from the supplied encoding. The mask is
computed from the path labels and is not an additional input.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Allocate the label mask of size 40 and mark every row of the source field. -/
def gm06MarkLabelRowsProg (src dst : Arr) : Cmd :=
  .seq (.alloc dst (.reg 40))
    (.seq (.assign 280 (.const 0))
      (.seq (readStreamWordProg src 280 283) (gm06MarkLabelRowsLoopProg src dst)))

/-- The complete row scan computes the union of all supplied labels,
with linear time in the mask size and encoded row lengths. -/
theorem gm06MarkLabelRowsProg_exec {w N : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (rows : List (List (Fin N))) (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hcw : rows.length < 2 ^ w)
    (hlen : (gm06EncodeRows (rows.map (List.map Fin.val))).length < 2 ^ w)
    {s : State} (hsize : s.regs 40 = N)
    (hsrc : s.arrs src = gm06EncodeRows (rows.map (List.map Fin.val))) :
    ∃ s' t, Exec w (gm06MarkLabelRowsProg src dst) s s' t ∧
      t ≤ N + 12 + 22 * rows.length + 14 * rows.flatten.length ∧
      s'.arrs dst = bitSetList rows.flatten.toFinset ∧
      (∀ a : ℕ, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 280 → q ≠ 281 → q ≠ 282 → q ≠ 283 → s'.regs q = s.regs q) := by
  let s₁ := s.setArr dst (List.replicate N 0)
  have he₁ : Exec w (.alloc dst (.reg 40)) s s₁ (N + 1) :=
    by simpa only [Expr.cost, Nat.add_comm] using (Exec.alloc (a := dst) (eval_reg hsize hN))
  let s₂ := s₁.setReg 280 0
  have he₂ : Exec w (.assign 280 (.const 0)) s₁ s₂ 2 :=
    .assign (eval_const (Nat.two_pow_pos w))
  have hs₂ : AtStream src 0
      (rows.length :: (gm06EncodeRowsPayload (rows.map (List.map Fin.val)) ++ [])) s₂ := by
    refine ⟨[], rfl, ?_⟩
    simpa [s₂, s₁, State.setArr, hne, gm06EncodeRows] using hsrc
  obtain ⟨s₃, t₃, he₃, ht₃, hc₃, hp₃, hs₃, ha₃, hg₃⟩ :=
    readStreamWordProg_exec 280 283 (by decide) hw hw hcw hs₂ rfl
  have hb₃ : s₃.arrs dst = bitSetList (∅ : Finset (Fin N)) := by
    rw [ha₃ dst, Alg91.bitSetList_empty]
    simp [s₂, s₁]
  have hend : 1 + (gm06EncodeRowsPayload (rows.map (List.map Fin.val))).length < 2 ^ w := by
    simpa only [gm06EncodeRows, List.length_cons, Nat.add_comm] using hlen
  obtain ⟨s₄, t₄, he₄, ht₄, hb₄, _, _, _, ha₄, hg₄⟩ :=
    gm06MarkLabelRowsLoopProg_exec src dst hne rows [] ∅ hw hN hcw hend hs₃ hp₃ hc₃ hb₃
  refine ⟨s₄, (N + 1) + (2 + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    by omega, by simpa using hb₄, ?_, ?_⟩
  · intro a ha
    rw [ha₄ a ha, ha₃ a]
    exact State.setArr_arrs_ne _ _ ha
  · intro q h280 h281 h282 h283
    rw [hg₄ q h280 h281 h282 h283, hg₃ q h280 h283]
    exact State.setReg_regs_ne _ _ h280

end GraphMinor.Compute
