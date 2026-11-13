module

public import GraphMinor.Compute.Basic

/-!
# Logarithmic word sizes after adding a fixed number of vertices

Adding one to the size argument increases its base-two logarithm by at
most one. Induction bounds a fixed additive shift, and increasing the
word-size coefficient absorbs that shift. The numeric split graph adds
only the fixed terminal-slot count to the supplied host size.
-/

public section
namespace GraphMinor.Compute

/-- A fixed additive size shift is absorbed by a fixed factor in the logarithmic word coefficient. -/
theorem gm02WordSize_add_le (c n a : ℕ) : wordSize c (n + a) ≤ wordSize (c * (a + 1)) n := by
  have hlog : ∀ a : ℕ, Nat.log 2 (n + a + 2) ≤ Nat.log 2 (n + 2) + a := by
    intro a
    induction a with
    | zero => simp only [Nat.add_zero]; exact le_rfl
    | succ a ih =>
      have hsize : n + (a + 1) + 2 ≤ (n + a + 2) * 2 := by omega
      have h := Nat.log_mono_right (b := 2) hsize
      rw [Nat.log_mul_base (by decide) (by omega : n + a + 2 ≠ 0)] at h
      omega
  have hfactor : Nat.log 2 (n + 2) + a + 1 ≤ (a + 1) * (Nat.log 2 (n + 2) + 1) := by
    have ha : a ≤ a * (Nat.log 2 (n + 2) + 1) := Nat.le_mul_of_pos_right _ (by omega)
    calc
      Nat.log 2 (n + 2) + a + 1 = a + (Nat.log 2 (n + 2) + 1) := by omega
      _ ≤ a * (Nat.log 2 (n + 2) + 1) + (Nat.log 2 (n + 2) + 1) := Nat.add_le_add_right ha _
      _ = (a + 1) * (Nat.log 2 (n + 2) + 1) := by rw [Nat.add_mul, Nat.one_mul]
  unfold wordSize
  calc
    c * (Nat.log 2 (n + a + 2) + 1) ≤ c * ((a + 1) * (Nat.log 2 (n + 2) + 1)) :=
      Nat.mul_le_mul_left c ((Nat.add_le_add_right (hlog a) 1).trans hfactor)
    _ = (c * (a + 1)) * (Nat.log 2 (n + 2) + 1) := (Nat.mul_assoc ..).symm

/-- The same coefficient transfer applies to every intermediate size below the fixed additive bound. -/
theorem gm02WordSize_le_of_le_add (c n a : ℕ) {m : ℕ} (hm : m ≤ n + a) :
    wordSize c m ≤ wordSize (c * (a + 1)) n :=
  (wordSize_mono_right c hm).trans (gm02WordSize_add_le c n a)

end GraphMinor.Compute
