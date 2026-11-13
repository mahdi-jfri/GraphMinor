module

public import GraphMinor.Compute.GM02AppendSavedArray

/-!
# Saving the three recursive frame arrays

Append the retained parent encoding and its two vertex-side arrays to
the frame buffer. Each pass reads its source length and preserves the
other sources. The final prefix is their concatenation in frame order,
and the total cost is linear in their combined length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Save the parent input and both vertex-side arrays in frame order. -/
def gm02SaveFrameArraysProg (parent left right stack : Arr) (r_len r_pos r_base : Reg) : Cmd :=
  .seq (gm02AppendSavedArrayProg parent stack r_len r_pos r_base)
    (.seq (gm02AppendSavedArrayProg left stack r_len r_pos r_base)
      (gm02AppendSavedArrayProg right stack r_len r_pos r_base))

/-- The saved array payload is exactly the parent encoding followed by both sides. -/
theorem gm02SaveFrameArraysProg_exec {w cap : ℕ} (parent left right stack : Arr)
    (r_len r_pos r_base : Reg) (hps : parent ≠ stack) (hls : left ≠ stack) (hrs : right ≠ stack)
    (hlb : r_len < r_base) (hpb : r_pos < r_base) (hlp : r_len ≠ r_pos)
    (P L R pref : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hP : s.arrs parent = P) (hL : s.arrs left = L) (hR : s.arrs right = R)
    (hpw : ∀ v ∈ P, v < 2 ^ w) (hlw : ∀ v ∈ L, v < 2 ^ w) (hrw : ∀ v ∈ R, v < 2 ^ w)
    (hlen : pref.length + P.length + L.length + R.length < 2 ^ w)
    (hstack : IsPrefixBuffer stack pref (P.length + L.length + R.length + cap) s)
    (hpos : s.regs r_pos = pref.length) :
    ∃ s' t, Exec w (gm02SaveFrameArraysProg parent left right stack r_len r_pos r_base) s s' t ∧
      t ≤ 17 * (P.length + L.length + R.length) + 21 ∧
      IsPrefixBuffer stack (pref ++ P ++ L ++ R) cap s' ∧
      s'.regs r_pos = pref.length + P.length + L.length + R.length ∧
      (∀ a, a ≠ stack → s'.arrs a = s.arrs a) ∧
      (∀ r < r_len, r ≠ r_pos → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hstack₁, hpos₁, ha₁, hr₁⟩ :=
    gm02AppendSavedArrayProg_exec (cap := L.length + R.length + cap)
      parent stack r_len r_pos r_base hps hlb hpb hlp pref P s hw hpw (by omega) hP
      (by simpa only [Nat.add_assoc] using hstack) hpos
  obtain ⟨s₂, t₂, he₂, ht₂, hstack₂, hpos₂, ha₂, hr₂⟩ :=
    gm02AppendSavedArrayProg_exec (cap := R.length + cap)
      left stack r_len r_pos r_base hls hlb hpb hlp (pref ++ P) L s₁ hw hlw
      (by simp only [List.length_append]; omega) ((ha₁ left hls).trans hL)
      (by simpa only [Nat.add_assoc] using hstack₁) hpos₁
  obtain ⟨s₃, t₃, he₃, ht₃, hstack₃, hpos₃, ha₃, hr₃⟩ :=
    gm02AppendSavedArrayProg_exec right stack r_len r_pos r_base hrs hlb hpb hlp
      ((pref ++ P) ++ L) R s₂ hw hrw (by simp only [List.length_append]; omega)
      ((ha₂ right hrs).trans ((ha₁ right hrs).trans hR)) hstack₂ hpos₂
  refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq he₁ (Exec.seq he₂ he₃), by omega, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc] using hstack₃
  · simpa only [List.length_append] using hpos₃
  · intro a has
    exact (ha₃ a has).trans ((ha₂ a has).trans (ha₁ a has))
  · intro r hrl hrp
    exact (hr₃ r hrl hrp).trans ((hr₂ r hrl hrp).trans (hr₁ r hrl hrp))

end GraphMinor.Compute
