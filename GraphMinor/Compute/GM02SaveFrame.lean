module

public import GraphMinor.Compute.GM02SaveFrameHeader
public import GraphMinor.Compute.GM02SaveFrameArrays

/-!
# Saving one complete alternating-recursion frame

Remember the current stack cursor, append the eight-word header and
three parent arrays, and finish with the remembered starting offset.
The resulting buffer prefix is exactly the specified frame layout.
Only the stack buffer, cursor, starting-offset scratch register, and
array-copy scratch registers change.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Save a complete parent frame before a recursive child reuses its arrays. -/
def gm02SaveFrameProg (parent left right stack : Arr)
    (r_pos r_start r_len r_base r_mode r_code r_aggregate r_left r_catalogue : Reg) : Cmd :=
  .seq (.assign r_start (.reg r_pos))
    (.seq (gm02SaveFrameHeaderProg parent left right stack
        r_pos r_mode r_code r_aggregate r_left r_catalogue)
      (.seq (gm02SaveFrameArraysProg parent left right stack r_len r_pos r_base)
        (appendWordProg stack r_pos (.reg r_start))))

/-- A complete saved frame has its exact words, start pointer, and linear copying cost. -/
theorem gm02SaveFrameProg_exec {w cap : ℕ} (parent left right stack : Arr)
    (r_pos r_start r_len r_base r_mode r_code r_aggregate r_left r_catalogue : Reg)
    (hps : parent ≠ stack) (hls : left ≠ stack) (hrs : right ≠ stack)
    (hpl : r_pos < r_len) (hsl : r_start < r_len) (hlb : r_len < r_base)
    (hsp : r_start ≠ r_pos)
    (hmetaPos : ∀ r ∈ [r_mode, r_code, r_aggregate, r_left, r_catalogue], r ≠ r_pos)
    (hmetaStart : ∀ r ∈ [r_mode, r_code, r_aggregate, r_left, r_catalogue], r ≠ r_start)
    (P L R pref : List ℕ) (mode code aggregate leftAnswer catalogue : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : pref.length + 9 + P.length + L.length + R.length < 2 ^ w)
    (hP : s.arrs parent = P) (hL : s.arrs left = L) (hR : s.arrs right = R)
    (hpw : ∀ v ∈ P, v < 2 ^ w) (hlw : ∀ v ∈ L, v < 2 ^ w) (hrw : ∀ v ∈ R, v < 2 ^ w)
    (hm : s.regs r_mode = mode) (hc : s.regs r_code = code)
    (ha : s.regs r_aggregate = aggregate) (hl : s.regs r_left = leftAnswer)
    (ht : s.regs r_catalogue = catalogue)
    (hmw : mode < 2 ^ w) (hcw : code < 2 ^ w) (haw : aggregate < 2 ^ w)
    (hlaw : leftAnswer < 2 ^ w) (htw : catalogue < 2 ^ w)
    (hstack : IsPrefixBuffer stack pref (9 + P.length + L.length + R.length + cap) s)
    (hpos : s.regs r_pos = pref.length) :
    ∃ s' t, Exec w (gm02SaveFrameProg parent left right stack
        r_pos r_start r_len r_base r_mode r_code r_aggregate r_left r_catalogue) s s' t ∧
      t ≤ 17 * (P.length + L.length + R.length) + 87 ∧
      IsPrefixBuffer stack
        (pref ++ gm02SavedFrameWords P L R mode code aggregate leftAnswer catalogue pref.length) cap s' ∧
      s'.regs r_pos = pref.length + 9 + P.length + L.length + R.length ∧
      (∀ a, a ≠ stack → s'.arrs a = s.arrs a) ∧
      (∀ r < r_len, r ≠ r_pos → r ≠ r_start → s'.regs r = s.regs r) := by
  let H := gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue
  let s₁ := s.setReg r_start pref.length
  have he₁ : Exec w (.assign r_start (.reg r_pos)) s s₁ 2 :=
    Exec.assign (by simp [Expr.eval, hpos, checkWord_of_lt (by omega : pref.length < 2 ^ w)])
  have hmstart (r : Reg) (hr : r ≠ r_start) : s₁.regs r = s.regs r :=
    State.setReg_regs_ne _ _ hr
  obtain ⟨s₂, t₂, he₂, ht₂, hstack₂, hpos₂, hk₂⟩ :=
    gm02SaveFrameHeaderProg_exec (cap := P.length + L.length + R.length + 1 + cap)
      parent left right stack r_pos r_mode r_code r_aggregate r_left r_catalogue hps hls hrs
      (hmetaPos _ (by simp)).symm (hmetaPos _ (by simp)).symm (hmetaPos _ (by simp)).symm
      (hmetaPos _ (by simp)).symm (hmetaPos _ (by simp)).symm
      P L R pref mode code aggregate leftAnswer catalogue s₁ hw (by omega) hP hL hR
      (by omega) (by omega) (by omega)
      ((hmstart _ (hmetaStart _ (by simp))).trans hm)
      ((hmstart _ (hmetaStart _ (by simp))).trans hc)
      ((hmstart _ (hmetaStart _ (by simp))).trans ha)
      ((hmstart _ (hmetaStart _ (by simp))).trans hl)
      ((hmstart _ (hmetaStart _ (by simp))).trans ht) hmw hcw haw hlaw htw
      (by simpa [IsPrefixBuffer, s₁, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstack)
      ((hmstart _ hsp.symm).trans hpos)
  have hstart₂ : s₂.regs r_start = pref.length :=
    (hk₂.1 _ (by simpa only [List.mem_singleton] using hsp)).trans (by simp [s₁])
  obtain ⟨s₃, t₃, he₃, ht₃, hstack₃, hpos₃, ha₃, hr₃⟩ :=
    gm02SaveFrameArraysProg_exec (cap := 1 + cap) parent left right stack r_len r_pos r_base
      hps hls hrs hlb (hpl.trans hlb) (Nat.ne_of_gt hpl) P L R (pref ++ H) s₂ hw
      ((hk₂.2 _ (by simp [hps])).trans hP) ((hk₂.2 _ (by simp [hls])).trans hL)
      ((hk₂.2 _ (by simp [hrs])).trans hR) hpw hlw hrw
      (by simp only [List.length_append, H, gm02SavedFrameHeader_length]; omega)
      (by simpa only [Nat.add_assoc] using hstack₂)
      (by simpa only [List.length_append, H, gm02SavedFrameHeader_length] using hpos₂)
  have hstart₃ : s₃.regs r_start = pref.length := (hr₃ _ hsl hsp).trans hstart₂
  obtain ⟨s₄, t₄, he₄, ht₄, hstack₄, hpos₄, ha₄, hr₄⟩ :=
    appendWordProg_exec (cap := cap) (pfx := pref ++ H ++ P ++ L ++ R) (val := pref.length)
      (s := s₃) stack r_pos (.reg r_start) hw
      (by simp only [List.length_append, H, gm02SavedFrameHeader_length]; omega)
      (by simpa only [Nat.add_comm cap 1] using hstack₃)
      (by simpa only [List.length_append, H, gm02SavedFrameHeader_length] using hpos₃)
      (by simp [Expr.eval, hstart₃, checkWord_of_lt (by omega : pref.length < 2 ^ w)])
  refine ⟨s₄, 2 + (t₂ + (t₃ + t₄)), Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost_reg] at ht₄
    omega
  · simpa only [gm02SavedFrameWords, H, List.append_assoc] using hstack₄
  · simp only [List.length_append, List.length_singleton, H, gm02SavedFrameHeader_length] at hpos₄
    omega
  · intro a has
    exact (ha₄ a has).trans ((ha₃ a has).trans (hk₂.2 a (by simp [has])))
  · intro r hrl hrp hrs'
    exact (hr₄ r hrp).trans ((hr₃ r hrl hrp).trans
      ((hk₂.1 r (by simp [hrp])).trans (hmstart r hrs')))

end GraphMinor.Compute
