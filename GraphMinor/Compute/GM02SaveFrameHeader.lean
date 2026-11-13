module

public import GraphMinor.Compute.GM02AppendSavedWords
public import GraphMinor.Compute.GM02SavedFrameWords

/-!
# Saving the eight-word recursive frame header

Read the three source-array lengths and five loop-state registers.
Append those eight values to the saved-frame buffer without changing
any source array or loop-state register. Only the stack cursor and
buffer change, and the header write has constant cost.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Header expressions read three array lengths and five control words. -/
def gm02SavedFrameHeaderExprs (parent left right : Arr)
    (r_mode r_code r_aggregate r_left r_catalogue : Reg) : List Expr :=
  [.len parent, .len left, .len right, .reg r_mode, .reg r_code,
    .reg r_aggregate, .reg r_left, .reg r_catalogue]

/-- Append the eight-word saved-frame header at the stack cursor. -/
def gm02SaveFrameHeaderProg (parent left right stack : Arr)
    (r_pos r_mode r_code r_aggregate r_left r_catalogue : Reg) : Cmd :=
  gm02AppendSavedWordsProg stack r_pos
    (gm02SavedFrameHeaderExprs parent left right r_mode r_code r_aggregate r_left r_catalogue)

/-- The saved header contains the exact source lengths and control values. -/
theorem gm02SaveFrameHeaderProg_exec {w cap : ℕ} (parent left right stack : Arr)
    (r_pos r_mode r_code r_aggregate r_left r_catalogue : Reg)
    (hps : parent ≠ stack) (hls : left ≠ stack) (hrs : right ≠ stack)
    (hpm : r_pos ≠ r_mode) (hpc : r_pos ≠ r_code) (hpa : r_pos ≠ r_aggregate)
    (hpl : r_pos ≠ r_left) (hpt : r_pos ≠ r_catalogue)
    (P L R pref : List ℕ) (mode code aggregate leftAnswer catalogue : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : pref.length + 8 < 2 ^ w)
    (hP : s.arrs parent = P) (hL : s.arrs left = L) (hR : s.arrs right = R)
    (hpw : P.length < 2 ^ w) (hlw : L.length < 2 ^ w) (hrw : R.length < 2 ^ w)
    (hm : s.regs r_mode = mode) (hc : s.regs r_code = code)
    (ha : s.regs r_aggregate = aggregate) (hl : s.regs r_left = leftAnswer)
    (ht : s.regs r_catalogue = catalogue)
    (hmw : mode < 2 ^ w) (hcw : code < 2 ^ w) (haw : aggregate < 2 ^ w)
    (hlaw : leftAnswer < 2 ^ w) (htw : catalogue < 2 ^ w)
    (hstack : IsPrefixBuffer stack pref (8 + cap) s) (hpos : s.regs r_pos = pref.length) :
    ∃ s' t, Exec w (gm02SaveFrameHeaderProg parent left right stack
        r_pos r_mode r_code r_aggregate r_left r_catalogue) s s' t ∧ t ≤ 57 ∧
      IsPrefixBuffer stack
        (pref ++ gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue) cap s' ∧
      s'.regs r_pos = pref.length + 8 ∧ Keeps [r_pos] [stack] s s' := by
  obtain ⟨s', t, he, htime, hout, hpos', hk⟩ := gm02AppendSavedWordsProg_exec stack r_pos
    (gm02SavedFrameHeaderExprs parent left right r_mode r_code r_aggregate r_left r_catalogue)
    (gm02SavedFrameHeader P L R mode code aggregate leftAnswer catalogue) pref s hw
    (by simpa only [gm02SavedFrameHeader_length] using hlen)
    (by simpa only [gm02SavedFrameHeader_length] using hstack) hpos
    (fun st hk => by
      have hp' := (hk.2 parent (by simp [hps])).trans hP
      have hl' := (hk.2 left (by simp [hls])).trans hL
      have hr' := (hk.2 right (by simp [hrs])).trans hR
      have hm' := (hk.1 r_mode (by simp [hpm.symm])).trans hm
      have hc' := (hk.1 r_code (by simp [hpc.symm])).trans hc
      have ha' := (hk.1 r_aggregate (by simp [hpa.symm])).trans ha
      have hla' := (hk.1 r_left (by simp [hpl.symm])).trans hl
      have ht' := (hk.1 r_catalogue (by simp [hpt.symm])).trans ht
      simp only [gm02SavedFrameHeaderExprs, gm02SavedFrameHeader,
        List.forall₂_cons]
      repeat' constructor
      all_goals simp [Expr.eval, hp', hl', hr', hm', hc', ha', hla', ht',
        checkWord_of_lt hpw, checkWord_of_lt hlw, checkWord_of_lt hrw,
        checkWord_of_lt hmw, checkWord_of_lt hcw, checkWord_of_lt haw,
        checkWord_of_lt hlaw, checkWord_of_lt htw])
  refine ⟨s', t, he, ?_, hout, ?_, hk⟩
  · simp only [gm02SavedFrameHeaderExprs, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Expr.cost, gm02SavedFrameHeader_length] at htime
    omega
  · simpa only [List.length_append, gm02SavedFrameHeader_length] using hpos'

end GraphMinor.Compute
