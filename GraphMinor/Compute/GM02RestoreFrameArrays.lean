module

public import GraphMinor.Compute.GM02RestoreSavedArray

/-!
# Restoring the three parent arrays from a saved frame

Use the header's three lengths to restore the parent encoding and both
vertex-side arrays in sequence. The read cursor advances through the
payload, while the stack buffer and all control registers outside that
cursor and the copying scratch range remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Restore the saved parent input and both side arrays in payload order. -/
def gm02RestoreFrameArraysProg (stack parent left right : Arr)
    (r_read r_parentLen r_leftLen r_rightLen r_base : Reg) : Cmd :=
  .seq (gm02RestoreSavedArrayProg stack parent r_read r_parentLen r_base)
    (.seq (gm02RestoreSavedArrayProg stack left r_read r_leftLen r_base)
      (gm02RestoreSavedArrayProg stack right r_read r_rightLen r_base))

/-- The complete frame payload is restored exactly in linear total length. -/
theorem gm02RestoreFrameArraysProg_exec {w : ℕ} (stack parent left right : Arr)
    (r_read r_parentLen r_leftLen r_rightLen r_base : Reg)
    (hsp : stack ≠ parent) (hsl : stack ≠ left) (hsr : stack ≠ right)
    (hpl : parent ≠ left) (hpr : parent ≠ right) (hlr : left ≠ right)
    (hrb : r_read < r_base) (hpb : r_parentLen < r_base)
    (hlb : r_leftLen < r_base) (hrrb : r_rightLen < r_base)
    (hlr' : r_leftLen ≠ r_read) (hrr : r_rightLen ≠ r_read)
    (pref P L R rest : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hpw : ∀ v ∈ P, v < 2 ^ w) (hlw : ∀ v ∈ L, v < 2 ^ w) (hrw : ∀ v ∈ R, v < 2 ^ w)
    (hlen : pref.length + P.length + L.length + R.length < 2 ^ w)
    (hstack : s.arrs stack = pref ++ P ++ L ++ R ++ rest)
    (hpos : s.regs r_read = pref.length) (hP : s.regs r_parentLen = P.length)
    (hL : s.regs r_leftLen = L.length) (hR : s.regs r_rightLen = R.length) :
    ∃ s' t, Exec w (gm02RestoreFrameArraysProg stack parent left right
        r_read r_parentLen r_leftLen r_rightLen r_base) s s' t ∧
      t ≤ 16 * (P.length + L.length + R.length) + 39 ∧
      s'.arrs parent = P ∧ s'.arrs left = L ∧ s'.arrs right = R ∧
      s'.regs r_read = pref.length + P.length + L.length + R.length ∧
      (∀ a, a ≠ parent → a ≠ left → a ≠ right → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_read → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hp₁, hpos₁, ha₁, hr₁⟩ := gm02RestoreSavedArrayProg_exec
    stack parent r_read r_parentLen r_base hsp hrb hpb pref P (L ++ R ++ rest) s hw hpw
      (by omega) (by simpa only [List.append_assoc] using hstack) hpos hP
  have hstack₁ : s₁.arrs stack = (pref ++ P) ++ L ++ R ++ rest := by
    simpa only [List.append_assoc] using (ha₁ stack hsp).trans hstack
  have hL₁ := (hr₁ r_leftLen hlb hlr').trans hL
  have hR₁ := (hr₁ r_rightLen hrrb hrr).trans hR
  obtain ⟨s₂, t₂, he₂, ht₂, hl₂, hpos₂, ha₂, hr₂⟩ := gm02RestoreSavedArrayProg_exec
    stack left r_read r_leftLen r_base hsl hrb hlb (pref ++ P) L (R ++ rest) s₁ hw hlw
      (by simp only [List.length_append]; omega)
      (by simpa only [List.append_assoc] using hstack₁)
      (by simpa only [List.length_append] using hpos₁) hL₁
  have hstack₂ : s₂.arrs stack = ((pref ++ P) ++ L) ++ R ++ rest := by
    simpa only [List.append_assoc] using (ha₂ stack hsl).trans hstack₁
  obtain ⟨s₃, t₃, he₃, ht₃, hr₃, hpos₃, ha₃, hr₃'⟩ := gm02RestoreSavedArrayProg_exec
    stack right r_read r_rightLen r_base hsr hrb hrrb ((pref ++ P) ++ L) R rest s₂ hw hrw
      (by simp only [List.length_append]; omega) hstack₂
      (by simpa only [List.length_append] using hpos₂) ((hr₂ r_rightLen hrrb hrr).trans hR₁)
  refine ⟨s₃, t₁ + (t₂ + t₃), Exec.seq he₁ (Exec.seq he₂ he₃), by omega,
    (ha₃ parent hpr).trans ((ha₂ parent hpl).trans hp₁), (ha₃ left hlr).trans hl₂,
    hr₃, ?_, ?_, ?_⟩
  · simpa only [List.length_append] using hpos₃
  · intro a hap hal har
    exact (ha₃ a har).trans ((ha₂ a hal).trans (ha₁ a hap))
  · intro r hrb' hrr'
    exact (hr₃' r hrb' hrr').trans ((hr₂ r hrb' hrr').trans (hr₁ r hrb' hrr'))

end GraphMinor.Compute
