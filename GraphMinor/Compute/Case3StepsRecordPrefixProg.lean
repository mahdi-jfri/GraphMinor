module

public import GraphMinor.Compute.Algorithm94Aux

/-!
# Prefixing a record buffer by an existing list

A fixed number of record sections is joined from right to left. Each join
copies the new prefix to scratch, appends the current suffix, and prefixes
one header word. The old member arrays remain available throughout.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Place the chosen list before record suffix 51, using arrays 52 and 53. -/
def case3RecordPrefixProg (a_pre : ℕ) : Cmd :=
  .seq (copyArrLoopProg a_pre 52 125 126)
    (.seq (.assign 124 (.len 52))
      (.seq (.assign 125 (.len 51)) (appendArrProg 52 51 53 124 125 128)))

/-- The prefix and suffix are joined with linear copying work, while the
original suffix and every other member-data array remain in place. -/
theorem case3RecordPrefixProg_exec {w : ℕ} (a_pre : ℕ) (hne : a_pre ≠ 52)
    (pre suf : List ℕ) (hw : 1 < 2 ^ w) (hlen : pre.length + suf.length < 2 ^ w)
    (hprew : ∀ x ∈ pre, x < 2 ^ w) (hsufw : ∀ x ∈ suf, x < 2 ^ w)
    {s : State} (hpre : s.arrs a_pre = pre) (hsuf : s.arrs 51 = suf) :
    ∃ s' t, Exec w (case3RecordPrefixProg a_pre) s s' t ∧
      t ≤ 49 * pre.length + 18 * suf.length + 48 ∧
      s'.arrs 52 = pre ++ suf ∧ s'.regs 124 = pre.length + suf.length ∧
      (∀ a, a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 124, s'.regs r = s.regs r) := by
  have hpw : pre.length < 2 ^ w := by omega
  have hsw : suf.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hdst₁, harr₁, hreg₁⟩ := copyArrLoopProg_exec a_pre 52 125 126
    hne (by decide) hw s (by rw [hpre]; exact hpw) (by rw [hpre]; exact hprew)
  have hdst : s₁.arrs 52 = pre := hdst₁.trans hpre
  let s₂ := s₁.setReg 124 pre.length
  let s₃ := s₂.setReg 125 suf.length
  have hex₂ : Exec w (.assign 124 (.len 52)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hdst, hpw, ↓reduceIte])
  have hex₃ : Exec w (.assign 125 (.len 51)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, s₂, State.setReg_arrs,
      harr₁ 51 (by decide), hsuf, hsw, ↓reduceIte])
  obtain ⟨s₄, t₄, hex₄, ht₄, hacc₄, hlen₄, harr₄, hreg₄⟩ := appendArrProg_exec
    52 51 53 124 125 128 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    pre suf hprew hsufw hw hlen (s := s₃) hdst ((harr₁ 51 (by decide)).trans hsuf)
    (by rw [State.setReg_regs_ne _ _ (show (124 : ℕ) ≠ 125 by decide), State.setReg_regs_self])
    (State.setReg_regs_self ..)
  have hex : Exec w (case3RecordPrefixProg a_pre) s s₄ (t₁ + (2 + (2 + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, t₁ + (2 + (2 + t₄)), hex, ?_, hacc₄, hlen₄, ?_, ?_⟩
  · rw [hpre] at ht₁
    omega
  · intro a h52 h53
    exact (harr₄ a h52 h53).trans (harr₁ a h52)
  · intro r hr
    rw [hreg₄ r (Or.inl (by romega)) (by romega),
      State.setReg_regs_ne _ _ (by romega), State.setReg_regs_ne _ _ (by romega),
      hreg₁ r (by romega) (by romega)]

/-- Prefix a section and its header word to the current record suffix. -/
def case3RecordPrependProg (a_pre r_word : ℕ) : Cmd :=
  .seq (case3RecordPrefixProg a_pre) (prependWordProg (.reg r_word) 52 51 124 128)

/-- A header and its section are inserted with linear work and preserve
all arrays except the three record buffers and all registers below 124. -/
theorem case3RecordPrependProg_exec {w : ℕ} (a_pre r_word : ℕ) (hne : a_pre ≠ 52)
    (hrword : r_word < 124) (pre suf : List ℕ) (tag : ℕ)
    (hw : 1 < 2 ^ w) (hlen : 1 + (pre ++ suf).length < 2 ^ w)
    (hprew : ∀ x ∈ pre, x < 2 ^ w) (hsufw : ∀ x ∈ suf, x < 2 ^ w) (htag : tag < 2 ^ w)
    {s : State} (hpre : s.arrs a_pre = pre) (hsuf : s.arrs 51 = suf) (hrtag : s.regs r_word = tag) :
    ∃ s' t, Exec w (case3RecordPrependProg a_pre r_word) s s' t ∧
      t ≤ 67 * pre.length + 36 * suf.length + 66 ∧ s'.arrs 51 = tag :: (pre ++ suf) ∧
      (∀ a, a ≠ 51 → a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 124, s'.regs r = s.regs r) := by
  have hlen' : pre.length + suf.length < 2 ^ w := by simp only [List.length_append] at hlen; omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hdst₁, hrlen₁, harr₁, hreg₁⟩ :=
    case3RecordPrefixProg_exec a_pre hne pre suf hw hlen' hprew hsufw hpre hsuf
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩ := prependWordProg_exec (tag := tag) (w := w)
    (.reg r_word) 52 51 124 128 (by decide) (by decide) (pre ++ suf)
    (by intro x hx; rcases List.mem_append.mp hx with hx | hx; exact hprew x hx; exact hsufw x hx)
    hw hlen (s := s₁)
    (by intro v; simp only [Expr.eval, checkWord, State.setArr_regs,
      State.setReg_regs_ne _ _ (show r_word ≠ 128 by omega), hreg₁ r_word hrword, hrtag, htag, ↓reduceIte])
    hdst₁ (by simpa only [List.length_append] using hrlen₁)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hdst₂, ?_, ?_⟩
  · simp only [List.length_append, Expr.cost] at ht₂
    omega
  · intro a h51 h52 h53
    exact (harr₂ a h51).trans (harr₁ a h52 h53)
  · intro r hr
    rw [hreg₂ r (Or.inl (by romega)), hreg₁ r hr]

end GraphMinor.Compute
