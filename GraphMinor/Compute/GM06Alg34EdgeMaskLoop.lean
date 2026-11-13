module

public import GraphMinor.Compute.GM06Alg34EdgeMaskStep

/-!
# Scanning the endpoint stream into the surviving-edge table

A counted loop applies the endpoint test to every supplied edge.
The proof follows the stream, records each exact table write, and
bounds the total work by a constant times the number of edges.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Endpoint words for a supplied list of old edge labels. -/
def gm06EdgeStream (x : GM06DrawingData) (L : List (Fin x.ends.length)) : List ℕ :=
  L.flatMap (fun e => [x.ends[e].1.val, x.ends[e].2.val])

/-- Exact successive survival-bit writes, starting at the supplied table position. -/
def gm06EdgeMaskWrites (x : GM06DrawingData) (vs : List (Fin x.n)) :
    List (Fin x.ends.length) → ℕ → List ℕ → List ℕ
  | [], _, dst => dst
  | e :: es, k, dst => gm06EdgeMaskWrites x vs es (k + 1)
      (dst.set k (if x.activeCell vs (.inr (.inl e)) then 1 else 0))

/-- Each endpoint pair occupies exactly two words. -/
theorem gm06EdgeStream_length (x : GM06DrawingData) (L : List (Fin x.ends.length)) :
    (gm06EdgeStream x L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons e L ih => simp only [gm06EdgeStream, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *; omega

/-- Count edges in register 134 and write consecutive table entries
starting at the position in register 135. -/
def gm06EdgeMaskLoopProg : Cmd :=
  .while (.reg 134) (.seq gm06EdgeMaskStepProg
    (.seq (.assign 135 (.op .add (.reg 135) (.const 1)))
      (.assign 134 (.op .sub (.reg 134) (.const 1)))))

/-- The edge scan performs exactly the supplied sequence of induced-edge
bit writes, in linear time. Scratch registers need no initial values
other than the displayed cursor, count, and table position. -/
theorem gm06EdgeMaskLoopProg_exec {w off k : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (L : List (Fin x.ends.length)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : off + 2 * L.length < 2 ^ w) (hk : k + L.length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (gm06EdgeStream x L ++ tail) s)
    (hpos : s.regs 103 = off) (hindex : s.regs 135 = k)
    (hcount : s.regs 134 = L.length) (hmask : s.arrs 4 = gm06VertexMask vs)
    (hcap : k + L.length ≤ (s.arrs 6).length) :
    ∃ s' t, Exec w gm06EdgeMaskLoopProg s s' t ∧ t ≤ 40 * L.length + 1 ∧
      s'.arrs 6 = gm06EdgeMaskWrites x vs L k (s.arrs 6) ∧
      s'.regs 103 = off + 2 * L.length ∧ s'.regs 135 = k + L.length ∧
      s'.regs 134 = 0 ∧ AtStream 0 (off + 2 * L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → q ≠ 134 → q ≠ 135 →
        s'.regs q = s.regs q) := by
  induction L generalizing off k s with
  | nil =>
    have hcond : (Expr.reg 134).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hcount, Nat.zero_lt_of_lt hw]
    exact ⟨s, 1, .while_false hcond, by simp, rfl, by simpa using hpos,
      by simpa using hindex, hcount, by simpa [gm06EdgeStream] using hstream,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | cons e L ih =>
    have hLw : L.length < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hL1w : L.length + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hkw : k < 2 ^ w := by omega
    have hk1w : k + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hstream₀ : AtStream 0 off
        (x.ends[e].1.val :: x.ends[e].2.val :: (gm06EdgeStream x L ++ tail)) s := by
      simpa only [gm06EdgeStream, List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc] using hstream
    obtain ⟨s₁, t₁, he₁, ht₁, hout₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      gm06EdgeMaskStepProg_exec x vs e (gm06EdgeStream x L ++ tail) hw hn
        (by simp only [List.length_cons] at hoff; omega) hkw hstream₀ hpos hindex hmask
        (by simp only [List.length_cons] at hcap; omega)
    have hi₁ : s₁.regs 135 = k :=
      (hr₁ 135 (by decide) (by decide) (by decide)).trans hindex
    have hc₁ : s₁.regs 134 = L.length + 1 := by
      simpa only [List.length_cons] using
        (hr₁ 134 (by decide) (by decide) (by decide)).trans hcount
    let s₂ := s₁.setReg 135 (k + 1)
    have he₂ : Exec w (.assign 135 (.op .add (.reg 135) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hkw, hw, hk1w])
    let s₃ := s₂.setReg 134 L.length
    have he₃ : Exec w (.assign 134 (.op .sub (.reg 134) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hL1w, hw, hLw])
    have hmask₃ : s₃.arrs 4 = gm06VertexMask vs := (ha₁ 4 (by decide)).trans hmask
    have hcap₃ : (k + 1) + L.length ≤ (s₃.arrs 6).length := by
      change k + 1 + L.length ≤ (s₁.arrs 6).length
      rw [hout₁, List.length_set]
      simp only [List.length_cons] at hcap
      omega
    have hp₃ : s₃.regs 103 = off + 2 := by simp [s₃, s₂, hp₁]
    have hi₃ : s₃.regs 135 = k + 1 := by simp [s₃, s₂]
    have hs₃ : AtStream 0 (off + 2) (gm06EdgeStream x L ++ tail) s₃ :=
      hs₁.of_arr_eq rfl
    obtain ⟨s₄, t₄, he₄, ht₄, hout₄, hp₄, hi₄, hc₄, hs₄, ha₄, hr₄⟩ :=
      ih (off := off + 2) (k := k + 1) (s := s₃)
        (by simp only [List.length_cons] at hoff; omega)
        (by simp only [List.length_cons] at hk; omega)
        hs₃ hp₃ hi₃ (by simp [s₃]) hmask₃ hcap₃
    have hcond : (Expr.reg 134).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hcount, hL1w]
    have he : Exec w gm06EdgeMaskLoopProg s s₄ ((1 + (t₁ + (4 + 4))) + t₄) :=
      .while_true hcond (by omega) (.seq he₁ (.seq he₂ he₃)) he₄
    refine ⟨s₄, _, he, by simp only [List.length_cons]; omega, ?_, ?_, ?_, hc₄, ?_, ?_, ?_⟩
    · rw [hout₄]
      change gm06EdgeMaskWrites x vs L (k + 1) (s₁.arrs 6) = _
      rw [hout₁]
      rfl
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega
    · convert hs₄ using 1 <;> simp only [List.length_cons] <;> omega
    · intro a ha
      exact (ha₄ a ha).trans (ha₁ a ha)
    · intro q hq hqA hqB hqc hqi
      rw [hr₄ q hq hqA hqB hqc hqi]
      change (s₂.setReg 134 L.length).regs q = _
      rw [State.setReg_regs_ne _ _ hqc, State.setReg_regs_ne _ _ hqi]
      exact hr₁ q hq hqA hqB

end GraphMinor.Compute
