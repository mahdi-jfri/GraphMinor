module

public import GraphMinor.Compute.GM06FaceRowReader
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reserved-memory row operations for the two successor phases

The finite phases of VI (5.7), page 133, copy current core fields
and select rows from saved component and linkage encodings. These
operations use only the reserved high registers. The selector scans
the actual stored row lengths, so no computed row address is supplied
as input. The copying theorem also handles a row prefix of a padded
physical buffer.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy exactly the first count words of a source array. -/
def gm06PhaseCopyPrefixProg (src dst : ℕ) (count : Expr) : Cmd :=
  gm13TabulateProg 650 count (.read src (.reg 650)) dst

/-- Exact copying from an occupied prefix, allowing unused capacity. -/
theorem gm06PhaseCopyPrefixProg_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (count : Expr) (xs padding : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : xs.length < 2 ^ w) (hwords : ∀ x ∈ xs, x < 2 ^ w)
    (ha : s.arrs src = xs ++ padding)
    (hcount : ∀ st, Keeps [650] [dst] s st → count.eval w st = some xs.length) :
    ∃ sf t, Exec w (gm06PhaseCopyPrefixProg src dst count) s sf t ∧
      t ≤ 4 + 2 * count.cost + xs.length * (count.cost + 13) ∧
      Keeps [650] [dst] s sf ∧ sf.arrs dst = xs := by
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec (w := w) 650 count
    (.read src (.reg 650)) dst xs s hw hlen hcount (by
      intro st i hi hk hr
      have hsrc : st.arrs src = xs ++ padding := (hk.2 src (by simpa using hne)).trans ha
      have hbound : i < (st.arrs src).length := by simp only [hsrc, List.length_append]; omega
      have hget : (st.arrs src)[i]'hbound = xs[i] := by
        simp only [hsrc, List.getElem_append_left hi]
      have he := GraphMinor.Compute.Crossing.eval_read (a := src)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega)) hbound
        (by rw [hget]; exact hwords _ (List.getElem_mem hi))
      simpa only [hget] using he)
  exact ⟨sf, t, he, by simpa only [Expr.cost] using ht, hk, hd⟩

/-- Copy a complete source array, preserving every other array and
all registers except the reserved copy cursor. -/
def gm06PhaseCopyProg (src dst : ℕ) : Cmd := gm06PhaseCopyPrefixProg src dst (.len src)

/-- Full-array copying is linear and needs no zeroed scratch state. -/
theorem gm06PhaseCopyProg_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst) (xs : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlen : xs.length < 2 ^ w) (hwords : ∀ x ∈ xs, x < 2 ^ w)
    (ha : s.arrs src = xs) :
    ∃ sf t, Exec w (gm06PhaseCopyProg src dst) s sf t ∧ t ≤ 6 + 14 * xs.length ∧
      Keeps [650] [dst] s sf ∧ sf.arrs dst = xs := by
  simpa only [gm06PhaseCopyProg, Expr.cost, Nat.mul_comm] using gm06PhaseCopyPrefixProg_exec src dst hne (.len src) xs [] s hw hlen hwords
    (by simpa only [List.append_nil] using ha)
    (fun st hk => GraphMinor.Compute.Crossing.eval_len
      ((hk.2 src (by simpa using hne)).trans ha) hlen)

/-- Read one length-prefixed row using only high registers. -/
def gm06PhaseReadRowProg (src dst : ℕ) : Cmd :=
  renameCmd gm06RotationReadRename (gm06ReadRowProg src dst)

/-- Exact row reading from any two distinct reserved arrays below 660. -/
theorem gm06PhaseReadRowProg_exec {w : ℕ} (src dst : ℕ)
    (hs : 600 ≤ src) (hs' : src < 660) (hd : 600 ≤ dst) (hd' : dst < 660) (hne : src ≠ dst)
    (pre row tail : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (ha : s.arrs src = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs src).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs src, x < 2 ^ w)
    (hr : s.regs 661 = pre.length) :
    ∃ sf t, Exec w (gm06PhaseReadRowProg src dst) s sf t ∧
      t ≤ 13 + 22 * row.length ∧ Keeps [660, 661, 662, 664] [dst] s sf ∧
      sf.arrs dst = row ∧ sf.regs 661 = pre.length + 1 + row.length := by
  have hsrc : gm06RotationReadRename src = src := by
    unfold gm06RotationReadRename
    split_ifs <;> omega
  have hdst : gm06RotationReadRename dst = dst := by
    unfold gm06RotationReadRename
    split_ifs <;> omega
  let sr := renameState gm06RotationReadRename s
  obtain ⟨sm, t, he, ht, hout, hp, hregs, harrs⟩ := gm06ReadRowProg_exec src dst hne pre row tail sr hw
    (by simpa only [sr, renameState, hsrc] using ha)
    (by simpa only [sr, renameState, hsrc] using hn)
    (by simpa only [sr, renameState, hsrc] using hwords) hr
  have hinv : renameState gm06RotationReadRename sr = s := by
    ext x <;> simp [sr, renameState, gm06RotationReadRename_involutive x]
  refine ⟨renameState gm06RotationReadRename sm, t, ?_, ht, ⟨?_, ?_⟩, ?_, hp⟩
  · rw [← hinv]
    exact exec_renameCmd gm06RotationReadRename_involutive he
  · intro r hr
    have hneq : gm06RotationReadRename r ≠ 7 ∧ gm06RotationReadRename r ≠ 8 ∧
        gm06RotationReadRename r ≠ 9 ∧ gm06RotationReadRename r ≠ 11 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      unfold gm06RotationReadRename
      split_ifs <;> omega
    change sm.regs (gm06RotationReadRename r) = s.regs r
    rw [hregs _ hneq.1 hneq.2.1 hneq.2.2.1 hneq.2.2.2]
    exact congrArg s.regs (gm06RotationReadRename_involutive r)
  · intro a ha
    have hneq : gm06RotationReadRename a ≠ dst := by
      intro heq
      have := congrArg gm06RotationReadRename heq
      rw [gm06RotationReadRename_involutive a, hdst] at this
      exact ha (by simpa only [List.mem_singleton] using this)
    change sm.arrs (gm06RotationReadRename a) = s.arrs a
    rw [harrs _ hneq]
    exact congrArg s.arrs (gm06RotationReadRename_involutive a)
  · simpa only [renameState, hdst] using hout

/-- Advance through as many rows as the remaining counter in 665. -/
def gm06PhaseSkipRowsProg (src dst : ℕ) : Cmd :=
  .while (.reg 665) (.seq (gm06PhaseReadRowProg src dst) (.assign 665 (.op .sub (.reg 665) (.const 1))))

/-- The row skipper computes its own next cursor from stored lengths. -/
theorem gm06PhaseSkipRowsProg_exec {w : ℕ} (src dst : ℕ)
    (hs : 600 ≤ src) (hs' : src < 660) (hd : 600 ≤ dst) (hd' : dst < 660) (hne : src ≠ dst)
    (rows : List (List ℕ)) (pre tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hc : rows.length < 2 ^ w)
    (ha : s.arrs src = pre ++ gm06EncodeRowsPayload rows ++ tail)
    (hn : (s.arrs src).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs src, x < 2 ^ w)
    (h661 : s.regs 661 = pre.length) (h665 : s.regs 665 = rows.length) :
    ∃ sf t, Exec w (gm06PhaseSkipRowsProg src dst) s sf t ∧
      t ≤ 1 + 18 * rows.length + 22 * rows.flatten.length ∧
      Keeps [660, 661, 662, 664, 665] [dst] s sf ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload rows).length ∧ sf.regs 665 = 0 := by
  induction rows generalizing pre s with
  | nil =>
    exact ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg h665 (Nat.two_pow_pos w)), by simp,
      Keeps.refl _ _ _, by simpa [gm06EncodeRowsPayload] using h661, h665⟩
  | cons row rows ih =>
    simp only [List.length_cons] at hc h665
    have hsource : s.arrs src = pre ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload rows ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using ha
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, _, hp₁⟩ := gm06PhaseReadRowProg_exec src dst hs hs' hd hd' hne
      pre row (gm06EncodeRowsPayload rows ++ tail) s hw hsource hn hwords h661
    have hcount : s₁.regs 665 = rows.length + 1 := (hk₁.1 665 (by decide)).trans h665
    let s₂ := s₁.setReg 665 rows.length
    have he₂ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₁ s₂ 4 :=
      .assign (by simpa using (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg hcount hc) (GraphMinor.Compute.Crossing.eval_const hw)))
    have hk₁₂ : Keeps [660, 661, 662, 664, 665] [dst] s s₂ :=
      (hk₁.mono (by simp) (fun _ h => h)).setReg (by simp) _
    let pre' := pre ++ gm06EncodeNatList row
    have hsrc : s₂.arrs src = pre' ++ gm06EncodeRowsPayload rows ++ tail := by
      rw [hk₁₂.2 src (by simpa using hne)]
      simpa only [pre', List.append_assoc] using hsource
    obtain ⟨sf, tf, hef, htf, hkf, hpf, hcf⟩ := ih pre' s₂ (by omega) hsrc
      (by rw [hk₁₂.2 src (by simpa using hne)]; exact hn)
      (by rw [hk₁₂.2 src (by simpa using hne)]; exact hwords)
      (by simpa [s₂, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp₁)
      (by simp [s₂])
    refine ⟨sf, 1 + (t₁ + 4) + tf, .while_true (GraphMinor.Compute.Crossing.eval_reg h665 hc)
      (Nat.succ_ne_zero _) (.seq he₁ he₂) hef, ?_, hk₁₂.trans hkf (fun _ h => h) (fun _ h => h), ?_, hcf⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf

/-- Select the row whose zero-based index is in register 688. -/
def gm06PhaseSelectRowProg (src dst : ℕ) : Cmd :=
  .seq (.assign 661 (.const 1))
    (.seq (.assign 665 (.reg 688))
      (.seq (gm06PhaseSkipRowsProg src dst) (gm06PhaseReadRowProg src dst)))

/-- Row selection returns the exact indexed row in linear code time. -/
theorem gm06PhaseSelectRowProg_exec {w i : ℕ} (src dst : ℕ)
    (hs : 600 ≤ src) (hs' : src < 660) (hd : 600 ≤ dst) (hd' : dst < 660) (hne : src ≠ dst)
    (rows : List (List ℕ)) (s : State) (hw : 1 < 2 ^ w) (hi : i < rows.length)
    (ha : s.arrs src = gm06EncodeRows rows)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) (h688 : s.regs 688 = i) :
    ∃ sf t, Exec w (gm06PhaseSelectRowProg src dst) s sf t ∧
      t ≤ 40 + 50 * (gm06EncodeRows rows).length ∧
      Keeps [661, 665, 660, 662, 664] [dst] s sf ∧ sf.arrs dst = rows[i] := by
  have hlen := gm06FaceCode_length rows
  have hsplit := gm06EncodeRowsPayload_split rows i hi
  let s₀ := s.setReg 661 1
  let s₁ := s₀.setReg 665 i
  have he₀ : Exec w (.assign 661 (.const 1)) s s₀ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have he₁ : Exec w (.assign 665 (.reg 688)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₀] using h688) (by omega))
  have hk₁ : Keeps [661, 665, 660, 662, 664] [dst] s s₁ :=
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _
  let tail := gm06EncodeNatList rows[i] ++ gm06EncodeRowsPayload (rows.drop (i + 1))
  have hsource : s₁.arrs src = [rows.length] ++ gm06EncodeRowsPayload (rows.take i) ++ tail := by
    rw [hk₁.2 src (by simpa using hne), ha]
    simp only [gm06EncodeRows, hsplit, tail, List.append_assoc, List.cons_append, List.nil_append]
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hp₂, _⟩ := gm06PhaseSkipRowsProg_exec src dst hs hs' hd hd' hne
    (rows.take i) [rows.length] tail s₁ hw (by simp only [List.length_take]; omega) hsource
    (by simpa only [hk₁.2 src (by simpa using hne), ha] using hn)
    (by simpa only [hk₁.2 src (by simpa using hne), ha] using hwords)
    (by simp [s₁, s₀]) (by simp only [s₁, State.setReg_regs_self, List.length_take]; omega)
  let pre := [rows.length] ++ gm06EncodeRowsPayload (rows.take i)
  obtain ⟨sf, tf, hef, htf, hkf, hdf, _⟩ := gm06PhaseReadRowProg_exec src dst hs hs' hd hd' hne pre rows[i]
    (gm06EncodeRowsPayload (rows.drop (i + 1))) s₂ hw
    (by rw [hk₂.2 src (by simpa using hne), hsource]; simp only [pre, tail, List.append_assoc])
    (by rw [hk₂.2 src (by simpa using hne), hk₁.2 src (by simpa using hne), ha]; exact hn)
    (by rw [hk₂.2 src (by simpa using hne), hk₁.2 src (by simpa using hne), ha]; exact hwords)
    (by simpa only [pre, List.length_append, List.length_singleton] using hp₂)
  have htakeLen := (List.take_sublist i rows).flatten.length_le
  have hrowLen : rows[i].length ≤ rows.flatten.length := by
    have hs : [rows[i]].Sublist rows := List.singleton_sublist.mpr (List.getElem_mem hi)
    simpa using hs.flatten.length_le
  refine ⟨sf, 2 + (2 + (t₂ + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_,
    (hk₁.trans hk₂ (by simp) (fun _ h => h)).trans hkf (by simp) (fun _ h => h), hdf⟩
  simp only [List.length_take] at ht₂
  omega

end GraphMinor.Compute
