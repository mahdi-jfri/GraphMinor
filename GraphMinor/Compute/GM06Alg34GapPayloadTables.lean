module

public import GraphMinor.Compute.GM06Alg34PayloadBuild
public import GraphMinor.Compute.GM06Alg34GapDeletionFrames

/-!
# Old complement tables survive base-payload replacement

The base payload installer changes its output and serialization buffers,
but preserves the old vertex mask, cuff copy, complement CSR lists, and
root tables. Recover the preparation postconditions by determinism,
then carry them through the installer using its syntactic write sets.
The gap pass can therefore run after base-payload installation without
repeating either preparation or serialization.
-/

public section
namespace GraphMinor.Compute

private abbrev installProg : Cmd :=
  .seq gm06PayloadAllocProg (.seq gm06PayloadWriteProg gm06PayloadCopyProg)

private theorem install_arrays : installProg.writtenArrs ⊆ {0, 9, 10, 11, 33, 34} := by decide

set_option maxRecDepth 2048 in
private theorem install_registers :
    4 ∉ installProg.writtenRegs ∧ 100 ∉ installProg.writtenRegs ∧ 101 ∉ installProg.writtenRegs := by decide

private theorem install_array_frame {w t : ℕ} {s s' : State} (he : Exec w installProg s s' t)
    {A : ℕ} (hA : A ≠ 0 ∧ A ≠ 9 ∧ A ≠ 10 ∧ A ≠ 11 ∧ A ≠ 33 ∧ A ≠ 34) :
    s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  have hh := install_arrays hm
  simpa only [Finset.mem_insert, Finset.mem_singleton, hA.1, hA.2.1, hA.2.2.1,
    hA.2.2.2.1, hA.2.2.2.2.1, hA.2.2.2.2.2, or_self] using hh

private theorem install_register_frame {w t : ℕ} {s s' : State} (he : Exec w installProg s s' t)
    {q : ℕ} (hq : q = 4 ∨ q = 100 ∨ q = 101) : s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  rcases hq with rfl | rfl | rfl
  · exact install_registers.1
  · exact install_registers.2.1
  · exact install_registers.2.2

/-- Base-payload installation retains all old finite complement tables
needed to update the external gap incidence array. -/
theorem gm06GapPayloadBuild_tables (x : GM06DrawingData) (vs : List (Fin x.n))
    {c : ℕ} (hc : 2 ≤ c) {s s' : State} {t : ℕ}
    (hinput : s.arrs 0 = x.words) (hmask : s.arrs 4 = gm06VertexMask vs)
    (he : Exec (wordSize c x.size) gm06PayloadBuildProg s s' t) :
    s'.arrs 4 = gm06VertexMask vs ∧ s'.regs 4 = x.cellCount ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧
      s'.arrs 36 = gm06RootMask x vs ∧
      s'.arrs 37 = List.ofFn (fun a : Fin x.cellCount => ((gm06RootMask x vs).take a.val).sum) ∧
      IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s' ∧
      (s'.arrs 32).length = x.cellCount * x.cellCount := by
  have hc1 : 1 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hN : x.cellCount < 2 ^ wordSize c x.size := x.cellCount_le_size.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by have hh := x.five_le_words_length; have hle := x.words_length_le_size; omega
  obtain ⟨s₁, t₁, he₁, _, _, hv₁, _, _, _, _, _, hroot₁, hsize₁, _, hn₁, hm₁,
    _, _, _, _, _, hadj₁, hlen₁⟩ := gm06DeletionPrepareProg_exec x vs hc hinput hmask
  have hrank₁ := gm06GapDeletionPrepare_rootRanks x vs hw hN he₁ hroot₁
  cases he with
  | seq hprep htail =>
    obtain ⟨rfl, _⟩ := Exec.deterministic hprep he₁
    have ha (A : ℕ) (hA : A ≠ 0 ∧ A ≠ 9 ∧ A ≠ 10 ∧ A ≠ 11 ∧ A ≠ 33 ∧ A ≠ 34) :=
      install_array_frame htail hA
    refine ⟨(ha 4 (by decide)).trans hv₁,
      (install_register_frame htail (Or.inl rfl)).trans hsize₁,
      (install_register_frame htail (Or.inr (Or.inl rfl))).trans hn₁,
      (install_register_frame htail (Or.inr (Or.inr rfl))).trans hm₁,
      (ha 36 (by decide)).trans hroot₁, (ha 37 (by decide)).trans hrank₁,
      hadj₁.of_arrs_eq (ha 30 (by decide)) (ha 31 (by decide)) (ha 32 (by decide)), ?_⟩
    rw [ha 32 (by decide)]
    exact hlen₁

/-- Base-payload replacement preserves the original cuff copy and gap input array. -/
theorem gm06GapPayloadBuild_array_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06PayloadBuildProg s s' t) {A : ℕ} (hA : A = 2 ∨ 38 ≤ A) :
    s'.arrs A = s.arrs A := by
  cases he with
  | seq hprep htail =>
    have hA' : A ≠ 0 ∧ A ≠ 9 ∧ A ≠ 10 ∧ A ≠ 11 ∧ A ≠ 33 ∧ A ≠ 34 := by
      rcases hA with rfl | hA <;> omega
    exact (install_array_frame htail hA').trans (gm06GapDeletionPrepare_array_frame hprep hA)

end GraphMinor.Compute
