module

public import GraphMinor.Compute.Case3StepsActivePairOwners
public import GraphMinor.Compute.Case3StepsPairOwnerProg
public import GraphMinor.Compute.Case3StepsBucketInsertProg

/-!
# Reading and inserting one positive multigraph pair

The program reads the pair endpoints, looks up their common owner, and
inserts the pair's encoding index into that owner's bucket. Its multiplicity
word stays in the input encoding and is copied only when encoding the member.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Read and route the pair whose index is in register 65. -/
def case3BucketPairProg : Cmd :=
  .seq (readTripleEndpoints 3 65 69 66 67)
    (.seq case3PairOwnerProg case3BucketInsertProg)

/-- One stored pair advances the three bucket tables in at most thirty-seven steps. -/
theorem case3BucketPairProg_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (j : Fin D.numActivePairs)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w)
    (hL : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hD : s.arrs 3 = D.enc) (hloop : s.arrs 33 = List.ofFn (case3OrderedLoopLabel x Z))
    (hmat : s.arrs 34 = case3EdgeMatrixPrefix x Z (case3InputEdges x).length)
    (hheads : s.arrs 35 = case3BucketHeads (case3ActivePairOwner x D Z)
      (x.n + (case3InputEdges x).length) (j.1 + 1))
    (hnext : s.arrs 36 = case3BucketNext (case3ActivePairOwner x D Z) (j.1 + 1))
    (hcounts : s.arrs 37 = case3BucketCounts (case3ActivePairOwner x D Z)
      (x.n + (case3InputEdges x).length) (j.1 + 1))
    (hrn : s.regs 14 = x.n) (hrj : s.regs 65 = j.1) :
    ∃ s' t, Exec w case3BucketPairProg s s' t ∧ t ≤ 37 ∧
      s'.arrs 35 = case3BucketHeads (case3ActivePairOwner x D Z)
        (x.n + (case3InputEdges x).length) j.1 ∧
      s'.arrs 36 = case3BucketNext (case3ActivePairOwner x D Z) j.1 ∧
      s'.arrs 37 = case3BucketCounts (case3ActivePairOwner x D Z)
        (x.n + (case3InputEdges x).length) j.1 ∧
      (∀ a, a ≠ 35 → a ≠ 36 → a ≠ 37 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 66 → r ≠ 67 → r ≠ 68 → r ≠ 69 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, _, hru, hrv, harr₁, hreg₁⟩ :=
    readTripleEndpoints_exec D [] 3 65 69 66 67 j.1 s (by decide) (by decide) (by decide)
      hw hn hA j.2 (by simpa only [List.append_nil] using hD) hrj
  obtain ⟨t₂, hex₂, ht₂⟩ := case3PairOwnerProg_exec x Z hdiv
    (D.activePairsList[j.1]).1 (D.activePairsList[j.1]).2 (case3ActivePair_valid x D hG j)
    (by omega) hn hsquare hL (s := s₁) ((harr₁ 33).trans hloop) ((harr₁ 34).trans hmat)
    ((hreg₁ 14 (by decide) (by decide) (by decide)).trans hrn) hru hrv
  let s₂ := s₁.setReg 68 (case3ActivePairOwner x D Z j)
  obtain ⟨s₃, hex₃, hheads₃, hnext₃, hcounts₃, harr₃, hreg₃⟩ :=
    case3BucketInsertProg_exec (case3ActivePairOwner x D Z) j.1 j.2
      (case3ActivePairOwner_lt x D hG Z hdiv j) (by omega) (by omega) hL
      (s := s₂) ((harr₁ 35).trans hheads) ((harr₁ 36).trans hnext) ((harr₁ 37).trans hcounts)
      (by rw [State.setReg_regs_ne _ _ (by decide), hreg₁ 65 (by decide) (by decide) (by decide)]; exact hrj)
      (State.setReg_regs_self ..)
  refine ⟨s₃, t₁ + (t₂ + 13), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hheads₃, hnext₃, hcounts₃, ?_, ?_⟩
  · intro a h35 h36 h37
    exact (harr₃ a h35 h36 h37).trans (harr₁ a)
  · intro r h66 h67 h68 h69
    rw [hreg₃ r, State.setReg_regs_ne _ _ h68]
    exact hreg₁ r h69 h66 h67

end GraphMinor.Compute
