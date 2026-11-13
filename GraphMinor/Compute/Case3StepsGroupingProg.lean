module

public import GraphMinor.Compute.Case3StepsGroupMaskProg
public import GraphMinor.Compute.Case3StepsLoopOwnersProg
public import GraphMinor.Compute.Case3StepsEdgeMatrixProg
public import GraphMinor.Compute.Case3StepsBucketsProg

/-!
# Computing all routing tables for the selected division members

The selected-group mask initializes traversal counts. Subsequent passes
compute first-containing-member loop owners, the endpoint matrix, and the
ordered positive-pair buckets. Together these tables support exact member
encoding with quadratic vertex and linear pair work in XIII (9.9), step 5.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Compute selected groups and all loop, nonloop, and pair-bucket routing tables. -/
def case3GroupingProg : Cmd :=
  .seq case3GroupMaskProg (.seq case3LoopOwnersProg (.seq case3EdgeMatrixProg case3BucketsProg))

/-- The complete routing tables are computed within one quadratic vertex and
linear pair bound, retaining all earlier input and representative tables. -/
theorem case3GroupingProg_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) {s : State}
    (hD : s.arrs 3 = D.enc) (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hedges : s.arrs 28 = case3CoreEdgeRepList x d.core.Z) :
    ∃ s' t, Exec w case3GroupingProg s s' t ∧
      t ≤ x.n * x.n + 11 * x.n + 42 * (case3InputEdges x).length + 43 * D.numActivePairs +
        (x.n + (case3InputEdges x).length) * (77 * x.n + 141) + 58 ∧
      s'.arrs 29 = bitSetList (case3GroupLabelSet x d.core.Z) ∧
      s'.arrs 33 = List.ofFn (case3OrderedLoopLabel x d.core.Z) ∧
      s'.arrs 34 = case3EdgeMatrixPrefix x d.core.Z (case3InputEdges x).length ∧
      s'.arrs 35 = case3BucketHeads (case3ActivePairOwner x D d.core.Z)
        (x.n + (case3InputEdges x).length) 0 ∧
      s'.arrs 36 = case3BucketNext (case3ActivePairOwner x D d.core.Z) 0 ∧
      s'.arrs 37 = case3BucketCounts (case3ActivePairOwner x D d.core.Z)
        (x.n + (case3InputEdges x).length) 0 ∧
      s'.regs 14 = x.n ∧ s'.regs 17 = (case3InputEdges x).length ∧
      s'.regs 52 = x.n + (case3InputEdges x).length ∧ s'.regs 64 = D.numActivePairs ∧
      (∀ a, a ≠ 25 → a ≠ 29 → a ≠ 30 → a ≠ 33 → a ≠ 34 → a ≠ 35 → a ≠ 36 → a ≠ 37 →
        s'.arrs a = s.arrs a) ∧ (∀ r < 13, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hmask₁, hn₁, hm₁, hL₁, harr₁, hreg₁⟩ :=
    case3GroupMaskProg_exec x d.core.Z (by omega) hsize hin hreps hedges
  obtain ⟨s₂, t₂, hex₂, ht₂, hloop₂, harr₂, hreg₂⟩ :=
    case3LoopOwnersProg_exec x d hd hw hn hkeys hm hsize
      ((harr₁ 16 (by decide)).trans hin) (hZ.of_arr_eq (harr₁ 10 (by decide)))
      ((harr₁ 26 (by decide)).trans htab) ((harr₁ 27 (by decide)).trans hreps)
      (IsBitSet.of_bitSetList _ _ _ hmask₁) hn₁ hL₁
  have hn₂ : s₂.regs 14 = x.n := (hreg₂ 14 (by decide)).trans hn₁
  have hm₂ : s₂.regs 17 = (case3InputEdges x).length := (hreg₂ 17 (by decide)).trans hm₁
  have hL₂ : s₂.regs 52 = x.n + (case3InputEdges x).length := (hreg₂ 52 (by decide)).trans hL₁
  obtain ⟨s₃, t₃, hex₃, ht₃, hmat₃, harr₃, hreg₃⟩ :=
    case3EdgeMatrixProg_exec x d.core.Z (by omega) (by omega) hsquare hm hsize
      ((harr₂ 16 (by decide) (by decide) (by decide)).trans ((harr₁ 16 (by decide)).trans hin))
      (hZ.of_arr_eq ((harr₂ 10 (by decide) (by decide) (by decide)).trans (harr₁ 10 (by decide))))
      ((harr₂ 27 (by decide) (by decide) (by decide)).trans ((harr₁ 27 (by decide)).trans hreps))
      ((harr₂ 28 (by decide) (by decide) (by decide)).trans ((harr₁ 28 (by decide)).trans hedges)) hn₂ hm₂
  have hn₃ : s₃.regs 14 = x.n := (hreg₃ 14 (by decide) (by decide) (by decide) (by decide)).trans hn₂
  have hm₃ : s₃.regs 17 = (case3InputEdges x).length :=
    (hreg₃ 17 (by decide) (by decide) (by decide) (by decide)).trans hm₂
  have hL₃ : s₃.regs 52 = x.n + (case3InputEdges x).length :=
    (hreg₃ 52 (by decide) (by decide) (by decide) (by decide)).trans hL₂
  obtain ⟨s₄, t₄, hex₄, ht₄, hheads₄, hnext₄, hcounts₄, hA₄, harr₄, hreg₄⟩ :=
    case3BucketsProg_exec x D hG d.core.Z hdiv (by omega) (by omega) hsquare hA hsize
      ((harr₃ 3 (by decide)).trans ((harr₂ 3 (by decide) (by decide) (by decide)).trans
        ((harr₁ 3 (by decide)).trans hD)))
      ((harr₃ 33 (by decide)).trans hloop₂) hmat₃ hn₃ hL₃
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by nlinarith, ?_, ?_, ?_, hheads₄, hnext₄, hcounts₄, ?_, ?_, ?_, hA₄, ?_, ?_⟩
  · exact (harr₄ 29 (by decide) (by decide) (by decide)).trans ((harr₃ 29 (by decide)).trans
      ((harr₂ 29 (by decide) (by decide) (by decide)).trans hmask₁))
  · exact (harr₄ 33 (by decide) (by decide) (by decide)).trans ((harr₃ 33 (by decide)).trans hloop₂)
  · exact (harr₄ 34 (by decide) (by decide) (by decide)).trans hmat₃
  · exact (hreg₄ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn₃
  · exact (hreg₄ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm₃
  · exact (hreg₄ 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL₃
  · intro a h25 h29 h30 h33 h34 h35 h36 h37
    exact (harr₄ a h35 h36 h37).trans ((harr₃ a h34).trans
      ((harr₂ a h25 h30 h33).trans (harr₁ a h29)))
  · intro r hr
    rw [hreg₄ r (by romega) (by romega) (by romega) (by romega) (by romega) (by romega),
      hreg₃ r (by romega) (by romega) (by romega) (by romega), hreg₂ r (Or.inl hr)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
