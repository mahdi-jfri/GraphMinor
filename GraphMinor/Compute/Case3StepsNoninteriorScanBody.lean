module

public import GraphMinor.Compute.Case3StepsNoninteriorMemberExec
public import GraphMinor.Compute.Case3StepsMemberEncodingProg
public import GraphMinor.Compute.Case3StepsInteriorProg
public import GraphMinor.Compute.Case3StepsGroupMask
import GraphMinor.Compute.Case3StepsMemberScanBody

/-!
# The noninterior record scan body

The second candidate scan retains every existing interior record. It
constructs and tests each selected member, and writes a placeholder only
when the member meets the perimeter. The surrounding counting loop owns
the candidate-index increment.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Fill the selected noninterior members while retaining interior records. -/
def case3NoninteriorScanBody : Cmd :=
  .ite (.read 29 (.reg 54))
    (.seq case3MemberEncodingProg
      (.seq case3InteriorProg (.ite (.reg 100) .skip case3NoninteriorMemberProg))) .skip

/-- An unselected label is skipped without changing the state. -/
theorem case3NoninteriorScanBody_inactive_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (j : Fin (x.n + (case3InputEdges x).length))
    (hj : j ∉ case3GroupLabelSet x Z) (hw : 1 < 2 ^ w)
    (hL : x.n + (case3InputEdges x).length < 2 ^ w)
    {s : State} (hmask : s.arrs 29 = bitSetList (case3GroupLabelSet x Z))
    (hindex : s.regs 54 = j.1) : Exec w case3NoninteriorScanBody s s 3 := by
  have htest := case3MemberMask_eval (case3GroupLabelSet x Z) j hw hL hmask hindex
  rw [ite_eq_right hj] at htest
  exact .ite_false htest (.skip s)

/-- An interior candidate is tested and skipped, leaving its retained
branch record and the scan counters unchanged. -/
theorem case3NoninteriorScanBody_interior_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (he : D.numEdges < 2 ^ w) (hA : 2 + 3 * D.numActivePairs < 2 ^ w) {s : State}
    (hD : s.arrs 3 = D.enc) (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hheads : s.arrs 35 = case3BucketHeads (case3ActivePairOwner x D d.core.Z)
      (x.n + (case3InputEdges x).length) 0)
    (hnext : s.arrs 36 = case3BucketNext (case3ActivePairOwner x D d.core.Z) 0)
    (hcounts : s.arrs 37 = case3BucketCounts (case3ActivePairOwner x D d.core.Z)
      (x.n + (case3InputEdges x).length) 0)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1)
    (P : Finset (Fin x.n)) (hP : IsBitSet P 20 s)
    (hint : Disjoint (case3SelectedMember x d.core.Z i).verts P)
    (hmask : s.arrs 29 = bitSetList (case3GroupLabelSet x d.core.Z)) :
    ∃ s' t, Exec w case3NoninteriorScanBody s s' t ∧
      t ≤ 97 * x.n + 83 * (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs + 142 ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 31 → a ≠ 39 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, _, hverts, _, _, _, harr₁, hreg₁⟩ :=
    case3MemberEncodingProg_exec x D d hd i hw hn hkeys hm hsize he hA
      hD hin hZ htab hreps hheads hnext hcounts hrn hrg
  obtain ⟨s₂, t₂, hex₂, ht₂, htest, harr₂, hreg₂⟩ :=
    case3InteriorProg_exec (w := w) (s := s₁) (case3SelectedMember x d.core.Z i).verts P (by omega) (by omega)
      (IsBitSet.of_bitSetList _ _ _ hverts)
      (hP.of_arr_eq (harr₁ 20 (by decide) (by decide) (by decide) (by decide)))
      ((hreg₁ 14 (by decide)).trans hrn)
  have hone : s₂.regs 100 = 1 := by simpa only [hint, ↓reduceIte] using htest
  have hcond : (Expr.reg 100).eval w s₂ = some 1 := by
    simp only [Expr.eval, checkWord, hone, show 1 < 2 ^ w by omega, ↓reduceIte]
  have hmasktest := case3MemberMask_eval (w := w) (s := s) (case3GroupLabelSet x d.core.Z)
    (case3GroupLabelEquiv x i.1) (by omega) hsize hmask
    (by rw [case3GroupLabelEquiv_val]; exact hrg)
  rw [ite_eq_left ((mem_case3GroupLabelSet x d.core.Z i.1).mpr i.2)] at hmasktest
  refine ⟨s₂, 2 + (t₁ + (t₂ + (1 + 1))),
    .ite_true hmasktest (by decide) (.seq hex₁ (.seq hex₂ (.ite_true hcond (by decide) (.skip s₂)))),
    by omega, ?_, ?_⟩
  · intro a h25 h30 h31 h39
    exact (harr₂ a).trans (harr₁ a h25 h30 h31 h39)
  · intro r hr
    have hr90 : r < 90 := by rcases hr with hr | hr | hr | hr | hr <;> romega
    rw [hreg₂ r hr90]
    apply hreg₁ r
    rcases hr with hr | hr | hr | hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inl hr))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))


end GraphMinor.Compute
