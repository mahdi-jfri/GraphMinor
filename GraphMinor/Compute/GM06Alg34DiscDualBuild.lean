module

public import GraphMinor.Compute.GM06Alg34DiscDualData
public import GraphMinor.Compute.GM06Alg34DualBuild
import GraphMinor.Compute.GM06Alg34GapPositionCast

/-!
# The dual constructor on plain augmented disc inputs

The supplied gap list determines the region lookup used by the dual
constructor. Its execution theorem therefore needs no extra function
or geometric witness as input. The exact output is the finite dual
operation on the supplied lists.
-/

public section
namespace GraphMinor.Compute

/-- Construct the finite disc dual directly from the two current input arrays,
while preserving the pending component queue and its cursors. -/
theorem gm06DualBuildProg_exec_input (X : GM06GapInput)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧
      R.length = L.length ∧ L.Nodup)
    (hR : 0 < X.drawing.regions.length) (hDiv : GM06.IsDivision X.drawing.divisionSet)
    {c : ℕ} (hc : 4 ≤ c) {s : State}
    (hinput : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    ∃ s' t, Exec (wordSize c X.drawing.size) gm06DualBuildProg s s' t ∧
      t ≤ 4000 * (X.drawing.size + 2) ^ 4 ∧
      s'.arrs 0 = X.discDualData.drawing.words ∧
      s'.arrs 47 = X.discDualData.discGapWords ∧
      s'.arrs 42 = s.arrs 42 ∧ s'.regs 7000 = s.regs 7000 ∧ s'.regs 7001 = s.regs 7001 ∧
      (∀ A : ℕ, 58 ≤ A → s'.arrs A = s.arrs A) := by
  obtain ⟨L, R, hL, hgroups, hlen, hLN⟩ := hshape
  let g : Fin L.length → Fin X.drawing.regions.length := fun i => R.get (Fin.cast hlen.symm i)
  have hg : List.ofFn g = R := (gm06OfFn_cast hlen.symm R.get).trans (List.ofFn_get R)
  have hw : List.ofFn (fun i => (g i).val) = R.map Fin.val := by
    calc
      List.ofFn (fun i => (g i).val) = (List.ofFn g).map Fin.val :=
        (List.map_ofFn (f := g) (g := Fin.val)).symm
      _ = R.map Fin.val := congrArg (List.map Fin.val) hg
  have hgap' : s.arrs 47 = List.ofFn (fun i => (g i).val) :=
    (hgap.trans (X.discGapWords_singleton R hgroups)).trans hw.symm
  have heq := X.discDualData_eq L R hL hgroups hR hlen g hg
  obtain ⟨s', t, he, ht, hi, hg', hq, hp, hend, ha⟩ :=
    gm06DualBuildProg_exec X.drawing hL hR hLN hDiv g hc hinput hgap'
  refine ⟨s', t, he, ht, ?_, ?_, hq, hp, hend, ha⟩
  · rw [heq]
    exact hi
  · rw [heq]
    exact hg'

end GraphMinor.Compute
