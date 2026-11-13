module

public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section15Printed
import GraphMinor.GM08.Section15ShortGraft
import GraphMinor.GM08.Section15VertexLabels
import GraphMinor.GM08.Section15IsoSimulation
import GraphMinor.GM08.Section12
import GraphMinor.GM08.Section13
import GraphMinor.GM08.Section14

/-!
# Graph Minors VIII (15.4)

Disc grafts of bounded index are well-rooted by Section 12. Opening a
short tube gives such a disc graft, and root identifications recover
an isomorphic copy of the tube. Thus (13.3) makes the short-tube class
well-rooted. Apply the concatenation decomposition (15.3) and (14.5).
Finite relabelling removes the auxiliary infinite vertex label type.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

private theorem classA_wellRooted_infinite {α : Type u} {β : Type v}
    [Infinite α] (k r s : ℕ) :
    IsWellRootedGraftClass (printedClassA (α := α) (β := β) k r s) := by
  let m := k + r * (r - 1)
  let ℬ : Set (Graft α β) := {X | X.index ≤ m + 2 * s ∧ EmbedsGraft ClosedUnitDisc X}
  have hdisc : IsClosedDisc (univ : Set ClosedUnitDisc) :=
    ⟨(Homeomorph.Set.univ ClosedUnitDisc).symm⟩
  have hℬ : IsWellRootedGraftClass ℬ := theorem_6_1_disc hdisc (m + 2 * s)
  have hshort : IsWellRootedGraftClass
      {X : Graft α β | IsTubularGraft X ∧ tubularLength X < s ∧ X.index ≤ m} := by
    apply isWellRootedGraftClass_mono ?_
      (isWellRootedGraftClass_isoGraftClass (theorem_13_3_proof hℬ))
    intro X hX
    exact mem_iso_W_disc_of_tubularLength_lt hX.1 hX.2.1 hX.2.2
  exact isWellRootedGraftClass_mono (theorem_15_3_proof k r s) (theorem_14_5_proof _ hshort)

/-- Graph Minors VIII, (15.4), page 282: for all nonnegative integers
`k`, `r`, and `s`, the printed class `𝒜(k,r,s)` is well-rooted. The proof
uses Section 12, the short-tube disc cut, (13.3), (15.3), and (14.5). -/
theorem theorem_15_4_proof {α : Type u} {β : Type v} (k r s : ℕ) :
    IsWellRootedGraftClass (printedClassA (α := α) (β := β) k r s) := by
  classical
  intro X hX
  choose Y f hYG hYT hfinj hi hindex using
    fun n => exists_vertex_relabel_graft (α := α ⊕ ℕ) (X n)
  have hY : ∀ n, Y n ∈ printedClassA k r s := by
    intro n
    obtain ⟨hk, S, tS, τ, hfr, hno⟩ := hX n
    refine ⟨?_, S, tS, τ, hfr.of_isGraftIso (hi n), hno⟩
    rw [hindex n]
    exact hk
  obtain ⟨i, j, hij, hsim⟩ := classA_wellRooted_infinite k r s Y hY
  have hleft := isGraftSimulatedIn_of_isGraftIso_same_edges (hi i)
  have hright := isGraftSimulatedIn_of_isGraftIso_same_edges (hi j).symm
  exact ⟨i, j, hij, (hleft.trans hsim).trans hright⟩

end GraphMinor.GM08
