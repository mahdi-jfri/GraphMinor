module

public import GraphMinor.GM08.Section18Components
public import GraphMinor.GM08.Section18CutStep
import GraphMinor.GM08.Section18ClassD
import GraphMinor.GM08.Section18Sphere
import GraphMinor.GM08.Section18SplitStep
import GraphMinor.Surface.Classification
import GraphMinor.Surface.AddCrosscap
import GraphMinor.Surface.NormalWord
import GraphMinor.GM07.CutBounds

/-!
# The induction of (18.3)

The proof of (18.3) on pages 287 and 288 of VIII is an induction on `h`, and
for fixed `h` on `k`. For each pair `(h, k)` it shows that `𝒟(h, k)` is
well-rooted (`isWellRooted_classD`, from the two steps and the inductive
hypotheses), and then that `𝒞(h, k)` is well-rooted
(`isWellRooted_classC_of_classD`). When `h = 0` the only connected surface is
the sphere, and there is no smaller `h` to use; we treat it directly
(`isWellRooted_classD_zero`).

Here the labels of the grafts lie in one universe, and the cut step is a
hypothesis (`classCWellRooted_of_cutStep`). It holds when (18.2) holds with
the lift counts of `CutCountStatement` (`classCWellRooted_of_cutCount`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u w

/-- `𝒟(0, k)` is well-rooted: its surfaces are spheres. -/
theorem isWellRooted_classD_zero {α β : Type u} (k : ℕ) :
    IsWellRootedGraftClass (classD.{u, u, w} (α := α) (β := β) 0 k) := by
  have hM : IsSurface (ULift.{w} (SurfaceModel 0 0 0)) :=
    isSurface_of_homeo Homeomorph.ulift.symm (isSurface_model _ _ _).1
  refine isWellRootedGraftClass_mono ?_ (isWellRooted_classCSurface_sphere hM ⟨Homeomorph.ulift⟩ k)
  rintro X ⟨S, tS, hS, hconn, hg, hX⟩
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification.{w} S hS hconn
  have hgS : surfaceComplexity S = 4 * a + 2 * b + c := by
    rw [surfaceComplexity_eq_connected]
    exact connectedSurfaceComplexity_eq ⟨e⟩
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  have hc : c = 0 := by omega
  subst ha hb hc
  rw [← classCSurface_congr (e.trans Homeomorph.ulift.symm)]
  exact hX

/-- **(18.3) from the cut step**, for labels in one universe: `𝒞(h, k)` is
well-rooted for all `h` and `k`. -/
theorem classCWellRooted_of_cutStep (hcut : CutStepStatement.{u, w}) :
    ∀ h k, ClassCWellRooted.{u, w} h k := by
  intro h
  induction h using Nat.strong_induction_on with
  | _ h ihh =>
  have hD : ∀ k, (1 ≤ k → ClassCWellRooted.{u, w} h (k - 1)) → ∀ α β : Type u,
      IsWellRootedGraftClass (classD.{u, u, w} (α := α) (β := β) h k) := by
    intro k hprev α β
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · exact isWellRooted_classD_zero k
    · exact isWellRooted_classD hcut splitStepStatement (fun k' => ihh (h - 1) (by omega) k')
        hprev
  have hD0 := hD 0 (fun h => absurd h (by omega))
  intro k
  induction k with
  | zero => exact fun α β => isWellRooted_classC_of_classD (hD0 α β) (hD0 α β)
  | succ k ihk =>
    intro α β
    have hprev : 1 ≤ k + 1 → ClassCWellRooted.{u, w} h (k + 1 - 1) := fun _ => by simpa using ihk
    exact isWellRooted_classC_of_classD (hD (k + 1) hprev α β) (hD0 α β)

/-- **(18.3) from (18.2) with lift counts**, for labels in one universe. -/
theorem classCWellRooted_of_cutCount (hcount : CutCountStatement.{w}) :
    ∀ h k, ClassCWellRooted.{u, w} h k :=
  classCWellRooted_of_cutStep (cutStepStatement_of_cutCount hcount)

end GraphMinor.GM08
