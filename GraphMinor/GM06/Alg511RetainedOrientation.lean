module

public import GraphMinor.Compute.GM06Alg511OrientationValue
public import GraphMinor.GM06.Section5ReflectionLinkage

/-!
# Retaining the stored linkage when reversing orientation

In VI (5.11), page 134, use the actual linkage already found by
maximum flow. The executed orientation branch records whether its
winding pair was negated. Retain the original linkage in one branch
and reflect that same linkage in the other. Its path drawings are
therefore fixed by the stored paths and the computed mode bit.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Every executed orientation choice preserves the winding of the
same found linkage or of its specified geometric reflection. -/
theorem alg511_orientation_retains_linkage {w k : ℕ} {G : Drawing ClosedCylinder}
    (hk : 0 < k) {s s' : State} {t : ℕ}
    (he : Exec w gm06Alg511OrientCompareProg s s' t)
    (L : CylinderLinkage k G) (htheta : L.HasTheta (gm06Alg511CurrentValue s)) :
    ∃ flip : Bool, s'.regs 57 = (if flip then 1 else 0) ∧
      (flip = false → L.HasTheta (gm06Alg511CurrentValue s')) ∧
      (flip = true → (section5ReflectedLinkage hk L).HasTheta (gm06Alg511CurrentValue s')) := by
  obtain ⟨flip, hmode, hvalue⟩ := gm06Alg511OrientCompareProg_value he
  cases flip with
  | false =>
    refine ⟨false, hmode, ?_, fun h => Bool.noConfusion h⟩
    intro _
    rw [hvalue]
    exact htheta
  | true =>
    refine ⟨true, hmode, fun h => Bool.noConfusion h, ?_⟩
    intro _
    rw [hvalue]
    exact hasTheta_section5ReflectedLinkage hk L htheta

end GraphMinor.GM06
