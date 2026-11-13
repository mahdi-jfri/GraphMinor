module

public import GraphMinor.GM08.Section18Main
public import GraphMinor.GM08.Section18X4Cut
import GraphMinor.GM08.Section18CutCount

/-!
# VIII (18.2) for every schism type but one

A schism (VII, pages 241–242) has one of six types. We have proved (18.2)
for each type except a circle that meets `bd(Σ)` in exactly one point:

* type (i) off the boundary: `theorem_18_2_circle_off`;
* types (ii) and (iii): `theorem_18_2_arc`;
* types (iv) and (v): `cutCountStatement`;
* type (vi): `theorem_18_2_X4`.

The remaining case is `CircleTouchCutStatement`. This file proves (18.2)
from it.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- (18.2) for a schism of type (i) that meets `bd(Σ)` in exactly one point. -/
def CircleTouchCutStatement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (a b c : ℕ), 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ (X : Set S) (p : S), IsOArc X → ¬ GM07.IsNearPlanar X → X ∩ bd S = {p} →
      ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
        GM07.IsCutAlongSet X ψ ∧ surfaceComplexity T < surfaceComplexity S

/-- **VIII (18.2)** from its one open case, the circle that touches the boundary. -/
theorem theorem182Statement_of_circleTouch (htouch : CircleTouchCutStatement.{w}) :
    Theorem182Statement.{w} := by
  intro S _ _ hS a b c habc hmodel X hX
  have : T2Space S := hS.2.1
  have hX' := hX
  rcases hX with ⟨hO, hnp, hfin, hle⟩ | harc | harc | ⟨h14, hoff, -⟩ | ⟨h3a, hoff, -⟩ |
    ⟨v, A, P, C₁, C₂, u, hA, hP, huv, hPA, rfl, hC₁, hC₂, hC, hv, hsur, hbd⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · have hoff : Disjoint X (bd S) :=
        disjoint_iff_inter_eq_empty.mpr ((ncard_eq_zero hfin).mp h0)
      exact theorem_18_2_circle_off hS hX' hoff hO hnp
    · obtain ⟨p, hp⟩ := ncard_eq_one.mp h1
      exact htouch S hS a b c habc hmodel X p hO hnp hp
  · exact theorem_18_2_arc hS hX' (Or.inl harc)
  · exact theorem_18_2_arc hS hX' (Or.inr harc)
  · obtain ⟨T, tT, ψ, hcut, -, hlt, -⟩ := cutCountStatement S hS a b c habc hmodel X hX' hoff
      (h14.elim Or.inl (fun h => Or.inr (Or.inl h)))
    exact ⟨T, tT, ψ, hcut, hlt⟩
  · obtain ⟨T, tT, ψ, hcut, -, hlt, -⟩ := cutCountStatement S hS a b c habc hmodel X hX' hoff
      (Or.inr (Or.inr h3a))
    exact ⟨T, tT, ψ, hcut, hlt⟩
  · obtain ⟨hncyl, h3⟩ := not_cylinder_and_three_le habc hmodel (two_le_ncard_cuffs hS hC₁ hC₂ hC)
    obtain ⟨T, tT, ψ, hcut, -, hlt⟩ :=
      theorem_18_2_X4 hS hncyl h3 hA hP huv hPA hC₁ hC hv hsur hbd
    exact ⟨T, tT, ψ, hcut, hlt⟩

end GraphMinor.GM08
