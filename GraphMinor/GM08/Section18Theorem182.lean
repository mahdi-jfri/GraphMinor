module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM07.CutStages
public import GraphMinor.GM07.Defs
import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM08.Section18SchismBoundary
import GraphMinor.GM08.Section18CircleCut
import GraphMinor.GM08.Section18ArcCases

/-!
# The statement of (18.2) with the counted cut

Page 285 says "we may “cut” along `X` in the natural way". At a point of `X`
where `k` branches meet, or at a point where `X` touches the boundary, the
natural cut has as many lifts as there are sides, not always two. So we state
(18.2) with `GM07.IsCutAlongSet`, which asks only that the cut map be a
quotient map with finite fibres, injective off the new boundary, and that the
new boundary lie exactly over `bd(Σ) ∪ X`. The predicate `IsCutting` of
`Surface/TopologyStatements`, with exactly two lifts at every point of `X`,
fits only the circle that misses the boundary and the proper arcs.

Every schism has such a cut (`exists_counted_cut_of_schism`, in any universe,
and `exists_cutAlongSet_of_schism`), so the statement is not vacuous. Here we
prove it for the closed surface, for the circle that misses the boundary, and
for both kinds of proper arc.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- **VIII (18.2)**, page 286: let `Σ` be a connected surface, not a sphere,
disc or cylinder, and let `X` be a schism in `Σ`. If `Σ'` is obtained from
`Σ` by cutting along `X`, then `g(Σ') < g(Σ)`. -/
def Theorem182Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ∀ (a b c : ℕ), 3 ≤ 3 * a + 3 * b + c → Nonempty (S ≃ₜ SurfaceModel a b c) →
    ∀ X : Set S, GM07.IsSchism X →
      ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
        GM07.IsCutAlongSet X ψ ∧ surfaceComplexity T < surfaceComplexity S

/-- A cut with two lifts at every point of a closed set is a cut along it in
the sense of `GM07.IsCutAlongSet`. -/
theorem isCutAlongSet_of_isCutting {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) (hT : IsSurface T) {F : Set S} (hF : IsClosed F) {ψ : T → S}
    (h : IsCutting ψ F) : GM07.IsCutAlongSet F ψ :=
  isCutAlongSet_of_cutMap hS hT hF (GM19.IsCutting.isCutMap h)

/-- (18.2) for a circle that misses the boundary (type (i) with no boundary
point). -/
theorem theorem_18_2_circle_off {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {X : Set S} (hX : GM07.IsSchism X) (hoff : Disjoint X (bd S))
    (hO : IsOArc X) (hnp : ¬ GM07.IsNearPlanar X) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      GM07.IsCutAlongSet X ψ ∧ surfaceComplexity T < surfaceComplexity S := by
  obtain ⟨T, tT, ψ, hT, hcut, hlt⟩ := exists_cut_complexity_lt_of_non_nearPlanar_oArc hS hO hoff hnp
  exact ⟨T, tT, ψ, isCutAlongSet_of_isCutting hS hT (isClosed_of_isSchism hS hX) hcut, hlt⟩

/-- (18.2) for the proper arcs, types (ii) and (iii). -/
theorem theorem_18_2_arc {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {X : Set S} (hX : GM07.IsSchism X)
    (harc : (IsProperIArc X ∧ ∃ C₁ ∈ cuffs S, ∃ C₂ ∈ cuffs S, C₁ ≠ C₂ ∧
      (lineEnds X ∩ C₁).Nonempty ∧ (lineEnds X ∩ C₂).Nonempty) ∨
      (IsProperIArc X ∧ ∃ C ∈ cuffs S, lineEnds X ⊆ C ∧ ¬ GM07.IsNearPlanar (X ∪ C))) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      GM07.IsCutAlongSet X ψ ∧ surfaceComplexity T < surfaceComplexity S := by
  have hXc := isClosed_of_isSchism hS hX
  rcases harc with ⟨hp, C, hC, D, hD, hCD, hmC, hmD⟩ | ⟨hp, C, hC, hends, hnp⟩
  · obtain ⟨T, tT, ψ, hT, hcut, hlt⟩ :=
      exists_cut_complexity_lt_of_schism_type_ii hS hp hC hD hCD hmC hmD
    exact ⟨T, tT, ψ, isCutAlongSet_of_isCutting hS hT hXc hcut, hlt⟩
  · obtain ⟨T, tT, ψ, hT, hcut, hlt⟩ :=
      exists_cut_complexity_lt_of_schism_type_iii hS hp hC hends hnp
    exact ⟨T, tT, ψ, isCutAlongSet_of_isCutting hS hT hXc hcut, hlt⟩

end GraphMinor.GM08
