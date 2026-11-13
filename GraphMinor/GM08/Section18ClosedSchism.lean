module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Schism
import GraphMinor.GM12.Section3NormalEssentialCircle
import GraphMinor.GM12.Section3SchismaticMinimum
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section9MoveOff

/-!
# A minimum normal schism on a closed surface

A small disc disjoint from the drawing has normal boundary. The proved
normal-circle criterion supplies an essential normal circle outside it.
Thus the alpha candidate family is nonempty even when its minimum is zero.
Extraction then attains alpha on a normal schism.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- On a connected closed non-sphere surface, alpha is attained on a normal
schism, including when alpha is zero. This supplies the small-schism
alternative in the closed-surface case of VIII (18.1). -/
theorem exists_normal_schism_at_alpha_of_closed {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (hns : ¬ IsSphere S) (G : Drawing S) :
    ∃ F : Set S, GM07.IsSchism F ∧ G.IsNormal F ∧ (F ∩ G.V).ncard = GM07.alpha G := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hs : IsSurface S := hS.isSurface
  have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hx (hS.2.2 x))
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨B, hB, _, _⟩ := GM07.exists_disc_in_open (hS.2.2 x) isOpen_univ (mem_univ x)
  obtain ⟨D, hD, _, hDoff⟩ := GM07.exists_subdisc_disjoint_drawing hs G hB (by rw [hbd]; simp)
  have hnD : G.IsNormal (discBd D) := by
    rintro z ⟨hzD, hzG⟩
    exact (disjoint_left.mp hDoff (Surface.discBd_subset D hzD) hzG).elim
  obtain ⟨A, hA, hnA, _, hAnull⟩ := GM12.exists_normal_nonnull_oArc_outside_disc hS hns G hD hnD
  have hnnear : ¬ GM07.IsNearPlanar A := by
    rintro (hp | ⟨C, hC, _⟩)
    · exact hAnull ((GM07.isPlanar_iff_isNullHomotopicOArc_of_isOArc hs hA).mp hp)
    · obtain ⟨y, hy, _⟩ := hC
      exact (hbd ▸ hy : y ∈ (∅ : Set S)).elim
  have hsch : GM07.IsSchismatic A := ⟨Or.inl hA, hnnear, fun F hF hFA =>
    (GM07.not_ssubset_of_isOArc hA hF hFA).elim⟩
  obtain ⟨F, hF, hnF, hcount⟩ := GM12.exists_normal_schismatic_at_alpha_of_extraction G
    ⟨A, hsch.isAlphaCandidate hs hnA⟩ (GM07.exists_schismatic_of_isAlphaCandidate hs hns G)
  exact ⟨F, isSchism_of_isSchismatic_off_boundary hs hns hF (by rw [hbd]; simp), hnF, hcount⟩

end GraphMinor.GM08
