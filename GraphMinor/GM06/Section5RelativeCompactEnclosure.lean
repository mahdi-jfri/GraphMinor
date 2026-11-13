module

public import GraphMinor.Surface.DiscGrow
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM06.Section5RelativeDiscEnlargement
import GraphMinor.Surface.DiscMerge

/-!
# Enclosing a compact set while retaining an attached seed disc

For the enclosure construction in VI (5.5), page 130, grow a seed
disc through the open part of an allowed set. Point enlargement
and a local chart give neighbourhoods that every seed enlargement
can absorb. Compact induction then absorbs a compact set in the
open region, retaining the seed and staying in the allowed set.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

private theorem exists_relative_disc_enlargement_neighbourhood
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Y Z : Set S} (hYZ : Y ⊆ Z)
    (hYo : IsOpen Y) (hYc : IsPreconnected Y)
    (H : ∀ F : Set S, F ⊆ Z → IsOArc F →
      ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ discBd E = F)
    (hns : ¬ (IsSphere S ∧ Z = univ)) {y : S} (hy : y ∈ Y) :
    ∃ V ∈ 𝓝 y, ∀ D : Set S, D ⊆ Z → IsClosedDisc D → (discInt D ∩ Y).Nonempty →
      ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ D ⊆ E ∧ V ⊆ discInt E := by
  obtain ⟨U, h, j, c, hUY, hj0⟩ := (hS.2.2 y).exists_ballChart hYo hy (R := 3) (by norm_num)
  have hb : ball (0 : ℂ) 1 ⊆ ball 0 3 := ball_subset_ball (by norm_num)
  have hyV : y ∈ j '' ball 0 1 := ⟨0, by simp, hj0⟩
  refine ⟨j '' ball 0 1, (c.isOpen_image isOpen_ball hb).mem_nhds hyV, ?_⟩
  intro D hDZ hD hmeet
  obtain ⟨E, hEZ, hE, hDE, hyE⟩ := exists_relative_disc_enlargement_at_point
    hS hYZ hYo hYc H hns hDZ hD hmeet hy
  obtain ⟨E', hE'Z, hE', hEE', hVE'⟩ := exists_disc_absorbing_chart_in_set hS H hns
    hEZ hE c (hUY.trans hYZ) ⟨y, hyE, hyV⟩
  exact ⟨E', hE'Z, hE', hDE.trans hEE', hVE'⟩

/-- Enlarge an attached seed disc to put a compact subset of the
open region into its interior, while staying in the allowed set. -/
theorem exists_relative_disc_enclosing_compact
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Y Z : Set S} (hYZ : Y ⊆ Z)
    (hYo : IsOpen Y) (hYc : IsPreconnected Y)
    (H : ∀ F : Set S, F ⊆ Z → IsOArc F →
      ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ discBd E = F)
    (hns : ¬ (IsSphere S ∧ Z = univ))
    {K D : Set S} (hK : IsCompact K) (hKY : K ⊆ Y)
    (hDZ : D ⊆ Z) (hD : IsClosedDisc D) (hmeet : (discInt D ∩ Y).Nonempty) :
    ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ D ⊆ E ∧ K ⊆ discInt E := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  refine hK.induction_on (p := fun K => ∀ D : Set S, D ⊆ Z → IsClosedDisc D →
    (discInt D ∩ Y).Nonempty →
    ∃ E : Set S, E ⊆ Z ∧ IsClosedDisc E ∧ D ⊆ E ∧ K ⊆ discInt E)
    ?_ ?_ ?_ ?_ D hDZ hD hmeet
  · exact fun D hDZ hD _ => ⟨D, hDZ, hD, subset_rfl, empty_subset _⟩
  · intro A B hAB hB D hDZ hD hmeet
    obtain ⟨E, hEZ, hE, hDE, hBE⟩ := hB D hDZ hD hmeet
    exact ⟨E, hEZ, hE, hDE, hAB.trans hBE⟩
  · intro A B hA hB D hDZ hD hmeet
    obtain ⟨E, hEZ, hE, hDE, hAE⟩ := hA D hDZ hD hmeet
    have hEmeet : (discInt E ∩ Y).Nonempty := hmeet.mono (by
      rintro x ⟨hxD, hxY⟩
      exact ⟨discInt_mono hman hD hDE hxD, hxY⟩)
    obtain ⟨E', hE'Z, hE', hEE', hBE'⟩ := hB E hEZ hE hEmeet
    exact ⟨E', hE'Z, hE', hDE.trans hEE',
      union_subset (hAE.trans (discInt_mono hman hE hEE')) hBE'⟩
  · intro x hx
    obtain ⟨V, hV, hp⟩ := exists_relative_disc_enlargement_neighbourhood
      hS hYZ hYo hYc H hns (hKY hx)
    exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, hp⟩

end GraphMinor.GM06
