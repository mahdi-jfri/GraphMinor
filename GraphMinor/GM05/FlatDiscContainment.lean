module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.GM11.PathClasses
import GraphMinor.GM07.Section11c
import GraphMinor.GM07.FlatEdges
import GraphMinor.GM11.OpenAround
import GraphMinor.GM11.FlatCover
import GraphMinor.GM11.RadialAccess
import GraphMinor.Surface.DiscMerge

/-!
# An open flat set lies in an open disc off the sphere

For GM V, (8.11), an open connected set whose circles bound ambient
discs is flat: GM VII, (11.2), extracts an essential circle from any
essential closed curve. Enlarge the set to a maximal open flat
path-connected set using the proved Zorn construction. Every circle
there bounds an ambient disc by Epstein's theorem. Adding that disc
preserves flatness, so maximality includes it. GM VII, (4.2), then
makes the maximal set an open disc unless the surface is a sphere.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM11 GM07

/-- Ambient disc boundaries in a set make it flat, by GM VII, (11.2). -/
theorem flat_of_ambient_discs {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {r : Set S}
    (H : ∀ F : Set S,F ⊆ r → IsOArc F → ∃ D : Set S,IsClosedDisc D ∧ F=discBd D) : Flat r := by
  let : T2Space S := hS.2.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  have hnull : ∀ F : Set S,F ⊆ r → IsOArc F → IsNullHomotopicOArc F := by
    intro F hF hO
    obtain ⟨D,hD,hbd⟩ := H F hF hO
    have hDF : F ⊆ D := by rw [hbd]; exact Surface.discBd_subset D
    have hd : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx ↦ hx (hS.2.2 x)
    exact (epstein S univ F hs inferInstance hO (subset_univ _) hd).2.1
      ⟨D,subset_univ _,hD,hDF⟩
  have hflat : IsFlat r := by
    intro φ hφ
    by_contra hn
    obtain ⟨F,hO,hsub,hnF⟩ := nonNullHomotopicOArc_in_curve hs φ hn
    exact hnF (hnull F (hsub.trans hφ) hO)
  exact GM07.IsFlat.flat hflat

/-- A maximal open flat path-connected set contains each disc bounded
by one of its circles. Adding such a disc preserves all three properties. -/
theorem maximal_flat_contains_disc {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Y : Set S} (hYo : IsOpen Y) (hYc : IsPathConnected Y) (hYf : Flat Y)
    (hmax : ∀ Y' : Set S,Y ⊆ Y' → IsOpen Y' → IsPathConnected Y' → Flat Y' → Y' ⊆ Y) :
    ∀ F : Set S,F ⊆ Y → IsOArc F → ∃ D : Set S,D ⊆ Y ∧ IsClosedDisc D ∧ discBd D=F := by
  let : T2Space S := hS.2.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  intro F hFY hF
  have hd : Disjoint F (bd S) := disjoint_left.mpr fun x _ hx ↦ hx (hS.2.2 x)
  obtain ⟨D,-,hD,hb⟩ := (epstein S univ F hs inferInstance hF (subset_univ _) hd).1 (null_of_flat hYf hF hFY)
  have hFclosed : IsClosed F := hF.isCompact.isClosed
  have hFpath : IsPathConnected F := by
    obtain ⟨φ⟩ := hF
    have hr : range (fun w : Circle ↦ (φ w).1)=F := by
      ext x
      exact ⟨fun ⟨w,hw⟩ ↦ hw ▸ (φ w).2,fun hx ↦ ⟨φ.symm ⟨x,hx⟩,by simp⟩⟩
    exact hr ▸ isPathConnected_range (continuous_subtype_val.comp φ.continuous)
  have hFD : F ⊆ D := by rw [← hb]; exact Surface.discBd_subset D
  have hDo : IsOpen (D \ F) := by rw [← hb]; exact (isOpenDisc_interior hS hD).1
  have hDsimple := IsClosedDisc.isSimplyConnectedSet hD
  have hflat : Flat (Y ∪ D) := flat_union_disc hYo hYc hYf (GM11.IsSimplyConnectedSet.flat hDsimple) hD.isCompact.isClosed
    hDsimple.1 hDo hFclosed hFpath hFY hFD
  have hopen : IsOpen (Y ∪ D) := by
    have he : Y ∪ D=Y ∪ (D \ F) := by
      ext x
      constructor
      · rintro (hy|hD)
        · exact .inl hy
        · by_cases hxF : x ∈ F
          · exact .inl (hFY hxF)
          · exact .inr ⟨hD,hxF⟩
      · rintro (hy|hD)
        · exact .inl hy
        · exact .inr hD.1
    rw [he]
    exact hYo.union hDo
  obtain ⟨x,hx⟩ := hFpath.nonempty
  have hpath : IsPathConnected (Y ∪ D) := hYc.union hDsimple.1 ⟨x,hFY hx,hFD hx⟩
  have hsub := hmax _ subset_union_left hopen hpath hflat
  exact ⟨D,fun x hx ↦ hsub (.inr hx),hD,hb⟩

/-- Off the sphere, the ambient disc condition yields an open-disc
container for any connected open set. -/
theorem nonsphere_openDisc_container {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬IsSphere S) {r : Set S} (hr : IsConnected r) (hro : IsOpen r)
    (H : ∀ F : Set S,F ⊆ r → IsOArc F → ∃ D : Set S,IsClosedDisc D ∧ F=discBd D) :
    ∃ D : Set S,IsOpenDisc D ∧ r ⊆ D := by
  let : T2Space S := hS.2.1
  let : LocallyPathConnectedSpace S := IsClosedSurface.locPathConnected hS
  have hrp : IsPathConnected r := hro.isConnected_iff_isPathConnected.mp hr
  obtain ⟨Y,hrY,hYo,hYc,hYf,hmax⟩ := exists_maximal_flat hro hrp (flat_of_ambient_discs hS H)
  have hbody := maximal_flat_contains_disc hS hYo hYc hYf hmax
  rcases open_disc S Y hS inferInstance hYc.isConnected hYo hbody with ⟨hsph,-⟩|hdisc
  · exact (hns hsph).elim
  · exact ⟨Y,hdisc,hrY⟩

end GraphMinor.GM05
