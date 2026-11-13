module

public import GraphMinor.GM06.Section3Dual
public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section5CompactRegionEnclosure

/-!
# Enclosures of components detached from a retained barrier

For the detached-component part of Reduction 2 in VI (5.5), page
130, fix one component of a drawing in the sphere. Every other
component lies in a complementary region of that component.
Group the finitely many components by region, and enclose each
group in a disc inside its region. Each disc boundary then misses
the entire drawing, including retained components nested inside it.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- All components except a chosen root component have finitely
many enclosures whose boundaries miss the whole drawing. -/
theorem exists_discs_enclosing_detached_components
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph) :
    ∃ F : Set (Set S), F.Finite ∧
      (∀ D ∈ F, IsClosedDisc D ∧ Disjoint D (compPointSet C) ∧
        Disjoint (discBd D) G.U ∧ (D ∩ G.U).Nonempty) ∧
      G.U \ compPointSet C ⊆ ⋃ D ∈ F, discInt D := by
  classical
  have : CompactSpace S := hS.1
  let T := graphComponents G.toGraph \ {C}
  have hT : T.Finite := (finite_graphComponents G).subset sdiff_subset
  let I := {B // B ∈ T}
  let : Fintype I := hT.fintype
  have hB (i : I) : IsGraphComponent i.1 G.toGraph := i.2.1
  have hne (i : I) : i.1 ≠ C := i.2.2
  let p : I → S := fun i => Classical.choose (isConnected_compPointSet G (hB i)).nonempty
  have hp (i : I) : p i ∈ compPointSet i.1 :=
    Classical.choose_spec (isConnected_compPointSet G (hB i)).nonempty
  have hoff (i : I) : compPointSet i.1 ⊆ (compPointSet C)ᶜ := by
    intro x hx hxC
    exact disjoint_left.mp (disjoint_compPointSet_of_ne G (hB i) hC (hne i)) hx hxC
  let r : I → Set S := fun i => connectedComponentIn (compPointSet C)ᶜ (p i)
  have hr (i : I) : r i ∈ componentsIn (compPointSet C)ᶜ :=
    ⟨p i, hoff i (hp i), rfl⟩
  have hsub (i : I) : compPointSet i.1 ⊆ r i :=
    (isConnected_compPointSet G (hB i)).isPreconnected.subset_connectedComponentIn (hp i) (hoff i)
  let K : I → Set S := fun i => ⋃ j : I, ⋃ (_ : r j = r i), compPointSet j.1
  have hKclosed (i : I) : IsClosed (K i) := by
    exact isClosed_iUnion_of_finite (fun j => isClosed_iUnion_of_finite
      (fun _ => isClosed_compPointSet G (hB j)))
  have hKr (i : I) : K i ⊆ r i := by
    rintro x hx
    obtain ⟨j, he, hxj⟩ := mem_iUnion₂.mp hx
    exact he ▸ hsub j hxj
  have hex (i : I) : ∃ D : Set S, IsClosedDisc D ∧ D ⊆ r i ∧
      K i ⊆ discInt D ∧ Disjoint D (compPointSet C) :=
    exists_disc_enclosing_compact_in_sphere_region hS hsph (isClosed_compPointSet G hC)
      (isConnected_compPointSet G hC) (hr i) (hKclosed i).isCompact (hKr i)
  choose D hD hDr hKD hDQ using hex
  have hbd (i : I) : Disjoint (discBd (D i)) G.U := by
    apply disjoint_left.mpr
    intro x hxb hxG
    rw [← biUnion_compPointSet_eq_U G] at hxG
    obtain ⟨B, hBmem, hxB⟩ := mem_iUnion₂.mp hxG
    by_cases hBC : B = C
    · exact disjoint_left.mp (hDQ i) (discBd_subset _ hxb) (hBC ▸ hxB)
    · let j : I := ⟨B, hBmem, hBC⟩
      have hxj : x ∈ r j := hsub j hxB
      have hxi : x ∈ r i := hDr i (discBd_subset _ hxb)
      have he : r j = r i := by
        exact (connectedComponentIn_eq hxj).trans (connectedComponentIn_eq hxi).symm
      have hxK : x ∈ K i := mem_iUnion₂.mpr ⟨j, he, hxB⟩
      exact (hKD i hxK).2 hxb
  refine ⟨range D, finite_range D, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    refine ⟨hD i, hDQ i, hbd i, ?_⟩
    refine ⟨p i, (hKD i (mem_iUnion₂.mpr ⟨i, rfl, hp i⟩)).1, ?_⟩
    rw [← biUnion_compPointSet_eq_U G]
    exact mem_iUnion₂.mpr ⟨i.1, i.2.1, hp i⟩
  · rintro x ⟨hxG, hxC⟩
    rw [← biUnion_compPointSet_eq_U G] at hxG
    obtain ⟨B, hBmem, hxB⟩ := mem_iUnion₂.mp hxG
    have hBC : B ≠ C := fun he => hxC (he ▸ hxB)
    let i : I := ⟨B, hBmem, hBC⟩
    exact mem_iUnion₂.mpr ⟨D i, mem_range_self i,
      hKD i (mem_iUnion₂.mpr ⟨i, rfl, hxB⟩)⟩

end GraphMinor.GM06
