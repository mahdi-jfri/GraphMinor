module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM08.Section15RegionDistance
import GraphMinor.GM08.Section15EmptySides
import GraphMinor.GM07.CylinderGrid

/-!
# A short normal arc between separated empty sides

A normal connected set joining two empty discs bounds their region
distance. The line for that distance joins their boundaries with no
larger vertex count. Empty larger disc sides let us apply this to the
original tube witness after separating its framing roots in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- A normal connector between empty caps produces a normal line
between them with no greater vertex count. This is the line used to
open the adjusted framing in VIII (15.4), page 282. -/
theorem exists_normal_line_between_discs_of_connector {S : Type}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S) (hsph : IsSphere S)
    {G : Drawing S} {D E A : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hDE : Disjoint D E) (hDoff : Disjoint (discInt D) G.U)
    (hEoff : Disjoint (discInt E) G.U) (hA : IsPreconnected A) (hn : G.IsNormal A)
    {p q : S} (hpA : p ∈ A) (hqA : q ∈ A) (hp : p ∈ discInt D) (hq : q ∈ discInt E) :
    ∃ (L : Set S) (u v : S), IsLineWithEnds L u v ∧ u ∈ discBd D ∧ v ∈ discBd E ∧
      G.IsNormal L ∧ Disjoint L (discInt D) ∧ Disjoint L (discInt E) ∧
      (L ∩ G.V).ncard ≤ (A ∩ G.V).ncard := by
  have hpU : p ∈ univ \ G.U := ⟨mem_univ _, disjoint_left.mp hDoff hp⟩
  have hqU : q ∈ univ \ G.U := ⟨mem_univ _, disjoint_left.mp hEoff hq⟩
  let r₀ := connectedComponentIn (univ \ G.U) p
  let r₂ := connectedComponentIn (univ \ G.U) q
  have hr₀ : r₀ ∈ G.R := ⟨p, hpU, rfl⟩
  have hr₂ : r₂ ∈ G.R := ⟨q, hqU, rfl⟩
  have hdist := mem_regLayer_of_normal_preconnected hS hsph hA hn hr₀ hr₂ hpA hqA
    (mem_connectedComponentIn hpU) (mem_connectedComponentIn hqU)
  have : T2Space S := hS.2.1
  exact GM07.exists_cross_line hS hD hE hDE hr₀ (mem_connectedComponentIn hpU) hp.1
    (mem_connectedComponentIn hqU) hq.1 hdist

/-- Shrinking empty sides does not increase the vertex cost of a normal
line between them. This is the short-line estimate after the root
adjustment in VIII (15.4), page 282. -/
theorem exists_normal_line_between_inner_discs {S : Type}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S) (hsph : IsSphere S)
    {G : Drawing S} {D E Q R I : Set S} {u v : S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : Disjoint D E)
    (hQ : IsClosedDisc Q) (hR : IsClosedDisc R) (hDQ : D ⊆ Q) (hER : E ⊆ R)
    (hQoff : Disjoint (discInt Q) G.U) (hRoff : Disjoint (discInt R) G.U)
    (hI : IsLineWithEnds I u v) (hu : u ∈ Q) (hv : v ∈ R) (hn : G.IsNormal I) :
    ∃ (L : Set S) (a b : S), IsLineWithEnds L a b ∧ a ∈ discBd D ∧ b ∈ discBd E ∧
      G.IsNormal L ∧ Disjoint L (discInt D) ∧ Disjoint L (discInt E) ∧
      (L ∩ G.V).ncard ≤ (I ∩ G.V).ncard := by
  have : T2Space S := hS.2.1
  obtain ⟨A, hAc, hNA, _, hQA, hRA, hAV⟩ :=
    exists_normal_connector_with_empty_sides hI hQ hR hu hv hQoff hRoff hn
  have hDint := discInt_mono (fun x => (hS.2.2 x).isManifoldPoint) hD hDQ
  have hEint := discInt_mono (fun x => (hS.2.2 x).isManifoldPoint) hE hER
  obtain ⟨p, hp⟩ := hD.nonempty_discInt
  obtain ⟨q, hq⟩ := hE.nonempty_discInt
  have h := exists_normal_line_between_discs_of_connector hS hsph hD hE hDE
    (hQoff.mono_left hDint) (hRoff.mono_left hEint) hAc hNA
    (hQA (hDint hp)) (hRA (hEint hq)) hp hq
  rwa [hAV] at h

end GraphMinor.GM08
