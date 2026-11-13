module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.CutComplement
import GraphMinor.Surface.CutOArc
import GraphMinor.Surface.PushOff

/-!
# Capping the surface cut along a circle

For the construction in Graph Minors V, (8.10), first cut a connected
closed surface along the circle using the library cutting theorem.
Then cap its cuffs using the library capping theorem. The caps are a
finite disjoint family of closed discs, and their complement is
homeomorphic to the complement of the original circle.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u

/-- The cut-and-cap construction in Graph Minors V, (8.10), before the
orientability and genus calculation. Both maps are the library maps,
and the complement homeomorphism is their restricted composite. -/
theorem exists_circle_cut_capping {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {C : Set S} (hC : IsOArc C) :
    ∃ (T : Type u) (_ : TopologicalSpace T), IsClosedSurface T ∧
      ∃ 𝓓 : Set (Set T), 𝓓.Finite ∧
        (∀ D ∈ 𝓓, IsClosedDisc D) ∧
        (∀ D ∈ 𝓓, ∀ D' ∈ 𝓓, D ≠ D' → Disjoint D D') ∧
        Nonempty (↥((⋃₀ 𝓓)ᶜ) ≃ₜ ↥(Cᶜ)) := by
  let : T2Space S := hS.2.1
  have hsurface : IsSurface S :=
    ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  have hd : Disjoint C (bd S) := by
    apply Set.disjoint_left.mpr
    intro x _ hx
    exact hx (hS.2.2 x)
  obtain ⟨Y,τY,ψ,hY,hψ,-,-⟩ := cutOArc S C hsurface inferInstance hC hd
  let : CompactSpace Y := hY.1
  let : T2Space Y := hY.2.1
  obtain ⟨T,τT,j,K,hT,hj,-,hcover,hmeet,-,𝓓,h𝓓,hunion,hdiscs,hdisjoint⟩ :=
    exists_capAll_discs Y hY
  refine ⟨T,τT,hT,𝓓,h𝓓,fun D hD ↦ (hdiscs D hD).1,hdisjoint,?_⟩
  rw [hunion]
  exact cut_cap_complement_homeomorph hψ hC.isCompact.isClosed hS
    hj.isEmbedding hcover hmeet

end GraphMinor.GM05
