module

public import GraphMinor.GM08.Section18GraphCut
import GraphMinor.GM19.CutDrawing3

/-!
# Counting regular fibres of a schism cut

For a graph representing a schism, a point inside an edge has two lifts.
The finite-line cutting construction provides two disjoint bijective
lifts of a small closed subline through that point. This gives the
regular-point count needed for the Euler calculation in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

/-- Construct the graph cut used in VIII (18.2), with exactly two points
over each nonvertex point of the cutting graph. Branch vertices and
boundary contacts remain vertices and may have more lifts. -/
theorem exists_cutMap_of_graph_frame_with_regular_fibres {S : Type u}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {V : Set S} {E 𝓐 𝓛 : Set (Set S)} (hg : IsGraph V E)
    (hno : V ⊆ ⋃₀ E) (hbd : gr V E ∩ bd S ⊆ V)
    (hframe : GM19.IsCutFrame S 𝓐 𝓛) (hcover : bd S ∪ gr V E = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsSurface Y ∧ GM19.IsCutMap ψ (gr V E) ∧
      ∀ x ∈ gr V E \ V, (ψ ⁻¹' {x}).ncard = 2 := by
  have : T2Space S := hS.2.1
  have hgr : gr V E = ⋃₀ E := union_eq_right.mpr hno
  obtain ⟨Y, tY, _, ψ, hY, hψ, hsurj, hinj, hfinite, hboundary, hlift⟩ :=
    GM19.exists_cut_lines hS hg.fin hg.fine hg.edge hg.disj
      (fun L hL x hx => hbd ⟨Or.inr ⟨L, hL, hx.1⟩, hx.2⟩) hno hframe
      (by rwa [hgr] at hcover)
  refine ⟨Y, tY, ψ, hY, hgr ▸ ⟨hψ, hsurj, hinj, hfinite, hboundary⟩, ?_⟩
  intro x hx
  have hxedges : x ∈ ⋃₀ E := hgr ▸ hx.1
  obtain ⟨L, hL, hxL⟩ := hxedges
  obtain ⟨L', _, hsub, u, v, A, B, hpair⟩ := hlift L hL {x}
    (singleton_subset_iff.mpr ⟨hxL, hx.2⟩) (isCompact_singleton)
  obtain ⟨_, _, _, _, _, _, hdis, hunion, hA, hB, _⟩ := hpair
  have hxL' : x ∈ L' := hsub (mem_singleton x)
  obtain ⟨a, ha, hax⟩ := hA.surjOn hxL'
  obtain ⟨b, hb, hbx⟩ := hB.surjOn hxL'
  have hab : a ≠ b := fun heq => disjoint_left.mp hdis ha (heq ▸ hb)
  have hpre : ψ ⁻¹' {x} = {a, b} := by
    ext z
    constructor
    · intro hz
      have hzx : ψ z = x := hz
      have hzpre : z ∈ ψ ⁻¹' L' := by
        change ψ z ∈ L'
        rwa [hzx]
      have hzunion : z ∈ A ∪ B := hunion.symm ▸ hzpre
      rcases hzunion with hzA | hzB
      · exact Or.inl (hA.injOn hzA ha (hzx.trans hax.symm))
      · exact Or.inr (hB.injOn hzB hb (hzx.trans hbx.symm))
    · rintro (rfl | rfl)
      · exact hax
      · exact hbx
  rw [hpre, ncard_pair hab]

end GraphMinor.GM08
