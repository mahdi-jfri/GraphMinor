module

public import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.CollarCut

/-!
# Keeping region-boundary collars away from other components

The boundary walks in the drawing input of VI (5.11), page 134,
may surround different connected components. A sufficiently short
collar of one component misses every other closed component. Project
the compact preimage of that closed set to the height interval and
choose a small positive height outside this projection.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.GM11 GraphMinor.Surface unitInterval
universe u

/-- A continuous collar whose bottom misses a closed set has a
uniform positive height up to which the entire collar misses it. -/
theorem alg511_exists_collar_height_avoiding_closed
    {S : Type u} [TopologicalSpace S] (h : C(Circle × I, S))
    {Q : Set S} (hQ : IsClosed Q) (hbot : ∀ z : Circle, h (z, 0) ∉ Q) :
    ∃ ε : I, 0 < ε ∧ ∀ z t, t ≤ ε → h (z, t) ∉ Q := by
  have hK : IsCompact (h ⁻¹' Q) := (hQ.preimage h.continuous).isCompact
  have hT : IsCompact (Prod.snd '' (h ⁻¹' Q)) := hK.image continuous_snd
  have hzero : (0 : I) ∉ Prod.snd '' (h ⁻¹' Q) := by
    rintro ⟨⟨z, t⟩, hp, rfl⟩
    exact hbot z hp
  obtain ⟨ε, hε, hsmall⟩ := exists_small (hT.isClosed.isOpen_compl.mem_nhds hzero)
  exact ⟨ε, hε, fun z t ht hmem => hsmall t ht ⟨(z, t), hmem, rfl⟩⟩

end GraphMinor.GM06
