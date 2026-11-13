module

public import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Reflection of singleton search through the supplied labels

A geometric singleton division block has a unique supplied vertex
label. Injectivity of the vertex map makes its finite block a singleton
as well. Thus failure of the executable singleton search is exactly
absence of geometric singleton blocks, even when supplied lists repeat
labels or list the same block more than once.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Geometric singleton blocks are exactly images of finite singleton blocks. -/
theorem singleton_mem_iff (h : GM06DrawingRep x G Δ) (p : S) :
    {p} ∈ Δ ↔ ∃ v : Fin x.n, h.vertexEmbedding v = p ∧ {v} ∈ x.divisionSet := by
  constructor
  · intro hp
    obtain ⟨A, hA, he⟩ := h.division_map_eq.symm ▸ hp
    have hp : p ∈ h.vertexEmbedding '' A := he.symm ▸ Set.mem_singleton p
    obtain ⟨v, hv, hvp⟩ := hp
    have hAv : A = {v} := by
      apply h.vertexEmbedding.injective.image_injective
      rw [he, Set.image_singleton, hvp]
    exact ⟨v, hvp, hAv ▸ hA⟩
  · rintro ⟨v, hvp, hv⟩
    apply h.division_map_eq ▸ (show {p} ∈ (Set.image h.vertexEmbedding) '' x.divisionSet from ?_)
    exact ⟨{v}, hv, by rw [Set.image_singleton, hvp]⟩

/-- The executable search fails exactly when the interpreted division
contains no singleton block. -/
theorem findSingleton_none_iff (h : GM06DrawingRep x G Δ) :
    gm06FindSingleton x.division = none ↔ ∀ p : S, {p} ∉ Δ := by
  rw [gm06FindSingleton_eq_none_iff]
  constructor
  · intro hn p hp
    obtain ⟨v, _, hv⟩ := (h.singleton_mem_iff p).mp hp
    exact hn v hv
  · intro hn v hv
    exact hn (h.vertexEmbedding v) ((h.singleton_mem_iff _).mpr ⟨v, rfl, hv⟩)

end GraphMinor.Compute.GM06DrawingRep
