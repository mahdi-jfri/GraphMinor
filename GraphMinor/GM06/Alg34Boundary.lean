module

public import GraphMinor.GM06.DiscRegions
public import GraphMinor.Compute.GM06Alg34Input

/-!
# Finite region boundaries for the disc input

A region boundary consists of its incident vertices and whole edges.
An edge meeting the closure of a region lies entirely in that closure,
by the local edge-side lemma. Thus finite vertex and edge labels give
finite incidence lists for every region, including non-disc regions.
-/

public section
namespace GraphMinor.GM06

open Set Surface GM11 Compute

universe u
variable {S : Type u} [TopologicalSpace S]

private theorem alg34_boundary_subset_U (hS : IsClosedDiscSpace S)
    {G : Drawing S} {r : Set S} (hr : r ∈ G.R) : closure r \ r ⊆ G.U := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  rintro p ⟨hcl, hn⟩
  by_contra hp
  obtain ⟨s, hs, hps⟩ := exists_region_of_notMem hp
  obtain ⟨q, hqs, hqr⟩ := mem_closure_iff.mp hcl s (region_isOpen hs) hps
  exact hn (region_eq_of_mem hs hr hqs hqr ▸ hps)

/-- The boundary of a region of a proper disc drawing is the union of
its incident vertices and edges. This supplies the finite boundary
information used as input to VI (3.4), page 121. -/
theorem alg34_region_boundary_eq (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hG : G.IsProper) {r : Set S} (hr : r ∈ G.R) :
    closure r \ r = (G.V ∩ closure r) ∪ ⋃ e ∈ {e ∈ G.E | e ⊆ closure r}, e := by
  ext p
  constructor
  · intro hp
    have hpU := alg34_boundary_subset_U hS hr hp
    by_cases hpV : p ∈ G.V
    · exact Or.inl ⟨hpV, hp.1⟩
    · obtain ⟨e, he, hpe⟩ := G.exists_edge_of_mem hpU hpV
      exact Or.inr (mem_iUnion₂.mpr ⟨e,
        ⟨he, disc_edge_subset_closure_of_incident hS hG he hr ⟨p, hpe, hp.1⟩⟩, hpe⟩)
  · rintro (hp | hp)
    · exact ⟨hp.2, fun hpr => region_subset hr hpr (G.V_subset_U hp.1)⟩
    · obtain ⟨e, ⟨he, hsub⟩, hpe⟩ := mem_iUnion₂.mp hp
      exact ⟨hsub hpe, fun hpr => region_subset hr hpr (G.closure_subset_U he (subset_closure hpe))⟩

/-- Given finite vertex and edge bijections, every region has a finite
boundary list. This is an existence proof for the input format, not an
encoding function from geometric instances. -/
theorem alg34_exists_region_boundary (hS : IsClosedDiscSpace S)
    {G : Drawing S} (hG : G.IsProper) {n m : ℕ}
    (v : Fin n ≃ G.V) (e : Fin m ≃ G.E) {r : Set S} (hr : r ∈ G.R) :
    ∃ b : GM06RegionBoundary n m,
      closure r \ r = {p | ∃ i ∈ b.vertices, (v i).val = p} ∪ ⋃ j ∈ b.edges, (e j).val := by
  classical
  let vs := (Finset.univ.filter (fun i => (v i).val ∈ closure r)).toList
  let es := (Finset.univ.filter (fun j => (e j).val ⊆ closure r)).toList
  refine ⟨⟨vs, es⟩, ?_⟩
  rw [alg34_region_boundary_eq hS hG hr]
  apply congrArg₂ (· ∪ ·)
  · ext p
    constructor
    · rintro ⟨hpV, hpr⟩
      obtain ⟨i, hi⟩ := v.surjective ⟨p, hpV⟩
      have hi' := congrArg Subtype.val hi
      refine ⟨i, ?_, hi'⟩
      simpa only [vs, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, hi'] using hpr
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(v i).property, by
        simpa only [vs, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hi⟩
  · ext p
    simp only [mem_iUnion, exists_prop, mem_ofPred_eq]
    constructor
    · rintro ⟨f, ⟨hf, hsub⟩, hpf⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨f, hf⟩
      have hj' := congrArg Subtype.val hj
      refine ⟨j, ?_, hj'.symm ▸ hpf⟩
      simpa only [es, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, hj'] using hsub
    · rintro ⟨j, hj, hpj⟩
      refine ⟨(e j).val, ⟨(e j).property, ?_⟩, hpj⟩
      simpa only [es, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj

end GraphMinor.GM06
