module

public import GraphMinor.GM06.Alg34ComponentDivision

/-!
# Canonical roots enumerate the represented drawing components

The supplied vertex bijection sends finite reachability to actual walks.
Every drawing component therefore contains a finite root. Distinct roots
cannot represent the same component, since then they would be reachable.
This gives the exact component enumeration needed by VI (3.3)(iv).
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- The represented components through distinct finite roots are distinct. -/
theorem componentRoot_injective (h : GM06DrawingRep x G Δ) :
    Set.InjOn (fun a : Fin x.n => GM06.compOf G.toGraph (h.vertex a).val)
      {a | a ∈ x.componentRoots} := by
  intro a ha b hb heq
  change GM06.compOf G.toGraph (h.vertex a).val =
    GM06.compOf G.toGraph (h.vertex b).val at heq
  have hmem := self_mem_reachSet (show (h.vertex b).val ∈ G.toGraph.vertexSet from (h.vertex b).property)
  change (h.vertex b).val ∈ (GM06.compOf G.toGraph (h.vertex b).val).vertexSet at hmem
  rw [← heq] at hmem
  exact x.componentRoots_eq_of_reachable ha hb ((h.vertex_reachable_iff a b).mpr hmem.2)

/-- The components represented by finite roots are exactly all drawing components. -/
theorem componentRoot_image (h : GM06DrawingRep x G Δ) :
    graphComponents G.toGraph =
      (fun a : Fin x.n => GM06.compOf G.toGraph (h.vertex a).val) ''
        {a | a ∈ x.componentRoots} := by
  apply Set.Subset.antisymm
  · intro C hC
    obtain ⟨p, hp⟩ := hC.2.1.1
    have hpG := hC.1.vertexSet_mono hp
    obtain ⟨b, hb⟩ := h.vertex.surjective ⟨p, hpG⟩
    have hbp : (h.vertex b).val = p := congrArg Subtype.val hb
    obtain ⟨a, ha, hba⟩ := x.exists_componentRoot b
    have hCeq : C = GM06.compOf G.toGraph (h.vertex b).val :=
      hC.eq_compOf_of_mem (hbp.symm ▸ hp)
    have haC : (h.vertex a).val ∈ C.vertexSet := by
      rw [hCeq]
      exact ⟨(h.vertex a).property, (h.vertex_reachable_iff b a).mp hba⟩
    exact ⟨a, ha, (hC.eq_compOf_of_mem haC).symm⟩
  · rintro C ⟨a, _, rfl⟩
    exact isGraphComponent_compOf (h.vertex a).property

/-- Indexing the root list enumerates drawing components without repetition. -/
theorem componentRoot_get_injective (h : GM06DrawingRep x G Δ) :
    Function.Injective (fun i : Fin x.componentRoots.length =>
      GM06.compOf G.toGraph (h.vertex (x.componentRoots.get i)).val) := by
  intro i j heq
  have hnodup : x.componentRoots.Nodup := (List.nodup_finRange _).filter _
  apply (List.nodup_iff_injective_get.mp hnodup)
  exact h.componentRoot_injective (List.get_mem _ _) (List.get_mem _ _) heq

/-- The indexed canonical components exhaust the drawing's components. -/
theorem componentRoot_get_range (h : GM06DrawingRep x G Δ) :
    graphComponents G.toGraph = Set.range (fun i : Fin x.componentRoots.length =>
      GM06.compOf G.toGraph (h.vertex (x.componentRoots.get i)).val) := by
  rw [h.componentRoot_image]
  ext C
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
    exact ⟨i, congrArg (fun a => GM06.compOf G.toGraph (h.vertex a).val) hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, List.get_mem _ _, rfl⟩

end GraphMinor.Compute.GM06DrawingRep
