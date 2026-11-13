module

public import GraphMinor.GM11.Corners
import GraphMinor.GM06.Section5InitialSpokes
import GraphMinor.GM06.Section5DiscBoundaryGerm
import GraphMinor.Surface.DiscMerge

/-!
# Comparing a region sector with a closed strip disc

For the local boundary argument in VI (5.1), page 129, the boundary
of a sector near its vertex lies on its two bounding edges. If the
sector region lies in a closed disc and those bounding edges lie on
the disc boundary, the local disc comparison puts every nearby disc
point in the sector. The other half-edges must then lie outside that
disc near the vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A sector boundary near its vertex lies on the closures of its
two bounding edges. -/
theorem exists_nhds_sector_boundary_subset_edges
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {c : S} (hc : c ∈ Γ.V)
    {next : halfEdges Γ γ c → halfEdges Γ γ c}
    {ρ P Q : halfEdges Γ γ c → Set S} {W : Set S} {τ : halfEdges Γ γ c → I}
    (hsec : IsSectors Γ γ c next ρ P W Q τ) (k : halfEdges Γ γ c) :
    ∃ N : Set S, IsOpen N ∧ c ∈ N ∧ N ∩ discBd (Q k) ⊆
      closure k.1.1 ∪ closure (next k).1.1 := by
  obtain ⟨N, hN, hcN, hcover⟩ := exists_nhds_drawing_initial_spokes hγ hc
  refine ⟨N ∩ W, hN.inter hsec.isOpen, ⟨hcN, hsec.mem⟩, ?_⟩
  rintro x ⟨⟨hxN, hxW⟩, hxbd⟩
  rcases hcover x ⟨hxN, hsec.bdU k ⟨hxW, hxbd⟩⟩ with hxc | ⟨j, t, ht, htx⟩
  · subst x
    apply Or.inl
    have hh := end_mem_closure hγ k.2.1 k.1.2
    rwa [k.2.2] at hh
  · have hj : j = k ∨ j = next k := by
      by_contra hn
      have hjk : j ≠ k := fun h => hn (Or.inl h)
      have hjnext : j ≠ next k := fun h => hn (Or.inr h)
      have hspW : spoke γ j.1 t ∈ W := htx.symm ▸ hxW
      exact hsec.off k j hjk hjnext t ht hspW (htx.symm ▸ Surface.discBd_subset (Q k) hxbd)
    rcases hj with hj | hj
    · subst j
      exact Or.inl (subset_closure (htx ▸ spoke_mem_edge hγ k.2.1 ht))
    · subst j
      exact Or.inr (subset_closure (htx ▸ spoke_mem_edge hγ (next k).2.1 ht))

/-- A sector whose region lies in a closed set lies in that set
near its vertex, including its boundary points. -/
theorem sector_inter_neighbourhood_subset_of_region_subset
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {γ : Set S → I → S} {c : S}
    {next : halfEdges Γ γ c → halfEdges Γ γ c}
    {ρ P Q : halfEdges Γ γ c → Set S} {W : Set S} {τ : halfEdges Γ γ c → I}
    (hsec : IsSectors Γ γ c next ρ P W Q τ) (k : halfEdges Γ γ c)
    {D : Set S} (hD : IsClosed D) (hrD : ρ k ⊆ D) : W ∩ Q k ⊆ D := by
  rintro x ⟨hxW, hxQ⟩
  have hxcl : x ∈ closure (W ∩ discInt (Q k)) :=
    hsec.isOpen.inter_closure ⟨hxW, (hsec.disc k).subset_closure_discInt hxQ⟩
  have hsub : W ∩ discInt (Q k) ⊆ D := by
    rintro y ⟨hyW, hyQ⟩
    exact hrD (hsec.sub k (hsec.inside k ⟨⟨hyW, hyQ.1⟩, hyQ.2⟩))
  exact hD.closure_subset_iff.mpr hsub hxcl

/-- If a sector region lies in a closed disc and its two bounding
edges lie on that boundary, every other half-edge lies outside the
disc sufficiently near the vertex. This is the local exclusion used
in the boundary-contact step of VI (5.1). -/
theorem exists_nhds_other_halfEdges_not_mem_disc
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {c : S} (hc : c ∈ Γ.V)
    {next : halfEdges Γ γ c → halfEdges Γ γ c}
    {ρ P Q : halfEdges Γ γ c → Set S} {W : Set S} {τ : halfEdges Γ γ c → I}
    (hsec : IsSectors Γ γ c next ρ P W Q τ) (k : halfEdges Γ γ c)
    {D : Set S} (hD : IsClosedDisc D) (hrD : ρ k ⊆ D)
    (hkD : closure k.1.1 ⊆ discBd D) (hnD : closure (next k).1.1 ⊆ discBd D) :
    ∃ N : Set S, IsOpen N ∧ c ∈ N ∧
      ∀ j : halfEdges Γ γ c, j ≠ k → j ≠ next k →
        ∀ t : I, 0 < t → spoke γ j.1 t ∈ N → spoke γ j.1 t ∉ D := by
  obtain ⟨V, hV, hcV, hbd⟩ := exists_nhds_sector_boundary_subset_edges hγ hc hsec k
  have hlocal := sector_inter_neighbourhood_subset_of_region_subset hsec k hD.isClosed hrD
  have hQD : (V ∩ W) ∩ Q k ⊆ D := fun _ hx => hlocal ⟨hx.1.2, hx.2⟩
  have hbdD : (V ∩ W) ∩ discBd (Q k) ⊆ discBd D := by
    intro x hx
    exact (hbd ⟨hx.1.1, hx.2⟩).elim (fun h => hkD h) (fun h => hnD h)
  obtain ⟨O, hO, hcO, hDO⟩ := exists_nhds_disc_of_local_boundary_germ hman hD (hsec.disc k)
    hQD (Surface.discBd_subset (Q k) (hsec.bd k))
    (hV.inter hsec.isOpen) ⟨hcV, hsec.mem⟩ hbdD
  refine ⟨O ∩ W, hO.inter hsec.isOpen, ⟨hcO, hsec.mem⟩, ?_⟩
  intro j hjk hjn t ht htN htD
  exact hsec.off k j hjk hjn t ht htN.2 (hDO ⟨htD, htN.1⟩)

end GraphMinor.GM06
