module

public import GraphMinor.GM11.Corners
import GraphMinor.GM06.Section5DistinctCorners
import GraphMinor.GM06.Section5SectorBoundaryGerm
import GraphMinor.Surface.Gluing

/-!
# Excluding another edge from a disc beside a region

For the boundary-contact argument in VI (5.1), page 129, a region
at a vertex that does not separate the capped drawing has one
corner. Two distinct incident edges therefore bound that corner.
If both lie on the boundary of a disc containing the region, every
other incident edge must leave the disc near the vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- At a vertex with connected punctured drawing in a sphere, two
incident boundary edges of a region exclude every other incident
edge from lying in the disc containing that region. -/
theorem not_subset_disc_of_two_incident_boundary_edges
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) {Γ : Drawing S}
    {c : S} (hc : c ∈ Γ.V) (hpun : IsPreconnected (Γ.U \ {c}))
    {r D : Set S} (hr : r ∈ Γ.R) (hcr : c ∈ closure r)
    (hD : IsClosedDisc D) (hrD : r ⊆ D)
    {a b e : Set S} (ha : a ∈ Γ.E) (hb : b ∈ Γ.E) (hab : a ≠ b)
    (hca : c ∈ closure a) (hcb : c ∈ closure b)
    (har : a ⊆ closure r) (hbr : b ⊆ closure r)
    (haD : closure a ⊆ discBd D) (hbD : closure b ⊆ discBd D)
    (he : e ∈ Γ.E) (hea : e ≠ a) (heb : e ≠ b) (hce : c ∈ closure e) :
    ¬ e ⊆ D := by
  classical
  have : Nonempty S := ⟨c⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  obtain ⟨ba, hba⟩ := exists_end_eq hγ ha hc hca
  obtain ⟨bb, hbb⟩ := exists_end_eq hγ hb hc hcb
  let ka : halfEdges Γ γ c := ⟨(a, ba), ha, hba⟩
  let kb : halfEdges Γ γ c := ⟨(b, bb), hb, hbb⟩
  have hne : ka ≠ kb := fun h => hab (congrArg (fun j : halfEdges Γ γ c => j.1.1) h)
  have : Finite (halfEdges Γ γ c) := (finite_halfEdges Γ γ c).to_subtype
  have h2 : 2 ≤ Nat.card (halfEdges Γ γ c) := by
    have hh := ncard_le_card ({ka, kb} : Set (halfEdges Γ γ c))
    rwa [ncard_pair hne] at hh
  obtain ⟨next, ρ, P, W, Q, τ, hsec⟩ := exists_sectors hS Γ hγ hc h2
  have hinj := corners_injective_of_punctured_drawing_connected hS hsph hc hsec hpun
  obtain ⟨k, hrk⟩ := hsec.corners.all r hr hcr
  have hpairbound := incident_halfEdges_eq_corner_pair hsec.corners hinj k
  have hka : ka ∈ ({k, next k} : Set (halfEdges Γ γ c)) := by
    rw [← hpairbound, ← hrk]
    exact har
  have hkb : kb ∈ ({k, next k} : Set (halfEdges Γ γ c)) := by
    rw [← hpairbound, ← hrk]
    exact hbr
  have hpair : ({ka, kb} : Set (halfEdges Γ γ c)) = {k, next k} := by
    have hka' : ka = k ∨ ka = next k := by simpa only [mem_insert_iff, mem_singleton_iff] using hka
    have hkb' : kb = k ∨ kb = next k := by simpa only [mem_insert_iff, mem_singleton_iff] using hkb
    rcases hka' with hka | hka <;> rcases hkb' with hkb | hkb
    · exact False.elim (hne (hka.trans hkb.symm))
    · rw [hka, hkb]
    · rw [hka, hkb, pair_comm]
    · exact False.elim (hne (hka.trans hkb.symm))
  have hbound : ∀ j ∈ ({k, next k} : Set (halfEdges Γ γ c)), closure j.1.1 ⊆ discBd D := by
    rw [← hpair]
    intro j hj
    rcases hj with hj | hj
    · subst j; exact haD
    · have hj' := mem_singleton_iff.mp hj
      subst j
      exact hbD
  have hrhoD : ρ k ⊆ D := hrk ▸ hrD
  obtain ⟨N, hN, hcN, hexclude⟩ := exists_nhds_other_halfEdges_not_mem_disc
    (fun x => (hS.2.2 x).isManifoldPoint) hγ hc hsec k hD hrhoD
    (hbound k (mem_insert k {next k})) (hbound (next k) (mem_insert_of_mem k rfl))
  obtain ⟨be, hbe⟩ := exists_end_eq hγ he hc hce
  let ke : halfEdges Γ γ c := ⟨(e, be), he, hbe⟩
  have hkeNot : ke ∉ ({k, next k} : Set (halfEdges Γ γ c)) := by
    rw [← hpair]
    rintro (hke | hke)
    · exact hea (congrArg (fun j : halfEdges Γ γ c => j.1.1) hke)
    · exact heb (congrArg (fun j : halfEdges Γ γ c => j.1.1) (mem_singleton_iff.mp hke))
  have hNk : IsOpen ((spoke γ ke.1) ⁻¹' N) := hN.preimage (continuous_spoke hγ he)
  have h0N : (0 : I) ∈ (spoke γ ke.1) ⁻¹' N := by
    change spoke γ ke.1 0 ∈ N
    rw [spoke_zero, ke.2.2]
    exact hcN
  have h0cl : (0 : I) ∈ closure (Ioi (0 : I)) := by
    rw [closure_Ioi' (⟨1, zero_lt_one⟩ : (Ioi (0 : I)).Nonempty)]
    exact le_rfl
  obtain ⟨t, htN, htpos⟩ := mem_closure_iff.mp h0cl _ hNk h0N
  intro heD
  exact hexclude ke (fun h => hkeNot (Or.inl h)) (fun h => hkeNot (Or.inr h)) t htpos htN
    (heD (spoke_mem_edge (x := ke.1) hγ he htpos))

end GraphMinor.GM06
