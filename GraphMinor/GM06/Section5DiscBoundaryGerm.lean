module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.SideCut
import GraphMinor.Surface.DiscNbhd
import GraphMinor.Surface.DiscMerge

/-!
# Nested discs with the same boundary near a point

In the local sector argument for VI (5.1), page 129, a smaller disc
and a strip disc share their two boundary arcs near the initial
vertex. They then contain the same side near that vertex. A small
half-disc in the larger disc has a connected set of interior points
dense in it. Those points cannot cross the smaller boundary, and
density of the smaller interior fixes which side they occupy.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u

/-- Local containment of one closed disc in another, together with
containment of their boundaries near a common point, makes the discs
agree on that side near the point. -/
theorem exists_nhds_disc_of_local_boundary_germ
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {D Q N : Set S} {c : S}
    (hD : IsClosedDisc D) (hQ : IsClosedDisc Q) (hQD : N ∩ Q ⊆ D)
    (hcQ : c ∈ Q) (hN : IsOpen N) (hcN : c ∈ N)
    (hbd : N ∩ discBd Q ⊆ discBd D) :
    ∃ O : Set S, IsOpen O ∧ c ∈ O ∧ D ∩ O ⊆ Q := by
  have hDu : IsClosedDisc (univ : Set D) := by
    obtain ⟨e⟩ := hD
    exact ⟨e.trans (Homeomorph.Set.univ D).symm⟩
  have hmanD (x : D) : IsManifoldPoint x := isManifoldPoint_of_disc hDu (by simp)
  let cD : D := ⟨c, hQD ⟨hcN, hcQ⟩⟩
  obtain ⟨V, P, hV, hcV, hVN, hPV, hPc, hPi, hVP⟩ :=
    (hmanD cD).exists_half (hN.preimage continuous_subtype_val) hcN
  let M : Set S := Subtype.val '' P
  have hMc : IsPreconnected M := hPc.image Subtype.val continuous_subtype_val.continuousOn
  have hMint : M ⊆ discInt D := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro ⟨z, hz, heq⟩
    have hzy : z = y := Subtype.ext heq
    exact (hzy ▸ hz) (hPi y hy)
  have hMN : M ⊆ N := by
    rintro x ⟨y, hy, rfl⟩
    exact hVN (hPV hy)
  have hMbd : Disjoint M (discBd Q) := by
    refine disjoint_left.mpr ?_
    intro x hx hxQ
    exact (hMint hx).2 (hbd ⟨hMN hx, hxQ⟩)
  have hMsplit : M ⊆ discInt Q ∪ Qᶜ := by
    intro x hx
    by_cases hxQ : x ∈ Q
    · exact Or.inl ⟨hxQ, fun h => disjoint_left.mp hMbd hx h⟩
    · exact Or.inr hxQ
  obtain ⟨O, hO, hVO⟩ := isOpen_induced_iff.mp hV
  have hcO : c ∈ O := by
    have hcV' : cD ∈ Subtype.val ⁻¹' O := hVO ▸ hcV
    exact hcV'
  have hVM : Subtype.val '' V ⊆ closure M := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_closure_image continuous_subtype_val.continuousAt (hVP hy)
  have hQintopen := hQ.isOpen_discInt hman
  obtain ⟨q, hqO, hqQ⟩ := mem_closure_iff.mp (hQ.subset_closure_discInt hcQ) (O ∩ N) (hO.inter hN) ⟨hcO, hcN⟩
  have hqD : q ∈ D := hQD ⟨hqO.2, hqQ.1⟩
  have hqV : (⟨q, hqD⟩ : D) ∈ V := by
    rw [← hVO]
    exact hqO.1
  have hqM : q ∈ closure M := hVM ⟨⟨q, hqD⟩, hqV, rfl⟩
  obtain ⟨x, hxQ, hxM⟩ := mem_closure_iff.mp hqM (discInt Q) hQintopen hqQ
  have hMQ : M ⊆ Q := by
    rcases hMc.subset_or_subset hQintopen hQ.isClosed.isOpen_compl
        (disjoint_left.mpr fun x hx hxQ => hxQ hx.1) hMsplit with h | h
    · exact h.trans (discInt_subset Q)
    · exact False.elim (h hxM hxQ.1)
  refine ⟨O ∩ N, hO.inter hN, ⟨hcO, hcN⟩, ?_⟩
  rintro x ⟨hxD, hxO⟩
  have hxV : (⟨x, hxD⟩ : D) ∈ V := by rw [← hVO]; exact hxO.1
  exact hQ.isClosed.closure_subset_iff.mpr hMQ (hVM ⟨⟨x, hxD⟩, hxV, rfl⟩)

/-- If the boundary of a nested closed disc stays on the larger
boundary near a common point, the smaller disc fills the larger disc
near that point. -/
theorem exists_nhds_nested_disc_of_boundary_germ
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {D Q N : Set S} {c : S}
    (hD : IsClosedDisc D) (hQ : IsClosedDisc Q) (hQD : Q ⊆ D)
    (hcQ : c ∈ Q) (hN : IsOpen N) (hcN : c ∈ N)
    (hbd : N ∩ discBd Q ⊆ discBd D) :
    ∃ O : Set S, IsOpen O ∧ c ∈ O ∧ D ∩ O ⊆ Q :=
  exists_nhds_disc_of_local_boundary_germ hman hD hQ
    (fun _ hx => hQD hx.2) hcQ hN hcN hbd

end GraphMinor.GM06
