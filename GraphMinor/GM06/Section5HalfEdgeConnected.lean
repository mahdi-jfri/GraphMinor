module

public import GraphMinor.GM11.Rotation

/-!
# A connected part of a vertex star uses one directed end

For the finite rotation interpretation in VI (5.7), page 133,
a positive polar edge ray is connected and misses the vertex.
Inside a small star it therefore uses a single directed end.
The full half-spokes are closed. Splitting off one of them from
the finite union of the others would separate the ray.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A point strictly before the midpoint of a directed end cannot
belong to any other incident half-spoke. -/
theorem halfedge_eq_of_short_spoke_point
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V)
    (a b : halfEdges Γ γ v) {t r : I} (ht0 : 0 < t) (ht1 : t < 1)
    (h : spoke γ a.1 t = spoke γ b.1 r) : a = b := by
  by_contra hab
  have hr0 : 0 < r := by
    apply unitInterval.pos_iff_ne_zero.mpr
    rintro rfl
    have hv' : spoke γ a.1 t = v := by
      rw [h, spoke_zero]
      exact b.2.2
    exact edge_notMem_V a.2.1 (spoke_mem_edge hγ a.2.1 ht0) (hv'.symm ▸ hv)
  have hne : a.1 ≠ b.1 := fun hh => hab (Subtype.ext hh)
  exact ht1.ne (spoke_eq_of_ne hγ a.2.1 b.2.1 hne ht0 hr0 h).1

/-- A nonempty connected set covered by short incident half-spokes
lies on exactly one of the incident half-spokes. -/
theorem exists_unique_halfedge_of_connected_star
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}
    {γ : Set S → I → S} (hγ : EdgePar Γ γ) {v : S} (hv : v ∈ Γ.V)
    {B : Set S} (hB : IsConnected B)
    (hstar : ∀ y ∈ B, ∃ a : halfEdges Γ γ v, ∃ t : I,
      0 < t ∧ t < 1 ∧ spoke γ a.1 t = y) :
    ∃! a : halfEdges Γ γ v, B ⊆ range (spoke γ a.1) := by
  classical
  let H := halfEdges Γ γ v
  let R : H → Set S := fun a => range (spoke γ a.1)
  have hRc (a : H) : IsClosed (R a) :=
    (isCompact_range (continuous_spoke hγ a.2.1)).isClosed
  let : Finite H := (finite_halfEdges Γ γ v).to_subtype
  obtain ⟨x, hxB⟩ := hB.nonempty
  obtain ⟨a, t, ht0, ht1, htx⟩ := hstar x hxB
  have hxR : x ∈ R a := ⟨t, htx⟩
  let D := ⋃ b : H, ⋃ (_ : b ≠ a), R b
  have hDc : IsClosed D := isClosed_iUnion_of_finite fun b => isClosed_iUnion_of_finite fun _ => hRc b
  have hcover : B ⊆ R a ∪ D := by
    intro y hyB
    obtain ⟨b, r, _, _, hry⟩ := hstar y hyB
    by_cases hba : b = a
    · subst b
      exact Or.inl ⟨r, hry⟩
    · exact Or.inr (mem_iUnion₂.mpr ⟨b, hba, r, hry⟩)
  have hno : B ∩ (R a ∩ D) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨hyB, ⟨r, hry⟩, hyD⟩
    obtain ⟨b, hba, u, huy⟩ := mem_iUnion₂.mp hyD
    obtain ⟨c, z, hz0, hz1, hzy⟩ := hstar y hyB
    have hca := halfedge_eq_of_short_spoke_point hγ hv c a hz0 hz1 (hzy.trans hry.symm)
    have hcb := halfedge_eq_of_short_spoke_point hγ hv c b hz0 hz1 (hzy.trans huy.symm)
    exact hba (hcb.symm.trans hca)
  have hBR : B ⊆ R a := by
    intro y hyB
    by_contra hyR
    have hyD : y ∈ D := (hcover hyB).resolve_left hyR
    obtain ⟨z, hz⟩ := isPreconnected_closed_iff.mp hB.isPreconnected _ _ (hRc a) hDc
      hcover ⟨x, hxB, hxR⟩ ⟨y, hyB, hyD⟩
    rw [hno] at hz
    exact hz
  refine ⟨a, hBR, ?_⟩
  intro b hb
  obtain ⟨r, hrx⟩ := hb hxB
  exact (halfedge_eq_of_short_spoke_point hγ hv a b ht0 ht1 (htx.trans hrx.symm)).symm

end GraphMinor.GM06
