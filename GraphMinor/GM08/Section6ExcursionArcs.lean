module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SphereDisc
import GraphMinor.Surface.DiscMerge
import GraphMinor.GM08.Section6Excursions

/-!
# Complete arcs for the outside components of a curve

For VIII (6.2), page 264, every component of the second curve outside the
first disc is an open arc. This file transports the parameter-circle
construction to the surface and proves that its two ends lie on the first
disc boundary. The full arc is exactly the closure of the component.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

local notation "𝕀" => unitInterval

/-- If the open part of a continuous arc avoids a closed disc, every point
of that arc in the disc lies on its boundary. Openness of the disc interior
rules out an endpoint reached from outside. -/
theorem arc_inter_disc_subset_boundary {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D : Set S} (hD : IsClosedDisc D)
    {a : 𝕀 → S} (ha : Continuous a)
    (havoid : ∀ r ∈ Ioo (0 : 𝕀) 1, a r ∉ D) : range a ∩ D ⊆ discBd D := by
  rintro x ⟨⟨r, rfl⟩, hrD⟩
  by_contra hrbd
  have hrcl : a r ∈ closure (a '' Ioo (0 : 𝕀) 1) := by
    rw [closure_open_arc_image_eq_range ha]
    exact mem_range_self r
  obtain ⟨y, hyD, t, ht, he⟩ := mem_closure_iff.mp hrcl
    (discInt D) (hD.isOpen_discInt hman) ⟨hrD, hrbd⟩
  exact havoid t ht (he.symm ▸ hyD.1)

/-- Every component of an `O`-arc outside a closed disc is the open part
of an embedded arc with both ends on the disc boundary, provided the curve
meets the disc in at least two points. This is the excursion decomposition
used in VIII (6.2), with no finiteness condition on the components. -/
theorem exists_arc_for_excursion_component {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D F : Set S} (hD : IsClosedDisc D)
    (hF : IsOArc F) (hinter : (F ∩ D).Nontrivial)
    {J : Set S} (hJ : J ∈ componentsIn (F \ D)) :
    ∃ a : 𝕀 → S, IsArcMap a ∧ a 0 ∈ discBd D ∧ a 1 ∈ discBd D ∧
      a '' Ioo (0 : 𝕀) 1 = J ∧ range a = closure J := by
  obtain ⟨φ⟩ := hF
  let q : Circle → S := fun w => (φ w).1
  have hq : Continuous q := continuous_subtype_val.comp φ.continuous
  have hqi : Function.Injective q := fun s t he => φ.injective (Subtype.ext he)
  have hqr : range q = F := by
    apply subset_antisymm
    · rintro _ ⟨w, rfl⟩
      exact (φ w).2
    · intro x hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp [q]⟩
  obtain ⟨q', hq'c, hleft⟩ := exists_inv_of_isEmbedding (hq.isClosedEmbedding hqi).isEmbedding
  let T : Set Circle := q ⁻¹' D
  have hT : IsClosed T := hD.isClosed.preimage hq
  obtain ⟨x, hx, y, hy, hxy⟩ := hinter
  obtain ⟨s, hs⟩ := hqr.symm ▸ hx.1
  obtain ⟨t, ht⟩ := hqr.symm ▸ hy.1
  have hsT : s ∈ T := by change q s ∈ D; rw [hs]; exact hx.2
  have htT : t ∈ T := by change q t ∈ D; rw [ht]; exact hy.2
  have hst : s ≠ t := fun he => hxy (hs.symm.trans ((congrArg q he).trans ht))
  rcases hJ with ⟨z, hz, rfl⟩
  obtain ⟨w, hw⟩ := hqr.symm ▸ hz.1
  have hwT : w ∉ T := fun h => hz.2 (hw ▸ h)
  obtain ⟨a, b, hab, _, ha0, ha1, hopen⟩ :=
    exists_circle_excursion_component hT hsT htT hst hwT
  let ℓ : 𝕀 → S := q ∘ a
  have hℓ : IsArcMap ℓ := ⟨hq.comp hab.1.1, hqi.comp hab.1.2⟩
  have him : q '' Tᶜ = F \ D := by
    apply subset_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨hqr ▸ mem_range_self v, hv⟩
    · rintro v ⟨hvF, hvD⟩
      obtain ⟨u, rfl⟩ := hqr.symm ▸ hvF
      exact ⟨u, hvD, rfl⟩
  have hcomp : q '' connectedComponentIn Tᶜ w = connectedComponentIn (F \ D) z := by
    have he := image_connectedComponentIn (f := q) (f' := q')
      (hq.continuousOn : ContinuousOn q Tᶜ)
      (hq'c.mono (image_subset_range _ _))
      (show LeftInvOn q' q Tᶜ from fun _ _ => hleft _) hwT
    rw [him, hw] at he
    exact he
  have hℓopen : ℓ '' Ioo (0 : 𝕀) 1 = connectedComponentIn (F \ D) z := by
    calc
      ℓ '' Ioo (0 : 𝕀) 1 = q '' (a '' Ioo (0 : 𝕀) 1) := by rw [image_image]; rfl
      _ = q '' connectedComponentIn Tᶜ w := by rw [hopen]
      _ = connectedComponentIn (F \ D) z := hcomp
  have hℓavoid : ∀ r ∈ Ioo (0 : 𝕀) 1, ℓ r ∉ D := by
    intro r hr
    exact (connectedComponentIn_subset (F \ D) z (hℓopen ▸ ⟨r, hr, rfl⟩)).2
  have hend : range ℓ ∩ D ⊆ discBd D := arc_inter_disc_subset_boundary hman hD hℓ.1 hℓavoid
  refine ⟨ℓ, hℓ, hend ⟨⟨0, rfl⟩, ha0⟩, hend ⟨⟨1, rfl⟩, ha1⟩, hℓopen, ?_⟩
  rw [← hℓopen, closure_open_arc_image_eq_range hℓ.1]

/-- Around a point of a circle outside a closed barrier, choose the whole
open arc component avoiding that barrier. Its complementary arc contains
all barrier intersections. In VIII (6.2), the chosen point is retained by
every enlargement, so this gives a common retained arc. -/
theorem exists_arc_around_point_avoiding_closed_set
    {S : Type u} [TopologicalSpace S] [T2Space S] {C B : Set S}
    (hC : IsOArc C) (hB : IsClosed B) (hinter : (C ∩ B).Nontrivial)
    {p : S} (hpC : p ∈ C) (hpB : p ∉ B) :
    ∃ q f : 𝕀 → S, IsTwoArcs q f ∧ range q ∪ range f = C ∧
      p ∈ q '' Ioo (0 : 𝕀) 1 ∧ Disjoint (q '' Ioo (0 : 𝕀) 1) B := by
  obtain ⟨φ⟩ := hC
  let j : Circle → S := fun w => (φ w).1
  have hj : Continuous j := continuous_subtype_val.comp φ.continuous
  have hji : Function.Injective j := fun s t he => φ.injective (Subtype.ext he)
  have hjr : range j = C := by
    apply subset_antisymm
    · rintro _ ⟨w, rfl⟩
      exact (φ w).2
    · intro x hx
      exact ⟨φ.symm ⟨x, hx⟩, by simp [j]⟩
  let T := j ⁻¹' B
  have hT : IsClosed T := hB.preimage hj
  obtain ⟨x, hx, y, hy, hxy⟩ := hinter
  obtain ⟨s, hs⟩ := hjr.symm ▸ hx.1
  obtain ⟨t, ht⟩ := hjr.symm ▸ hy.1
  obtain ⟨w, hw⟩ := hjr.symm ▸ hpC
  have hsT : s ∈ T := by change j s ∈ B; rw [hs]; exact hx.2
  have htT : t ∈ T := by change j t ∈ B; rw [ht]; exact hy.2
  have hst : s ≠ t := fun he => hxy (hs.symm.trans ((congrArg j he).trans ht))
  have hwT : w ∉ T := fun h => hpB (hw ▸ h)
  obtain ⟨a, b, hab, hcover, _, _, hopen⟩ :=
    exists_circle_excursion_component hT hsT htT hst hwT
  let q := j ∘ a
  let f := j ∘ b
  have hqf : IsTwoArcs q f := by
    refine ⟨⟨hj.comp hab.1.1, hji.comp hab.1.2⟩,
      ⟨hj.comp hab.2.1, hji.comp hab.2.2⟩,
      congrArg j hab.3, congrArg j hab.4, ?_⟩
    intro r v he
    exact hab.5 r v (hji he)
  have hrange : range q ∪ range f = C := by
    calc
      range q ∪ range f = j '' (range a ∪ range b) := by
        rw [image_union, ← range_comp, ← range_comp]
      _ = C := by rw [hcover, image_univ, hjr]
  have hqopen : q '' Ioo (0 : 𝕀) 1 = j '' connectedComponentIn Tᶜ w := by
    calc
      q '' Ioo (0 : 𝕀) 1 = j '' (a '' Ioo (0 : 𝕀) 1) := by rw [image_image]; rfl
      _ = j '' connectedComponentIn Tᶜ w := by rw [hopen]
  refine ⟨q, f, hqf, hrange, ?_, ?_⟩
  · rw [hqopen]
    exact ⟨w, mem_connectedComponentIn hwT, hw⟩
  · rw [hqopen]
    apply Set.disjoint_left.mpr
    rintro x ⟨v, hv, rfl⟩ hxB
    exact connectedComponentIn_subset Tᶜ w hv hxB

/-- The open arc of one excursion misses the complete arc of a different
excursion. Shared endpoints lie in the old disc and therefore cannot lie
in an open outside component. -/
theorem open_excursion_disjoint_complete_other
    {S : Type u} [TopologicalSpace S] {D F : Set S}
    {J K : Set S} (hJ : J ∈ componentsIn (F \ D)) (hK : K ∈ componentsIn (F \ D))
    (hne : J ≠ K) {a b : 𝕀 → S}
    (ha : a '' Ioo (0 : 𝕀) 1 = J) (hb : b '' Ioo (0 : 𝕀) 1 = K)
    (hb0 : b 0 ∈ D) (hb1 : b 1 ∈ D) :
    Disjoint (a '' Ioo (0 : 𝕀) 1) (range b) := by
  have hJK : Disjoint J K := by
    rcases hJ with ⟨x, hx, rfl⟩
    rcases hK with ⟨y, hy, rfl⟩
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)
  have hJD : J ⊆ Dᶜ := by
    rcases hJ with ⟨x, hx, rfl⟩
    exact (connectedComponentIn_subset (F \ D) x).trans (fun _ h => h.2)
  apply Set.disjoint_left.mpr
  rintro x hxa ⟨t, rfl⟩
  have hxJ : b t ∈ J := ha ▸ hxa
  have ht0 : t ≠ 0 := fun h => hJD hxJ (h ▸ hb0)
  have ht1 : t ≠ 1 := fun h => hJD hxJ (h ▸ hb1)
  have hxK : b t ∈ K := hb ▸ ⟨t,
    ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0),
      lt_of_le_of_ne (unitInterval.le_one t) ht1⟩, rfl⟩
  exact Set.disjoint_left.mp hJK hxJ hxK

end GraphMinor.GM08
