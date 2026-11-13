module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM08.Section15ShrinkDisc

/-!
# Separating the empty sides of a tube

Shrink the second empty disc while fixing its drawing vertices that
are not on the first boundary. The two discs become disjoint. Their
new boundary union meets exactly the same drawing vertices as before,
including vertices shared by the original framing hoops. This makes
all framing roots actual boundary roots in the disc construction of
VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Two empty disc sides that meet only on their boundaries can be made
disjoint without changing the drawing roots on their boundary union.
This is the root-preserving framing adjustment in VIII (15.4), page 282. -/
theorem exists_separated_empty_sides {S : Type w} [TopologicalSpace S] [T2Space S]
    (G : Drawing S) {D E : Set S} (hE : IsClosedDisc E)
    (hinter : D ∩ E ⊆ discBd D ∩ discBd E)
    (hoff : Disjoint (discInt E) G.U) :
    ∃ E' : Set S, IsClosedDisc E' ∧ E' ⊆ E ∧ Disjoint D E' ∧
      Disjoint (discInt E') G.U ∧ G.IsNormal E' ∧
      G.V ∩ (discBd D ∪ discBd E') = G.V ∩ (discBd D ∪ discBd E) := by
  let Z := (G.V ∩ discBd E) \ discBd D
  have hZfin : Z.Finite := G.finite_V.subset (sdiff_subset.trans inter_subset_left)
  obtain ⟨E', hE', hsub, hcap, hZbd⟩ :=
    exists_shrunk_disc_fixing_finite_boundary hE hZfin (sdiff_subset.trans inter_subset_right)
  have hdis : Disjoint D E' := by
    refine disjoint_left.mpr ?_
    intro x hxD hxE'
    have hxold := hinter ⟨hxD, hsub hxE'⟩
    have hxZ : x ∈ Z := hcap ▸ ⟨hxE', hxold.2⟩
    exact hxZ.2 hxold.1
  have hGUold : G.U ∩ E ⊆ discBd E := by
    intro x hx
    by_contra hn
    exact disjoint_left.mp hoff ⟨hx.2, hn⟩ hx.1
  have hoff' : Disjoint (discInt E') G.U := by
    refine disjoint_left.mpr ?_
    intro x hx hxU
    have hxZ : x ∈ Z := hcap ▸ ⟨hx.1, hGUold ⟨hxU, hsub hx.1⟩⟩
    exact hx.2 (hZbd hxZ)
  have hVnew : G.V ∩ discBd E' = Z := by
    apply subset_antisymm
    · intro x hx
      have hxE' := discBd_subset E' hx.2
      exact hcap ▸ ⟨hxE', hGUold ⟨G.V_subset_U hx.1, hsub hxE'⟩⟩
    · exact fun x hx => ⟨hx.1.1, hZbd hx⟩
  have hnormal : G.IsNormal E' := by
    intro x hx
    have hxZ : x ∈ Z := hcap ▸ ⟨hx.1, hGUold ⟨hx.2, hsub hx.1⟩⟩
    exact hxZ.1.1
  refine ⟨E', hE', hsub, hdis, hoff', hnormal, ?_⟩
  rw [inter_union_distrib_left, hVnew, inter_union_distrib_left]
  ext x
  constructor
  · rintro (hx | hx)
    · exact .inl hx
    · exact .inr hx.1
  · rintro (hx | hx)
    · exact .inl hx
    · by_cases hxD : x ∈ discBd D
      · exact .inl ⟨hx.1, hxD⟩
      · exact .inr ⟨hx, hxD⟩

end GraphMinor.GM08
