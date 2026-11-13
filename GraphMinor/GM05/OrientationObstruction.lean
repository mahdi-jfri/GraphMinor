module

public import GraphMinor.GM19.Defs2
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM19.FeatureOrient
import GraphMinor.GM19.FragmentDirection
import GraphMinor.Surface.DiscUnion

/-!
# A geometric obstruction to orientation

For the orientable classification needed in GM V, (8.10), a crosscap
can be detected by a homeomorphism that fixes one disc and reverses a
second. A homeomorphism of a connected surface either preserves or
reverses its orientation everywhere. Fixing a disc rules out reversal.
Swapping two of three boundary points of another invariant disc then
rules out preservation. The lemmas here prove this obstruction using
the library's disc-based definition of an orientation.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- A homeomorphism fixing a closed disc pointwise preserves every
orientation of a connected surface. -/
theorem orientation_preserved_of_fixed_disc {S : Type} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsSurface S) (ω : SurfaceOrientation S)
    (e : S ≃ₜ S) {D : Set S} (hD : IsClosedDisc D) (hfix : ∀ x ∈ D,e x=x) :
    ω.IsPreservedBy e := by
  rcases homeo_orientation hS e with hp|hr
  · exact hp ω
  · have heD : e '' D=D := by
      apply Subset.antisymm
      · rintro _ ⟨x,hx,rfl⟩
        rw [hfix x hx]
        exact hx
      · intro x hx
        exact ⟨x,hx,hfix x hx⟩
    obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := hD.isOArc_discBd.exists_three
    have h := hr ω D hD a b c ha hb hc hab hbc hac
    rw [heD,hfix a (discBd_subset _ ha),hfix b (discBd_subset _ hb),hfix c (discBd_subset _ hc)] at h
    by_cases hp : ω.pos D a b c
    · exact ((h.mp hp) hp).elim
    · exact (hp (h.mpr hp)).elim

/-- A connected surface is not orientable if a homeomorphism fixes one
disc, maps another disc onto itself, and fixes one of three distinct
boundary points while exchanging the other two. These hypotheses are
properties of the map and discs, with no orientation chosen. -/
theorem not_orientable_of_disc_swap {S : Type} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsSurface S) (e : S ≃ₜ S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hfix : ∀ x ∈ D,e x=x) (hEimage : e '' E=E)
    {a b c : S} (ha : a ∈ discBd E) (hb : b ∈ discBd E) (hc : c ∈ discBd E)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hea : e a=a) (heb : e b=c) (hec : e c=b) : ¬IsOrientableSurface S := by
  rintro ⟨ω⟩
  have hp := orientation_preserved_of_fixed_disc hS ω e hD hfix
  have h := hp E hE a b c ha hb hc hab hbc hac
  rw [hEimage,hea,heb,hec] at h
  have hs := (show IsDirectionOf (discBd E) (ω.pos E) from ω.isDirection E hE).swap ha hb hc hab hbc hac
  by_cases hp : ω.pos E a b c
  · exact (hs.mp hp) (h.mpr hp)
  · have hq : ω.pos E a c b := by
      by_contra hq
      exact hp (hs.mpr hq)
    exact hp (h.mp hq)

end GraphMinor.GM05
