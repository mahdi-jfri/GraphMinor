module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.Crossing

/-! The path-connected version of disc crossing follows by applying the proved
compact-connected crossing theorem to the images of two paths. -/

public section
namespace GraphMinor.Surface
open Set Topology
universe u

/-- `DiscCrossingStatement` for path-connected sets: the ends lie on compact paths inside the two
sets. -/
theorem DiscCrossingStatement.of_isPathConnected_proved
    {S : Type u} [TopologicalSpace S] (D A B : Set S) (a c b d : S)
    (hD : IsClosedDisc D) (hA : A ⊆ D) (hB : B ⊆ D)
    (hA' : IsPathConnected A) (hB' : IsPathConnected B)
    (ha : a ∈ A) (hc : c ∈ A) (hb : b ∈ B) (hd : d ∈ B)
    (hcross : PairsCrossOn (discBd D) a c b d) : (A ∩ B).Nonempty := by
  obtain ⟨p, hp⟩ := hA'.joinedIn a ha c hc
  obtain ⟨q, hq⟩ := hB'.joinedIn b hb d hd
  have hprange : range p ⊆ A := by rintro _ ⟨x, rfl⟩; exact hp x
  have hqrange : range q ⊆ B := by rintro _ ⟨x, rfl⟩; exact hq x
  have hmeet := disc_crossing.{u} D (range p) (range q) a c b d hD (hprange.trans hA) (hqrange.trans hB)
    (isCompact_range p.continuous) (isCompact_range q.continuous)
    (isConnected_range p.continuous) (isConnected_range q.continuous)
    ⟨0, p.source⟩ ⟨1, p.target⟩ ⟨0, q.source⟩ ⟨1, q.target⟩ hcross
  exact hmeet.mono (inter_subset_inter hprange hqrange)

end GraphMinor.Surface
