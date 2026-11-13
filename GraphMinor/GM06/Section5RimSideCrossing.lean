module

public import GraphMinor.GM06.Section2Dual
import Mathlib.Topology.Connected.PathConnected

/-!
# A closed rim side is detected by crossing two boundary directions

For the side interpretation in VI (5.7), page 133, the local
closed strip has two boundary directions on the polar rim. Away
from those directions, each of the two open arcs is entirely
inside or entirely outside. An outside marker and an inside point
therefore determine which arc is the strip side. Crossing the two
boundary directions against the candidate and outside marker is
exactly the test for that side.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem mem_closed_of_preconnected_avoids_frontier
    {X : Type*} [TopologicalSpace X] {B K : Set X}
    (hB : IsPreconnected B) (hK : IsClosed K) (hoff : Disjoint B (frontier K))
    {a b : X} (haB : a ∈ B) (haK : a ∈ K) (hbB : b ∈ B) : b ∈ K := by
  by_contra hbK
  have hcover : B ⊆ K ∪ (interior K)ᶜ := by
    intro x _
    by_cases hx : x ∈ K
    · exact Or.inl hx
    · exact Or.inr (fun hi => hx (interior_subset hi))
  obtain ⟨z, hzB, hzK, hzint⟩ := isPreconnected_closed_iff.mp hB _ _ hK
    isOpen_interior.isClosed_compl hcover ⟨a, haB, haK⟩
    ⟨b, hbB, fun hi => hbK (interior_subset hi)⟩
  have hzfr : z ∈ frontier K := by
    rw [frontier, hK.closure_eq]
    exact ⟨hzK, hzint⟩
  exact disjoint_left.mp hoff hzB hzfr

/-- A closed subset of the circle with only two possible boundary
points is detected, off those points, by crossing against any outside marker. -/
theorem mem_closed_circle_side_iff_crossesOn
    {K : Set Circle} (hK : IsClosed K) {p q c r : Circle}
    (hpq : p ≠ q) (hfr : frontier K ⊆ {p, q})
    (hin : (K \ {p, q}).Nonempty) (hcK : c ∉ K)
    (hcp : c ≠ p) (hcq : c ≠ q)
    (hrp : r ≠ p) (hrq : r ≠ q) (hrc : r ≠ c) :
    r ∈ K ↔ CrossesOn (univ : Set Circle) p q r c := by
  let A := circleOpenArc p q
  let B := circleOpenArc q p
  have hpart : ({p, q} : Set Circle)ᶜ = A ∪ B := compl_pair_eq_union_circleOpenArc hpq
  have hdis : Disjoint A B := disjoint_circleOpenArc hpq
  have hAB : A ≠ B := by
    obtain ⟨x, hx⟩ := nonempty_circleOpenArc hpq
    intro hh
    exact disjoint_left.mp hdis hx (hh ▸ hx)
  have hAoff : Disjoint A (frontier K) := by
    apply disjoint_left.mpr
    intro x hxA hxfr
    have hxpair := hfr hxfr
    have hxcomp : x ∈ ({p, q} : Set Circle)ᶜ := hpart.symm ▸ Or.inl hxA
    exact hxcomp hxpair
  have hBoff : Disjoint B (frontier K) := by
    apply disjoint_left.mpr
    intro x hxB hxfr
    have hxpair := hfr hxfr
    have hxcomp : x ∈ ({p, q} : Set Circle)ᶜ := hpart.symm ▸ Or.inr hxB
    exact hxcomp hxpair
  have hsameA {a b : Circle} (ha : a ∈ A) (haK : a ∈ K) (hb : b ∈ A) : b ∈ K :=
    mem_closed_of_preconnected_avoids_frontier (isPathConnected_circleOpenArc p q).isConnected.isPreconnected
      hK hAoff ha haK hb
  have hsameB {a b : Circle} (ha : a ∈ B) (haK : a ∈ K) (hb : b ∈ B) : b ∈ K :=
    mem_closed_of_preconnected_avoids_frontier (isPathConnected_circleOpenArc q p).isConnected.isPreconnected
      hK hBoff ha haK hb
  have hcpart : c ∈ A ∪ B := hpart ▸ (by simp [hcp, hcq])
  have hrpart : r ∈ A ∪ B := hpart ▸ (by simp [hrp, hrq])
  obtain ⟨a, haK, hapq⟩ := hin
  have hapart : a ∈ A ∪ B := hpart ▸ hapq
  have hcomp : r ∈ K ↔
      connectedComponentIn ({p, q} : Set Circle)ᶜ r ≠
        connectedComponentIn ({p, q} : Set Circle)ᶜ c := by
    rcases hcpart with hcA | hcB
    · have haB : a ∈ B := hapart.resolve_left (fun haA => hcK (hsameA haA haK hcA))
      rcases hrpart with hrA | hrB
      · have hrK : r ∉ K := fun hh => hcK (hsameA hrA hh hcA)
        rw [connectedComponentIn_compl_pair_eq_left hpq hrA,
          connectedComponentIn_compl_pair_eq_left hpq hcA]
        simp only [ne_eq, not_true_eq_false, iff_false]
        exact hrK
      · have hrK : r ∈ K := hsameB haB haK hrB
        rw [connectedComponentIn_compl_pair_eq_right hpq hrB,
          connectedComponentIn_compl_pair_eq_left hpq hcA]
        exact iff_of_true hrK hAB.symm
    · have haA : a ∈ A := hapart.resolve_right (fun haB => hcK (hsameB haB haK hcB))
      rcases hrpart with hrA | hrB
      · have hrK : r ∈ K := hsameA haA haK hrA
        rw [connectedComponentIn_compl_pair_eq_left hpq hrA,
          connectedComponentIn_compl_pair_eq_right hpq hcB]
        exact iff_of_true hrK hAB
      · have hrK : r ∉ K := fun hh => hcK (hsameB hrB hh hcB)
        rw [connectedComponentIn_compl_pair_eq_right hpq hrB,
          connectedComponentIn_compl_pair_eq_right hpq hcB]
        simp only [ne_eq, not_true_eq_false, iff_false]
        exact hrK
  rw [crossesOn_univ_iff_circleStdCoord]
  exact hcomp.trans (connectedComponentIn_compl_pair_ne_iff_circleCrosses
    hpq hrc hrp.symm hcp.symm hrq.symm hcq.symm)


/-- For a continuous rim map, two boundary directions and an outside
marker detect membership in a closed side by the rim crossing order. -/
theorem mem_closed_side_iff_crossesOn_of_rim_map
    {S : Type*} [TopologicalSpace S] (f : C(Circle, S))
    {D : Set S} (hD : IsClosed D) {p q c r : Circle}
    (hpq : p ≠ q) (hfr : f ⁻¹' frontier D ⊆ {p, q})
    (hin : (f ⁻¹' D \ {p, q}).Nonempty) (hcD : f c ∉ D)
    (hcp : c ≠ p) (hcq : c ≠ q)
    (hrp : r ≠ p) (hrq : r ≠ q) (hrc : r ≠ c) :
    f r ∈ D ↔ CrossesOn (univ : Set Circle) p q r c := by
  exact mem_closed_circle_side_iff_crossesOn (hD.preimage f.continuous) hpq
    ((f.continuous.frontier_preimage_subset D).trans hfr) hin hcD hcp hcq hrp hrq hrc

end GraphMinor.GM06
