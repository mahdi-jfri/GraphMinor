module

public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section15TrimArc
import GraphMinor.GM07.GoodEdge
import GraphMinor.GM07.Whisker
import GraphMinor.GM11.RadialAccess
import GraphMinor.GM11.Section6
import GraphMinor.Surface.ChartCells

/-!
# A free hole next to an empty boundary interval

At a point of a disc boundary off the drawing, take a small connected
open neighbourhood also off the drawing. It meets the outside of the
disc, where a new small disc can be chosen. Shorten a path between the
two discs to an arc that meets each only at its end. Both the new disc
and the joining arc miss the drawing. This is used when choosing an
unlinked framing in the empty-cuff case of VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- A free point on a disc boundary allows a disjoint free disc joined
to it by an arc off the drawing. This is the hole choice in the
empty-cuff case of VIII (17.2), page 284. -/
theorem exists_free_disc_and_joining_line {S : Type w} [TopologicalSpace S]
    (hS : IsClosedSurface S) (G : Drawing S) {D : Set S}
    (hD : IsClosedDisc D) {p : S} (hp : p ∈ discBd D) (hpoff : p ∉ G.U) :
    ∃ (E J : Set S) (a b : S), IsClosedDisc E ∧ Disjoint D E ∧
      Disjoint E G.U ∧ IsLineWithEnds J a b ∧
      a ∈ discBd D ∧ b ∈ discBd E ∧
      J ∩ (D ∪ E) = {a, b} ∧ Disjoint J G.U := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let N := connectedComponentIn G.Uᶜ p
  have hNopen : IsOpen N := G.isClosed_U.isOpen_compl.connectedComponentIn
  have hpN : p ∈ N := mem_connectedComponentIn hpoff
  have hNsub : N ⊆ G.Uᶜ := connectedComponentIn_subset _ _
  have hNpath : IsPathConnected N := GM11.isPathConnected_of_isOpen hS hNopen
    isPreconnected_connectedComponentIn ⟨p, hpN⟩
  have hpcl : p ∈ closure Dᶜ := by
    have hpfr : p ∈ frontier D := (GM11.IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ hp
    rw [frontier_eq_closure_inter_closure] at hpfr
    exact hpfr.2
  obtain ⟨q, hqN, hqD⟩ := mem_closure_iff.mp hpcl N hNopen hpN
  obtain ⟨E, hE, hqE, hEsub⟩ := GM07.exists_disc_in_open (hS.2.2 q)
    (hNopen.inter hD.isClosed.isOpen_compl) ⟨hqN, hqD⟩
  have hDE : Disjoint D E := disjoint_left.mpr fun x hxD hxE => (hEsub hxE).2 hxD
  obtain ⟨c, hcD, L, hLN, hL, _⟩ := GM07.exists_whisker_line hD.isClosed
    (discBd_subset D hp) hqD (hNpath.joinedIn p hpN q hqN)
  obtain ⟨J, a, b, hJL, haD, hbE, hJ, hends⟩ :=
    exists_subarc_between_closed_sets hL hD.isClosed hE.isClosed hDE hcD hqE.1
  have hdiff : J \ {a, b} ⊆ (D ∪ E)ᶜ := by
    rintro x ⟨hxJ, hxend⟩ hxDE
    exact hxend (hends ▸ ⟨hxJ, hxDE⟩)
  have hfront : ∀ x ∈ J, x ∈ D ∪ E → x ∈ frontier D ∨ x ∈ frontier E := by
    intro x hxJ hxDE
    have hxcl : x ∈ closure (D ∪ E)ᶜ :=
      closure_mono hdiff (hJ.subset_closure_diff hxJ)
    rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure]
    rcases hxDE with hxD | hxE
    · exact .inl ⟨subset_closure hxD,
        closure_mono (show (D ∪ E)ᶜ ⊆ Dᶜ from fun y hy hyD => hy (.inl hyD)) hxcl⟩
    · exact .inr ⟨subset_closure hxE,
        closure_mono (show (D ∪ E)ᶜ ⊆ Eᶜ from fun y hy hyE => hy (.inr hyE)) hxcl⟩
  have haBd : a ∈ discBd D := by
    rcases hfront a hJ.left_mem (.inl haD) with ha | ha
    · exact (GM11.IsClosedDisc.frontier_eq_discBd hS hD) ▸ ha
    · exact False.elim (disjoint_left.mp hDE haD (hE.isClosed.frontier_subset ha))
  have hbBd : b ∈ discBd E := by
    rcases hfront b hJ.right_mem (.inr hbE) with hb | hb
    · exact False.elim (disjoint_left.mp hDE (hD.isClosed.frontier_subset hb) hbE)
    · exact (GM11.IsClosedDisc.frontier_eq_discBd hS hE) ▸ hb
  exact ⟨E, J, a, b, hE, hDE,
    disjoint_left.mpr (fun x hxE hxG => hNsub (hEsub hxE).1 hxG),
    hJ, haBd, hbBd, hends,
    disjoint_left.mpr (fun x hxJ hxG => hNsub (hLN (hJL hxJ)) hxG)⟩

end GraphMinor.GM08
