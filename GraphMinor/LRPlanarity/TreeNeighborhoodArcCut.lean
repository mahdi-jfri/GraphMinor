module

public import GraphMinor.Surface.Defs
import GraphMinor.LRPlanarity.TreeNeighborhoodArcExits
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.EdgeLoop

/-!
# The exterior middle of a cotree arc

Part IV, Section 7b of the planarity note removes the two endpoint tails
from a cotree arc. Its intersections with the endpoint polygons are
connected, and each polygon frontier meets it at its designated port.
The last source exit and first target entry are therefore ordered and
are those ports. The intervening closed subarc is exactly what remains
after deleting the neighborhood interior.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface Topology

/-- Part IV, Section 7b: two connected endpoint intersections with single
frontier ports cut an arc into interior tails and one exterior middle.
The neighborhood meets the arc only in the two endpoint polygons. -/
theorem cut_arc_at_polygon_ports {L A B D : Set ℂ} {u v a b : ℂ}
    (hL : IsLineWithEnds L u v) (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) (hu : u ∈ A) (hv : v ∈ B) (hAD : A ⊆ D) (hBD : B ⊆ D)
    (hconnA : IsPreconnected (A ∩ L)) (hconnB : IsPreconnected (B ∩ L))
    (hfrontA : frontier A ∩ L = {a}) (hfrontB : frontier B ∩ L = {b})
    (haD : a ∈ frontier D) (hbD : b ∈ frontier D)
    (hmeet : D ∩ L = (A ∪ B) ∩ L) :
    IsLineWithEnds (L \ interior D) a b ∧ (L \ interior D) ∩ D = {a,b} := by
  obtain ⟨f, hf, hrange, hzero, hone⟩ := hL.exists_arc
  have hzeroA : f 0 ∈ A := hzero.symm ▸ hu
  have honeB : f 1 ∈ B := hone.symm ▸ hv
  have honeA : f 1 ∉ A := fun h => disjoint_left.mp hAB h honeB
  have hzeroB : f 0 ∉ B := fun h => disjoint_left.mp hAB hzeroA h
  obtain ⟨s, hs1, hsfront, hlast⟩ := exists_last_closed_set_exit hf.1 hA hzeroA honeA
  obtain ⟨t, ht0, htfront, hfirst⟩ := exists_first_closed_set_entry hf.1 hB hzeroB honeB
  have hmemL : ∀ r, f r ∈ L := fun r => hrange ▸ mem_range_self r
  have hfs : f s = a := by
    have hm : f s ∈ frontier A ∩ L := ⟨hsfront, hmemL s⟩
    rw [hfrontA] at hm
    exact hm
  have hft : f t = b := by
    have hm : f t ∈ frontier B ∩ L := ⟨htfront, hmemL t⟩
    rw [hfrontB] at hm
    exact hm
  have hsA : f s ∈ A := hA.closure_eq ▸ frontier_subset_closure hsfront
  have htB : f t ∈ B := hB.closure_eq ▸ frontier_subset_closure htfront
  have hemb : IsEmbedding f := (hf.1.isClosedEmbedding hf.2).isEmbedding
  have hpreA : IsPreconnected (f ⁻¹' A) := by
    apply hemb.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_inter_range, hrange]
    exact hconnA
  have hpreB : IsPreconnected (f ⁻¹' B) := by
    apply hemb.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_inter_range, hrange]
    exact hconnB
  have hst : s < t := by
    apply lt_of_not_ge
    intro hts
    have htA := hpreA.ordConnected.out hzeroA hsA ⟨t.2.1, hts⟩
    exact disjoint_left.mp hAB htA htB
  have hleft : ∀ r, r < s → f r ∈ interior D := by
    intro r hrs
    have hrA : f r ∈ A := hpreA.ordConnected.out hzeroA hsA ⟨r.2.1, hrs.le⟩
    have hnotfront : f r ∉ frontier A := by
      intro hm
      have he : f r = a := by
        have h : f r ∈ frontier A ∩ L := ⟨hm,hmemL r⟩
        rw [hfrontA] at h
        exact h
      exact hrs.ne (hf.2 (he.trans hfs.symm))
    apply interior_mono hAD
    rw [← self_sdiff_frontier]
    exact ⟨hrA, hnotfront⟩
  have hright : ∀ r, t < r → f r ∈ interior D := by
    intro r htr
    have hrB : f r ∈ B := hpreB.ordConnected.out htB honeB ⟨htr.le, r.2.2⟩
    have hnotfront : f r ∉ frontier B := by
      intro hm
      have he : f r = b := by
        have h : f r ∈ frontier B ∩ L := ⟨hm,hmemL r⟩
        rw [hfrontB] at h
        exact h
      exact htr.ne' (hf.2 (he.trans hft.symm))
    apply interior_mono hBD
    rw [← self_sdiff_frontier]
    exact ⟨hrB, hnotfront⟩
  have hnotmid : ∀ r ∈ Icc s t, f r ∉ interior D := by
    intro r hr hi
    by_cases hrs : r = s
    · exact disjoint_left.mp disjoint_interior_frontier hi (hrs.symm ▸ hfs.symm ▸ haD)
    by_cases hrt : r = t
    · exact disjoint_left.mp disjoint_interior_frontier hi (hrt.symm ▸ hft.symm ▸ hbD)
    have hrD : f r ∈ D ∩ L := ⟨interior_subset hi, hmemL r⟩
    have hrAB : f r ∈ A ∪ B := (hmeet ▸ hrD).1
    exact hrAB.elim (hlast r (lt_of_le_of_ne hr.1 (Ne.symm hrs)))
      (hfirst r (lt_of_le_of_ne hr.2 hrt))
  have hmiddle : L \ interior D = f '' Icc s t := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨r, rfl⟩ := hrange.symm ▸ hx.1
      refine ⟨r, ⟨le_of_not_gt (fun hrs => hx.2 (hleft r hrs)),
        le_of_not_gt (fun htr => hx.2 (hright r htr))⟩, rfl⟩
    · rintro x ⟨r, hr, rfl⟩
      exact ⟨hmemL r, hnotmid r hr⟩
  have hline := (hf.sub hst.ne).isLineWithEnds
  rw [range_subArc f hst.le, subArc_zero, subArc_one, hfs, hft] at hline
  refine ⟨hmiddle.symm ▸ hline, ?_⟩
  rw [hmiddle]
  apply Subset.antisymm
  · rintro x ⟨⟨r, hr, rfl⟩, hrD⟩
    have hrDL : f r ∈ D ∩ L := ⟨hrD, hmemL r⟩
    rw [hmeet] at hrDL
    have hrAB : f r ∈ A ∪ B := hrDL.1
    rcases hrAB with hrA | hrB
    · have hrs : r = s := le_antisymm (le_of_not_gt (fun hsr => hlast r hsr hrA)) hr.1
      exact Or.inl ((congrArg f hrs).trans hfs)
    · have hrt : r = t := le_antisymm hr.2 (le_of_not_gt (fun hrt => hfirst r hrt hrB))
      exact Or.inr ((congrArg f hrt).trans hft)
  · intro x hx
    rcases hx with hxa | hxb
    · subst x
      exact ⟨⟨s, ⟨le_rfl,hst.le⟩, hfs⟩, hfs ▸ hAD hsA⟩
    · subst x
      exact ⟨⟨t, ⟨hst.le,le_rfl⟩, hft⟩, hft ▸ hBD htB⟩

end GraphMinor.LRPlanarity
