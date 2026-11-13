module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18GraphEuler
import Lean.Elab.Tactic.Omega

/-!
# Euler sums of a circle and an arc

An arc has a graph with two vertices and one edge. Split a circle
between two distinct points to obtain a graph with two vertices and
two edges. Subdivision invariance gives the same Euler sums for every
finite graph on these sets, as needed in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- The one-edge graph of a line, used in the Euler calculation of
VIII (18.2), page 286. -/
theorem isGraph_single_line {S : Type*} [TopologicalSpace S] {L : Set S} {u v : S}
    (huv : u ≠ v) (hL : IsLineWithEnds L u v) :
    IsGraph {u, v} {L} ∧ gr {u, v} {L} = L := by
  have hends : ({u, v} : Set S) ⊆ L := by
    rintro x (rfl | rfl)
    · exact hL.left_mem
    · exact hL.right_mem
  refine ⟨⟨(finite_singleton v).insert u, finite_singleton L, ?_, ?_⟩, ?_⟩
  · rintro e rfl
    exact ⟨u, v, huv, hL, inter_eq_right.mpr hends⟩
  · rintro e rfl d rfl hne
    exact (hne rfl).elim
  · simpa only [gr, sUnion_singleton] using union_eq_right.mpr hends

private theorem circle_graph {S : Type} [TopologicalSpace S] [T2Space S]
    {F : Set S} (hF : IsOArc F) :
    ∃ V E, IsGraph V E ∧ gr V E = F ∧ V.ncard = 2 ∧ E.ncard = 2 := by
  classical
  have hneF : F.Nonempty := by
    obtain ⟨φ⟩ := hF
    exact ⟨(φ 1).1, (φ 1).2⟩
  obtain ⟨x, hx⟩ := hneF
  obtain ⟨y, hy, hyx⟩ := hF.exists_ne x
  obtain ⟨a, b, hab, ha0, ha1, hcover⟩ := hF.exists_arcs hx hy hyx.symm
  have la : IsLineWithEnds (range a) x y := ha0 ▸ ha1 ▸ hab.arc_left.isLineWithEnds
  have lb : IsLineWithEnds (range b) x y := by
    have hb0 : b 0 = x := hab.zero.trans ha0
    have hb1 : b 1 = y := hab.one.trans ha1
    exact hb0 ▸ hb1 ▸ hab.arc_right.isLineWithEnds
  have hmeet : range a ∩ range b = {x, y} := by rw [hab.inter, ha0, ha1]
  have hne : range a ≠ range b := by
    intro heq
    let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
    obtain ⟨s, hs⟩ := heq ▸ (mem_range_self t : a t ∈ range a)
    rcases hab.meet t s hs.symm with hh | hh
    · have ht := congrArg Subtype.val hh.1
      norm_num [t] at ht
    · have ht := congrArg Subtype.val hh.1
      norm_num [t] at ht
  have haG := (isGraph_single_line hyx.symm la).1
  have hbG := (isGraph_single_line hyx.symm lb).1
  have hg : IsGraph {x, y} {range a, range b} := by
    refine ⟨haG.fin, (finite_singleton (range b)).insert (range a), ?_, ?_⟩
    · rintro L (rfl | rfl)
      · exact haG.edge _ rfl
      · exact hbG.edge _ rfl
    · rintro L (rfl | rfl) K (rfl | rfl) hLK
      · exact (hLK rfl).elim
      · exact hmeet.subset
      · exact (inter_comm _ _).subset.trans hmeet.subset
      · exact (hLK rfl).elim
  have hgr : gr {x, y} {range a, range b} = F := by
    rw [gr, sUnion_pair, ← hcover]
    exact union_eq_right.mpr ((by
      rintro z (rfl | rfl)
      · exact Or.inl la.left_mem
      · exact Or.inl la.right_mem) : ({x, y} : Set S) ⊆ range a ∪ range b)
  exact ⟨{x, y}, {range a, range b}, hg, hgr, ncard_pair hyx.symm, ncard_pair hne⟩

/-- Any finite graph whose carrier is a circle has Euler sum zero,
as used for type (i) in VIII (18.2), page 286. -/
theorem graph_euler_oArc {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) (hF : IsOArc (gr V E)) :
    (V.ncard : ℤ) - E.ncard = 0 := by
  obtain ⟨W, D, hd, hgr, hW, hD⟩ := circle_graph hF
  have heq := graph_euler_eq_of_carrier_eq hg hd hgr.symm
  rw [hW, hD] at heq
  exact heq

/-- Any finite graph whose carrier is a line has Euler sum one,
as used for types (ii) and (iii) in VIII (18.2), page 286. -/
theorem graph_euler_line {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) {u v : S} (huv : u ≠ v)
    (hL : IsLineWithEnds (gr V E) u v) :
    (V.ncard : ℤ) - E.ncard = 1 := by
  obtain ⟨hd, hgr⟩ := isGraph_single_line huv hL
  have heq := graph_euler_eq_of_carrier_eq hg hd hgr.symm
  rw [ncard_pair huv, ncard_singleton] at heq
  exact heq

end GraphMinor.GM08
