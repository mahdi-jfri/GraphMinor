module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.SurfaceGraph

/-!
# Boundary arcs between alternating ports

Part IV, Section 7c of the planarity note uses the four boundary arcs between
consecutive ports as a cycle. First split the boundary circle at the ends of
one exterior arc. The two remaining ports lie on opposite open arcs because
they lie in different components after those ends are removed. Splitting once
more at each remaining port gives the four sides.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Topology

private theorem same_component_of_mem_arc {C : Set ℂ} {f : unitInterval → ℂ}
    (hf : Surface.IsArcMap f) (hsub : range f ⊆ C) {b d : ℂ}
    (hb : b ∈ range f) (hd : d ∈ range f)
    (hb0 : b ≠ f 0) (hb1 : b ≠ f 1) (hd0 : d ≠ f 0) (hd1 : d ≠ f 1) :
    connectedComponentIn (C \ {f 0, f 1}) b =
      connectedComponentIn (C \ {f 0, f 1}) d := by
  have mem_open : ∀ {x}, x ∈ range f → x ≠ f 0 → x ≠ f 1 →
      x ∈ f '' Ioo (0 : unitInterval) 1 := by
    rintro x ⟨t, rfl⟩ hx0 hx1
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · exact lt_of_le_of_ne bot_le (fun he => hx0 (congrArg f he.symm))
    · exact lt_of_le_of_ne le_top (fun he => hx1 (congrArg f he))
  have sub_open : f '' Ioo (0 : unitInterval) 1 ⊆ C \ {f 0, f 1} := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨hsub (mem_range_self t), ?_⟩
    rintro (he | he)
    · exact ht.1.ne' (hf.2 he)
    · exact ht.2.ne (hf.2 he)
  exact connectedComponentIn_eq
    ((isPreconnected_Ioo.image f hf.1.continuousOn).subset_connectedComponentIn
      (mem_open hb hb0 hb1) sub_open (mem_open hd hd0 hd1))

/-- Part IV, Section 7c: splitting a circle at the first opposite pair puts
the other two alternating ports on different arcs. -/
theorem exists_opposite_boundary_arcs {C : Set ℂ} (hC : Surface.IsOArc C)
    {a c b d : ℂ} (hcross : Surface.PairsCrossOn C a c b d) :
    ∃ L R : Set ℂ, Surface.IsLineWithEnds L a c ∧
      Surface.IsLineWithEnds R a c ∧ L ∪ R = C ∧ L ∩ R = {a, c} ∧
      b ∈ L ∧ d ∈ R ∧ b ∉ R ∧ d ∉ L := by
  obtain ⟨ha, hb, hc, hd, hac, _, hab, had, hcb, hcd, hcomp⟩ := hcross
  obtain ⟨f, g, hfg, hf0, hf1, hfgC⟩ := hC.exists_arcs ha hc hac
  have hg0 : g 0 = a := hfg.zero.trans hf0
  have hg1 : g 1 = c := hfg.one.trans hf1
  have hfi : Surface.IsLineWithEnds (range f) a c := by
    simpa only [hf0, hf1] using hfg.arc_left.isLineWithEnds
  have hgi : Surface.IsLineWithEnds (range g) a c := by
    simpa only [hg0, hg1] using hfg.arc_right.isLineWithEnds
  have hmeet : range f ∩ range g = {a, c} := by
    simpa only [hf0, hf1] using hfg.inter
  have hnot_same : ∀ (k : unitInterval → ℂ), Surface.IsArcMap k →
      range k ⊆ C → k 0 = a → k 1 = c →
      b ∈ range k → d ∈ range k → False := by
    intro k hk hsub hk0 hk1 hbk hdk
    apply hcomp
    simpa only [hk0, hk1] using same_component_of_mem_arc hk hsub hbk hdk
      (hk0 ▸ hab.symm) (hk1 ▸ hcb.symm) (hk0 ▸ had.symm) (hk1 ▸ hcd.symm)
  have hfsub : range f ⊆ C := hfgC ▸ subset_union_left
  have hgsub : range g ⊆ C := hfgC ▸ subset_union_right
  have hbmem : b ∈ range f ∪ range g := hfgC ▸ hb
  have hdmem : d ∈ range f ∪ range g := hfgC ▸ hd
  rcases hbmem with hbf | hbg
  · have hdnf : d ∉ range f := hnot_same f hfg.arc_left hfsub hf0 hf1 hbf
    have hdg : d ∈ range g := hdmem.resolve_left hdnf
    have hbng : b ∉ range g := fun h =>
      hnot_same g hfg.arc_right hgsub hg0 hg1 h hdg
    exact ⟨range f, range g, hfi, hgi, hfgC, hmeet, hbf, hdg, hbng, hdnf⟩
  · have hdng : d ∉ range g := hnot_same g hfg.arc_right hgsub hg0 hg1 hbg
    have hdf : d ∈ range f := hdmem.resolve_right hdng
    have hbnf : b ∉ range f := fun h =>
      hnot_same f hfg.arc_left hfsub hf0 hf1 h hdf
    refine ⟨range g, range f, hgi, hfi, ?_, ?_, hbg, hdf, hbnf, hdng⟩
    · rw [union_comm, hfgC]
    · rw [inter_comm, hmeet]

/-- Part IV, Section 7c: the four boundary arcs through alternating ports
form a cycle. Adjacent sides meet at their common end and opposite sides
are disjoint. -/
theorem exists_boundary_four_cycle {C : Set ℂ} (hC : Surface.IsOArc C)
    {a c b d : ℂ} (hcross : Surface.PairsCrossOn C a c b d) :
    ∃ P Q R S : Set ℂ,
      Surface.IsLineWithEnds P a b ∧ Surface.IsLineWithEnds Q b c ∧
      Surface.IsLineWithEnds R c d ∧ Surface.IsLineWithEnds S d a ∧
      P ∪ Q ∪ R ∪ S = C ∧
      P ∩ Q = {b} ∧ Q ∩ R = {c} ∧ R ∩ S = {d} ∧ S ∩ P = {a} ∧
      Disjoint P R ∧ Disjoint Q S := by
  obtain ⟨L, U, hL, hU, hcover, hmeet, hbL, hdU, hbU, hdL⟩ :=
    exists_opposite_boundary_arcs hC hcross
  obtain ⟨ha, hb, hc, hd, hac, hbd, hab, had, hcb, hcd, hcomp⟩ := hcross
  obtain ⟨P, Q, hP, hQ, hPQ, hPQmeet⟩ := hL.split hbL hab.symm hcb.symm
  obtain ⟨S, R, hS, hR, hSR, hSRmeet⟩ := hU.split hdU had.symm hcd.symm
  have hpL : P ⊆ L := hPQ ▸ subset_union_left
  have hqL : Q ⊆ L := hPQ ▸ subset_union_right
  have hsU : S ⊆ U := hSR ▸ subset_union_left
  have hrU : R ⊆ U := hSR ▸ subset_union_right
  have haQ : a ∉ Q := fun ha => hab (mem_singleton_iff.mp (hPQmeet ▸ ⟨hP.left_mem, ha⟩))
  have hcP : c ∉ P := fun hc => hcb (mem_singleton_iff.mp (hPQmeet ▸ ⟨hc, hQ.right_mem⟩))
  have haR : a ∉ R := fun ha => had (mem_singleton_iff.mp (hSRmeet ▸ ⟨hS.left_mem, ha⟩))
  have hcS : c ∉ S := fun hc => hcd (mem_singleton_iff.mp (hSRmeet ▸ ⟨hc, hR.right_mem⟩))
  have cross : ∀ {x}, x ∈ L → x ∈ U → x = a ∨ x = c := by
    intro x hx hy
    exact (show x ∈ ({a, c} : Set ℂ) from hmeet ▸ ⟨hx, hy⟩)
  have hQR : Q ∩ R = {c} := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      rcases cross (hqL hx) (hrU hy) with rfl | rfl
      · exact (haQ hx).elim
      · rfl
    · rintro rfl
      exact ⟨hQ.right_mem, hR.right_mem⟩
  have hSP : S ∩ P = {a} := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      rcases cross (hpL hy) (hsU hx) with rfl | rfl
      · rfl
      · exact (hcP hy).elim
    · rintro rfl
      exact ⟨hS.left_mem, hP.left_mem⟩
  have hPR : Disjoint P R := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases cross (hpL hx) (hrU hy) with rfl | rfl
    · exact haR hy
    · exact hcP hx
  have hQS : Disjoint Q S := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases cross (hqL hx) (hsU hy) with rfl | rfl
    · exact haQ hx
    · exact hcS hy
  refine ⟨P, Q, R, S, hP, hQ, hR.symm, hS.symm, ?_, hPQmeet, hQR,
    ?_, hSP, hPR, hQS⟩
  · calc
      P ∪ Q ∪ R ∪ S = (P ∪ Q) ∪ (S ∪ R) := by ac_rfl
      _ = C := by rw [hPQ, hSR, hcover]
  · rw [inter_comm, hSRmeet]

end GraphMinor.LRPlanarity
