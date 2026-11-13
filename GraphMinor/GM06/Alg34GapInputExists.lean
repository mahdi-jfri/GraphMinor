module

public import GraphMinor.GM06.Alg34GapInputRep
public import GraphMinor.GM06.Alg34GapOrderExists
public import GraphMinor.GM06.Section3Reduction
import GraphMinor.GM06.Alg34InputExists
import GraphMinor.GM06.Alg34GapRegions
import GraphMinor.GM11.Regions

/-!
# Every proper disc instance has augmented gap incidence input

Start with finite vertex, edge, and region labels. Replace the cuff
list by the complete ordered vertex-and-gap construction. A gap point
avoids the proper drawing and hence belongs to a region, whose supplied
finite label records that gap incidence. All selections occur inside
this existence proof in Prop. The input format and RAM programs read
only the resulting plain finite lists.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute GM11

universe u
variable {S : Type u} [TopologicalSpace S]

/-- Every proper disc drawing and division of its vertices admits the
plain augmented input and its exact geometric interpretation for VI (3.4).
The proof supplies representation witnesses, not an executable geometric encoder. -/
theorem alg34_exists_gap_input_rep (hS : IsClosedDiscSpace S) (G : Drawing S)
    (hG : G.IsProper) (Δ : Set (Set S)) (hΔ : IsDivision Δ)
    (hsub : divisionUnion Δ ⊆ G.V) :
    ∃ X : GM06GapInput, Nonempty (GM06GapInputRep X G Δ) := by
  classical
  obtain ⟨x, ⟨h⟩⟩ := alg34_exists_drawing_rep hS G hG Δ hΔ hsub
  let v : Fin x.n ↪ S := ⟨fun a => (h.vertex a).val, Subtype.val_injective.comp h.vertex.injective⟩
  have hrange : Set.range v = G.V := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      exact (h.vertex a).property
    · intro hp
      obtain ⟨a, ha⟩ := h.vertex.surjective ⟨p, hp⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨L, hnd, hmem, segs, q, hsegs, hinj, hcover, hpoint, hord, hpg, hgg⟩ :=
    alg34_exists_cuff_gap_order hS.isOArc_bd v
  rw [hrange] at hsegs hcover
  have hconn : IsConnected (bd S) := isConnected_of_isOArc hS.isOArc_bd
  have hcs : cuffs S = {bd S} := by
    ext C
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hconn.2.connectedComponentIn hp
    · rintro rfl
      obtain ⟨p, hp⟩ := hconn.1
      exact ⟨p, hp, hconn.2.connectedComponentIn hp⟩
  have hc : bd S ∈ cuffs S := hcs.symm ▸ mem_singleton _
  have hc_eq : ∀ C : cuffs S, C.val = bd S := by
    intro C
    exact mem_singleton_iff.mp (hcs ▸ C.property)
  let ce : Fin 1 ≃ cuffs S := Equiv.ofBijective (fun _ => ⟨bd S, hc⟩)
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun C => ⟨0, Subtype.ext (hc_eq C).symm⟩⟩
  let y : GM06DrawingData := {x with cuffs := [L]}
  let hy : GM06DrawingRep y G Δ := {
    vertex := h.vertex
    edge := h.edge
    region := h.region
    ends := h.ends
    boundary := h.boundary
    cuff := ce
    cuff_vertices := by
      intro i
      have hi0 : i.val = 0 := by
        have hip := i.isLt
        change i.val < 1 at hip
        omega
      have hi : i = 0 := Fin.ext hi0
      subst i
      change (fun a => (h.vertex a).val) '' GM06DrawingData.block L = G.V ∩ bd S
      ext p
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨(h.vertex a).property, (hmem a).mp ha⟩
      · intro hp
        obtain ⟨a, ha⟩ := h.vertex.surjective ⟨p, hp.1⟩
        have ha' : (h.vertex a).val = p := congrArg Subtype.val ha
        refine ⟨a, (hmem a).mpr ?_, ha'⟩
        change (h.vertex a).val ∈ bd S
        rw [ha']
        exact hp.2
    cuff_nodup := by
      intro K hK
      exact (List.mem_singleton.mp hK) ▸ hnd
    order := by
      intro a b i j
      simpa only [GM06DrawingData.crosses, y, List.any_cons, List.any_nil, Bool.or_false,
        hcs, mem_singleton_iff, exists_eq_left, v, Function.Embedding.coeFn_mk] using hord a b i j
    division := h.division }
  have hg : ∀ i : Fin L.length, ∃ a : Fin x.regions.length,
      ((h.region a).val ∩ segs i).Nonempty := by
    intro i
    have hn : q i ∉ G.U := (GM06DrawingRep.gap_subset_complement hG (hsegs i) (hpoint i)).2
    obtain ⟨r, hr, hqr⟩ := exists_region_of_notMem hn
    obtain ⟨a, ha⟩ := h.region.surjective ⟨r, hr⟩
    exact ⟨a, q i, (congrArg Subtype.val ha).symm ▸ hqr, hpoint i⟩
  choose g hg using hg
  let X : GM06GapInput := ⟨y, [List.ofFn g]⟩
  refine ⟨X, ⟨{ drawing := hy, gap_count := rfl, gap := ?_ }⟩⟩
  intro c
  have hcval : c.val = 0 := by
    have hcp := c.isLt
    change c.val < 1 at hcp
    omega
  have hc0 : c = 0 := Fin.ext hcval
  subst c
  refine {
    region := g
    region_list := rfl
    segment := segs
    segment_mem := ?_
    segment_injective := hinj
    segment_cover := ?_
    region_meets := hg
    point := q
    point_mem := hpoint
    primal_gap_order := ?_
    gap_order := ?_ }
  · change ∀ i, segs i ∈ segmentsOf (bd S) (G.V ∩ bd S)
    exact hsegs
  · change ∀ seg ∈ segmentsOf (bd S) (G.V ∩ bd S), ∃ i, segs i = seg
    exact hcover
  · change ∀ a b i j, GM06DrawingData.pairCrossesGaps L a b i j = true ↔
      CrossesOn (bd S) (v a) (v b) (q i) (q j)
    exact hpg
  · change ∀ a b i j : Fin L.length,
      GM06DrawingData.crossesOnList (List.finRange L.length) a b i j = true ↔
        CrossesOn (bd S) (q a) (q b) (q i) (q j)
    exact hgg

/-- Every intended disc instance has some supplied augmented finite input. -/
theorem DiscDivInstance.exists_gap_input_rep (I : DiscDivInstance.{u}) :
    ∃ X : GM06GapInput, Nonempty (GM06GapInputRep X I.G I.Δ) :=
  alg34_exists_gap_input_rep I.hDisc I.G I.hProper I.Δ I.hΔ
    (I.hΔ_eq.subset.trans inter_subset_left)

end GraphMinor.GM06
