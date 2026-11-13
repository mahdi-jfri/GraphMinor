module

public import GraphMinor.GM04.Painting
import GraphMinor.GM04.NoncrossingMatching
import GraphMinor.GM04.PairingFromEquiv
import GraphMinor.GM06.Section2Dual
import GraphMinor.GM14.DiscSlope

/-!
# Robustness of the noncrossing cell patches

In the proof of IV (9.2), page 254, the patch on a cell consists of all
noncrossing pairings. Choose a minimum-cost matching between the two
prescribed sets of nodes, using a circular coordinate on the cell boundary.
The strict uncrossing inequality rules out crossing edges. The resulting
pairing proves robustness.
-/

public section

namespace GraphMinor.GM04

open Set Surface

universe u w

private noncomputable def boundaryCoord {S : Type u} [TopologicalSpace S]
    {C V : Set S} (φ : Circle ≃ₜ C) (hV : V ⊆ C) : CircleCoord V where
  angle v := circleStdCoord.angle (φ.symm ⟨v, hV v.property⟩)
  injective := by
    intro a b h
    have hf := φ.symm.injective (circleStdCoord.injective h)
    exact Subtype.ext (congrArg (fun z : C ↦ z.val) hf)

private theorem boundaryCoord_crosses {S : Type u} [TopologicalSpace S]
    {C V : Set S} (φ : Circle ≃ₜ C) (hV : V ⊆ C) (a c b d : V) :
    GM06.CrossesOn C a c b d ↔ circleCrosses (boundaryCoord φ hV) a c b d := by
  let f : V → Circle := fun x ↦ φ.symm ⟨x, hV x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : C ↦ z.val) (φ.symm.injective h))
  have hmap (x : V) : GM06.oArcMap φ (f x) = x := by
    change (φ (φ.symm ⟨x, hV x.property⟩)).val = x.val
    rw [φ.apply_symm_apply]
  have h := (GM06.crossesOn_oArcMap_iff φ (a := f a) (c := f c) (b := f b) (d := f d)).trans
    GM06.crossesOn_univ_iff_circleStdCoord
  rw [hmap, hmap, hmap, hmap] at h
  rw [h]
  simp only [circleCrosses, onOpenArc, hf.ne_iff]
  rfl

/-- On a finite set of points of an `O`-arc, equally large disjoint sets can
be paired without crossings. This proves the local matching assertion used
in IV (9.2), page 254. -/
theorem exists_noncrossing_pairing_of_isOArc {S : Type u} [TopologicalSpace S]
    {C V : Set S} (hC : IsOArc C) (hV : V.Finite) (hVC : V ⊆ C)
    {X Y : Set S} (hX : X ⊆ V) (hY : Y ⊆ V) (hcard : X.ncard = Y.ncard)
    (hXY : Disjoint X Y) :
    ∃ δ : (⊤ : SimpleGraph S).Subgraph,
      IsPairing V δ ∧ δ.verts = V ∧ Pairs V δ X Y ∧
      ∀ a c b d, δ.Adj a c → δ.Adj b d → ¬ GM06.CrossesOn C a c b d := by
  classical
  obtain ⟨φ⟩ := hC
  let coord := boundaryCoord φ hVC
  have hbound : ∀ x : V, -Real.pi ≤ coord.angle x ∧ coord.angle x ≤ Real.pi := by
    intro x
    exact ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
  have hspan : Real.pi - -Real.pi < 4 * Real.pi := by linarith [Real.pi_pos]
  let : Fintype X := (hV.subset hX).fintype
  let : Fintype Y := (hV.subset hY).fintype
  let ix : X → V := fun x ↦ ⟨x, hX x.property⟩
  let iy : Y → V := fun y ↦ ⟨y, hY y.property⟩
  have hc : Fintype.card X = Fintype.card Y := by
    simpa only [Set.fintypeCard_eq_ncard] using hcard
  obtain ⟨e, he⟩ := exists_equiv_exchange_le hc
    (fun x y ↦ pairingCost (4 * Real.pi) (coord.angle (ix x)) (coord.angle (iy y)))
  have hnc (x y : X) : ¬ GM06.CrossesOn C x (e x) y (e y) := by
    intro hcr
    have hcr' := (boundaryCoord_crosses φ hVC (ix x) (iy (e x)) (ix y) (iy (e y))).mp hcr
    have hlt := pairingCost_lt_of_circleCrosses coord hbound hspan hcr'
    exact (not_lt_of_ge (he x y)) hlt
  let δ := equivPairing hX hY hXY e
  refine ⟨δ, isPairing_equivPairing hV hX hY hXY e, rfl,
    pairs_equivPairing hV hX hY hXY e, ?_⟩
  rintro a c b d ⟨x, hx⟩ ⟨y, hy⟩
  rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hnc x y
  · intro h
    exact hnc x y h.symm_right
  · intro h
    exact hnc x y h.symm_left
  · intro h
    exact hnc x y h.symm_left.symm_right

namespace LabelledPainting

/-- The cell patches in the proof of Graph Minors IV, (9.2), page 254, are
robust: any two equally large disjoint subsets of the incident nodes have
a noncrossing pairing. -/
theorem cellPatch_isRobust {Ω : Type w} {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) (P : LabelledPainting Ω S)
    {e : Set S} (he : e ∈ P.painting.E) : (P.cellPatch e).IsRobust := by
  have hdisc := (P.painting.edge_cond e he).1
  have hC : IsOArc (subBd (closure e)) := by
    rw [GM14.IsClosedDisc.subBd_eq_discBd hS hdisc]
    exact hdisc.isOArc_discBd
  have hV : P.toRootedHypergraph.ends e |>.Finite :=
    P.toRootedHypergraph.vertexSet_finite.subset
      (fun _ hv ↦ P.toRootedHypergraph.vertex_mem_of_inc hv)
  have hVC : P.toRootedHypergraph.ends e ⊆ subBd (closure e) := by
    intro v hv
    rw [P.ends_eq he, ← P.painting.cell_complement e he] at hv
    exact (P.painting.edge_cond e he).2 hv
  intro X hX Y hY hcard hXY
  obtain ⟨δ, hpair, hverts, hpairs, hnc⟩ :=
    exists_noncrossing_pairing_of_isOArc hC hV hVC hX hY hcard hXY
  exact ⟨δ, ⟨hpair, hverts, hnc⟩, hpair, hpairs⟩

/-- The patchwork associated with a labelled painting is robust, as asserted
in the proof of Graph Minors IV, (9.2), page 254. -/
theorem toPatchwork_isRobust {Ω : Type w} {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) (P : LabelledPainting Ω S) : P.toPatchwork.IsRobust :=
  fun _ he ↦ P.cellPatch_isRobust hS he

end LabelledPainting

end GraphMinor.GM04
