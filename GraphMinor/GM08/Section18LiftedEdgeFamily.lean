module

public import GraphMinor.GM19.CutDrawing
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18LineLift
import GraphMinor.GM08.Section18CutEdgeLines
import GraphMinor.GM19.Section6Tri

/-!
# One or two lifted edges over each old edge

An uncut edge has one lifted line. A cut edge has the two lines supplied
by its edge-lift maps. Their only common points are lifted vertices.
This constructs the finite edge families used to build and count the
cut dissection in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

private theorem line_inter_preimage_vertices {S Y : Type*} [TopologicalSpace S]
    [TopologicalSpace Y] {ψ : Y → S} {V e : Set S} {L : Set Y} {u v : S} {x y : Y}
    (huv : u ≠ v) (hL : IsLineWithEnds L x y) (hb : BijOn ψ L e)
    (hcap : e ∩ V = {u, v}) (hψx : ψ x = u) (hψy : ψ y = v) :
    x ≠ y ∧ L ∩ ψ ⁻¹' V = {x, y} := by
  have huV : u ∈ V := (hcap.symm.subset (mem_insert u {v})).2
  have hvV : v ∈ V := (hcap.symm.subset (mem_insert_of_mem u (mem_singleton v))).2
  refine ⟨fun heq => huv (hψx.symm.trans ((congrArg ψ heq).trans hψy)), ?_⟩
  ext z
  constructor
  · rintro ⟨hzL, hzV⟩
    have hzends : ψ z ∈ ({u, v} : Set S) := hcap.subset ⟨hb.mapsTo hzL, hzV⟩
    rcases hzends with hzu | hzv
    · exact Or.inl (hb.injOn hzL hL.left_mem (hzu.trans hψx.symm))
    · exact Or.inr (hb.injOn hzL hL.right_mem (hzv.trans hψy.symm))
  · rintro (rfl | rfl)
    · refine ⟨hL.left_mem, ?_⟩
      change ψ _ ∈ V
      rw [hψx]
      exact huV
    · refine ⟨hL.right_mem, ?_⟩
      change ψ _ ∈ V
      rw [hψy]
      exact hvV

open Classical in
/-- Over an edge of the source dissection there is one lifted edge if
it is uncut, and two if it is cut. Their intersections occur only at
lifted vertices. This is the edge-family step of VIII (18.2), page 286. -/
theorem exists_lifted_edge_family {S Y : Type} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space S] (hY : IsSurface Y)
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {D : Set (Set S)} (hDE : D ⊆ E)
    {ψ : Y → S} (hcm : GM19.IsCutMap ψ (⋃₀ D))
    (hlift : ∀ e ∈ D, ∃ r r', GM19.IsEdgeLift ψ (extI (A e)) (GM19.EndFine A D e) r r')
    {e : Set S} (he : e ∈ E) :
    ∃ B : Set (Set Y), B.Finite ∧ B.ncard = (if e ∈ D then 2 else 1) ∧
      (∀ L ∈ B, ∃ x y, x ≠ y ∧ IsLineWithEnds L x y ∧
        L ∩ ψ ⁻¹' V = {x, y} ∧ BijOn ψ L e) ∧
      (∀ L ∈ B, ∀ K ∈ B, L ≠ K → L ∩ K ⊆ ψ ⁻¹' V) ∧
      ψ ⁻¹' (e \ V) ⊆ ⋃₀ B := by
  have : T2Space Y := hY.2.1
  have : CompactSpace Y := hY.1
  have hclosed : IsClosed (⋃₀ D) := (hw.graph.fine.subset hDE).isClosed_sUnion
    (fun L hL => by obtain ⟨u, v, _, hl, _⟩ := hw.graph.edge L (hDE hL); exact hl.isCompact.isClosed)
  obtain ⟨ha, hrange, hcap⟩ := hw.arc e he
  let u := A e 0
  let v := A e 1
  have huv : u ≠ v := fun hh => zero_ne_one (ha.2 hh)
  have hline : IsLineWithEnds e u v := hrange ▸ ha.isLineWithEnds
  have hopen : e \ V = e \ {u, v} := GM19.IsGraphD.diff_eq hw.graph hcap
  by_cases hcut : e ∈ D
  · obtain ⟨r, r', hrlift⟩ := hlift e hcut
    obtain ⟨L, K, hL, hK, hbL, hbK, hLK, hmeet, hcover⟩ := exists_lines_of_edge_lift ha hrlift
    rw [hrange] at hbL hbK hcover
    have h0 : extI (A e) 0 = A e 0 := extI_coe (A e) 0
    have h1 : extI (A e) 1 = A e 1 := extI_coe (A e) 1
    have hψr0 : ψ (r 0) = u := by simpa only [u, h0] using (hrlift.2.2.1 0 (by constructor <;> norm_num)).1
    have hψr1 : ψ (r 1) = v := by simpa only [v, h1] using (hrlift.2.2.1 1 (by constructor <;> norm_num)).1
    have hψr'0 : ψ (r' 0) = u := by simpa only [u, h0] using (hrlift.2.2.1 0 (by constructor <;> norm_num)).2
    have hψr'1 : ψ (r' 1) = v := by simpa only [v, h1] using (hrlift.2.2.1 1 (by constructor <;> norm_num)).2
    obtain ⟨hLne, hLV⟩ := line_inter_preimage_vertices huv hL hbL hcap hψr0 hψr1
    obtain ⟨hKne, hKV⟩ := line_inter_preimage_vertices huv hK hbK hcap hψr'0 hψr'1
    have huV : u ∈ V := (hcap.symm.subset (mem_insert u {v})).2
    have hvV : v ∈ V := (hcap.symm.subset (mem_insert_of_mem u (mem_singleton v))).2
    have hmeetV : L ∩ K ⊆ ψ ⁻¹' V := by
      intro z hz
      change ψ z ∈ V
      rcases hmeet hz with hz | hz
      · exact hz.symm ▸ huV
      · exact hz.symm ▸ hvV
    refine ⟨{L, K}, (finite_singleton K).insert L, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_left hcut, ncard_pair hLK]
    · rintro Z (rfl | rfl)
      · exact ⟨r 0, r 1, hLne, hL, hLV, hbL⟩
      · exact ⟨r' 0, r' 1, hKne, hK, hKV, hbK⟩
    · rintro Z (rfl | rfl) Q (rfl | rfl) hne
      · exact (hne rfl).elim
      · exact hmeetV
      · exact (inter_comm _ _).subset.trans hmeetV
      · exact (hne rfl).elim
    · rw [hopen, sUnion_pair]
      exact hcover
  · have hoff : Disjoint (e \ {u, v}) (⋃₀ D) := by
      apply disjoint_left.mpr
      rintro z ⟨hze, hzn⟩ ⟨L, hL, hzL⟩
      have heL : e ≠ L := fun hh => hcut (hh ▸ hL)
      have hzV : z ∈ V := hw.graph.disj e he L (hDE hL) heL ⟨hze, hzL⟩
      exact hzn (hcap.subset ⟨hze, hzV⟩)
    obtain ⟨x, y, hψx, hψy, hL, hb, _⟩ := exists_line_closure_lift_of_cutMap hcm hclosed hline hoff
    let L := closure (ψ ⁻¹' (e \ {u, v}))
    obtain ⟨hxy, hLV⟩ := line_inter_preimage_vertices huv hL hb hcap hψx hψy
    refine ⟨{L}, finite_singleton L, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_right hcut, ncard_singleton]
    · rintro K rfl
      exact ⟨x, y, hxy, hL, hLV, hb⟩
    · rintro K rfl Q rfl hne
      exact (hne rfl).elim
    · rw [hopen, sUnion_singleton]
      exact subset_closure

end GraphMinor.GM08
