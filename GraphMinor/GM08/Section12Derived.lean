module

public import GraphMinor.GM08.Section11Cells
import GraphMinor.GM08.Section12Thickening
import GraphMinor.GM08.Section12FoundationPainting
import GraphMinor.GM08.Section12PieceLabel
import GraphMinor.GM08.Section12PortraitLabels
import GraphMinor.GM08.Section12RootOrder
import GraphMinor.GM08.Section9GraftDrawing
import GraphMinor.GM08.Section9Foundation

/-!
# Existence of the derived portrait

Choose the smaller rooted graph for each foundation ring. Thicken the
remaining edges and form the painting from all these discs. Order the
outer boundary by the original root list, and order each ring cell by
its smaller rooted graph. The other cells get arbitrary orders of their
ends and the label `*`. This carries out the construction on VIII,
page 272, used in the disc induction of Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v w

/-- The construction on VIII, page 272, gives a derived portrait for
every cellular graft drawing and foundation. Section 12 applies the
portrait theorems to this constructed object. The union includes the
nodes. The displayed union on page 272 omits isolated vertices (see the
corrections on page 272 in `corrections/GM08.md`). -/
theorem exists_derived_portrait_via {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (hS : IsClosedDisc (univ : Set S))
    {k : ℕ} (X : RootedGraph α β) (hX : X ∈ discRootedClassA S k)
    (hk : X.index = k) (gd : GraftDrawing X.G X.toGraft.T S)
    (hcell : IsCellularDrawing gd.drawing)
    {t : ℕ} {F : Fin t → Set S} (hF : IsFoundation gd.drawing univ F) :
    ∃ P : QPortrait (QKElem α β S ((k : ℤ) - 1)) S,
      IsDerivedPortraitVia X gd F P := by
  classical
  have : T2Space S := t2Space_of_univ hS
  have : Nonempty S := by
    obtain ⟨x, -⟩ := hS.nonempty_discInt
    exact ⟨x⟩
  have hbcard : (gd.drawing.V ∩ discBd (univ : Set S)).ncard = k := by
    rw [GM06.discBd_univ, graftDrawing_boundary_ncard gd]
    change X.toGraft.index = k
    rw [graft_index_eq_of_nodup X hX.2.2, hk]
  have hex : ∀ i, ∃ (R : RootedGraph α β) (μ : List S),
      R ∈ discRootedClassA S ((k : ℤ) - 1) ∧ IsRingGraph X gd (F i) R μ := by
    intro i
    apply exists_ring_graph_label hS X gd (hF.isOArc i) (hF.isNormal i)
    rw [← hbcard]
    exact hF.ring_card_lt_boundary_card i
  choose R μring hR hRing using hex
  obtain ⟨C, hC, hCC⟩ := exists_edge_thickening hS gd.drawing gd.isProper hcell hF
  let B : Fin t ⊕ ringEdges gd.drawing F → Set S :=
    Sum.elim (fun i => F i ∪ insideSet (F i)) C
  let c := fun i => B i \ ringNodes gd.drawing F
  obtain ⟨Pt, hN, hU, hcells, hcl, hinj, hbd⟩ := exists_foundation_painting hS gd.drawing hF C hC hCC
  have hEndsFin : ∀ i : ringEdges gd.drawing F,
      (C i ∩ ringNodes gd.drawing F).Finite := fun i =>
    (gd.drawing.finite_V.subset (sep_subset _ _)).subset inter_subset_right
  let μedge := fun i => (hEndsFin i).toFinset.toList
  have hEnds : ∀ i, {x | x ∈ μedge i} = C i ∩ ringNodes gd.drawing F := by
    intro i
    ext x
    simp [μedge]
  let μ := Sum.elim μring μedge
  let φ : Fin t ⊕ ringEdges gd.drawing F → QKElem α β S ((k : ℤ) - 1) :=
    Sum.elim (fun i => some ⟨R i, hR i⟩) (fun _ => none)
  let αroot := X.τ.map gd.iso.fv
  have hαn : αroot.Nodup := (List.nodup_map_iff_inj_on hX.2.2).mpr (by
    intro x hx y hy heq
    exact gd.iso.fv_injOn (X.τ_subset _ hx) (X.τ_subset _ hy) heq)
  have hαset : {x | x ∈ αroot} = Pt.U ∩ bd S := by
    rw [hbd, graftDrawing_boundary_eq gd]
    ext x
    simp only [αroot, List.mem_map, mem_ofPred_eq, mem_image]
    rfl
  have hμn : ∀ i, (μ i).Nodup := by
    intro i
    cases i with
    | inl i => exact (hRing i).2.2.2.1
    | inr i => exact Finset.nodup_toList _
  have hμset : ∀ i, {x | x ∈ μ i} = closure (c i) \ c i := by
    intro i
    rw [hcl]
    have hs : B i \ c i = B i ∩ ringNodes gd.drawing F := by
      ext x
      simp only [c, mem_sdiff, mem_inter_iff]
      tauto
    rw [hs]
    cases i with
    | inl i =>
      exact (hRing i).2.2.2.2.1.trans (hF.ring_inter_nodes hS i).symm
    | inr i => exact hEnds i
  obtain ⟨P, hPt, hα, hμ, hφ⟩ := exists_portrait_of_indexed_cells Pt c hcells hinj
    αroot hαn hαset μ hμn hμset φ none
  let Dedge : Set S → Set S := fun e =>
    if he : e ∈ ringEdges gd.drawing F then C ⟨e, he⟩ else ∅
  have hDe : ∀ e (he : e ∈ ringEdges gd.drawing F), Dedge e = C ⟨e, he⟩ := by
    intro e he
    simp only [Dedge, dite_eq_left he]
  refine ⟨P, hX, hk, hcell, hF, ?_, ?_, μring, R, hR, Dedge, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hα]
    exact List.length_map _
  · intro n hn hn'
    simp only [hα, αroot, List.getElem_map]
    exact (gd.iso.fv_of_mem (X.τ_subset _ (List.getElem_mem hn))).symm
  · intro i
    obtain ⟨hle, hV, hE, hn, hset, hlen, hroot⟩ := hRing i
    exact ⟨hn, hset, hle, hV, hE, hlen, hroot⟩
  · intro e he
    rw [hDe e he]
    refine ⟨(hC ⟨e, he⟩).1, subset_closure.trans (hC ⟨e, he⟩).2.1,
      (hC ⟨e, he⟩).2.2.1, (hC ⟨e, he⟩).2.2.2.1, ?_⟩
    intro e' he' hne
    rw [hDe e' he']
    exact hCC _ _ (fun h => hne (congrArg (fun z : ringEdges gd.drawing F => z.1) h))
  · rw [hPt]
    exact hN
  · change P.painting.U = (ringNodes gd.drawing F ∪ ⋃ i, F i ∪ insideSet (F i)) ∪
        ⋃ e ∈ ringEdges gd.drawing F, Dedge e
    have heU : (⋃ i, C i) = ⋃ e ∈ ringEdges gd.drawing F, Dedge e := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨⟨e, he⟩, hx⟩
        exact ⟨e, he, (hDe e he).symm ▸ hx⟩
      · rintro ⟨e, he, hx⟩
        exact ⟨⟨e, he⟩, (hDe e he) ▸ hx⟩
    rw [hPt, hU, iUnion_sum]
    change ringNodes gd.drawing F ∪ ((⋃ i, F i ∪ insideSet (F i)) ∪ ⋃ i, C i) = _
    rw [← union_assoc, heU]
  · change P.painting.cells = (range fun i => (F i ∪ insideSet (F i)) \ ringNodes gd.drawing F) ∪
        ((fun e => Dedge e \ ringNodes gd.drawing F) '' ringEdges gd.drawing F)
    rw [hPt, hcells]
    ext e
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl i => exact .inl ⟨i, rfl⟩
      | inr i =>
        apply Or.inr
        refine ⟨i.1, i.2, ?_⟩
        change Dedge i.1 \ ringNodes gd.drawing F = C i \ ringNodes gd.drawing F
        rw [hDe i.1 i.2]
    · rintro (⟨i, rfl⟩ | ⟨e, he, rfl⟩)
      · exact ⟨Sum.inl i, rfl⟩
      · refine ⟨Sum.inr ⟨e, he⟩, ?_⟩
        change C ⟨e, he⟩ \ ringNodes gd.drawing F = Dedge e \ ringNodes gd.drawing F
        rw [hDe e he]
  · intro i
    exact ⟨hcl (Sum.inl i), hμ (Sum.inl i), hφ (Sum.inl i)⟩
  · intro e he
    rw [hDe e he]
    exact ⟨hcl (Sum.inr ⟨e, he⟩), hφ (Sum.inr ⟨e, he⟩)⟩

end GraphMinor.GM08
