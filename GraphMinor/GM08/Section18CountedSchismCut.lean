module

public import GraphMinor.GM07.CutStages
public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM19.CutDrawing3
import GraphMinor.GM08.Section18GraphDegreeSum
import Mathlib.Data.Set.Card.Arithmetic
import GraphMinor.GM08.Section18CountedWordCut
import GraphMinor.GM08.Section18SchismGraph
import GraphMinor.GM08.Section18SchismFrame
import GraphMinor.GM08.Section18SchismBoundary
import GraphMinor.GM08.Section18CutBoundary

/-!
# A schism cut with all vertex fibre counts

Refine the finite graph of the schism inside a dissection, and cut its
edges in the word presentation. Keep the refined cutting graph and the
proved degree formula for every vertex fibre. This is the counted cut
construction in the Euler proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM19

universe u

open Classical in
private theorem counted_cut_of_line_frame {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {N : Set S} {𝓔 𝓐 𝓛 : Set (Set S)}
    (hN : N.Finite) (h𝓔 : 𝓔.Finite)
    (hline : ∀ L ∈ 𝓔, ∃ a b, a ≠ b ∧ IsLineWithEnds L a b ∧ L ∩ N = {a, b})
    (hdisj : ∀ L ∈ 𝓔, ∀ L' ∈ 𝓔, L ≠ L' → L ∩ L' ⊆ N)
    (hbd : ∀ L ∈ 𝓔, L ∩ bd S ⊆ N) (hNs : N ⊆ ⋃₀ 𝓔)
    (hF : IsCutFrame S 𝓐 𝓛) (hc : bd S ∪ ⋃₀ 𝓔 = ⋃₀ 𝓐 ∪ ⋃₀ 𝓛) :
    ∃ (V : Set S) (D : Set (Set S)) (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsGraph V D ∧ V ⊆ ⋃₀ D ∧ gr V D = ⋃₀ 𝓔 ∧ N ⊆ V ∧
      IsSurface Y ∧ GM19.IsCutMap ψ (⋃₀ 𝓔) ∧
      ∀ v ∈ V, (ψ ⁻¹' {v}).ncard =
        {e ∈ D | v ∈ e}.ncard + if v ∈ bd S then 1 else 0 := by
  have : T2Space S := hS.2.1
  classical
  obtain ⟨V₀, E₀, hNV, hg, hV₀, hU, h𝓔E⟩ := exists_graph_of_lines hS hN h𝓔 hline hdisj hbd
    (hNs.trans subset_union_right)
  obtain ⟨V, E, 𝓕, hd, hVV, hEE⟩ := exists_dissection_lines hS hg hV₀ hF (hU.trans hc)
  obtain ⟨W, f, A, lab, hw, hdn⟩ := exists_word_edges hS hd
  have hLg : ∀ L ∈ 𝓔, L ⊆ gr V E := fun L hL ↦
    (subset_sUnion_of_mem (h𝓔E hL)).trans hEE
  have hchain : ∀ L ∈ 𝓔, ∃ u v, u ≠ v ∧ IsLineWithEnds L u v ∧ L ∩ N = {u, v} ∧ u ∈ V ∧ v ∈ V := fun L hL ↦ by
    obtain ⟨u, v, huv, hl, hi⟩ := hline L hL
    have hu : u ∈ L ∩ N := hi ▸ mem_insert _ _
    have hv : v ∈ L ∩ N := hi ▸ mem_insert_of_mem _ rfl
    exact ⟨u, v, huv, hl, hi, hVV (hNV hu.2), hVV (hNV hv.2)⟩
  let D : Set (Set S) := {e ∈ E | ∃ L ∈ 𝓔, e ⊆ L}
  have hDE : D ⊆ E := fun e he ↦ he.1
  have hmemD : ∀ L ∈ 𝓔, ∀ x ∈ L, ∃ e ∈ D, x ∈ e ∧ e ⊆ L := fun L hL x hx ↦ by
    obtain ⟨u, v, huv, hl, -, hu, hv⟩ := hchain L hL
    obtain ⟨ι, m, t, ss, ε, -, -, himg, -, -, -, -, -, -, -, hch, -, hun⟩ :=
      exists_chain_of_line hw huv hl hu hv (hLg L hL)
    obtain ⟨_, ⟨p, hp, rfl⟩, hxp⟩ := hun.symm ▸ hx
    have hsub : ss p ⊆ L := fun z hz ↦ hun ▸ ⟨ss p, ⟨p, hp, rfl⟩, hz⟩
    exact ⟨ss p, ⟨(hch p hp).1, L, hL, hsub⟩, hxp, hsub⟩
  have hUD : ⋃₀ D = ⋃₀ 𝓔 := by
    apply subset_antisymm
    · rintro x ⟨e, ⟨-, L, hL, heL⟩, hx⟩
      exact ⟨L, hL, heL hx⟩
    · rintro x ⟨L, hL, hx⟩
      obtain ⟨e, he, hxe, -⟩ := hmemD L hL x hx
      exact ⟨e, he, hxe⟩
  have hmid : ∀ e ∈ D, edgeMid A e ∉ bd S := by
    rintro e ⟨heE, L, hL, heL⟩ hb
    have hmem : edgeMid A e ∈ L ∩ bd S := ⟨heL (hw.extI_mem heE _), hb⟩
    exact hw.extI_notMem heE (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num) (hVV (hNV (hbd L hL hmem)))
  obtain ⟨Y, tY, _, ψ, hY, hcut, _, hcount, _⟩ := exists_counted_word_cut hw hS hdn hDE hmid
  let C : Set S := V ∩ ⋃₀ D
  have hgraph : IsGraph C D := by
    refine ⟨hw.graph.fin.subset inter_subset_left, hw.graph.fine.subset hDE, ?_, ?_⟩
    · intro e he
      obtain ⟨a, b, hab, hl, hcap⟩ := hw.graph.edge e (hDE he)
      have heD : e ⊆ ⋃₀ D := subset_sUnion_of_mem he
      have hcap' : e ∩ C = e ∩ V := by
        ext x
        exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, heD hx.1⟩⟩
      exact ⟨a, b, hab, hl, hcap'.trans hcap⟩
    · intro e he d hd hne x hx
      exact ⟨hw.graph.disj e (hDE he) d (hDE hd) hne hx, ⟨e, he, hx.1⟩⟩
  have hCsub : C ⊆ ⋃₀ D := inter_subset_right
  have hgr : gr C D = ⋃₀ 𝓔 := (union_eq_right.mpr hCsub).trans hUD
  have hNC : N ⊆ C := fun x hx => ⟨hVV (hNV hx), hUD.symm ▸ hNs hx⟩
  refine ⟨C, D, Y, tY, ψ, hgraph, hCsub, hgr, hNC, hY, hUD ▸ hcut, ?_⟩
  exact fun v hv => hcount v hv

private theorem ncard_preimage_eq_sum {X Y : Type*} (ψ : Y → X) {V : Set X}
    (hV : V.Finite) (hfin : ∀ v ∈ V, (ψ ⁻¹' {v}).Finite) :
    (ψ ⁻¹' V).ncard = ∑ v ∈ hV.toFinset, (ψ ⁻¹' {v}).ncard := by
  classical
  have heq : ψ ⁻¹' V = ⋃ v ∈ V, ψ ⁻¹' {v} := by
    ext y
    simp
  have hdis : V.PairwiseDisjoint (fun v => ψ ⁻¹' {v}) := by
    intro v hv w hw hne
    exact disjoint_left.mpr (fun y hy hy' => hne (hy.symm.trans hy'))
  rw [heq, hV.ncard_biUnion hfin hdis, finsum_mem_eq_finite_toFinset_sum _ hV]

open Classical in
/-- Every schism has a finite graph subdivision and a cut with the exact
vertex fibre counts needed by VIII (18.2), page 286. The cut-degree term
includes auxiliary subdivision vertices, and boundary contacts contribute
one further lift. -/
theorem exists_counted_cut_of_schism {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ (V : Set S) (E : Set (Set S)) (Y : Type u) (_ : TopologicalSpace Y) (ψ : Y → S),
      IsGraph V E ∧ V ⊆ ⋃₀ E ∧ gr V E = F ∧ F ∩ bd S ⊆ V ∧
      GM07.IsCutAlongSet F ψ ∧ GM19.IsCutMap ψ F ∧
      (∀ v ∈ V, (ψ ⁻¹' {v}).ncard =
        {e ∈ E | v ∈ e}.ncard + if v ∈ bd S then 1 else 0) ∧
      (ψ ⁻¹' V).ncard = 2 * E.ncard + (F ∩ bd S).ncard := by
  obtain ⟨N, D, hg, hno, hgr, hmarks⟩ := exists_graph_of_schism hS hF
  obtain ⟨𝓐, 𝓛, hframe, hcover⟩ := exists_cutFrame_of_schism hS hF
  have hDunion : ⋃₀ D = F := (union_eq_right.mpr hno).symm.trans hgr
  obtain ⟨V, E, Y, tY, ψ, hgraph, hV, hgraphF, hNV, hY, hcut, hcount⟩ :=
    counted_cut_of_line_frame hS hg.fin hg.fine hg.edge hg.disj
      (fun L hL x hx => hmarks ⟨hDunion ▸ (mem_sUnion.mpr ⟨L, hL, hx.1⟩), hx.2⟩)
      hno hframe (by rwa [hDunion])
  let := tY
  have hcutF : GM19.IsCutMap ψ F := hDunion ▸ hcut
  have hgrF : gr V E = F := hgraphF.trans hDunion
  have hVbd : V ∩ bd S = F ∩ bd S := by
    ext x
    constructor
    · rintro ⟨hxV, hxbd⟩
      exact ⟨hgrF ▸ (Or.inl hxV : x ∈ gr V E), hxbd⟩
    · intro hx
      exact ⟨hNV (hmarks hx), hx.2⟩
  refine ⟨V, E, Y, tY, ψ, hgraph, hV, hgrF, hmarks.trans hNV,
    isCutAlongSet_of_cutMap hS hY (isClosed_of_isSchism hS hF) hcutF, hcutF, hcount, ?_⟩
  rw [ncard_preimage_eq_sum ψ hgraph.fin (fun v _ => hcutF.2.2.2.1 v)]
  have hsum : (∑ v ∈ hgraph.fin.toFinset, (ψ ⁻¹' {v}).ncard) =
      ∑ v ∈ hgraph.fin.toFinset,
        ({e ∈ E | v ∈ e}.ncard + if v ∈ bd S then 1 else 0) := by
    exact Finset.sum_congr rfl (fun v hv => hcount v (hgraph.fin.mem_toFinset.mp hv))
  rw [hsum, Finset.sum_add_distrib, graph_sum_degrees hgraph]
  congr 1
  rw [← Finset.card_filter, ← ncard_coe_finset, ← hVbd]
  congr 1
  ext x
  simp only [Finset.mem_coe, Finset.mem_filter, hgraph.fin.mem_toFinset, mem_inter_iff]

end GraphMinor.GM08
