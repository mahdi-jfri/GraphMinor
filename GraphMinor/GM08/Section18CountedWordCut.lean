module

public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.CutEdges
public import GraphMinor.GM19.CutDrawing
import GraphMinor.GM08.Section18WordVertexDegree
import GraphMinor.GM08.Section18WordVertexSum

/-!
# A word cut with its vertex counts

Keep the word presentation in the finite-edge cut construction.
The cut has finite fibres, the cut graph lifts to the boundary, and its
vertex fibres have the degree formula proved from the side ends.
This supplies the counted cut needed by VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology Function GraphMinor.Surface GraphMinor.GM19

universe u

open Classical in
/-- Construct the word cut with its exact vertex fibre counts, for the
Euler calculation of VIII (18.2), page 286. The construction uses the
same polygon cutting map as the finite-line cut. -/
theorem exists_counted_word_cut {S : Type u} [TopologicalSpace S] [T2Space S]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (h : WordEdges W f V E A lab) (hS : IsSurface S) (hne : (Dsk W).Nonempty)
    {D : Set (Set S)} (hD : D ⊆ E) (hmid : ∀ e ∈ D, edgeMid A e ∉ bd S) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S),
      IsSurface Y ∧ GM19.IsCutMap ψ (⋃₀ D) ∧
      (∀ e ∈ D, ∃ r r', GM19.IsEdgeLift ψ (extI (A e)) (GM19.EndFine A D e) r r') ∧
      (∀ v ∈ V ∩ ⋃₀ D, (ψ ⁻¹' {v}).ncard =
        {e ∈ D | v ∈ e}.ncard + if v ∈ bd S then 1 else 0) ∧
      (⋃₀ D ∩ bd S ⊆ V →
        (ψ ⁻¹' (V ∩ ⋃₀ D)).ncard = 2 * D.ncard + (⋃₀ D ∩ bd S).ncard) := by
  classical
  have hsd : ∀ e ∈ D, ∃ (i p j q : ℕ) (e₁ e₂ : Bool), EdgeSides W (lab e) i p j q e₁ e₂ := fun e he ↦ by
    obtain ⟨i, p, j, q, e₁, e₂, h1, h2, h3⟩ := h.exists_sides (hD he) (hmid e he)
    exact ⟨i, p, j, q, e₁, e₂, h1, h2, h3⟩
  obtain ⟨Y, tY, t2, g, hg⟩ := exists_cut_presented.{u} (W := cutW W (lab '' D)) (finW_cut h.fin)
    (isPaired_cut h.paired) (by rw [dsk_cut]; exact hne)
  obtain ⟨ψ, h1, h2, h3, h4, hψ, hrep, hlift⟩ := WordEdges.cut_edges h hD hsd hg
  have : Finite (SE W) := finite_se h.fin
  have hfinV : ∀ v ∈ V ∩ ⋃₀ E, (ψ ⁻¹' {v}).Finite := fun v hv ↦ by
    refine ((finite_range (spe W)).image g).subset ?_
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hrep z
    have hfa : f a = v := by rw [← hψ a ha]; exact hz
    exact ⟨a, WordEdges.subset_range_spe h ha (hfa ▸ hv.1) (hfa ▸ hv.2), rfl⟩
  have hfin : ∀ x, (ψ ⁻¹' {x}).Finite := fun x ↦ by
    by_cases hx : x ∈ ⋃₀ D
    · obtain ⟨e, he, hxe⟩ := hx
      by_cases hxV : x ∈ V
      · exact hfinV x ⟨hxV, e, hD he, hxe⟩
      obtain ⟨t, ht, rfl, hc⟩ := WordEdges.exists_param h (hD he) hxe
      obtain ⟨r, r', -, -, -, -, hf⟩ := hlift e he
      have hI : t ∈ Ioo (0 : ℝ) 1 := hc.resolve_right (by
        rintro ⟨τ, rfl⟩
        exact hxV (h.extI_mem_V (hD he) τ))
      refine (Set.toFinite {r t, r' t}).subset fun z hz ↦ ?_
      exact (hf t ht (.inl hI)).2 z hz
    · have hoff : ∀ {z}, z ∈ ψ ⁻¹' {x} → z ∈ ψ ⁻¹' (⋃₀ D)ᶜ := fun {z} hz ↦ by
        show ψ z ∉ ⋃₀ D
        rw [show ψ z = x from hz]
        exact hx
      exact Set.Subsingleton.finite fun z hz z' hz' ↦ h3 (hoff hz) (hoff hz') (hz.trans hz'.symm)
  have hbdcut : ψ ⁻¹' (⋃₀ D) ⊆ bd Y := by
    rintro z ⟨e, he, hze⟩
    by_contra hz
    have hzi : IsInteriorPoint z := not_not.mp hz
    have hend : ∀ {w t e'}, e' ∈ D → t ∈ Ioo (0 : ℝ) 1 → ψ w = extI (A e') t → w ∈ bd Y := fun {w t e'} he' ht hw ↦ by
      obtain ⟨r, r', -, -, -, hb, hf⟩ := hlift e' he'
      have hI := Ioo_subset_Icc_self ht
      rcases (hf t hI (.inl ht)).2 w hw with rfl | rfl
      · exact (hb t hI).1
      · exact (hb t hI).2
    obtain ⟨t, ht, hte, hc⟩ := WordEdges.exists_param h (hD he) hze
    obtain ⟨τ, rfl⟩ : ∃ τ, eo τ = t := hc.resolve_left fun hI ↦ hz (hend he hI hte.symm)
    let P : Set Y := ψ ⁻¹' (V ∩ ⋃₀ E)
    have hP : P.Finite := by
      have : P = ⋃ v ∈ V ∩ ⋃₀ E, ψ ⁻¹' {v} := by
        ext w
        simp [P]
      rw [this]
      exact (h.graph.fin.subset inter_subset_left).biUnion fun v _ ↦ hfin v
    let U : Set Y := (bd Y)ᶜ ∩ (P \ {z})ᶜ
    have hUo : IsOpen U := (isClosed_bd Y).isOpen_compl.inter (hP.subset sdiff_subset).isClosed.isOpen_compl
    have hzU : z ∈ U := ⟨hz, fun hc ↦ hc.2 rfl⟩
    have key : ∀ w ∈ U, ψ w ∈ ⋃₀ D → w = z := by
      rintro w hw ⟨e', he', hwe⟩
      obtain ⟨t', ht', hte', hc'⟩ := WordEdges.exists_param h (hD he') hwe
      obtain ⟨τ', rfl⟩ : ∃ τ', eo τ' = t' := hc'.resolve_left fun hI ↦ hw.1 (hend he' hI hte'.symm)
      by_contra hne'
      exact hw.2 ⟨⟨hte' ▸ h.extI_mem_V (hD he') τ', e', hD he', hwe⟩, hne'⟩
    have hinj : InjOn ψ U := by
      intro a ha b hb hab
      by_cases hD' : ψ a ∈ ⋃₀ D
      · rw [key a ha hD', key b hb (hab ▸ hD')]
      · exact h3 hD' (show ψ b ∉ ⋃₀ D from hab ▸ hD') hab
    have hN := image_mem_nhds_of_injOn hzi (hS.2.2 (ψ z)) h1 hUo hzU hinj
    have hN' : extI (A e) ⁻¹' (ψ '' U) ∈ 𝓝 (eo τ) :=
      (continuous_extI (h.arc e (hD he)).1.1).continuousAt.preimage_mem_nhds (hte ▸ hN)
    have hcl : eo τ ∈ closure (Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (zero_ne_one' ℝ)]
      exact eo_mem τ
    obtain ⟨t', ht'N, ht'I⟩ := mem_closure_iff_nhds.mp hcl _ hN'
    obtain ⟨w, hw, he'⟩ := ht'N
    exact hw.1 (hend he ht'I he')
  have hcm : GM19.IsCutMap ψ (⋃₀ D) := ⟨h1, h2, h3, hfin, hbdcut⟩
  refine ⟨Y, tY, t2, ψ, h4, hcm, hlift, ?_, ?_⟩
  · intro v hv
    exact word_cut_vertex_fibre_eq_degree h hD hmid hg hψ hv.1 hv.2
  · intro hbd
    exact word_cut_vertices_ncard h hD hmid hg hψ hcm hbd

end GraphMinor.GM08
