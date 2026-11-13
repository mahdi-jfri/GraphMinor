module

public import GraphMinor.GM08.Section18Step
public import GraphMinor.GM08.Section11Iso
import GraphMinor.GM08.Section18SurroundDisc
import GraphMinor.GM08.Section18SplitOuter
import GraphMinor.GM08.Section18SplitInner
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM08.Section14
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.CuffStep

/-!
# The split step of (18.3)

Case (ii) of the proof of (18.3), page 287: the graft has a drawing `Γ` in
`Σ` with a `Γ`-normal `O`-arc `F` that surrounds a cuff `C`, meets `bd(Σ)`
only in `C`, and has fewer vertices than `C`. Paste a disc onto `C`. Then `F`
bounds a disc `Δ` around the pasted disc (`exists_surrounding_disc`). The
part of the graft outside `Δ` is drawn in `Σ` with `F` in place of `C`
(`exists_outer_graft`), so it has index at most `k - 1`. The part inside `Δ`
is a tubular graft with roots on `C ∪ F` (`exists_inner_graft`), so it has
index at most `2k - 1`. The graft is the gluing of the two parts along the
vertices of `F`, so it lies in `W(𝒞(Σ, k - 1)* ⊕ ℬ(2k - 1)*)` by
`mem_WGraftClass_of_isTwoPieceGluing`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u v w

/-- A graft drawing counts the vertices drawn in any set. -/
theorem ncard_fv_mem {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] [Nonempty S] {X : Graft α β} (gd : GraftDrawing X.G X.T S)
    (P : Set S) :
    {v ∈ V(X.G) | gd.iso.fv v ∈ P}.ncard = (gd.drawing.V ∩ P).ncard := by
  rw [← ((Iso.fv_injOn (a := gd.iso)).mono (sep_subset _ _)).ncard_image]
  congr 1
  ext x
  constructor
  · rintro ⟨v, ⟨hv, hP⟩, rfl⟩
    exact ⟨(show gd.iso.fv v ∈ gd.drawing.V from Iso.fv_mem (a := gd.iso) hv), hP⟩
  · rintro ⟨hx, hP⟩
    let w := gd.iso.vertexEquiv.symm ⟨x, hx⟩
    have hw : gd.iso.fv w.1 = x := by
      rw [Iso.fv_of_mem w.2]
      change ((gd.iso.vertexEquiv (gd.iso.vertexEquiv.symm ⟨x, hx⟩)).1 : S) = x
      rw [Equiv.apply_symm_apply]
    exact ⟨w.1, ⟨w.2, hw ▸ hP⟩, hw⟩

/-- The roots of a graft drawing are the vertices drawn in the boundary. -/
theorem fv_mem_bd_iff {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] [Nonempty S] {X : Graft α β} (gd : GraftDrawing X.G X.T S)
    {v : α} (hv : v ∈ V(X.G)) : gd.iso.fv v ∈ bd S ↔ v ∈ X.T := by
  rw [Iso.fv_of_mem hv]
  exact gd.mem_bd_iff v hv

/-- **The split step of (18.3)**, page 287, case (ii). -/
theorem splitStepStatement : SplitStepStatement.{u, w} := by
  intro S _ _ hS a b c h3 hm α β _ X gd C F k hC hn hF hsur hFb hlt hk
  classical
  have : T2Space S := hS.2.1
  obtain ⟨x₀, hx₀⟩ : C.Nonempty := by
    obtain ⟨φ⟩ := (cuff_statement S hS).2.2 C hC
    exact ⟨(φ 1).1, (φ 1).2⟩
  have : Nonempty S := ⟨x₀⟩
  have hCbd : C ⊆ bd S := GM07.connectedComponentIn_subset_of_cuff hC
  obtain ⟨T, tT, j, D, hcap, hbT⟩ := GM07.exists_cappedCuff hS hC
  have hT := hcap.isSurface
  have : T2Space T := hT.2.1
  have hman := hT.2.2
  have hj := hcap.isEmbedding
  obtain ⟨Δ, hΔ, hbΔ, hDΔ⟩ := exists_surrounding_disc hS hF hsur hcap
  have hFpre : j ⁻¹' discBd Δ = F := by rw [hbΔ]; exact preimage_image_eq _ hj.injective
  have hne : (gd.drawing.V ∩ C).Nonempty := nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨A, hAX, hAV, hAE, hAT, hAemb⟩ :=
    exists_outer_graft hS gd hC hF hFb hn hcap hbT hΔ hbΔ hDΔ
  obtain ⟨B, hBX, hBV, hBE, hBT, hBtub⟩ :=
    exists_inner_graft hS gd hC hFb hn hcap hbT hΔ hbΔ hDΔ hne
  set Z : Set S := j ⁻¹' discInt Δ with hZdef
  set R : Set S := j ⁻¹' Δ with hRdef
  have hZR : Z ⊆ R := preimage_mono (discInt_subset Δ)
  have hRZ : ∀ x, x ∈ R → x ∉ Z → x ∈ F := fun x hxR hxZ => by
    rw [← hFpre]
    by_contra hb
    exact hxZ ⟨hxR, hb⟩
  have hFR : ∀ x ∈ F, x ∈ R ∧ x ∉ Z := fun x hx => by
    have h : j x ∈ discBd Δ := hbΔ ▸ mem_image_of_mem j hx
    exact ⟨discBd_subset Δ h, fun hz => hz.2 h⟩
  have hCR : ∀ x ∈ C, x ∈ R := fun x hx =>
    hDΔ (discBd_subset D (hcap.discBd_eq ▸ mem_image_of_mem j hx))
  have hbdZ : ∀ x ∈ bd S \ C, x ∉ Z := fun x hx hxZ => by
    have : j x ∈ bd T := hbT ▸ mem_image_of_mem j hx
    exact this (isInteriorPoint_of_mem_discInt hman hΔ hxZ)
  have hnF : gd.drawing.IsNormal (j ⁻¹' discBd Δ) := hFpre ▸ hn
  -- the gluing
  have hglue : IsTwoPieceGluing X A B := by
    refine ⟨hAX, hBX, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply subset_antisymm (union_subset hAX.vertexSet_mono hBX.vertexSet_mono)
      intro v hv
      by_cases hvZ : gd.iso.fv v ∈ Z
      · exact .inr (hBV ▸ ⟨hv, hZR hvZ⟩)
      · exact .inl (hAV ▸ ⟨hv, hvZ⟩)
    · apply subset_antisymm (union_subset hAX.edgeSet_mono hBX.edgeSet_mono)
      intro g hg
      have hge : gd.iso.fe g ∈ gd.drawing.E := Iso.fe_mem (a := gd.iso) hg
      rcases edge_subset_or_disjoint hman hj.continuous hΔ hnF hge with h1 | h1
      · exact .inr (hBE ▸ ⟨hg, disjoint_compl_right_iff_subset.mpr (h1.trans hZR)⟩)
      · exact .inl (hAE ▸ ⟨hg, h1.mono_right hZR⟩)
    · rw [hAE, hBE, Set.disjoint_left]
      rintro g ⟨hg, h1⟩ ⟨-, h2⟩
      have hge : gd.iso.fe g ∈ gd.drawing.E := Iso.fe_mem (a := gd.iso) hg
      obtain ⟨x, hx⟩ := hge.2.2.1.isConnected.nonempty
      have hxR : x ∈ R := by
        by_contra hxR
        exact disjoint_left.mp h2 hx hxR
      have hxF := hRZ x hxR (disjoint_left.mp h1 hx)
      have hxU := hge.2.1 hx
      exact hxU.2 (hn ⟨hxF, hxU.1⟩)
    · rintro v ⟨hvA, hvB⟩
      rw [hAV] at hvA
      rw [hBV] at hvB
      rw [hAT]
      exact ⟨hvA.1, .inr (hRZ _ hvB.2 hvA.2)⟩
    · rintro v ⟨hvA, hvB⟩
      rw [hAV] at hvA
      rw [hBV] at hvB
      rw [hBT]
      exact ⟨hvA.1, .inr (hRZ _ hvB.2 hvA.2)⟩
    · intro v hv
      have hvV := X.T_subset hv
      have hb := (fv_mem_bd_iff gd hvV).mpr hv
      by_cases hvC : gd.iso.fv v ∈ C
      · exact .inr (hBT ▸ ⟨hvV, .inl hvC⟩)
      · exact .inl (hAT ▸ ⟨hvV, .inl ⟨hb, hvC⟩⟩)
    · rintro v ⟨hvT, hvn⟩
      have hvV : v ∈ V(X.G) := by
        rcases hvT with h | h
        · exact hAX.vertexSet_mono (A.T_subset h)
        · exact hBX.vertexSet_mono (B.T_subset h)
      refine (fv_mem_bd_iff gd hvV).mp ?_
      by_cases hvF : gd.iso.fv v ∈ F
      · exfalso
        refine hvn ⟨hAV ▸ ⟨hvV, (hFR _ hvF).2⟩, hBV ▸ ⟨hvV, (hFR _ hvF).1⟩⟩
      rcases hvT with h | h
      · rw [hAT] at h
        rcases h.2 with h' | h'
        · exact h'.1
        · exact absurd h' hvF
      · rw [hBT] at h
        rcases h.2 with h' | h'
        · exact hCbd h'
        · exact absurd h' hvF
  -- the indices
  have hidx : X.index = (gd.drawing.V ∩ bd S).ncard := ncard_roots_eq_boundary_vertices gd
  have hfin : gd.drawing.V.Finite := gd.drawing.finite_V
  have hsplit : (gd.drawing.V ∩ (bd S \ C)).ncard + (gd.drawing.V ∩ C).ncard =
      (gd.drawing.V ∩ bd S).ncard := by
    have hdisj : Disjoint (gd.drawing.V ∩ (bd S \ C)) (gd.drawing.V ∩ C) := by
      rw [Set.disjoint_left]
      rintro x ⟨-, -, hc⟩ ⟨-, hc'⟩
      exact hc hc'
    rw [← ncard_union_eq hdisj (hfin.subset inter_subset_left) (hfin.subset inter_subset_left)]
    congr 1
    ext x
    constructor
    · rintro (⟨hx, hb, -⟩ | ⟨hx, hc⟩)
      · exact ⟨hx, hb⟩
      · exact ⟨hx, hCbd hc⟩
    · rintro ⟨hx, hb⟩
      by_cases hc : x ∈ C
      · exact .inr ⟨hx, hc⟩
      · exact .inl ⟨hx, hb, hc⟩
  have hAidx : A.index ≤ (gd.drawing.V ∩ (bd S \ C)).ncard + (gd.drawing.V ∩ F).ncard := by
    change A.T.ncard ≤ _
    rw [hAT, ncard_fv_mem gd, inter_union_distrib_left]
    exact ncard_union_le _ _
  have hBidx : B.index ≤ (gd.drawing.V ∩ C).ncard + (gd.drawing.V ∩ F).ncard := by
    change B.T.ncard ≤ _
    rw [hBT, ncard_fv_mem gd, inter_union_distrib_left]
    exact ncard_union_le _ _
  have hAmem : A ∈ classCSurface S (k - 1) := ⟨by omega, hAemb⟩
  have hBmem : B ∈ classB (2 * (k : ℤ) - 1) := ⟨hBtub, by omega⟩
  exact mem_WGraftClass_of_isTwoPieceGluing hglue hAmem hBmem

end GraphMinor.GM08
