module

public import GraphMinor.GM13.Section8c
import GraphMinor.GM11.ArcDrawings

/-!
# Graph Minors XIII, Section 8 (Part 4): Rurality of `coreDivision` and Algorithm (8.6)

This file completes the formalization of Section 8 of Graph Minors XIII (pages 96–97):
- `isRuralDivision_coreDivision`: for any cross-free society `S` and 4-linked core `C` of `S`,
  `coreDivision S C` is a rural division of `S`.
- `algorithm_8_6_correct` / `theorem_8_6`: `(8.6)` (pages 96–97), finding either a cross in a
  society `(G, Ω)` or a rural division `𝒜` of `(G, Ω)`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Classical Function Topology Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM09 GraphMinor.GM11

universe u v

variable {α : Type u} {β : Type v} {β' : Type*}

/-! ## Edge Splitting and Loop Half-Arc Helpers on Drawings -/

theorem graphDrawingVertexSet_eq_singleton {S : Type*} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(G)) :
    graphDrawingVertexSet Γ v = {(Γ.iso.vertexEquiv ⟨v, hv⟩).1} := by
  ext x
  simp [graphDrawingVertexSet, hv, eq_comm]

/-- If `a ∈ D.E` has `closure a ∩ D.V = {x}`, then `closure a` is an `O`-arc containing `x`. -/
theorem isOArc_closure {S : Type*} [TopologicalSpace S] {D : Drawing S} {a : Set S}
    (ha : a ∈ D.E) {x : S} (hcap : closure a ∩ D.V = {x}) :
    IsOArc (closure a) ∧ x ∈ closure a := by
  have hx : x ∈ closure a := (hcap ▸ mem_singleton x).1
  rcases D.edge_cond a ha with ⟨u, v, huv, hc, -⟩ | ⟨u, -, hF⟩
  · have hset : ({u, v} : Set S) = {x} := hc.symm.trans hcap
    have hu : u = x := mem_singleton_iff.mp (hset ▸ mem_insert u {v})
    have hv : v = x := mem_singleton_iff.mp (hset ▸ mem_insert_of_mem u (mem_singleton v))
    exact (huv (hu.trans hv.symm)).elim
  · exact ⟨hF, hx⟩

/-- Splitting a non-loop edge `a ∈ D.E` with `closure a ∩ D.V = {x, y}` (`x ≠ y`) at an interior
point `m ∈ a` produces two lines `L₁` (from `m` to `x`) and `L₂` (from `m` to `y`) whose open
interiors lie in `a \ {m}` and are disjoint. -/
theorem split_drawing_edge_of_isLine {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {a : Set S} (ha : a ∈ D.E) {x y m : S}
    (hxy : x ≠ y) (hcap : closure a ∩ D.V = {x, y}) (hm : m ∈ a) :
    ∃ L₁ L₂ : Set S,
      IsLineWithEnds L₁ m x ∧
      IsLineWithEnds L₂ m y ∧
      L₁ ⊆ closure a ∧
      L₂ ⊆ closure a ∧
      L₁ \ {m, x} ⊆ a \ {m} ∧
      L₂ \ {m, y} ⊆ a \ {m} ∧
      Disjoint (L₁ \ {m, x}) (L₂ \ {m, y}) := by
  have hL : IsLineWithEnds (closure a) x y := isLine_closure ha hxy hcap
  have hm_cl : m ∈ closure a := subset_closure hm
  have hm_not_V : m ∉ D.V := (ha.2.1 hm).2
  have hx_V : x ∈ D.V := (hcap ▸ mem_insert x {y}).2
  have hy_V : y ∈ D.V := (hcap ▸ mem_insert_of_mem x (mem_singleton y)).2
  have hmx : m ≠ x := fun h => hm_not_V (h ▸ hx_V)
  have hmy : m ≠ y := fun h => hm_not_V (h ▸ hy_V)
  obtain ⟨f, hf0, hf1⟩ := id hL
  let g : unitInterval → S := fun t => (f t).1
  have hgc : Continuous g := continuous_subtype_val.comp f.continuous
  have hgi : Function.Injective g := Subtype.val_injective.comp f.injective
  have hrange : range g = closure a := by
    ext z
    exact ⟨fun ⟨t, ht⟩ => ht ▸ (f t).2, fun hz =>
      let ⟨t, ht⟩ := f.surjective ⟨z, hz⟩
      ⟨t, congrArg Subtype.val ht⟩⟩
  obtain ⟨τ, hτ⟩ : m ∈ range g := hrange ▸ hm_cl
  have hτ0 : (0 : unitInterval) < τ :=
    bot_lt_iff_ne_bot.mpr fun h => hmx (hτ.symm.trans ((congrArg g h).trans hf0))
  have hτ1 : τ < (1 : unitInterval) :=
    lt_top_iff_ne_top.mpr fun h => hmy (hτ.symm.trans ((congrArg g h).trans hf1))
  let L₁ : Set S := g '' Icc 0 τ
  let L₂ : Set S := g '' Icc τ 1
  have hL₁ : IsLineWithEnds L₁ x m := by
    have := isLine_piece hgc hgi hτ0
    rwa [hτ, show g 0 = x from hf0] at this
  have hL₂ : IsLineWithEnds L₂ m y := by
    have := isLine_piece hgc hgi hτ1
    rwa [hτ, show g 1 = y from hf1] at this
  have hL₁_sub : L₁ ⊆ closure a := by
    rw [← hrange]; exact image_subset_range _ _
  have hL₂_sub : L₂ ⊆ closure a := by
    rw [← hrange]; exact image_subset_range _ _
  have hinter : L₁ ∩ L₂ = {m} := by
    refine subset_antisymm ?_ (singleton_subset_iff.mpr
      ⟨⟨τ, ⟨hτ0.le, le_rfl⟩, hτ⟩, ⟨τ, ⟨le_rfl, hτ1.le⟩, hτ⟩⟩)
    rintro z ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
    have hst : t = s := hgi hts
    have hsτ : s = τ := le_antisymm hs.2 (hst ▸ ht.1)
    rw [mem_singleton_iff, hsτ, hτ]
  have hx_L₁ : x ∈ L₁ := ⟨0, ⟨le_rfl, hτ0.le⟩, hf0⟩
  have hy_L₂ : y ∈ L₂ := ⟨1, ⟨hτ1.le, le_rfl⟩, hf1⟩
  have hy_not_L₁ : y ∉ L₁ := fun hy₁ =>
    hmy (mem_singleton_iff.mp (hinter ▸ ⟨hy₁, hy_L₂⟩)).symm
  have hx_not_L₂ : x ∉ L₂ := fun hx₂ =>
    hmx (mem_singleton_iff.mp (hinter ▸ ⟨hx_L₁, hx₂⟩)).symm
  have hcl_diff : closure a \ D.V = a := D.closure_diff_V ha
  refine ⟨L₁, L₂, GraphMinor.GM11.IsLineWithEnds.symm hL₁, hL₂, hL₁_sub, hL₂_sub, ?_, ?_, ?_⟩
  · rintro z ⟨hz₁, hz_ne⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_ne
    have hz_cl : z ∈ closure a := hL₁_sub hz₁
    have hz_not_V : z ∉ D.V := by
      intro hzV
      have hz_xy : z ∈ ({x, y} : Set S) := hcap ▸ ⟨hz_cl, hzV⟩
      rcases hz_xy with rfl | rfl
      · exact hz_ne.2 rfl
      · exact hy_not_L₁ hz₁
    exact ⟨hcl_diff ▸ ⟨hz_cl, hz_not_V⟩, hz_ne.1⟩
  · rintro z ⟨hz₂, hz_ne⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_ne
    have hz_cl : z ∈ closure a := hL₂_sub hz₂
    have hz_not_V : z ∉ D.V := by
      intro hzV
      have hz_xy : z ∈ ({x, y} : Set S) := hcap ▸ ⟨hz_cl, hzV⟩
      rcases hz_xy with rfl | rfl
      · exact hx_not_L₂ hz₂
      · exact hz_ne.2 rfl
    exact ⟨hcl_diff ▸ ⟨hz_cl, hz_not_V⟩, hz_ne.1⟩
  · rw [disjoint_left]
    rintro z ⟨hz₁, hz_ne⟩ ⟨hz₂, _⟩
    have hzm : z = m := mem_singleton_iff.mp (hinter ▸ ⟨hz₁, hz₂⟩)
    exact hz_ne (Or.inl hzm)

/-- Taking a half-arc of a loop `a ∈ D.E` with `closure a ∩ D.V = {x}` from an interior point
`m ∈ a` to `x` produces a line `L` from `m` to `x` whose open interior lies in `a \ {m}`. -/
theorem half_drawing_edge_of_loop {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {a : Set S} (ha : a ∈ D.E) {x m : S}
    (hcap : closure a ∩ D.V = {x}) (hm : m ∈ a) :
    ∃ L : Set S,
      IsLineWithEnds L m x ∧
      L ⊆ closure a ∧
      L \ {m, x} ⊆ a \ {m} := by
  obtain ⟨hF, hx_cl⟩ := isOArc_closure ha hcap
  have hm_cl : m ∈ closure a := subset_closure hm
  have hm_not_V : m ∉ D.V := (ha.2.1 hm).2
  have hx_V : x ∈ D.V := (hcap ▸ mem_singleton x).2
  have hmx : m ≠ x := fun h => hm_not_V (h ▸ hx_V)
  obtain ⟨f, b, htwo, hf0, hf1, hunion⟩ := hF.exists_arcs hm_cl hx_cl hmx
  have hL : IsLineWithEnds (range f) m x := by
    have := isLine_range htwo.arc_left.1 htwo.arc_left.2
    rwa [hf0, hf1] at this
  have hL_sub : range f ⊆ closure a := hunion ▸ subset_union_left
  have hcl_diff : closure a \ D.V = a := D.closure_diff_V ha
  refine ⟨range f, hL, hL_sub, ?_⟩
  rintro z ⟨hzL, hz_ne⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_ne
  have hz_cl : z ∈ closure a := hL_sub hzL
  have hz_not_V : z ∉ D.V := by
    intro hzV
    have hzx : z = x := mem_singleton_iff.mp (hcap ▸ ⟨hz_cl, hzV⟩)
    exact hz_ne.2 hzx
  exact ⟨hcl_diff ▸ ⟨hz_cl, hz_not_V⟩, hz_ne.1⟩

/-- Constructing a `GraphDrawing` of a finite graph `B` by gluing lines `K e` along its edges. -/
theorem GraphDrawing.of_edge_lines {S : Type*} [TopologicalSpace S] [T2Space S]
    {γ δ : Type*} {B : Graph γ δ} (hV_fin : V(B).Finite) (hE_fin : E(B).Finite)
    {ν : γ → S} (hν_inj : InjOn ν V(B))
    {u_end v_end : δ → γ}
    (hends : ∀ e ∈ E(B), u_end e ≠ v_end e ∧ B.IsLink e (u_end e) (v_end e))
    {K : δ → Set S}
    (hK_line : ∀ e ∈ E(B), IsLineWithEnds (K e) (ν (u_end e)) (ν (v_end e)))
    (hdisj_V : ∀ e ∈ E(B), Disjoint (K e \ {ν (u_end e), ν (v_end e)}) (ν '' V(B)))
    (hdisj_E : ∀ e₁ ∈ E(B), ∀ e₂ ∈ E(B), e₁ ≠ e₂ →
      Disjoint (K e₁ \ {ν (u_end e₁), ν (v_end e₁)}) (K e₂ \ {ν (u_end e₂), ν (v_end e₂)})) :
    ∃ Γ : GraphDrawing B S,
      Γ.drawing.U = (ν '' V(B)) ∪ (⋃ e ∈ E(B), K e) ∧
      ∀ v : V(B), (Γ.iso.vertexEquiv v).1 = ν v.1 := by
  suffices ∀ (n : ℕ) (F : Set δ), F ⊆ E(B) → F.ncard = n →
      ∃ Γ : GraphDrawing (B.restrict F) S,
        Γ.drawing.U = (ν '' V(B)) ∪ (⋃ e ∈ F, K e) ∧
        ∀ v : V(B.restrict F), (Γ.iso.vertexEquiv v).1 = ν v.1 by
    obtain ⟨Γ₀, hU₀, hν₀⟩ := this E(B).ncard E(B) Subset.rfl rfl
    have hB_eq : B.restrict E(B) = B := by
      refine le_antisymm restrict_le ⟨by simp, fun {_ _ _} hl => ?_⟩
      refine (restrict_le.isLink_iff ?_).mpr hl
      rw [edgeSet_restrict, inter_self]
      exact hl.edge_mem
    obtain ⟨Γ, hD_eq, hν⟩ := GraphDrawing.of_eq hB_eq Γ₀ hν₀
    exact ⟨Γ, (congrArg Drawing.U hD_eq).trans hU₀, hν⟩
  intro n
  induction n with
  | zero =>
    intro F hF hn
    have hF_fin : F.Finite := hE_fin.subset hF
    have hF_empty : F = ∅ := (ncard_eq_zero hF_fin).mp hn
    have hE_empty : E(B.restrict F) = ∅ := by simp [edgeSet_restrict, hF_empty]
    have hV_eq : V(B.restrict F) = V(B) := vertexSet_restrict B F
    obtain ⟨Γ, hU, hν⟩ := GraphDrawing.of_edgeless (hV_eq ▸ hV_fin) hE_empty (hV_eq ▸ hν_inj)
    refine ⟨Γ, ?_, hν⟩
    rw [hU, hV_eq, hF_empty]
    simp
  | succ n ih =>
    intro F hF hn
    have hF_fin : F.Finite := hE_fin.subset hF
    have hF_ne : F.Nonempty := (ncard_pos hF_fin).mp (by omega)
    obtain ⟨e₀, he₀F⟩ := hF_ne
    let F' := F \ {e₀}
    have hF'_sub : F' ⊆ E(B) := sdiff_subset.trans hF
    have hF'_card : F'.ncard = n := by
      change (F \ {e₀}).ncard = n
      rw [ncard_sdiff_singleton_of_mem he₀F, hn]
      omega
    obtain ⟨Γ₁, hU₁, hν₁⟩ := ih F' hF'_sub hF'_card
    have he₀B : e₀ ∈ E(B) := hF he₀F
    obtain ⟨hne₀, hlink₀⟩ := hends e₀ he₀B
    have hu₀ : u_end e₀ ∈ V(B) := hlink₀.left_mem
    have hv₀ : v_end e₀ ∈ V(B) := hlink₀.right_mem
    let H₂ : Graph γ δ := (B.induce {u_end e₀, v_end e₀}).restrict {e₀}
    have hV₂ : V(H₂) = {u_end e₀, v_end e₀} := by simp [H₂]
    have hE₂ : E(H₂) = {e₀} := by
      ext e
      simp only [H₂, edgeSet_restrict, mem_inter_iff, mem_singleton_iff, edgeSet_induce,
        mem_ofPred_eq]
      refine ⟨fun h => h.2, fun he => ?_⟩
      rw [he]
      exact ⟨⟨u_end e₀, v_end e₀, hlink₀, by simp, by simp⟩, rfl⟩
    have hlink₂ : H₂.IsLink e₀ (u_end e₀) (v_end e₀) := ⟨rfl, hlink₀, by simp, by simp⟩
    have hν_ne : ν (u_end e₀) ≠ ν (v_end e₀) := fun h => hne₀ (hν_inj hu₀ hv₀ h)
    obtain ⟨Γ₂, hU₂, hν₂⟩ :=
      GraphDrawing.of_single_edge hV₂ hE₂ hlink₂ hν_ne (hK_line e₀ he₀B)
    have hG₁_le : B.restrict F' ≤ B.restrict F :=
      ⟨by simp, fun {_ _ _} hl => ⟨sdiff_subset hl.1, hl.2⟩⟩
    have hH₂_le : H₂ ≤ B.restrict F := by
      refine ⟨?_, fun {_ _ _} hl => ⟨hl.1 ▸ he₀F, hl.2.1⟩⟩
      rw [hV₂, vertexSet_restrict]
      rintro x (rfl | rfl) <;> assumption
    have hV_union : V(B.restrict F') ∪ V(H₂) = V(B.restrict F) := by
      rw [hV₂, vertexSet_restrict, vertexSet_restrict, union_eq_self_of_subset_right]
      rintro x (rfl | rfl) <;> assumption
    have hE_union : E(B.restrict F') ∪ E(H₂) = E(B.restrict F) := by
      rw [hE₂, edgeSet_restrict, edgeSet_restrict]
      ext e
      simp only [mem_union, mem_inter_iff, mem_sdiff, mem_singleton_iff, F']
      refine ⟨fun h => ?_, fun ⟨heB, heF⟩ => ?_⟩
      · rcases h with ⟨heB, heF, _⟩ | rfl
        · exact ⟨heB, heF⟩
        · exact ⟨he₀B, he₀F⟩
      · by_cases h : e = e₀
        · exact Or.inr h
        · exact Or.inl ⟨heB, heF, h⟩
    have hE_disj : Disjoint E(B.restrict F') E(H₂) := by
      rw [hE₂, edgeSet_restrict, disjoint_singleton_right]
      intro h
      exact h.2.2 rfl
    have hV_inter : V(B.restrict F') ∩ V(H₂) = {u_end e₀, v_end e₀} := by
      rw [hV₂, vertexSet_restrict]
      exact inter_eq_right.mpr (by rintro x (rfl | rfl) <;> assumption)
    have hmeet : Γ₁.drawing.U ∩ Γ₂.drawing.U ⊆ ν '' (V(B.restrict F') ∩ V(H₂)) := by
      rw [hV_inter, image_pair, hU₁, hU₂]
      rintro z ⟨hz₁, hz₂⟩
      by_contra hz_not_end
      have hz_int₀ : z ∈ K e₀ \ {ν (u_end e₀), ν (v_end e₀)} := ⟨hz₂, hz_not_end⟩
      rcases hz₁ with hzV | hzE
      · exact disjoint_left.mp (hdisj_V e₀ he₀B) hz_int₀ hzV
      · obtain ⟨e, heF', hze⟩ := mem_iUnion₂.mp hzE
        have heB : e ∈ E(B) := hF'_sub heF'
        have hee₀ : e ≠ e₀ := heF'.2
        by_cases hz_end_e : z ∈ ({ν (u_end e), ν (v_end e)} : Set S)
        · have hzV : z ∈ ν '' V(B) := by
            rcases hz_end_e with rfl | rfl
            · exact ⟨u_end e, (hends e heB).2.left_mem, rfl⟩
            · exact ⟨v_end e, (hends e heB).2.right_mem, rfl⟩
          exact disjoint_left.mp (hdisj_V e₀ he₀B) hz_int₀ hzV
        · exact disjoint_left.mp (hdisj_E e heB e₀ he₀B hee₀) ⟨hze, hz_end_e⟩ hz_int₀
    obtain ⟨Γ, hU, hν⟩ := GraphDrawing.glue hG₁_le hH₂_le hV_union hE_union hE_disj
      (by rwa [vertexSet_restrict]) Γ₁ Γ₂ hν₁ hν₂ hmeet
    refine ⟨Γ, ?_, hν⟩
    rw [hU, hU₁, hU₂]
    ext z
    simp only [mem_union, mem_iUnion, exists_prop, F', mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ((hzV | ⟨e, ⟨heF, _⟩, hze⟩) | hze₀)
      · exact Or.inl hzV
      · exact Or.inr ⟨e, heF, hze⟩
      · exact Or.inr ⟨e₀, he₀F, hze₀⟩
    · rintro (hzV | ⟨e, heF, hze⟩)
      · exact Or.inl (Or.inl hzV)
      · by_cases h : e = e₀
        · subst h; exact Or.inr hze
        · exact Or.inl (Or.inr ⟨e, ⟨heF, h⟩, hze⟩)

/-- Helper to package a disc drawing of `S'.G` into `S'.IsRuralSociety`. -/
theorem isRuralSociety_of_disc_drawing {γ δ : Type*} (S' : Society γ δ)
    (Γ : GraphDrawing S'.G EuclideanPlane) (Δ : Set EuclideanPlane)
    (hΔ : IsClosedDisc Δ) (hU : Γ.drawing.U ⊆ Δ)
    (hbd : ∀ v ∈ V(S'.G), graphDrawingVertexSet Γ v ⊆ subBd Δ ↔ v ∈ S'.Ω.bar)
    (φ : Circle ≃ₜ subBd Δ) (hcw : IsClockwiseDiscHomeo Δ φ)
    (hagrees : DrawingAgreesWithOArcHomeo Γ S'.Ω (subBd Δ) φ) :
    S'.IsRuralSociety := by
  let Ω₀ : CyclicPerm γ := ⟨∅, id, finite_empty, bijOn_empty id, fun _ h => h.elim⟩
  refine ⟨Ω₀, empty_subset _, rfl, Γ, Δ, ∅, hΔ, empty_subset _, ?_, hbd, ?_, ⟨φ, hcw, hagrees⟩,
    Or.inl ⟨rfl, rfl⟩⟩
  · simpa using hU
  · intro v hv
    simp only [Ω₀, mem_empty_iff_false, iff_false]
    intro hsub
    have hpt : (Γ.iso.vertexEquiv ⟨v, hv⟩).1 ∈ subBd (∅ : Set EuclideanPlane) :=
      hsub ⟨hv, rfl⟩
    simp [subBd] at hpt

/-- Extracting a clean disc drawing from `S'.IsRuralSociety`. -/
theorem exists_clean_disc_drawing_of_isRuralSociety {γ δ : Type*} (S' : Society γ δ)
    (hrural : S'.IsRuralSociety) :
    ∃ (Γ : GraphDrawing S'.G EuclideanPlane) (Δ : Set EuclideanPlane) (φ : Circle ≃ₜ subBd Δ),
      IsClosedDisc Δ ∧
      IsClockwiseDiscHomeo Δ φ ∧
      Γ.drawing.U ⊆ Δ ∧
      Γ.drawing.U ∩ subBd Δ = (⋃ v ∈ S'.Ω.bar, graphDrawingVertexSet Γ v) ∧
      (∀ v ∈ V(S'.G), graphDrawingVertexSet Γ v ⊆ subBd Δ ↔ v ∈ S'.Ω.bar) ∧
      DrawingAgreesWithOArcHomeo Γ S'.Ω (subBd Δ) φ := by
  obtain ⟨Ω₀, h₀, _, Γ₀, Δ, Δ₀, hΔ, hΔ₀_sub, hU₀_sub, hbd₀, hbd₀', ⟨φ, hcw₀, hagrees₀⟩, hinner₀⟩ :=
    hrural
  obtain ⟨_, _, Γ, Δ₀', _, _, _, _, _, _, _, _, hU_sub, _, _, _, hU_inter_bd, _, hbd, _,
    hagrees, _⟩ :=
    exists_clean_presentation_of_restrict_outer S'.bar_subset Subset.rfl
      (fun _ _ _ h => h) Γ₀ Δ Δ₀ hΔ hΔ₀_sub hU₀_sub hbd₀ hbd₀' φ hagrees₀ hinner₀
  exact ⟨Γ, Δ, φ, hΔ, hcw₀, hU_sub.trans sdiff_subset, hU_inter_bd, hbd, hagrees⟩

/-! ## Empty-Core Auxiliary Disc -/

/-- There exists a closed disc `Δ` in `EuclideanPlane`, an interior point `p₀ ∈ Δ \ subBd Δ`, and a
homeomorphism `φ : Circle ≃ₜ subBd Δ`. -/
theorem exists_closedDisc_and_interior_point :
    ∃ (Δ : Set EuclideanPlane) (p₀ : EuclideanPlane) (φ : Circle ≃ₜ subBd Δ),
      IsClosedDisc Δ ∧ IsClockwiseDiscHomeo Δ φ ∧ p₀ ∈ Δ \ subBd Δ := by
  let G₁ : Graph Unit Empty :=
    { vertexSet := univ
      edgeSet := ∅
      IsLink := fun e => nomatch e
      isLink_symm := fun e => nomatch e
      eq_or_eq_of_isLink_of_isLink := fun e => nomatch e
      edge_mem_iff_exists_isLink := fun e => nomatch e
      left_mem_of_isLink := fun e => nomatch e }
  let Ω₁ : CyclicPerm Unit :=
    ⟨{()}, id, finite_singleton (), bijOn_singleton.mpr rfl, fun _ _ _ _ => ⟨0, rfl⟩⟩
  let S₁ : Society Unit Empty :=
    { G := G₁
      Ω := Ω₁
      finite_V := finite_univ
      finite_E := finite_empty
      bar_subset := subset_univ _ }
  have hconn₁ : S₁.IsKConnected 3 := by
    intro k _ A₁ A₂ ⟨⟨hsep, hbar⟩, _, hne⟩
    refine hne (subset_antisymm hsep.2.1.vertexSet_mono ?_)
    rintro ⟨⟩ _
    exact hbar (mem_singleton ())
  have hnocross₁ : ¬ ∃ Q₁ Q₂ : Graph Unit Empty, S₁.IsCross Q₁ Q₂ := by
    rintro ⟨_, _, _, p₁, p₂, _, _, _, _, hcr⟩
    rcases hcr with ⟨hnodup, _, _⟩ | ⟨hnodup, _, _⟩ <;>
      simp [Subsingleton.elim p₁ p₂] at hnodup
  have hnotripod₁ : ¬ ∃ T₁ T₂ T₃ : Graph Unit Empty, S₁.IsTripod T₁ T₂ T₃ := by
    rintro ⟨T₁, T₂, T₃, htr⟩
    rcases GraphMinor.GM09.theorem_2_3_proof S₁ htr with hcr | ⟨A₁, A₂, hint, _⟩
    · exact hnocross₁ hcr
    · exact hint.1.2.2 (subset_antisymm hint.1.1.1.2.1.vertexSet_mono
        (fun ⟨⟩ _ => hint.1.1.2 (mem_singleton ())))
  have hrural₁ : S₁.IsRuralSociety := GraphMinor.GM09.theorem_2_4_proof S₁ hconn₁ hnocross₁ hnotripod₁
  obtain ⟨Ω₀, h₀, _, Γ₀, Δ, Δ₀, hΔ, hΔ₀_sub, hU₀_sub, hbd₀, hbd₀', ⟨φ, hcw₀, hagrees₀⟩, hinner₀⟩ :=
    hrural₁
  let Ω' : CyclicPerm Unit := ⟨∅, id, finite_empty, bijOn_empty id, fun _ h => h.elim⟩
  obtain ⟨_, _, Γ, _, _, _, _, _, _, _, _, _, hU_sub, _, _, _, _, _, hbd', _, _, _⟩ :=
    exists_clean_presentation_of_restrict_outer (Ω' := Ω') (empty_subset _) (empty_subset _)
      (fun v₁ _ _ hcw => (hcw.2.1 v₁ (by simp)).elim)
      Γ₀ Δ Δ₀ hΔ hΔ₀_sub hU₀_sub hbd₀ hbd₀' φ hagrees₀ hinner₀
  let p₀ : EuclideanPlane := (Γ.iso.vertexEquiv ⟨(), trivial⟩).1
  have hp₀_U : p₀ ∈ Γ.drawing.U := Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨(), trivial⟩).2
  have hp₀_Δ : p₀ ∈ Δ := (hU_sub.trans sdiff_subset) hp₀_U
  have hp₀_not_bd : p₀ ∉ subBd Δ := by
    intro hp₀_bd
    have hsub : graphDrawingVertexSet Γ () ⊆ subBd Δ := by
      rw [graphDrawingVertexSet_eq_singleton Γ trivial, singleton_subset_iff]
      exact hp₀_bd
    exact (hbd' () trivial).mp hsub
  exact ⟨Δ, p₀, φ, hΔ, hcw₀, hp₀_Δ, hp₀_not_bd⟩

/-! ## Rurality of `coreDivision S C` -/

/-- For `A ∈ coreDivision S C` with `(divBoundary S A).ncard = 2`, the chosen pair of distinct
vertices in `divBoundary S A` and core edge linking them. -/
noncomputable def coreTwoBoundaryData {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {A : Graph α β} (hA : A ∈ coreDivision S C)
    (hcard2 : (divBoundary S A).ncard = 2) :
    { p : (α × α) × β' //
      p.1.1 ≠ p.1.2 ∧
      divBoundary S A = {p.1.1, p.1.2} ∧
      C.IsLink p.2 p.1.1 p.1.2 } := by
  have hex : ∃ u v : α, u ≠ v ∧ divBoundary S A = {u, v} := ncard_eq_two.mp hcard2
  let u := Classical.choose hex
  let v := Classical.choose (Classical.choose_spec hex)
  have huv : u ≠ v ∧ divBoundary S A = {u, v} :=
    Classical.choose_spec (Classical.choose_spec hex)
  have hu_bd : u ∈ divBoundary S A := huv.2 ▸ mem_insert u {v}
  have hv_bd : v ∈ divBoundary S A := huv.2 ▸ mem_insert_of_mem u (mem_singleton v)
  have hex_e : ∃ e, C.IsLink e u v :=
    (boundary_isClique_in_core hC hA).2 u hu_bd v hv_bd huv.1
  let e := Classical.choose hex_e
  exact ⟨((u, v), e), huv.1, huv.2, Classical.choose_spec hex_e⟩

theorem inl_mem_edgeSet_auxCoreGraph {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C)) {e : β'} (he : e ∈ E(C)) :
    (Sum.inl e : AuxCoreEdge α β β') ∈ E(auxCoreGraph hC hv₀) :=
  Or.inl (Or.inl ⟨e, he, rfl⟩)

theorem inr_inl_mem_edgeSet_auxCoreGraph {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    {p : Graph α β × α} (hpA : p.1 ∈ coreDivision S C)
    (hp3 : (divBoundary S p.1).ncard = 3) (hpu : p.2 ∈ divBoundary S p.1) :
    (Sum.inr (Sum.inl p) : AuxCoreEdge α β β') ∈ E(auxCoreGraph hC hv₀) :=
  Or.inl (Or.inr ⟨Sum.inl p, ⟨p, ⟨hpA, hp3, hpu⟩, rfl⟩, rfl⟩)

theorem inr_inr_mem_edgeSet_auxCoreGraph {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) {v₀ : α} (hv₀ : v₀ ∈ V(C))
    {A : Graph α β} (hA : A ∈ coreDivision S C) (hle1 : (divBoundary S A).ncard ≤ 1) :
    (Sum.inr (Sum.inr A) : AuxCoreEdge α β β') ∈ E(auxCoreGraph hC hv₀) :=
  Or.inr ⟨Sum.inr A, ⟨A, ⟨hA, hle1⟩, rfl⟩, rfl⟩

/-- If `S` has no cross and `C` is a 4-linked core of `S`, then `coreDivision S C` is a rural
division of `S` (Graph Minors XIII, Section 8, (8.6), pages 96–97). -/
theorem isRuralDivision_coreDivision {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) (hnocross : ¬ HasCross S) :
    IsRuralDivision S (coreDivision S C) := by
  have hdiv : IsSocietyDivision S (coreDivision S C) := isSocietyDivision_coreDivision hC
  have hfin_𝒜 : (coreDivision S C).Finite := hdiv.finite
  let 𝒜 := coreDivision S C
  let B := divisionBipartiteGraph S 𝒜
  have htot_eq : divTotalBoundary S 𝒜 ∪ S.Ω.bar = V(C) :=
    divTotalBoundary_union_bar_coreDivision_eq hC
  have hfin_C : V(C).Finite := S.finite_V.subset hC.isCore.isTrisecting.subset_V
  have hV_B_eq : V(B) = (Sum.inl '' 𝒜) ∪ (Sum.inr '' V(C)) := by
    change (Sum.inl '' 𝒜) ∪ (Sum.inr '' (divTotalBoundary S 𝒜 ∪ S.Ω.bar)) = _
    rw [htot_eq]
  have hV_fin : V(B).Finite := by
    rw [hV_B_eq]
    exact (hfin_𝒜.image Sum.inl).union (hfin_C.image Sum.inr)
  have hE_fin : E(B).Finite := by
    refine (hfin_𝒜.prod hfin_C).subset ?_
    rintro ⟨A, u⟩ ⟨hA, hu⟩
    exact ⟨hA, (boundary_isClique_in_core hC hA).1 hu⟩
  have hbar_sub : (liftCyclicPermInr S.Ω).bar ⊆ V(B) := by
    rw [hV_B_eq]
    rintro _ ⟨u, hu, rfl⟩
    exact Or.inr ⟨u, hC.isCore.isTrisecting.bar_subset hu, rfl⟩
  refine ⟨hdiv, hfin_𝒜, hV_fin, hE_fin, hbar_sub, ?_⟩
  let S_B : Society (Graph α β ⊕ α) (Graph α β × α) :=
    Society.mk B (liftCyclicPermInr S.Ω) hV_fin hE_fin hbar_sub
  by_cases hVC_ne : V(C).Nonempty
  · obtain ⟨v₀, hv₀⟩ := hVC_ne
    obtain ⟨Γ₀, Δ, φ, hΔ, hcw₀, hU₀_Δ, hU₀_inter_bd, hbd₀, hagrees₀⟩ :=
      exists_clean_disc_drawing_of_isRuralSociety (auxCoreSociety hC hv₀)
        (isRuralSociety_auxCoreSociety hC hv₀ hnocross)
    let G₀ := auxCoreGraph hC hv₀
    let ν₀ : (Graph α β ⊕ α) → EuclideanPlane := fun z =>
      if hz : z ∈ V(G₀) then (Γ₀.iso.vertexEquiv ⟨z, hz⟩).1 else 0
    have hν₀_V : ∀ z ∈ V(G₀), ν₀ z ∈ Γ₀.drawing.V := fun z hz => by
      simp only [ν₀, hz, ↓reduceDIte]
      exact (Γ₀.iso.vertexEquiv ⟨z, hz⟩).2
    have hν₀_inj : InjOn ν₀ V(G₀) := by
      intro z₁ hz₁ z₂ hz₂ heq
      simp only [ν₀, hz₁, hz₂, ↓reduceDIte] at heq
      exact congrArg Subtype.val (Γ₀.iso.vertexEquiv.injective (Subtype.ext heq))
    -- Assign to each `A ∈ 𝒜` with `|∂A| ≤ 2` its carrier edge `c_A ∈ E(G₀)`
    let carrierEdge (A : Graph α β) (hA : A ∈ 𝒜) (hle2 : (divBoundary S A).ncard ≤ 2) :
        E(G₀) :=
      if h2 : (divBoundary S A).ncard = 2 then
        ⟨Sum.inl (coreTwoBoundaryData hC hA h2).1.2,
          inl_mem_edgeSet_auxCoreGraph hC hv₀
            (coreTwoBoundaryData hC hA h2).2.2.2.edge_mem⟩
      else
        ⟨Sum.inr (Sum.inr A),
          inr_inr_mem_edgeSet_auxCoreGraph hC hv₀ hA (by omega)⟩
    have hcarrierEdge_inj :
        ∀ (A₁ : Graph α β) (hA₁ : A₁ ∈ 𝒜) (hle₁ : (divBoundary S A₁).ncard ≤ 2)
          (A₂ : Graph α β) (hA₂ : A₂ ∈ 𝒜) (hle₂ : (divBoundary S A₂).ncard ≤ 2),
          carrierEdge A₁ hA₁ hle₁ = carrierEdge A₂ hA₂ hle₂ → A₁ = A₂ := by
      intro A₁ hA₁ hle₁ A₂ hA₂ hle₂ heq
      have hval := congrArg Subtype.val heq
      dsimp [carrierEdge] at hval
      split_ifs at hval with h2₁ h2₂ h2₂
      · have he_eq : (coreTwoBoundaryData hC hA₁ h2₁).1.2 =
            (coreTwoBoundaryData hC hA₂ h2₂).1.2 := Sum.inl.inj hval
        have hl₁ := (coreTwoBoundaryData hC hA₁ h2₁).2.2.2
        have hl₂ := he_eq ▸ (coreTwoBoundaryData hC hA₂ h2₂).2.2.2
        have hbd₁ := (coreTwoBoundaryData hC hA₁ h2₁).2.2.1
        have hbd₂ := (coreTwoBoundaryData hC hA₂ h2₂).2.2.1
        have hpair : ({(coreTwoBoundaryData hC hA₁ h2₁).1.1.1,
            (coreTwoBoundaryData hC hA₁ h2₁).1.1.2} : Set α) =
            {(coreTwoBoundaryData hC hA₂ h2₂).1.1.1,
            (coreTwoBoundaryData hC hA₂ h2₂).1.1.2} := by
          rcases hl₁.eq_and_eq_or_eq_and_eq hl₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, pair_comm]
        exact hdiv.boundary_injOn hA₁ hA₂ (hbd₁.trans (hpair.trans hbd₂.symm))
      · exact Sum.inr.inj (Sum.inr.inj hval)
    -- For each `A ∈ 𝒜` with `|∂A| ≤ 2`, pick `m_A` in the open edge of `carrierEdge`
    let openCarrier (A : Graph α β) (hA : A ∈ 𝒜) (hle2 : (divBoundary S A).ncard ≤ 2) :
        Γ₀.drawing.E :=
      Γ₀.iso.edgeEquiv (carrierEdge A hA hle2)
    let midPt (A : Graph α β) (hA : A ∈ 𝒜) (hle2 : (divBoundary S A).ncard ≤ 2) :
        EuclideanPlane :=
      (openCarrier A hA hle2).2.1.some
    have hmidPt_mem (A : Graph α β) (hA : A ∈ 𝒜) (hle2 : (divBoundary S A).ncard ≤ 2) :
        midPt A hA hle2 ∈ (openCarrier A hA hle2).1 :=
      (openCarrier A hA hle2).2.1.some_mem
    -- Define the vertex placement `ν` on `Graph α β ⊕ α`
    let ν : (Graph α β ⊕ α) → EuclideanPlane := fun z =>
      match z with
      | Sum.inr u => ν₀ (Sum.inr u)
      | Sum.inl A =>
        if hA : A ∈ 𝒜 then
          if hle2 : (divBoundary S A).ncard ≤ 2 then
            midPt A hA hle2
          else
            ν₀ (Sum.inl A)
        else 0
    have hν_inr : ∀ u : α, ν (Sum.inr u) = ν₀ (Sum.inr u) := fun _ => rfl
    have hν_inl_three : ∀ (A : Graph α β) (hA : A ∈ 𝒜), (divBoundary S A).ncard = 3 →
        ν (Sum.inl A) = ν₀ (Sum.inl A) := by
      intro A hA h3
      have hnot : ¬ (divBoundary S A).ncard ≤ 2 := by omega
      simp [ν, hA, hnot]
    have hν_inl_le2 : ∀ (A : Graph α β) (hA : A ∈ 𝒜) (hle2 : (divBoundary S A).ncard ≤ 2),
        ν (Sum.inl A) = midPt A hA hle2 := by
      intro A hA hle2
      simp [ν, hA, hle2]
    have hν_mem_U₀ : ∀ z ∈ V(B), ν z ∈ Γ₀.drawing.U := by
      rw [hV_B_eq]
      rintro z (⟨A, hA, rfl⟩ | ⟨u, huC, rfl⟩)
      · by_cases hle2 : (divBoundary S A).ncard ≤ 2
        · rw [hν_inl_le2 A hA hle2]
          exact ((openCarrier A hA hle2).2.2.1 (hmidPt_mem A hA hle2)).1
        · have h3 : (divBoundary S A).ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA; omega
          rw [hν_inl_three A hA h3]
          exact Γ₀.drawing.V_subset_U (hν₀_V (Sum.inl A) (Or.inl ⟨A, ⟨hA, h3⟩, rfl⟩))
      · exact Γ₀.drawing.V_subset_U (hν₀_V (Sum.inr u) (Or.inr ⟨u, huC, rfl⟩))
    have hν_inj : InjOn ν V(B) := by
      rw [hV_B_eq]
      rintro z₁ (⟨A₁, hA₁, rfl⟩ | ⟨u₁, hu₁, rfl⟩) z₂ (⟨A₂, hA₂, rfl⟩ | ⟨u₂, hu₂, rfl⟩) heq
      · by_cases hle₁ : (divBoundary S A₁).ncard ≤ 2 <;>
          by_cases hle₂ : (divBoundary S A₂).ncard ≤ 2
        · rw [hν_inl_le2 A₁ hA₁ hle₁, hν_inl_le2 A₂ hA₂ hle₂] at heq
          have hm₁ := hmidPt_mem A₁ hA₁ hle₁
          have hm₂ : midPt A₁ hA₁ hle₁ ∈ (openCarrier A₂ hA₂ hle₂).1 :=
            heq ▸ hmidPt_mem A₂ hA₂ hle₂
          have ha_eq : (openCarrier A₁ hA₁ hle₁).1 = (openCarrier A₂ hA₂ hle₂).1 :=
            Γ₀.drawing.edge_eq_of_mem (openCarrier A₁ hA₁ hle₁).2
              (openCarrier A₂ hA₂ hle₂).2 hm₁ hm₂
          have hc_eq : carrierEdge A₁ hA₁ hle₁ = carrierEdge A₂ hA₂ hle₂ :=
            Γ₀.iso.edgeEquiv.injective (Subtype.ext ha_eq)
          exact congrArg Sum.inl (hcarrierEdge_inj A₁ hA₁ hle₁ A₂ hA₂ hle₂ hc_eq)
        · exfalso
          have h3₂ : (divBoundary S A₂).ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA₂; omega
          rw [hν_inl_le2 A₁ hA₁ hle₁, hν_inl_three A₂ hA₂ h3₂] at heq
          have hm_not_V : midPt A₁ hA₁ hle₁ ∉ Γ₀.drawing.V :=
            ((openCarrier A₁ hA₁ hle₁).2.2.1 (hmidPt_mem A₁ hA₁ hle₁)).2
          exact hm_not_V (heq ▸ hν₀_V (Sum.inl A₂) (Or.inl ⟨A₂, ⟨hA₂, h3₂⟩, rfl⟩))
        · exfalso
          have h3₁ : (divBoundary S A₁).ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA₁; omega
          rw [hν_inl_three A₁ hA₁ h3₁, hν_inl_le2 A₂ hA₂ hle₂] at heq
          have hm_not_V : midPt A₂ hA₂ hle₂ ∉ Γ₀.drawing.V :=
            ((openCarrier A₂ hA₂ hle₂).2.2.1 (hmidPt_mem A₂ hA₂ hle₂)).2
          exact hm_not_V (heq.symm ▸ hν₀_V (Sum.inl A₁) (Or.inl ⟨A₁, ⟨hA₁, h3₁⟩, rfl⟩))
        · have h3₁ : (divBoundary S A₁).ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA₁; omega
          have h3₂ : (divBoundary S A₂).ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA₂; omega
          rw [hν_inl_three A₁ hA₁ h3₁, hν_inl_three A₂ hA₂ h3₂] at heq
          exact hν₀_inj (Or.inl ⟨A₁, ⟨hA₁, h3₁⟩, rfl⟩) (Or.inl ⟨A₂, ⟨hA₂, h3₂⟩, rfl⟩) heq
      · exfalso
        by_cases hle₁ : (divBoundary S A₁).ncard ≤ 2
        · rw [hν_inl_le2 A₁ hA₁ hle₁, hν_inr] at heq
          have hm_not_V : midPt A₁ hA₁ hle₁ ∉ Γ₀.drawing.V :=
            ((openCarrier A₁ hA₁ hle₁).2.2.1 (hmidPt_mem A₁ hA₁ hle₁)).2
          exact hm_not_V (heq ▸ hν₀_V (Sum.inr u₂) (Or.inr ⟨u₂, hu₂, rfl⟩))
        · have h3₁ : (divBoundary S A₁).ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA₁; omega
          rw [hν_inl_three A₁ hA₁ h3₁, hν_inr] at heq
          exact nomatch (hν₀_inj (Or.inl ⟨A₁, ⟨hA₁, h3₁⟩, rfl⟩)
            (Or.inr ⟨u₂, hu₂, rfl⟩) heq)
      · exfalso
        by_cases hle₂ : (divBoundary S A₂).ncard ≤ 2
        · rw [hν_inr, hν_inl_le2 A₂ hA₂ hle₂] at heq
          have hm_not_V : midPt A₂ hA₂ hle₂ ∉ Γ₀.drawing.V :=
            ((openCarrier A₂ hA₂ hle₂).2.2.1 (hmidPt_mem A₂ hA₂ hle₂)).2
          exact hm_not_V (heq.symm ▸ hν₀_V (Sum.inr u₁) (Or.inr ⟨u₁, hu₁, rfl⟩))
        · have h3₂ : (divBoundary S A₂).ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA₂; omega
          rw [hν_inr, hν_inl_three A₂ hA₂ h3₂] at heq
          exact nomatch (hν₀_inj (Or.inr ⟨u₁, hu₁, rfl⟩)
            (Or.inl ⟨A₂, ⟨hA₂, h3₂⟩, rfl⟩) heq)
      · exact hν₀_inj (Or.inr ⟨u₁, hu₁, rfl⟩) (Or.inr ⟨u₂, hu₂, rfl⟩) heq
    -- Now construct the edge lines `K e` for each `e = (A, u) ∈ E(B)`
    -- First, for `A ∈ 𝒜` with `|∂A| = 2`, split `openCarrier A` at `midPt A`
    have hsplit_two : ∀ (A : Graph α β) (hA : A ∈ 𝒜) (h2 : (divBoundary S A).ncard = 2),
        let d := coreTwoBoundaryData hC hA h2
        let a := (openCarrier A hA (by omega)).1
        ∃ L₁ L₂ : Set EuclideanPlane,
          IsLineWithEnds L₁ (midPt A hA (by omega)) (ν₀ (Sum.inr d.1.1.1)) ∧
          IsLineWithEnds L₂ (midPt A hA (by omega)) (ν₀ (Sum.inr d.1.1.2)) ∧
          L₁ ⊆ closure a ∧
          L₂ ⊆ closure a ∧
          L₁ \ {midPt A hA (by omega), ν₀ (Sum.inr d.1.1.1)} ⊆ a \ {midPt A hA (by omega)} ∧
          L₂ \ {midPt A hA (by omega), ν₀ (Sum.inr d.1.1.2)} ⊆ a \ {midPt A hA (by omega)} ∧
          Disjoint (L₁ \ {midPt A hA (by omega), ν₀ (Sum.inr d.1.1.1)})
            (L₂ \ {midPt A hA (by omega), ν₀ (Sum.inr d.1.1.2)}) := by
      intro A hA h2 d a
      have hl_C : C.IsLink d.1.2 d.1.1.1 d.1.1.2 := d.2.2.2
      have huC : d.1.1.1 ∈ V(C) := hl_C.left_mem
      have hvC : d.1.1.2 ∈ V(C) := hl_C.right_mem
      have huG₀ : (Sum.inr d.1.1.1 : Graph α β ⊕ α) ∈ V(G₀) := Or.inr ⟨d.1.1.1, huC, rfl⟩
      have hvG₀ : (Sum.inr d.1.1.2 : Graph α β ⊕ α) ∈ V(G₀) := Or.inr ⟨d.1.1.2, hvC, rfl⟩
      have hc_eq : (carrierEdge A hA (by omega)).1 = Sum.inl d.1.2 := by
        simp [carrierEdge, h2, d]
      have hl_G₀ : G₀.IsLink (carrierEdge A hA (by omega)).1
          (Sum.inr d.1.1.1) (Sum.inr d.1.1.2) := by
        rw [hc_eq]
        exact ⟨d.1.1.1, d.1.1.2, hl_C, rfl, rfl⟩
      have hlink_D := (Γ₀.iso.isLink_iff (e := carrierEdge A hA (by omega))
        (x := ⟨Sum.inr d.1.1.1, huG₀⟩) (y := ⟨Sum.inr d.1.1.2, hvG₀⟩)).mp hl_G₀
      have hcap : closure a ∩ Γ₀.drawing.V =
          {ν₀ (Sum.inr d.1.1.1), ν₀ (Sum.inr d.1.1.2)} := by
        simpa [a, openCarrier, ν₀, huG₀, hvG₀] using hlink_D.2.2.2
      have hxy : ν₀ (Sum.inr d.1.1.1) ≠ ν₀ (Sum.inr d.1.1.2) := fun h =>
        d.2.1 (Sum.inr.inj (hν₀_inj huG₀ hvG₀ h))
      exact split_drawing_edge_of_isLine (openCarrier A hA (by omega)).2
        hxy hcap (hmidPt_mem A hA (by omega))
    -- Second, for `A ∈ 𝒜` with `|∂A| = 1`, take half-arc of `openCarrier A` at `midPt A`
    have hhalf_one : ∀ (A : Graph α β) (hA : A ∈ 𝒜) (h1 : (divBoundary S A).ncard = 1),
        let a := (openCarrier A hA (by omega)).1
        ∃ L : Set EuclideanPlane,
          IsLineWithEnds L (midPt A hA (by omega)) (ν₀ (Sum.inr (loopVertex S v₀ A))) ∧
          L ⊆ closure a ∧
          L \ {midPt A hA (by omega), ν₀ (Sum.inr (loopVertex S v₀ A))} ⊆
            a \ {midPt A hA (by omega)} := by
      intro A hA h1 a
      have huC : loopVertex S v₀ A ∈ V(C) := loopVertex_mem_core hC hv₀ hA
      have huG₀ : (Sum.inr (loopVertex S v₀ A) : Graph α β ⊕ α) ∈ V(G₀) :=
        Or.inr ⟨loopVertex S v₀ A, huC, rfl⟩
      have hnot2 : ¬ (divBoundary S A).ncard = 2 := by omega
      have hc_eq : (carrierEdge A hA (by omega)).1 = Sum.inr (Sum.inr A) := by
        simp [carrierEdge, hnot2]
      have hl_G₀ : G₀.IsLink (carrierEdge A hA (by omega)).1
          (Sum.inr (loopVertex S v₀ A)) (Sum.inr (loopVertex S v₀ A)) := by
        rw [hc_eq]
        exact ⟨hA, by omega, rfl, rfl⟩
      have hlink_D := (Γ₀.iso.isLink_iff (e := carrierEdge A hA (by omega))
        (x := ⟨Sum.inr (loopVertex S v₀ A), huG₀⟩)
        (y := ⟨Sum.inr (loopVertex S v₀ A), huG₀⟩)).mp hl_G₀
      have hcap : closure a ∩ Γ₀.drawing.V = {ν₀ (Sum.inr (loopVertex S v₀ A))} := by
        have h := hlink_D.2.2.2
        rw [pair_eq_singleton] at h
        simpa [a, openCarrier, ν₀, huG₀] using h
      exact half_drawing_edge_of_loop (openCarrier A hA (by omega)).2
        hcap (hmidPt_mem A hA (by omega))
    -- Define the line `K e` and ambient open edge `ambEdge e he` for each `e = (A, u) ∈ E(B)`
    let K : Graph α β × α → Set EuclideanPlane := fun e =>
      if hA : e.1 ∈ 𝒜 then
        if h1 : (divBoundary S e.1).ncard = 1 then
          Classical.choose (hhalf_one e.1 hA h1)
        else if h2 : (divBoundary S e.1).ncard = 2 then
          if e.2 = (coreTwoBoundaryData hC hA h2).1.1.1 then
            Classical.choose (hsplit_two e.1 hA h2)
          else
            Classical.choose (Classical.choose_spec (hsplit_two e.1 hA h2))
        else if h3 : (divBoundary S e.1).ncard = 3 then
          if hu : e.2 ∈ divBoundary S e.1 then
            closure (Γ₀.iso.edgeEquiv
              ⟨Sum.inr (Sum.inl e), inr_inl_mem_edgeSet_auxCoreGraph hC hv₀ hA h3 hu⟩).1
          else ∅
        else ∅
      else ∅
    let ambEdge (e : Graph α β × α) (he : e ∈ E(B)) : E(G₀) :=
      if hle2 : (divBoundary S e.1).ncard ≤ 2 then
        carrierEdge e.1 he.1 hle2
      else
        ⟨Sum.inr (Sum.inl e), inr_inl_mem_edgeSet_auxCoreGraph hC hv₀ he.1
          (by have := hdiv.boundary_ncard_le_three he.1; omega) he.2⟩
    have hK_props : ∀ (e : Graph α β × α) (he : e ∈ E(B)),
        IsLineWithEnds (K e) (ν (Sum.inl e.1)) (ν (Sum.inr e.2)) ∧
        K e ⊆ closure (Γ₀.iso.edgeEquiv (ambEdge e he)).1 ∧
        K e \ {ν (Sum.inl e.1), ν (Sum.inr e.2)} ⊆ (Γ₀.iso.edgeEquiv (ambEdge e he)).1 ∧
        (∀ (A' : Graph α β) (hA' : A' ∈ 𝒜) (hle' : (divBoundary S A').ncard ≤ 2),
          midPt A' hA' hle' ∉ K e \ {ν (Sum.inl e.1), ν (Sum.inr e.2)}) := by
      rintro ⟨A, u⟩ he
      have hA : A ∈ 𝒜 := he.1
      have hu_bd : u ∈ divBoundary S A := he.2
      have hle3 : (divBoundary S A).ncard ≤ 3 := hdiv.boundary_ncard_le_three hA
      have hne0 : (divBoundary S A).ncard ≠ 0 :=
        ((ncard_pos (hfin_C.subset (boundary_isClique_in_core hC hA).1)).mpr ⟨u, hu_bd⟩).ne'
      have hcases : (divBoundary S A).ncard = 1 ∨ (divBoundary S A).ncard = 2 ∨
          (divBoundary S A).ncard = 3 := by omega
      rcases hcases with h1 | h2 | h3
      · have hle2 : (divBoundary S A).ncard ≤ 2 := by omega
        have hspec := Classical.choose_spec (hhalf_one A hA h1)
        have hK_eq : K (A, u) = Classical.choose (hhalf_one A hA h1) := by
          simp only [K, hA, h1, ↓reduceDIte]
        have hamb_eq : ambEdge (A, u) he = carrierEdge A hA hle2 := by
          simp only [ambEdge, hle2, ↓reduceDIte]
        have hu_eq : u = loopVertex S v₀ A :=
          mem_singleton_iff.mp (divBoundary_eq_singleton_loopVertex v₀ h1 ▸ hu_bd)
        rw [hK_eq, hamb_eq, hν_inl_le2 A hA hle2, hν_inr, hu_eq]
        refine ⟨hspec.1, hspec.2.1, hspec.2.2.trans sdiff_subset, ?_⟩
        intro A' hA' hle' hm_in
        have hm_in' := hspec.2.2 hm_in
        by_cases hAA' : A' = A
        · subst hAA'; exact hm_in'.2 rfl
        · have ha_eq : (openCarrier A' hA' hle').1 = (openCarrier A hA hle2).1 :=
            Γ₀.drawing.edge_eq_of_mem (openCarrier A' hA' hle').2
              (openCarrier A hA hle2).2 (hmidPt_mem A' hA' hle') hm_in'.1
          exact hAA' (hcarrierEdge_inj A' hA' hle' A hA hle2
            (Γ₀.iso.edgeEquiv.injective (Subtype.ext ha_eq)))
      · have hle2 : (divBoundary S A).ncard ≤ 2 := by omega
        have hspec := Classical.choose_spec (Classical.choose_spec (hsplit_two A hA h2))
        let d := coreTwoBoundaryData hC hA h2
        have hamb_eq : ambEdge (A, u) he = carrierEdge A hA hle2 := by
          simp only [ambEdge, hle2, ↓reduceDIte]
        have hu_pair : u = d.1.1.1 ∨ u = d.1.1.2 := by
          have : u ∈ ({d.1.1.1, d.1.1.2} : Set α) := d.2.2.1 ▸ hu_bd
          simpa using this
        rcases hu_pair with hu_eq | hu_eq
        · have hK_eq : K (A, u) = Classical.choose (hsplit_two A hA h2) := by
            simp only [K, hA, h2, d, hu_eq, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
          rw [hK_eq, hamb_eq, hν_inl_le2 A hA hle2, hν_inr, hu_eq]
          refine ⟨hspec.1, hspec.2.2.1, hspec.2.2.2.2.1.trans sdiff_subset, ?_⟩
          intro A' hA' hle' hm_in
          have hm_in' := hspec.2.2.2.2.1 hm_in
          by_cases hAA' : A' = A
          · subst hAA'; exact hm_in'.2 rfl
          · have ha_eq : (openCarrier A' hA' hle').1 = (openCarrier A hA hle2).1 :=
              Γ₀.drawing.edge_eq_of_mem (openCarrier A' hA' hle').2
                (openCarrier A hA hle2).2 (hmidPt_mem A' hA' hle') hm_in'.1
            exact hAA' (hcarrierEdge_inj A' hA' hle' A hA hle2
              (Γ₀.iso.edgeEquiv.injective (Subtype.ext ha_eq)))
        · have hne_u : d.1.1.2 ≠ d.1.1.1 := d.2.1.symm
          have hK_eq : K (A, u) =
              Classical.choose (Classical.choose_spec (hsplit_two A hA h2)) := by
            simp only [K, hA, h2, d, hu_eq, hne_u, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
          rw [hK_eq, hamb_eq, hν_inl_le2 A hA hle2, hν_inr, hu_eq]
          refine ⟨hspec.2.1, hspec.2.2.2.1, hspec.2.2.2.2.2.1.trans sdiff_subset, ?_⟩
          intro A' hA' hle' hm_in
          have hm_in' := hspec.2.2.2.2.2.1 hm_in
          by_cases hAA' : A' = A
          · subst hAA'; exact hm_in'.2 rfl
          · have ha_eq : (openCarrier A' hA' hle').1 = (openCarrier A hA hle2).1 :=
              Γ₀.drawing.edge_eq_of_mem (openCarrier A' hA' hle').2
                (openCarrier A hA hle2).2 (hmidPt_mem A' hA' hle') hm_in'.1
            exact hAA' (hcarrierEdge_inj A' hA' hle' A hA hle2
              (Γ₀.iso.edgeEquiv.injective (Subtype.ext ha_eq)))
      · have hnot_le2 : ¬ (divBoundary S A).ncard ≤ 2 := by omega
        let c : E(G₀) := ⟨Sum.inr (Sum.inl (A, u)),
          inr_inl_mem_edgeSet_auxCoreGraph hC hv₀ hA h3 hu_bd⟩
        have hamb_eq : ambEdge (A, u) he = c := by
          simp only [ambEdge, hnot_le2, c, ↓reduceDIte]
        have hK_eq : K (A, u) = closure (Γ₀.iso.edgeEquiv c).1 := by
          simp only [K, hA, h3, hu_bd, c, Nat.reduceEqDiff, ↓reduceDIte]; rfl
        let a := (Γ₀.iso.edgeEquiv c).1
        have hA_G₀ : (Sum.inl A : Graph α β ⊕ α) ∈ V(G₀) := Or.inl ⟨A, ⟨hA, h3⟩, rfl⟩
        have hu_G₀ : (Sum.inr u : Graph α β ⊕ α) ∈ V(G₀) :=
          Or.inr ⟨u, (boundary_isClique_in_core hC hA).1 hu_bd, rfl⟩
        have hl_G₀ : G₀.IsLink c.1 (Sum.inl A) (Sum.inr u) :=
          ⟨hA, h3, hu_bd, Or.inl ⟨rfl, rfl⟩⟩
        have hlink_D := (Γ₀.iso.isLink_iff (e := c) (x := ⟨Sum.inl A, hA_G₀⟩)
          (y := ⟨Sum.inr u, hu_G₀⟩)).mp hl_G₀
        have hcap : closure a ∩ Γ₀.drawing.V = {ν₀ (Sum.inl A), ν₀ (Sum.inr u)} := by
          simpa [a, ν₀, hA_G₀, hu_G₀] using hlink_D.2.2.2
        have hxy : ν₀ (Sum.inl A) ≠ ν₀ (Sum.inr u) := fun h =>
          nomatch (hν₀_inj hA_G₀ hu_G₀ h)
        have hL : IsLineWithEnds (closure a) (ν₀ (Sum.inl A)) (ν₀ (Sum.inr u)) :=
          isLine_closure (Γ₀.iso.edgeEquiv c).2 hxy hcap
        have hcl_diff : closure a \ Γ₀.drawing.V = a :=
          Γ₀.drawing.closure_diff_V (Γ₀.iso.edgeEquiv c).2
        have hint_sub : closure a \ {ν (Sum.inl A), ν (Sum.inr u)} ⊆ a := by
          rw [hν_inl_three A hA h3, hν_inr]
          rintro z ⟨hz_cl, hz_ne⟩
          have hz_not_V : z ∉ Γ₀.drawing.V := fun hzV => hz_ne (hcap ▸ ⟨hz_cl, hzV⟩)
          exact hcl_diff ▸ ⟨hz_cl, hz_not_V⟩
        rw [hK_eq, hamb_eq]
        refine ⟨?_, Subset.rfl, hint_sub, ?_⟩
        · rwa [hν_inl_three A hA h3, hν_inr]
        · intro A' hA' hle' hm_in
          have hm_a : midPt A' hA' hle' ∈ a := hint_sub hm_in
          have ha_eq : (openCarrier A' hA' hle').1 = a :=
            Γ₀.drawing.edge_eq_of_mem (openCarrier A' hA' hle').2
              (Γ₀.iso.edgeEquiv c).2 (hmidPt_mem A' hA' hle') hm_a
          have hc_eq : carrierEdge A' hA' hle' = c :=
            Γ₀.iso.edgeEquiv.injective (Subtype.ext ha_eq)
          have hval := congrArg Subtype.val hc_eq
          by_cases h2' : (divBoundary S A').ncard = 2 <;> simp [carrierEdge, c, h2'] at hval
    have hdisj_V : ∀ e ∈ E(B),
        Disjoint (K e \ {ν (Sum.inl e.1), ν (Sum.inr e.2)}) (ν '' V(B)) := by
      intro e he
      rw [disjoint_left]
      rintro z hz_int ⟨w, hwB, rfl⟩
      have hprop := hK_props e he
      have hz_amb : ν w ∈ (Γ₀.iso.edgeEquiv (ambEdge e he)).1 := hprop.2.2.1 hz_int
      have hz_not_V₀ : ν w ∉ Γ₀.drawing.V :=
        ((Γ₀.iso.edgeEquiv (ambEdge e he)).2.2.1 hz_amb).2
      rw [hV_B_eq] at hwB
      rcases hwB with ⟨A', hA', rfl⟩ | ⟨u', hu', rfl⟩
      · by_cases hle' : (divBoundary S A').ncard ≤ 2
        · rw [hν_inl_le2 A' hA' hle'] at hz_int
          exact hprop.2.2.2 A' hA' hle' hz_int
        · have h3' : (divBoundary S A').ncard = 3 := by
            have := hdiv.boundary_ncard_le_three hA'; omega
          rw [hν_inl_three A' hA' h3'] at hz_not_V₀
          exact hz_not_V₀ (hν₀_V (Sum.inl A') (Or.inl ⟨A', ⟨hA', h3'⟩, rfl⟩))
      · exact hz_not_V₀ (hν₀_V (Sum.inr u') (Or.inr ⟨u', hu', rfl⟩))
    have hdisj_E : ∀ e₁ ∈ E(B), ∀ e₂ ∈ E(B), e₁ ≠ e₂ →
        Disjoint (K e₁ \ {ν (Sum.inl e₁.1), ν (Sum.inr e₁.2)})
          (K e₂ \ {ν (Sum.inl e₂.1), ν (Sum.inr e₂.2)}) := by
      intro e₁ he₁ e₂ he₂ hne
      rw [disjoint_left]
      intro z hz₁ hz₂
      have hprop₁ := hK_props e₁ he₁
      have hprop₂ := hK_props e₂ he₂
      have hz_amb₁ : z ∈ (Γ₀.iso.edgeEquiv (ambEdge e₁ he₁)).1 := hprop₁.2.2.1 hz₁
      have hz_amb₂ : z ∈ (Γ₀.iso.edgeEquiv (ambEdge e₂ he₂)).1 := hprop₂.2.2.1 hz₂
      have ha_eq : (Γ₀.iso.edgeEquiv (ambEdge e₁ he₁)).1 =
          (Γ₀.iso.edgeEquiv (ambEdge e₂ he₂)).1 :=
        Γ₀.drawing.edge_eq_of_mem (Γ₀.iso.edgeEquiv (ambEdge e₁ he₁)).2
          (Γ₀.iso.edgeEquiv (ambEdge e₂ he₂)).2 hz_amb₁ hz_amb₂
      have hamb_eq : ambEdge e₁ he₁ = ambEdge e₂ he₂ :=
        Γ₀.iso.edgeEquiv.injective (Subtype.ext ha_eq)
      have hval := congrArg Subtype.val hamb_eq
      dsimp [ambEdge] at hval
      split_ifs at hval with hle₁ hle₂ hle₂
      · have hA_eq : e₁.1 = e₂.1 :=
          hcarrierEdge_inj e₁.1 he₁.1 hle₁ e₂.1 he₂.1 hle₂ (Subtype.ext hval)
        rcases e₁ with ⟨A, u₁⟩
        rcases e₂ with ⟨A₂, u₂⟩
        dsimp at hA_eq
        subst hA_eq
        have hA : A ∈ 𝒜 := he₁.1
        have hu₁_bd : u₁ ∈ divBoundary S A := he₁.2
        have hu₂_bd : u₂ ∈ divBoundary S A := he₂.2
        have hle_A : (divBoundary S A).ncard ≤ 2 := hle₁
        have hu_ne : u₁ ≠ u₂ := fun h => hne (congrArg (Prod.mk A) h)
        have hnot1 : ¬ (divBoundary S A).ncard = 1 := by
          intro h1
          have hbd1 := divBoundary_eq_singleton_loopVertex v₀ h1
          have hu₁_eq : u₁ = loopVertex S v₀ A := mem_singleton_iff.mp (hbd1 ▸ hu₁_bd)
          have hu₂_eq : u₂ = loopVertex S v₀ A := mem_singleton_iff.mp (hbd1 ▸ hu₂_bd)
          exact hu_ne (hu₁_eq.trans hu₂_eq.symm)
        have h2 : (divBoundary S A).ncard = 2 := by
          have hne0 : (divBoundary S A).ncard ≠ 0 :=
            ((ncard_pos (hfin_C.subset (boundary_isClique_in_core hC hA).1)).mpr
              ⟨u₁, hu₁_bd⟩).ne'
          omega
        let d := coreTwoBoundaryData hC hA h2
        have hspec := Classical.choose_spec (Classical.choose_spec (hsplit_two A hA h2))
        have hu₁_pair : u₁ = d.1.1.1 ∨ u₁ = d.1.1.2 := by
          have : u₁ ∈ ({d.1.1.1, d.1.1.2} : Set α) := d.2.2.1 ▸ hu₁_bd
          simpa using this
        have hu₂_pair : u₂ = d.1.1.1 ∨ u₂ = d.1.1.2 := by
          have : u₂ ∈ ({d.1.1.1, d.1.1.2} : Set α) := d.2.2.1 ▸ hu₂_bd
          simpa using this
        rcases hu₁_pair with hu₁_eq | hu₁_eq <;> rcases hu₂_pair with hu₂_eq | hu₂_eq
        · exact hu_ne (hu₁_eq.trans hu₂_eq.symm)
        · have hne_d : d.1.1.2 ≠ d.1.1.1 := d.2.1.symm
          have hK₁ : K (A, u₁) = Classical.choose (hsplit_two A hA h2) := by
            simp only [K, hA, h2, d, hu₁_eq, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
          have hK₂ : K (A, u₂) =
              Classical.choose (Classical.choose_spec (hsplit_two A hA h2)) := by
            simp only [K, hA, h2, d, hu₂_eq, hne_d, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
          rw [hK₁, hν_inl_le2 A hA hle_A, hν_inr, hu₁_eq] at hz₁
          rw [hK₂, hν_inl_le2 A hA hle_A, hν_inr, hu₂_eq] at hz₂
          exact disjoint_left.mp hspec.2.2.2.2.2.2 hz₁ hz₂
        · have hne_d : d.1.1.2 ≠ d.1.1.1 := d.2.1.symm
          have hK₁ : K (A, u₁) =
              Classical.choose (Classical.choose_spec (hsplit_two A hA h2)) := by
            simp only [K, hA, h2, d, hu₁_eq, hne_d, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
          have hK₂ : K (A, u₂) = Classical.choose (hsplit_two A hA h2) := by
            simp only [K, hA, h2, d, hu₂_eq, Nat.reduceEqDiff, ↓reduceDIte, ↓reduceIte]
          rw [hK₁, hν_inl_le2 A hA hle_A, hν_inr, hu₁_eq] at hz₁
          rw [hK₂, hν_inl_le2 A hA hle_A, hν_inr, hu₂_eq] at hz₂
          exact disjoint_right.mp hspec.2.2.2.2.2.2 hz₁ hz₂
        · exact hu_ne (hu₁_eq.trans hu₂_eq.symm)
      · by_cases h2₁ : (divBoundary S e₁.1).ncard = 2 <;> simp [carrierEdge, h2₁] at hval
      · by_cases h2₂ : (divBoundary S e₂.1).ncard = 2 <;> simp [carrierEdge, h2₂] at hval
      · exact hne (Sum.inl.inj (Sum.inr.inj hval))
    have hends : ∀ e ∈ E(B),
        (Sum.inl e.1 : Graph α β ⊕ α) ≠ Sum.inr e.2 ∧
        B.IsLink e (Sum.inl e.1) (Sum.inr e.2) := by
      intro e he
      refine ⟨by rintro ⟨⟩, ?_⟩
      exact ⟨he.1, he.2, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨Γ, hU_eq, hν_Γ⟩ := GraphDrawing.of_edge_lines hV_fin hE_fin hν_inj hends
      (fun e he => (hK_props e he).1) hdisj_V hdisj_E
    have hU_sub_U₀ : Γ.drawing.U ⊆ Γ₀.drawing.U := by
      rw [hU_eq]
      refine union_subset ?_ (iUnion₂_subset fun e he => ?_)
      · rintro _ ⟨w, hwB, rfl⟩
        exact hν_mem_U₀ w hwB
      · exact (hK_props e he).2.1.trans
          (Γ₀.drawing.closure_subset_U (Γ₀.iso.edgeEquiv (ambEdge e he)).2)
    have hvert_Γ : ∀ v ∈ V(B), graphDrawingVertexSet Γ v = {ν v} := by
      intro v hv
      rw [graphDrawingVertexSet_eq_singleton Γ hv, hν_Γ ⟨v, hv⟩]
    have hvert_bar : ∀ v ∈ (liftCyclicPermInr S.Ω).bar,
        graphDrawingVertexSet Γ v = graphDrawingVertexSet Γ₀ v := by
      rintro _ ⟨u, hu_bar, rfl⟩
      have huC : u ∈ V(C) := hC.isCore.isTrisecting.bar_subset hu_bar
      have huB : (Sum.inr u : Graph α β ⊕ α) ∈ V(B) := hV_B_eq ▸ Or.inr ⟨u, huC, rfl⟩
      have huG₀ : (Sum.inr u : Graph α β ⊕ α) ∈ V(G₀) := Or.inr ⟨u, huC, rfl⟩
      rw [hvert_Γ (Sum.inr u) huB, graphDrawingVertexSet_eq_singleton Γ₀ huG₀, hν_inr]
      simp [ν₀, huG₀]
    have hbd_Γ : ∀ v ∈ V(B),
        graphDrawingVertexSet Γ v ⊆ subBd Δ ↔ v ∈ (liftCyclicPermInr S.Ω).bar := by
      intro v hvB
      rw [hvert_Γ v hvB, singleton_subset_iff]
      constructor
      · intro hv_bd
        have hv_inter : ν v ∈ Γ₀.drawing.U ∩ subBd Δ := ⟨hU_sub_U₀ (hU_eq ▸ Or.inl ⟨v, hvB, rfl⟩), hv_bd⟩
        rw [hU₀_inter_bd] at hv_inter
        obtain ⟨z, hz_bar, hνz⟩ := mem_iUnion₂.mp hv_inter
        have hzB : z ∈ V(B) := hbar_sub hz_bar
        rw [← hvert_bar z hz_bar, hvert_Γ z hzB, mem_singleton_iff] at hνz
        exact hν_inj hvB hzB hνz ▸ hz_bar
      · intro hv_bar
        have hv_sub := hagrees₀.1 v hv_bar
        rwa [← hvert_bar v hv_bar, hvert_Γ v hvB, singleton_subset_iff] at hv_sub
    have hagrees_Γ : DrawingAgreesWithOArcHomeo Γ (liftCyclicPermInr S.Ω) (subBd Δ) φ := by
      refine ⟨fun v hv => ?_, fun v₁ v₂ v₃ hcw => ?_⟩
      · rw [hvert_bar v hv]
        exact hagrees₀.1 v hv
      · have hv₁ : v₁ ∈ (liftCyclicPermInr S.Ω).bar := hcw.2.1 v₁ (by simp)
        have hv₂ : v₂ ∈ (liftCyclicPermInr S.Ω).bar := hcw.2.1 v₂ (by simp)
        have hv₃ : v₃ ∈ (liftCyclicPermInr S.Ω).bar := hcw.2.1 v₃ (by simp)
        rw [hvert_bar v₁ hv₁, hvert_bar v₂ hv₂, hvert_bar v₃ hv₃]
        exact hagrees₀.2 v₁ v₂ v₃ hcw
    exact isRuralSociety_of_disc_drawing S_B Γ Δ hΔ (hU_sub_U₀.trans hU₀_Δ) hbd_Γ φ hcw₀ hagrees_Γ
  · -- Empty core case: `V(C) = ∅`
    have hVC_emp : V(C) = ∅ := not_nonempty_iff_eq_empty.mp hVC_ne
    have hbar_emp : S.Ω.bar = ∅ :=
      subset_eq_empty hC.isCore.isTrisecting.bar_subset hVC_emp
    have hbar_lift_emp : (liftCyclicPermInr (γ := Graph α β) S.Ω).bar = ∅ := by
      simp [liftCyclicPermInr, hbar_emp]
    have hE_B_emp : E(B) = ∅ := by
      ext ⟨A, u⟩
      simp only [B, divisionBipartiteGraph, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hA hu
      have huC : u ∈ V(C) := (boundary_isClique_in_core hC hA).1 hu
      rw [hVC_emp] at huC
      exact huC
    have hV_B_sub : V(B).Subsingleton := by
      rw [hV_B_eq, hVC_emp, image_empty, union_empty]
      rintro _ ⟨A₁, hA₁, rfl⟩ _ ⟨A₂, hA₂, rfl⟩
      have hbd₁ : divBoundary S A₁ = ∅ :=
        subset_eq_empty (boundary_isClique_in_core hC hA₁).1 hVC_emp
      have hbd₂ : divBoundary S A₂ = ∅ :=
        subset_eq_empty (boundary_isClique_in_core hC hA₂).1 hVC_emp
      exact congrArg Sum.inl (hdiv.boundary_injOn hA₁ hA₂ (hbd₁.trans hbd₂.symm))
    obtain ⟨Δ, p₀, φ, hΔ, hcw₀, hp₀_Δ, hp₀_not_bd⟩ := exists_closedDisc_and_interior_point
    let ν : (Graph α β ⊕ α) → EuclideanPlane := fun _ => p₀
    have hν_inj : InjOn ν V(B) := fun _ hx _ hy _ => hV_B_sub hx hy
    obtain ⟨Γ, hU_eq, hν_Γ⟩ := GraphDrawing.of_edgeless hV_fin hE_B_emp hν_inj
    have hU_Δ : Γ.drawing.U ⊆ Δ := by
      rw [hU_eq]
      rintro _ ⟨_, _, rfl⟩
      exact hp₀_Δ
    have hbd_Γ : ∀ v ∈ V(B),
        graphDrawingVertexSet Γ v ⊆ subBd Δ ↔
        v ∈ (liftCyclicPermInr (γ := Graph α β) S.Ω).bar := by
      intro v hvB
      rw [graphDrawingVertexSet_eq_singleton Γ hvB, hν_Γ ⟨v, hvB⟩, singleton_subset_iff,
        hbar_lift_emp]
      exact ⟨fun h => (hp₀_not_bd h).elim, fun h => h.elim⟩
    have hagrees_Γ :
        DrawingAgreesWithOArcHomeo Γ (liftCyclicPermInr (γ := Graph α β) S.Ω) (subBd Δ) φ := by
      refine ⟨fun _ h => (hbar_lift_emp ▸ h).elim, fun v₁ _ _ hcw => ?_⟩
      have hv₁ := hcw.2.1 v₁ (by simp)
      rw [hbar_lift_emp] at hv₁
      exact hv₁.elim
    exact isRuralSociety_of_disc_drawing S_B Γ Δ hΔ hU_Δ hbd_Γ φ hcw₀ hagrees_Γ

/-! ## Algorithm (8.6) (pages 96–97) -/

/-- **(8.6) Algorithm** (Graph Minors XIII, Section 8, pages 96–97):
“*Input:* A society $(G, \Omega)$.
*Output:* Either a cross in $(G, \Omega)$, or a rural division of $(G, \Omega)$.
*Running time:* $O(\nu\varepsilon)$.”

Mathematical correctness statement: for any society `S = (G, Ω)`, either `S` has a cross
(`(∃ C, IsCrossSubgraph S C) ∧ HasCross S`), or `S` has no cross and admits a rural division `𝒜`
(`¬ HasCross S ∧ ∃ 𝒜, IsRuralDivision S 𝒜`).

The RAM program and its `O(v e)` time bound are `GM13.algorithm_8_6` in `Results.lean`. The method
calls (8.1) (`algorithm_8_1_correct`) to test for a cross, and if there is none it calls (8.3)
(`algorithm_8_3_correct`) to compute a 4-linked core `C`, builds the raw division
`coreRawDivision S C`, groups its members by equal boundaries `∂A₁ = ∂A₂`, and outputs
`coreDivision S C`. -/
theorem algorithm_8_6_correct (S : Society α β) :
    ((∃ C : Graph α β, IsCrossSubgraph S C) ∧ HasCross S) ∨
      (¬ HasCross S ∧ ∃ 𝒜 : Set (Graph α β), IsRuralDivision S 𝒜) := by
  rcases (algorithm_8_1_correct S).2 with hcross | hnocross
  · exact Or.inl hcross
  · obtain ⟨C, hC⟩ := algorithm_8_3_correct S
    exact Or.inr ⟨hnocross, coreDivision S C, isRuralDivision_coreDivision hC hnocross⟩

/-- Alias of `algorithm_8_6_correct` under the paper's numbering `(8.6)`. -/
theorem theorem_8_6_proof (S : Society α β) :
    ((∃ C : Graph α β, IsCrossSubgraph S C) ∧ HasCross S) ∨
      (¬ HasCross S ∧ ∃ 𝒜 : Set (Graph α β), IsRuralDivision S 𝒜) := by
  rcases (algorithm_8_1_correct S).2 with hcross | hnocross
  · exact Or.inl hcross
  · obtain ⟨C, hC⟩ := algorithm_8_3_correct S
    exact Or.inr ⟨hnocross, coreDivision S C, isRuralDivision_coreDivision hC hnocross⟩

end GraphMinor.GM13
