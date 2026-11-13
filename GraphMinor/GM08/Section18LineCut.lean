module

public import GraphMinor.GM08.Section18CutSum
public import GraphMinor.GM08.Section18ComponentMeasure
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.CutLoop
import GraphMinor.Surface.Cuffs
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section3
import GraphMinor.GM07.CutConnected
import GraphMinor.GM08.Section18DiscPiece
import GraphMinor.GM08.Section18CutSide
import GraphMinor.Surface.CutComp

/-!
# Cutting one part of a surface along a line between two cuffs

The last step of the cut along an `X₁`-arc (VIII (18.2), page 286) cuts along
the line of the arc. After the two circles are cut, this line joins two
different cuffs of one component `Q` of the cut surface. Cutting `Q` along it
joins the two cuffs, so `g(Q)` drops by one, and the other components stay as
they are (`exists_line_cut_of_distinct`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- Two points on disjoint circles in the boundary lie in different cuffs. -/
theorem connectedComponentIn_bd_ne {T : Type w} [TopologicalSpace T] (hT : IsSurface T)
    {Zx Zy : Set T} (hZx : IsOArc Zx) (hZy : IsOArc Zy) (hZxb : Zx ⊆ bd T) (hZyb : Zy ⊆ bd T)
    (hdis : Disjoint Zx Zy) {x y : T} (hx : x ∈ Zx) (hy : y ∈ Zy) :
    connectedComponentIn (bd T) x ≠ connectedComponentIn (bd T) y := by
  have : T2Space T := hT.2.1
  intro heq
  have hK : connectedComponentIn (bd T) x ∈ cuffs T := ⟨x, hZxb hx, rfl⟩
  obtain ⟨φ⟩ := (cuff_statement T hT).2.2 _ hK
  have h1 : Zx = connectedComponentIn (bd T) x :=
    oarc_eq φ hZx ((GM07.IsOArc.isConnected hZx).isPreconnected.subset_connectedComponentIn hx hZxb)
  have h2 : Zy = connectedComponentIn (bd T) x :=
    oarc_eq φ hZy (heq ▸ (GM07.IsOArc.isConnected hZy).isPreconnected.subset_connectedComponentIn
      hy hZyb)
  have : y ∈ Zx := h1 ▸ h2 ▸ hy
  exact disjoint_left.mp hdis this hy

/-- **Points over disjoint closed sets lie in different cuffs.** If the
boundary maps into the union of two disjoint closed sets, then boundary points
over different sets lie in different components of the boundary. -/
theorem connectedComponentIn_bd_ne_of_map {K S : Type w} [TopologicalSpace K] [TopologicalSpace S]
    {θ : K → S} (hθ : Continuous θ) {G₁ G₂ : Set S} (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂)
    (hdis : Disjoint G₁ G₂) (hbd : ∀ z ∈ bd K, θ z ∈ G₁ ∪ G₂) {p q : K} (hp : p ∈ bd K)
    (hq : q ∈ bd K) (hpG : θ p ∈ G₁) (hqG : θ q ∈ G₂) :
    connectedComponentIn (bd K) p ≠ connectedComponentIn (bd K) q := by
  intro heq
  have hc : IsPreconnected (θ '' connectedComponentIn (bd K) p) :=
    (isPreconnected_connectedComponentIn).image _ hθ.continuousOn
  have hsub : θ '' connectedComponentIn (bd K) p ⊆ G₁ ∪ G₂ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hbd z (connectedComponentIn_subset _ _ hz)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hc) G₁ G₂ hG₁ hG₂ hsub
      (by rw [hdis.inter_eq, inter_empty]) with h | h
  · have hqc : q ∈ connectedComponentIn (bd K) p := heq ▸ mem_connectedComponentIn hq
    exact disjoint_left.mp hdis (h ⟨q, hqc, rfl⟩) hqG
  · exact disjoint_left.mp hdis hpG (h ⟨p, mem_connectedComponentIn hp, rfl⟩)

/-- **Cutting a part along a line between two cuffs.** Let `Q` be an open and
closed connected part of a surface `T`, and `L ⊆ Q` a line whose ends `x, y`
are its only boundary points and lie in different cuffs. Cutting `Q` along `L`
lowers `g(Q)` by one and keeps the other components. -/
theorem exists_line_cut_of_distinct {T : Type w} [TopologicalSpace T] (hT : IsSurface T)
    {Q : Set T} (hQ : IsClopen Q) [ConnectedSpace Q] {L : Set T} {x y : T} (hLQ : L ⊆ Q)
    (hL : IsLineWithEnds L x y) (hxy : x ≠ y) (hbd : L ∩ bd T = {x, y})
    (hcuffsT : connectedComponentIn (bd T) x ≠ connectedComponentIn (bd T) y) {n : ℕ}
    (hQn : surfaceComplexity Q ≤ n + 1)
    (hc : ∀ z ∉ Q, connectedSurfaceComplexity (connectedComponent z) ≤ n) :
    ∃ (T' : Type w) (_ : TopologicalSpace T') (ψ : T' → T), IsSurface T' ∧ IsCutting ψ L ∧
      surfaceComplexity T' ≤ n := by
  have hxQ : x ∈ Q := hLQ (hL.left_mem)
  have hyQ : y ∈ Q := hLQ (hL.right_mem)
  have hQs : IsSurface Q := isSurface_sub hT hQ
  set L' : Set Q := Subtype.val ⁻¹' L
  have hL' : IsLineWithEnds L' ⟨x, hxQ⟩ ⟨y, hyQ⟩ := GM12.isLineWithEnds_subtype_preimage hLQ hL
  have hne : (⟨x, hxQ⟩ : Q) ≠ ⟨y, hyQ⟩ := fun h => hxy (congrArg Subtype.val h)
  have hbd' : L' ∩ bd Q = {⟨x, hxQ⟩, ⟨y, hyQ⟩} := by
    ext z
    simp only [L', mem_inter_iff, mem_preimage, mem_bd_sub hQ.isOpen, mem_insert_iff,
      mem_singleton_iff, Subtype.ext_iff]
    rw [← mem_inter_iff, hbd]
    simp
  have hxb : x ∈ bd T := (hbd.symm ▸ Or.inl rfl : x ∈ L ∩ bd T).2
  have hyb : y ∈ bd T := (hbd.symm ▸ Or.inr rfl : y ∈ L ∩ bd T).2
  have hcuffs : connectedComponentIn (bd Q) (⟨x, hxQ⟩ : Q) ≠
      connectedComponentIn (bd Q) ⟨y, hyQ⟩ := by
    intro heq
    have hy' : (⟨y, hyQ⟩ : Q) ∈ connectedComponentIn (bd Q) ⟨x, hxQ⟩ :=
      heq ▸ mem_connectedComponentIn ((mem_bd_sub hQ.isOpen).mpr hyb)
    have himg : Subtype.val '' connectedComponentIn (bd Q) (⟨x, hxQ⟩ : Q) ⊆
        connectedComponentIn (bd T) x :=
      (isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn).subset_connectedComponentIn
        ⟨_, mem_connectedComponentIn ((mem_bd_sub hQ.isOpen).mpr hxb), rfl⟩
        (by rintro _ ⟨z, hz, rfl⟩; exact (mem_bd_sub hQ.isOpen).mp (connectedComponentIn_subset _ _ hz))
    exact hcuffsT (connectedComponentIn_eq (himg ⟨_, hy', rfl⟩))
  obtain ⟨T₀, t₀, ψ₀, hT₀, hcut₀, hdist, -, -⟩ :=
    cutIArc Q L' ⟨x, hxQ⟩ ⟨y, hyQ⟩ hQs inferInstance hne hbd' hL'
  obtain ⟨hconn, a, b, c, ⟨eQ⟩, ⟨e₀⟩⟩ := hdist hcuffs
  let := t₀
  refine ⟨T₀ ⊕ (Qᶜ : Set T), inferInstance, _, GM07.isSurface_sum hT₀ (isSurface_sub hT hQ.compl),
    isCutting_sum_compl hLQ hcut₀, ?_⟩
  refine (surfaceComplexity_sum_le hT₀ (isSurface_sub hT hQ.compl)).trans (max_le ?_ ?_)
  · rw [surfaceComplexity_eq_connected, connectedSurfaceComplexity_eq ⟨e₀⟩]
    rw [surfaceComplexity_eq_connected, connectedSurfaceComplexity_eq ⟨eQ⟩] at hQn
    omega
  · refine surfaceComplexity_le_of_components fun z => ?_
    rw [connectedSurfaceComplexity_component_subtype hQ.compl]
    exact hc z z.2

/-- A line is connected. -/
theorem isPreconnected_of_isLine {T : Type w} [TopologicalSpace T] {X : Set T} (h : IsLine X) :
    IsPreconnected X := by
  obtain ⟨e⟩ := h
  have h := isPreconnected_range (continuous_subtype_val.comp e.continuous)
  rwa [range_comp, e.range_coe, image_univ, Subtype.range_coe] at h

/-- The disc piece of a cut of a part `Q`, read in the whole cut surface. -/
private theorem disc_piece_of_sum {T : Type w} [TopologicalSpace T] {Q L : Set T}
    {T₀ : Type w} [TopologicalSpace T₀] [T2Space (T₀ ⊕ (Qᶜ : Set T))] {ψ₀ : T₀ → Q}
    {K : Set T₀} (hKo : IsOpen K) (hK : IsClosedDisc K) (hinj : InjOn ψ₀ K)
    (hmeet : (K ∩ ψ₀ ⁻¹' (Subtype.val ⁻¹' L)).Nonempty) :
    ∃ D : Set (T₀ ⊕ (Qᶜ : Set T)), IsOpen D ∧ IsClosedDisc D ∧
      InjOn (Sum.elim (Subtype.val ∘ ψ₀) (Subtype.val : (Qᶜ : Set T) → T)) D ∧
      D ⊆ Sum.elim (Subtype.val ∘ ψ₀) (Subtype.val : (Qᶜ : Set T) → T) ⁻¹' Q ∧
      (D ∩ Sum.elim (Subtype.val ∘ ψ₀) (Subtype.val : (Qᶜ : Set T) → T) ⁻¹' L).Nonempty := by
  refine ⟨Sum.inl '' K, isOpenMap_inl _ hKo,
    (isClosedDisc_image_of_injOn continuous_inl hK Sum.inl_injective.injOn).1, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact congrArg Sum.inl (hinj ha hb (Subtype.ext hab))
  · rintro _ ⟨a, -, rfl⟩
    exact (ψ₀ a).2
  · obtain ⟨a, ha, haL⟩ := hmeet
    exact ⟨Sum.inl a, ⟨a, ha, rfl⟩, haL⟩

/-- **Cutting a part along a line between boundary points.** Let `Q` be an
open and closed connected part of a surface `T`, and `L ⊆ Q` a line whose ends
are its only boundary points. Cutting `Q` along `L` either lowers the measure
of every piece over `Q` below `g(Q)`, or has a piece over `Q` that is a closed
disc, on which the cut map is one to one, and which holds a lift of `L`. -/
theorem exists_line_cut_piece {T : Type w} [TopologicalSpace T] (hT : IsSurface T)
    {Q : Set T} (hQ : IsClopen Q) [ConnectedSpace Q] {L : Set T} {x y : T} (hLQ : L ⊆ Q)
    (hL : IsLineWithEnds L x y) (hxy : x ≠ y) (hbd : L ∩ bd T = {x, y}) :
    ∃ (T' : Type w) (_ : TopologicalSpace T') (ψ : T' → T), IsSurface T' ∧ IsCutting ψ L ∧
      ((∀ n, surfaceComplexity Q ≤ n + 1 →
          (∀ z ∉ Q, connectedSurfaceComplexity (connectedComponent z) ≤ n) →
          surfaceComplexity T' ≤ n) ∨
        ∃ D : Set T', IsOpen D ∧ IsClosedDisc D ∧ InjOn ψ D ∧ D ⊆ ψ ⁻¹' Q ∧
          (D ∩ ψ ⁻¹' L).Nonempty) := by
  have hxQ : x ∈ Q := hLQ (hL.left_mem)
  have hyQ : y ∈ Q := hLQ (hL.right_mem)
  have hQs : IsSurface Q := isSurface_sub hT hQ
  set L' : Set Q := Subtype.val ⁻¹' L
  have hL' : IsLineWithEnds L' ⟨x, hxQ⟩ ⟨y, hyQ⟩ := GM12.isLineWithEnds_subtype_preimage hLQ hL
  have hne : (⟨x, hxQ⟩ : Q) ≠ ⟨y, hyQ⟩ := fun h => hxy (congrArg Subtype.val h)
  have hbd' : L' ∩ bd Q = {⟨x, hxQ⟩, ⟨y, hyQ⟩} := by
    ext z
    simp only [L', mem_inter_iff, mem_preimage, mem_bd_sub hQ.isOpen, mem_insert_iff,
      mem_singleton_iff, Subtype.ext_iff]
    rw [← mem_inter_iff, hbd]
    simp
  obtain ⟨T₀, t₀, ψ₀, hT₀, hcut₀, hdist, hsame, X, Y, -, hun, hX, hY, hbX, hbY⟩ :=
    cutIArc Q L' ⟨x, hxQ⟩ ⟨y, hyQ⟩ hQs inferInstance hne hbd' hL'
  let := t₀
  have hQc : IsSurface (Qᶜ : Set T) := isSurface_sub hT hQ.compl
  have hsum : IsSurface (T₀ ⊕ (Qᶜ : Set T)) := GM07.isSurface_sum hT₀ hQc
  have : T2Space (T₀ ⊕ (Qᶜ : Set T)) := hsum.2.1
  have : Nonempty T₀ := ⟨(hcut₀.2.1 ⟨x, hxQ⟩).choose⟩
  refine ⟨T₀ ⊕ (Qᶜ : Set T), inferInstance, _, hsum, isCutting_sum_compl hLQ hcut₀, ?_⟩
  have hrest : ∀ n, (∀ z ∉ Q, connectedSurfaceComplexity (connectedComponent z) ≤ n) →
      surfaceComplexity (Qᶜ : Set T) ≤ n := fun n hc =>
    surfaceComplexity_le_of_components fun z => by
      rw [connectedSurfaceComplexity_component_subtype hQ.compl]
      exact hc z z.2
  by_cases hc : connectedComponentIn (bd Q) ⟨x, hxQ⟩ = connectedComponentIn (bd Q) ⟨y, hyQ⟩
  · rcases hsame hc with hsimp | ⟨K₁, K₂, hK, hcomps, ⟨e₁⟩, -⟩
    · left
      intro n hQn hcn
      refine (surfaceComplexity_sum_le hT₀ hQc).trans (max_le ?_ (hrest n hcn))
      have := surfaceComplexity_lt_of_cutIsSimpler hsimp
      omega
    · right
      have hT₀c : CompactSpace T₀ := hT₀.1
      have : T2Space Q := hQs.2.1
      obtain ⟨eX⟩ := hX
      obtain ⟨eY⟩ := hY
      rcases cut_comps hcut₀ hT₀ (isPreconnected_of_isLine ⟨eX⟩) (isPreconnected_of_isLine ⟨eY⟩) hun
          (eX 0).2 (eY 0).2 with hconn |
        ⟨W₁, W₂, -, hW, hXW, hYW, hW₁, hW₂, -, hdis, -, -⟩
      · exfalso
        have h1 : K₁ ∈ spaceComponents T₀ := hcomps ▸ (Or.inl rfl)
        have h2 : K₂ ∈ spaceComponents T₀ := hcomps ▸ (Or.inr rfl)
        rw [Surface.spaceComponents_eq] at h1 h2
        obtain ⟨a, rfl⟩ := h1
        obtain ⟨b, rfl⟩ := h2
        exact hK ((PreconnectedSpace.connectedComponent_eq_univ a).trans
          (PreconnectedSpace.connectedComponent_eq_univ b).symm)
      have hK₁ : K₁ ∈ ({W₁, W₂} : Set (Set T₀)) := hW ▸ hcomps ▸ (Or.inl rfl)
      have hdisc : IsClosedDisc K₁ := ⟨e₁.symm⟩
      rcases hK₁ with rfl | rfl
      · exact disc_piece_of_sum hW₁.isOpen hdisc
          (injOn_cut_side hcut₀ hun (hdis.symm.mono_left hYW) hbX.injOn)
          ⟨(eX 0).1, hXW (eX 0).2, (hun ▸ Or.inl (eX 0).2 : (eX 0).1 ∈ ψ₀ ⁻¹' L')⟩
      · exact disc_piece_of_sum hW₂.isOpen hdisc
          (injOn_cut_side hcut₀ (union_comm X Y ▸ hun) (hdis.mono_left hXW) hbY.injOn)
          ⟨(eY 0).1, hYW (eY 0).2, (hun ▸ Or.inr (eY 0).2 : (eY 0).1 ∈ ψ₀ ⁻¹' L')⟩
  · left
    intro n hQn hcn
    obtain ⟨hconn, a, b, c, ⟨eQ⟩, ⟨e₀⟩⟩ := hdist hc
    let := hconn
    refine (surfaceComplexity_sum_le hT₀ hQc).trans (max_le ?_ (hrest n hcn))
    rw [surfaceComplexity_eq_connected, connectedSurfaceComplexity_eq ⟨e₀⟩]
    rw [surfaceComplexity_eq_connected, connectedSurfaceComplexity_eq ⟨eQ⟩] at hQn
    omega
