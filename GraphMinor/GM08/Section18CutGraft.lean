module

public import GraphMinor.GM08.Section18CutChain
public import GraphMinor.GM08.Section18Classes
public import GraphMinor.GM07.CutStages
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18Pullback
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM07.PullForest
import GraphMinor.GM07.NetExists

/-!
# The cut graft

This is the cut case on page 287 of VIII. A graft is drawn in `Σ`, and `F` is
a normal set that misses the boundary. We cut `Σ` along `F` and pull the
drawing back to the cut surface `Σ'`. A vertex on `F` gets several lifts, all
on the boundary of `Σ'`. One lift keeps the old label and the others get new
labels. This gives a graft drawn in `Σ'`, and the old graft comes back from
it by vertex identifications (`obtainedByVertexIdChain_of_retraction`).

So the graft lies in `W(𝒞(g(Σ'), k + M))`, where `k` bounds its index and
`M` bounds the number of lifts of the vertices on `F`
(`mem_WGraftClass_classC_of_cut`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Graph GraphMinor.Surface

universe u v w

/-! ## Relabelling a graph along bijections -/

/-- Relabel a graph along bijections of its vertex set and its edge set. -/
def relabelGraphBy {A B α β : Type*} (H : Graph A B) {V' : Set α} {E' : Set β}
    (ev : V(H) ≃ V') (ee : E(H) ≃ E') : Graph α β where
  vertexSet := V'
  edgeSet := E'
  IsLink e x y := ∃ (e₀ : E(H)) (x₀ y₀ : V(H)), H.IsLink e₀ x₀ y₀ ∧
    ((ee e₀ : E') : β) = e ∧ ((ev x₀ : V') : α) = x ∧ ((ev y₀ : V') : α) = y
  isLink_symm := by
    intro e _
    refine ⟨?_⟩
    rintro x y ⟨e₀, x₀, y₀, h, rfl, rfl, rfl⟩
    exact ⟨e₀, y₀, x₀, h.symm, rfl, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y z w ⟨e₀, x₀, y₀, h, he, rfl, rfl⟩ ⟨e₁, z₀, w₀, h', he', rfl, rfl⟩
    have : e₀ = e₁ := ee.injective (Subtype.ext (he.trans he'.symm))
    subst this
    rcases h.left_eq_or_eq h' with hx | hx
    · exact Or.inl (congrArg (fun a : V(H) => ((ev a : V') : α)) (Subtype.ext hx))
    · exact Or.inr (congrArg (fun a : V(H) => ((ev a : V') : α)) (Subtype.ext hx))
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro he
      obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet (ee.symm ⟨e, he⟩).2
      exact ⟨_, _, ee.symm ⟨e, he⟩, ⟨a, hab.left_mem⟩, ⟨b, hab.right_mem⟩, hab,
        by simp, rfl, rfl⟩
    · rintro ⟨x, y, e₀, x₀, y₀, h, rfl, -, -⟩
      exact (ee e₀).2
  left_mem_of_isLink := by
    rintro e x y ⟨e₀, x₀, y₀, h, -, rfl, -⟩
    exact (ev x₀).2

/-- The relabelled graph is isomorphic to the original one. -/
def relabelGraphByIso {A B α β : Type*} (H : Graph A B) {V' : Set α} {E' : Set β}
    (ev : V(H) ≃ V') (ee : E(H) ≃ E') : Iso H (relabelGraphBy H ev ee) where
  vertexEquiv := ev
  edgeEquiv := ee
  isLink_iff e x y := by
    constructor
    · intro h
      exact ⟨e, x, y, h, rfl, rfl, rfl⟩
    · rintro ⟨e₀, x₀, y₀, h, he, hx, hy⟩
      have he' : e₀ = e := ee.injective (Subtype.ext he)
      have hx' : x₀ = x := ev.injective (Subtype.ext hx)
      have hy' : y₀ = y := ev.injective (Subtype.ext hy)
      subst he' hx' hy'
      exact h

/-- The inverse isomorphism, from the relabelled graph back to the original. -/
def relabelGraphByIsoSymm {A B α β : Type*} (H : Graph A B) {V' : Set α} {E' : Set β}
    (ev : V(H) ≃ V') (ee : E(H) ≃ E') : Iso (relabelGraphBy H ev ee) H where
  vertexEquiv := ev.symm
  edgeEquiv := ee.symm
  isLink_iff e x y := by
    constructor
    · rintro ⟨e₀, x₀, y₀, h, he, hx, hy⟩
      have he' : e₀ = ee.symm ⟨e.1, e.2⟩ :=
        (ee.symm_apply_eq.mpr (Subtype.ext he).symm).symm
      have hx' : x₀ = ev.symm ⟨x.1, x.2⟩ :=
        (ev.symm_apply_eq.mpr (Subtype.ext hx).symm).symm
      have hy' : y₀ = ev.symm ⟨y.1, y.2⟩ :=
        (ev.symm_apply_eq.mpr (Subtype.ext hy).symm).symm
      subst he' hx' hy'
      exact h
    · intro h
      exact ⟨ee.symm ⟨e.1, e.2⟩, ev.symm ⟨x.1, x.2⟩, ev.symm ⟨y.1, y.2⟩, h,
        congrArg Subtype.val (ee.apply_symm_apply _), congrArg Subtype.val (ev.apply_symm_apply _),
        congrArg Subtype.val (ev.apply_symm_apply _)⟩

/-! ## Edges of a pulled-back drawing -/

section Pullback

variable {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]

/-- A continuous surjection from a compact space onto a Hausdorff space maps
the closure of a preimage onto the closure. -/
theorem image_closure_preimage_eq [CompactSpace T] [T2Space S] {ψ : T → S}
    (hc : Continuous ψ) (hs : Surjective ψ) (A : Set S) :
    ψ '' closure (ψ ⁻¹' A) = closure A := by
  apply Subset.antisymm
  · calc ψ '' closure (ψ ⁻¹' A) ⊆ closure (ψ '' (ψ ⁻¹' A)) := image_closure_subset_closure_image hc
      _ = closure A := by rw [image_preimage_eq A hs]
  · refine closure_minimal (fun x hx => ?_) (isClosed_closure.isCompact.image hc).isClosed
    obtain ⟨y, rfl⟩ := hs x
    exact ⟨y, subset_closure hx, rfl⟩

/-- In a pulled-back drawing whose edges are preimages of edges, the
preimage of every edge is an edge. -/
theorem preimage_mem_E_of_pullback {D : Drawing S} {G' : Drawing T} {ψ : T → S}
    (hs : Surjective ψ) (hpb : GM07.IsPullbackDrawing ψ D G')
    (hE : ∀ e' ∈ G'.E, ∃ e ∈ D.E, e' = ψ ⁻¹' e) {e : Set S} (he : e ∈ D.E) :
    ψ ⁻¹' e ∈ G'.E := by
  obtain ⟨x, hx⟩ := he.1
  obtain ⟨y, rfl⟩ := hs x
  have hxUV : ψ y ∈ D.U \ D.V := he.2.1 hx
  have hyU : y ∈ G'.U := by rw [hpb.1]; exact hxUV.1
  have hyV : y ∉ G'.V := by rw [hpb.2]; exact hxUV.2
  obtain ⟨e₀, he₀, hy⟩ := GM07.exists_edge_of_mem hyU hyV
  obtain ⟨e₁, he₁, rfl⟩ := hE e₀ he₀
  have h : e₁ = e := GM07.arcComponentsIn_eq_of_mem he₁ he hy hx
  rwa [h] at he₀

/-- The edges of the pulled-back drawing correspond to the old edges. -/
noncomputable def pullbackEdgeEquiv {D : Drawing S} {G' : Drawing T} {ψ : T → S}
    (hs : Surjective ψ) (hpb : GM07.IsPullbackDrawing ψ D G')
    (hE : ∀ e' ∈ G'.E, ∃ e ∈ D.E, e' = ψ ⁻¹' e) : G'.E ≃ D.E where
  toFun e' := ⟨ψ '' e', by
    obtain ⟨e, he, h⟩ := hE e'.1 e'.2
    rw [h, image_preimage_eq e hs]
    exact he⟩
  invFun e := ⟨ψ ⁻¹' e, preimage_mem_E_of_pullback hs hpb hE e.2⟩
  left_inv e' := by
    obtain ⟨e, he, h⟩ := hE e'.1 e'.2
    apply Subtype.ext
    change ψ ⁻¹' (ψ '' e'.1) = e'.1
    rw [h, image_preimage_eq e hs]
  right_inv e := Subtype.ext (image_preimage_eq e.1 hs)

end Pullback

/-! ## The cut graft -/

/-- **The cut case of page 287.** Let `ψ : Σ' → Σ` cut `Σ` along a schism `F`
that misses the boundary, and let a graft `X` of index at most `k` be drawn in
`Σ` with `F` normal. Suppose every vertex on `F` has at least two lifts, and
the vertices on `F` have at most `M` lifts in all. Then `X` lies in
`W(𝒞(g(Σ'), k + M))`, up to isomorphism. -/
theorem mem_WGraftClass_classC_of_cut {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) {ψ : T → S}
    (hcut : GM07.IsCutAlongSet F ψ) (hmap : GM19.IsCutMap ψ F) (hFbd : F ∩ bd S = ∅)
    {α : Type u} {β : Type v} [Infinite α] (X : Graft α β) (DX : GraftDrawing X.G X.T S)
    (hn : DX.drawing.IsNormal F)
    (hlift : ∀ x ∈ DX.drawing.V ∩ F, 1 < (ψ ⁻¹' {x}).ncard)
    {k M : ℕ} (hk : X.index ≤ k) (hM : (ψ ⁻¹' (DX.drawing.V ∩ F)).ncard ≤ M) :
    X ∈ WGraftClass (isoGraftClass (classC.{u, v, w} (surfaceComplexity T) (k + M))) := by
  classical
  have : T2Space S := hS.2.1
  have hT : IsSurface T := hcut.isSurface
  have : CompactSpace T := hT.1
  have : T2Space T := hT.2.1
  obtain ⟨G', hpb, hG'p, hE'⟩ :=
    exists_pullback_drawing_of_schism_cut hS hF hcut DX.drawing DX.isProper hn
  have hs : Surjective ψ := hmap.2.1
  have hc : Continuous ψ := hmap.1
  have hinjF : ∀ y₁ y₂ : T, ψ y₁ ∉ F → ψ y₁ = ψ y₂ → y₁ = y₂ := fun y₁ y₂ h₁ h =>
    hmap.2.2.1 (show ψ y₁ ∈ Fᶜ from h₁) (show ψ y₂ ∈ Fᶜ from h ▸ h₁) h
  set D := DX.drawing with hD
  set ι := DX.iso with hι
  have hG'V : ∀ y, y ∈ G'.V ↔ ψ y ∈ D.V := fun y => by rw [hpb.2]; rfl
  have hbdT : ∀ y, y ∈ bd T ↔ ψ y ∈ bd S ∪ F := fun y => by rw [← hcut.preimage_bd]; rfl
  -- labels of the old vertices
  obtain ⟨a₀⟩ : Nonempty α := inferInstance
  let σ : S → α := fun z => if h : z ∈ D.V then (ι.vertexEquiv.symm ⟨z, h⟩ : α) else a₀
  have hσ : ∀ z (hz : z ∈ D.V), σ z = (ι.vertexEquiv.symm ⟨z, hz⟩ : α) := fun z hz => by
    simp [σ, hz]
  have hσV : ∀ z ∈ D.V, σ z ∈ V(X.G) := fun z hz => by rw [hσ z hz]; exact Subtype.coe_prop _
  have hσι : ∀ a : V(X.G), σ (ι.vertexEquiv a : S) = a := fun a => by
    rw [hσ _ (ι.vertexEquiv a).2]
    simp
  have hισ : ∀ z (hz : z ∈ D.V), ((ι.vertexEquiv ⟨σ z, hσV z hz⟩ : V(D.toGraph)) : S) = z :=
    fun z hz => by
      have : (⟨σ z, hσV z hz⟩ : V(X.G)) = ι.vertexEquiv.symm ⟨z, hz⟩ := Subtype.ext (hσ z hz)
      rw [this, Equiv.apply_symm_apply]
  have hσinj : InjOn σ D.V := fun z₁ h₁ z₂ h₂ h => by
    rw [← hισ z₁ h₁, ← hισ z₂ h₂]
    congr 2
    exact Subtype.ext h
  -- a chosen lift of each point, and the extra lifts
  let sl : S → T := fun z => (hs z).choose
  have hsl : ∀ z, ψ (sl z) = z := fun z => (hs z).choose_spec
  let Q : Set T := {y | y ∈ G'.V ∧ ψ y ∈ F ∧ y ≠ sl (ψ y)}
  have hQfin : Q.Finite := G'.finite_V.subset fun y hy => hy.1
  have hQV : Q ⊆ G'.V := fun y hy => hy.1
  -- fresh labels
  have hinf : (V(X.G))ᶜ.Infinite := X.finite_G.1.infinite_compl
  let ν : ℕ ↪ ((V(X.G))ᶜ : Set α) := Set.Infinite.natEmbedding _ hinf
  have : Finite Q := hQfin.to_subtype
  let eQ : Q ≃ Fin (Nat.card Q) := Finite.equivFin Q
  let lab : T → α := fun y =>
    if h : y ∈ Q then ((ν (eQ ⟨y, h⟩ : ℕ) : _) : α) else σ (ψ y)
  have hlabQd : ∀ y (hy : y ∈ Q), lab y = ((ν (eQ ⟨y, hy⟩ : ℕ) : _) : α) := fun y hy => by
    simp [lab, hy]
  have hlabQ : ∀ y ∈ Q, lab y ∉ V(X.G) := fun y hy => by
    rw [hlabQd y hy]
    exact (ν _).2
  have hlabQ' : ∀ y ∉ Q, lab y = σ (ψ y) := fun y hy => by simp [lab, hy]
  have hlabV : ∀ y ∈ G'.V, y ∉ Q → lab y ∈ V(X.G) := fun y hy hyQ => by
    rw [hlabQ' y hyQ]; exact hσV _ ((hG'V y).1 hy)
  have hslQ : ∀ y, sl (ψ y) ∉ Q := fun y h => h.2.2 (by rw [hsl])
  have hinj : InjOn lab G'.V := by
    intro y₁ h₁ y₂ h₂ h
    by_cases hq₁ : y₁ ∈ Q <;> by_cases hq₂ : y₂ ∈ Q
    · rw [hlabQd y₁ hq₁, hlabQd y₂ hq₂] at h
      have h' := ν.injective (Subtype.ext h)
      have h'' := eQ.injective (Fin.ext h')
      exact congrArg Subtype.val h''
    · exact (hlabQ y₁ hq₁ (h ▸ hlabV y₂ h₂ hq₂)).elim
    · exact (hlabQ y₂ hq₂ (h ▸ hlabV y₁ h₁ hq₁)).elim
    · rw [hlabQ' y₁ hq₁, hlabQ' y₂ hq₂] at h
      have hz := hσinj ((hG'V y₁).1 h₁) ((hG'V y₂).1 h₂) h
      by_cases hF₁ : ψ y₁ ∈ F
      · have e₁ : y₁ = sl (ψ y₁) := by_contra fun hne => hq₁ ⟨h₁, hF₁, hne⟩
        have e₂ : y₂ = sl (ψ y₂) := by_contra fun hne => hq₂ ⟨h₂, hz ▸ hF₁, hne⟩
        rw [e₁, e₂, hz]
      · exact hinjF y₁ y₂ hF₁ hz
  -- the map back to the old labels
  let π : α → α := fun a => if h : ∃ y ∈ Q, lab y = a then σ (ψ h.choose) else a
  have hπlab : ∀ y ∈ G'.V, π (lab y) = σ (ψ y) := by
    intro y hy
    by_cases hq : y ∈ Q
    · have hex : ∃ y' ∈ Q, lab y' = lab y := ⟨y, hq, rfl⟩
      simp only [π, hex, dite_true]
      have := hinj (hQV hex.choose_spec.1) hy hex.choose_spec.2
      rw [this]
    · have hex : ¬ ∃ y' ∈ Q, lab y' = lab y := by
        rintro ⟨y', hy', h⟩
        exact hlabQ y' hy' (h ▸ hlabV y hy hq)
      simp only [π, hex, dite_false]
      exact hlabQ' y hq
  -- the cut graft
  let V' : Set α := lab '' G'.V
  let ev : V(G'.toGraph) ≃ V' := Equiv.Set.imageOfInjOn lab G'.V hinj
  have hev : ∀ y : V(G'.toGraph), ((ev y : V') : α) = lab y := fun _ => rfl
  let eE : G'.E ≃ D.E := pullbackEdgeEquiv hs hpb hE'
  have heE : ∀ e₀ : G'.E, ((eE e₀ : D.E) : Set S) = ψ '' e₀ := fun _ => rfl
  have heEs : ∀ e₁ : D.E, ((eE.symm e₁ : G'.E) : Set T) = ψ ⁻¹' e₁ := fun _ => rfl
  let ee : E(G'.toGraph) ≃ E(X.G) := eE.trans ι.edgeEquiv.symm
  let YG : Graph α β := relabelGraphBy G'.toGraph ev ee
  let YT : Set α := lab '' (G'.V ∩ bd T)
  have hYT : YT ⊆ V(YG) := image_mono inter_subset_left
  let Y : Graft α β := ⟨YG, YT, hYT, ⟨G'.finite_V.image lab, X.finite_G.2⟩⟩
  have hevsymm : ∀ y (hy : y ∈ G'.V) (h : lab y ∈ V'),
      ((ev.symm ⟨lab y, h⟩ : V(G'.toGraph)) : T) = y := fun y hy h => by
    have : ev.symm ⟨lab y, h⟩ = ⟨y, hy⟩ := by rw [Equiv.symm_apply_eq]; rfl
    rw [this]
  let DY : GraftDrawing Y.G Y.T T :=
    { drawing := G'
      iso := relabelGraphByIsoSymm G'.toGraph ev ee
      isProper := hG'p
      T_subset_V := hYT
      mem_bd_iff := by
        intro v hv
        obtain ⟨y, hy, rfl⟩ := id hv
        change ((ev.symm ⟨lab y, hv⟩ : G'.V) : T) ∈ bd T ↔ lab y ∈ lab '' (G'.V ∩ bd T)
        rw [hevsymm y hy hv]
        constructor
        · intro h
          exact ⟨y, ⟨hy, h⟩, rfl⟩
        · rintro ⟨y', ⟨hy', hb⟩, he⟩
          rwa [← hinj hy' hy he] }
  have hYidx : Y.index ≤ k + M := by
    change (lab '' (G'.V ∩ bd T)).ncard ≤ k + M
    rw [(hinj.mono inter_subset_left).ncard_image]
    have hsplit : G'.V ∩ bd T = ψ ⁻¹' (D.V ∩ bd S) ∪ ψ ⁻¹' (D.V ∩ F) := by
      ext y
      simp only [mem_inter_iff, mem_union, mem_preimage, hG'V, hbdT]
      tauto
    rw [hsplit]
    refine (ncard_union_le _ _).trans (Nat.add_le_add ?_ hM)
    have hidx : X.index = (D.V ∩ bd S).ncard := ncard_roots_eq_boundary_vertices DX
    have hinjbd : InjOn ψ (ψ ⁻¹' (D.V ∩ bd S)) := fun y₁ h₁ y₂ _ h =>
      hinjF y₁ y₂ (fun hF => by
        have : ψ y₁ ∈ F ∩ bd S := ⟨hF, h₁.2⟩
        rw [hFbd] at this
        exact this) h
    rw [← hinjbd.ncard_image, image_preimage_eq _ hs, ← hidx]
    exact hk
  have hYmem : Y ∈ classC.{u, v, w} (surfaceComplexity T) (k + M) :=
    ⟨T, inferInstance, hT, le_rfl, hYidx, ⟨DY⟩⟩
  -- the chain of identifications
  let R : Set α := lab '' Q
  have hRV : ∀ a ∈ R, a ∉ V(X.G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hlabQ y hy
  have hfix : ∀ x ∈ V(Y.G), x ∉ R → π x = x := by
    rintro _ ⟨y, hy, rfl⟩ hR
    have hq : y ∉ Q := fun hq => hR ⟨y, hq, rfl⟩
    rw [hπlab y hy, hlabQ' y hq]
  have hRT : R ⊆ Y.T := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, ⟨hy.1, (hbdT y).2 (Or.inr hy.2.1)⟩, rfl⟩
  have hπR : ∀ r ∈ R, π r ∈ Y.T ∧ π r ∉ R := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hπlab y hy.1]
    have hy₀V : sl (ψ y) ∈ G'.V := (hG'V _).2 (by rw [hsl]; exact (hG'V y).1 hy.1)
    have hl : lab (sl (ψ y)) = σ (ψ y) := by rw [hlabQ' _ (hslQ y), hsl]
    refine ⟨⟨sl (ψ y), ⟨hy₀V, (hbdT _).2 (Or.inr (by rw [hsl]; exact hy.2.1))⟩, hl⟩, ?_⟩
    exact fun h => hRV _ h (hσV _ ((hG'V y).1 hy.1))
  have hTX : X.T = Y.T \ (R ∪ π '' R) := by
    ext a
    constructor
    · intro ha
      have haV : a ∈ V(X.G) := X.T_subset ha
      set z : S := (ι.vertexEquiv ⟨a, haV⟩ : S) with hzdef
      have hzV : z ∈ D.V := (ι.vertexEquiv ⟨a, haV⟩).2
      have hzbd : z ∈ bd S := (DX.mem_bd_iff a haV).2 ha
      have hσz : σ z = a := hσι ⟨a, haV⟩
      have hzF : z ∉ F := fun hF => by
        have : z ∈ F ∩ bd S := ⟨hF, hzbd⟩
        rw [hFbd] at this
        exact this
      have hyV : sl z ∈ G'.V := (hG'V _).2 (by rw [hsl]; exact hzV)
      have hyQ : sl z ∉ Q := fun hq => hzF (hsl z ▸ hq.2.1)
      refine ⟨⟨sl z, ⟨hyV, (hbdT _).2 (Or.inl (by rw [hsl]; exact hzbd))⟩, ?_⟩, ?_⟩
      · rw [hlabQ' _ hyQ, hsl, hσz]
      · rintro (h | ⟨_, ⟨y', hy', rfl⟩, h⟩)
        · exact hRV a h haV
        · rw [hπlab y' hy'.1, ← hσz] at h
          have := hσinj ((hG'V y').1 hy'.1) hzV h
          exact hzF (this ▸ hy'.2.1)
    · rintro ⟨⟨y, ⟨hyV, hyb⟩, rfl⟩, hnot⟩
      have hyQ : y ∉ Q := fun hq => hnot (Or.inl ⟨y, hq, rfl⟩)
      have hzV : ψ y ∈ D.V := (hG'V y).1 hyV
      rcases (hbdT y).1 hyb with hb | hF
      · rw [hlabQ' y hyQ, ← DX.mem_bd_iff _ (hσV _ hzV)]
        change ((ι.vertexEquiv ⟨σ (ψ y), hσV _ hzV⟩ : V(D.toGraph)) : S) ∈ bd S
        rw [hισ _ hzV]
        exact hb
      · exfalso
        have hyl : y = sl (ψ y) := by_contra fun hne => hyQ ⟨hyV, hF, hne⟩
        have hfib := hlift (ψ y) ⟨hzV, hF⟩
        obtain ⟨a, b, ha, hb, hab⟩ :=
          (one_lt_ncard_iff (hcut.finite_fiber (ψ y))).1 hfib
        obtain ⟨y', hy', hy'y⟩ : ∃ y', ψ y' = ψ y ∧ y' ≠ y := by
          by_cases hay : a = y
          · exact ⟨b, hb, fun h => hab (hay.trans h.symm)⟩
          · exact ⟨a, ha, hay⟩
        have hy'V : y' ∈ G'.V := (hG'V _).2 (hy' ▸ hzV)
        have hy'Q : y' ∈ Q := ⟨hy'V, hy' ▸ hF, by rw [hy']; exact fun h => hy'y (h.trans hyl.symm)⟩
        refine hnot (Or.inr ⟨lab y', ⟨y', hy'Q, rfl⟩, ?_⟩)
        rw [hπlab y' hy'V, hy', hlabQ' y hyQ]
  have hcl : ∀ e ∈ D.E, ψ '' (closure (ψ ⁻¹' e) ∩ G'.V) = closure e ∩ D.V := fun e _ => by
    rw [hpb.2, image_inter_preimage, image_closure_preimage_eq hc hs]
  have hGX : X.G = Y.G.map π := by
    refine Graph.ext ?_ fun e x y => ?_
    · ext a
      constructor
      · intro ha
        have hz : (ι.vertexEquiv ⟨a, ha⟩ : S) ∈ D.V := (ι.vertexEquiv ⟨a, ha⟩).2
        have hyV : sl (ι.vertexEquiv ⟨a, ha⟩ : S) ∈ G'.V := (hG'V _).2 (by rw [hsl]; exact hz)
        refine ⟨lab (sl (ι.vertexEquiv ⟨a, ha⟩ : S)), ⟨_, hyV, rfl⟩, ?_⟩
        rw [hπlab _ hyV, hsl, hσι]
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        rw [hπlab y hy]
        exact hσV _ ((hG'V y).1 hy)
    · rw [map_isLink]
      constructor
      · intro hl
        have heX : e ∈ E(X.G) := hl.edge_mem
        have hxV : x ∈ V(X.G) := hl.left_mem
        have hyV : y ∈ V(X.G) := hl.right_mem
        have h2 := (ι.isLink_iff ⟨e, heX⟩ ⟨x, hxV⟩ ⟨y, hyV⟩).1 hl
        set e₁ : D.E := ι.edgeEquiv ⟨e, heX⟩ with he₁
        set zx : S := (ι.vertexEquiv ⟨x, hxV⟩ : S) with hzx
        set zy : S := (ι.vertexEquiv ⟨y, hyV⟩ : S) with hzy
        have hcap : closure (e₁ : Set S) ∩ D.V = {zx, zy} := h2.2.2.2
        obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet (G := G'.toGraph) (eE.symm e₁).2
        have hcap' : closure ((eE.symm e₁ : G'.E) : Set T) ∩ G'.V = {a, b} := hab.2.2.2
        have hpair : ({ψ a, ψ b} : Set S) = {zx, zy} := by
          rw [← image_pair, ← hcap', heEs, hcl _ e₁.2, hcap]
        have hee : ((ee (eE.symm e₁) : E(X.G)) : β) = e := by
          change ((ι.edgeEquiv.symm (eE (eE.symm e₁)) : E(X.G)) : β) = e
          rw [Equiv.apply_symm_apply, he₁, Equiv.symm_apply_apply]
        have hσx : σ zx = x := hσι ⟨x, hxV⟩
        have hσy : σ zy = y := hσι ⟨y, hyV⟩
        rcases pair_eq_pair_iff.1 hpair with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · refine ⟨lab a, lab b, ⟨eE.symm e₁, ⟨a, hab.2.1⟩, ⟨b, hab.2.2.1⟩, hab, hee, rfl, rfl⟩,
            ?_, ?_⟩
          · rw [hπlab a hab.2.1, ha, hσx]
          · rw [hπlab b hab.2.2.1, hb, hσy]
        · refine ⟨lab b, lab a, ⟨eE.symm e₁, ⟨b, hab.2.2.1⟩, ⟨a, hab.2.1⟩, hab.symm, hee, rfl,
            rfl⟩, ?_, ?_⟩
          · rw [hπlab b hab.2.2.1, hb, hσx]
          · rw [hπlab a hab.2.1, ha, hσy]
      · rintro ⟨_, _, ⟨e₀, x₀, y₀, hl, he, rfl, rfl⟩, rfl, rfl⟩
        rw [hev, hev, hπlab _ x₀.2, hπlab _ y₀.2]
        have hx₀ := (hG'V _).1 x₀.2
        have hy₀ := (hG'V _).1 y₀.2
        have heq : ee e₀ = ι.edgeEquiv.symm (eE e₀) := rfl
        have h3 := (ι.isLink_iff (ee e₀) ⟨σ (ψ x₀), hσV _ hx₀⟩ ⟨σ (ψ y₀), hσV _ hy₀⟩).2
        rw [← he]
        refine h3 ?_
        have hι1 : ((ι.edgeEquiv (ι.edgeEquiv.symm (eE e₀)) : E(D.toGraph)) : Set S) =
            (eE e₀ : Set S) := congrArg Subtype.val (ι.edgeEquiv.apply_symm_apply (eE e₀))
        rw [heq, hι1, hισ _ hx₀, hισ _ hy₀]
        refine ⟨(eE e₀).2, hx₀, hy₀, ?_⟩
        have he₀ : ((e₀ : Set T)) = ψ ⁻¹' (eE e₀ : Set S) :=
          congrArg Subtype.val (eE.symm_apply_apply e₀).symm
        rw [← hcl _ (eE e₀).2, ← he₀, hl.2.2.2, image_pair]
  have hchain := obtainedByVertexIdChain_of_retraction R.ncard Y X π R (hQfin.image lab) rfl
    hGX hfix hRT hπR hTX
  exact mem_WGraftClass_of_obtainedByVertexIdChain (subset_isoGraftClass _ hYmem) hchain

end GraphMinor.GM08
