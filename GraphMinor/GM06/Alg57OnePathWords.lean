module

public import GraphMinor.GM06.Alg57WalkOrder
public import GraphMinor.GM06.Alg57CurrentCutEnds
public import GraphMinor.GM06.Alg57CurrentCutPathKeys
public import GraphMinor.GM06.Alg57CurrentFaceRotation
public import GraphMinor.GM06.Alg57FaceRegions
public import GraphMinor.GM06.Alg57PersistentRowRotation

/-!
# The words of the one path, read along `P₁`

The row `x.linkage[0]` lists the darts of `P₁` in order, as words. Here we read off where they
are on `P₁`:

* every word runs forward along `P₁`: its tail is `P₁(τ)` and its head is `P₁(σ)` with `τ < σ`
  (`path_word_params`). The reason is `param_lt_of_not_mem_walk'`: the walk of `P₁` up to the tail
  of a word is a connected piece of `P₁` from its start, and the head of the word is not on it;
* every ordinary word is the label of an actual dart at its tail, whose reverse is at its head
  (`exists_word_dart`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

section Generic

variable {S : Type*} [TopologicalSpace S]

/-- `param_lt_of_not_mem_walk` for a walk of any drawing whose point set lies on the arc. -/
theorem param_lt_of_not_mem_walk' [T2Space S] {Γ : Drawing S} {f : ℝ → S} (hf : Continuous f)
    (hinj : InjOn f (Icc 0 1)) {x : S} (W : GraphWalk Γ.toGraph (f 0) x)
    (hU : (walkDrawing Γ W).U ⊆ f '' Icc 0 1) {τ σ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (hx : f τ = x)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hyV : f σ ∈ Γ.V) (hy : f σ ∉ W.support) : τ < σ := by
  by_contra hle
  push_neg at hle
  set A := (walkDrawing Γ W).U
  have hA := isPreconnected_walkDrawing_U' Γ W
  let g : Icc (0 : ℝ) 1 → S := fun u => f u
  have hg : Continuous g := hf.comp continuous_subtype_val
  have hginj : Function.Injective g := fun u v h => Subtype.ext (hinj u.2 v.2 h)
  have hemb : IsClosedEmbedding g := hg.isClosedEmbedding hginj
  have hrange : A ⊆ range g := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hU hz
    exact ⟨⟨u, hu⟩, rfl⟩
  have hB : IsPreconnected (g ⁻¹' A) := by
    rw [← hemb.isInducing.isPreconnected_image, image_preimage_eq_inter_range,
      inter_eq_left.mpr hrange]
    exact hA
  have hC : IsPreconnected (Subtype.val '' (g ⁻¹' A) : Set ℝ) :=
    hB.image _ continuous_subtype_val.continuousOn
  have h0 : (0 : ℝ) ∈ Subtype.val '' (g ⁻¹' A) :=
    ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩,
      (mem_walkDrawing_U Γ W).mpr (Or.inl W.start_mem_support), rfl⟩
  have hτC : τ ∈ Subtype.val '' (g ⁻¹' A) :=
    ⟨⟨τ, hτ⟩, (mem_walkDrawing_U Γ W).mpr (Or.inl (hx ▸ W.end_mem_support)), rfl⟩
  obtain ⟨u, hu, hu'⟩ := hC.Icc_subset h0 hτC ⟨hσ.1, hle⟩
  have hσA : f σ ∈ A := by
    rw [← hu']
    exact hu
  exact hy (mem_support_of_mem_walkDrawing_U (Drawing.IsSubdrawing.refl Γ) W hσA hyV)

variable {α β : Type*} {Γ : Graph α β}

/-- Moving one step from the second walk to the first does not change the joined walk. -/
theorem append_cons_nil_append {u v w z : α} {e : β} (A : GraphWalk Γ u v) (hl : Γ.IsLink e v w)
    (hw : w ∈ Γ.vertexSet) (R : GraphWalk Γ w z) :
    (A.append (.cons hl (.nil hw))).append R = A.append (.cons hl R) := by
  induction A with
  | nil _ => rfl
  | cons h r ih => exact congrArg (GraphWalk.cons h) (ih hl)

end Generic

/-- The point set of the first part of a joined walk is part of the point set of the whole. -/
theorem walkDrawing_U_append_left {S : Type*} [TopologicalSpace S] [T1Space S] {Γ : Drawing S} {u v w : S}
    (A : GraphWalk Γ.toGraph u v) (B : GraphWalk Γ.toGraph v w) :
    (walkDrawing Γ A).U ⊆ (walkDrawing Γ (A.append B)).U := by
  intro z hz
  rw [mem_walkDrawing_U] at hz ⊢
  rw [GraphWalk.support_append, GraphWalk.edges_append]
  rcases hz with hz | ⟨e, he, hze⟩
  · exact Or.inl (List.mem_append_left _ hz)
  · exact Or.inr ⟨e, List.mem_append_left _ he, hze⟩

section Encoding

variable {S : Type*} [TopologicalSpace S] [T2Space S] {n : ℕ}
  {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → S} {Γ : Drawing S}
  {edge : Fin tagged.length → Set S}

/-- **Encoded words run forward along the arc.** Let a simple walk `A + W` lie on the arc `f`
from `f 0`, and let `W` be encoded by `row`. Then every word of `row` has its tail at `f τ` and its
head at `f σ` with `τ < σ`. -/
theorem encoded_word_params {f : ℝ → S} (hf : Continuous f) (hinj : InjOn f (Icc 0 1))
    {y z : S} {W : GraphWalk Γ.toGraph y z} {row : List ℕ}
    (henc : GM06WalkDartEncoding Γ.toGraph tagged vertex edge W row) :
    ∀ {s : S} (A : GraphWalk Γ.toGraph s y), f 0 = s → (A.append W).IsSimple →
      (walkDrawing Γ (A.append W)).U ⊆ f '' Icc 0 1 →
      ∀ d ∈ row, ∃ hd : d < 2 * tagged.length, ∃ τ σ : ℝ, τ ∈ Icc (0 : ℝ) 1 ∧
        σ ∈ Icc (0 : ℝ) 1 ∧ τ < σ ∧ vertex (gm06DartTail tagged ⟨d, hd⟩) = f τ ∧
        vertex (gm06DartHead tagged ⟨d, hd⟩) = f σ := by
  induction henc with
  | nil => intro s A _ _ _ d hd; simp at hd
  | @cons x y' z' e hl R row d hd hactive hedge htail hhead hrest ih =>
    intro s A hs hsimp hU d' hd'
    subst hs
    have hsupp : (A.append (.cons hl R)).support = A.support ++ R.support := by
      rw [GraphWalk.support_append]
      rfl
    have hmemU : ∀ v ∈ (A.append (.cons hl R)).support, ∃ τ ∈ Icc (0 : ℝ) 1, f τ = v := by
      intro v hv
      obtain ⟨τ, hτ, h⟩ := hU ((mem_walkDrawing_U _ _).mpr (Or.inl hv))
      exact ⟨τ, hτ, h⟩
    rcases List.mem_cons.mp hd' with rfl | hd'
    · refine ⟨hd, ?_⟩
      obtain ⟨τ, hτ, hfτ⟩ := hmemU x (by rw [hsupp]; exact List.mem_append_left _ A.end_mem_support)
      obtain ⟨σ, hσ, hfσ⟩ := hmemU y' (by
        rw [hsupp]; exact List.mem_append_right _ R.start_mem_support)
      refine ⟨τ, σ, hτ, hσ, ?_, htail.trans hfτ.symm, hhead.trans hfσ.symm⟩
      have hnd : (A.support ++ R.support).Nodup := hsupp ▸ hsimp
      have hy : f σ ∉ A.support := by
        rw [hfσ]
        intro h
        exact List.disjoint_of_nodup_append hnd h R.start_mem_support
      exact param_lt_of_not_mem_walk' hf hinj A
        ((walkDrawing_U_append_left A (.cons hl R)).trans hU) hτ hfτ hσ
        (hfσ ▸ hl.2.2.1) hy
    · have heq := append_cons_nil_append A hl hl.2.2.1 R
      exact ih (A.append (.cons hl (.nil hl.2.2.1))) rfl (heq ▸ hsimp) (heq ▸ hU) d' hd'

end Encoding

/-- The path `P₁` as a curve on the real line. -/
noncomputable def pathLine {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) :
    ℝ → ClosedCylinder :=
  fun s => L.curve 0 (projIcc 0 1 zero_le_one s)

theorem continuous_pathLine {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) :
    Continuous (pathLine L) :=
  (L.curve 0).continuous.comp continuous_projIcc

theorem pathLine_of_mem {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : pathLine L s = L.curve 0 ⟨s, hs⟩ := by
  simp only [pathLine, projIcc_of_mem _ hs]

theorem injOn_pathLine {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) :
    InjOn (pathLine L) (Icc 0 1) := by
  intro a ha b hb h
  rw [pathLine_of_mem L ha, pathLine_of_mem L hb] at h
  exact congrArg Subtype.val ((L.curve_parametrizes 0).1 h)

theorem image_pathLine {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) :
    pathLine L '' Icc 0 1 = (L.pathDrawing 0).U := by
  rw [← (L.curve_parametrizes 0).2.1]
  ext c
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [pathLine_of_mem L hs]
    exact mem_range_self _
  · rintro ⟨t, rfl⟩
    exact ⟨t.1, t.2, by rw [pathLine_of_mem L t.2]⟩

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {L : CylinderLinkage 1 G}
  (rep : GM06CurrentDrawingRep x G L)

/-- The row of the one path. -/
theorem linkage_zero_mem {d : ℕ} (hd : d ∈ x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos)) :
    d ∈ x.linkage.flatten :=
  List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd⟩

/-- **The words of `P₁` run forward.** For a word `d` of the row of `P₁`, its tail is `P₁(τ)` and
its head is `P₁(σ)` with `τ < σ`. -/
theorem path_word_params {d : ℕ} (hd : d ∈ x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos))
    (a b : Fin x.vertexCount) (ha : x.endpoints[d]?.getD 0 = a.val)
    (hb : x.endpoints[gm06DartMate d]?.getD 0 = b.val) :
    ∃ τ σ : unitInterval, τ < σ ∧ rep.vertex a = L.curve 0 τ ∧ rep.vertex b = L.curve 0 σ := by
  obtain ⟨W, hWs, henc, hP⟩ := rep.linkage.path 0
  have hs : cylinderM1Point 1 0 ∈ G.toGraph.vertexSet := by
    rw [← rep.source_point 0]; exact rep.vertex_mem _ (rep.source_live 0)
  have h0 : pathLine L 0 = cylinderM1Point 1 0 := by
    rw [pathLine_of_mem L ⟨le_rfl, zero_le_one⟩]
    exact (L.curve_parametrizes 0).2.2.1
  have hU : (walkDrawing G ((GraphWalk.nil (G := G.toGraph) (hs)).append W)).U ⊆
      pathLine L '' Icc 0 1 := by
    change (walkDrawing G W).U ⊆ _
    rw [hP, image_pathLine]
  obtain ⟨hdb, τ, σ, hτ, hσ, hlt, htail, hhead⟩ := encoded_word_params (continuous_pathLine L)
    (injOn_pathLine L) henc (GraphWalk.nil hs) h0 hWs hU d hd
  obtain ⟨hta, hhb⟩ := gm06Dart_endpoint_words rep.tagged ⟨d, hdb⟩
  rw [← rep.endpoints] at hta hhb
  have hta' : gm06DartTail rep.tagged ⟨d, hdb⟩ = a := Fin.ext (hta.symm.trans ha)
  have hhb' : gm06DartHead rep.tagged ⟨d, hdb⟩ = b := Fin.ext (hhb.symm.trans hb)
  refine ⟨⟨τ, hτ⟩, ⟨σ, hσ⟩, hlt, ?_, ?_⟩
  · rw [← hta', htail, pathLine_of_mem L hτ]
  · rw [← hhb', hhead, pathLine_of_mem L hσ]

/-- The edge of a word of the row of `P₁` is an edge of `P₁`. -/
theorem path_word_edge {d : ℕ} (hd : d ∈ x.linkage[0]'(by rw [rep.linkage.1]; exact one_pos))
    (hdb : d < 2 * rep.tagged.length) :
    rep.edge ⟨d / 2, by omega⟩ ∈ (L.pathDrawing 0).E := by
  obtain ⟨W, -, henc, hP⟩ := rep.linkage.path 0
  have hmem : rep.edge ⟨d / 2, by omega⟩ ∈ W.edges := (henc.edge_mem_iff _).mpr ⟨d, hd, hdb, rfl⟩
  rw [← hP, walkDrawing_E]
  exact hmem

/-- **The dart of an ordinary word.** An active ordinary word `d` is the label of a dart at the
vertex of its tail slot, whose reverse is at the vertex of its head slot, along its edge. -/
theorem exists_word_dart {d : ℕ} (hd : d < 2 * rep.tagged.length)
    (hactive : (rep.tagged[d / 2]'(by omega)).2 = 1) (a b : Fin x.vertexCount)
    (ha : x.endpoints[d]?.getD 0 = a.val) (hb : x.endpoints[gm06DartMate d]?.getD 0 = b.val) :
    ∃ c : DrawingDart (cylinderSphereDrawing rep.cuffed), persistentDartLabel rep.label c = d ∧
      dartVertex rep.par c = cylinderToSphere (rep.vertex a) ∧
      dartVertex rep.par (dartFlip _ c) = cylinderToSphere (rep.vertex b) ∧
      c.1.1 = cylinderToSphere '' rep.edge ⟨d / 2, by omega⟩ := by
  have hmd : gm06DartMate d < 2 * rep.tagged.length := gm06DartMate_lt hd
  have hactive' : (rep.tagged[gm06DartMate d / 2]'(by omega)).2 = 1 := by
    simpa only [gm06DartMate_edge] using hactive
  have hra := rep.ordinary_word_mem_row a d hd hactive ha
  have hrb := rep.ordinary_word_mem_row b (gm06DartMate d) hmd hactive' hb
  have haL := rep.live_of_mem_row hra
  have hbL := rep.live_of_mem_row hrb
  obtain ⟨c, hcv, hcl⟩ := exists_persistentDart_of_mem_row (rep.rows a haL) hra
  obtain ⟨c', hc'v, hc'l⟩ := exists_persistentDart_of_mem_row (rep.rows b hbL) hrb
  have hflip : dartFlip _ c = c' := persistentDartLabel_injective rep.label
    (by rw [persistentDartLabel_flip, hcl, hc'l])
  refine ⟨c, hcl, hcv, hflip ▸ hc'v, ?_⟩
  obtain ⟨f, hf, hfl⟩ := rep.ordinary_labels ⟨d / 2, by omega⟩ hactive
  have hlab : rep.label ⟨c.1.1, c.2⟩ = rep.label f := by
    rw [hfl]
    have h : 2 * rep.label ⟨c.1.1, c.2⟩ + c.1.2.toNat = d := hcl
    have hb1 : c.1.2.toNat ≤ 1 := by cases c.1.2 <;> simp
    show _ = d / 2
    omega
  have := rep.label.injective hlab
  rw [← hf]
  exact congrArg Subtype.val this

end GM06CurrentDrawingRep

end GraphMinor.GM06
