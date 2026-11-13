module

public import GraphMinor.GM08.Section15PocketFan

/-!
# Graph Minors VIII, printed (15.1): the parts of the train

The train of our proof of the printed (15.1) (`Section15PrintedFinal.lean`) is glued from
three kinds of parts, each cut out of the framing by hoops:
* a piece with no edges, from the first end set `A` to a junction `J`
  (`Tube.Framing.decomposes_base`);
* the bridges of a pocket, padded by `J` (`Tube.Framing.decomposes_step`, which adds them after
  what comes before);
* the middle, where every hoop has at least `r` vertices (`Tube.Framing.decomposes_middle`, from
  Lemma 3).

`Tube.Framing.split` describes the vertices and edges on the two sides of a normal hoop.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v}

namespace Tube.Framing

variable {S : Type w} [TopologicalSpace S] {τ : Tube S} {X : Graft α β}

/-- A graft with no edges whose roots are all its vertices `J` is tubular, of printed width at
least `|J| + 1` (Fact E with an empty piece). -/
theorem edgeless_mem (fr : τ.Framing X) (cap : CylinderSphereCap S) {J : Set α}
    (hJV : J ⊆ V(X.G)) {t u : ℕ} (ht : t ≤ J.ncard + 1) (hu : J.ncard ≤ u) (h hf) :
    Graft.mk (subOf X.G J ∅) J h hf ∈ printedTubularClass t u := by
  classical
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have : CompactSpace S := hS.1.1
  obtain ⟨p₀, -, -, hp₀, -⟩ := τ.isHoop_F₁.1.exists_three
  have : Nonempty S := ⟨p₀⟩
  have : T2Space cap.Z := cap.t2Space_Z
  have : ConnectedSpace cap.Z := cap.connectedSpace
  obtain ⟨Γz, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
  have hb : IsGraphBij X.G Γz.toGraph (cap.j ∘ fr.iso.fv) (image cap.j ∘ fr.iso.fe) :=
    fr.iso.isGraphBij.trans
      (isGraphBij_of_matched_embedding cap.isClosedEmbedding.isEmbedding hm)
  obtain ⟨htub, hwid⟩ := le_tubularPrintedWidth_of_piece cap.isClosedSurface cap.isSphere hb
    cap.isClosedDisc_D₁ (Vp := ∅) (att := ∅) (Ep := ∅) (empty_subset _) (empty_subset _)
    (fun _ he => absurd he (notMem_empty _)) (empty_subset _) (by simp)
    (fun _ hx => absurd hx (notMem_empty _)) (fun _ he => absurd he (notMem_empty _))
    (fun _ hx => absurd hx (notMem_empty _)) (fun _ hx => absurd hx (notMem_empty _))
    (fun _ he => absurd he (notMem_empty _)) hJV (disjoint_empty _)
    (Graft.mk (subOf X.G J ∅) J h hf) (by rw [empty_union]) (by rw [union_empty])
  refine ⟨htub, ?_, hu⟩
  change ((J.ncard + 1 : ℕ) : ℕ∞) ≤ _ at hwid
  exact le_trans (by exact_mod_cast ht) hwid

/-- **Splitting at a normal hoop.** For hoops `G₁`, `G`, `G₂` in this order along the cylinder,
with `G` normal, the vertices and edges between `G₁` and `G₂` are those between `G₁` and `G`
together with those between `G` and `G₂`. The two vertex sets meet in the vertices on `G`, and
no edge lies on both sides. -/
theorem split (fr : τ.Framing X) (cap : CylinderSphereCap S) {G₁ G G₂ : Set S}
    (h₁ : IsHoop G₁) (h : IsHoop G) (h₂ : IsHoop G₂) (hN : τ.Γ.IsNormal G)
    (hle1 : cap.disc₁ τ.isCylinder.1 h₁ ⊆ cap.disc₁ τ.isCylinder.1 h)
    (hle2 : cap.disc₁ τ.isCylinder.1 h ⊆ cap.disc₁ τ.isCylinder.1 h₂) :
    fr.vertsIn (cylinderBetween G₁ G) ∪ fr.vertsIn (cylinderBetween G G₂) =
        fr.vertsIn (cylinderBetween G₁ G₂) ∧
      fr.vertsIn (cylinderBetween G₁ G) ∩ fr.vertsIn (cylinderBetween G G₂) = fr.vertsIn G ∧
      fr.edgesIn (cylinderBetween G₁ G) ∪ fr.edgesIn (cylinderBetween G G₂) =
        fr.edgesIn (cylinderBetween G₁ G₂) ∧
      Disjoint (fr.edgesIn (cylinderBetween G₁ G)) (fr.edgesIn (cylinderBetween G G₂)) := by
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hunion := cap.cylinderBetween_union hS h₁ h h₂ hle1 hle2
  have hinter := cap.cylinderBetween_inter hS h₁ h h₂ hle1 hle2
  refine ⟨by rw [← fr.vertsIn_union, hunion], by rw [← fr.vertsIn_inter, hinter], ?_, ?_⟩
  · apply Subset.antisymm
    · rw [← hunion]
      exact union_subset (fr.edgesIn_mono subset_union_left)
        (fr.edgesIn_mono subset_union_right)
    · rintro e ⟨he, hsub⟩
      rcases cap.edge_subset_left_or_right hS τ.Γ h₁ h h₂ hle1 hle2 hN
          (fr.iso.edgeEquiv ⟨e, he⟩).2 hsub with ⟨hA, -⟩ | ⟨hB, -⟩
      exacts [.inl ⟨he, hA⟩, .inr ⟨he, hB⟩]
  · rw [disjoint_left]
    rintro e ⟨he, h1⟩ ⟨he', h2⟩
    have hed := (fr.iso.edgeEquiv ⟨e, he⟩).2
    obtain ⟨p, hp⟩ := hed.1
    have hpG : p ∈ G := hinter ▸ ⟨h1 hp, h2 hp⟩
    exact (hed.2.1 hp).2 (hN ⟨hpG, (hed.2.1 hp).1⟩)

/-- **An empty strip.** If the drawing between two hoops `L'`, `L''` lies on `L''`, with `L''`
normal, then the vertices between them lie on `L''` and no edge lies between them. -/
theorem strip (fr : τ.Framing X) {L' L'' : Set S} (hN : τ.Γ.IsNormal L'')
    (hstrip : τ.Γ.U ∩ cylinderBetween L' L'' ⊆ L'') :
    fr.vertsIn (cylinderBetween L' L'') ⊆ fr.vertsIn L'' ∧
      fr.edgesIn (cylinderBetween L' L'') = ∅ := by
  refine ⟨fun x ⟨hx, hxR⟩ => ⟨hx, hstrip ⟨τ.Γ.V_subset_U (fr.iso.vertexEquiv ⟨x, hx⟩).2, hxR⟩⟩,
    eq_empty_of_forall_notMem fun e ⟨he, hsub⟩ => ?_⟩
  have hed := (fr.iso.edgeEquiv ⟨e, he⟩).2
  obtain ⟨p, hp⟩ := hed.1
  exact (hed.2.1 hp).2 (hN ⟨hstrip ⟨(hed.2.1 hp).1, hsub hp⟩, (hed.2.1 hp).1⟩)

/-- The ends of an edge drawn in a closed set are drawn there too, so they lie in its padded
vertex set. -/
theorem ends_mem_of_isClosed (fr : τ.Framing X) {R : Set S} (hR : IsClosed R) (J : Set α) :
    ∀ e ∈ fr.edgesIn R, ∀ x y, X.G.IsLink e x y → x ∈ fr.vertsIn R ∪ J :=
  fun _ he _ _ hl => .inl (fr.ends_mem_vertsIn_of_isClosed hR he hl).1

/-- **The start of the train.** The piece with no edges from `A` to `J`, written as the part
between a normal hoop `G₀` and itself, padded by `J`, where `G₀` carries no vertex outside
`J`. -/
theorem decomposes_base (fr : τ.Framing X) (cap : CylinderSphereCap S) {G₀ : Set S}
    (hN₀ : τ.Γ.IsNormal G₀) {A J : Set α} (hJV : J ⊆ V(X.G)) (hG₀J : fr.vertsIn G₀ ⊆ J)
    (hAJ : A ⊆ J) {t u : ℕ} (ht : t ≤ J.ncard + 1) (hu : J.ncard ≤ u) (r : ℕ) :
    Decomposes (printedTubularClass t u) X (fr.vertsIn (cylinderBetween G₀ G₀) ∪ J)
      (fr.edgesIn (cylinderBetween G₀ G₀)) A J A J r := by
  rw [cylinderBetween_self]
  have hE : fr.edgesIn G₀ = ∅ := by
    have := (fr.strip hN₀ (L' := G₀) (by rw [cylinderBetween_self]; exact inter_subset_right)).2
    rwa [cylinderBetween_self] at this
  rw [hE, union_eq_right.mpr hG₀J]
  refine Decomposes.single r hJV (union_subset hAJ subset_rfl) fun h hf => ?_
  exact GraftPathDecomposition.graft_mem_of_eq rfl (union_eq_right.mpr hAJ)
    (fr.edgeless_mem cap hJV ht hu subset_rfl hf)

/-- **Adding the bridges of a pocket.** Let the part between `G₀` and `H`, padded by `J`, have a
decomposition from `A` to `J` all of whose later junctions are `J`. Let `H`, `L'` bound a pocket,
and let the drawing between `L'` and `L''` lie on `L''`. Then the part between `G₀` and `L''`,
padded by `J`, has such a decomposition too: the padded bridges of the pocket come next. -/
theorem decomposes_step (fr : τ.Framing X) (cap : CylinderSphereCap S) {G₀ H L' L'' : Set S}
    (h₀ : IsHoop G₀) (hH : IsHoop H) (hL' : IsHoop L') (hL'' : IsHoop L'')
    (hNH : τ.Γ.IsNormal H) (hNL' : τ.Γ.IsNormal L') (hNL'' : τ.Γ.IsNormal L'')
    (le₁ : cap.disc₁ τ.isCylinder.1 h₀ ⊆ cap.disc₁ τ.isCylinder.1 hH)
    (le₂ : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 hL')
    (le₃ : cap.disc₁ τ.isCylinder.1 hL' ⊆ cap.disc₁ τ.isCylinder.1 hL'')
    (hpocket : fr.vertsIn H = fr.vertsIn L')
    (hstrip : τ.Γ.U ∩ cylinderBetween L' L'' ⊆ L'')
    {A J Y₁' : Set α} {r t u : ℕ} (hJV : J ⊆ V(X.G)) (hHJ : fr.vertsIn H ⊆ J)
    (hJin : J ∩ fr.vertsIn (cylinderBetween H L') ⊆ fr.vertsIn H)
    (hL''J : fr.vertsIn L'' ⊆ J) (ht : t ≤ J.ncard + 1) (hu : J.ncard ≤ u) (hr : J.ncard = r)
    (hD : Decomposes (printedTubularClass t u) X (fr.vertsIn (cylinderBetween G₀ H) ∪ J)
      (fr.edgesIn (cylinderBetween G₀ H)) A J Y₁' J r) :
    Decomposes (printedTubularClass t u) X (fr.vertsIn (cylinderBetween G₀ L'') ∪ J)
      (fr.edgesIn (cylinderBetween G₀ L'')) A J J J r := by
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have hP := fr.decomposes_pocket cap hH hL' hNH hNL' le₂ hpocket hJV hHJ hJin ht hu hr
  have hlam : ∀ {F₁ F₂ : Set S} (h₁ : IsHoop F₁) (h₂ : IsHoop F₂),
      cap.disc₁ hS.1 h₁ ⊆ cap.disc₁ hS.1 h₂ → IsClosed (cylinderBetween F₁ F₂) :=
    fun h₁ h₂ hle => isClosed_cylinderBetween ((cap.areLaminarHoops_iff hS h₁ h₂).mpr (.inl hle))
  obtain ⟨hV1, hI1, hE1, hD1⟩ := fr.split cap h₀ hH hL' hNH le₁ le₂
  obtain ⟨hV2, -, hE2, -⟩ := fr.split cap h₀ hL' hL'' hNL' (le₁.trans le₂) le₃
  obtain ⟨hst, hstE⟩ := fr.strip hNL'' hstrip
  have hA := hD.append hP (fr.edgesIn_subset_E _) (fr.edgesIn_subset_E _)
    (fr.ends_mem_of_isClosed (hlam h₀ hH le₁) J) (fr.ends_mem_of_isClosed (hlam hH hL' le₂) J)
    (by
      have hd : ∀ a b : Set α, (a ∪ J) ∩ (b ∪ J) = (a ∩ b) ∪ J := fun a b => by
        ext x; simp only [mem_inter_iff, mem_union]; tauto
      rw [hd, hI1]; exact union_eq_right.mpr hHJ)
    hD1 hr
  refine hA.congr_sets ?_ ?_
  · rw [← hV2, ← hV1]
    apply Subset.antisymm
    · rintro x ((hx | hx) | (hx | hx))
      exacts [.inl (.inl (.inl hx)), .inr hx, .inl (.inl (.inr hx)), .inr hx]
    · rintro x (((hx | hx) | hx) | hx)
      exacts [.inl (.inl hx), .inr (.inl hx), .inl (.inr (hL''J (hst hx))), .inl (.inr hx)]
  · rw [← hE2, hstE, union_empty, hE1]

/-- The vertices that the induced framing of a sub-tube puts in a set are the vertices between
its hoops that the framing puts there. -/
theorem subFraming_vertsIn (fr : τ.Framing X) {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂) (A : Set S) :
    (fr.subFraming hlam hN₁ hN₂).vertsIn A = fr.vertsIn (cylinderBetween H₁ H₂) ∩ fr.vertsIn A := by
  ext v
  exact ⟨fun ⟨hv, h⟩ => ⟨hv, hv.1, h⟩, fun ⟨hv, _, h⟩ => ⟨hv, h⟩⟩

theorem subGraph_eq_subOf (fr : τ.Framing X) {R : Set S} (hR : IsClosed R) :
    fr.subGraph R hR = subOf X.G (fr.vertsIn R) (fr.edgesIn R) :=
  (Compatible.of_le_le (fr.subGraph_le R hR) (subOf_le X.G (fr.vertsIn_subset_V R) _)).ext rfl
    (by
      rw [fr.subGraph_edgeSet, subOf_edgeSet_of_ends X.G (fr.edgesIn_subset_E R)
        fun _ he _ _ hl => (fr.ends_mem_vertsIn_of_isClosed hR he hl).1])

/-- **The middle.** If every normal hoop between `G₁` and `G₂` carries at least `r` vertices,
then the part between them has a decomposition (Lemma 3) from the vertices on `G₁` to those on
`G₂`, with inner junctions of `r` vertices, and with `r` disjoint paths from the vertices on `G₁`
to those on `G₂`, and to the second to last junction when `G₁` carries `r` vertices. -/
theorem decomposes_middle (fr : τ.Framing X) {G₁ G₂ : Set S} (hlam : AreLaminarHoops G₁ G₂)
    (hN₁ : τ.Γ.IsNormal G₁) (hN₂ : τ.Γ.IsNormal G₂) {r k : ℕ}
    (hmin : ∀ F : Set S, IsHoop F → τ.Γ.IsNormal F → F ⊆ cylinderBetween G₁ G₂ →
      r ≤ (F ∩ τ.Γ.V).ncard)
    (hk₁ : (fr.vertsIn G₁).ncard ≤ k + r) (hk₂ : (fr.vertsIn G₂).ncard ≤ k + r)
    (hkT : (fr.vertsIn G₁ ∪ fr.vertsIn G₂).ncard ≤ k + 2 * r) :
    ∃ Y₀' Y₁', Decomposes (printedTubularClass (r + 1) (k + 2 * r)) X
      (fr.vertsIn (cylinderBetween G₁ G₂)) (fr.edgesIn (cylinderBetween G₁ G₂))
      (fr.vertsIn G₁) Y₀' Y₁' (fr.vertsIn G₂) r ∧
      HasDisjointGraphPathsFromTo X.G (fr.vertsIn G₁) (fr.vertsIn G₂) r ∧
      ((fr.vertsIn G₁).ncard = r → HasDisjointGraphPathsFromTo X.G (fr.vertsIn G₁) Y₁' r) := by
  have : T2Space S := τ.t2Space
  have hcl := isClosed_cylinderBetween hlam
  set σ := τ.subTube hlam hN₁ hN₂ with hσ
  have hσV : σ.Γ.V = τ.Γ.V ∩ cylinderBetween G₁ G₂ := interSet_V_of_isClosed τ.Γ hcl
  have hv : ∀ A ⊆ cylinderBetween G₁ G₂, (fr.subFraming hlam hN₁ hN₂).vertsIn A = fr.vertsIn A :=
    fun A hA => by rw [subFraming_vertsIn, inter_eq_right.mpr (fr.vertsIn_mono hA)]
  have h₁ := hv G₁ (subset_cylinderBetween_left hlam)
  have h₂ := hv G₂ (subset_cylinderBetween_right hlam)
  obtain ⟨D, hD0, hDr, hint, hpaths⟩ := σ.exists_strong_decomposition
    (fr.subFraming hlam hN₁ hN₂) (r := r) (k := k)
    (fun F hF hN hsub => by
      have hN' := (τ.subTube_isNormal_iff hlam hN₁ hN₂ hsub).mp hN
      have := hmin F hF hN' hsub
      change r ≤ (F ∩ σ.Γ.V).ncard
      rwa [hσV, ← inter_assoc, inter_eq_left.mpr
        (show F ∩ τ.Γ.V ⊆ cylinderBetween G₁ G₂ from inter_subset_left.trans hsub)])
    (by change ((fr.subFraming hlam hN₁ hN₂).vertsIn G₁).ncard ≤ k + r; rw [h₁]; exact hk₁)
    (by change ((fr.subFraming hlam hN₁ hN₂).vertsIn G₂).ncard ≤ k + r; rw [h₂]; exact hk₂)
    hkT
  change D.Yn 0 = (fr.subFraming hlam hN₁ hN₂).vertsIn G₁ at hD0
  change D.Yn D.r = (fr.subFraming hlam hN₁ hN₂).vertsIn G₂ at hDr
  rw [h₁] at hD0
  rw [h₂] at hDr
  have hn := D.hr
  have hle : (fr.subGraft hlam).G ≤ X.G := fr.subGraph_le _ hcl
  refine ⟨D.Yn 1, D.Yn (D.r - 1), ⟨fr.subGraft hlam, fr.subGraph_eq_subOf hcl, rfl, D, hD0, rfl,
    rfl, hDr, hint⟩, ?_, fun hJ => ?_⟩
  · rw [← hD0, ← hDr]
    exact hasDisjointGraphPathsFromTo_of_le hle (hpaths 0 D.r hn le_rfl)
  · rcases Nat.eq_zero_or_pos (D.r - 1) with h0 | hpos
    · rw [h0, hD0, ← hJ]
      exact hasDisjointGraphPathsFromTo_self X.G (fr.vertsIn_subset_V _)
        (X.finite_G.1.subset (fr.vertsIn_subset_V _))
    · rw [← hD0]
      exact hasDisjointGraphPathsFromTo_of_le hle (hpaths 0 (D.r - 1) hpos (Nat.sub_le _ _))

end Tube.Framing

end GraphMinor.GM08
