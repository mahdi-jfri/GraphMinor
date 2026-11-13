module

public import GraphMinor.GM08.Section15Pieces
public import GraphMinor.GM08.Section15Decomposes
public import GraphMinor.GM08.Section9Transport
public import GraphMinor.GM08.Section15ImageIso

/-!
# Graph Minors VIII, printed (15.1): the bridges of a pocket

A *pocket* of a tube is the part of the drawing between two hoops `H₁`, `H₂` that carry the same
vertex set `C`. Lemma 2 of the proof of the printed (15.1) in `Section15PrintedFinal.lean` says that
each bridge of a pocket has at most two attachments in `C`, and the remark after it turns each
bridge, padded by a set `J ⊇ C` of isolated roots, into a tubular graft of printed width at least
`|J| + 1` (Fact E). This file proves both and puts the padded bridges side by side in a
path-decomposition all of whose junctions are `J` (`Tube.Framing.decomposes_pocket`).

The bridges are taken in the sphere obtained by capping the cylinder. Let `D₁` be the disc on the
far side of `H₁` and `D₂` the disc on the far side of `H₂`. The drawing outside `D₁ ∪ D₂` is the
pocket without the vertices of `C`, and a bridge is the part of the graph drawn in one of its
connected components. A component has at most two points of `C` in its closure
(`false_of_three_attachments`). The disc for Fact E is the closed disc bounded by `H₁` that holds
the pocket. A bridge meets its boundary only in its attachments.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v}

/-- A point of `W` in the closure of a connected component of `W` lies in that component. -/
theorem mem_connectedComponentIn_of_mem_closure {Z : Type*} [TopologicalSpace Z] {W : Set Z}
    {z p : Z} (hz : z ∈ W) (hp : p ∈ W) (hcl : p ∈ closure (connectedComponentIn W z)) :
    p ∈ connectedComponentIn W z := by
  have hK : IsPreconnected (connectedComponentIn W z) := isPreconnected_connectedComponentIn
  have h1 : IsPreconnected (insert p (connectedComponentIn W z)) :=
    hK.subset_closure (subset_insert _ _) (insert_subset hcl subset_closure)
  exact h1.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hz))
    (insert_subset hp (connectedComponentIn_subset _ _)) (mem_insert _ _)

/-- **The bridges of a pocket.** Let `H₁`, `H₂` be normal hoops of a tube, with `H₂` on the far
side of `H₁` from the first end, carrying the same vertices `C`. Let `J ⊇ C` be a set of vertices
of `X` that meets the part between `H₁` and `H₂` only in `C`. Then that part, padded by `J`, has a
path-decomposition into tubular grafts of printed width at least `|J| + 1` and index `|J|`, all of
whose junctions are `J`.

There is one piece for each bridge, and one more piece with no edges; the extra piece makes the
fan nonempty. -/
theorem Tube.Framing.decomposes_pocket {S : Type w} [TopologicalSpace S] {τ : Tube S}
    {X : Graft α β} (fr : τ.Framing X) (cap : CylinderSphereCap S) {H₁ H₂ : Set S}
    (hH₁ : IsHoop H₁) (hH₂ : IsHoop H₂) (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hle : cap.disc₁ τ.isCylinder.1 hH₁ ⊆ cap.disc₁ τ.isCylinder.1 hH₂)
    (hC : fr.vertsIn H₁ = fr.vertsIn H₂) {J : Set α} (hJV : J ⊆ V(X.G))
    (hCJ : fr.vertsIn H₁ ⊆ J) (hJin : J ∩ fr.vertsIn (cylinderBetween H₁ H₂) ⊆ fr.vertsIn H₁)
    {t u k : ℕ} (ht : t ≤ J.ncard + 1) (hu : J.ncard ≤ u) (hk : J.ncard = k) :
    Decomposes (printedTubularClass t u) X (fr.vertsIn (cylinderBetween H₁ H₂) ∪ J)
      (fr.edgesIn (cylinderBetween H₁ H₂)) J J J J k := by
  classical
  have : T2Space S := τ.t2Space
  have hS := τ.isCylinder
  have : CompactSpace S := hS.1.1
  obtain ⟨p₀, -, -, hp₀, -⟩ := hH₁.1.exists_three
  have : Nonempty S := ⟨p₀⟩
  have : T2Space cap.Z := cap.t2Space_Z
  have : ConnectedSpace cap.Z := cap.connectedSpace
  obtain ⟨Γz, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
  have hb : IsGraphBij X.G Γz.toGraph (cap.j ∘ fr.iso.fv) (image cap.j ∘ fr.iso.fe) :=
    fr.iso.isGraphBij.trans
      (isGraphBij_of_matched_embedding cap.isClosedEmbedding.isEmbedding hm)
  set φ := cap.j ∘ fr.iso.fv with hφ
  set ψ := image cap.j ∘ fr.iso.fe with hψ
  have hvR : ∀ x ∈ V(X.G), ∀ R : Set cap.Z, x ∈ fr.vertsIn (cap.j ⁻¹' R) ↔ φ x ∈ R := by
    intro x hx R
    rw [show x = (⟨x, hx⟩ : V(X.G)).1 from rfl, fr.mem_vertsIn_iff]
    simp only [hφ, Function.comp, fr.iso.fv_of_mem hx, mem_preimage]
  have heR : ∀ e ∈ E(X.G), ∀ R : Set cap.Z, e ∈ fr.edgesIn (cap.j ⁻¹' R) ↔ ψ e ⊆ R := by
    intro e he R
    simp only [hψ, Function.comp, fr.iso.fe_of_mem he, image_subset_iff]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨he, h⟩⟩
  -- the four discs
  set D₁ := cap.disc₁ hS.1 hH₁ with hD₁def
  set E₂ := cap.disc₂ hS.1 hH₁ with hE₂def
  set E₁ := cap.disc₁ hS.1 hH₂ with hE₁def
  set D₂ := cap.disc₂ hS.1 hH₂ with hD₂def
  obtain ⟨hD₁, hE₂, hbD₁, hbE₂, hcup₁, hcap₁, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hH₁
  obtain ⟨hE₁, hD₂, hbE₁, hbD₂, hcup₂, hcap₂, -, -⟩ := cap.disc₁_disc₂_spec hS.1 hH₂
  have hD₂E₂ : D₂ ⊆ E₂ := (cap.disc₂_subset_iff_disc₁_subset hS.1 hH₁ hH₂).mpr hle
  have hreg : cylinderBetween H₁ H₂ = cap.j ⁻¹' (E₁ ∩ E₂) :=
    cap.cylinderBetween_eq_of_disc₁_subset hS hH₁ hH₂ hle
  have hH₁eq : H₁ = cap.j ⁻¹' (D₁ ∩ E₂) := by rw [hcap₁, preimage_image_eq _ cap.inj]
  have hH₂eq : H₂ = cap.j ⁻¹' (E₁ ∩ D₂) := by rw [hcap₂, preimage_image_eq _ cap.inj]
  have hRcl : IsClosed (E₁ ∩ E₂) := hE₁.isCompact.isClosed.inter hE₂.isCompact.isClosed
  -- the drawing in the sphere
  have hU : Γz.U = cap.j '' τ.Γ.U := by simpa only [sdiff_empty] using hm.image_U.symm
  have hV : Γz.V = cap.j '' τ.Γ.V := by simpa only [sdiff_empty] using hm.image_V.symm
  have hnorm : ∀ {H : Set S}, τ.Γ.IsNormal H → cap.j '' H ∩ Γz.U ⊆ Γz.V := by
    rintro H hN z ⟨⟨p, hp, rfl⟩, hz⟩
    rw [hU] at hz
    obtain ⟨q, hq, hqp⟩ := hz
    rw [cap.inj hqp] at hq
    rw [hV]
    exact ⟨p, hN ⟨hp, hq⟩, rfl⟩
  -- the vertices `C` and the pocket
  set C := fr.vertsIn H₁ with hCdef
  have hCV : C ⊆ V(X.G) := fr.vertsIn_subset_V _
  have hmemC : ∀ x ∈ V(X.G), x ∈ C ↔ φ x ∈ D₁ ∩ E₂ := fun x hx => by
    have := hvR x hx (D₁ ∩ E₂)
    rwa [← hH₁eq] at this
  have hmemC₂ : ∀ x ∈ V(X.G), x ∈ C ↔ φ x ∈ E₁ ∩ D₂ := fun x hx => by
    have := hvR x hx (E₁ ∩ D₂)
    rwa [← hH₂eq, ← hC] at this
  have hmemR : ∀ x ∈ V(X.G), x ∈ fr.vertsIn (cylinderBetween H₁ H₂) ↔ φ x ∈ E₁ ∩ E₂ :=
    fun x hx => by rw [hreg]; exact hvR x hx _
  have hmemE : ∀ e ∈ E(X.G), e ∈ fr.edgesIn (cylinderBetween H₁ H₂) ↔ ψ e ⊆ E₁ ∩ E₂ :=
    fun e he => by rw [hreg]; exact heR e he _
  have hCR : ∀ x ∈ C, φ x ∈ E₁ ∩ E₂ := fun x hx =>
    have h := (hmemC x (hCV hx)).mp hx
    ⟨hle h.1, h.2⟩
  have hφU : ∀ x ∈ V(X.G), φ x ∈ Γz.U := fun x hx => Γz.V_subset_U (hb.bijV.mapsTo hx)
  set W := Γz.U \ (D₁ ∪ D₂) with hW
  have hWE : W ⊆ E₁ ∩ E₂ := by
    rintro z ⟨-, hz⟩
    refine ⟨?_, ?_⟩
    · exact (hcup₂ ▸ mem_univ z : z ∈ E₁ ∪ D₂).resolve_right fun h => hz (.inr h)
    · exact (hcup₁ ▸ mem_univ z : z ∈ D₁ ∪ E₂).resolve_left fun h => hz (.inl h)
  have hW_of : ∀ x ∈ V(X.G), φ x ∈ E₁ ∩ E₂ → x ∉ C → φ x ∈ W := by
    intro x hx hR hxC
    refine ⟨hφU x hx, ?_⟩
    rintro (h | h)
    · exact hxC ((hmemC x hx).mpr ⟨h, hR.2⟩)
    · exact hxC ((hmemC₂ x hx).mpr ⟨hR.1, h⟩)
  have hof_W : ∀ x ∈ V(X.G), φ x ∈ W → x ∈ fr.vertsIn (cylinderBetween H₁ H₂) ∧ x ∉ C :=
    fun x hx hW' => ⟨(hmemR x hx).mpr (hWE hW'),
      fun hxC => hW'.2 (.inl ((hmemC x hx).mp hxC).1)⟩
  -- edges
  have hψE : ∀ e ∈ E(X.G), ψ e ∈ Γz.E := fun e he => hb.bijE.mapsTo he
  have hψW : ∀ e ∈ E(X.G), ψ e ⊆ E₁ ∩ E₂ → ψ e ⊆ W := by
    intro e he hR z hz
    have hzU := (hψE e he).2.1 hz
    refine ⟨hzU.1, ?_⟩
    rintro (h | h)
    · exact hzU.2 (hnorm hN₁ ⟨hcap₁ ▸ ⟨h, (hR hz).2⟩, hzU.1⟩)
    · exact hzU.2 (hnorm hN₂ ⟨hcap₂ ▸ ⟨(hR hz).1, h⟩, hzU.1⟩)
  have hcl : ∀ e x y, X.G.IsLink e x y → φ x ∈ closure (ψ e) := by
    intro e x y h
    have hl := (hb.isLink e h.edge_mem x h.left_mem y h.right_mem).mp h
    have : φ x ∈ closure (ψ e) ∩ Γz.V := by rw [hl.2.2.2]; exact mem_insert _ _
    exact this.1
  -- the components
  let comp : cap.Z → Set cap.Z := fun z => connectedComponentIn W z
  let pt : β → cap.Z := fun e => Classical.epsilon (· ∈ ψ e)
  have hpt : ∀ e ∈ E(X.G), pt e ∈ ψ e := fun e he => Classical.epsilon_spec (hψE e he).1
  have hψK : ∀ e ∈ E(X.G), ψ e ⊆ W → ψ e ⊆ comp (pt e) := fun e he hW' =>
    (hψE e he).2.2.1.isConnected.isPreconnected.subset_connectedComponentIn (hpt e he) hW'
  set Vw := {x | x ∈ V(X.G) ∧ φ x ∈ W} with hVw
  set Ew := {e | e ∈ E(X.G) ∧ ψ e ⊆ W} with hEw
  have hVwfin : Vw.Finite := X.finite_G.1.subset fun x hx => hx.1
  have hEwfin : Ew.Finite := X.finite_G.2.subset fun e he => he.1
  set Ks : Set (Set cap.Z) := (fun x => comp (φ x)) '' Vw ∪ (fun e => comp (pt e)) '' Ew
    with hKsdef
  have hKsfin : Ks.Finite := (hVwfin.image _).union (hEwfin.image _)
  have hKs : ∀ K ∈ Ks, ∃ z ∈ W, K = comp z := by
    rintro K (⟨x, hx, rfl⟩ | ⟨e, he, rfl⟩)
    exacts [⟨φ x, hx.2, rfl⟩, ⟨pt e, he.2 (hpt e he.1), rfl⟩]
  -- the pieces
  let att : Set cap.Z → Set α := fun K => {c | c ∈ C ∧ φ c ∈ closure K}
  let Vp : Set cap.Z → Set α := fun K => {x | x ∈ V(X.G) ∧ φ x ∈ K} ∪ att K
  let Ep : Set cap.Z → Set β := fun K => {e | e ∈ E(X.G) ∧ ψ e ⊆ K}
  let Q : Set cap.Z → Graph α β := fun K => subOf X.G (Vp K ∪ J) (Ep K)
  set s : Finset (Set cap.Z) := insert ∅ hKsfin.toFinset with hs
  have hmem_s : ∀ K ∈ s, K = ∅ ∨ ∃ z ∈ W, K = comp z := by
    intro K hK
    rcases Finset.mem_insert.mp hK with rfl | hK
    · exact .inl rfl
    · exact .inr (hKs K (hKsfin.mem_toFinset.mp hK))
  have hKW : ∀ K ∈ s, K ⊆ W := by
    intro K hK
    rcases hmem_s K hK with rfl | ⟨z, -, rfl⟩
    exacts [empty_subset _, connectedComponentIn_subset _ _]
  have hKpre : ∀ K ∈ s, IsPreconnected K := by
    intro K hK
    rcases hmem_s K hK with rfl | ⟨z, -, rfl⟩
    exacts [isPreconnected_empty, isPreconnected_connectedComponentIn]
  have hVpR : ∀ K ∈ s, Vp K ⊆ fr.vertsIn (cylinderBetween H₁ H₂) := by
    rintro K hK x (⟨hx, hxK⟩ | ⟨hxC, -⟩)
    · exact (hof_W x hx (hKW K hK hxK)).1
    · exact (hmemR x (hCV hxC)).mpr (hCR x hxC)
  have hends : ∀ K ∈ s, ∀ e ∈ Ep K, ∀ x y, X.G.IsLink e x y → x ∈ Vp K := by
    intro K hK e he x y hxy
    have hx := hcl e x y hxy
    have hxK : φ x ∈ closure K := closure_mono he.2 hx
    by_cases hxC : x ∈ C
    · exact .inr ⟨hxC, hxK⟩
    · rcases hmem_s K hK with rfl | ⟨z, hz, rfl⟩
      · exact absurd ((hψE e he.1).1.mono he.2) not_nonempty_empty
      have hxR : φ x ∈ E₁ ∩ E₂ :=
        closure_minimal ((he.2.trans (hKW _ hK)).trans hWE) hRcl hx
      exact .inl ⟨hxy.left_mem, mem_connectedComponentIn_of_mem_closure hz
        (hW_of x hxy.left_mem hxR hxC) hxK⟩
  -- each piece is a tubular graft of large printed width
  have hpiece : ∀ K ∈ s, ∀ h hf, Graft.mk (Q K) J h hf ∈ printedTubularClass t u := by
    intro K hK h hf
    have hattC : att K ⊆ C := fun c hc => hc.1
    have hattV : att K ⊆ V(X.G) := hattC.trans hCV
    have hatt2 : (att K).ncard ≤ 2 := by
      by_contra hlt
      obtain ⟨a, b, c, ha, hb', hc, hab, hac, hbc⟩ :=
        (two_lt_ncard_iff (X.finite_G.1.subset hattV)).mp (by omega)
      have hbd : ∀ x ∈ att K, φ x ∈ discBd D₁ ∧ φ x ∈ discBd D₂ := by
        intro x hx
        have h1 := (hmemC x (hattV hx)).mp hx.1
        have h2 := (hmemC₂ x (hattV hx)).mp hx.1
        rw [hbD₁, ← hcap₁, hbD₂, ← hcap₂]
        exact ⟨h1, h2⟩
      have hinj : ∀ x ∈ att K, ∀ y ∈ att K, x ≠ y → φ x ≠ φ y := fun x hx y hy hxy hφ' =>
        hxy (hb.bijV.injOn (hattV hx) (hattV hy) hφ')
      refine false_of_three_attachments cap.isClosedSurface cap.isSphere hD₁ hD₂ ?_ ?_
        (hKpre K hK) ?_ (hbd a ha).1 (hbd a ha).2 (hbd b hb').1 (hbd b hb').2 (hbd c hc).1
        (hbd c hc).2 (hinj a ha b hb' hab) (hinj a ha c hc hac) (hinj b hb' c hc hbc)
        ha.2 hb'.2 hc.2
      · rw [disjoint_left]
        rintro z ⟨hz1, hz2⟩ hz3
        exact hz2 (hbD₁ ▸ hcap₁ ▸ ⟨hz1, hD₂E₂ hz3⟩)
      · rw [disjoint_left]
        rintro z hz1 ⟨hz3, hz4⟩
        exact hz4 (hbD₂ ▸ hcap₂ ▸ ⟨hle hz1, hz3⟩)
      · rw [disjoint_left]
        intro z hz
        exact (hKW K hK hz).2
    have hVpV : Vp K ⊆ V(X.G) := union_subset (fun x hx => hx.1) hattV
    have hJT : (J \ Vp K) ∪ att K = J := by
      apply Subset.antisymm (union_subset sdiff_subset (hattC.trans hCJ))
      intro x hxJ
      by_cases hx : x ∈ Vp K
      · rcases hx with ⟨hxV, hxK⟩ | hxa
        · exfalso
          obtain ⟨hxR, hxC⟩ := hof_W x hxV (hKW K hK hxK)
          exact hxC (hJin ⟨hxJ, hxR⟩)
        · exact .inr hxa
      · exact .inl ⟨hxJ, hx⟩
    obtain ⟨htub, hwid⟩ := le_tubularPrintedWidth_of_piece cap.isClosedSurface cap.isSphere hb
      hE₂ hVpV (fun e he => he.1) (hends K hK) subset_union_right hatt2
      (by
        rintro x (⟨hx, hxK⟩ | ⟨hxC, -⟩)
        · exact (hWE (hKW K hK hxK)).2
        · exact ((hmemC x (hCV hxC)).mp hxC).2)
      (fun e he => closure_minimal (he.2.trans ((hKW K hK).trans (hWE.trans inter_subset_right)))
        hE₂.isCompact.isClosed)
      (by
        rintro x (⟨hx, hxK⟩ | hxa) hxb
        · exfalso
          rw [hbE₂, ← hcap₁] at hxb
          exact (hKW K hK hxK).2 (.inl hxb.1)
        · exact hxa)
      (by
        intro x hx
        rw [hbE₂, ← hcap₁]
        exact (hmemC x (hattV hx)).mp hx.1)
      (by
        intro e he
        rw [disjoint_left]
        intro z hz hzb
        rw [hbE₂, ← hcap₁] at hzb
        exact (hKW K hK (he.2 hz)).2 (.inl hzb.1))
      (sdiff_subset.trans hJV) disjoint_sdiff_left (Graft.mk (Q K) J h hf)
      (by change subOf X.G (Vp K ∪ J) (Ep K) = _; rw [union_sdiff_self]) hJT.symm
    refine ⟨htub, ?_, ?_⟩
    · change ((J.ncard + 1 : ℕ) : ℕ∞) ≤ _ at hwid
      exact le_trans (by exact_mod_cast ht) hwid
    · exact hu
  -- the fan
  have hendsR : ∀ e ∈ fr.edgesIn (cylinderBetween H₁ H₂), ∀ x y, X.G.IsLink e x y →
      x ∈ fr.vertsIn (cylinderBetween H₁ H₂) ∪ J := by
    intro e he x y hxy
    have hψR := (hmemE e (fr.edgesIn_subset_E _ he)).mp he
    exact .inl ((hmemR x hxy.left_mem).mpr (closure_minimal hψR hRcl (hcl e x y hxy)))
  have hRV : fr.vertsIn (cylinderBetween H₁ H₂) ∪ J ⊆ V(X.G) :=
    union_subset (fr.vertsIn_subset_V _) hJV
  have hle' := subOf_le X.G hRV (fr.edgesIn (cylinderBetween H₁ H₂))
  let Xp : Graft α β := ⟨subOf X.G (fr.vertsIn (cylinderBetween H₁ H₂) ∪ J)
    (fr.edgesIn (cylinderBetween H₁ H₂)), J, subset_union_right,
    ⟨X.finite_G.1.subset hle'.vertexSet_mono, X.finite_G.2.subset hle'.edgeSet_mono⟩⟩
  have hEQ : ∀ K ∈ s, E(Q K) = Ep K := fun K hK =>
    subOf_edgeSet_of_ends X.G (fun e he => he.1) fun e he x y hxy =>
      .inl (hends K hK e he x y hxy)
  have hsame : ∀ K ∈ s, ∀ K' ∈ s, ∀ z ∈ K, z ∈ K' → K = K' := by
    intro K hK K' hK' z hz hz'
    rcases hmem_s K hK with rfl | ⟨a, -, rfl⟩
    · exact absurd hz (notMem_empty z)
    rcases hmem_s K' hK' with rfl | ⟨b, -, rfl⟩
    · exact absurd hz' (notMem_empty z)
    change connectedComponentIn W a = connectedComponentIn W b
    rw [connectedComponentIn_eq hz, connectedComponentIn_eq hz']
  obtain ⟨D, -, hDY⟩ := exists_fan_decomposition (𝒜 := printedTubularClass t u) Q J s
    ⟨∅, Finset.mem_insert_self _ _⟩ Xp
    (fun K hK => subOf_mono X.G (union_subset_union_left J (hVpR K hK))
      fun e he => (hmemE e he.1).mpr ((he.2.trans (hKW K hK)).trans hWE))
    (fun K _ => subset_union_right)
    (by
      rintro K hK K' hK' hne x ⟨hx | hx, hx' | hx'⟩
      · by_cases hxJ : x ∈ J
        · exact hxJ
        rcases hx with ⟨-, hxK⟩ | ⟨hxC, -⟩
        · rcases hx' with ⟨-, hxK'⟩ | ⟨hxC', -⟩
          · exact absurd (hsame K hK K' hK' _ hxK hxK') hne
          · exact absurd (hCJ hxC') hxJ
        · exact absurd (hCJ hxC) hxJ
      all_goals assumption)
    (by
      intro K hK K' hK' hne
      rw [hEQ K hK, hEQ K' hK', disjoint_left]
      intro e he he'
      obtain ⟨z, hz⟩ := (hψE e he.1).1
      exact hne (hsame K hK K' hK' z (he.2 hz) (he'.2 hz)))
    (by
      apply Subset.antisymm
      · rintro x (hxR | hxJ)
        · by_cases hxJ : x ∈ J
          · exact mem_biUnion (Finset.mem_insert_self ∅ _) (Or.inr hxJ)
          have hxV := fr.vertsIn_subset_V _ hxR
          have hxC : x ∉ C := fun h => hxJ (hCJ h)
          have hxW := hW_of x hxV ((hmemR x hxV).mp hxR) hxC
          refine mem_biUnion (x := comp (φ x)) (Finset.mem_insert_of_mem ?_) ?_
          · exact hKsfin.mem_toFinset.mpr (.inl ⟨x, ⟨hxV, hxW⟩, rfl⟩)
          · exact .inl (.inl ⟨hxV, mem_connectedComponentIn hxW⟩)
        · exact mem_biUnion (Finset.mem_insert_self ∅ _) (Or.inr hxJ)
      · simp only [iUnion_subset_iff]
        intro K hK
        exact union_subset_union_left J (hVpR K hK))
    (by
      change E(subOf X.G _ _) = _
      rw [subOf_edgeSet_of_ends X.G (fr.edgesIn_subset_E _) hendsR]
      apply Subset.antisymm
      · intro e he
        have heE := fr.edgesIn_subset_E _ he
        have hW' := hψW e heE ((hmemE e heE).mp he)
        refine mem_biUnion (x := comp (pt e)) (Finset.mem_insert_of_mem ?_) ?_
        · exact hKsfin.mem_toFinset.mpr (.inr ⟨e, ⟨heE, hW'⟩, rfl⟩)
        · rw [hEQ _ (Finset.mem_insert_of_mem
            (hKsfin.mem_toFinset.mpr (.inr ⟨e, ⟨heE, hW'⟩, rfl⟩)))]
          exact ⟨heE, hψK e heE hW'⟩
      · simp only [iUnion_subset_iff]
        intro K hK e he
        rw [hEQ K hK] at he
        exact (hmemE e he.1).mpr ((he.2.trans (hKW K hK)).trans hWE))
    rfl hpiece
  refine ⟨Xp, rfl, (union_self J).symm, D, hDY 0 (Nat.zero_le _), hDY 1 D.hr,
    hDY _ (Nat.sub_le _ _), hDY _ le_rfl, fun i _ hi => ?_⟩
  rw [hDY i hi.le, hk]

end GraphMinor.GM08
