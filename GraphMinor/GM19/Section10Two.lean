module

public import GraphMinor.GM19.Defs3
import GraphMinor.GM19.FragmentForm
import GraphMinor.GM19.Section10f

/-!
# Graph Minors XIX, (10.2)

This file formalizes **Graph Minors XIX, (10.2)** (pages 354–355): for a colour scheme $\chi$
satisfying $\mathbf{S}_1$, a fixed circuit $F$ in $\hat{\Sigma}_\chi$, and a march $\pi$, there is a
well-behaved set $\mathscr{C}(F, \pi)$ of $\chi$-places such that for every
$(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ for which $F \subseteq \Gamma^*$ is a
representativeness flaw with $U(F) \cap V(\Gamma) = \bar{\pi}$ and
$\operatorname{dist}(\Gamma) > \frac{1}{4}|E(F)| + 1$, the single-arm rooted location
$\mathscr{L} = \{(\Gamma \cap \Sigma_1, \pi)\}$ has $\operatorname{ord}(\mathscr{L}^-) =
\frac{1}{2}|E(F)|$, $(\frac{1}{2}|E(F)| + 1)$-isolates $\mathscr{T}$, and gives a place in
$\mathscr{C}(F, \pi)$.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

/-- If two tangle data share the same circuit `F` and the same intersection `U(F) ∩ V(Γ) = π̄`, then
the feature `K` of `F` in `Σ` for the first datum is also a circuit part with two vertices for the
second datum. -/
private theorem isCircuitPart_of_same_march {D₀ D : TangleDatum cap χ} {F : Drawing Shat}
    {K : Drawing S} {π : List S}
    (hK₀ : IsCircuitPart cap χ.Φ D₀.P.Γ F K)
    (htwo₀ : ∃ a ∈ K.U ∩ D₀.P.Γ.V, ∃ b ∈ K.U ∩ D₀.P.Γ.V, a ≠ b)
    (hUFV₀ : F.U ∩ cap.emb '' D₀.P.Γ.V = cap.emb '' {v | v ∈ π})
    (hFsub : F.IsSubdrawing D.rad.G)
    (hUFV : F.U ∩ cap.emb '' D.P.Γ.V = cap.emb '' {v | v ∈ π}) :
    IsCircuitPart cap χ.Φ D.P.Γ F K ∧ ∃ a ∈ K.U ∩ D.P.Γ.V, ∃ b ∈ K.U ∩ D.P.Γ.V, a ≠ b := by
  have hsameV : ∀ {x : S}, x ∈ K.U → (x ∈ D.P.Γ.V ↔ x ∈ D₀.P.Γ.V) := by
    intro x hxK
    have hxF : cap.emb x ∈ F.U := hK₀.form.image_subset (mem_image_of_mem _ hxK)
    have h₁ : x ∈ D.P.Γ.V ↔ cap.emb x ∈ F.U ∩ cap.emb '' D.P.Γ.V :=
      ⟨fun h ↦ ⟨hxF, mem_image_of_mem _ h⟩,
       fun ⟨_, y, hy, hyx⟩ ↦ cap.isEmbedding.injective hyx ▸ hy⟩
    have h₂ : x ∈ D₀.P.Γ.V ↔ cap.emb x ∈ F.U ∩ cap.emb '' D₀.P.Γ.V :=
      ⟨fun h ↦ ⟨hxF, mem_image_of_mem _ h⟩,
       fun ⟨_, y, hy, hyx⟩ ↦ cap.isEmbedding.injective hyx ▸ hy⟩
    rw [h₁, h₂, hUFV, hUFV₀]
  have hinter : D.P.Γ.U ∩ K.U ⊆ D.P.Γ.V ∩ K.V := by
    rintro x ⟨hxU, hxK⟩
    have hxF : cap.emb x ∈ F.U := hK₀.form.image_subset (mem_image_of_mem _ hxK)
    have hxhatV : cap.emb x ∈ D.P.Γ.hatV cap :=
      D.rad.isPreRadial.1 ▸ ⟨mem_image_of_mem _ hxU, hFsub.U_subset hxF⟩
    obtain ⟨y, hy, hyx⟩ := hxhatV
    have hxV : x ∈ D.P.Γ.V := cap.isEmbedding.injective hyx ▸ hy
    have hxV₀ : x ∈ D₀.P.Γ.V := (hsameV hxK).mp hxV
    exact ⟨hxV, (hK₀.inter ⟨D₀.P.Γ.V_subset hxV₀, hxK⟩).2⟩
  refine ⟨⟨hK₀.feature, hinter, hK₀.lines, hK₀.V_le, hK₀.E_le, hK₀.form⟩, ?_⟩
  obtain ⟨a, ⟨haK, haV⟩, b, ⟨hbK, hbV⟩, hab⟩ := htwo₀
  exact ⟨a, ⟨haK, (hsameV haK).mpr haV⟩, b, ⟨hbK, (hsameV hbK).mpr hbV⟩, hab⟩

/-- **Graph Minors XIX, (10.2)** (page 354):
"**10.2.** *Let $\chi$ satisfy $\mathbf{S}_1$, let $F$ be a circuit in $\hat{\Sigma}_\chi$, with
vertex set $\{v_1, \dots, v_{2n}\}$, numbered in order in $F$, and let $\pi$ be the march
$v_2, v_4, \dots, v_{2n}$. Then there is a well-behaved set $\mathscr{C}(F, \pi)$ of $\chi$-places
with the following property. Let $(\Gamma, \phi, \lambda, \mathscr{T}) \in \mathscr{D}$ satisfy*
• *$F \subseteq \Gamma^*$, and $U(F) \cap V(\Gamma) = \bar{\pi}$,*
• *$F$ is a representativeness flaw for $(\Gamma, \phi, \lambda, \mathscr{T})$, and*
• *$dist(\Gamma) > \frac{1}{4}|(E(F)| + 1$.*

*Then there is a rooted location $\mathscr{L}$ with $ord(\mathscr{L}^-) = \frac{1}{2}|E(F)|$, which
$(\frac{1}{2}|E(F)| + 1)$-isolates $\mathscr{T}$ and for which
$(\Gamma, \phi, \mathscr{L}) \in \mathscr{C}(F, \pi)$.*" -/
theorem theorem_10_2_proof [Nonempty β] (cap : IsCappedSurface S Shat) (χ : ColourScheme S β)
    (hd : χ.IsDisjoint) (𝒮 : Set (ColouredPainting χ)) (hS1 : ConditionS1.{0, w} Shat)
    (F : Drawing Shat) (hFc : F.IsCircuit) (π : List S) (hπ : π.Nodup) :
    ∃ 𝒞 : Set (Place χ), IsWellBehavedPlaces 𝒞 ∧
      ∀ D : TangleDatum cap χ, D.P ∈ 𝒮 →
        F.IsSubdrawing D.rad.G →
        F.U ∩ cap.emb '' D.P.Γ.V = cap.emb '' {v | v ∈ π} →
        D.IsRepFlaw F →
        ((F.E.ncard + 4 : ℕ) : ℕ∞) < Painting.dist D.rad * 4 →
        ∃ L : RootedLocation D.P.Γ,
          L.ord = F.E.ncard / 2 ∧
          L.Isolates D.tb (F.E.ncard / 2 + 1) D.ord D.𝒯 ∧
          (⟨hd, D.P, L⟩ : Place χ) ∈ 𝒞 := by
  classical
  have hS := χ.isSurface
  have : ConnectedSpace S := χ.connected
  have : ConnectedSpace Shat := cap.connected
  have hT := cap.isClosedSurface
  let a₀ : β := Classical.arbitrary β
  let InD1 (D : TangleDatum cap χ) : Prop :=
    D.P ∈ 𝒮 ∧ F.IsSubdrawing D.rad.G ∧
    F.U ∩ cap.emb '' D.P.Γ.V = cap.emb '' {v | v ∈ π} ∧
    D.IsRepFlaw F ∧ ((F.E.ncard + 4 : ℕ) : ℕ∞) < Painting.dist D.rad * 4
  by_cases hne : ∃ D₀ : TangleDatum cap χ, InD1 D₀
  · obtain ⟨D₀, _, hFsub₀, hUFV₀, hFl₀, hdist₀⟩ := hne
    have : Nonempty S := by
      obtain ⟨e, he⟩ := IsCircuit.E_nonempty hFc
      obtain ⟨v, _, _, _, _⟩ := D₀.rad.edge_ends (hFsub₀.2 he)
      exact ⟨v⟩
    obtain ⟨S₁₀, S₂₀, hs₀, hnd₀, hm₀⟩ := hFl₀.has_non_disc
    obtain ⟨K, hK₀, htwo₀⟩ :=
      TangleDatum.exists_flaw_part hS D₀.P.fits.internally_three_connected hFl₀ hs₀ hnd₀ hm₀ hdist₀
    have hKne : K.V ⊆ ⋃ e ∈ arcComponentsIn (K.U \ K.V), closure e := fun v hv ↦ by
      obtain ⟨e, he, hve⟩ := hK₀.feature.no_isolated_vertices v hv
      exact mem_biUnion he hve.1
    obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hsheet⟩ :=
      exists_cut_of_form hS D₀.P.fits hK₀.form hK₀.inter hK₀.lines hKne
    obtain ⟨B, hB, hmem⟩ := exists_class_cut (χ := χ) (K := K) hY (ψ := ψ) 1
      (fun c ↦ ∀ (Shat₁ : Type) [TopologicalSpace Shat₁], IsCappedSurface c Shat₁ →
        IsSimplerThan Shat₁ Shat)
      (fun _ ↦ True)
      (fun y l h ↦ wellBehaved_S1 hS hK₀.feature hK₀.lines hY hψ hsheet y l 1 a₀ hS1 h)
    refine ⟨B, hB, fun D hD𝒮 hFsub hUFV hFl hdist ↦ ?_⟩
    have h3 := D.P.fits.internally_three_connected
    obtain ⟨S₁, S₂, hs, hnd, hm⟩ := hFl.has_non_disc
    obtain ⟨Δ, hΔ, hbd⟩ := exists_disc_of_lt_rep hFl.is_circuit hFl.lt_two_rep
    have hsides : S₁ = closure Δᶜ ∧ Δ = S₂ := by
      rcases isSidesOf_cases hT hΔ hbd hs with ⟨rfl, -⟩ | ⟨h₁, h₂⟩
      · exact absurd hΔ hnd
      · exact ⟨h₁, h₂.symm⟩
    obtain ⟨rfl, rfl⟩ := hsides
    obtain ⟨hK, htwo⟩ := isCircuitPart_of_same_march hK₀ htwo₀ hUFV₀ hFsub hUFV
    obtain ⟨y, hy, hsph⟩ :=
      discSide S Shat cap K F.U Δ hS hK.form hΔ hbd Y tY t2Y ψ hY hψ
    set Γ := D.P.Γ
    set A₁ := cap.emb ⁻¹' closure Δᶜ
    set A₂ := cap.emb ⁻¹' Δ
    have hsep : Γ.toHypergraph.IsSeparation (Γ.restrict A₁) (Γ.restrict A₂) :=
      D.isTangle.isSeparation hm
    obtain ⟨-, -, S₁', S₂', hs', hlink⟩ :=
      TangleDatum.IsRepFlaw.linked hS h3 hFl hs hnd hm
    have hlink' : GM18.IsLambdaLinkedTo D.tb.lambdaOrder D.𝒯 (Γ.restrict A₁) (Γ.restrict A₂) := by
      rcases isSidesOf_cases hT hΔ hbd hs' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂] at hlink
        refine absurd ?_ (D.isTangle.axiom2 hm hm hlink.1)
        change Γ.restrict A₁ ∪ Γ.restrict A₁ ∪ Γ.restrict A₂ = Γ.toHypergraph
        rw [GM10.union_self, hsep.union_eq]
      · rw [h₁, h₂] at hlink
        exact hlink
    have hπ_set : {v | v ∈ π} = (Γ.restrict A₁ ∩ Γ.restrict A₂).vertexSet := by
      ext v
      have hv_iff : cap.emb v ∈ F.U ∩ cap.emb '' Γ.V ↔ v ∈ (Γ.restrict A₁ ∩ Γ.restrict A₂).vertexSet := by
        constructor
        · rintro ⟨hvF, u, hu, huv⟩
          have hvV : v ∈ Γ.V := cap.isEmbedding.injective huv ▸ hu
          have hvA₁ : v ∈ A₁ := (isSide_out hT hΔ hbd).U_subset_closure hvF
          have hvA₂ : v ∈ A₂ := (hbd ▸ Surface.discBd_subset Δ : F.U ⊆ Δ) hvF
          exact ⟨⟨hvV, hvA₁⟩, ⟨hvV, hvA₂⟩⟩
        · rintro ⟨⟨hvV, hvA₁⟩, ⟨_, hvA₂⟩⟩
          exact ⟨(disc_facts hS h3 D.rad hFl.is_circuit hΔ hbd).2.1 v ⟨⟨hvV, hvA₂⟩, ⟨hvV, hvA₁⟩⟩,
            mem_image_of_mem _ hvV⟩
      rw [← hv_iff, hUFV]
      exact ⟨fun h ↦ mem_image_of_mem _ h,
        fun ⟨u, hu, huv⟩ ↦ cap.isEmbedding.injective huv ▸ hu⟩
    let A : Arm Γ := restrictArm Γ A₁ A₂ hsep π hπ hπ_set
    let L : RootedLocation Γ := oneLocation A
    have hLord : L.ord = A.order := by
      change sSup (Arm.order '' ({A} : Set (Arm Γ))) = _
      simp
    have hFcard : F.E.ncard = 2 * A.order := by
      have hdo := disc_order hS h3 D.rad hFl.is_circuit hΔ hbd
      change F.E.ncard = 2 * Hypergraph.separationOrder (Γ.restrict A₁) (Γ.restrict A₂)
      rw [separationOrder_comm]
      exact hdo
    have hLord_eq : L.ord = F.E.ncard / 2 := by omega
    have hLl : L.IsLambdaLinked D.tb D.𝒯 := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨B, rfl, rfl⟩
        exact hm
      · rintro B rfl
        exact hlink'
    have hle_rep : F.E.ncard ≤ 2 * D.rep := hFl.card_le
    have hlt_ord : D.rep < D.ord := hFl.lt_ord_T
    have hiso : L.Isolates D.tb (F.E.ncard / 2 + 1) D.ord D.𝒯 :=
      theorem_8_8_proof D.tb hS h3 D.isTangle hLl (by omega) (by omega)
    have hfin : (K.V ∩ Γ.V).Finite := K.finite_V.subset inter_subset_left
    let l : List S := hfin.toFinset.toList
    have hrange : range (fun x : connectedComponent y ↦ ψ x.1) = A₂ := by
      have : range (fun x : connectedComponent y ↦ ψ x.1) = ψ '' connectedComponent y := by
        ext z
        simp
      rw [this, hy]
    have hclosed : IsClosed A₂ := hΔ.isClosed.preimage cap.isEmbedding.continuous
    have hcut : IsCutPlace χ K (fun x : connectedComponent y ↦ ψ x.1) l 1 ⟨hd, D.P, L⟩ := by
      refine ⟨hK.inter, fun v ↦ by simp [l, Γ], fun v hv ↦ ?_,
        isAnchored_of_form hK.form hK.inter htwo, ?_, ?_, ?_, ?_⟩
      · rw [hrange]
        have hvK : v ∈ K.V := (hfin.mem_toFinset.mp (Finset.mem_toList.mp hv)).1
        exact (hbd ▸ Surface.discBd_subset Δ : F.U ⊆ Δ)
          (hK.form.image_subset (mem_image_of_mem _ (K.V_subset_U hvK)))
      · change (oneLocation A).M.vertexSet = _
        rw [oneLocation_M_V, hrange]
        ext v
        exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, h⟩⟩
      · change (oneLocation A).M.edgeSet = _
        rw [oneLocation_M_E, hrange]
        ext e
        constructor
        · exact fun h ↦ ⟨h.1, h.2.2.1⟩
        · refine fun h ↦ ⟨h.1, h.1, h.2, ?_⟩
          exact fun x hx ↦ closure_minimal h.2 hclosed hx.1.1
      · rintro B rfl v hv
        have hv' : v ∈ (Γ.restrict A₁ ∩ Γ.restrict A₂).vertexSet := hπ_set.subset hv
        have h₁ : cap.emb v ∈ F.U :=
          (disc_facts hS h3 D.rad hFl.is_circuit hΔ hbd).2.1 v ⟨hv'.2, hv'.1⟩
        have h₂ : v ∈ K.U := hK.form.mem_U h₁
        have h₃ : v ∈ K.V := (hK.inter ⟨Γ.V_subset hv'.1.1, h₂⟩).2
        exact Finset.mem_toList.mpr (hfin.mem_toFinset.mpr ⟨h₃, hv'.1.1⟩)
      · change ({A} : Set (Arm Γ)).ncard ≤ 1
        simp
    refine ⟨L, hLord_eq, hiso, hmem y l ⟨hd, D.P, L⟩ (fun Shat₁ _ cap₁ ↦ ?_) (fun v hv ↦ ?_) hcut trivial⟩
    · exact simpler_of_sphere cap hFl.not_sphere (hsph Shat₁ cap₁)
    · exact (hfin.mem_toFinset.mp (Finset.mem_toList.mp hv)).1
  · refine ⟨∅, fun Ω hΩ seq hseq ↦ absurd (hseq 0) (notMem_empty _),
      fun D h₁ h₂ h₃ h₄ h₅ ↦ absurd ⟨D, h₁, h₂, h₃, h₄, h₅⟩ hne⟩

end GraphMinor.GM19
