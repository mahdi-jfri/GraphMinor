module

public import GraphMinor.GM20.Section3
public import GraphMinor.GM20.Section10c

import GraphMinor.GM20.Section9hProved

import GraphMinor.GM20.Section10l

import GraphMinor.GM20.Section8b

/-!
# Graph Minors XX, Section 11

(11.1) is (10.4) done "a little more conservatively": instead of using (7.3) it stops at a fine
rooted location that isolates the tangle. (11.2) combines it with (3.1).
-/

@[expose] public section

namespace GraphMinor.GM20

open Set Topology GraphMinor.Surface GraphMinor.GM17 GraphMinor.GM18 GraphMinor.GM10 Hypergraph
  GraphMinor.GM04

universe u v

variable {α : Type u} {β : Type v}

theorem IsFree.isRobust {Ω : Type*} {P : Patchwork Ω α β} (hfree : IsFree P) : P.IsRobust := by
  intro e he
  refine Patch.IsFree.isRobust ?_ (hfree e he)
  rw [P.Δ_verts e he]
  exact P.G.vertexSet_finite.subset fun v hv ↦ P.G.vertex_mem_of_inc hv

theorem isRootless_of_roots {Ω : Type*} {P : Patchwork Ω α β} (h : P.G.roots = []) :
    IsRootless P := by
  change {v | v ∈ P.G.roots} = ∅
  simp [h]

theorem roots_of_isRootless {Ω : Type*} {P : Patchwork Ω α β} (h : IsRootless P) :
    P.G.roots = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun x hx ↦ ?_
  have h₁ : x ∈ P.G.rootSet := hx
  rw [show P.G.rootSet = ∅ from h] at h₁
  exact h₁

/-- A tangle that truncates to one controlling a minor controls the minor, if the truncation keeps
all separations of order `< |V(H)|`. -/
theorem controls_of_truncation {α' β' : Type*} {G : Hypergraph α β} {H : Hypergraph α' β'}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {θ : ℕ}
    (h : ControlsMinor G (truncation 𝒯 θ) H) (hθ : H.vertexSet.ncard ≤ θ) :
    ControlsMinor G 𝒯 H := by
  obtain ⟨hg, av, ae', ae, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨hg, av, ae', ae, h₁, h₂, h₃, h₄, h₅, h₆, fun A B hAB hord ↦ ?_⟩
  exact h₇ ⟨hAB, hord.trans_le hθ⟩ hord

theorem ncard_vertexSet_completeHypergraph (p : ℕ) :
    (completeHypergraph p).vertexSet.ncard = p := by
  change (univ : Set (Fin p)).ncard = p
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Graph Minors XX, (11.1) (page 356): "For every* $p \ge 0$, *there exist* $\theta > 0$ *and a well-behaved set of patchworks*
$\mathcal{F}$ *with the following property. Let* $P = (G, \mu, \Delta)$ *be a rootless free
patchwork, and let* $\mathcal{T}$ *be a tangle in* $G$ *of order* $\ge \theta$, *controlling
no* $K_p$*-minor of* $sk(G^-)$. *Then there is a fine rooted location* $\mathcal{L}$ *in*
$G$ *such that* * $(P, \mathcal{L})$ *has a heart in* $\mathcal{F}$, *and* * $\mathcal{L}$
$\theta$*-isolates* $\mathcal{T}$ *for every edge-based tie-breaker of* $G$."

The location of the proof depends on the tie-breaker, so here `ℒ` is chosen after `λ`. This is the
form that the proof gives and that (11.2) uses. -/
theorem theorem_11_1_proof [Infinite β]
     (p : ℕ) :
    ∃ (θ : ℕ) (𝓕 : Set (UnlabeledPatchwork α β)), 0 < θ ∧ WellBehaved 𝓕 ∧
      ∀ P : UnlabeledPatchwork α β, IsFree P → P.G.roots = [] →
      ∀ (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle P.G.toHypergraph θ' 𝒯 →
        θ ≤ θ' → ¬ ControlsMinor P.G.toHypergraph 𝒯 (completeHypergraph p) →
        ∀ lam : Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ, IsEdgeBased P.G.toHypergraph lam →
        ∃ ℒ : Set (RootedHypergraph α β), IsFine P.G ℒ ∧ IsRootedLocation P.G ℒ ∧
          (∃ Q ∈ 𝓕, HasPatchworkHeart P ℒ Q) ∧
          Isolates P.G.toHypergraph lam θ 𝒯 (rootedLocationToLocation P.G ℒ) := by
  obtain ⟨θ₀, 𝒮, hθ₀, hfin, h⟩ := GraphMinor.GM20.theorem_10_3_proof.{u, v} (completeHypergraph p) (isGraph_completeHypergraph p)
  obtain ⟨θ₁, hθ₁, hθ₀₁, hp⟩ : ∃ θ₁, 1 ≤ θ₁ ∧ θ₀ ≤ θ₁ ∧ p ≤ θ₁ :=
    ⟨max θ₀ p, le_max_of_le_left hθ₀, le_max_left _ _, le_max_right _ _⟩
  have h𝓕₁ : WellBehaved (⋃ X ∈ 𝒮, {P : UnlabeledPatchwork α β | IsHulled X P}) :=
    wellBehaved_biUnion hfin fun X _ ↦ theorem_9_1_proof X
  obtain ⟨𝓕₂, h𝓕₂, H₂⟩ := theorem_7_2_proof h𝓕₁ θ₁
  obtain ⟨𝓕₃, h𝓕₃, H₃⟩ := theorem_5_6_proof.{u, v, 0} h𝓕₂ (θ := θ₁ + 1) (Nat.succ_pos _)
  refine ⟨(θ₁ + 1) ^ 2, 𝓕₃, by positivity, h𝓕₃, ?_⟩
  rintro P hfree hroot θ' 𝒯 h𝒯 hθ' hnc lam ⟨f, v, hdef⟩
  have hle₁ : θ₁ ≤ θ' := by nlinarith
  have h𝒯₁ := h𝒯.truncation hθ₁ hle₁
  obtain ⟨W, hWV, hWθ, ℒ₁, hfine, ⟨X, hX, hs⟩, hlink⟩ := h P hfree hroot θ₁ _ h𝒯₁ hθ₀₁ fun hc ↦
    hnc (controls_of_truncation hc (by rw [ncard_vertexSet_completeHypergraph]; exact hp))
  have hWlt : W.ncard < θ₁ := hWθ.trans_le hθ₀₁
  obtain ⟨Q, hQ, hul⟩ := theorem_10_2_proof (isFree_slash hfree W) (by
    change marchSlash P.G.roots W = []
    rw [hroot]
    rfl) hs
  obtain ⟨ℒ₂, hfine₂, hloc₂, hWA, hslash, hh⟩ := H₂ P hfree θ₁ _ h𝒯₁ le_rfl W hWV hWlt ℒ₁ hfine
    ⟨Q, mem_biUnion hX hul, hQ⟩
  have hlink₂ : IsLinkedTo (P.G.slash W) (quotientTangle P.G.toHypergraph (truncation 𝒯 θ₁) W)
      (locationSlash ℒ₂ W) := by
    rw [hslash]
    exact hlink
  obtain ⟨hord, hlink'⟩ := linked_truncation h𝒯₁ hloc₂ hWA hlink₂
  have hiso := theorem_6_2_proof h𝒯 hdef hloc₂ (θ := θ₁ + 1) (fun A hA ↦ (hord A hA).trans
    (Nat.lt_succ_self _)) hWA hlink'
  have hsub : Sum.inl '' W ∪ {Sum.inr f} ⊆ zSet P.G.toHypergraph := by
    rintro x (⟨y, hy, rfl⟩ | rfl)
    · exact Or.inl ⟨y, hWV hy, rfl⟩
    · exact Or.inr ⟨f, hdef.1, rfl⟩
  have hcard : (Sum.inl '' W ∪ {Sum.inr f} : Set (α ⊕ β)).ncard ≤ θ₁ + 1 := by
    have hfw : W.Finite := P.G.vertexSet_finite.subset hWV
    have h₁ := Set.ncard_union_le (Sum.inl '' W : Set (α ⊕ β)) {Sum.inr f}
    have h₂ := Set.ncard_image_le (f := (Sum.inl : α → α ⊕ β)) hfw
    rw [Set.ncard_singleton] at h₁
    omega
  obtain ⟨ℒ₃, hf₃, hl₃, his, hq⟩ := H₃ P _ lam 𝒯 θ' _ ℒ₂ (isTieBreaker_of_isDefinedBy hdef) h𝒯 hθ'
    hsub hcard (isRootless_of_roots hroot) (IsFree.isRobust hfree).isRemovable hfine₂ hiso hh
  exact ⟨ℒ₃, hf₃, hl₃, hq, his⟩

/-- A location that `θ`-isolates a tangle also `θ₂`-isolates it, for `θ ≤ θ₂`. -/
theorem _root_.GraphMinor.GM18.Isolates.mono {Λ : Type*} [LE Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} {θ θ₂ : ℕ}
    {𝒯 ℒ : Set (Hypergraph α β × Hypergraph α β)} (h : Isolates G lam θ 𝒯 ℒ) (hθ : θ ≤ θ₂) :
    Isolates G lam θ₂ 𝒯 ℒ where
  isLocation := h.isLocation
  subset := h.subset
  locationOrder_lt := h.locationOrder_lt.trans_le hθ
  order_lt _ _ hCD := (h.order_lt hCD).trans_le hθ
  distinction_le _ _ hCD _ _ h𝒯 hθ' := h.distinction_le hCD h𝒯 (hθ.trans hθ')

/-- Graph Minors XX, (11.2) (pages 356–357): "Let* $\Omega$ *be a well-quasi-order, let* $\mathcal{F}$ *be a well-behaved set of partial*
$\Omega$*-patchworks, and let* $\theta \ge 1$ *and* $p \ge 0$. *Let* $P_i = (G_i, \mu_i,
\Delta_i, \phi_i)$ $(i = 1, 2, \dots)$ *be a countable sequence of free rootless*
$\Omega$*-patchworks. For each* $i \ge 1$, *let* $\lambda_i$ *be an edge-based tie-breaker
in* $G_i$. ... *Suppose that for each $i \ge 1$ and each tangle $\mathcal{T}$ in $G_i$ of order
$\ge \theta$ which controls a $K_p$-minor of $sk(G_i^-)$, there is a rooted location
$\mathcal{L}$ in $G_i$ which $\theta$-isolates $\mathcal{T}$ such that $(P_i, \mathcal{L})$
has a heart in $\mathcal{F}$. Then there exist $j > i \ge 1$ such that $P_i$ is simulated in
$P_j$." -/
theorem theorem_11_2_proof [Infinite β]
    {Ω : Type (max u v)} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {𝓕 : Set (PartialPatchwork Ω α β)} (h𝓕 : GM18.WellBehaved 𝓕) {θ : ℕ} (hθ : 1 ≤ θ) (p : ℕ)
    (P : ℕ → GM04.Patchwork Ω α β) (hfree : ∀ i, IsFree (P i)) (hroot : ∀ i, IsRootless (P i))
    (lam : ∀ _ : ℕ, Hypergraph α β × Hypergraph α β → ℝ ×ₗ ℝ ×ₗ ℝ)
    (hlam : ∀ i, IsEdgeBased (P i).G.toHypergraph (lam i))
    (h : ∀ i (θ' : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (P i).G.toHypergraph θ' 𝒯 → θ ≤ θ' →
      ControlsMinor (P i).G.toHypergraph 𝒯 (completeHypergraph p) →
      ∃ ℒ : Set (RootedHypergraph α β), IsOmegaPlace (PartialPatchwork.ofPatchwork (P i)) ℒ ∧
        (∃ Q ∈ 𝓕, HasPlaceHeart (PartialPatchwork.ofPatchwork (P i)) ℒ Q) ∧
        GM18.Isolates (P i).G.toHypergraph (lam i) θ 𝒯 (rootedLocationToLocation (P i).G ℒ)) :
    ∃ i j, i < j ∧ GM04.Simulated (P i) (P j) := by
  classical
  obtain ⟨θ₁, 𝓕₁, hθ₁, h𝓕₁, H₁⟩ := theorem_11_1_proof (α := α) (β := β) p
  let 𝓕₃ : Set (PartialPatchwork Ω α β) := {R | IsRootless R ∧ (R ∈ 𝓕 ∨
    ((∀ e ∈ R.G.edgeSet, R.φ e = ⊥) ∧ ∃ Q ∈ 𝓕₁, IsCompletionOf Q R))}
  have hwb : GM18.WellBehaved 𝓕₃ := by
    intro Ω' _ ι hΩ' Q hQ
    obtain ⟨g, hg, hor⟩ := exists_strictMono_of_or (fun n ↦ ∃ R ∈ 𝓕, IsCompletion ι R (Q n))
      (fun n ↦ ∃ Q₀ ∈ 𝓕₁, IsCompletionOf Q₀ (Q n)) fun n ↦ by
        obtain ⟨R, ⟨-, h₁ | ⟨-, Q₀, hQ₀, hc⟩⟩, hR⟩ := hQ n
        · exact Or.inl ⟨R, h₁, hR⟩
        · refine Or.inr ⟨Q₀, hQ₀, hR.G_eq.trans hc.G_eq, hR.dom_eq.trans hc.dom_eq,
            fun e he ↦ ?_, fun e he ↦ ?_⟩
          · have he' : e ∈ R.dom := hc.dom_eq ▸ he
            exact (hR.μ_eq he').trans (hc.μ_eq he)
          · have he' : e ∈ R.G.edgeSet := by
              rw [hc.G_eq]
              exact he
            exact (hR.Δ_eq he').trans (hc.Δ_eq he)
    rcases hor with hor | hor
    · obtain ⟨i, j, hij, hs⟩ := h𝓕 Ω' ι hΩ' (fun n ↦ Q (g n)) hor
      exact ⟨g i, g j, hg hij, hs⟩
    · obtain ⟨i, j, hij, hs⟩ := h𝓕₁ Ω' hΩ' (fun n ↦ Q (g n)) hor
      exact ⟨g i, g j, hg hij, hs⟩
  refine theorem_3_1_proof hΩ hwb (fun R hR ↦ hR.1) (θ := max θ θ₁) (le_max_of_le_left hθ) P
    (fun i ↦ ⟨hroot i, IsFree.isRobust (hfree i)⟩) (fun _ ↦ ℝ ×ₗ ℝ ×ₗ ℝ) lam
    (fun i ↦ by obtain ⟨f, v, hd⟩ := hlam i; exact isTieBreaker_of_isDefinedBy hd) ?_
  intro i θ' 𝒯 h𝒯 hθ'
  have hle₁ : θ ≤ θ' := (le_max_left _ _).trans hθ'
  have hle₂ : θ₁ ≤ θ' := (le_max_right _ _).trans hθ'
  by_cases hc : ControlsMinor (P i).G.toHypergraph 𝒯 (completeHypergraph p)
  · obtain ⟨ℒ, ho, ⟨Q, hQ, hQh⟩, hi⟩ := h i θ' 𝒯 h𝒯 hle₁ hc
    obtain ⟨e, he⟩ := hQh
    refine ⟨ℒ, ho, ⟨Q, ⟨?_, Or.inl hQ⟩, e, he⟩, hi.mono (le_max_left _ _)⟩
    change {v | v ∈ Q.G.roots} = ∅
    rw [he.roots_eq]
    exact hroot i
  · have hfree' : IsFree ((P i).relabel fun _ ↦ ()) := fun e he ↦ hfree i e he
    obtain ⟨ℒ, hfine, hloc, ⟨Q, hQ, e, hQe⟩, hi⟩ := H₁ ((P i).relabel fun _ ↦ ()) hfree'
      (roots_of_isRootless (hroot i)) θ' 𝒯 h𝒯 hle₂ hc (lam i) (hlam i)
    refine ⟨ℒ, ⟨fun e _ ↦ WithBot.coe_ne_bot, hloc⟩, ⟨Q.relabel fun _ ↦ ⊥, ⟨?_, Or.inr ⟨fun _ _ ↦ rfl,
      Q, hQ, isCompletionOf_relabel _ _⟩⟩, e, placeHeart_of_patchworkHeart hfine hQe⟩,
      hi.mono (le_max_right _ _)⟩
    change {v | v ∈ Q.G.roots} = ∅
    rw [hQe.roots_eq]
    exact hroot i

end GraphMinor.GM20
