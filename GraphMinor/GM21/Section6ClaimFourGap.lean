module

public import GraphMinor.GM21.Section6ClaimFour
public import GraphMinor.GM21.Section6SidePieces
public import GraphMinor.GM21.Section6GapPieces
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6RestrictLink

/-!
# Graph Minors XXI, (6.3), claim (4): the bound for one side

Claim (4) of the proof of (6.3) (page 29 of the preprint) bounds the jumps on each side `Σ_i`
of a separating line `F` by the inductive hypothesis (1): "there is a presentation of $G_i$ in
$\Sigma_i$ of depth $\le q$ and defect $\le r + 1$, using $\Gamma_i$; and $L \cap G_i$ is an
exhaustive vital $(p + 2q)$-linkage". This file proves the bound for one side, in the two cases
that occur.

* `side_jumps_le_of_supports`: every set `F_j* ∩ Σ₁` that is not empty is a support. Then the
  restricted presentation has defect at most `r` (`presentationHasDepthLe_side`).
* `side_jumps_le_of_gap`: a support `F_{j₀}*` holds both ends of `F` and meets `Σ₁` in two arcs
  `K_a ∋ a` and `K_b ∋ b`. Here the paper's sentence fails as written: `μ(K_a)` and `μ(K_b)` may
  share vertices, namely those of `μ(a) ∩ μ(b)`, so (V1) fails (see the correction to the proof of
  (6.3) in `corrections/GM21.md`). We split each such
  vertex, giving its edges in `μ(K_a)` to one copy and its edges in `μ(K_b)` to the other. The data
  before the split satisfy all conditions of a presentation except (V1)
  (`isOverlappingPresentation_side`), and the split graph has a presentation of depth `≤ q` and
  defect `≤ r + 1` (`isPresentation_splitAlong`). By (2.4), applied once for each of the at most
  `q` split vertices, it has an exhaustive vital `(p + 4q)`-linkage (`isVitalPLinkage_splitAlong`).

In both cases the bound used is `λ(p + 4q, q, r + 1)` of the inductive hypothesis. The side that
holds the middle arc of the cut support is bounded by `side_jumps_le_of_mid`. `claim_4` puts the
cases together: either the disc of claim (4) exists, or there are at most
`2λ(p + 4q, q, r + 1)` jumps.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimFour

open Set Topology Function GraphMinor.Surface GraphMinor.GM21.Induction GraphMinor.GM21.Side
  GraphMinor.GM21.Supports GraphMinor.GM21.Split GraphMinor.GM19 Hypergraph

universe u v

/-- A `p`-linkage is a `p'`-linkage for `p ≤ p'`. -/
theorem IsPLinkage.mono {α : Type u} {β : Type v} {G L : Hypergraph α β} {p p' : ℕ}
    (h : IsPLinkage G L p) (hp : p ≤ p') : IsPLinkage G L p' :=
  ⟨h.1, h.2.trans hp⟩

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S] [T2Space S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
  {r' : ℕ} {F_star : Fin r' → Set S} {H : Fin r' → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {L : Hypergraph α β} {qf : Fin r' → ℕ}

omit [T2Space S] in
/-- In a presentation of a graph, the graphs `H_j` and `H_k` share no edge for `j ≠ k`: an edge has
an end, and the end would be a common vertex. -/
theorem disjoint_edgeSet_H (hP : IsPresentation G Γ Γ_sub ιV ιE r' F_star H μ qf)
    (hG : G.IsGraph) {j k : Fin r'} (hjk : j ≠ k) :
    Disjoint (H j).edgeSet (H k).edgeSet := by
  rw [Set.disjoint_left]
  intro e hej hek
  obtain ⟨v, hv⟩ := (hG e ((hP.v1_sub j).edgeSet_subset hej)).1
  have hvj : v ∈ (H j).vertexSet :=
    (H j).vertex_mem_of_inc ((GM10.inc_iff_of_le (hP.v1_sub j) hej).mpr hv)
  have hvk : v ∈ (H k).vertexSet :=
    (H k).vertex_mem_of_inc ((GM10.inc_iff_of_le (hP.v1_sub k) hek).mpr hv)
  exact disjoint_left.mp (hP.v1_disjoint hjk) hvj hvk

variable {S₁ S₂ F : Set S} {a b : S}

/-- **The bound for one side, when every piece is a support** (Graph Minors XXI, proof of (6.3),
claim (4), page 29 of the preprint). If every nonempty `F_j* ∩ Σ₁` is a support, then `Γ ∩ Σ₁` has
at most `λ(p + 4q, q, r + 1)` jumps. -/
theorem side_jumps_le_of_supports {n c p q r lam : ℕ}
    (hlam : BoundBelow.{u, v} n c (p + 4 * q) q (r + 1) lam)
    (hP : IsPresentation G Γ Γ_sub ιV ιE r' F_star H μ qf) (hqf : ∀ j, qf j ≤ q) (hr : r' ≤ r)
    (hG : G.IsGraph) (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (h : IsSideOfLine Γ S₁ S₂ F a b) [ConnectedSpace S₁] {n₁ c₁ : ℕ} (hT₁ : HasType S₁ n₁ c₁)
    (hlt : TypeLt n₁ c₁ n c)
    (hsupp : ∀ j, (F_star j ∩ S₁).Nonempty → IsSupportOfDrawing Γ (F_star j ∩ S₁)) :
    (sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
      (ιV ∘ Subtype.val)).encard ≤ lam := by
  classical
  obtain ⟨σ, hσ, hPσ, hall⟩ := exists_enum (fun j => (F_star j ∩ S₁).Nonempty)
  have hσsup : ∀ i, IsSupportOfDrawing Γ (F_star (σ i) ∩ S₁) := fun i => hsupp _ (hPσ i)
  obtain ⟨hL₁, hLp₁⟩ := isExhaustiveLinkage_side hP h hqf hσsup hall hL hLp
  have hcard : (Finset.univ.filter fun j => (F_star j ∩ S₁).Nonempty).card ≤ r + 1 :=
    (Finset.card_filter_le _ _).trans (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  exact hlam _ h.surface_left n₁ c₁ hT₁ hlt _ _ _ _ _ _ _ _ _ _
    (isGraph_of_le (sideGraph_le hP h.isClosed_left) hG) hcard
    (presentationHasDepthLe_side hP h hqf inferInstance hσ hσsup hall) hL₁
    (IsPLinkage.mono hLp₁ (by omega))

/-- The indices of the pieces of the gap side: the listed supports `castAdd 2 k`, then `K_a` at
`natAdd m 0` and `K_b` at `natAdd m 1`. -/
theorem fin_cases_add_two {m : ℕ} (i : Fin (m + 2)) :
    (∃ k : Fin m, i = Fin.castAdd 2 k) ∨ i = Fin.natAdd m 0 ∨ i = Fin.natAdd m 1 := by
  refine Fin.addCases (fun k => Or.inl ⟨k, rfl⟩) (fun k => Or.inr ?_) i
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The bound for the side where a support is cut in two** (Graph Minors XXI, proof of (6.3),
claim (4), page 29 of the preprint, corrected as in `corrections/GM21.md`). Let
`F_{j₀}* = f([t₀, t₁])` hold both ends of `F`, at
the angles `x < y`, and let `Σ₁` miss the arc of angles `(x, y)` and contain the arc of angles
`(y, x + 2π)`. Then `F_{j₀}* ∩ Σ₁` is the union of `K_a = f([t₀, x])` and `K_b = f([y, t₁])`. Split
the vertices of `μ(a) ∩ μ(b)`, giving their edges in `μ(K_a)` to one copy and the others to the
second copy. The split graph has a presentation in `Σ₁` of depth `≤ q` and defect `≤ r + 1` with
the drawing `Γ ∩ Σ₁`, and an exhaustive vital `(p + 4q)`-linkage, so `Γ ∩ Σ₁` has at most
`λ(p + 4q, q, r + 1)` jumps. -/
theorem side_jumps_le_of_gap (hS : IsSurface S) {n c p q r lam : ℕ}
    (hlam : BoundBelow.{u, v} n c (p + 4 * q) q (r + 1) lam)
    (hP : IsPresentation G Γ Γ_sub ιV ιE r' F_star H μ qf) (hqf : ∀ j, qf j ≤ q) (hr : r' ≤ r)
    (hG : G.IsGraph) (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (h : IsSideOfLine Γ S₁ S₂ F a b) [ConnectedSpace S₁] {n₁ c₁ : ℕ} (hT₁ : HasType S₁ n₁ c₁)
    (hlt : TypeLt n₁ c₁ n c) {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C) (j₀ : Fin r')
    {t₀ t₁ x y : ℝ} (ht₀x : t₀ ≤ x) (hxy : x < y) (hyt₁ : y ≤ t₁)
    (hlt' : t₁ < t₀ + 2 * Real.pi) (ht₀V : cuffPoint f t₀ ∈ Γ.V) (ht₁V : cuffPoint f t₁ ∈ Γ.V)
    (hFj : F_star j₀ = cuffPoint f '' Icc t₀ t₁)
    (hab : ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b})
    (hM : Disjoint (cuffPoint f '' Ioo x y) S₁)
    (hO : cuffPoint f '' Ioo y (x + 2 * Real.pi) ⊆ S₁) :
    (sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
      (ιV ∘ Subtype.val)).encard ≤ lam := by
  classical
  have hpi := Real.pi_pos
  set Ka := cuffPoint f '' Icc t₀ x with hKa_def
  set Kb := cuffPoint f '' Icc y t₁ with hKb_def
  -- The ends of `F` are the points at the angles `x` and `y`.
  have hxab : cuffPoint f x = a ∨ cuffPoint f x = b := by
    have : cuffPoint f x ∈ ({a, b} : Set S) := hab ▸ Or.inl rfl
    exact this
  have hyab : cuffPoint f y = a ∨ cuffPoint f y = b := by
    have : cuffPoint f y ∈ ({a, b} : Set S) := hab ▸ Or.inr rfl
    exact this
  have hxV : cuffPoint f x ∈ Γ.V := by rcases hxab with h' | h' <;> rw [h']
                                       exacts [h.left_mem, h.right_mem]
  have hyV : cuffPoint f y ∈ Γ.V := by rcases hyab with h' | h' <;> rw [h']
                                       exacts [h.left_mem, h.right_mem]
  have hxy_ne : cuffPoint f x ≠ cuffPoint f y := fun h' => by
    have := GM17.cuffPoint_injOn_Ico f x ⟨le_rfl, by linarith⟩ ⟨hxy.le, by linarith⟩ h'
    linarith
  have hsplit : F_star j₀ ∩ S₁ = Ka ∪ Kb := by
    rw [hFj]
    exact Gap.inter_side_eq_of_mid_disjoint h f ht₀x hxy hyt₁ hlt' hab hM hO
  have hKaF : Ka ⊆ F_star j₀ ∩ S₁ := hsplit ▸ subset_union_left
  have hKbF : Kb ⊆ F_star j₀ ∩ S₁ := hsplit ▸ subset_union_right
  have hxKa : cuffPoint f x ∈ Ka := ⟨x, ⟨ht₀x, le_rfl⟩, rfl⟩
  have hyKb : cuffPoint f y ∈ Kb := ⟨y, ⟨le_rfl, hyt₁⟩, rfl⟩
  have hdisjK : Disjoint Ka Kb := Gap.disjoint_pieces f ht₀x hxy hyt₁ hlt'
  -- The other supports do not contain both ends.
  have habF : a ∈ F_star j₀ ∧ b ∈ F_star j₀ := by
    have hx' := (hKaF hxKa).1
    have hy' := (hKbF hyKb).1
    rcases hxab with h₁ | h₁ <;> rcases hyab with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hxy_ne
    · exact ⟨h₁ ▸ hx', h₂ ▸ hy'⟩
    · exact ⟨h₂ ▸ hy', h₁ ▸ hx'⟩
    · exact absurd (h₁.trans h₂.symm) hxy_ne
  have hsupp_j : ∀ j, j ≠ j₀ → (F_star j ∩ S₁).Nonempty →
      IsSupportOfDrawing Γ (F_star j ∩ S₁) := fun j hj hne =>
    isSupport_inter_side h (hP.supports_isSupport j)
      (fun hab' => disjoint_left.mp (hP.supports_disjoint hj) hab'.1 habF.1) hne
  -- The pieces of the side.
  obtain ⟨m, σ, hσ, hPσ, hall⟩ : ∃ m, ∃ σ : Fin m → Fin r', Injective σ ∧
      (∀ k, σ k ≠ j₀ ∧ (F_star (σ k) ∩ S₁).Nonempty) ∧
      ∀ j, (j ≠ j₀ ∧ (F_star j ∩ S₁).Nonempty) → ∃ k, σ k = j :=
    ⟨_, exists_enum (fun j => j ≠ j₀ ∧ (F_star j ∩ S₁).Nonempty)⟩
  let K : Fin (m + 2) → Set S := Fin.append (fun k => F_star (σ k) ∩ S₁) ![Ka, Kb]
  let τ : Fin (m + 2) → Fin r' := Fin.append σ ![j₀, j₀]
  let cc : Fin (m + 2) → Bool := Fin.append (fun _ => false) ![false, true]
  set ia : Fin (m + 2) := Fin.natAdd m 0
  set ib : Fin (m + 2) := Fin.natAdd m 1
  have hKc : ∀ k, K (Fin.castAdd 2 k) = F_star (σ k) ∩ S₁ := fun k => Fin.append_left _ _ k
  have hKa' : K ia = Ka := Fin.append_right _ _ 0
  have hKb' : K ib = Kb := Fin.append_right _ _ 1
  have hτc : ∀ k, τ (Fin.castAdd 2 k) = σ k := fun k => Fin.append_left _ _ k
  have hτa : τ ia = j₀ := Fin.append_right _ _ 0
  have hτb : τ ib = j₀ := Fin.append_right _ _ 1
  have hcc : ∀ k, cc (Fin.castAdd 2 k) = false := fun k => Fin.append_left _ _ k
  have hca : cc ia = false := Fin.append_right _ _ 0
  have hcb : cc ib = true := Fin.append_right _ _ 1
  have hab_ne : ia ≠ ib := by simp [ia, ib, Fin.ext_iff]
  have hca_ne : ∀ k, Fin.castAdd 2 k ≠ ia := fun k h' => by
    simp only [ia, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h'; omega
  have hcb_ne : ∀ k, Fin.castAdd 2 k ≠ ib := fun k h' => by
    simp only [ib, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at h'; omega
  have hσj : ∀ k, σ k ≠ j₀ := fun k => (hPσ k).1
  have hKF : ∀ i, K i ⊆ F_star (τ i) ∩ S₁ := by
    intro i
    rcases fin_cases_add_two i with ⟨k, rfl⟩ | rfl | rfl
    · rw [hKc, hτc]
    · rw [hKa', hτa]; exact hKaF
    · rw [hKb', hτb]; exact hKbF
  have hKsup : ∀ i, IsSupportOfDrawing Γ (K i) := by
    intro i
    rcases fin_cases_add_two i with ⟨k, rfl⟩ | rfl | rfl
    · rw [hKc]; exact hsupp_j _ (hσj k) (hPσ k).2
    · rw [hKa']; exact Gap.isSupport_piece_left hC f ht₀x hxy hyt₁ hlt' ht₀V hxV hS
    · rw [hKb']; exact Gap.isSupport_piece_right hC f ht₀x hxy hyt₁ hlt' ht₁V hyV hS
  -- Pieces from different supports `F_j*` are disjoint.
  have hKdisj_of_τ : ∀ i i', τ i ≠ τ i' → Disjoint (K i) (K i') := fun i i' hτ =>
    (hP.supports_disjoint hτ).mono ((hKF i).trans inter_subset_left)
      ((hKF i').trans inter_subset_left)
  have hτ_eq : ∀ i i', i ≠ i' → τ i = τ i' → (i = ia ∧ i' = ib) ∨ (i = ib ∧ i' = ia) := by
    intro i i' hii' hτ
    rcases fin_cases_add_two i with ⟨k, rfl⟩ | rfl | rfl <;>
      rcases fin_cases_add_two i' with ⟨k', rfl⟩ | rfl | rfl
    · rw [hτc, hτc] at hτ
      exact absurd (congrArg _ (hσ hτ)) hii'
    · rw [hτc, hτa] at hτ; exact absurd hτ (hσj k)
    · rw [hτc, hτb] at hτ; exact absurd hτ (hσj k)
    · rw [hτc, hτa] at hτ; exact absurd hτ.symm (hσj k')
    · exact absurd rfl hii'
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hτc, hτb] at hτ; exact absurd hτ.symm (hσj k')
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hii'
  have hKdisj : Pairwise (fun i i' => Disjoint (K i) (K i')) := by
    intro i i' hii'
    by_cases hτ : τ i = τ i'
    · rcases hτ_eq i i' hii' hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hKa', hKb']; exact hdisjK
      · rw [hKa', hKb']; exact hdisjK.symm
    · exact hKdisj_of_τ i i' hτ
  have hKV : ∀ j, ∀ u ∈ Γ.V ∩ (F_star j ∩ S₁), ∃ i, τ i = j ∧ u ∈ K i := by
    rintro j u ⟨huV, hu⟩
    by_cases hj : j = j₀
    · subst hj
      rw [hsplit] at hu
      rcases hu with hu | hu
      · exact ⟨ia, hτa, hKa' ▸ hu⟩
      · exact ⟨ib, hτb, hKb' ▸ hu⟩
    · obtain ⟨k, rfl⟩ := hall j ⟨hj, u, hu⟩
      exact ⟨Fin.castAdd 2 k, hτc k, (hKc k).symm ▸ hu⟩
  have hKs : ∀ j, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j ∩ S₁ → ∃ i, τ i = j ∧ s ⊆ K i := by
    intro j s hs hsF
    by_cases hj : j = j₀
    · subst hj
      rw [hsplit] at hsF
      rcases Gap.subset_piece_of_isPreconnected (f := f) (ht₀x := ht₀x) (hxy := hxy)
        (hyt₁ := hyt₁) (hlt := hlt') (isConnected_of_mem_drawingSpaces hs).isPreconnected hsF
        with h' | h'
      · exact ⟨ia, hτa, hKa' ▸ h'⟩
      · exact ⟨ib, hτb, hKb' ▸ h'⟩
    · obtain ⟨k, rfl⟩ := hall j ⟨hj, nonempty_of_mem_drawingSpaces hs |>.mono hsF⟩
      exact ⟨Fin.castAdd 2 k, hτc k, (hKc k).symm ▸ hsF⟩
  have hOP := isOverlappingPresentation_side hP h inferInstance hKF hKsup hKdisj hKV hKs
  -- The graphs `μ(K_i)` lie in the graphs `H_{τ i}`.
  have hH₁le : ∀ i, supportGraph G Γ μ (K i) ≤ H (τ i) := fun i =>
    (supportGraph_mono hP (τ i) inter_subset_left (hKF i)).trans (supportGraph_inter_le_H hP (τ i))
  have hE₂H : (supportGraph G Γ μ Kb).edgeSet ⊆ (H j₀).edgeSet := by
    have := (hH₁le ib).edgeSet_subset
    rwa [hKb', hτb] at this
  -- The set `X` of vertices to split: those of both `μ(a)` and `μ(b)`.
  set X := (μ (.vertex (cuffPoint f x))).vertexSet ∩ (μ (.vertex (cuffPoint f y))).vertexSet
    with hX_def
  set E₂ := (supportGraph G Γ μ Kb).edgeSet with hE₂_def
  have hxF : cuffPoint f x ∈ Γ.V ∩ F_star j₀ := ⟨hxV, (hKaF hxKa).1⟩
  have hyF : cuffPoint f y ∈ Γ.V ∩ F_star j₀ := ⟨hyV, (hKbF hyKb).1⟩
  have hμK : ∀ u ∈ Γ.V ∩ F_star j₀, ∀ I : Set S, u ∈ I →
      (μ (.vertex u)).vertexSet ⊆ (supportGraph G Γ μ I).vertexSet := fun u hu I huI v hv =>
    ⟨((hP.μ_vertex_sub j₀ u hu).1.trans (hP.v1_sub j₀)).vertexSet_subset hv,
      Or.inr (mem_biUnion (x := u) ⟨hu.1, huI⟩ hv)⟩
  have hXa : X ⊆ (supportGraph G Γ μ (K ia)).vertexSet := by
    rw [hKa']; exact inter_subset_left.trans (hμK _ hxF _ hxKa)
  have hXb : X ⊆ (supportGraph G Γ μ (K ib)).vertexSet := by
    rw [hKb']; exact inter_subset_right.trans (hμK _ hyF _ hyKb)
  have hXG : X ⊆ (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁).vertexSet :=
    hXa.trans (hOP.v1_sub ia).vertexSet_subset
  -- The hypotheses of `isPresentation_splitAlong`.
  have hcc_false : ∀ i, i ≠ ib → cc i = false := by
    intro i hi
    rcases fin_cases_add_two i with ⟨k, rfl⟩ | rfl | rfl
    · exact hcc k
    · exact hca
    · exact absurd rfl hi
  have hcolor : ∀ i, ∀ e ∈ (supportGraph G Γ μ (K i)).edgeSet, (e ∈ E₂ ↔ cc i = true) := by
    intro i e he
    rcases fin_cases_add_two i with ⟨k, rfl⟩ | rfl | rfl
    · rw [hcc]
      have heH := (hH₁le _).edgeSet_subset he
      rw [hτc] at heH
      exact iff_of_false (fun he₂ => disjoint_left.mp (disjoint_edgeSet_H hP hG (hσj k)) heH
        (hE₂H he₂)) (by simp)
    · rw [hca, hKa'] at *
      exact iff_of_false (disjoint_left.mp (Gap.edgeSet_disjoint_pieces hP j₀ hC f ht₀x hxy hyt₁
        hlt' ht₀V ht₁V hxV hFj) he) (by simp)
    · rw [hcb]
      rw [hKb'] at he
      exact iff_of_true he rfl
  have hΓE : Disjoint (sideSub Γ Γ_sub ιV ιE S₁).edgeSet E₂ :=
    ((hP.v1_inter_E j₀).mono hE₂H (sideSub_le hP h.isClosed_left).edgeSet_subset).symm
  have hΓX : Disjoint (sideSub Γ Γ_sub ιV ιE S₁).vertexSet X := by
    rw [Set.disjoint_left]
    intro v hvΓ hvX
    have hvΓ' := (sideSub_le hP h.isClosed_left).vertexSet_subset hvΓ
    have h₁ : v ∈ ({ιV (cuffPoint f x)} : Set α) :=
      (hP.μ_vertex_sub j₀ _ hxF).2.2.2 ▸ ⟨hvX.1, hvΓ'⟩
    have h₂ : v ∈ ({ιV (cuffPoint f y)} : Set α) :=
      (hP.μ_vertex_sub j₀ _ hyF).2.2.2 ▸ ⟨hvX.2, hvΓ'⟩
    exact hxy_ne (hP.drawing_iso.ιV_injOn hxV hyV ((mem_singleton_iff.mp h₁).symm.trans h₂))
  let cu : BoundaryUnit S₁ → Bool := fun
    | .vertex w => decide (w.1 ∈ Kb)
    | .space s => decide (Subtype.val '' s ⊆ Kb)
  have hKib : ∀ i, i ≠ ib → Disjoint (K i) Kb := fun i hi => hKb' ▸ hKdisj hi
  have hcu_vertex : ∀ i, ∀ u ∈ (sideDrawing Γ h.isClosed_left).V ∩ (Subtype.val ⁻¹' K i),
      cu (.vertex u) = cc i := by
    rintro i u ⟨-, hu⟩
    by_cases hi : i = ib
    · subst hi
      rw [hKb'] at hu
      simpa [cu, hcb] using hu
    · rw [hcc_false i hi]
      simpa [cu] using disjoint_left.mp (hKib i hi) hu
  have hcu_space : ∀ i, ∀ s ∈ drawingSpaces (sideDrawing Γ h.isClosed_left),
      s ⊆ Subtype.val ⁻¹' K i → cu (.space s) = cc i := by
    intro i s hs hsK
    have hsK' : Subtype.val '' s ⊆ K i := image_subset_iff.mpr hsK
    by_cases hi : i = ib
    · subst hi
      rw [hKb'] at hsK'
      simpa [cu, hcb, image_subset_iff] using hsK'
    · rw [hcc_false i hi]
      obtain ⟨w, hw⟩ := (nonempty_of_mem_drawingSpaces hs).image Subtype.val
      have hnot : ¬ Subtype.val '' s ⊆ Kb := fun hsub =>
        disjoint_left.mp (hKib i hi) (hsK' hw) (hsub hw)
      simpa [cu, image_subset_iff] using hnot
  have hover : ∀ i i', i ≠ i' → (supportGraph G Γ μ (K i)).vertexSet ∩
      (supportGraph G Γ μ (K i')).vertexSet ⊆ X ∧
      (cc i = cc i' → Disjoint (supportGraph G Γ μ (K i)).vertexSet
        (supportGraph G Γ μ (K i')).vertexSet) := by
    intro i i' hii'
    by_cases hτ : τ i = τ i'
    · have hpieces := Gap.vertexSet_inter_pieces_subset hP j₀ hC f ht₀x hxy hyt₁ hlt' ht₀V ht₁V
        hxV hyV hFj
      rcases hτ_eq i i' hii' hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hca, hcb, hKa', hKb']
        exact ⟨hpieces, fun h' => absurd h' (by simp)⟩
      · rw [hca, hcb, hKa', hKb', Set.inter_comm]
        exact ⟨hpieces, fun h' => absurd h' (by simp)⟩
    · have hd : Disjoint (supportGraph G Γ μ (K i)).vertexSet
          (supportGraph G Γ μ (K i')).vertexSet :=
        (hP.v1_disjoint hτ).mono (hH₁le i).vertexSet_subset (hH₁le i').vertexSet_subset
      exact ⟨fun v hv => absurd hv.2 (disjoint_left.mp hd hv.1), fun _ => hd⟩
  have hPres := isPresentation_splitAlong hOP hXG cc cu hcolor hΓE hΓX hcu_vertex hcu_space hover
    (fun v hv => ⟨ia, hca, hXa hv⟩) (fun v hv => ⟨ib, hcb, hXb hv⟩)
  -- The linkage of the side.
  have hunion : (μ (.vertex (cuffPoint f x))).vertexSet ∪ (μ (.vertex (cuffPoint f y))).vertexSet =
      (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet := by
    rcases hxab with h₁ | h₁ <;> rcases hyab with h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hxy_ne
    · rw [h₁, h₂]
    · rw [h₁, h₂, Set.union_comm]
    · exact absurd (h₁.trans h₂.symm) hxy_ne
  have hspace : ∀ j, (F_star j ∩ S₁).Nonempty → ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j →
      Disjoint s S₁ → (μ (.space s)).vertexSet ∩ (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ⊆
        (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet := by
    intro j hne s hs hsF hsS₁
    by_cases hj : j = j₀
    · subst hj
      rw [← hunion]
      exact Gap.space_inter_pieces_subset hP j hC f ht₀x hxy hyt₁ hlt' ht₀V ht₁V hxV hyV hFj hS
        hsplit hs hsF hsS₁
    · exact space_inter_supportGraph_side_subset hP h j (hsupp_j j hj hne) hs hsF hsS₁
  obtain ⟨hL₁, hLp₁⟩ := isExhaustiveLinkage_side_of hP h (r₁ := m + 2)
    (H₁ := fun i => supportGraph G Γ μ (K i)) hqf hspace
    (fun hx => (supportGraph_subset_iUnion (hKV _) (hKs _)).1 hx) hL hLp
  have hXfin : X.Finite := (μ _).vertexSet_finite.subset inter_subset_left
  obtain ⟨hV₂, hT₂⟩ := isVitalPLinkage_splitAlong ⟨hL₁.1, hLp₁⟩ hXfin.toFinset
    (by rw [hXfin.coe_toFinset]; exact hXG) E₂
  rw [hXfin.coe_toFinset] at hV₂ hT₂
  have hXcard : hXfin.toFinset.card ≤ q := by
    rw [← ncard_eq_toFinset_card X hXfin]
    calc X.ncard ≤ (μ (.vertex (cuffPoint f x))).vertexSet.ncard :=
          ncard_le_ncard inter_subset_left (μ _).vertexSet_finite
      _ = qf j₀ := (hP.μ_vertex_sub j₀ _ hxF).2.2.1
      _ ≤ q := hqf j₀
  -- The split graph has an exhaustive vital `(p + 4q)`-linkage.
  have hExh : IsExhaustiveLinkage (splitAlong (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) X E₂)
      (isoImage (splitName X false) id (sideSub Γ Γ_sub ιV ιE S₁)) (m + 2)
      (fun i => isoImage (splitName X (cc i)) id (supportGraph G Γ μ (K i)))
      (splitSpanningSubgraph (splitAlong (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) X E₂)
        (isoImage Sum.inl id (L ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁))) := by
    refine ⟨hV₂.1, le_splitSpanningSubgraph hPres.drawing_subgraph
      (image_mono hL₁.2.1.edgeSet_subset), ?_⟩
    intro t ht
    rcases hT₂ ht with (⟨t', ht', rfl⟩ | ⟨v, hv, rfl⟩) | ⟨v, hv, rfl⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hL₁.2.2 ht')
      have ht'X : t' ∉ X := (mem_splitAlong_inl (E₂ := E₂).mp ht.1).2
      exact mem_iUnion.mpr ⟨i, t', hi, splitName_of_notMem ht'X⟩
    · exact mem_iUnion.mpr ⟨ia, v, hXa hv, by rw [hca, splitName_false_of_mem hv]; rfl⟩
    · exact mem_iUnion.mpr ⟨ib, v, hXb hv, by rw [hcb, splitName_true_of_mem hv]; rfl⟩
  have hLp₂ := IsPLinkage.mono hV₂.2 (show p + 2 * q + 2 * hXfin.toFinset.card ≤ p + 4 * q by
    omega)
  -- The number of pieces.
  have hcard : m + 2 ≤ r + 1 := by
    have h₁ : (Finset.univ.image σ).card = m := by
      rw [Finset.card_image_of_injective _ hσ, Finset.card_univ, Fintype.card_fin]
    have h₂ : Finset.univ.image σ ⊆ Finset.univ.erase j₀ := fun j hj => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_erase.mpr ⟨hσj k, Finset.mem_univ _⟩
    have h₃ := Finset.card_le_card h₂
    rw [h₁, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin] at h₃
    have : 0 < r' := j₀.pos
    omega
  have hG₁ := isGraph_of_le (sideGraph_le hP h.isClosed_left) hG
  exact (encard_sigmaJumps_le_isoImage (splitName_injective false)).trans
    (hlam _ h.surface_left n₁ c₁ hT₁ hlt _ _ _ _ _ _ _ _ _ _ (isGraph_splitAlong hG₁ X E₂) hcard
      ⟨_, hPres, fun i => hqf _, fun h' => absurd h' (by omega)⟩ hExh hLp₂)

/-- **The bound for the side that holds the middle of a cut support** (Graph Minors XXI, proof of
(6.3), claim (4), page 29 of the preprint). Let `F_{j₀}* = f([t₀, t₁])` hold both ends of `F`, at
the angles `x < y`, and let `Σ₁` contain the arc of angles `(x, y)` and miss the arc of angles
`(y, x + 2π)`. Then `F_{j₀}* ∩ Σ₁ = f([x, y])` is a support, and so is every other nonempty
`F_j* ∩ Σ₁` (`isSupport_inter_side`), so `side_jumps_le_of_supports` applies. -/
theorem side_jumps_le_of_mid (hS : IsSurface S) {n c p q r lam : ℕ}
    (hlam : BoundBelow.{u, v} n c (p + 4 * q) q (r + 1) lam)
    (hP : IsPresentation G Γ Γ_sub ιV ιE r' F_star H μ qf) (hqf : ∀ j, qf j ≤ q) (hr : r' ≤ r)
    (hG : G.IsGraph) (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (h : IsSideOfLine Γ S₁ S₂ F a b) [ConnectedSpace S₁] {n₁ c₁ : ℕ} (hT₁ : HasType S₁ n₁ c₁)
    (hlt : TypeLt n₁ c₁ n c) {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C) (j₀ : Fin r')
    {t₀ t₁ x y : ℝ} (ht₀x : t₀ ≤ x) (hxy : x < y) (hyt₁ : y ≤ t₁)
    (hlt' : t₁ < t₀ + 2 * Real.pi) (hFj : F_star j₀ = cuffPoint f '' Icc t₀ t₁)
    (hab : ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b})
    (hM : cuffPoint f '' Ioo x y ⊆ S₁)
    (hO : Disjoint (cuffPoint f '' Ioo y (x + 2 * Real.pi)) S₁) :
    (sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
      (ιV ∘ Subtype.val)).encard ≤ lam := by
  have hxab : cuffPoint f x = a ∨ cuffPoint f x = b := by
    have : cuffPoint f x ∈ ({a, b} : Set S) := hab ▸ Or.inl rfl
    exact this
  have hyab : cuffPoint f y = a ∨ cuffPoint f y = b := by
    have : cuffPoint f y ∈ ({a, b} : Set S) := hab ▸ Or.inr rfl
    exact this
  have hxV : cuffPoint f x ∈ Γ.V := by rcases hxab with h' | h' <;> rw [h']
                                       exacts [h.left_mem, h.right_mem]
  have hyV : cuffPoint f y ∈ Γ.V := by rcases hyab with h' | h' <;> rw [h']
                                       exacts [h.left_mem, h.right_mem]
  -- `a` is one of the points at angles `x` and `y`, so it lies in `F_{j₀}*`.
  have haF : a ∈ F_star j₀ := by
    have ha : a ∈ ({cuffPoint f x, cuffPoint f y} : Set S) := hab ▸ Or.inl rfl
    rw [hFj]
    rcases ha with h' | h'
    · exact h' ▸ ⟨x, ⟨ht₀x, hxy.le.trans hyt₁⟩, rfl⟩
    · exact h' ▸ ⟨y, ⟨ht₀x.trans hxy.le, hyt₁⟩, rfl⟩
  have hsplit : F_star j₀ ∩ S₁ = cuffPoint f '' Icc x y := by
    rw [hFj]
    exact Gap.inter_side_eq_of_mid_subset h f ht₀x hxy hyt₁ hlt' hab hO hM
  refine side_jumps_le_of_supports hlam hP hqf hr hG hL hLp h hT₁ hlt fun j hne => ?_
  by_cases hj : j = j₀
  · subst hj
    rw [hsplit]
    exact ⟨_, _, supportHasEnds_cuffPoint_Icc hS hC f ht₀x hxy.le hyt₁ hlt' hxV hyV⟩
  · exact isSupport_inter_side h (hP.supports_isSupport j)
      (fun hab' => disjoint_left.mp (hP.supports_disjoint hj) hab'.1 haF) hne

/-- **Graph Minors XXI, proof of (6.3), claim (4)** (page 29 of the preprint), with the
correction in `corrections/GM21.md`: "If both $\Sigma_1$ and $\Sigma_2$ are not discs, then by
(4.2)(i) and (4.2)(ii), either $\hat{\Sigma}_i$ is simpler than $\hat{\Sigma}$, or $\hat{\Sigma}_i$
is homeomorphic to $\hat{\Sigma}$ and $c(\Sigma_i) < c(\Sigma)$ for $i = 1, 2$. But then from (1),
there are $\le \lambda(p + 2q, q, r + 1)$ $\Sigma_i$-jumps in $\Gamma_i$ for $i = 1, 2$, and hence
$\le 2\lambda(p + 2q, q, r + 1) \le \lambda$ $\Sigma$-jumps in $\Gamma$, as required."

Here `F` is a proper line with both ends in one cuff `C`, with sides `Σ₁, Σ₂`, and `hlam` is the
inductive hypothesis (1) for `λ(p + 4q, q, r + 1)`. Either there is a closed disc `Δ ⊆ Σ` with
`F ⊆ bd(Δ) ⊆ F ∪ bd(Σ)`, or there are at most `2λ(p + 4q, q, r + 1)` jumps. When no support holds
both ends of `F`, the nonempty pieces of supports on each side are supports. When a support
`F_{j₀}*` holds both, the two arcs of `C` between `a` and `b` lie on different sides
(`Gap.arcs_on_sides`). The side with the arc inside `F_{j₀}*` is bounded by
`side_jumps_le_of_mid`, the other side by `side_jumps_le_of_gap`. -/
theorem claim_4 [ConnectedSpace S] (hS : IsSurface S) {n c : ℕ} (hT : HasType S n c)
    {p q r lam : ℕ} (hlam : BoundBelow.{u, v} n c (p + 4 * q) q (r + 1) lam) (hG : G.IsGraph)
    (hr : r' ≤ r) (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    (h : IsSideOfLine Γ S₁ S₂ F a b) [ConnectedSpace S₁] [ConnectedSpace S₂] {C : Set S}
    (hC : C ∈ cuffs S) (haC : a ∈ C) (hbC : b ∈ C) :
    (∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S) ∨
      (sigmaJumps Γ Γ_sub ιV).encard ≤ lam + lam := by
  classical
  obtain ⟨n₁, c₁, hT₁⟩ := exists_hasType h.surface_left
  obtain ⟨n₂, c₂, hT₂⟩ := exists_hasType h.surface_right
  rcases sides_typeLt_or_disc hS h.surface_left h.surface_right h.union_eq h.inter_eq h.proper
    hC haC hbC hT hT₁ hT₂ with hΔ | ⟨hlt₁, hlt₂⟩
  · exact Or.inl hΔ
  right
  obtain ⟨qf, hP, hqf, -⟩ := hd
  refine (encard_sigmaJumps_le_side hP h).trans ?_
  by_cases hboth : ∃ j₀, a ∈ F_star j₀ ∧ b ∈ F_star j₀
  swap
  · -- No support holds both ends: every nonempty piece of a support is a support.
    exact add_le_add
      (side_jumps_le_of_supports hlam hP hqf hr hG hL hLp h hT₁ hlt₁ fun j hne =>
        isSupport_inter_side h (hP.supports_isSupport j) (not_exists.mp hboth j) hne)
      (side_jumps_le_of_supports hlam hP hqf hr hG hL hLp h.symm hT₂ hlt₂ fun j hne =>
        isSupport_inter_side h.symm (hP.supports_isSupport j) (not_exists.mp hboth j) hne)
  obtain ⟨j₀, haj, hbj⟩ := hboth
  -- Read `F_{j₀}*` as the angles `[t₀, t₁]` on its cuff.
  obtain ⟨e₀, e₁, hFe⟩ := hP.supports_isSupport j₀
  obtain ⟨C', hC', hFC'⟩ := exists_cuff_of_supportHasEnds hFe
  set f := cuffHomeo hS hC'
  obtain ⟨t₀, -, t₁, ⟨-, hlt'⟩, hends, hFeq, -⟩ := support_eq_cuffPoint_Icc hS hC' f hFe hFC'
  have hFends := ends_mem_of_supportHasEnds hFe
  have ht₀V : cuffPoint f t₀ ∈ Γ.V := by
    rcases hends with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h']
    · exact hFends.2.2.1.1
    · exact hFends.2.2.2.1.1
  have ht₁V : cuffPoint f t₁ ∈ Γ.V := by
    rcases hends with ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [h']
    · exact hFends.2.2.2.1.1
    · exact hFends.2.2.1.1
  -- The angles `x < y` of the ends of `F`.
  obtain ⟨xa, hxa, hxa_eq⟩ := hFeq ▸ haj
  obtain ⟨xb, hxb, hxb_eq⟩ := hFeq ▸ hbj
  have hne : xa ≠ xb := fun h' => h.proper.ne (hxa_eq.symm.trans (h' ▸ hxb_eq))
  obtain ⟨x, y, ht₀x, hxy, hyt₁, hab⟩ : ∃ x y, t₀ ≤ x ∧ x < y ∧ y ≤ t₁ ∧
      ({cuffPoint f x, cuffPoint f y} : Set S) = {a, b} := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨xa, xb, hxa.1, hlt, hxb.2, by rw [hxa_eq, hxb_eq]⟩
    · exact ⟨xb, xa, hxb.1, hlt, hxa.2, by rw [hxa_eq, hxb_eq, pair_comm]⟩
  have hpi := Real.pi_pos
  have hy2 : y < x + 2 * Real.pi := by linarith
  have haC' : a ∈ C' := hFC' haj
  -- A nonempty set cannot miss both sides.
  have hcov : ∀ T : Set S, Disjoint T S₁ → Disjoint T S₂ → T.Nonempty → False := by
    rintro T h₁ h₂ ⟨z, hz⟩
    have : z ∈ S₁ ∪ S₂ := h.union_eq ▸ mem_univ z
    rcases this with hz' | hz'
    exacts [disjoint_left.mp h₁ hz hz', disjoint_left.mp h₂ hz hz']
  have hmid : (cuffPoint f '' Ioo x y).Nonempty := (nonempty_Ioo.mpr hxy).image _
  have hout : (cuffPoint f '' Ioo y (x + 2 * Real.pi)).Nonempty :=
    (nonempty_Ioo.mpr hy2).image _
  rcases Gap.arcs_on_sides hS h hC' haC' f hxy hy2 hab with ⟨hM₁, hO₁⟩ | ⟨hM₁, hO₁⟩ <;>
    rcases Gap.arcs_on_sides hS h.symm hC' haC' f hxy hy2 hab with ⟨hM₂, hO₂⟩ | ⟨hM₂, hO₂⟩
  · exact (hcov _ hO₁ hO₂ hout).elim
  · exact add_le_add
      (side_jumps_le_of_mid hS hlam hP hqf hr hG hL hLp h hT₁ hlt₁ hC' f j₀ ht₀x hxy hyt₁ hlt'
        hFeq hab hM₁ hO₁)
      (side_jumps_le_of_gap hS hlam hP hqf hr hG hL hLp h.symm hT₂ hlt₂ hC' f j₀ ht₀x hxy hyt₁
        hlt' ht₀V ht₁V hFeq hab hM₂ hO₂)
  · exact add_le_add
      (side_jumps_le_of_gap hS hlam hP hqf hr hG hL hLp h hT₁ hlt₁ hC' f j₀ ht₀x hxy hyt₁
        hlt' ht₀V ht₁V hFeq hab hM₁ hO₁)
      (side_jumps_le_of_mid hS hlam hP hqf hr hG hL hLp h.symm hT₂ hlt₂ hC' f j₀ ht₀x hxy hyt₁
        hlt' hFeq hab hM₂ hO₂)
  · exact (hcov _ hM₁ hM₂ hmid).elim

end ClaimFour
end GM21
end GraphMinor
