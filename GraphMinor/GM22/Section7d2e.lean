module

public import GraphMinor.GM22.Section7d2a
public import GraphMinor.GM22.Section7d2d
public import GraphMinor.GM12.Section77
public import GraphMinor.GM12.Section79

/-!
# Graph Minors XXII – Section 7.4 (Part 2e): Claims (2) and (4)

This file completes the proofs of **Claim (2)** and **Claim (4)** of **Theorem 7.4** from
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (pages 553–554):

- `subsetTangleDist_le_of_inducedBySubgraph`: monotonic increase of `subsetTangleDist` under
  tangle induction to a 2-cell superdrawing (`GM12.theorem_7_7_proof`).
- `isTangleIns_of_inducedBySubgraph`: preservation of `IsTangleIns` under tangle induction to a
  superdrawing.
- `nonempty_range_πS_inter_V_of_nonempty_D_inter_U`: if `D A` meets `Γ.U`, then `bd(D A)` meets
  `Γ.V` in `Set.range (πS A)`.
- `lemma_7_4_claim_2`: Claim (2) of (7.4) (page 553).
- `lemma_7_4_claim_4`: Claim (4) of (7.4) (page 554).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06
  GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 Hypergraph

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
  {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Tangle Induction to a 2-Cell Superdrawing -/

/-- By `GM12.theorem_7_7_proof`, if `Γ` is a 2-cell subdrawing of a 2-cell drawing `Γ'` in a connected
closed surface `S`, and `T'` is the tangle of order `ord` in `Γ'` induced by `T`, with metric `d'`,
then `subsetTangleDist Γ ord d X Y ≤ subsetTangleDist Γ' ord d' X Y` for all `X, Y ⊆ S`. -/
theorem subsetTangleDist_le_of_inducedBySubgraph
    (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ Γ' : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ}
    (hSub : Γ.IsSubdrawing Γ')
    (hd : HasTangleMetric Γ ord T d)
    (hd' : HasTangleMetric Γ' ord (inducedBySubgraph Γ'.toHypergraph Γ.toHypergraph ord T) d')
    (X Y : Set S) :
    subsetTangleDist Γ ord d X Y ≤ subsetTangleDist Γ' ord d' X Y := by
  have h77 := (GM12.theorem_7_7_proof hS hd' hSub hd.1.1 le_rfl hd).2 rfl rfl
  unfold subsetTangleDist
  by_cases h : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty <;>
    by_cases h' : ∃ a' ∈ Γ'.A, ∃ b' ∈ Γ'.A, (a' ∩ X).Nonempty ∧ (b' ∩ Y).Nonempty <;>
    simp only [h, h', ↓reduceIte]
  · rcases h' with ⟨a', ha', b', hb', ha'X, hb'Y⟩
    refine le_csInf ⟨d' a' b', a', ha', b', hb', ha'X, hb'Y, rfl⟩ ?_
    rintro k ⟨a₁', ha₁', b₁', hb₁', ha₁'X, hb₁'Y, rfl⟩
    obtain ⟨a₁, ha₁, ha₁_sub⟩ := exists_atom_superset_of_isSubdrawing hSub ha₁'
    obtain ⟨b₁, hb₁, hb₁_sub⟩ := exists_atom_superset_of_isSubdrawing hSub hb₁'
    have ha₁X : (a₁ ∩ X).Nonempty := ha₁'X.mono (inter_subset_inter_left X ha₁_sub)
    have hb₁Y : (b₁ ∩ Y).Nonempty := hb₁'Y.mono (inter_subset_inter_left Y hb₁_sub)
    have hcs : sInf {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k}
        ≤ d a₁ b₁ :=
      Nat.sInf_le ⟨a₁, ha₁, b₁, hb₁, ha₁X, hb₁Y, rfl⟩
    exact hcs.trans (h77 a₁' ha₁' b₁' hb₁' a₁ ha₁ b₁ hb₁ ha₁_sub hb₁_sub)
  · rcases h with ⟨a, ha, b, hb, haX, hbY⟩
    have hcs : sInf {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k}
        ≤ d a b :=
      Nat.sInf_le ⟨a, ha, b, hb, haX, hbY, rfl⟩
    exact hcs.trans (HasTangleMetric.le_ord hd ha hb)
  · rcases h' with ⟨a', ha', b', hb', ha'X, hb'Y⟩
    obtain ⟨a, ha, ha_sub⟩ := exists_atom_superset_of_isSubdrawing hSub ha'
    obtain ⟨b, hb, hb_sub⟩ := exists_atom_superset_of_isSubdrawing hSub hb'
    exact False.elim (h ⟨a, ha, b, hb,
      ha'X.mono (inter_subset_inter_left X ha_sub),
      hb'Y.mono (inter_subset_inter_left Y hb_sub)⟩)
  · exact le_rfl

omit [T2Space S] in
private theorem drawing_inter_le_toHypergraph (H' : Drawing S) {D : Set S} (hD : IsClosed D) :
    (PaintingOrDrawing.drawing H').inter D ≤ H'.toHypergraph := by
  refine ⟨inter_subset_left, fun _ h => h.1, fun e he => ?_⟩
  ext v
  change (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ↔
    (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ∧ e ⊆ D ∧ v ∈ D
  exact ⟨fun h => ⟨h, he.2, hD.closure_subset_iff.mpr he.2 h.2.2⟩, fun h => h.1⟩

/-- If `Γ` is a subdrawing of `Γ'`, `F` is a `Γ'`-normal `O`-arc with `(F ∩ Γ'.V).ncard < ord`,
and `IsTangleIns Γ T F Δ`, then
`IsTangleIns Γ' (inducedBySubgraph Γ'.toHypergraph Γ.toHypergraph ord T) F Δ`. -/
theorem isTangleIns_of_inducedBySubgraph
    {Γ Γ' : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {F Δ : Set S}
    (hSub : Γ.IsSubdrawing Γ')
    (hF : IsOArc F)
    (hNorm' : Γ'.IsNormal F)
    (hcard' : (F ∩ Γ'.V).ncard < ord)
    (hIns : IsTangleIns Γ T F Δ) :
    IsTangleIns Γ' (inducedBySubgraph Γ'.toHypergraph Γ.toHypergraph ord T) F Δ := by
  have _ := hF
  rcases hIns with ⟨hΔ, hbd, hmem₀⟩
  refine ⟨hΔ, hbd, ?_, ?_, ?_⟩
  · have hAl : (PaintingOrDrawing.drawing Γ').inter Δ ≤ Γ'.toHypergraph :=
      drawing_inter_le_toHypergraph Γ' hΔ.isClosed
    have hBl : (PaintingOrDrawing.drawing Γ').interOutside Δ ≤ Γ'.toHypergraph :=
      drawing_inter_le_toHypergraph Γ' isClosed_closure
    refine (GM10.isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩
    · ext x
      change (x ∈ Γ'.V ∩ Δ ∨ x ∈ Γ'.V ∩ closure (univ \ Δ)) ↔ x ∈ Γ'.V
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases hxΔ : x ∈ Δ
        · exact Or.inl ⟨hx, hxΔ⟩
        · exact Or.inr ⟨hx, subset_closure ⟨mem_univ x, hxΔ⟩⟩
    · ext e
      change (e ∈ {e ∈ Γ'.E | e ⊆ Δ} ∨ e ∈ {e ∈ Γ'.E | e ⊆ closure (univ \ Δ)}) ↔ e ∈ Γ'.E
      constructor
      · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
      · intro he
        obtain ⟨x, hxe⟩ := he.1
        have he_pre : IsPreconnected e :=
          (GM11.PaintingOrDrawing.edge_props (Γ := PaintingOrDrawing.drawing Γ') he).1
        have hdisF : Disjoint e (frontier Δ) := by
          rw [GM11.subBd_eq_frontier' Δ, hbd]
          exact disjoint_left.mpr fun y hye hyF =>
            (he.2.1 hye).2 (hNorm' ⟨hyF, (he.2.1 hye).1⟩)
        by_cases hxΔ : x ∈ Δ
        · exact Or.inl ⟨he, GM12.subset_of_disjoint_frontier
            he_pre hΔ.isClosed hdisF hxe hxΔ⟩
        · have hdisF' : Disjoint e (frontier (closure (univ \ Δ))) := by
            refine Disjoint.mono_right ?_ hdisF
            intro y hy
            have hy1 : y ∈ frontier (univ \ Δ) := frontier_closure_subset hy
            rwa [← compl_eq_univ_sdiff, frontier_compl] at hy1
          exact Or.inr ⟨he, GM12.subset_of_disjoint_frontier
            he_pre isClosed_closure hdisF' hxe (subset_closure ⟨mem_univ x, hxΔ⟩)⟩
    · ext e
      change (e ∈ {e ∈ Γ'.E | e ⊆ Δ} ∧ e ∈ {e ∈ Γ'.E | e ⊆ closure (univ \ Δ)}) ↔
        e ∈ (∅ : Set (Set S))
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨he, heΔ⟩, ⟨_, heOut⟩⟩
      obtain ⟨x, hxe⟩ := he.1
      have hxF : x ∈ F := by
        rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
        exact ⟨subset_closure (heΔ hxe), heOut hxe⟩
      exact (he.2.1 hxe).2 (hNorm' ⟨hxF, (he.2.1 hxe).1⟩)
  · have hsub : (((PaintingOrDrawing.drawing Γ').inter Δ) ∩
        ((PaintingOrDrawing.drawing Γ').interOutside Δ)).vertexSet ⊆ F ∩ Γ'.V := by
      rintro x ⟨⟨hxV, hxΔ⟩, ⟨_, hxOut⟩⟩
      refine ⟨?_, hxV⟩
      rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
      exact ⟨subset_closure hxΔ, hxOut⟩
    exact lt_of_le_of_lt (ncard_le_ncard hsub (Γ'.finite_V.subset inter_subset_right)) hcard'
  · rwa [drawing_inter_inter_subdrawing hSub Δ, drawing_interOutside_inter_subdrawing hSub Δ]

/-! ## 2. Boundary Vertex Intersection when `(D A ∩ Γ.U).Nonempty` -/

/-- Under `(J1)`–`(J6)`, if `A ∈ 𝒜` and `(D A ∩ Γ.U).Nonempty`, then
`(Set.range (πS A) ∩ Γ.V).Nonempty`. -/
theorem nonempty_range_πS_inter_V_of_nonempty_D_inter_U {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    {A : Graph α β} (hA : A ∈ 𝒜) (hne : (D A ∩ Γ.U).Nonempty) :
    (Set.range (πS A) ∩ Γ.V).Nonempty := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hD_disc : IsClosedDisc (D A) := (hJ.disc_D A hA).1
  have hD_norm : Γ.IsNormal (subBd (D A)) := (hJ.disc_D A hA).2.1
  have hD_ins_eq : D A = ins (subBd (D A)) := (hJ.disc_D A hA).2.2
  have hV_sub_VG : Γ.V ⊆ ιV ⁻¹' V(R_G.G.toGraph) := by
    intro x hx
    exact (hJ.Γ_le.trans deleteVerts_le).vertexSet_mono ⟨x, hx, rfl⟩
  have hbd_V_sub : subBd (D A) ∩ Γ.V ⊆ Set.range (πS A) := by
    rw [hJ.π_bar_eq_bd_inter A hA]
    exact inter_subset_inter_right _ hV_sub_VG
  have hπ_fin : (Set.range (πS A)).Finite := Set.finite_range (πS A)
  have hcard_π : (Set.range (πS A)).ncard ≤ 3 := by
    have h1 := Set.ncard_range_of_injective (hJ.π_valid A hA).2.2.1
    have h2 := (hJ.π_valid A hA).2.1
    rw [Nat.card_fin] at h1
    omega
  have h4 := hJ.four_le_θ
  have hθ_ord := hJ.θ_le_ord
  have hcard_lt : (subBd (D A) ∩ Γ.V).ncard < ord := by
    have hle := Set.ncard_le_ncard hbd_V_sub hπ_fin
    omega
  have hOArc_bd : IsOArc (subBd (D A)) := by
    rw [IsClosedDisc.subBd_eq_discBd hS hD_disc]
    exact hD_disc.isOArc_discBd
  have hIns : IsTangleIns Γ T (subBd (D A)) (D A) := by
    have hspec := hJ.ins_spec (subBd (D A)) hOArc_bd hD_norm hcard_lt
    rwa [← hD_ins_eq] at hspec
  have hT : IsTangle Γ.toHypergraph ord T := hJ.hasMetric.1.2.1
  have hV_not_sub : ¬ (Γ.V ⊆ D A) := by
    intro hsub
    have hVEq : ((PaintingOrDrawing.drawing Γ).inter (D A)).vertexSet = Γ.toHypergraph.vertexSet :=
      Subset.antisymm inter_subset_left (subset_inter Subset.rfl hsub)
    exact hT.axiom3 hIns.2.2 hVEq
  have hU_not_sub : ¬ (Γ.U ⊆ D A) := fun hsub => hV_not_sub (Γ.V_subset_U.trans hsub)
  have hU_pre : IsPreconnected Γ.U := isPreconnected_U_of_isTwoCell hS hJ.isTwoCell
  have hnot_disj : ¬ Disjoint Γ.U (frontier (D A)) := by
    intro hdisj
    rcases hne with ⟨x₀, hx₀D, hx₀U⟩
    exact hU_not_sub (isPreconnected_subset_of_disjoint_frontier'
      hU_pre hD_disc.isCompact.isClosed hdisj hx₀U hx₀D)
  rw [← GM11.subBd_eq_frontier, Set.not_disjoint_iff] at hnot_disj
  rcases hnot_disj with ⟨z, hzU, hzbd⟩
  have hzV : z ∈ Γ.V := hD_norm ⟨hzbd, hzU⟩
  exact ⟨z, hbd_V_sub ⟨hzbd, hzV⟩, hzV⟩

/-! ## 3. Proof of Claim (2) of Theorem 7.4 (page 553) -/

private theorem walk_length_pos_of_edges_nonempty {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) (hne : {e | e ∈ W.edges}.Nonempty) :
    1 ≤ W.length := by
  rcases hne with ⟨e₀, he₀⟩
  cases W with
  | nil _ => exact False.elim (List.not_mem_nil he₀)
  | cons _ _ =>
    rw [GraphWalk.length_cons]
    omega

set_option maxHeartbeats 800000 in
/-- **Graph Minors XXII, (7.4) Claim (2)** (page 553):
(2) *If $A \in \mathcal{A}$ is bad then either $d(D(A), \Sigma \setminus \Delta) \ge \theta$, or $D(A) \cap U(\Gamma) = \emptyset$.*

The subproof prints "If we replace $\Gamma$ by $\Gamma'$ and $d$ and $d'$ then (J1)–(J6) remain
satisfied", a misprint for "$d$ by $d'$"; the Lean replaces $d$ by the metric $d'$ of the induced
tangle (see the correction to the proof of (7.4) in `corrections/GM22.md`). -/
theorem lemma_7_4_claim_2
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (hc_ext : c.IsExtremal)
    {A : Graph α β} (hA : A ∈ 𝒜)
    (hBad : IsBadMember c.ιV c.ιE c.Γ πLen πS A) :
    θ ≤ subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) ∨ Disjoint (D A) c.Γ.U := by
  by_contra! hcontra
  rcases hcontra with ⟨hdist_lt, hnot_disj⟩
  rw [Set.not_disjoint_iff_nonempty_inter] at hnot_disj
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface c.hJ.isSphere
  have hne_πV : (Set.range (πS A) ∩ c.Γ.V).Nonempty :=
    nonempty_range_πS_inter_V_of_nonempty_D_inter_U c.hJ hA hnot_disj
  -- Step 1: Obtain the augmenting path `Q` in `A \ W` with ends `s₁, s₂` and the chord `L_arc`.
  obtain ⟨s₁, s₂, Q, hs₁₂, hs₁_HAV, hs₂_mem, hQ_path, hQ_ne, hQ_disj_E, hQ_inter, hQ_J7⟩ :=
    exists_augmenting_path_of_bad c.hJ c.hJ7 hA hBad hne_πV
  obtain ⟨L_arc, hL_line, hL_sub_D, hL_int⟩ :=
    exists_chord_of_bad c.hJ c.hJ7 hA hBad hne_πV (Or.inl hs₁_HAV) hs₂_mem hs₁₂
  have hs₁_V : s₁ ∈ c.Γ.V :=
    ((mem_interSet_V_iff (c.hJ.disc_D A hA).1.isCompact.isClosed).mp hs₁_HAV).1
  have hs₁_D : s₁ ∈ D A :=
    ((mem_interSet_V_iff (c.hJ.disc_D A hA).1.isCompact.isClosed).mp hs₁_HAV).2
  have hs₂_D : s₂ ∈ D A := by
    rcases hs₂_mem with hs₂_HAV | hs₂_π
    · exact ((mem_interSet_V_iff (c.hJ.disc_D A hA).1.isCompact.isClosed).mp hs₂_HAV).2
    · rw [c.hJ.π_bar_eq_bd_inter A hA] at hs₂_π
      exact (c.hJ.disc_D A hA).1.isCompact.isClosed.closure_subset_iff.mpr Subset.rfl hs₂_π.1.1
  -- Step 2: Convert `Q` into a simple walk `W_Q` of length `≥ 1` and draw it on `L_arc`.
  obtain ⟨hQ_le_Adel, W_Q, hWQ_simple, hVQ_eq, hEQ_eq⟩ := id hQ_path
  have hWQ_len_pos : 1 ≤ W_Q.length :=
    walk_length_pos_of_edges_nonempty W_Q (hEQ_eq ▸ hQ_ne)
  obtain ⟨M, ιV', ιE', hMU, hs₁_MV, hs₂_MV, hME_ne, hM_emb, hιV'_eq, hιE'_eq⟩ :=
    exists_drawing_of_simpleWalk_on_line (W_Q.length - 1) hL_line hs₁₂ W_Q hWQ_simple (by omega)
  have hwalk_eq_Q : walkSubgraph W_Q = Q := by
    refine (Compatible.of_le_le (walkSubgraph_le W_Q) le_rfl).ext ?_ ?_
    · rw [vertexSet_walkSubgraph, hVQ_eq]
    · rw [edgeSet_walkSubgraph, hEQ_eq]
  have hM_emb_Q : M.toEmbeddedGraph ιV' ιE' = Q := hM_emb.trans hwalk_eq_Q
  -- Step 3: Agreement of `ιV'` and `ιE'` with `c.ιV` and `c.ιE`.
  have hL_int_not_U : ∀ x ∈ L_arc \ {s₁, s₂}, x ∉ c.Γ.U :=
    fun x hx => (hL_int hx).2
  have hL_int_not_bd : ∀ A₀ ∈ 𝒜, ∀ x ∈ L_arc \ {s₁, s₂}, x ∉ subBd (D A₀) := by
    intro A₀ hA₀ x hx hxbd
    by_cases hA₀_eq : A₀ = A
    · subst A₀
      exact (hL_int hx).1.2 hxbd
    · have hx_DA₀ : x ∈ D A₀ :=
        (c.hJ.disc_D A₀ hA₀).1.isCompact.isClosed.closure_subset_iff.mpr Subset.rfl hxbd.1
      have hx_inter : x ∈ D A ∩ D A₀ := ⟨(hL_int hx).1.1, hx_DA₀⟩
      rw [c.hJ.D_inter_eq A hA A₀ hA₀ (Ne.symm hA₀_eq)] at hx_inter
      have hx_bdA : x ∈ subBd (D A) := by
        have := hx_inter.1
        rw [c.hJ.π_bar_eq_bd_inter A hA] at this
        exact this.1
      exact (hL_int hx).1.2 hx_bdA
  have hL_int_not_D_other : ∀ A₀ ∈ 𝒜, A₀ ≠ A → ∀ x ∈ L_arc \ {s₁, s₂}, x ∉ D A₀ := by
    intro A₀ hA₀ hne x hx hx_DA₀
    have hx_inter : x ∈ D A ∩ D A₀ := ⟨(hL_int hx).1.1, hx_DA₀⟩
    rw [c.hJ.D_inter_eq A hA A₀ hA₀ hne.symm] at hx_inter
    have hx_bdA : x ∈ subBd (D A) := by
      have := hx_inter.1
      rw [c.hJ.π_bar_eq_bd_inter A hA] at this
      exact this.1
    exact (hL_int hx).1.2 hx_bdA
  have hVQ_sub_VA : V(Q) ⊆ V(A) \ W := by
    intro z hz
    have hz' := hQ_le_Adel.vertexSet_mono hz
    rwa [vertexSet_deleteVerts] at hz'
  have hEQ_sub_EA : E(Q) ⊆ E(A) :=
    hQ_le_Adel.edgeSet_mono.trans deleteVerts_le.edgeSet_mono
  have hιV'_on_ΓV : ∀ x ∈ c.Γ.V, ιV' x = c.ιV x := by
    intro x hx
    refine hιV'_eq x (fun hxL => hL_int_not_U x hxL (c.Γ.V_subset_U hx)) ?_
    rintro ⟨hx_supp, hx_ne₁, hx_ne₂⟩
    have hx_VQ : c.ιV x ∈ V(Q) := by rwa [hVQ_eq]
    have hx_GA : c.ιV x ∈ V((c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A) :=
      ⟨⟨x, hx, rfl⟩, (hVQ_sub_VA hx_VQ).1⟩
    have hx_end : c.ιV x ∈ ({c.ιV s₁, c.ιV s₂} : Set α) :=
      hQ_inter ⟨hx_VQ, Or.inl hx_GA⟩
    rcases hx_end with h1 | h2
    · exact hx_ne₁ h1
    · exact hx_ne₂ h2
  have hιV'_on_bd : ∀ A₀ ∈ 𝒜, ∀ x ∈ subBd (D A₀), ιV' x = c.ιV x := by
    intro A₀ hA₀ x hxbd
    refine hιV'_eq x (fun hxL => hL_int_not_bd A₀ hA₀ x hxL hxbd) ?_
    rintro ⟨hx_supp, hx_ne₁, hx_ne₂⟩
    have hx_VQ : c.ιV x ∈ V(Q) := by rwa [hVQ_eq]
    have hx_VG : c.ιV x ∈ V(R_G.G.toGraph) :=
      (c.hJ.le_of_mem_𝒜 A hA).vertexSet_mono (hVQ_sub_VA hx_VQ).1
    have hx_πA₀ : x ∈ Set.range (πS A₀) := by
      rw [c.hJ.π_bar_eq_bd_inter A₀ hA₀]
      exact ⟨hxbd, hx_VG⟩
    have hx_πA : c.ιV x ∈ c.ιV '' Set.range (πS A) := by
      by_cases hA₀_eq : A₀ = A
      · subst A₀
        exact ⟨x, hx_πA₀, rfl⟩
      · rcases hx_πA₀ with ⟨i, rfl⟩
        have hx_VA₀ : c.ιV (πS A₀ i) ∈ V(A₀) \ W := (c.hJ.π_valid A₀ hA₀).2.2.2 i
        have hx_inter : c.ιV (πS A₀ i) ∈ V(A) ∩ V(A₀) :=
          ⟨(hVQ_sub_VA hx_VQ).1, hx_VA₀.1⟩
        rw [c.hJ.vertex_inter_𝒜 A hA A₀ hA₀ (Ne.symm hA₀_eq)] at hx_inter
        rcases hx_inter with ⟨hx_πA, _⟩ | hxW
        · exact hx_πA
        · exact False.elim (hx_VA₀.2 hxW)
    have hx_end : c.ιV x ∈ ({c.ιV s₁, c.ιV s₂} : Set α) :=
      hQ_inter ⟨hx_VQ, Or.inr hx_πA⟩
    rcases hx_end with h1 | h2
    · exact hx_ne₁ h1
    · exact hx_ne₂ h2
  have hιV'_on_π : ∀ A₀ ∈ 𝒜, ∀ x ∈ Set.range (πS A₀), ιV' x = c.ιV x := by
    intro A₀ hA₀ x hxπ
    have hxbd : x ∈ subBd (D A₀) := by
      rw [c.hJ.π_bar_eq_bd_inter A₀ hA₀] at hxπ
      exact hxπ.1
    exact hιV'_on_bd A₀ hA₀ x hxbd
  have hπ_img_eq : ∀ A₀ ∈ 𝒜, ιV' '' Set.range (πS A₀) = c.ιV '' Set.range (πS A₀) := by
    intro A₀ hA₀
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hιV'_on_π A₀ hA₀ x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hιV'_on_π A₀ hA₀ x hx⟩
  have hcompat_Γ_A : ∀ A₀ ∈ 𝒜, (c.Γ.toEmbeddedGraph c.ιV c.ιE).Compatible A₀ :=
    fun A₀ hA₀ => Compatible.of_le_le (c.hJ.Γ_le.trans deleteVerts_le) (c.hJ.le_of_mem_𝒜 A₀ hA₀)
  have hιE'_on_ΓE : ∀ e ∈ c.Γ.E, ιE' e = c.ιE e := by
    intro e he
    refine hιE'_eq e ?_ ?_
    · rintro ⟨⟨z, hze⟩, he_sub⟩
      exact hL_int_not_U z (he_sub hze) (he.2.1 hze).1
    · intro he_edges
      have he_EQ : c.ιE e ∈ E(Q) := by rwa [hEQ_eq]
      have he_GA : c.ιE e ∈ E((c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A) := by
        rw [(hcompat_Γ_A A hA).edgeSet_inf]
        exact ⟨⟨e, he, rfl⟩, hEQ_sub_EA he_EQ⟩
      exact Set.disjoint_left.mp hQ_disj_E he_EQ he_GA
  have hΓ_emb_eq : c.Γ.toEmbeddedGraph ιV' ιE' = c.Γ.toEmbeddedGraph c.ιV c.ιE :=
    toEmbeddedGraph_congr hιV'_on_ΓV hιE'_on_ΓE
  -- Step 4: Glue `c.Γ` and `M` into `Γ'`.
  have hs₂_ΓV_iff : s₂ ∈ c.Γ.V ↔ s₂ ∈ (c.Γ.interSet (D A)).V :=
    ⟨fun h => (mem_interSet_V_iff (c.hJ.disc_D A hA).1.isCompact.isClosed).mpr ⟨h, hs₂_D⟩,
     fun h => ((mem_interSet_V_iff (c.hJ.disc_D A hA).1.isCompact.isClosed).mp h).1⟩
  have hmeet : c.Γ.U ∩ M.U ⊆ c.Γ.V ∩ M.V := by
    rintro x ⟨hxU, hxMU⟩
    rw [hMU] at hxMU
    by_cases hx_ends : x ∈ ({s₁, s₂} : Set S)
    · rcases hx_ends with rfl | rfl
      · exact ⟨hs₁_V, hs₁_MV⟩
      · refine ⟨?_, hs₂_MV⟩
        rcases hs₂_mem with hs₂_HAV | hs₂_π
        · exact hs₂_ΓV_iff.mpr hs₂_HAV
        · rw [c.hJ.π_bar_eq_bd_inter A hA] at hs₂_π
          exact (c.hJ.disc_D A hA).2.1 ⟨hs₂_π.1, hxU⟩
    · exact False.elim (hL_int_not_U x ⟨hxMU, hx_ends⟩ hxU)
  have hE_disj : Disjoint c.Γ.E M.E := by
    rw [Set.disjoint_left]
    intro e heΓ heM
    obtain ⟨z, hze⟩ := heM.1
    have hz_MU : z ∈ M.U \ M.V := heM.2.1 hze
    have hz_L_int : z ∈ L_arc \ {s₁, s₂} := by
      refine ⟨hMU ▸ hz_MU.1, ?_⟩
      rintro (rfl | rfl)
      · exact hz_MU.2 hs₁_MV
      · exact hz_MU.2 hs₂_MV
    exact hL_int_not_U z hz_L_int (heΓ.2.1 hze).1
  let Γ' : Drawing S := c.Γ.glue M hmeet
  have hSub : c.Γ.IsSubdrawing Γ' :=
    ⟨subset_union_left, by rw [Drawing.glue_E]; exact subset_union_left⟩
  have hSub_M : M.IsSubdrawing Γ' :=
    ⟨subset_union_right, by rw [Drawing.glue_E]; exact subset_union_right⟩
  have hΓ'_emb : Γ'.toEmbeddedGraph ιV' ιE' =
      graphUnion (c.Γ.toEmbeddedGraph c.ιV c.ιE) Q := by
    rw [glue_toEmbeddedGraph_eq_graphUnion hmeet hE_disj ιV' ιE', hΓ_emb_eq, hM_emb_Q]
  have hQ_le_Gdel : Q ≤ R_G.G.toGraph.deleteVerts W := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [vertexSet_deleteVerts]
      have hx' := hVQ_sub_VA hx
      exact ⟨(c.hJ.le_of_mem_𝒜 A hA).vertexSet_mono hx'.1, hx'.2⟩
    · intro e x y hL
      have hLA := hL.mono hQ_le_Adel
      rw [deleteVerts_isLink] at hLA ⊢
      exact ⟨hLA.1.mono (c.hJ.le_of_mem_𝒜 A hA), hLA.2⟩
  have hΓ'_le : Γ'.toEmbeddedGraph ιV' ιE' ≤ R_G.G.toGraph.deleteVerts W := by
    rw [hΓ'_emb]
    exact graphUnion_le c.hJ.Γ_le hQ_le_Gdel
  have h2cell' : Γ'.IsTwoCell := by
    refine isTwoCell_of_subdrawing_of_isPreconnected_U hS c.hJ.isTwoCell ⟨s₁, hs₁_V⟩ hSub ?_
    change IsPreconnected (c.Γ.U ∪ M.U)
    rw [hMU]
    have hL_pre : IsPreconnected L_arc := by
      obtain ⟨f, _, _⟩ := id hL_line
      have hrange : L_arc = range (fun t : unitInterval => (f t).1) := by
        ext z
        exact ⟨fun hz => ⟨f.symm ⟨z, hz⟩, by simp⟩, by rintro ⟨t, rfl⟩; exact (f t).2⟩
      rw [hrange]
      exact isPreconnected_range (continuous_subtype_val.comp f.continuous)
    have hs₁_L : s₁ ∈ L_arc := hMU ▸ M.V_subset_U hs₁_MV
    exact (isPreconnected_U_of_isTwoCell hS c.hJ.isTwoCell).union'
      ⟨s₁, c.Γ.V_subset_U hs₁_V, hs₁_L⟩ hL_pre
  -- Step 5: Induce the respectful tangle `T'` and metric `d'` in `Γ'`.
  let T' := inducedBySubgraph Γ'.toHypergraph c.Γ.toHypergraph c.ord c.T
  have hSubHyp : c.Γ.toHypergraph ≤ Γ'.toHypergraph := toHypergraph_le_of_isSubdrawing hSub
  have hT' : IsTangle Γ'.toHypergraph c.ord T' :=
    inducedBySubgraph_isTangle hSubHyp c.hJ.hasMetric.1.2.1
  have hResp' : (PaintingOrDrawing.drawing Γ').IsRespectful c.ord T' :=
    GM12.isRespectful_inducedBySubgraph hSub c.hJ.hasMetric.1.2.2
  have hRDT' : IsRespectfulDrawingTangle Γ' c.ord T' := ⟨h2cell', hT', hResp'⟩
  obtain ⟨d', hd'⟩ := GM12.exists_hasTangleMetric hS hRDT'
  have hdist_le : ∀ X Y : Set S,
      subsetTangleDist c.Γ c.ord c.d X Y ≤ subsetTangleDist Γ' c.ord d' X Y :=
    subsetTangleDist_le_of_inducedBySubgraph hS hSub c.hJ.hasMetric hd'
  -- Step 6: Verify `Γ'.IsNormal (subBd (D A₀))` and `Γ_inter_D` for all `A₀ ∈ 𝒜`.
  have hMV_sub_L : M.V ⊆ L_arc := hMU ▸ M.V_subset_U
  have hNorm'_bd : ∀ A₀ ∈ 𝒜, Γ'.IsNormal (subBd (D A₀)) := by
    intro A₀ hA₀ x ⟨hxbd, hxU'⟩
    change x ∈ c.Γ.U ∪ M.U at hxU'
    rw [hMU] at hxU'
    rcases hxU' with hxU | hxL
    · exact Or.inl ((c.hJ.disc_D A₀ hA₀).2.1 ⟨hxbd, hxU⟩)
    · by_cases hx_ends : x ∈ ({s₁, s₂} : Set S)
      · rcases hx_ends with rfl | rfl
        · exact Or.inr hs₁_MV
        · exact Or.inr hs₂_MV
      · exact False.elim (hL_int_not_bd A₀ hA₀ x ⟨hxL, hx_ends⟩ hxbd)
  have hMV_inter_D_other : ∀ A₀ ∈ 𝒜, A₀ ≠ A → M.V ∩ D A₀ = {s₁, s₂} ∩ D A₀ := by
    intro A₀ hA₀ hne
    ext x
    constructor
    · rintro ⟨hxMV, hxD⟩
      refine ⟨?_, hxD⟩
      by_contra hx_not
      exact hL_int_not_D_other A₀ hA₀ hne x ⟨hMV_sub_L hxMV, hx_not⟩ hxD
    · rintro ⟨rfl | rfl, hxD⟩
      · exact ⟨hs₁_MV, hxD⟩
      · exact ⟨hs₂_MV, hxD⟩
  have hVQ_inter_VA_other : ∀ A₀ ∈ 𝒜, A₀ ≠ A →
      V(Q) ∩ V(A₀) = ιV' '' (M.V ∩ D A₀) := by
    intro A₀ hA₀ hne
    rw [hMV_inter_D_other A₀ hA₀ hne]
    ext y
    constructor
    · rintro ⟨hyQ, hyA₀⟩
      have hy_AW : y ∈ V(A) \ W := hVQ_sub_VA hyQ
      have hy_inter : y ∈ V(A) ∩ V(A₀) := ⟨hy_AW.1, hyA₀⟩
      rw [c.hJ.vertex_inter_𝒜 A hA A₀ hA₀ hne.symm] at hy_inter
      rcases hy_inter with ⟨hy_πA, hy_πA₀⟩ | hyW
      · have hy_ends : y ∈ ({c.ιV s₁, c.ιV s₂} : Set α) :=
          hQ_inter ⟨hyQ, Or.inr hy_πA⟩
        rcases hy_πA₀ with ⟨s₀, hs₀_πA₀, hs₀_eq⟩
        have hs₀_DA₀ : s₀ ∈ D A₀ := by
          rw [c.hJ.π_bar_eq_bd_inter A₀ hA₀] at hs₀_πA₀
          exact (c.hJ.disc_D A₀ hA₀).1.isCompact.isClosed.closure_subset_iff.mpr Subset.rfl hs₀_πA₀.1.1
        rcases hy_ends with rfl | rfl
        · obtain rfl : s₀ = s₁ := c.ιV.injective hs₀_eq
          refine ⟨s₀, ⟨Or.inl rfl, hs₀_DA₀⟩, ?_⟩
          exact hιV'_on_π A₀ hA₀ s₀ hs₀_πA₀
        · obtain rfl : s₀ = s₂ := c.ιV.injective hs₀_eq
          refine ⟨s₀, ⟨Or.inr rfl, hs₀_DA₀⟩, ?_⟩
          exact hιV'_on_π A₀ hA₀ s₀ hs₀_πA₀
      · exact False.elim (hy_AW.2 hyW)
    · rintro ⟨x, ⟨hx_ends, hxD₀⟩, rfl⟩
      have hxD : x ∈ D A ∩ D A₀ := by
        rcases hx_ends with rfl | rfl
        · exact ⟨hs₁_D, hxD₀⟩
        · exact ⟨hs₂_D, hxD₀⟩
      rw [c.hJ.D_inter_eq A hA A₀ hA₀ hne.symm] at hxD
      rw [hιV'_on_π A₀ hA₀ x hxD.2]
      refine ⟨?_, ?_⟩
      · rcases hx_ends with rfl | rfl
        · exact IsGraphPathWithEnds.left_mem hQ_path
        · exact IsGraphPathWithEnds.right_mem hQ_path
      · rcases hxD.2 with ⟨i, rfl⟩
        exact ((c.hJ.π_valid A₀ hA₀).2.2.2 i).1
  have hcompat_Γ'_A : ∀ A₀ ∈ 𝒜, (Γ'.toEmbeddedGraph ιV' ιE').Compatible A₀ :=
    fun A₀ hA₀ => Compatible.of_le_le (hΓ'_le.trans deleteVerts_le) (c.hJ.le_of_mem_𝒜 A₀ hA₀)
  have hGA_eq_union : (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A =
      subgraphUnion (A.deleteVerts W) ((c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A) Q := by
    have hGA_le_Adel : (c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A ≤ A.deleteVerts W := by
      refine ⟨?_, ?_⟩
      · intro x ⟨hxΓ, hxA⟩
        rw [vertexSet_deleteVerts]
        have hx_del := c.hJ.Γ_le.vertexSet_mono hxΓ
        rw [vertexSet_deleteVerts] at hx_del
        exact ⟨hxA, hx_del.2⟩
      · intro e x y hL
        rw [deleteVerts_isLink]
        have hLΓ := hL.mono inf_le_left
        have hx_del := c.hJ.Γ_le.vertexSet_mono hLΓ.left_mem
        have hy_del := c.hJ.Γ_le.vertexSet_mono hLΓ.right_mem
        rw [vertexSet_deleteVerts] at hx_del hy_del
        exact ⟨hL.mono inf_le_right, hx_del.2, hy_del.2⟩
    have hle₁ : (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A ≤ R_G.G.toGraph :=
      inf_le_right.trans (c.hJ.le_of_mem_𝒜 A hA)
    have hle₂ : subgraphUnion (A.deleteVerts W) ((c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A) Q ≤
        R_G.G.toGraph :=
      (subgraphUnion_le hGA_le_Adel hQ_le_Adel).trans
        (deleteVerts_le.trans (c.hJ.le_of_mem_𝒜 A hA))
    refine (Compatible.of_le_le hle₁ hle₂).ext ?_ ?_
    · change (V(Γ'.toEmbeddedGraph ιV' ιE') ∩ V(A)) =
        V((c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A) ∪ V(Q)
      rw [hΓ'_emb, vertexSet_graphUnion, union_inter_distrib_right, vertexSet_inf,
        inter_eq_left.mpr (fun x hx => (hVQ_sub_VA hx).1)]
    · rw [(hcompat_Γ'_A A hA).edgeSet_inf, edgeSet_subgraphUnion hGA_le_Adel hQ_le_Adel,
        (hcompat_Γ_A A hA).edgeSet_inf, hΓ'_emb, edgeSet_graphUnion,
        union_inter_distrib_right, inter_eq_left.mpr hEQ_sub_EA]
  have hΓ'_inter_D : ∀ A₀ ∈ 𝒜,
      (Γ'.interSet (D A₀)).toEmbeddedGraph ιV' ιE' = (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀ := by
    intro A₀ hA₀
    have hD₀_closed : IsClosed (D A₀) := (c.hJ.disc_D A₀ hA₀).1.isCompact.isClosed
    have hsub_inter : (Γ'.interSet (D A₀)).IsSubdrawing Γ' := interSet_isSub
    have hle₁ : (Γ'.interSet (D A₀)).toEmbeddedGraph ιV' ιE' ≤ R_G.G.toGraph :=
      (toEmbeddedGraph_le_of_isSubdrawing hsub_inter ιV' ιE').trans (hΓ'_le.trans deleteVerts_le)
    have hle₂ : (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀ ≤ R_G.G.toGraph :=
      inf_le_right.trans (c.hJ.le_of_mem_𝒜 A₀ hA₀)
    refine (Compatible.of_le_le hle₁ hle₂).ext ?_ ?_
    · change ιV' '' (Γ'.interSet (D A₀)).V = V(Γ'.toEmbeddedGraph ιV' ιE') ∩ V(A₀)
      have hV_inter : (Γ'.interSet (D A₀)).V = (c.Γ.interSet (D A₀)).V ∪ (M.V ∩ D A₀) := by
        ext x
        rw [mem_interSet_V_iff hD₀_closed, mem_union, mem_interSet_V_iff hD₀_closed]
        change x ∈ (c.Γ.V ∪ M.V) ∧ x ∈ D A₀ ↔ (x ∈ c.Γ.V ∧ x ∈ D A₀) ∨ x ∈ M.V ∧ x ∈ D A₀
        rw [mem_union, or_and_right]
      rw [hV_inter, image_union]
      have h1 : ιV' '' (c.Γ.interSet (D A₀)).V = V(c.Γ.toEmbeddedGraph c.ιV c.ιE) ∩ V(A₀) := by
        rw [← vertexSet_inf, ← c.hJ.Γ_inter_D A₀ hA₀]
        change ιV' '' (c.Γ.interSet (D A₀)).V = c.ιV '' (c.Γ.interSet (D A₀)).V
        refine image_congr fun x hx =>
          hιV'_on_ΓV x ((mem_interSet_V_iff hD₀_closed).mp hx).1
      rw [h1, hΓ'_emb, vertexSet_graphUnion, union_inter_distrib_right]
      by_cases hA₀_eq : A₀ = A
      · subst A₀
        have hMV_D : M.V ∩ D A = M.V := inter_eq_left.mpr (hMV_sub_L.trans hL_sub_D)
        have hMV_Q : ιV' '' M.V = V(Q) := by
          rw [← hM_emb_Q]
          rfl
        rw [hMV_D, hMV_Q, inter_eq_left.mpr (fun x hx => (hVQ_sub_VA hx).1)]
      · rw [hVQ_inter_VA_other A₀ hA₀ hA₀_eq]
    · rw [(hcompat_Γ'_A A₀ hA₀).edgeSet_inf]
      change ιE' '' (Γ'.interSet (D A₀)).E = E(Γ'.toEmbeddedGraph ιV' ιE') ∩ E(A₀)
      by_cases hA₀_eq : A₀ = A
      · subst A₀
        have hE_inter : (Γ'.interSet (D A)).E = (c.Γ.interSet (D A)).E ∪ M.E := by
          ext e
          rw [mem_union, GM11.mem_interSet_E_iff, GM11.mem_interSet_E_iff, Drawing.glue_E]
          constructor
          · rintro ⟨heΓ | heM, heD⟩
            · exact Or.inl ⟨heΓ, heD⟩
            · exact Or.inr heM
          · rintro (⟨heΓ, heD⟩ | heM)
            · exact ⟨Or.inl heΓ, heD⟩
            · exact ⟨Or.inr heM, fun z hze => hL_sub_D (hMU ▸ (heM.2.1 hze).1)⟩
        have h1 : ιE' '' (c.Γ.interSet (D A)).E = E(c.Γ.toEmbeddedGraph c.ιV c.ιE) ∩ E(A) := by
          rw [← (hcompat_Γ_A A hA).edgeSet_inf, ← c.hJ.Γ_inter_D A hA]
          change ιE' '' (c.Γ.interSet (D A)).E = c.ιE '' (c.Γ.interSet (D A)).E
          refine image_congr fun e he => hιE'_on_ΓE e (GM11.mem_interSet_E_iff.mp he).1
        have h2 : ιE' '' M.E = E(Q) := by
          rw [← hM_emb_Q]
          rfl
        rw [hE_inter, image_union, h1, h2, hΓ'_emb, edgeSet_graphUnion,
          union_inter_distrib_right, inter_eq_left.mpr hEQ_sub_EA]
      · have hE_inter : (Γ'.interSet (D A₀)).E = (c.Γ.interSet (D A₀)).E := by
          ext e
          rw [GM11.mem_interSet_E_iff, GM11.mem_interSet_E_iff, Drawing.glue_E]
          constructor
          · rintro ⟨heΓ | heM, heD⟩
            · exact ⟨heΓ, heD⟩
            · obtain ⟨z, hze⟩ := heM.1
              have hz_MU : z ∈ M.U \ M.V := heM.2.1 hze
              have hz_L_int : z ∈ L_arc \ {s₁, s₂} := by
                refine ⟨hMU ▸ hz_MU.1, ?_⟩
                rintro (rfl | rfl)
                · exact hz_MU.2 hs₁_MV
                · exact hz_MU.2 hs₂_MV
              exact False.elim (hL_int_not_D_other A₀ hA₀ hA₀_eq z hz_L_int (heD hze))
          · rintro ⟨heΓ, heD⟩
            exact ⟨Or.inl heΓ, heD⟩
        have h1 : ιE' '' (c.Γ.interSet (D A₀)).E = E(c.Γ.toEmbeddedGraph c.ιV c.ιE) ∩ E(A₀) := by
          rw [← (hcompat_Γ_A A₀ hA₀).edgeSet_inf, ← c.hJ.Γ_inter_D A₀ hA₀]
          change ιE' '' (c.Γ.interSet (D A₀)).E = c.ιE '' (c.Γ.interSet (D A₀)).E
          refine image_congr fun e he => hιE'_on_ΓE e (GM11.mem_interSet_E_iff.mp he).1
        have hEQ_disj : E(Q) ∩ E(A₀) = ∅ := by
          rw [← Set.disjoint_iff_inter_eq_empty]
          exact Disjoint.mono_left hEQ_sub_EA (c.hJ.edge_disjoint_𝒜 A hA A₀ hA₀ (Ne.symm hA₀_eq))
        rw [hE_inter, h1, hΓ'_emb, edgeSet_graphUnion, union_inter_distrib_right,
          hEQ_disj, union_empty]
  -- Step 7: Build the new configuration `c'` and contradict `hc_ext.1`.
  have hAK_eq : A ⊓ K = Graph.noEdge W β := by
    by_contra hne
    exact not_le_of_gt hdist_lt (c.hJ.dist_D_of_inter_K A hA hne)
  have hVQ_disj_VK : Disjoint V(Q) V(K) := by
    rw [Set.disjoint_left]
    intro x hxQ hxK
    have hx_AW := hVQ_sub_VA hxQ
    have hx_AK : x ∈ V(A ⊓ K) := ⟨hx_AW.1, hxK⟩
    rw [hAK_eq] at hx_AK
    exact hx_AW.2 hx_AK
  have hN_eq' : N = graphUnion (graphUnion (Γ'.toEmbeddedGraph ιV' ιE') (Graph.noEdge W β))
      (subgraphSUnion R_G.G.toGraph 𝒜) := by
    rw [c.hJ.N_eq]
    have hle_G₁ : graphUnion (graphUnion (c.Γ.toEmbeddedGraph c.ιV c.ιE) (Graph.noEdge W β))
        (subgraphSUnion R_G.G.toGraph 𝒜) ≤ R_G.G.toGraph :=
      graphUnion_le
        (graphUnion_le (c.hJ.Γ_le.trans deleteVerts_le)
          (noEdge_le_iff.mpr (c.hJ.sep_NK.2.trans
            (inter_subset_left.trans c.hJ.sep_NK.1.1.vertexSet_mono))))
        (subgraphSUnion_le c.hJ.le_of_mem_𝒜)
    have hle_G₂ : graphUnion (graphUnion (Γ'.toEmbeddedGraph ιV' ιE') (Graph.noEdge W β))
        (subgraphSUnion R_G.G.toGraph 𝒜) ≤ R_G.G.toGraph :=
      graphUnion_le
        (graphUnion_le (hΓ'_le.trans deleteVerts_le)
          (noEdge_le_iff.mpr (c.hJ.sep_NK.2.trans
            (inter_subset_left.trans c.hJ.sep_NK.1.1.vertexSet_mono))))
        (subgraphSUnion_le c.hJ.le_of_mem_𝒜)
    have hQ_le_U : Q ≤ subgraphSUnion R_G.G.toGraph 𝒜 :=
      (hQ_le_Adel.trans deleteVerts_le).trans
        (le_subgraphSUnion c.hJ.le_of_mem_𝒜 hA)
    refine (Compatible.of_le_le hle_G₁ hle_G₂).ext ?_ ?_
    · change (V(c.Γ.toEmbeddedGraph c.ιV c.ιE) ∪ W) ∪ V(subgraphSUnion R_G.G.toGraph 𝒜) =
        (V(Γ'.toEmbeddedGraph ιV' ιE') ∪ W) ∪ V(subgraphSUnion R_G.G.toGraph 𝒜)
      rw [hΓ'_emb, vertexSet_graphUnion]
      have hVQ_U : V(Q) ⊆ V(subgraphSUnion R_G.G.toGraph 𝒜) := hQ_le_U.vertexSet_mono
      ext x
      simp only [mem_union]
      tauto
    · change (E(c.Γ.toEmbeddedGraph c.ιV c.ιE) ∪ E(Graph.noEdge W β)) ∪
          E(subgraphSUnion R_G.G.toGraph 𝒜) =
        (E(Γ'.toEmbeddedGraph ιV' ιE') ∪ E(Graph.noEdge W β)) ∪
          E(subgraphSUnion R_G.G.toGraph 𝒜)
      rw [hΓ'_emb, edgeSet_graphUnion]
      have hEQ_U : E(Q) ⊆ E(subgraphSUnion R_G.G.toGraph 𝒜) := hQ_le_U.edgeSet_mono
      ext e
      simp only [mem_union]
      tauto
  have hJ' : SystemJ1ToJ6 ιV' ιE' R_G W 𝒜 πLen πS Γ' orient θ c.ord T' c.ins d' D N K Δ
      v_star δ R_H c.φV c.φE :=
    { c.hJ with
      π_valid := fun A₀ hA₀ => by
        refine ⟨(c.hJ.π_valid A₀ hA₀).1, (c.hJ.π_valid A₀ hA₀).2.1,
          (c.hJ.π_valid A₀ hA₀).2.2.1, fun i => ?_⟩
        rw [hιV'_on_π A₀ hA₀ (πS A₀ i) ⟨i, rfl⟩]
        exact (c.hJ.π_valid A₀ hA₀).2.2.2 i
      vertex_inter_𝒜 := fun A₁ hA₁ A₂ hA₂ hne => by
        rw [hπ_img_eq A₁ hA₁, hπ_img_eq A₂ hA₂]
        exact c.hJ.vertex_inter_𝒜 A₁ hA₁ A₂ hA₂ hne
      Γ_le := hΓ'_le
      isTwoCell := h2cell'
      hasMetric := hd'
      ins_spec := fun F hF hNorm' hcard' => by
        have hNorm₀ : c.Γ.IsNormal F := isNormal_of_isSubdrawing hSub hNorm'
        have hcard₀ : (F ∩ c.Γ.V).ncard < c.ord :=
          lt_of_le_of_lt
            (ncard_le_ncard (inter_subset_inter_right F hSub.1)
              (Γ'.finite_V.subset inter_subset_right))
            hcard'
        exact isTangleIns_of_inducedBySubgraph hSub hF hNorm' hcard'
          (c.hJ.ins_spec F hF hNorm₀ hcard₀)
      disc_D := fun A₀ hA₀ =>
        ⟨(c.hJ.disc_D A₀ hA₀).1, hNorm'_bd A₀ hA₀, (c.hJ.disc_D A₀ hA₀).2.2⟩
      Γ_inter_D := hΓ'_inter_D
      π_bar_eq_bd_inter := fun A₀ hA₀ => by
        rw [c.hJ.π_bar_eq_bd_inter A₀ hA₀]
        ext x
        constructor
        · rintro ⟨hxbd, hxV⟩
          refine ⟨hxbd, ?_⟩
          change ιV' x ∈ V(R_G.G.toGraph)
          rw [hιV'_on_bd A₀ hA₀ x hxbd]
          exact hxV
        · rintro ⟨hxbd, hxV'⟩
          refine ⟨hxbd, ?_⟩
          change c.ιV x ∈ V(R_G.G.toGraph)
          rw [← hιV'_on_bd A₀ hA₀ x hxbd]
          exact hxV'
      N_eq := hN_eq'
      disc_Δ := ⟨c.hJ.disc_Δ.1, c.hJ.disc_Δ.2.trans hSub.U_subset⟩
      dist_Γ_inter_K := fun v hv' hvK => by
        rcases hv' with hvΓ | hvM
        · rw [hιV'_on_ΓV v hvΓ] at hvK
          exact (c.hJ.dist_Γ_inter_K v hvΓ hvK).trans (hdist_le {v} (Set.univ \ Δ))
        · have hvQ : ιV' v ∈ V(Q) := by
            rw [← hM_emb_Q]
            exact ⟨v, hvM, rfl⟩
          exact False.elim (Set.disjoint_left.mp hVQ_disj_VK hvQ hvK)
      dist_D_of_inter_K := fun A₀ hA₀ hne =>
        (c.hJ.dist_D_of_inter_K A₀ hA₀ hne).trans (hdist_le (D A₀) (Set.univ \ Δ))
      v_star_mem := ⟨hSub.1 c.hJ.v_star_mem.1, c.hJ.v_star_mem.2⟩ }
  have hJ7' : ConditionJ7 ιV' ιE' R_G.G.toGraph W 𝒜 πLen πS Γ' T' :=
    { path_in_A := fun A₀ hA₀ u hu v hv => by
        rw [hπ_img_eq A₀ hA₀] at hu hv ⊢
        exact c.hJ7.path_in_A A₀ hA₀ u hu v hv
      no_small_sep := fun A₀ hA₀ ⟨C, D_sep, C_Γ', D_Γ', hSep, hOrd, hA₀_le,
          hCV', hCE', hDV', hDE', hmemT'⟩ => by
        have hmemT : (C_Γ' ∩ c.Γ.toHypergraph, D_Γ' ∩ c.Γ.toHypergraph) ∈ c.T := hmemT'.2.2
        refine c.hJ7.no_small_sep A₀ hA₀
          ⟨C, D_sep, C_Γ' ∩ c.Γ.toHypergraph, D_Γ' ∩ c.Γ.toHypergraph, hSep, hOrd, hA₀_le,
            ?_, ?_, ?_, ?_, hmemT⟩
        · change C_Γ'.vertexSet ∩ c.Γ.V = c.ιV ⁻¹' V(C) ∩ c.Γ.V
          rw [hCV', Set.inter_assoc, inter_eq_right.mpr hSub.1]
          ext x
          exact ⟨fun ⟨hxC, hxV⟩ => ⟨by rw [mem_preimage, ← hιV'_on_ΓV x hxV]; exact hxC, hxV⟩,
            fun ⟨hxC, hxV⟩ => ⟨by rw [mem_preimage, hιV'_on_ΓV x hxV]; exact hxC, hxV⟩⟩
        · change C_Γ'.edgeSet ∩ c.Γ.E = c.ιE ⁻¹' E(C) ∩ c.Γ.E
          rw [hCE', Set.inter_assoc, inter_eq_right.mpr hSub.2]
          ext e
          exact ⟨fun ⟨heC, heE⟩ => ⟨by rw [mem_preimage, ← hιE'_on_ΓE e heE]; exact heC, heE⟩,
            fun ⟨heC, heE⟩ => ⟨by rw [mem_preimage, hιE'_on_ΓE e heE]; exact heC, heE⟩⟩
        · change D_Γ'.vertexSet ∩ c.Γ.V = c.ιV ⁻¹' V(D_sep) ∩ c.Γ.V
          rw [hDV', Set.inter_assoc, inter_eq_right.mpr hSub.1]
          ext x
          exact ⟨fun ⟨hxD, hxV⟩ => ⟨by rw [mem_preimage, ← hιV'_on_ΓV x hxV]; exact hxD, hxV⟩,
            fun ⟨hxD, hxV⟩ => ⟨by rw [mem_preimage, hιV'_on_ΓV x hxV]; exact hxD, hxV⟩⟩
        · change D_Γ'.edgeSet ∩ c.Γ.E = c.ιE ⁻¹' E(D_sep) ∩ c.Γ.E
          rw [hDE', Set.inter_assoc, inter_eq_right.mpr hSub.2]
          ext e
          exact ⟨fun ⟨heD, heE⟩ => ⟨by rw [mem_preimage, ← hιE'_on_ΓE e heE]; exact heD, heE⟩,
            fun ⟨heD, heE⟩ => ⟨by rw [mem_preimage, hιE'_on_ΓE e heE]; exact heD, heE⟩⟩
      structure_Γ_inter_A := fun A₀ hA₀ => by
        by_cases hA₀_eq : A₀ = A
        · subst A₀
          have hV'_sub : c.Γ.V ∪ {s₁, s₂} ⊆ Γ'.V := by
            refine union_subset hSub.1 ?_
            rintro x (rfl | rfl)
            · exact Or.inr hs₁_MV
            · exact Or.inr hs₂_MV
          have hres := hQ_J7 Γ' ιV' ιE' (hιV'_on_π A hA) hV'_sub hGA_eq_union
          dsimp only at hres ⊢
          rw [hπ_img_eq A hA]
          exact hres
        · have hsub_GA₀ : (c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A₀ ≤
              (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀ := by
            rw [← hΓ_emb_eq]
            exact inf_le_inf_right A₀ (toEmbeddedGraph_le_of_isSubdrawing hSub ιV' ιE')
          have hV_sub_GA₀ : V((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀) ⊆
              V((c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A₀) ∪ (ιV' '' Set.range (πS A₀)) := by
            change V(Γ'.toEmbeddedGraph ιV' ιE') ∩ V(A₀) ⊆
              (V(c.Γ.toEmbeddedGraph c.ιV c.ιE) ∩ V(A₀)) ∪ (ιV' '' Set.range (πS A₀))
            rw [hΓ'_emb, vertexSet_graphUnion, union_inter_distrib_right,
              hVQ_inter_VA_other A₀ hA₀ hA₀_eq, hMV_inter_D_other A₀ hA₀ hA₀_eq]
            refine union_subset subset_union_left ( subset_trans ?_ subset_union_right)
            refine image_mono ?_
            rintro x ⟨rfl | rfl, hxD₀⟩
            · have hx_inter : x ∈ D A ∩ D A₀ := ⟨hs₁_D, hxD₀⟩
              rw [c.hJ.D_inter_eq A hA A₀ hA₀ (Ne.symm hA₀_eq)] at hx_inter
              exact hx_inter.2
            · have hx_inter : x ∈ D A ∩ D A₀ := ⟨hs₂_D, hxD₀⟩
              rw [c.hJ.D_inter_eq A hA A₀ hA₀ (Ne.symm hA₀_eq)] at hx_inter
              exact hx_inter.2
          have hE_eq_GA₀ : E((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀) =
              E((c.Γ.toEmbeddedGraph c.ιV c.ιE) ⊓ A₀) := by
            rw [(hcompat_Γ'_A A₀ hA₀).edgeSet_inf, (hcompat_Γ_A A₀ hA₀).edgeSet_inf,
              hΓ'_emb, edgeSet_graphUnion, union_inter_distrib_right]
            have hEQ_disj : E(Q) ∩ E(A₀) = ∅ := by
              rw [← Set.disjoint_iff_inter_eq_empty]
              exact Disjoint.mono_left hEQ_sub_EA
                (c.hJ.edge_disjoint_𝒜 A hA A₀ hA₀ (Ne.symm hA₀_eq))
            rw [hEQ_disj, union_empty]
          exact structure_Γ_inter_A_of_sub_πBar c.hJ c.hJ7 hSub.1 hA₀
            (hιV'_on_π A₀ hA₀) hsub_GA₀ hV_sub_GA₀ hE_eq_GA₀ }
  let c' : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam' :=
    { c with
      ιV := ιV'
      ιE := ιE'
      Γ := Γ'
      T := T'
      d := d'
      ιV_eq := fun x hx => by
        rcases hx with rfl | ⟨A₀, hA₀, hxπ⟩
        · rw [hιV'_on_ΓV x c.hJ.v_star_mem.1]
          exact c.ιV_eq x (Or.inl rfl)
        · rw [hιV'_on_π A₀ hA₀ x hxπ]
          exact c.ιV_eq x (Or.inr ⟨A₀, hA₀, hxπ⟩)
      hJ := hJ'
      hJ7 := hJ7'
      hdist_other := fun A₀ hA₀ =>
        (c.hdist_other A₀ hA₀).trans (hdist_le (D A₀) (Set.univ \ Δ))
      h_iii_dist := fun i =>
        (c.h_iii_dist i).trans (hdist_le {v_star} (D (A_fam' i)))
      h_iv := fun i j hij =>
        (c.h_iv i j hij).trans (hdist_le (D (A_fam' i)) (D (A_fam' j))) }
  have hcard_le : Γ'.E.ncard ≤ c.Γ.E.ncard := hc_ext.1 c'
  have hΓ'_E_fin : Γ'.E.Finite := by
    have hsub_G : ιE' '' Γ'.E ⊆ E(R_G.G.toGraph) :=
      (hΓ'_le.trans Graph.deleteVerts_le).edgeSet_mono
    exact (c.hJ.finite_E.subset hsub_G).of_finite_image ιE'.injective.injOn
  rcases hME_ne with ⟨e₀, he₀M⟩
  have he₀_not_Γ : e₀ ∉ c.Γ.E := Set.disjoint_right.mp hE_disj he₀M
  have he₀_Γ' : e₀ ∈ Γ'.E := by
    rw [Drawing.glue_E]
    exact Or.inr he₀M
  have hssub : c.Γ.E ⊂ Γ'.E :=
    ⟨hSub.2, fun h => he₀_not_Γ (h he₀_Γ')⟩
  exact not_lt_of_ge hcard_le (Set.ncard_lt_ncard hssub hΓ'_E_fin)

/-! ## 4. Proof of Claim (4) of Theorem 7.4 (page 554) -/

/-- **Graph Minors XXII, (7.4) Claim (4)** (page 554):
"(4) *Every $A \in \mathcal{A}$ with $d(D(A), \Sigma \setminus \Delta) < \theta$ is good.*" -/
theorem lemma_7_4_claim_4
    {q : ℕ}
    {ιV₀ : S ↪ α} {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 ℬ : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {orient : GM19.SurfaceOrientation S} {θ : ℕ}
    {D : Graph α β → Set S} {N K : Graph α β} {Δ : Set S} {v_star : S} {δ : ℕ}
    {R_H : RootedDigraph αH βH q} {t : ℕ} {A_fam A_fam' : Fin t → Graph α β}
    (c : ValidConfig74 ιV₀ R_G W 𝒜 ℬ πLen πS orient θ D N K Δ v_star δ R_H t A_fam A_fam')
    (hc_ext : c.IsExtremal)
    {A : Graph α β} (hA : A ∈ 𝒜)
    (hdist : subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) < θ) :
    IsGoodMember c.ιV c.ιE c.Γ πLen πS A := by
  by_contra hNotGood
  have hBad : IsBadMember c.ιV c.ιE c.Γ πLen πS A := hNotGood
  have hDisj : Disjoint (D A) c.Γ.U :=
    (lemma_7_4_claim_2 c hc_ext hA hBad).resolve_left (not_le_of_gt hdist)
  have hDA_disc : IsClosedDisc (D A) := (c.hJ.disc_D A hA).1
  obtain ⟨x₀, hx₀⟩ := GM14.IsClosedDisc.nonempty hDA_disc
  have hx₀_not_U : x₀ ∉ c.Γ.U := Set.disjoint_left.mp hDisj hx₀
  obtain ⟨r, hr, hx₀r⟩ := GM11.exists_region_of_notMem hx₀_not_U
  have hDA_sub_r : D A ⊆ r :=
    GM11.subset_region hr (GM14.IsClosedDisc.isPreconnected hDA_disc) hDisj hx₀ hx₀r
  let 𝒞 : Set (Graph α β) := {A' ∈ 𝒜 | D A' ⊆ r}
  have hA_𝒞 : A ∈ 𝒞 := ⟨hA, hDA_sub_r⟩
  refine no_isolated_disc_cluster c.hJ c.hJ7 (fun _ h => h.1) hA_𝒞 hdist hr (fun _ h => h.2) ?_
  intro A' hA' A'' hA''
  rw [Set.disjoint_left]
  intro s hsA' hsA''
  have hne : A' ≠ A'' := fun heq => hA''.2 (heq ▸ hA')
  have hs_inter : s ∈ D A' ∩ D A'' := ⟨hsA', hsA''⟩
  rw [c.hJ.D_inter_eq A' hA'.1 A'' hA''.1 hne] at hs_inter
  have hs_r : s ∈ r := hA'.2 hsA'
  have hs_not_U : s ∉ c.Γ.U := fun hsU => GM11.region_subset hr hs_r hsU
  have hs_not_V : s ∉ c.Γ.V := fun hsV => hs_not_U (c.Γ.V_subset_U hsV)
  have hBad'' : IsBadMember c.ιV c.ιE c.Γ πLen πS A'' :=
    fun hGood'' => hs_not_V (hGood''.1 hs_inter.2)
  have hdist_le_A : subsetTangleDist c.Γ c.ord c.d (D A'') (Set.univ \ Δ) ≤
      subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) := by
    have h1 : subsetTangleDist c.Γ c.ord c.d {s} (Set.univ \ Δ) =
        subsetTangleDist c.Γ c.ord c.d (D A) (Set.univ \ Δ) :=
      subsetTangleDist_eq_of_subset_region hr (singleton_subset_iff.mpr hs_r)
        (singleton_nonempty s) hDA_sub_r ⟨x₀, hx₀⟩ (Set.univ \ Δ)
    have h2 : subsetTangleDist c.Γ c.ord c.d (D A'') (Set.univ \ Δ) ≤
        subsetTangleDist c.Γ c.ord c.d {s} (Set.univ \ Δ) :=
      subsetTangleDist_anti (fun a ha b hb => HasTangleMetric.le_ord c.hJ.hasMetric ha hb)
        (singleton_subset_iff.mpr hsA'') Subset.rfl
    exact h2.trans_eq h1
  have hdist''_lt : subsetTangleDist c.Γ c.ord c.d (D A'') (Set.univ \ Δ) < θ :=
    lt_of_le_of_lt hdist_le_A hdist
  have hDisj'' : Disjoint (D A'') c.Γ.U :=
    (lemma_7_4_claim_2 c hc_ext hA''.1 hBad'').resolve_left (not_le_of_gt hdist''_lt)
  have hDA''_sub_r : D A'' ⊆ r :=
    GM11.subset_region hr (GM14.IsClosedDisc.isPreconnected (c.hJ.disc_D A'' hA''.1).1)
      hDisj'' hsA'' hs_r
  exact hA''.2 ⟨hA''.1, hDA''_sub_r⟩

end GraphMinor.GM22
