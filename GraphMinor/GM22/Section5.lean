module

public import GraphMinor.GM22.Section4Sleeve
public import GraphMinor.GM22.Section5Menger
public import GraphMinor.GM14.Section9a
public import GraphMinor.GM14.Section7a
public import GraphMinor.GM14.Section5
public import GraphMinor.GM12.Section2Simple
public import GraphMinor.GM12.Section2TangleTraceExistence
public import GraphMinor.GM12.Section2CurveCounts
public import GraphMinor.GM12.Section3ShortTrace
public import GraphMinor.GM12.Section4WalkMetric
public import GraphMinor.GM07.CylinderPaths
public import GraphMinor.GM07.CuffGrid
public import GraphMinor.Surface.RemoveDiscs

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 5: Tangles

This file formalizes Section 5 (pages 539–542) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563:

- **5.1** (`theorem_5_1`, page 539)
- **5.2** (`theorem_5_2`, page 540, with Claim (1) `lemma_5_2_claim_1`)
- **5.3** (`theorem_5_3`, pages 540–542, with Claims (1)–(7))
-/

@[expose] public section

set_option linter.deprecated false

namespace GraphMinor.GM22

open Set Function Topology Classical Graph
  GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14
  Hypergraph

universe u v w

/-! ## 1. Theorem 5.1 (page 539) -/

/-- Stronger internal form of **5.1** (Graph Minors XXII, page 539), returning both the open disc
`Λ` (`(κ + 2)`-zone around `z`) and the bounding circuit `C` of `Γ` with `Δ = closure Λ` and
`subBd Δ = C.U`. -/
theorem lemma_5_1_full {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (Γ : Surface.Drawing S) (ord κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S)
    (hMetric : HasTangleMetric Γ ord T d) (hz : z ∈ Γ.A)
    (hκ2 : 2 ≤ κ) (hκ_ord : κ + 3 ≤ ord) :
    ∃ (C : Surface.Drawing S) (Λ Δ : Set S),
      Δ = closure Λ ∧
      C.IsSubdrawing Γ ∧ C.IsCircuit ∧
      IsClosedDisc Δ ∧
      subBd Λ = C.U ∧ subBd Δ = C.U ∧ Δ \ subBd Δ = Λ ∧
      IsLambdaZoneAround Γ d (κ + 2) z Λ ∧
      subBd Δ ⊆ Γ.U ∧
      (∀ x ∈ Γ.A, (x ∩ Δ).Nonempty → x ⊆ Δ ∧ d z x ≤ κ + 2) ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → κ ≤ d z x) ∧
      z ⊆ Δ \ subBd Δ := by
  have : ConnectedSpace S := hConn
  obtain ⟨C, Λ, hCΓ, hC, hbdΛ, hbd_cl, hdiff, hZone, hx_sub⟩ :=
    GM14.full_of_9_2 hS hConn Γ ord κ T d z hMetric hz hκ2 hκ_ord
  refine ⟨C, Λ, closure Λ, rfl, hCΓ, hC, hZone.isClosedDisc_closure,
    hbdΛ, hbd_cl, hbd_cl.symm ▸ hdiff, hZone, hbd_cl ▸ hCΓ.U_subset, ?_, ?_, ?_⟩
  · intro x hx hne
    have hx_cl : x ⊆ closure Λ :=
      GM14.atom_subset_closure_of_inter_nonempty hS hCΓ hZone.isClosedDisc_closure
        hbd_cl hdiff hx hne
    exact ⟨hx_cl, hZone.dist_le x hx hx_cl⟩
  · intro x hx hnot
    by_contra hlt
    push Not at hlt
    have hxΛ : x ⊆ Λ := hx_sub x hx hlt
    rw [hbd_cl, hdiff] at hnot
    exact hnot hxΛ
  · rw [hbd_cl, hdiff]
    exact hZone.z_subset

/-- **5.1** (Graph Minors XXII, page 539):
"Let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with $\text{bd}(\Sigma) = \emptyset$, and
let $\mathcal{T}$ be a respectful tangle in $\Gamma$, with metric $d$. Let $z \in A(H)$, and
let $\kappa$ be an integer with $2 \le \kappa \le \text{ord}(\mathcal{T}) - 3$. Then there is a
closed disc $\Delta \subseteq \Sigma$ satisfying
(i) $\text{bd}(\Delta) \subseteq U(\Gamma)$,
(ii) $d(z, x) \le \kappa + 2$ for all $x \in A(\Gamma)$ with $x \cap \Delta \ne \emptyset$,
(iii) $d(z, x) \ge \kappa$ for all $x \in A(\Gamma)$ with
$x \nsubseteq \Delta \setminus \text{bd}(\Delta)$ (and in particular,
$z \subseteq \Delta \setminus \text{bd}(\Delta)$)."
The print has "$z \in A(H)$", a misprint for $z \in A(\Gamma)$: no $H$ is defined there, and
$d(z, x)$ needs $z$ to be an atom of $\Gamma$. The Lean takes $z \in A(\Gamma)$. See the correction
on page 539 in `corrections/GM22.md`. -/
theorem theorem_5_1_proof {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (Γ : Surface.Drawing S) (ord κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S)
    (hMetric : HasTangleMetric Γ ord T d) (hz : z ∈ Γ.A)
    (hκ2 : 2 ≤ κ) (hκ_ord : κ + 3 ≤ ord) :
    ∃ Δ : Set S,
      IsClosedDisc Δ ∧
      subBd Δ ⊆ Γ.U ∧
      (∀ x ∈ Γ.A, (x ∩ Δ).Nonempty → d z x ≤ κ + 2) ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → κ ≤ d z x) ∧
      z ⊆ Δ \ subBd Δ := by
  obtain ⟨_, _, Δ, _, _, _, hΔ, _, _, _, _, hbdU, h_ii, h_iii, hz_sub⟩ :=
    lemma_5_1_full hS hConn Γ ord κ T d z hMetric hz hκ2 hκ_ord
  exact ⟨Δ, hΔ, hbdU, fun x hx hne => (h_ii x hx hne).2, h_iii, hz_sub⟩

/-! ## 2. Theorem 5.2 (page 540) -/

/-- If `z ∈ A(Γ)` and `r ∈ R(Γ)` satisfy `(closure r ∩ z).Nonempty`, then `d(z, r) ≤ 2` and
`d(r, z) ≤ 2`. -/
private theorem dist_atom_region_le_two {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric Γ ord T d) (hord : 2 ≤ ord)
    {z r : Set S} (hz : z ∈ Γ.A) (hr : r ∈ Γ.R) (hne : (closure r ∩ z).Nonempty) :
    d z r ≤ 2 ∧ d r z ≤ 2 := by
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have hrefl := h91_prop.2.1
  have hsymm := h91_prop.2.2.2.1
  have hv_reg := h91_prop.2.2.2.2.2.1
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hE : Γ.E.Nonempty := GM14.edgeSet_nonempty_of_isTangle hResp.2.1 hord
  have hrA : r ∈ Γ.A := Or.inr hr
  obtain ⟨p, hpr, hpz⟩ := hne
  obtain ⟨z', hz', -⟩ := GM14.existsUnique_correspondingAtom hK hz
  have hzr : d z r ≤ 2 := by
    rcases hz'.2.2 with ⟨v, hv, rfl, rfl⟩ | ⟨he, hr', her'⟩ | ⟨hzR, v, ⟨-, hcz⟩, rfl⟩
    · have hpv : p = v := mem_singleton_iff.mp hpz
      have hvr : d {v} r ≤ 1 := hv_reg hE v hv r hr (hpv ▸ hpr)
      omega
    · obtain ⟨q, hqr', hqr⟩ := mem_closure_iff.mp hpr z' (region_isOpen hr') (her' hpz)
      have hrz : d r z ≤ 2 := by
        rw [hd_eq r hrA z hz]
        exact GM14.tangleMetric_region_edge_le hS hResp hK hd hr he hr' her' ⟨q, hqr, hqr'⟩
      rw [hsymm z hz r hrA]
      exact hrz
    · obtain ⟨q, hqz, hqr⟩ := mem_closure_iff.mp hpr z (region_isOpen hzR) hpz
      have hrz_eq : r = z := region_eq_of_mem hr hzR hqr hqz
      subst hrz_eq
      rw [hrefl r hrA]
      omega
  exact ⟨hzr, hsymm r hrA z hz ▸ hzr⟩

/-- If `r₁, r₂ ∈ R(Γ)` satisfy `(closure r₁ ∩ closure r₂).Nonempty`, then `d(r₁, r₂) ≤ 2`. -/
private theorem dist_region_region_le_two {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric Γ ord T d) (hord : 2 ≤ ord)
    {r₁ r₂ : Set S} (hr₁ : r₁ ∈ Γ.R) (hr₂ : r₂ ∈ Γ.R)
    (hne : (closure r₁ ∩ closure r₂).Nonempty) :
    d r₁ r₂ ≤ 2 := by
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have hrefl := h91_prop.2.1
  have hsymm := h91_prop.2.2.2.1
  have htri := h91_prop.2.2.2.2.1
  have hv_reg := h91_prop.2.2.2.2.2.1
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hP := hK.2.1
  have hE : Γ.E.Nonempty := GM14.edgeSet_nonempty_of_isTangle hResp.2.1 hord
  have hr₁A : r₁ ∈ Γ.A := Or.inr hr₁
  have hr₂A : r₂ ∈ Γ.A := Or.inr hr₂
  obtain ⟨p, hpr₁, hpr₂⟩ := hne
  obtain ⟨a, haA, hpa⟩ := GM14.exists_atom_mem_of_point Γ p
  obtain ⟨a', ha', -⟩ := GM14.existsUnique_correspondingAtom hK haA
  rcases ha'.2.2 with ⟨v, hv, rfl, rfl⟩ | ⟨he, hr', her'⟩ | ⟨haR, v, ⟨-, -⟩, rfl⟩
  · have hpv : p = v := mem_singleton_iff.mp hpa
    have hv₁ : d {v} r₁ ≤ 1 := hv_reg hE v hv r₁ hr₁ (hpv ▸ hpr₁)
    have hv₂ : d {v} r₂ ≤ 1 := hv_reg hE v hv r₂ hr₂ (hpv ▸ hpr₂)
    have hr₁v : d r₁ {v} ≤ 1 := by
      rw [hsymm r₁ hr₁A {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩))]
      exact hv₁
    have htri' := htri r₁ hr₁A {v} (Or.inl (Or.inl ⟨v, hv, rfl⟩)) r₂ hr₂A
    omega
  · by_cases hθ : ord ≤ 2
    · rw [hd_eq r₁ hr₁A r₂ hr₂A]
      exact (GM11.tangleMetric_le_order hP r₁ r₂).trans hθ
    push Not at hθ
    obtain ⟨q₁, hq₁r', hq₁r₁⟩ := mem_closure_iff.mp hpr₁ a' (region_isOpen hr') (her' hpa)
    obtain ⟨q₂, hq₂r', hq₂r₂⟩ := mem_closure_iff.mp hpr₂ a' (region_isOpen hr') (her' hpa)
    have hT := hResp.2.1
    have heG : a ∈ Γ.toHypergraph.edgeSet := he
    have hsep := GM10.isSeparation_edgeHypergraph_deleteEdges heG
    obtain ⟨u₀, v₀, hl⟩ := (Γ.toGraph.edge_mem_iff_exists_isLink a).mp he
    have hends : Γ.toHypergraph.ends a ⊆ {u₀, v₀} := fun w hw => by
      rw [← hl.2.2.2]
      exact ⟨hw.2.2, hw.2.1⟩
    have hefin : (Γ.toHypergraph.ends a).Finite := (toFinite ({u₀, v₀} : Set S)).subset hends
    have h2 : (Γ.toHypergraph.ends a).ncard ≤ 2 :=
      (ncard_le_ncard hends (toFinite _)).trans ((ncard_insert_le u₀ {v₀}).trans (by simp))
    have hord_sep : Hypergraph.separationOrder (GM10.edgeHypergraph Γ.toHypergraph a)
        (Γ.toHypergraph.deleteEdges {a}) < ord := by
      rw [GM10.separationOrder_edgeHypergraph_deleteEdges]
      change (Γ.toHypergraph.ends a).ncard < ord
      omega
    have hAB : (GM10.edgeHypergraph Γ.toHypergraph a, Γ.toHypergraph.deleteEdges {a}) ∈ T :=
      (hT.axiom1 hsep hord_sep).resolve_right fun h => hT.axiom3 h rfl
    obtain ⟨D, hD, hDs, hDl, hDV, heD⟩ := GM14.theorem_7_2_proof hS ‹_› ⟨a, he⟩ hResp hK hd hAB rfl
    have hpre : IsPretangle (PaintingOrDrawing.drawing Γ).toHypergraph ord T :=
      GM10.IsTangle.isPretangle hT
    have hs := GM11.isSlope_of_derived hS hpre hP.1 hd
    obtain ⟨-, -, hnice⟩ := GM11.ins_slope_facts hS hs hD hDs hDl
    have hcl : IsClosed (ins D) := (hs.isClosedDisc D hD hDs hDl).isCompact.isClosed
    obtain ⟨u, W₀, hW₀, -, hV, hE_D⟩ := id hD
    obtain ⟨W, hsu, hed⟩ := hDs.exists_walk_up W₀
    have hDeq := (GM12.circuit_length_eq_two_mul_ncard hP hD hDs).1
    have hWlen : W.length = D.length := by
      rw [Surface.Drawing.length, hE_D, ← hed]
      have h : {f | f ∈ W.edges} = (W.edges.toFinset : Set (Set S)) := by ext; simp
      rw [h, ncard_coe_finset, List.toFinset_card_of_nodup (hed ▸ hW₀.2)]
      rfl
    have hDV_ends : D.V ∩ Γ.V ⊆ Γ.toHypergraph.ends a := fun x hx => (hDV hx).1
    have hncard_le : (D.V ∩ Γ.V).ncard ≤ 2 :=
      (ncard_le_ncard hDV_ends hefin).trans h2
    set n := (D.V ∩ Γ.V).ncard
    have hsub : D.IsSubdrawing (walkDrawing K W) := by
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · rw [walkDrawing_V, hsu]
        rw [hV] at hx
        exact hx
      · rw [walkDrawing_E, hed]
        rw [hE_D] at hf
        exact hf
    have hins : ins D ⊆ insWalk ins K W := fun x hx =>
      Or.inr (mem_iUnion₂.mpr ⟨D, ⟨hD, hsub⟩, hx⟩)
    obtain ⟨y, hy⟩ := he.1
    have hr'D : a' ⊆ ins D := GM11.nice_atom hnice (Or.inr hr') ⟨y, her' hy, heD hy⟩
    obtain ⟨w₁, ⟨hw₁r₁, hw₁V⟩, -⟩ := hP.2.2.1 r₁ hr₁
    obtain ⟨w₂, ⟨hw₂r₂, hw₂V⟩, -⟩ := hP.2.2.1 r₂ hr₂
    have hw₁_cl : w₁ ∈ closure a' :=
      GM14.hub_mem_closure_of_inter_nonempty hS hK hr₁ hr' ⟨q₁, hq₁r₁, hq₁r'⟩ ⟨hw₁V, hw₁r₁⟩
    have hw₂_cl : w₂ ∈ closure a' :=
      GM14.hub_mem_closure_of_inter_nonempty hS hK hr₂ hr' ⟨q₂, hq₂r₂, hq₂r'⟩ ⟨hw₂V, hw₂r₂⟩
    have hwit : GM11.MetricWitness Γ K ins ord r₁ r₂ n := by
      refine ⟨u, W, {w₁}, {w₂}, ?_, ?_, by omega, by omega, ?_, ?_⟩
      · exact ⟨hr₁A, Or.inl (Or.inl ⟨w₁, hw₁V, rfl⟩),
          Or.inr (Or.inr ⟨hr₁, w₁, ⟨hw₁V, hw₁r₁⟩, rfl⟩)⟩
      · exact ⟨hr₂A, Or.inl (Or.inl ⟨w₂, hw₂V, rfl⟩),
          Or.inr (Or.inr ⟨hr₂, w₂, ⟨hw₂V, hw₂r₂⟩, rfl⟩)⟩
      · rw [singleton_subset_iff]
        exact hins (closure_minimal hr'D hcl hw₁_cl)
      · rw [singleton_subset_iff]
        exact hins (closure_minimal hr'D hcl hw₂_cl)
    rw [hd_eq r₁ hr₁A r₂ hr₂A]
    exact (GM11.tangleMetric_le hwit).trans hncard_le
  · obtain ⟨q₁, hq₁a, hq₁r₁⟩ := mem_closure_iff.mp hpr₁ a (region_isOpen haR) hpa
    obtain ⟨q₂, hq₂a, hq₂r₂⟩ := mem_closure_iff.mp hpr₂ a (region_isOpen haR) hpa
    have hr₁_eq : r₁ = a := region_eq_of_mem hr₁ haR hq₁r₁ hq₁a
    have hr₂_eq : r₂ = a := region_eq_of_mem hr₂ haR hq₂r₂ hq₂a
    rw [hr₁_eq, hr₂_eq, hrefl a haA]
    omega

/-- **5.2, Claim (1)** (Graph Minors XXII, page 540):
"(1) If $r_1, \ldots, r_t$ is a sequence of regions of $\Gamma$ with $z \subseteq \bar{r}_1$,
$\bar{r}_t \cap \text{bd}(\Delta) \ne \emptyset$, and $\bar{r}_i \cap \bar{r}_{i+1} \ne \emptyset$
for $1 \le i < t$, then $t \ge h$."
We state this more generally assuming only $(\bar{r}_1 \cap z) \ne \emptyset$ (which follows from
$z \subseteq \bar{r}_1$ since $z$ is non-empty). -/
theorem lemma_5_2_claim_1 {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord h t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Δ : Set S}
    (hMetric : HasTangleMetric Γ ord T d) (hord : 2 * h + 5 ≤ ord)
    (hz : z ∈ Γ.A) (_hz_sub : z ⊆ Δ \ subBd Δ)
    (hΔ_iii : ∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → 2 * h + 2 ≤ d z x)
    (ht_pos : 0 < t) (r : Fin t → Set S)
    (hr : ∀ i : Fin t, r i ∈ Γ.R)
    (hr0 : (closure (r ⟨0, ht_pos⟩) ∩ z).Nonempty)
    (hrt : (closure (r ⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩) ∩ subBd Δ).Nonempty)
    (hstep : ∀ (i : Fin t) (hi : i.1 + 1 < t),
      (closure (r i) ∩ closure (r ⟨i.1 + 1, hi⟩)).Nonempty) :
    h ≤ t := by
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have htri := h91_prop.2.2.2.2.1
  have hord2 : 2 ≤ ord := by omega
  have hd_le : ∀ (k : ℕ) (hk : k < t), d z (r ⟨k, hk⟩) ≤ 2 * k + 2 := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa using (dist_atom_region_le_two hS hConn hMetric hord2 hz (hr ⟨0, hk⟩) hr0).1
    | succ k ih =>
      intro hk
      have hk' : k < t := Nat.lt_of_succ_lt hk
      have h_ih := ih hk'
      have h_adj : d (r ⟨k, hk'⟩) (r ⟨k + 1, hk⟩) ≤ 2 :=
        dist_region_region_le_two hS hConn hMetric hord2
          (hr ⟨k, hk'⟩) (hr ⟨k + 1, hk⟩) (hstep ⟨k, hk'⟩ hk)
      have htri' := htri z hz (r ⟨k, hk'⟩) (Or.inr (hr ⟨k, hk'⟩))
        (r ⟨k + 1, hk⟩) (Or.inr (hr ⟨k + 1, hk⟩))
      omega
  obtain ⟨p, hpr_last, hp_bd⟩ := hrt
  obtain ⟨z', hz'A, hpz'⟩ := GM14.exists_atom_mem_of_point Γ p
  have hlast_z' : d (r ⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩) z' ≤ 2 :=
    (dist_atom_region_le_two hS hConn hMetric hord2 hz'A
      (hr ⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩) ⟨p, hpr_last, hpz'⟩).2
  have hz'_not_sub : ¬ (z' ⊆ Δ \ subBd Δ) := fun hsub => (hsub hpz').2 hp_bd
  have hge : 2 * h + 2 ≤ d z z' := hΔ_iii z' hz'A hz'_not_sub
  have hd_last := hd_le (t - 1) (Nat.sub_lt ht_pos zero_lt_one)
  have htri_end := htri z hz (r ⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩)
    (Or.inr (hr ⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩)) z' hz'A
  omega

/-- **5.2** (Graph Minors XXII, page 540):
"Let $h \ge 1$ be an integer, let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathcal{T}$ be a respectful tangle in $\Gamma$ of order
$\ge 2h + 5$, with metric $d$. Let $x \in \Sigma$, and let $Y$ be the union of all atoms
$y \in A(\Gamma)$ with $d(y, z) \ge 2h + 5$, where $z$ is the atom of $\Gamma$ with $x \in z$. Then
$x$ is $h$-insulated from $Y$ by $\Gamma$." -/
theorem theorem_5_2_proof {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    (Γ : Surface.Drawing S) (ord h : ℕ) (hh : 1 ≤ h)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (hMetric : HasTangleMetric Γ ord T d) (hord : 2 * h + 5 ≤ ord)
    (x : S) (z Y : Set S) (hz : z ∈ Γ.A) (hxz : x ∈ z)
    (hY : Y ⊆ ⋃ y ∈ {y ∈ Γ.A | 2 * h + 5 ≤ d y z}, y) :
    IsInsulated Γ Y h x := by
  have : ConnectedSpace S := hConn
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have hsymm := h91_prop.2.2.2.1
  obtain ⟨_, _, Δ, _, _, _, hΔ_disc, _, _, _, _, hbdU, h_ii, h_iii, hz_sub⟩ :=
    lemma_5_1_full hS hConn Γ ord (2 * h + 2) T d z hMetric hz (by omega) (by omega)
  have hreg_dist : (h - 1) + 1 ≤ regionalDistance Γ z (subBd Δ) := by
    obtain ⟨f⟩ := hΔ_disc.isOArc_discBd
    have hbd_ne : (subBd Δ).Nonempty := by
      rw [IsClosedDisc.subBd_eq_discBd hS hΔ_disc]
      exact ⟨(f 1).1, (f 1).2⟩
    obtain ⟨v_seq, r_seq, hchain⟩ := GM14.regionalDistance_spec hS Γ ⟨x, hxz⟩ hbd_ne
    generalize ht : regionalDistance Γ z (subBd Δ) = t at v_seq r_seq hchain ⊢
    rcases Nat.eq_zero_or_pos t with rfl | ht_pos
    · exfalso
      exact (hz_sub hchain.1).2 hchain.2.1
    · have hr : ∀ i : Fin t, r_seq i ∈ Γ.R := fun i => (hchain.2.2 i).1
      have hr0 : (closure (r_seq ⟨0, ht_pos⟩) ∩ z).Nonempty :=
        ⟨v_seq 0, (hchain.2.2 ⟨0, ht_pos⟩).2.1, hchain.1⟩
      have hrt :
          (closure (r_seq ⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩) ∩ subBd Δ).Nonempty := by
        refine ⟨v_seq (Fin.last t), ?_, hchain.2.1⟩
        have h_idx : (⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩ : Fin t).succ = Fin.last t := by
          ext
          change (t - 1) + 1 = t
          omega
        rw [← h_idx]
        exact (hchain.2.2 ⟨t - 1, Nat.sub_lt ht_pos zero_lt_one⟩).2.2
      have hstep : ∀ (i : Fin t) (hi : i.1 + 1 < t),
          (closure (r_seq i) ∩ closure (r_seq ⟨i.1 + 1, hi⟩)).Nonempty := by
        intro i hi
        refine ⟨v_seq i.succ, (hchain.2.2 i).2.2, ?_⟩
        have h_eq : (⟨i.1 + 1, hi⟩ : Fin t).castSucc = i.succ := rfl
        rw [← h_eq]
        exact (hchain.2.2 ⟨i.1 + 1, hi⟩).2.1
      have hle := lemma_5_2_claim_1 hS hConn hMetric hord hz hz_sub h_iii ht_pos r_seq
        hr hr0 hrt hstep
      omega
  have hz_conn : IsPreconnected z := GM14.atom_isPreconnected hz
  obtain ⟨C_seq, Λ_seq, hprops, hnest⟩ :=
    GM14.theorem_5_5_aux hS Γ hΔ_disc (h - 1) hz_sub ⟨x, hxz⟩ hz_conn hreg_dist
  let Δ_seq : Fin h → Set S := fun i =>
    if hi0 : i.1 = 0 then Δ
    else closure (Λ_seq ⟨h - 1 - i.1, by omega⟩)
  refine ⟨Δ_seq, ?_, ?_, ?_⟩
  · intro i
    dsimp only [Δ_seq]
    split_ifs with hi0
    · exact ⟨hΔ_disc, IsClosedDisc.subBd_eq_discBd hS hΔ_disc, hbdU⟩
    · set j : Fin (h - 1) := ⟨h - 1 - i.1, by omega⟩
      have hdisc_j : IsClosedDisc (closure (Λ_seq j)) := (hprops j).2.2.2.2.2.1
      have hbd_j : subBd (closure (Λ_seq j)) = (C_seq j).U := (hprops j).2.2.2.2.2.2.2.1
      exact ⟨hdisc_j, IsClosedDisc.subBd_eq_discBd hS hdisc_j,
        hbd_j ▸ (hprops j).1.U_subset⟩
  · intro i hi
    have hi_succ_ne : (⟨i.1 + 1, hi⟩ : Fin h).1 ≠ 0 := by
      change i.1 + 1 ≠ 0
      omega
    have hΔ_succ : Δ_seq ⟨i.1 + 1, hi⟩ = closure (Λ_seq ⟨h - 1 - (i.1 + 1), by omega⟩) :=
      dif_neg hi_succ_ne
    rw [hΔ_succ]
    by_cases hi0 : i.1 = 0
    · have hΔ_i : Δ_seq i = Δ := dif_pos hi0
      rw [hΔ_i]
      exact (hprops ⟨h - 1 - (i.1 + 1), by omega⟩).2.2.2.2.1
    · have hΔ_i : Δ_seq i = closure (Λ_seq ⟨h - 1 - i.1, by omega⟩) := dif_neg hi0
      rw [hΔ_i]
      set j₁ : Fin (h - 1) := ⟨h - 1 - (i.1 + 1), by omega⟩
      set j₂ : Fin (h - 1) := ⟨h - 1 - i.1, by omega⟩
      have hj_lt : j₁ < j₂ := by
        change h - 1 - (i.1 + 1) < h - 1 - i.1
        omega
      have hsub := hnest j₁ j₂ hj_lt
      have hbd₂ : subBd (closure (Λ_seq j₂)) = (C_seq j₂).U := (hprops j₂).2.2.2.2.2.2.2.1
      have hdiff₂ : closure (Λ_seq j₂) \ (C_seq j₂).U = Λ_seq j₂ := (hprops j₂).2.2.2.2.2.2.2.2.1
      change closure (Λ_seq j₁) ⊆ closure (Λ_seq j₂) \ subBd (closure (Λ_seq j₂))
      rw [hbd₂, hdiff₂]
      exact hsub
  · intro hpos
    refine ⟨?_, ?_⟩
    · dsimp only [Δ_seq]
      split_ifs with h1
      · exact hz_sub hxz
      · set j₀ : Fin (h - 1) := ⟨h - 1 - (h - 1), by omega⟩
        have hbd₀ : subBd (closure (Λ_seq j₀)) = (C_seq j₀).U := (hprops j₀).2.2.2.2.2.2.2.1
        have hdiff₀ : closure (Λ_seq j₀) \ (C_seq j₀).U = Λ_seq j₀ :=
          (hprops j₀).2.2.2.2.2.2.2.2.1
        change x ∈ closure (Λ_seq j₀) \ subBd (closure (Λ_seq j₀))
        rw [hbd₀, hdiff₀]
        exact (hprops j₀).2.2.2.2.2.2.2.2.2 hxz
    · dsimp only [Δ_seq]
      simp only [↓reduceDIte]
      refine disjoint_left.mpr fun p hpY hpΔ => ?_
      have hp_u := hY hpY
      obtain ⟨y, ⟨hyA, hdist_yz⟩, hpy⟩ := mem_iUnion₂.mp hp_u
      have hd_zy : d z y ≤ 2 * h + 4 := (h_ii y hyA ⟨p, hpy, hpΔ⟩).2
      rw [hsymm y hyA z hz] at hdist_yz
      omega

/-! ## 3. Helper Lemmas for Theorem 5.3 (pages 540–542) -/

/-- **5.3, Claim (1)** (Graph Minors XXII, page 540):
"(1) For $1 \le i \le t$, if $z \in A(\Gamma)$ and $z \cap \text{ins}(F_i) \ne \emptyset$ then
$d(z, r_i) \le p$."
More generally, for any two atoms $a, b \in A(\Gamma)$ meeting $\operatorname{ins}(F)$,
$d(a, b) \le |F \cap V(\Gamma)| \le p$. -/
theorem lemma_5_3_claim_1 {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord p : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {F ins_F a b : Set S}
    (hMetric : HasTangleMetric Γ ord T d) (hp_ord : p < ord)
    (hF_oArc : IsOArc F) (hF_norm : Γ.IsNormal F) (hF_card : (F ∩ Γ.V).ncard ≤ p)
    (hIns : IsTangleIns Γ T F ins_F)
    (ha : a ∈ Γ.A) (hb : b ∈ Γ.A)
    (ha_ne : (a ∩ ins_F).Nonempty) (hb_ne : (b ∩ ins_F).Nonempty) :
    d a b ≤ p := by
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hResp, K, ins_K, hK, hd, hd_eq⟩ := hMetric
  obtain ⟨f⟩ := hF_oArc
  let φ : C(Circle, S) := ⟨fun x => (f x).1, continuous_subtype_val.comp f.continuous⟩
  have hφ_emb : IsEmbedding φ := IsEmbedding.subtypeVal.comp f.isEmbedding
  have hφ_range : range φ = F := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, congrArg Subtype.val (f.apply_symm_apply ⟨x, hx⟩)⟩
  have hφ_norm : IsNormalCurve Γ φ :=
    GM12.isNormalCurve_of_injective φ hφ_emb.injective (hφ_range ▸ hF_norm)
  have hlen_eq : curveLength Γ φ = (F ∩ Γ.V).ncard := by
    rw [GM12.curveLength_eq_vertex_count φ hφ_emb.injective (hφ_range ▸ hF_norm), hφ_range]
  have hlen_lt : curveLength Γ φ < ord := by omega
  obtain ⟨u, W, hW⟩ :=
    GM12.exists_trace_of_curveLength_lt_tangle_order hS hResp.2.1 hK hφ_norm hlen_lt
  have ha_W : (a ∩ insWalk ins_K K W).Nonempty :=
    GM12.theorem_2_1_simple hS hResp.2.1 hResp.2.2 hK hd hφ_emb W hW hlen_lt
      hIns.1 (hIns.2.1.trans hφ_range.symm) hIns.2.2 ha ha_ne
  have hb_W : (b ∩ insWalk ins_K K W).Nonempty :=
    GM12.theorem_2_1_simple hS hResp.2.1 hResp.2.2 hK hd hφ_emb W hW hlen_lt
      hIns.1 (hIns.2.1.trans hφ_range.symm) hIns.2.2 hb hb_ne
  obtain ⟨a', ha', -⟩ := GM14.existsUnique_correspondingAtom hK ha
  obtain ⟨b', hb', -⟩ := GM14.existsUnique_correspondingAtom hK hb
  have hW_len : W.length = 2 * curveLength Γ φ := GM12.trace_length_eq_two_mul_curveLength hW
  have hW_lt : W.length < 2 * ord := by omega
  have ha'_sub : a' ⊆ insWalk ins_K K W :=
    (GM12.corresponding_atom_subset_iff hS hK hd ha' W hW_lt).mpr ha_W
  have hb'_sub : b' ⊆ insWalk ins_K K W :=
    (GM12.corresponding_atom_subset_iff hS hK hd hb' W hW_lt).mpr hb_W
  rw [hd_eq a ha b hb]
  exact (GM12.tangleMetric_le_of_walk ha' hb' W hW_lt hW_len ha'_sub hb'_sub).trans
    (hlen_eq ▸ hF_card)

/-- Normal-`O`-arc version of Graph Minors XIV, Theorem 7.5 (used in the subproof of **5.3,
Claim (5)**, page 541): if `Λ` is a `λ`-zone around `z ∈ R(Γ)`, `Δ ⊆ closure Λ` is a closed disc
bounded by a `Γ`-normal `O`-arc `F = subBd Δ` with `|F ∩ V(Γ)| + λ < ord`, and `ins_F` satisfies
`IsTangleIns Γ T F ins_F`, then `Δ = ins_F` (and hence `IsTangleIns Γ T F Δ`). -/
theorem tangleIns_eq_of_subset_zone_closure {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord lam : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {z Λ F Δ ins_F : Set S}
    (hMetric : HasTangleMetric Γ ord T d) (hlam : 1 ≤ lam)
    (hZone : IsLambdaZoneAround Γ d lam z Λ) (hzR : z ∈ Γ.R)
    (hΔ_disc : IsClosedDisc Δ) (hΔ_sub : Δ ⊆ closure Λ) (hΔ_bd : subBd Δ = F)
    (hF_norm : Γ.IsNormal F) (hF_card : (F ∩ Γ.V).ncard + lam < ord)
    (hIns : IsTangleIns Γ T F ins_F) :
    Δ = ins_F := by
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have htri := h91_prop.2.2.2.2.1
  obtain ⟨hResp, K₀, ins₀, hK₀, hd₀, hd_eq⟩ := hMetric
  have hMetric' : HasTangleMetric Γ ord T d := ⟨hResp, K₀, ins₀, hK₀, hd₀, hd_eq⟩
  by_contra h_ne
  have hbd_eq : discBd ins_F = discBd Δ := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hIns.1, ← IsClosedDisc.subBd_eq_discBd hS hΔ_disc,
      hIns.2.1, hΔ_bd]
  have hcov : ins_F ∪ Δ = univ :=
    GM14.cover_of_discBd_eq hS hIns.1 hΔ_disc hbd_eq (Ne.symm h_ne)
  have hE_ne : Γ.E.Nonempty := GM14.edgeSet_nonempty_of_isTangle hResp.2.1 (by omega)
  have hz_not_E : z ∉ Γ.E := by
    intro hzE
    obtain ⟨p, hp⟩ := hzE.1
    exact region_subset hzR hp (hzE.2.1 hp).1
  obtain ⟨e, heΓ, hze⟩ :=
    GM14.exists_edge_dist_eq_theta hS hConn hMetric' hE_ne hZone.z_mem (Or.inr hz_not_E)
  have he_not_cl : ¬ e ⊆ closure Λ := by
    intro hsub
    have hle := hZone.dist_le e (Or.inl (Or.inr heΓ)) hsub
    omega
  have he_dis_F : Disjoint e F :=
    disjoint_left.mpr fun x hxe hxF => (heΓ.2.1 hxe).2 (hF_norm ⟨hxF, (heΓ.2.1 hxe).1⟩)
  have he_sub_ins : e ⊆ ins_F := by
    have he_not_Δ : ¬ (e ∩ Δ).Nonempty := by
      rintro ⟨x, hxe, hxΔ⟩
      have hfrΔ : frontier Δ = F := by rw [subBd_eq_frontier', hΔ_bd]
      have hsub : e ⊆ Δ :=
        GM12.subset_of_disjoint_frontier heΓ.2.2.1.isConnected.isPreconnected hΔ_disc.isClosed
          (hfrΔ ▸ he_dis_F) hxe hxΔ
      exact he_not_cl (hsub.trans hΔ_sub)
    intro x hxe
    have hx_univ : x ∈ ins_F ∪ Δ := hcov.symm ▸ mem_univ x
    exact hx_univ.resolve_right fun hxΔ => he_not_Δ ⟨x, hxe, hxΔ⟩
  set A := (PaintingOrDrawing.drawing Γ).inter ins_F
  set B := (PaintingOrDrawing.drawing Γ).interOutside ins_F
  have heA : e ∈ A.edgeSet := ⟨heΓ, he_sub_ins⟩
  have hAB_V : (A ∩ B).vertexSet ⊆ F ∩ Γ.V := by
    intro x hx
    have hxA : x ∈ Γ.V ∧ x ∈ ins_F := hx.1
    have hxB : x ∈ Γ.V ∧ x ∈ closure (univ \ ins_F) := hx.2
    have hx_fr : x ∈ frontier ins_F := by
      rw [frontier_eq_closure_inter_closure, hIns.1.isClosed.closure_eq, Set.compl_eq_univ_sdiff]
      exact ⟨hxA.2, hxB.2⟩
    have hx_sub : x ∈ subBd ins_F := by
      rw [← subBd_eq_frontier']
      exact hx_fr
    rw [hIns.2.1] at hx_sub
    exact ⟨hx_sub, hxA.1⟩
  obtain ⟨D₀, hD₀, hD₀s, hD₀len, hD₀V, heD₀⟩ :=
    GM14.theorem_7_2_proof hS hConn hE_ne hResp hK₀ hd₀ hIns.2.2 heA
  obtain ⟨v, hv₀⟩ := (GM12.circuit_length_eq_two_mul_ncard hK₀.2.1 hD₀ hD₀s).2
  have hvF : v ∈ F ∩ Γ.V := hAB_V (hD₀V hv₀)
  have hv_frΔ : v ∈ frontier Δ := by
    rw [subBd_eq_frontier', hΔ_bd]
    exact hvF.1
  have hv_cl : ({v} : Set S) ⊆ closure Λ :=
    singleton_subset_iff.mpr (hΔ_sub (hΔ_disc.isClosed.frontier_subset hv_frΔ))
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hvF.2, rfl⟩)
  have hzv_le : d z {v} ≤ lam := hZone.dist_le {v} hvA hv_cl
  obtain ⟨p, hp⟩ := heΓ.1
  have hve_le : d {v} e ≤ (F ∩ Γ.V).ncard := by
    rw [hd_eq {v} hvA e (Or.inl (Or.inr heΓ))]
    refine (GM14.tangleMetric_vertex_le_of_circuit hS hK₀ hd₀ hD₀ hD₀s hD₀len hv₀
      (Or.inl (Or.inr heΓ)) ⟨p, hp, heD₀ hp⟩).2.trans ?_
    exact ncard_le_ncard (hD₀V.trans hAB_V) (Γ.finite_V.subset inter_subset_right)
  have htri' := htri z hZone.z_mem {v} hvA e (Or.inl (Or.inr heΓ))
  omega

/-- Upper bound for `subsetTangleDist Γ ord d X Y` given atoms `a, b ∈ A(Γ)` meeting `X, Y`. -/
theorem subsetTangleDist_le {S : Type*} [TopologicalSpace S] (Γ : Surface.Drawing S)
    (ord : ℕ) (d : Set S → Set S → ℕ) {X Y a b : Set S}
    (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) (haX : (a ∩ X).Nonempty) (hbY : (b ∩ Y).Nonempty) :
    subsetTangleDist Γ ord d X Y ≤ d a b := by
  unfold subsetTangleDist
  rw [if_pos ⟨a, ha, b, hb, haX, hbY⟩]
  exact Nat.sInf_le ⟨a, ha, b, hb, haX, hbY, rfl⟩

/-- If `subsetTangleDist Γ ord d X Y < m` and `m ≤ ord`, there exist atoms `a, b ∈ A(Γ)` meeting
`X, Y` with `d a b < m`. -/
theorem exists_atoms_of_subsetTangleDist_lt {S : Type*} [TopologicalSpace S]
    (Γ : Surface.Drawing S) (ord : ℕ) (d : Set S → Set S → ℕ) {X Y : Set S} {m : ℕ}
    (hlt : subsetTangleDist Γ ord d X Y < m) (hm : m ≤ ord) :
    ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b < m := by
  unfold subsetTangleDist at hlt
  split_ifs at hlt with hex
  · obtain ⟨a₀, ha₀, b₀, hb₀, ha₀X, hb₀Y⟩ := hex
    have hne : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k}.Nonempty :=
      ⟨d a₀ b₀, a₀, ha₀, b₀, hb₀, ha₀X, hb₀Y, rfl⟩
    obtain ⟨a, ha, b, hb, haX, hbY, hd⟩ := Nat.sInf_mem hne
    exact ⟨a, ha, b, hb, haX, hbY, hd ▸ hlt⟩
  · omega

/-- Every `Γ`-normal `O`-arc `F` in a closed surface `S` meets some region `r ∈ R(Γ)`. -/
theorem exists_region_inter_normal_oArc {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Surface.Drawing S) {F : Set S}
    (hF_oArc : IsOArc F) (hF_norm : Γ.IsNormal F) :
    ∃ r ∈ Γ.R, (r ∩ F).Nonempty := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hF_inf : F.Infinite := GM11.infinite_of_isOArc hF_oArc
  obtain ⟨x, hxF, hxV⟩ := hF_inf.exists_notMem_finite Γ.finite_V
  have hxU : x ∉ Γ.U := fun hxU => hxV (hF_norm ⟨hxF, hxU⟩)
  obtain ⟨r, hr, hxr⟩ := GM11.exists_region_of_notMem hxU
  exact ⟨r, hr, x, hxr, hxF⟩

/-- When `P : Fin t → Set S` are pairwise disjoint closed discs with `Γ`-normal boundaries `F i =
subBd (P i)` and `S_sub = (⋃ i, discInt (P i))ᶜ`, `(Γ.interSet S_sub).U = Γ.U ∩ S_sub`. -/
theorem interSet_U_eq_of_normal_discs {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Surface.Drawing S) {t : ℕ}
    {F P : Fin t → Set S}
    (hP_disc : ∀ i : Fin t, IsClosedDisc (P i))
    (hP_bd : ∀ i : Fin t, subBd (P i) = F i)
    (hF_norm : ∀ i : Fin t, Γ.IsNormal (F i)) :
    (Γ.interSet (⋃ i : Fin t, discInt (P i))ᶜ).U =
      Γ.U ∩ (⋃ i : Fin t, discInt (P i))ᶜ := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  set S_sub : Set S := (⋃ i : Fin t, discInt (P i))ᶜ
  have hS_sub_closed : IsClosed S_sub :=
    (isOpen_iUnion fun i => (hP_disc i).isOpen_discInt hman).isClosed_compl
  refine Subset.antisymm (fun x hx => ⟨(GM11.interSet_isSub (Γ := Γ)).U_subset hx,
    GM11.interSet_U_subset hS_sub_closed hx⟩) ?_
  rintro q ⟨hqU, hqS_sub⟩
  by_cases hqV : q ∈ Γ.V
  · exact (Γ.interSet S_sub).V_subset_U (GM11.mem_interSet_V hqV hqS_sub)
  · obtain ⟨e, he, hqe⟩ := Γ.exists_edge_of_mem hqU hqV
    have he_sub : e ⊆ S_sub := by
      intro z hze hz_in
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz_in
      have he_dis : Disjoint e (frontier (P i)) := by
        rw [subBd_eq_frontier', hP_bd i]
        exact disjoint_left.mpr fun w hwe hwF =>
          (he.2.1 hwe).2 (hF_norm i ⟨hwF, (he.2.1 hwe).1⟩)
      have he_P : e ⊆ P i :=
        GM12.subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected (hP_disc i).isClosed
          he_dis hze hzi.1
      have hq_int : q ∈ discInt (P i) := by
        refine ⟨he_P hqe, fun hq_bd => ?_⟩
        rw [← IsClosedDisc.subBd_eq_discBd hS (hP_disc i), ← subBd_eq_frontier'] at hq_bd
        exact disjoint_left.mp he_dis hqe hq_bd
      exact hqS_sub (mem_iUnion.mpr ⟨i, hq_int⟩)
    have he_inter : e ∈ (Γ.interSet S_sub).E := GM11.mem_interSet_E_iff.mpr ⟨he, he_sub⟩
    exact (he_inter.2.1 hqe).1

/-- If `x` is `h`-insulated in `S` from `X` by `Γ`, `1 ≤ h`, `S \ S_sub ⊆ X`, and `Y ⊆ X`, then `x` is
`h`-insulated in `S` from `Y` by `Γ.interSet S_sub`. -/
theorem isInsulated_interSet_of_compl_subset {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Surface.Drawing S) {t h : ℕ} (hh : 1 ≤ h)
    {F P : Fin t → Set S} {X Y : Set S} {x : S}
    (hP_disc : ∀ i : Fin t, IsClosedDisc (P i))
    (hP_bd : ∀ i : Fin t, subBd (P i) = F i)
    (hF_norm : ∀ i : Fin t, Γ.IsNormal (F i))
    (hcompl : (⋃ i : Fin t, discInt (P i)) ⊆ X)
    (hYX : Y ⊆ X)
    (hInsul : IsInsulated Γ X h x) :
    IsInsulated (Γ.interSet (⋃ i : Fin t, discInt (P i))ᶜ) Y h x := by
  set S_sub : Set S := (⋃ i : Fin t, discInt (P i))ᶜ
  have hU_eq : (Γ.interSet S_sub).U = Γ.U ∩ S_sub :=
    interSet_U_eq_of_normal_discs hS Γ hP_disc hP_bd hF_norm
  obtain ⟨Δ, hΔ_props, hΔ_nest, hΔ_end⟩ := hInsul
  have hpos : 0 < h := by omega
  have hΔ0_sub : Δ ⟨0, hpos⟩ ⊆ S_sub := by
    intro q hq hu
    exact disjoint_left.mp (hΔ_end hpos).2 (hcompl hu) hq
  have hΔ_sub_0 : ∀ (k : ℕ) (hk : k < h), Δ ⟨k, hk⟩ ⊆ Δ ⟨0, hpos⟩ := by
    intro k
    induction k with
    | zero => intro _; exact subset_rfl
    | succ k ih =>
      intro hk
      exact (hΔ_nest ⟨k, Nat.lt_of_succ_lt hk⟩ hk).trans
        (sdiff_subset.trans (ih (Nat.lt_of_succ_lt hk)))
  refine ⟨Δ, fun m => ⟨(hΔ_props m).1, (hΔ_props m).2.1, ?_⟩, hΔ_nest, fun hpos' =>
    ⟨(hΔ_end hpos').1, Disjoint.mono_left hYX (hΔ_end hpos').2⟩⟩
  rw [hU_eq]
  intro q hq
  have hq_Δm : q ∈ Δ m := by
    rw [(hΔ_props m).2.1] at hq
    exact Surface.discBd_subset (Δ m) hq
  exact ⟨(hΔ_props m).2.2 hq, hΔ0_sub (hΔ_sub_0 m.1 m.2 hq_Δm)⟩

/-! ## 4. Claims (2)–(7) of Theorem 5.3 (pages 541–542) -/

/-- **5.3, Claim (2)** (Graph Minors XXII, page 541):
"(2) For $1 \le i \le t$ there is a closed disc $S_i \subseteq \Sigma$ such that
(i) $\text{bd}(S_i) \subseteq U(\Gamma)$,
(ii) $d(r_i, x) \le p + 2h + 7$ for all $x \in A(\Gamma)$ with $x \cap S_i \ne \emptyset$, and
(iii) $d(r_i, x) \ge p + 2h + 5$ for all $x \in A(\Gamma)$ with
$x \nsubseteq S_i \setminus \text{bd}(S_i)$." -/
theorem lemma_5_3_claim_2 {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord p h t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (r : Fin t → Set S)
    (hMetric : HasTangleMetric Γ ord T d)
    (hord : 2 * p + 4 * h + 15 ≤ ord)
    (hr : ∀ i : Fin t, r i ∈ Γ.R) (i : Fin t) :
    ∃ (C_i : Surface.Drawing S) (Λ_i S_i : Set S),
      S_i = closure Λ_i ∧
      C_i.IsSubdrawing Γ ∧ C_i.IsCircuit ∧
      IsClosedDisc S_i ∧
      subBd Λ_i = C_i.U ∧ subBd S_i = C_i.U ∧ S_i \ subBd S_i = Λ_i ∧
      IsLambdaZoneAround Γ d (p + 2 * h + 7) (r i) Λ_i ∧
      subBd S_i ⊆ Γ.U ∧
      (∀ x ∈ Γ.A, (x ∩ S_i).Nonempty → x ⊆ S_i ∧ d (r i) x ≤ p + 2 * h + 7) ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ S_i \ subBd S_i) → p + 2 * h + 5 ≤ d (r i) x) ∧
      r i ⊆ S_i \ subBd S_i := by
  obtain ⟨C_i, Λ_i, S_i, h1, h2, h3, h4, h5, h6, h7, hZone, h8, h9, h10, h11⟩ :=
    lemma_5_1_full hS hConn Γ ord (p + 2 * h + 5) T d (r i) hMetric
      (Or.inr (hr i)) (by omega) (by omega)
  have h7_eq : p + 2 * h + 5 + 2 = p + 2 * h + 7 := by omega
  rw [h7_eq] at hZone h9
  exact ⟨C_i, Λ_i, S_i, h1, h2, h3, h4, h5, h6, h7, hZone, h8, h9, h10, h11⟩

/-- **5.3, Claim (3)** (Graph Minors XXII, page 541):
"(3) For $1 \le i < j \le t$, $S_i \cap S_j = \emptyset$." -/
theorem lemma_5_3_claim_3 {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord p h t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {ins_F r S_disc : Fin t → Set S}
    (hMetric : HasTangleMetric Γ ord T d)
    (hr : ∀ i : Fin t, r i ∈ Γ.R)
    (hr_ins : ∀ i : Fin t, (r i ∩ ins_F i).Nonempty)
    (hS_ii : ∀ (i : Fin t) (x : Set S), x ∈ Γ.A → (x ∩ S_disc i).Nonempty →
      d (r i) x ≤ p + 2 * h + 7)
    (h_ii : ∀ i j : Fin t, i ≠ j →
      2 * p + 4 * h + 15 ≤ subsetTangleDist Γ ord d (ins_F i) (ins_F j))
    {i j : Fin t} (hij : i ≠ j) :
    Disjoint (S_disc i) (S_disc j) := by
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have hsymm := h91_prop.2.2.2.1
  have htri := h91_prop.2.2.2.2.1
  refine disjoint_left.mpr fun q hqi hqj => ?_
  obtain ⟨x, hxA, hqx⟩ := GM14.exists_atom_mem_of_point Γ q
  have h1 : d (r i) x ≤ p + 2 * h + 7 := hS_ii i x hxA ⟨q, hqx, hqi⟩
  have h2 : d (r j) x ≤ p + 2 * h + 7 := hS_ii j x hxA ⟨q, hqx, hqj⟩
  have h2' : d x (r j) ≤ p + 2 * h + 7 := by
    rw [hsymm x hxA (r j) (Or.inr (hr j))]
    exact h2
  have htri' := htri (r i) (Or.inr (hr i)) x hxA (r j) (Or.inr (hr j))
  have hsub_le : subsetTangleDist Γ ord d (ins_F i) (ins_F j) ≤ d (r i) (r j) :=
    subsetTangleDist_le Γ ord d (Or.inr (hr i)) (Or.inr (hr j)) (hr_ins i) (hr_ins j)
  have hge := h_ii i j hij
  omega

/-- **5.3, Claim (4)** (Graph Minors XXII, page 541):
"(4) For $1 \le i \le t$, $S_i \cap V(\Gamma \cap K) = \emptyset$ and
$\text{ins}(F_i) \subseteq S_i$." (In fact $\operatorname{ins}(F_i) \subseteq S_i \setminus
\operatorname{bd}(S_i)$.) -/
theorem lemma_5_3_claim_4 {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord p h t : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {F ins_F r S_disc : Fin t → Set S} {VK : Set S}
    (hMetric : HasTangleMetric Γ ord T d)
    (hord : 2 * p + 4 * h + 15 ≤ ord)
    (hF_oArc : ∀ i : Fin t, IsOArc (F i))
    (hF_norm : ∀ i : Fin t, Γ.IsNormal (F i))
    (hF_card : ∀ i : Fin t, (F i ∩ Γ.V).ncard ≤ p)
    (hIns : ∀ i : Fin t, IsTangleIns Γ T (F i) (ins_F i))
    (hr : ∀ i : Fin t, r i ∈ Γ.R)
    (hr_ins : ∀ i : Fin t, (r i ∩ ins_F i).Nonempty)
    (hVK_sub : VK ⊆ Γ.V)
    (h_iii : ∀ (i : Fin t), ∀ v ∈ VK,
      2 * p + 4 * h + 15 ≤ subsetTangleDist Γ ord d (ins_F i) {v})
    (hS_ii : ∀ (i : Fin t) (x : Set S), x ∈ Γ.A → (x ∩ S_disc i).Nonempty →
      d (r i) x ≤ p + 2 * h + 7)
    (hS_iii : ∀ (i : Fin t) (x : Set S), x ∈ Γ.A → ¬ (x ⊆ S_disc i \ subBd (S_disc i)) →
      p + 2 * h + 5 ≤ d (r i) x)
    (i : Fin t) :
    Disjoint (S_disc i) VK ∧ ins_F i ⊆ S_disc i \ subBd (S_disc i) := by
  refine ⟨disjoint_left.mpr fun v hvS hvVK => ?_, fun q hq => ?_⟩
  · have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hVK_sub hvVK, rfl⟩)
    have h1 : d (r i) {v} ≤ p + 2 * h + 7 :=
      hS_ii i {v} hvA ⟨v, mem_singleton v, hvS⟩
    have hsub_le : subsetTangleDist Γ ord d (ins_F i) {v} ≤ d (r i) {v} :=
      subsetTangleDist_le Γ ord d (Or.inr (hr i)) hvA (hr_ins i) ⟨v, mem_singleton v, mem_singleton v⟩
    have hge := h_iii i v hvVK
    omega
  · obtain ⟨z, hzA, hqz⟩ := GM14.exists_atom_mem_of_point Γ q
    have hrz : d (r i) z ≤ p :=
      lemma_5_3_claim_1 hS hConn hMetric (by omega) (hF_oArc i) (hF_norm i) (hF_card i)
        (hIns i) (Or.inr (hr i)) hzA (hr_ins i) ⟨q, hqz, hq⟩
    have hz_sub : z ⊆ S_disc i \ subBd (S_disc i) := by
      by_contra hnot
      have hge := hS_iii i z hzA hnot
      omega
    exact hz_sub hqz

/-- **5.3, Claim (5)** (Graph Minors XXII, page 541):
"(5) For $1 \le i \le t$ there are $|F_i \cap V(\Gamma)|$ mutually disjoint paths of
$\Gamma \cap \Sigma'$ between $V(\Gamma) \cap F_i$ and $V(\Gamma) \cap \text{bd}(S_i)$." -/
theorem lemma_5_3_claim_5 {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord p h t : ℕ} (hh : 1 ≤ h)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {C : Fin t → Surface.Drawing S}
    {ins : Set S → Set S}
    {F ins_F r Λ_disc S_disc : Fin t → Set S} {X : Set S}
    (hMetric : HasTangleMetric Γ ord T d)
    (hord : 2 * p + 4 * h + 15 ≤ ord)
    (hF_norm : ∀ i : Fin t, Γ.IsNormal (F i))
    (hF_card : ∀ i : Fin t, (F i ∩ Γ.V).ncard ≤ p)
    (hIns : ∀ i : Fin t, IsTangleIns Γ T (F i) (ins_F i))
    (hIns_fn : ∀ F₀ : Set S, IsOArc F₀ → Γ.IsNormal F₀ → (F₀ ∩ Γ.V).ncard < ord →
      IsTangleIns Γ T F₀ (ins F₀))
    (hr : ∀ i : Fin t, r i ∈ Γ.R)
    (h_i : ∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ Γ.IsNormal F₀ ∧
      (F₀ ∩ Γ.V).ncard < (F i ∩ Γ.V).ncard ∧ ins_F i ⊆ ins F₀)
    (hS_cl : ∀ i : Fin t, S_disc i = closure (Λ_disc i))
    (hC_sub : ∀ i : Fin t, (C i).IsSubdrawing Γ)
    (hS_disc : ∀ i : Fin t, IsClosedDisc (S_disc i))
    (hS_bd : ∀ i : Fin t, subBd (S_disc i) = (C i).U)
    (hZone : ∀ i : Fin t, IsLambdaZoneAround Γ d (p + 2 * h + 7) (r i) (Λ_disc i))
    (hins_sub : ∀ i : Fin t, ins_F i ⊆ S_disc i \ subBd (S_disc i))
    (hX : IsClosed X) (i : Fin t)
    (hsubX : S_disc i \ discInt (ins_F i) ⊆ X) :
    let D_pull := drawingPullSubtype (Γ.interSet X) hX (GM11.interSet_U_subset hX)
    let C_pull : Set ↥X := Subtype.val ⁻¹' F i
    ∃ P : ↑(D_pull.V ∩ C_pull) → Graph ↥X (Set ↥X),
      (∀ x : ↑(D_pull.V ∩ C_pull),
        ∃ y ∈ D_pull.V ∩ Subtype.val ⁻¹' subBd (S_disc i),
          GM09.IsGraphPathWithEnds D_pull.toGraph (P x) x.1 y) ∧
      Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂)) := by
  have : ConnectedSpace S := hConn
  have hbd_ins : discBd (ins_F i) = F i := by
    rw [← IsClosedDisc.subBd_eq_discBd hS (hIns i).1, (hIns i).2.1]
  have hbd_S : discBd (S_disc i) = (C i).U := by
    rw [← IsClosedDisc.subBd_eq_discBd hS (hS_disc i), hS_bd i]
  have hin : ins_F i ⊆ S_disc i \ discBd (S_disc i) := by
    rw [← IsClosedDisc.subBd_eq_discBd hS (hS_disc i)]
    exact hins_sub i
  have hn₁ : Γ.IsNormal (discBd (ins_F i)) := hbd_ins ▸ hF_norm i
  rw [← hbd_ins]
  refine exists_disc_paths_pull_of_circuit_bd hS (hIns i).1 (hS_disc i) hin (hC_sub i) hbd_S
    hn₁ hX hsubX ?_
  intro B hB_disc hinsB hBS hB_norm
  rw [hbd_ins]
  by_contra hlt
  push Not at hlt
  set F_B := discBd B
  have hFB_oArc : IsOArc F_B := hB_disc.isOArc_discBd
  have hFB_card : (F_B ∩ Γ.V).ncard < (F i ∩ Γ.V).ncard := by
    rw [inter_comm F_B Γ.V, inter_comm (F i) Γ.V]
    exact hlt
  have hFB_ord : (F_B ∩ Γ.V).ncard < ord := by
    have := hF_card i
    omega
  have hIns_B : IsTangleIns Γ T F_B (ins F_B) :=
    hIns_fn F_B hFB_oArc hB_norm hFB_ord
  have hB_eq : B = ins F_B :=
    tangleIns_eq_of_subset_zone_closure hS hConn hMetric (by omega) (hZone i) (hr i)
      hB_disc (hS_cl i ▸ hBS) (IsClosedDisc.subBd_eq_discBd hS hB_disc) hB_norm
      (by change (F_B ∩ Γ.V).ncard + (p + 2 * h + 7) < ord; have := hF_card i; omega) hIns_B
  exact h_i i ⟨F_B, hFB_oArc, hB_norm, hFB_card, hB_eq ▸ hinsB⟩

/-- **5.3, Claim (6)** (Graph Minors XXII, page 541):
"(6) $R \cap \Sigma' \subseteq S \cup T$." -/
theorem lemma_5_3_claim_6 {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord p h t : ℕ} (hh : 1 ≤ h)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {F ins_F r S_disc : Fin t → Set S} {VK Y : Set S}
    (hMetric : HasTangleMetric Γ ord T d)
    (hord : 2 * p + 4 * h + 15 ≤ ord)
    (hF_oArc : ∀ i : Fin t, IsOArc (F i))
    (hF_norm : ∀ i : Fin t, Γ.IsNormal (F i))
    (hF_card : ∀ i : Fin t, (F i ∩ Γ.V).ncard ≤ p)
    (hIns : ∀ i : Fin t, IsTangleIns Γ T (F i) (ins_F i))
    (hr : ∀ i : Fin t, r i ∈ Γ.R)
    (hr_ins : ∀ i : Fin t, (r i ∩ ins_F i).Nonempty)
    (hVK_sub : VK ⊆ Γ.V)
    (hS_iii : ∀ (i : Fin t) (x : Set S), x ∈ Γ.A → ¬ (x ⊆ S_disc i \ subBd (S_disc i)) →
      p + 2 * h + 5 ≤ d (r i) x)
    (hY_sub : Y ⊆ VK ∪ ⋃ i : Fin t, ins_F i) :
    let S_sub := (⋃ i : Fin t, discInt (ins_F i))ᶜ
    let R := {x : S | ∃ z ∈ Γ.A, x ∈ z ∧ ∀ v ∈ VK, 2 * p + 4 * h + 15 ≤ d z {v}}
    R ∩ S_sub ⊆
      ((⋃ i : Fin t, S_disc i) ∩ S_sub) ∪
        (insulatedSet (Γ.interSet S_sub) Y h ∩ S_sub) := by
  intro S_sub R
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have hsymm := h91_prop.2.2.2.1
  have htri := h91_prop.2.2.2.2.1
  rintro x ⟨⟨z, hzA, hxz, hz_dist⟩, hxS_sub⟩
  by_cases hex_i : ∃ i : Fin t, ∃ y ∈ Γ.A, (y ∩ ins_F i).Nonempty ∧ d z y ≤ 2 * h + 4
  · obtain ⟨i, y, hyA, hy_ne, hd_zy⟩ := hex_i
    have hd_ry : d (r i) y ≤ p :=
      lemma_5_3_claim_1 hS hConn hMetric (by omega) (hF_oArc i) (hF_norm i) (hF_card i)
        (hIns i) (Or.inr (hr i)) hyA (hr_ins i) hy_ne
    have hd_yz : d y z ≤ 2 * h + 4 := by
      rw [hsymm y hyA z hzA]
      exact hd_zy
    have htri' := htri (r i) (Or.inr (hr i)) y hyA z hzA
    have hz_sub : z ⊆ S_disc i \ subBd (S_disc i) := by
      by_contra hnot
      have hge := hS_iii i z hzA hnot
      omega
    exact Or.inl ⟨mem_iUnion.mpr ⟨i, (hz_sub hxz).1⟩, hxS_sub⟩
  · push Not at hex_i
    set X := VK ∪ ⋃ i : Fin t, ins_F i
    have hX_sub : X ⊆ ⋃ y ∈ {y ∈ Γ.A | 2 * h + 5 ≤ d y z}, y := by
      intro q hq
      rcases hq with hqVK | hq_ins
      · have hqA : ({q} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨q, hVK_sub hqVK, rfl⟩)
        have hd_zq := hz_dist q hqVK
        have hd_qz : 2 * h + 5 ≤ d {q} z := by
          rw [hsymm {q} hqA z hzA]
          omega
        exact mem_iUnion₂.mpr ⟨{q}, ⟨hqA, hd_qz⟩, mem_singleton q⟩
      · obtain ⟨i, hqi⟩ := mem_iUnion.mp hq_ins
        obtain ⟨y, hyA, hqy⟩ := GM14.exists_atom_mem_of_point Γ q
        have hd_zy : 2 * h + 5 ≤ d z y := hex_i i y hyA ⟨q, hqy, hqi⟩
        have hd_yz : 2 * h + 5 ≤ d y z := by
          rw [hsymm y hyA z hzA]
          exact hd_zy
        exact mem_iUnion₂.mpr ⟨y, ⟨hyA, hd_yz⟩, hqy⟩
    have hIns_Γ : IsInsulated Γ X h x :=
      theorem_5_2_proof hS hConn Γ ord h hh T d hMetric (by omega) x z X hzA hxz hX_sub
    have hcompl : (⋃ i : Fin t, discInt (ins_F i)) ⊆ X := fun q hq => by
      obtain ⟨i, hqi⟩ := mem_iUnion.mp hq
      exact Or.inr (mem_iUnion.mpr ⟨i, hqi.1⟩)
    exact Or.inr ⟨isInsulated_interSet_of_compl_subset hS Γ hh (fun i => (hIns i).1)
      (fun i => (hIns i).2.1) hF_norm hcompl hY_sub hIns_Γ, hxS_sub⟩

/-- **5.3, Claim (7)** (Graph Minors XXII, pages 541–542):
"(7) For $1 \le i \le t$, $\text{bd}(S_i) \subseteq T$." -/
theorem lemma_5_3_claim_7 {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ : Surface.Drawing S} {ord p h t : ℕ} (hh : 1 ≤ h)
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {F ins_F r S_disc : Fin t → Set S} {VK Y : Set S}
    (hMetric : HasTangleMetric Γ ord T d)
    (hord : 2 * p + 4 * h + 15 ≤ ord)
    (hF_oArc : ∀ i : Fin t, IsOArc (F i))
    (hF_norm : ∀ i : Fin t, Γ.IsNormal (F i))
    (hF_card : ∀ i : Fin t, (F i ∩ Γ.V).ncard ≤ p)
    (hIns : ∀ i : Fin t, IsTangleIns Γ T (F i) (ins_F i))
    (hr : ∀ i : Fin t, r i ∈ Γ.R)
    (hr_ins : ∀ i : Fin t, (r i ∩ ins_F i).Nonempty)
    (hVK_sub : VK ⊆ Γ.V)
    (h_ii : ∀ i j : Fin t, i ≠ j →
      2 * p + 4 * h + 15 ≤ subsetTangleDist Γ ord d (ins_F i) (ins_F j))
    (h_iii : ∀ (i : Fin t), ∀ v ∈ VK,
      2 * p + 4 * h + 15 ≤ subsetTangleDist Γ ord d (ins_F i) {v})
    (hS_ii : ∀ (i : Fin t) (x : Set S), x ∈ Γ.A → (x ∩ S_disc i).Nonempty →
      d (r i) x ≤ p + 2 * h + 7)
    (hS_iii : ∀ (i : Fin t) (x : Set S), x ∈ Γ.A → ¬ (x ⊆ S_disc i \ subBd (S_disc i)) →
      p + 2 * h + 5 ≤ d (r i) x)
    (hS_disc : ∀ i : Fin t, IsClosedDisc (S_disc i))
    (hY_sub : Y ⊆ VK ∪ ⋃ i : Fin t, ins_F i) (i : Fin t) :
    let S_sub := (⋃ j : Fin t, discInt (ins_F j))ᶜ
    subBd (S_disc i) ⊆ insulatedSet (Γ.interSet S_sub) Y h := by
  intro S_sub x hx_bd
  have h91_prop := GM11.gm15_theorem_9_1 Γ ord T d hS hConn hMetric
  have hsymm := h91_prop.2.2.2.1
  have htri := h91_prop.2.2.2.2.1
  obtain ⟨z, hzA, hxz⟩ := GM14.exists_atom_mem_of_point Γ x
  have hx_S : x ∈ S_disc i := by
    rw [IsClosedDisc.subBd_eq_discBd hS (hS_disc i)] at hx_bd
    exact Surface.discBd_subset (S_disc i) hx_bd
  have hd_rz_le : d (r i) z ≤ p + 2 * h + 7 := hS_ii i z hzA ⟨x, hxz, hx_S⟩
  have hd_rz_ge : p + 2 * h + 5 ≤ d (r i) z :=
    hS_iii i z hzA fun hsub => (hsub hxz).2 hx_bd
  set X := VK ∪ ⋃ j : Fin t, ins_F j
  have hX_sub : X ⊆ ⋃ y ∈ {y ∈ Γ.A | 2 * h + 5 ≤ d y z}, y := by
    intro q hq
    rcases hq with hqVK | hq_ins
    · have hqA : ({q} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨q, hVK_sub hqVK, rfl⟩)
      have hge := h_iii i q hqVK
      have hsub_le : subsetTangleDist Γ ord d (ins_F i) {q} ≤ d (r i) {q} :=
        subsetTangleDist_le Γ ord d (Or.inr (hr i)) hqA (hr_ins i)
          ⟨q, mem_singleton q, mem_singleton q⟩
      have htri' := htri (r i) (Or.inr (hr i)) z hzA {q} hqA
      have hd_qz : 2 * h + 5 ≤ d {q} z := by
        rw [hsymm {q} hqA z hzA]
        omega
      exact mem_iUnion₂.mpr ⟨{q}, ⟨hqA, hd_qz⟩, mem_singleton q⟩
    · obtain ⟨j, hqj⟩ := mem_iUnion.mp hq_ins
      obtain ⟨y, hyA, hqy⟩ := GM14.exists_atom_mem_of_point Γ q
      by_cases hij : j = i
      · subst hij
        have hd_ry : d (r j) y ≤ p :=
          lemma_5_3_claim_1 hS hConn hMetric (by omega) (hF_oArc j) (hF_norm j) (hF_card j)
            (hIns j) (Or.inr (hr j)) hyA (hr_ins j) ⟨q, hqy, hqj⟩
        have htri' := htri (r j) (Or.inr (hr j)) y hyA z hzA
        have hd_yz : 2 * h + 5 ≤ d y z := by omega
        exact mem_iUnion₂.mpr ⟨y, ⟨hyA, hd_yz⟩, hqy⟩
      · have hge := h_ii i j (Ne.symm hij)
        have hsub_le : subsetTangleDist Γ ord d (ins_F i) (ins_F j) ≤ d (r i) y :=
          subsetTangleDist_le Γ ord d (Or.inr (hr i)) hyA (hr_ins i) ⟨q, hqy, hqj⟩
        have htri' := htri (r i) (Or.inr (hr i)) z hzA y hyA
        have hd_yz : 2 * h + 5 ≤ d y z := by
          rw [hsymm y hyA z hzA]
          omega
        exact mem_iUnion₂.mpr ⟨y, ⟨hyA, hd_yz⟩, hqy⟩
  have hIns_Γ : IsInsulated Γ X h x :=
    theorem_5_2_proof hS hConn Γ ord h hh T d hMetric (by omega) x z X hzA hxz hX_sub
  have hcompl : (⋃ j : Fin t, discInt (ins_F j)) ⊆ X := fun q hq => by
    obtain ⟨j, hqj⟩ := mem_iUnion.mp hq
    exact Or.inr (mem_iUnion.mpr ⟨j, hqj.1⟩)
  exact isInsulated_interSet_of_compl_subset hS Γ hh (fun j => (hIns j).1)
    (fun j => (hIns j).2.1) hF_norm hcompl hY_sub hIns_Γ

/-! ## 5. Theorem 5.3 (pages 540–542) -/

private theorem sub_open_iff_univ {R : Type w} [TopologicalSpace R]
    {A W : Set R} (hW : IsOpen W) (hs : W ⊆ A) {y : A} (hy : y.1 ∈ W) :
    (IsInteriorPoint y ↔ IsInteriorPoint y.1) ∧ (IsManifoldPoint y.1 → IsManifoldPoint y) := by
  have hW' : IsOpen (Subtype.val ⁻¹' W : Set A) := hW.preimage continuous_subtype_val
  let e : (Subtype.val ⁻¹' W : Set A) ≃ₜ W :=
    { toFun := fun z => ⟨z.1.1, z.2⟩
      invFun := fun w => ⟨⟨w.1, hs w.2⟩, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h1 := isInteriorPoint_sub hW' (x := ⟨y, hy⟩)
  have h2 := isInteriorPoint_sub hW (x := ⟨y.1, hy⟩)
  have h3 := isInteriorPoint_homeomorph_iff e ⟨y, hy⟩
  refine ⟨h1.symm.trans (h3.symm.trans h2), fun hm => ?_⟩
  have h4 : IsManifoldPoint (⟨y.1, hy⟩ : W) := isManifoldPoint_sub hW hm
  have h5 : IsManifoldPoint (⟨y, hy⟩ : (Subtype.val ⁻¹' W : Set A)) :=
    (isManifoldPoint_iff_of_isOpenEmbedding e.isOpenEmbedding).mp h4
  exact isManifoldPoint_of_isOpenEmbedding hW'.isOpenEmbedding_subtypeVal h5

private theorem exists_outer_disc_univ {R : Type w} [TopologicalSpace R]
    (hR : IsSurface R) {E : Set R} (hE : IsClosedDisc E) (hint : ∀ x ∈ discBd E, IsInteriorPoint x)
    {x : R} (hx : x ∈ discBd E) :
    ∃ G, IsClosedDisc G ∧ x ∈ discBd G ∧ Disjoint G (discInt E) ∧
      ∀ᶠ y in 𝓝 x, y ∉ discInt E → y ∈ G := by
  have ht2 : T2Space R := hR.2.1
  have hman := hR.2.2
  obtain ⟨Δ', hΔ', hin, -⟩ := exists_disc_around hman hE hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hE.isOArc_discBd
  obtain ⟨c, c', hcc, hc'c, hmc, hmc', hl, hr, hcE, hcb, hcp⟩ := exists_disc_collar hE hΔ' hin p
  let w₀ : Circle := p.symm ⟨x, hx⟩
  have hcw : c w₀ = x := by rw [hcp, p.apply_symm_apply]
  have hw : ‖(w₀ : ℂ)‖ = 1 := Circle.norm_coe w₀
  obtain ⟨f, Q, hfc, hfi, hQc, hQ, hQ0, hf0, hfn, hev⟩ := exists_half_disc hw
  have hin2 : ∀ ζ ∈ Q, f ζ ∈ Metric.closedBall (0 : ℂ) 2 := fun ζ hζ => by
    have := (hfn ζ hζ).2
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hcont : ContinuousOn (fun ζ => c (f ζ)) Q := hcc.comp hfc hin2
  have hinj : InjOn (fun ζ => c (f ζ)) Q := fun a ha b hb he => hfi ha hb (by
    rw [← hl (hin2 a ha), ← hl (hin2 b hb)]
    exact congrArg c' he)
  have : Nonempty ℂ := ⟨0⟩
  obtain ⟨hG, hGb⟩ := isClosedDisc_image_injOn hQ hQc hcont hinj
  have hball1 : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z ∈ Metric.closedBall (0 : ℂ) 2 :=
    fun z hz => Metric.closedBall_subset_closedBall (by norm_num) hz
  have hEout : ∀ z ∈ Metric.closedBall (0 : ℂ) 2, c z ∈ E → ‖z‖ ≤ 1 := fun z hz hmem => by
    rw [← hcE] at hmem
    obtain ⟨u, hu, he⟩ := hmem
    have h2 : u = z := by
      rw [← hl (hball1 u hu), he, hl hz]
    have : ‖u‖ ≤ 1 := by simpa using hu
    rwa [h2] at this
  have hbdc : ∀ z : ℂ, ‖z‖ = 1 → c z ∈ discBd E := fun z hz => by
    have h1 : c ((⟨z, by simpa [Submonoid.unitSphere] using hz⟩ : Circle) : ℂ) = _ := hcp _
    exact h1 ▸ (p _).2
  refine ⟨_, hG, ?_, ?_, ?_⟩
  · rw [hGb]
    refine ⟨0, hQ0, ?_⟩
    show c (f 0) = x
    rw [hf0, hcw]
  · rw [disjoint_left]
    rintro _ ⟨ζ, hζ, rfl⟩ hz
    have h1 := hEout _ (hin2 ζ hζ) hz.1
    have h2 := hfn ζ hζ
    exact hz.2 (hbdc _ (le_antisymm h1 h2.1))
  · have hxΔ' : x ∈ Δ' \ discBd Δ' := hin (Surface.discBd_subset E hx)
    have hopen := hΔ'.isOpen_discInt hman
    have hnΔ : Δ' ∈ 𝓝 x := Filter.mem_of_superset (hopen.mem_nhds hxΔ') (discInt_subset Δ')
    have hca : ContinuousAt c' x := hc'c.continuousAt hnΔ
    have hc'x : c' x = w₀ := by
      rw [← hcw]
      exact hl (hball1 _ (by simp))
    rw [← hf0] at hev
    have htend : Filter.Tendsto c' (𝓝 x) (𝓝 (f 0)) := by
      rw [hf0, ← hc'x]
      exact hca
    filter_upwards [htend.eventually hev, hnΔ] with y hy hyΔ hyn
    have hcy : c (c' y) = y := hr hyΔ
    have hz2 := hmc' hyΔ
    have hn1 : 1 ≤ ‖c' y‖ := by
      by_contra hlt
      push Not at hlt
      apply hyn
      refine ⟨hcy ▸ hcE ▸ mem_image_of_mem _
        (show c' y ∈ Metric.closedBall (0 : ℂ) 1 by simpa using hlt.le), fun hb => ?_⟩
      have h5 : c (p.symm ⟨y, hb⟩) = y := by rw [hcp, p.apply_symm_apply]
      have h6 : c' y = p.symm ⟨y, hb⟩ := by
        conv_lhs => rw [← h5]
        exact hl (hball1 _ (by simp))
      rw [h6] at hlt
      simp at hlt
    obtain ⟨ζ, hζ, he⟩ := hy hn1
    exact ⟨ζ, hζ, by show c (f ζ) = y; rw [he, hcy]⟩

private theorem remove_disc_univ {R : Type w} [TopologicalSpace R]
    (hR : IsSurface R) {E : Set R} (hE : IsClosedDisc E) (hint : ∀ x ∈ discBd E, IsInteriorPoint x) :
    IsClosed (discInt E)ᶜ ∧ IsSurface ↥(discInt E)ᶜ ∧
      bd ↥(discInt E)ᶜ = Subtype.val ⁻¹' (bd R ∪ discBd E) := by
  have ht2 : T2Space R := hR.2.1
  have hcR : CompactSpace R := hR.1
  have hman := hR.2.2
  have hop := hE.isOpen_discInt hman
  have hcl : IsClosed (discInt E)ᶜ := hop.isClosed_compl
  have hEc : IsClosed E := hE.isClosed
  have hne : Nonempty ↥(discInt E)ᶜ := by
    obtain ⟨φ⟩ := id hE.isOArc_discBd
    exact ⟨⟨_, fun h => h.2 (φ 1).2⟩⟩
  have hEsub : Eᶜ ⊆ (discInt E)ᶜ := fun x hx h => hx h.1
  have hjc : IsClosedEmbedding (Subtype.val : ↥(discInt E)ᶜ → R) := hcl.isClosedEmbedding_subtypeVal
  have hlocal : ∀ {x : ↥(discInt E)ᶜ}, x.1 ∈ discBd E →
      IsManifoldPoint x ∧ x ∈ bd ↥(discInt E)ᶜ := by
    intro x hx
    obtain ⟨G, hG, hxG, hd, hev⟩ := exists_outer_disc_univ hR hE hint hx
    have hGs : G ⊆ range (Subtype.val : ↥(discInt E)ᶜ → R) := by
      rw [Subtype.range_val]
      exact fun y hy => disjoint_left.mp hd hy
    have hcS : CompactSpace ↥(discInt E)ᶜ := isCompact_iff_compactSpace.mp hcl.isCompact
    obtain ⟨hG', hGb⟩ := isClosedDisc_preimage hjc hG hGs
    have hnb : (Subtype.val ⁻¹' G : Set ↥(discInt E)ᶜ) ∈ 𝓝 x := by
      rw [nhds_subtype_eq_comap]
      refine Filter.mem_comap.mpr ⟨_, hev, fun y hy => ?_⟩
      exact hy y.2
    exact ⟨isManifoldPoint_of_disc hG' hnb, mem_bd_of_disc hnb (hGb ▸ hxG)⟩
  have hoff : ∀ {x : ↥(discInt E)ᶜ}, x.1 ∉ discBd E → x.1 ∈ Eᶜ := fun {x} hx hxE => x.2 ⟨hxE, hx⟩
  have hsurf : IsSurface ↥(discInt E)ᶜ := by
    refine ⟨isCompact_iff_compactSpace.mp hcl.isCompact, inferInstance, fun x => ?_⟩
    by_cases hx : x.1 ∈ discBd E
    · exact (hlocal hx).1
    · exact (sub_open_iff_univ hEc.isOpen_compl hEsub (hoff hx)).2 (hman _)
  refine ⟨hcl, hsurf, ?_⟩
  ext x
  by_cases hx : x.1 ∈ discBd E
  · exact ⟨fun _ => .inr hx, fun _ => (hlocal hx).2⟩
  · have h1 := (sub_open_iff_univ hEc.isOpen_compl hEsub (hoff hx)).1
    constructor
    · intro h
      exact .inl fun h2 => h (h1.mpr h2)
    · rintro (h | h)
      · exact fun h2 => h (h1.mp h2)
      · exact absurd h hx

private theorem exists_local_homeo_univ {S : Type w} [TopologicalSpace S]
    {X Y W O : Set S} (h : X ∩ W = Y ∩ W) (hO : O ⊆ W) :
    Nonempty ((Subtype.val ⁻¹' O : Set ↥X) ≃ₜ (Subtype.val ⁻¹' O : Set ↥Y)) := by
  have hXY : X ∩ O = Y ∩ O := by
    ext z
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨(h.subset ⟨h₁, hO h₂⟩).1, h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨(h.symm.subset ⟨h₁, hO h₂⟩).1, h₂⟩
  have hem : ∀ Z : Set S, IsEmbedding (fun z : (Subtype.val ⁻¹' O : Set ↥Z) => (z.1.1 : S)) := fun Z =>
    IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hr : ∀ Z : Set S, range (fun z : (Subtype.val ⁻¹' O : Set ↥Z) => (z.1.1 : S)) = Z ∩ O := fun Z => by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1.2, w.2⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨⟨z, h₁⟩, h₂⟩, rfl⟩
  have eq : range (fun z : (Subtype.val ⁻¹' O : Set ↥X) => (z.1.1 : S)) =
      range (fun z : (Subtype.val ⁻¹' O : Set ↥Y) => (z.1.1 : S)) := by
    rw [hr, hr, hXY]
  exact ⟨((hem X).toHomeomorph.trans (Homeomorph.setCongr eq)).trans (hem Y).toHomeomorph.symm⟩

private theorem isInteriorPoint_congr_local_univ {S : Type w} [TopologicalSpace S]
    {X Y W : Set S} (hW : IsOpen W) (h : X ∩ W = Y ∩ W) {x : ↥X} {y : ↥Y}
    (hxy : x.1 = y.1) (hx : x.1 ∈ W) (hi : IsInteriorPoint x) : IsInteriorPoint y := by
  obtain ⟨U, hU, hxU, hsub, ⟨f⟩⟩ := hi.exists_subset (hW.preimage continuous_subtype_val) hx
  obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hU
  have heq : (Subtype.val ⁻¹' O₀ : Set ↥X) = Subtype.val ⁻¹' (O₀ ∩ W) := by
    ext z
    exact ⟨fun hz => ⟨hz, hsub hz⟩, fun hz => hz.1⟩
  obtain ⟨g⟩ := exists_local_homeo_univ h (inter_subset_right (s := O₀) (t := W))
  exact ⟨Subtype.val ⁻¹' (O₀ ∩ W), (hO₀.inter hW).preimage continuous_subtype_val, ⟨hxy ▸ hxU, hxy ▸ hx⟩,
    ⟨g.symm.trans ((Homeomorph.setCongr heq.symm).trans f)⟩⟩

private theorem isManifoldPoint_congr_local_univ {S : Type w} [TopologicalSpace S]
    {X Y W : Set S} (hW : IsOpen W) (h : X ∩ W = Y ∩ W) {x : ↥X} {y : ↥Y}
    (hxy : x.1 = y.1) (hx : x.1 ∈ W) (hi : IsManifoldPoint x) : IsManifoldPoint y := by
  obtain ⟨U, V, hU, hV, hxU, ⟨f⟩⟩ := hi
  obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hU
  obtain ⟨g⟩ := exists_local_homeo_univ h (inter_subset_right (s := O₀) (t := W))
  have hsub : (Subtype.val ⁻¹' (O₀ ∩ W) : Set ↥X) ⊆ Subtype.val ⁻¹' O₀ := fun z hz => hz.1
  have hj : IsOpenEmbedding (fun z : (Subtype.val ⁻¹' (O₀ ∩ W) : Set ↥X) =>
      ((f (inclusion hsub z)).1 : EuclideanHalfSpace 2)) := by
    have h₁ : IsOpenEmbedding (inclusion hsub) :=
      .inclusion hsub (((hO₀.inter hW).preimage continuous_subtype_val).preimage continuous_subtype_val)
    exact hV.isOpenEmbedding_subtypeVal.comp (f.isOpenEmbedding.comp h₁)
  exact ⟨Subtype.val ⁻¹' (O₀ ∩ W), _, (hO₀.inter hW).preimage continuous_subtype_val, hj.isOpen_range,
    ⟨hxy ▸ hxU, hxy ▸ hx⟩, ⟨g.symm.trans hj.toIsEmbedding.toHomeomorph⟩⟩

private theorem remove_discs_univ {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) (hb : ∀ x : S, IsInteriorPoint x) [ConnectedSpace S]
    {ι : Type*} [Finite ι] {P : ι → Set S} (hP : ∀ i, IsClosedDisc (P i))
    (hd : Pairwise fun i j => Disjoint (P i) (P j)) :
    IsClosed (⋃ i, discInt (P i))ᶜ ∧ IsSurface ↥(⋃ i, discInt (P i))ᶜ ∧
      bd ↥(⋃ i, discInt (P i))ᶜ = Subtype.val ⁻¹' (⋃ i, discBd (P i)) ∧
      ConnectedSpace ↥(⋃ i, discInt (P i))ᶜ ∧
      cuffs ↥(⋃ i, discInt (P i))ᶜ =
        range fun i => (Subtype.val ⁻¹' discBd (P i) : Set ↥(⋃ i, discInt (P i))ᶜ) := by
  classical
  have hman : ∀ x : S, IsManifoldPoint x := hS.2.2
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hPc : ∀ i, IsClosed (P i) := fun i => (hP i).isClosed
  have hopen : IsOpen (⋃ i, discInt (P i)) := isOpen_iUnion fun i => (hP i).isOpen_discInt hman
  set X : Set S := (⋃ i, discInt (P i))ᶜ with hX
  have hXc : IsClosed X := hopen.isClosed_compl
  have hdB : ∀ i, discBd (P i) ⊆ P i := fun i => by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hXd : ∀ {z i}, z ∈ X → z ∈ P i → z ∈ discBd (P i) := fun {z i} hz hi => by
    by_contra hn
    exact hz (mem_iUnion.2 ⟨i, hi, hn⟩)
  have hBX : ∀ {z i}, z ∈ discBd (P i) → z ∈ X := fun {z i} hz hu => by
    obtain ⟨j, hj, hn⟩ := mem_iUnion.1 hu
    by_cases hij : j = i
    · subst hij
      exact hn hz
    · exact Set.disjoint_left.mp (hd hij) hj (hdB i hz)
  let W : ι → Set S := fun i => (⋃ j ∈ {j | j ≠ i}, P j)ᶜ
  have hWo : ∀ i, IsOpen (W i) := fun i => ((Set.toFinite _).isClosed_biUnion fun j _ => hPc j).isOpen_compl
  have hW : ∀ i, X ∩ W i = (discInt (P i))ᶜ ∩ W i := fun i => by
    ext z
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨fun h => h₁ (mem_iUnion.2 ⟨i, h⟩), h₂⟩
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun hu => ?_, h₂⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hu
      by_cases hij : j = i
      · exact h₁ (hij ▸ hj)
      · exact h₂ (mem_iUnion₂.2 ⟨j, hij, hj.1⟩)
  have hPW : ∀ {z i}, z ∈ P i → z ∈ W i := fun {z i} hz hu => by
    obtain ⟨j, hj, hm⟩ := mem_iUnion₂.1 hu
    exact Set.disjoint_left.mp (hd hj) hm hz
  have hmem : ∀ i, IsSurface ↥(discInt (P i))ᶜ ∧
      bd ↥(discInt (P i))ᶜ = Subtype.val ⁻¹' (bd S ∪ discBd (P i)) := fun i => by
    obtain ⟨-, h₂, h₃⟩ := remove_disc_univ hS (hP i) (fun x _ => hb x)
    exact ⟨h₂, h₃⟩
  have hoff : ∀ x : ↥X, (∀ i, x.1 ∉ P i) → IsInteriorPoint x := fun x hn => by
    have hint' : IsInteriorPoint (⟨x.1, mem_univ _⟩ : ↥(univ : Set S)) :=
      (isInteriorPoint_homeomorph_iff (Homeomorph.Set.univ S) ⟨x.1, mem_univ _⟩).mp (hb x.1)
    have hWW : IsOpen (⋃ j, P j)ᶜ := (isClosed_iUnion_of_finite hPc).isOpen_compl
    refine isInteriorPoint_congr_local_univ (X := univ) (Y := X) hWW ?_ rfl (by simpa using hn) hint'
    ext z
    simp only [mem_inter_iff, mem_univ, true_and, mem_compl_iff]
    constructor
    · intro h
      refine ⟨fun hu => ?_, h⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hu
      exact h (mem_iUnion.2 ⟨j, hj.1⟩)
    · exact fun h => h.2
  have hbdX : bd ↥X = Subtype.val ⁻¹' (⋃ i, discBd (P i)) := by
    ext x
    constructor
    · intro hx
      by_contra hn
      refine hx (hoff x fun i hi => hn (mem_iUnion.2 ⟨i, hXd x.2 hi⟩))
    · intro hx hi
      obtain ⟨i, hxi⟩ := mem_iUnion.1 hx
      have hy : (⟨x.1, fun h => h.2 hxi⟩ : ↥(discInt (P i))ᶜ) ∈ bd ↥(discInt (P i))ᶜ := by
        rw [(hmem i).2]
        exact Or.inr hxi
      exact hy (isInteriorPoint_congr_local_univ (W := W i) (hWo i) (hW i) rfl (hPW (hdB i hxi)) hi)
  have hsurf : IsSurface ↥X := by
    have : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXc.isCompact
    refine ⟨inferInstance, inferInstance, fun x => ?_⟩
    by_cases hi : ∃ i, x.1 ∈ P i
    · obtain ⟨i, hi⟩ := hi
      have hb' : x.1 ∈ discBd (P i) := hXd x.2 hi
      exact isManifoldPoint_congr_local_univ (hWo i) (hW i).symm rfl (hPW hi)
        ((hmem i).1.2.2 ⟨x.1, fun h => h.2 hb'⟩)
    · push Not at hi
      exact (hoff x hi).isManifoldPoint
  have hne : ∀ i, (discBd (P i)).Nonempty := fun i => (IsOArc.isConnected' (hP i).isOArc_discBd).nonempty
  have hXne : X.Nonempty := by
    by_cases hι : Nonempty ι
    · obtain ⟨i⟩ := hι
      obtain ⟨z, hz⟩ := hne i
      exact ⟨z, hBX hz⟩
    · have : IsEmpty ι := not_nonempty_iff.mp hι
      obtain ⟨z⟩ : Nonempty S := inferInstance
      exact ⟨z, by simp [hX]⟩
  have hcon : ConnectedSpace ↥X := by
    have hPX : ∀ i, P i ∩ X = discBd (P i) := fun i => by
      ext z
      exact ⟨fun h => hXd h.2 h.1, fun h => ⟨hdB i h, hBX h⟩⟩
    refine connected_compl hXc hXne (Set.finite_range P) ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩
      exact hPc i
    · rintro _ ⟨i, rfl⟩
      rw [hPX]
      exact (IsOArc.isConnected' (hP i).isOArc_discBd).isPreconnected
    · rintro _ ⟨i, rfl⟩
      rw [hPX]
      exact hne i
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne'
      exact hd fun h => hne' (h ▸ rfl)
    · ext z
      simp only [mem_union, mem_sUnion, mem_range, exists_exists_eq_and, mem_univ, iff_true]
      by_cases hz : z ∈ X
      · exact Or.inl hz
      · have : z ∈ ⋃ i, discInt (P i) := not_not.mp hz
        obtain ⟨i, hi⟩ := mem_iUnion.1 this
        exact Or.inr ⟨i, hi.1⟩
  refine ⟨hXc, hsurf, hbdX, hcon, ?_⟩
  have hu : (Subtype.val ⁻¹' (⋃ i, discBd (P i)) : Set ↥X) =
      ⋃ i, (Subtype.val ⁻¹' discBd (P i) : Set ↥X) := preimage_iUnion
  rw [cuffs, hbdX, hu]
  refine GM12.componentsIn_iUnion_disjoint_closed (fun i => (Subtype.val ⁻¹' discBd (P i) : Set ↥X)) ?_ ?_ ?_ ?_
  · exact fun i => (hP i).isOArc_discBd.isCompact.isClosed.preimage continuous_subtype_val
  · intro i
    refine (IsOArc.isConnected' (hP i).isOArc_discBd).isPreconnected.preimage_of_isClosedMap Subtype.val_injective
      hXc.isClosedEmbedding_subtypeVal.isClosedMap ?_
    intro z hz
    exact ⟨⟨z, hBX hz⟩, rfl⟩
  · intro i
    obtain ⟨z, hz⟩ := hne i
    exact ⟨⟨z, hBX hz⟩, hz⟩
  · intro i j hij
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    exact Set.disjoint_left.mp (hd hij) (hdB i hz) (hdB j hz')

/-- Auxiliary form of **5.3** (Graph Minors XXII, pages 540–542) with explicit union graphs
`G` and `G'`. -/
theorem lemma_5_3_aux
     (p : ℕ) :
    ∃ θ > p, ∀ {S : Type w} [TopologicalSpace S] [T2Space S],
      (hS : IsClosedSurface S) → (hConn : ConnectedSpace S) →
      ∀ {α : Type u} {β : Type v}
        (D D' : Surface.Drawing S) (ord t : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S)
        (d : Set S → Set S → ℕ)
        (F : Fin t → Set S)
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (G Γ_sub K G' Γ'_sub L' : Graph α β) (Z : Set α),
      HasTangleMetric D ord T d → θ ≤ ord →
      (∀ F₀ : Set S, IsOArc F₀ → D.IsNormal F₀ → (F₀ ∩ D.V).ncard < ord →
        IsTangleIns D T F₀ (ins F₀)) →
      (∀ i : Fin t, IsOArc (F i) ∧ D.IsNormal (F i)) →
      Pairwise (fun i j => Disjoint (ins (F i)) (ins (F j))) →
      ιV '' ((⋃ i : Fin t, F i) ∩ D.V) ⊆ Z →
      Z ⊆ ιV '' ((⋃ i : Fin t, F i) ∩ D.V) ∪ V(K) →
      Z.ncard ≤ p →
      (∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ D.IsNormal F₀ ∧
        (F₀ ∩ D.V).ncard < (F i ∩ D.V).ncard ∧ ins (F i) ⊆ ins F₀) →
      (∀ i j : Fin t, i ≠ j → θ ≤ subsetTangleDist D ord d (ins (F i)) (ins (F j))) →
      (∀ (i : Fin t), ∀ v ∈ D.V ∩ ιV ⁻¹' V(K), θ ≤ subsetTangleDist D ord d (ins (F i)) {v}) →
      let S_sub : Set S := (⋃ i : Fin t, (ins (F i) \ F i))ᶜ
      let R : Set S := {x : S | ∃ z ∈ D.A, x ∈ z ∧ ∀ v ∈ D.V ∩ ιV ⁻¹' V(K), θ ≤ d z {v}}
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ_sub ≤ G → K ≤ G → V(G) = V(Γ_sub) ∪ V(K) → E(G) = E(Γ_sub) ∪ E(K) →
      Γ'_sub ≤ G' → K ≤ G' → V(G') = V(Γ'_sub) ∪ V(K) → E(G') = E(Γ'_sub) ∪ E(K) →
      GM09.subgraphInter G Γ_sub K = GM09.subgraphInter G' Γ'_sub K →
      Γ_sub = (D.interSet S_sub).toEmbeddedGraph ιV ιE →
      Γ'_sub = (D'.interSet S_sub).toEmbeddedGraph ιV ιE →
      IsVariant D D' (R ∩ S_sub) →
      (∀ i : Fin t, D.V ∩ ins (F i) = D'.V ∩ ins (F i)) →
      L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ GM09.subgraphInter G L K ≤ L' := by
  classical
  obtain ⟨h, hh, h42⟩ := theorem_4_2_proof.{u, v, w} p
  use 2 * p + 4 * h + 15, by omega
  intro S _ _ hS hConn α β D D' ord t T ins d F ιV ιE G Γ_sub K G' Γ'_sub L' Z
    hMetric hord hIns_fn hF_props hIns_disj hZ_ge hZ_le hZp h_i h_ii h_iii
    S_sub R hVG hEG hVG' hEG'
    hΓG hKG hVG_union hEG_union hΓ'G' hKG' hVG'_union hEG'_union hInter
    hΓ_sub hΓ'_sub hVar hD_ins_eq hL'
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let ins_F : Fin t → Set S := fun i => ins (F i)
  have hF_oArc : ∀ i : Fin t, IsOArc (F i) := fun i => (hF_props i).1
  have hF_norm : ∀ i : Fin t, D.IsNormal (F i) := fun i => (hF_props i).2
  have hF_card : ∀ i : Fin t, (F i ∩ D.V).ncard ≤ p := fun i => by
    have hsub : ιV '' (F i ∩ D.V) ⊆ Z :=
      (image_mono (inter_subset_inter_left D.V (subset_iUnion F i))).trans hZ_ge
    have hfinZ : Z.Finite := by
      have hVK_fin : V(K).Finite := hVG.subset (hVG_union ▸ subset_union_right)
      exact ((D.finite_V.subset inter_subset_right).image ιV |>.union hVK_fin).subset hZ_le
    rw [← ncard_image_of_injective _ ιV.injective]
    exact (ncard_le_ncard hsub hfinZ).trans hZp
  have hIns : ∀ i : Fin t, IsTangleIns D T (F i) (ins_F i) := fun i => by
    refine hIns_fn (F i) (hF_oArc i) (hF_norm i) ?_
    have := hF_card i
    omega
  have hF_discBd : ∀ i : Fin t, discBd (ins_F i) = F i := fun i => by
    rw [← IsClosedDisc.subBd_eq_discBd hS (hIns i).1, (hIns i).2.1]
  have hS_sub_eq : S_sub = (⋃ i : Fin t, discInt (ins_F i))ᶜ := by
    change (⋃ i : Fin t, (ins_F i \ F i))ᶜ = (⋃ i : Fin t, (ins_F i \ discBd (ins_F i)))ᶜ
    simp_rw [hF_discBd]
  have hr_ex : ∀ i : Fin t, ∃ r_i ∈ D.R, (r_i ∩ F i).Nonempty := fun i =>
    exists_region_inter_normal_oArc hS D (hF_oArc i) (hF_norm i)
  choose r hr hr_F using hr_ex
  have hr_ins : ∀ i : Fin t, (r i ∩ ins_F i).Nonempty := fun i => by
    obtain ⟨q, hqr, hqF⟩ := hr_F i
    refine ⟨q, hqr, ?_⟩
    rw [← hF_discBd i] at hqF
    exact Surface.discBd_subset (ins_F i) hqF
  have hClaim2 := fun i => lemma_5_3_claim_2 hS hConn r hMetric hord hr i
  choose C Λ_disc S_disc hS_cl hC_sub hC_cir hS_disc hΛ_bd hS_bd hS_diff hZone hS_bd_U
    hS_ii_full hS_iii hr_sub using hClaim2
  have hS_ii : ∀ (i : Fin t) (x : Set S), x ∈ D.A → (x ∩ S_disc i).Nonempty →
      d (r i) x ≤ p + 2 * h + 7 := fun i x hx hne => (hS_ii_full i x hx hne).2
  have hClaim3 : ∀ {i j : Fin t}, i ≠ j → Disjoint (S_disc i) (S_disc j) :=
    fun hij => lemma_5_3_claim_3 hS hConn hMetric hr hr_ins hS_ii h_ii hij
  set VK : Set S := D.V ∩ ιV ⁻¹' V(K)
  have hClaim4 := fun i =>
    lemma_5_3_claim_4 hS hConn hMetric hord hF_oArc hF_norm hF_card hIns hr hr_ins
      inter_subset_left h_iii hS_ii hS_iii i
  -- Build the surface `↥S_sub` and capped surface `cap : IsCappedSurface ↥S_sub S`
  have hSurf_S : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨hS_sub_closed, hS'_surf, hbd_S_sub, hConn_S_sub, hcuffs_S_sub⟩ :=
    remove_discs_univ hSurf_S hS.2.2 (fun i => (hIns i).1) hIns_disj
  rw [← hS_sub_eq] at hS_sub_closed hS'_surf hbd_S_sub hConn_S_sub hcuffs_S_sub
  have hclo_ins : ∀ i : Fin t, closure (discInt (ins_F i)) = ins_F i := fun i =>
    Subset.antisymm (closure_minimal (discInt_subset _) (hIns i).1.isClosed)
      (hIns i).1.subset_closure_discInt
  have hbW : ∀ i : Fin t, F i ⊆ S_sub := fun i x hx hu => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hij : i = j
    · subst hij
      exact hj.2 hx
    · exact disjoint_left.mp (hIns_disj hij) (Surface.discBd_subset (ins_F i) (hF_discBd i ▸ hx)) hj.1
  have hinj_cuff : ∀ {i j : Fin t},
      (Subtype.val ⁻¹' F i : Set ↥S_sub) = Subtype.val ⁻¹' F j → i = j := by
    intro i j he
    by_contra hij
    obtain ⟨y, hy⟩ := (IsOArc.isConnected' (hF_oArc i)).nonempty
    have h1 : (⟨y, hbW i hy⟩ : ↥S_sub) ∈ (Subtype.val ⁻¹' F j : Set ↥S_sub) := by
      rw [← he]; exact hy
    exact disjoint_left.mp (hIns_disj hij)
      (Surface.discBd_subset (ins_F i) (hF_discBd i ▸ hy))
      (Surface.discBd_subset (ins_F j) (hF_discBd j ▸ h1))
  have hcuffs_eq : cuffs ↥S_sub = range (fun i : Fin t => (Subtype.val ⁻¹' F i : Set ↥S_sub)) := by
    rw [hcuffs_S_sub]
    simp_rw [hF_discBd]
  have hbd_eq : bd ↥S_sub = Subtype.val ⁻¹' (⋃ i : Fin t, F i) := by
    rw [hbd_S_sub]
    simp_rw [hF_discBd]
  let cd : Set ↥S_sub → Set S := fun Θ =>
    {x | ∃ i : Fin t, Θ = Subtype.val ⁻¹' F i ∧ x ∈ discInt (ins_F i)}
  have hcd : ∀ i : Fin t, cd (Subtype.val ⁻¹' F i) = discInt (ins_F i) := fun i => by
    ext x
    constructor
    · rintro ⟨j, he, hx⟩
      rw [hinj_cuff he]; exact hx
    · exact fun hx => ⟨i, rfl, hx⟩
  have hS_sub_compl : S_subᶜ = ⋃ i : Fin t, discInt (ins_F i) := by
    rw [hS_sub_eq, compl_compl]
  let cap : GM19.IsCappedSurface ↥S_sub S :=
    { isSurface := hSurf_S
      connected := hConn
      bd_empty := by
        ext x
        simp only [mem_empty_iff_false, iff_false]
        exact fun hb => hb (hS.2.2 x)
      emb := Subtype.val
      isEmbedding := IsEmbedding.subtypeVal
      cuffDisc := cd
      cuffDisc_closedDisc := by
        rintro Θ hΘ
        rw [hcuffs_eq] at hΘ
        obtain ⟨i, rfl⟩ := hΘ
        rw [hcd, hclo_ins]
        exact (hIns i).1
      cuffDisc_bd := by
        rintro Θ hΘ
        rw [hcuffs_eq] at hΘ
        obtain ⟨i, rfl⟩ := hΘ
        rw [hcd, hclo_ins, hF_discBd, Subtype.image_preimage_coe, inter_eq_right.mpr (hbW i)]
      cuffDisc_disjoint := by
        rintro Θ₁ hΘ₁ Θ₂ hΘ₂ hne
        rw [hcuffs_eq] at hΘ₁ hΘ₂
        obtain ⟨i, rfl⟩ := hΘ₁
        obtain ⟨j, rfl⟩ := hΘ₂
        rw [hcd, hcd, hclo_ins, hclo_ins]
        exact hIns_disj fun h => hne (by rw [h])
      compl_eq := by
        rw [Subtype.range_coe, hS_sub_compl]
        ext x
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨i, hx⟩
          refine ⟨Subtype.val ⁻¹' F i, ?_, by rw [hcd]; exact hx⟩
          rw [hcuffs_eq]
          exact ⟨i, rfl⟩
        · rintro ⟨Θ, hΘ, hx⟩
          rw [hcuffs_eq] at hΘ
          obtain ⟨i, rfl⟩ := hΘ
          rw [hcd] at hx
          exact ⟨i, hx⟩ }
  -- Pull back `D.interSet S_sub` and `D'.interSet S_sub` to `↥S_sub`
  let D_pull := drawingPullSubtype (D.interSet S_sub) hS_sub_closed (GM11.interSet_U_subset hS_sub_closed)
  let D'_pull := drawingPullSubtype (D'.interSet S_sub) hS_sub_closed (GM11.interSet_U_subset hS_sub_closed)
  let embV : ↥S_sub ↪ S := ⟨Subtype.val, Subtype.val_injective⟩
  let embE : Set ↥S_sub ↪ Set S := ⟨image Subtype.val, image_injective.mpr Subtype.val_injective⟩
  let ιV' : ↥S_sub ↪ α := embV.trans ιV
  let ιE' : Set ↥S_sub ↪ β := embE.trans ιE
  have hΓ_pull : Γ_sub = D_pull.toEmbeddedGraph ιV' ιE' := by
    rw [hΓ_sub, ← toEmbeddedGraph_drawingPullSubtype (D.interSet S_sub) hS_sub_closed
      (GM11.interSet_U_subset hS_sub_closed) ιV ιE]
  have hΓ'_pull : Γ'_sub = D'_pull.toEmbeddedGraph ιV' ιE' := by
    rw [hΓ'_sub, ← toEmbeddedGraph_drawingPullSubtype (D'.interSet S_sub) hS_sub_closed
      (GM11.interSet_U_subset hS_sub_closed) ιV ιE]
  have hDU_S_sub : (D.interSet S_sub).U = D.U ∩ S_sub := by
    rw [hS_sub_eq]
    exact interSet_U_eq_of_normal_discs hS D (fun i => (hIns i).1) (fun i => (hIns i).2.1) hF_norm
  have hD_pull_bd : D_pull.U ∩ bd ↥S_sub ⊆ D_pull.V := by
    rintro ⟨x, hxS_sub⟩ ⟨hxU, hxbd⟩
    rw [hbd_eq] at hxbd
    obtain ⟨i, hxFi⟩ := mem_iUnion.mp hxbd
    have hxDU : x ∈ D.U := (GM11.interSet_isSub (Γ := D)).U_subset hxU
    have hxDV : x ∈ D.V := hF_norm i ⟨hxFi, hxDU⟩
    exact GM11.mem_interSet_V hxDV hxS_sub
  have hDV_bd_eq : D'_pull.V ∩ bd ↥S_sub = D_pull.V ∩ bd ↥S_sub := by
    ext ⟨x, hxS_sub⟩
    simp only [mem_inter_iff, hbd_eq, mem_preimage, mem_iUnion]
    change (x ∈ (D'.interSet S_sub).V ∧ ∃ i, x ∈ F i) ↔ (x ∈ (D.interSet S_sub).V ∧ ∃ i, x ∈ F i)
    rw [GM11.mem_interSet_V_iff hS_sub_closed, GM11.mem_interSet_V_iff hS_sub_closed]
    constructor
    · rintro ⟨⟨hxV', _⟩, i, hxFi⟩
      have hx_ins : x ∈ ins_F i := Surface.discBd_subset (ins_F i) (hF_discBd i ▸ hxFi)
      have hxV : x ∈ D.V ∩ ins_F i := by
        rw [hD_ins_eq i]
        exact ⟨hxV', hx_ins⟩
      exact ⟨⟨hxV.1, hxS_sub⟩, i, hxFi⟩
    · rintro ⟨⟨hxV, _⟩, i, hxFi⟩
      have hx_ins : x ∈ ins_F i := Surface.discBd_subset (ins_F i) (hF_discBd i ▸ hxFi)
      have hxV' : x ∈ D'.V ∩ ins_F i := by
        rw [← hD_ins_eq i]
        exact ⟨hxV, hx_ins⟩
      exact ⟨⟨hxV'.1, hxS_sub⟩, i, hxFi⟩
  -- Define `S_sleeve : Set ↥S_sub → Set S`
  let S_sleeve : Set ↥S_sub → Set S := fun C_cuff =>
    if hC : ∃ i : Fin t, C_cuff = Subtype.val ⁻¹' F i then S_disc hC.choose else ∅
  have hS_sleeve_eq : ∀ i : Fin t, S_sleeve (Subtype.val ⁻¹' F i) = S_disc i := fun i => by
    have hex : ∃ j : Fin t, (Subtype.val ⁻¹' F i : Set ↥S_sub) = Subtype.val ⁻¹' F j := ⟨i, rfl⟩
    change (if hC : ∃ j : Fin t, (Subtype.val ⁻¹' F i : Set ↥S_sub) = Subtype.val ⁻¹' F j
      then S_disc hC.choose else ∅) = S_disc i
    rw [dif_pos hex, hinj_cuff hex.choose_spec.symm]
  have hS_sub_S_sub : ∀ i : Fin t, S_disc i \ discInt (ins_F i) ⊆ S_sub :=
      fun i x ⟨hxS, hx_not_int⟩ hu => by
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hu
    have hxj' : x ∈ discInt (ins_F j) := ⟨hxj.1, hF_discBd j ▸ hxj.2⟩
    by_cases hij : j = i
    · subst hij
      exact hx_not_int hxj'
    · exact disjoint_left.mp (hClaim3 (Ne.symm hij)) hxS ((hClaim4 j).2 hxj.1).1
  have hSleeve : ∀ C_cuff ∈ cuffs ↥S_sub, IsSleeve cap D_pull C_cuff (S_sleeve C_cuff) := by
    rintro C_cuff hC_cuff
    have hC_cuff' := hC_cuff
    rw [hcuffs_eq] at hC_cuff'
    obtain ⟨i, rfl⟩ := hC_cuff'
    rw [hS_sleeve_eq i]
    refine ⟨hC_cuff, hS_disc i, ?_, ?_, ?_⟩
    · have hU_img : cap.emb '' D_pull.U = (D.interSet S_sub).U := by
        ext x
        exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy,
          fun hx => ⟨⟨x, GM11.interSet_U_subset hS_sub_closed hx⟩, hx, rfl⟩⟩
      rw [hU_img, hDU_S_sub]
      intro x hx_bd
      have hxS : x ∈ S_disc i := by
        rw [IsClosedDisc.subBd_eq_discBd hS (hS_disc i)] at hx_bd
        exact Surface.discBd_subset (S_disc i) hx_bd
      have hx_not_int : x ∉ discInt (ins_F i) := fun hx_int =>
        ((hClaim4 i).2 hx_int.1).2 hx_bd
      exact ⟨hS_bd_U i hx_bd, hS_sub_S_sub i ⟨hxS, hx_not_int⟩⟩
    · show cd (Subtype.val ⁻¹' F i) ⊆ S_disc i
      rw [hcd i]
      exact (discInt_subset (ins_F i)).trans fun x hx => ((hClaim4 i).2 hx).1
    · show S_disc i ∩ (Subtype.val '' bd ↥S_sub) = Subtype.val '' (Subtype.val ⁻¹' F i)
      rw [hbd_eq, Subtype.image_preimage_coe, Subtype.image_preimage_coe,
        inter_eq_right.mpr (hbW i)]
      ext x
      constructor
      · rintro ⟨hxS, hx_pre⟩
        obtain ⟨j, hxj⟩ := mem_iUnion.mp hx_pre.2
        by_cases hij : j = i
        · rwa [← hij]
        · exfalso
          have hxj_S : x ∈ S_disc j :=
            ((hClaim4 j).2 (Surface.discBd_subset (ins_F j) (hF_discBd j ▸ hxj))).1
          exact disjoint_left.mp (hClaim3 (Ne.symm hij)) hxS hxj_S
      · intro hxFi
        exact ⟨((hClaim4 i).2 (Surface.discBd_subset (ins_F i) (hF_discBd i ▸ hxFi))).1,
          hbW i hxFi, mem_iUnion.mpr ⟨i, hxFi⟩⟩
  have hSleeve_disj : ∀ C₁ ∈ cuffs ↥S_sub, ∀ C₂ ∈ cuffs ↥S_sub, C₁ ≠ C₂ →
      Disjoint (S_sleeve C₁) (S_sleeve C₂) := by
    rintro C₁ hC₁ C₂ hC₂ hne
    rw [hcuffs_eq] at hC₁ hC₂
    obtain ⟨i, rfl⟩ := hC₁
    obtain ⟨j, rfl⟩ := hC₂
    rw [hS_sleeve_eq i, hS_sleeve_eq j]
    exact hClaim3 fun hij => hne (by rw [hij])
  have hPaths : ∀ C_cuff ∈ cuffs ↥S_sub, ∃ P : ↑(D_pull.V ∩ C_cuff) → Graph ↥S_sub (Set ↥S_sub),
      (∀ x : ↑(D_pull.V ∩ C_cuff), ∃ y ∈ D_pull.V ∩ cap.emb ⁻¹' subBd (S_sleeve C_cuff),
        GM09.IsGraphPathWithEnds D_pull.toGraph (P x) x.1 y) ∧
      Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂)) := by
    rintro C_cuff hC_cuff
    rw [hcuffs_eq] at hC_cuff
    obtain ⟨i, rfl⟩ := hC_cuff
    rw [hS_sleeve_eq i]
    exact lemma_5_3_claim_5 hS hConn hh hMetric hord hF_norm hF_card hIns hIns_fn hr h_i
      hS_cl hC_sub hS_disc hS_bd hZone (fun j => (hClaim4 j).2) hS_sub_closed i (hS_sub_S_sub i)
  have hmap_pull : drawingMapEmb D_pull (isClosedEmbedding_w hS'_surf cap) = D.interSet S_sub :=
    drawingMapEmb_drawingPullSubtype (D.interSet S_sub) hS_sub_closed (GM11.interSet_U_subset hS_sub_closed)
  set Y_cap : Set S :=
    cap.emb '' ((ιV' ⁻¹' (V(Γ_sub) ∩ V(K))) ∪ (D_pull.V ∩ bd ↥S_sub))
  have hY_cap_sub : Y_cap ⊆ VK ∪ ⋃ i : Fin t, ins_F i := by
    rintro x ⟨⟨x, hxS_sub⟩, hx_in, rfl⟩
    rcases hx_in with hx_VK | ⟨_, hx_bd⟩
    · left
      have hx_Γ : ιV x ∈ V(Γ_sub) := hx_VK.1
      rw [hΓ_sub] at hx_Γ
      obtain ⟨w, hwV, hw_eq⟩ := hx_Γ
      obtain rfl : w = x := ιV.injective hw_eq
      exact ⟨(GM11.mem_interSet_V_iff hS_sub_closed).mp hwV |>.1, hx_VK.2⟩
    · right
      rw [hbd_eq] at hx_bd
      obtain ⟨i, hxFi⟩ := mem_iUnion.mp hx_bd
      exact mem_iUnion.mpr ⟨i, Surface.discBd_subset (ins_F i) (hF_discBd i ▸ hxFi)⟩
  have hVK_cap_sub : cap.emb '' (ιV' ⁻¹' (V(Γ_sub) ∩ V(K))) ⊆ VK := by
    rintro x ⟨⟨x, hxS_sub⟩, hx_VK, rfl⟩
    have hx_Γ : ιV x ∈ V(Γ_sub) := hx_VK.1
    rw [hΓ_sub] at hx_Γ
    obtain ⟨w, hwV, hw_eq⟩ := hx_Γ
    obtain rfl : w = x := ιV.injective hw_eq
    exact ⟨(GM11.mem_interSet_V_iff hS_sub_closed).mp hwV |>.1, hx_VK.2⟩
  have hSleeve_T : ∀ C_cuff ∈ cuffs ↥S_sub,
      subBd (S_sleeve C_cuff) ⊆
        cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D_pull (isClosedEmbedding_w hS'_surf cap))
          Y_cap h) ∧
      Disjoint (S_sleeve C_cuff) (cap.emb '' (ιV' ⁻¹' (V(Γ_sub) ∩ V(K)))) := by
    rintro C_cuff hC_cuff
    rw [hcuffs_eq] at hC_cuff
    obtain ⟨i, rfl⟩ := hC_cuff
    rw [hS_sleeve_eq i, hmap_pull]
    refine ⟨?_, Disjoint.mono_right hVK_cap_sub (hClaim4 i).1⟩
    have h7 := lemma_5_3_claim_7 hS hConn hh hMetric hord hF_oArc hF_norm hF_card hIns hr hr_ins
      inter_subset_left h_ii h_iii hS_ii hS_iii hS_disc hY_cap_sub i
    change subBd (S_disc i) ⊆ insulatedSet (D.interSet (⋃ j : Fin t, discInt (ins_F j))ᶜ) Y_cap h at h7
    rw [← hS_sub_eq] at h7
    intro x hx_bd
    have hxS : x ∈ S_disc i := by
      rw [IsClosedDisc.subBd_eq_discBd hS (hS_disc i)] at hx_bd
      exact Surface.discBd_subset (S_disc i) hx_bd
    have hx_not_int : x ∉ discInt (ins_F i) := fun hx_int =>
      ((hClaim4 i).2 hx_int.1).2 hx_bd
    have hxS_sub : x ∈ S_sub := hS_sub_S_sub i ⟨hxS, hx_not_int⟩
    exact ⟨⟨x, hxS_sub⟩, h7 hx_bd, rfl⟩
  have hVar_pull : IsVariant D_pull D'_pull
      ((⋃ C_cuff ∈ cuffs ↥S_sub, cap.emb ⁻¹' S_sleeve C_cuff) ∪
        cap.emb ⁻¹' insulatedSet (drawingMapEmb D_pull (isClosedEmbedding_w hS'_surf cap))
          Y_cap h) := by
    rw [hmap_pull]
    have hClaim6 := lemma_5_3_claim_6 hS hConn hh hMetric hord hF_oArc hF_norm hF_card hIns
      hr hr_ins inter_subset_left hS_iii hY_cap_sub
    change R ∩ (⋃ i : Fin t, discInt (ins_F i))ᶜ ⊆
      ((⋃ i : Fin t, S_disc i) ∩ (⋃ i : Fin t, discInt (ins_F i))ᶜ) ∪
        (insulatedSet (D.interSet (⋃ i : Fin t, discInt (ins_F i))ᶜ) Y_cap h ∩
          (⋃ i : Fin t, discInt (ins_F i))ᶜ) at hClaim6
    rw [← hS_sub_eq] at hClaim6
    set W_pull : Set ↥S_sub :=
      (⋃ C_cuff ∈ cuffs ↥S_sub, cap.emb ⁻¹' S_sleeve C_cuff) ∪
        cap.emb ⁻¹' insulatedSet (D.interSet S_sub) Y_cap h
    have hR_sub_W : Subtype.val ⁻¹' (R ∩ S_sub) ⊆ W_pull := by
      rintro ⟨x, hxS_sub⟩ hxR
      rcases hClaim6 hxR with ⟨hxS, _⟩ | ⟨hxT, _⟩
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxS
        left
        refine mem_iUnion₂.mpr ⟨Subtype.val ⁻¹' F i, ?_, ?_⟩
        · rw [hcuffs_eq]; exact ⟨i, rfl⟩
        · change x ∈ S_sleeve (Subtype.val ⁻¹' F i)
          rwa [hS_sleeve_eq i]
      · exact Or.inr hxT
    have hV_pull : ∀ P : Surface.Drawing S, (hU : P.U ⊆ S_sub) →
        (drawingPullSubtype P hS_sub_closed hU).V = Subtype.val ⁻¹' P.V := fun _ _ => rfl
    have hE_pull : ∀ P : Surface.Drawing S, (hU : P.U ⊆ S_sub) →
        (drawingPullSubtype P hS_sub_closed hU).E = preimage Subtype.val '' P.E := fun P hU => by
      have hmap_E := drawingMapEmb_E (drawingPullSubtype P hS_sub_closed hU)
        hS_sub_closed.isClosedEmbedding_subtypeVal
      rw [drawingMapEmb_drawingPullSubtype P hS_sub_closed hU] at hmap_E
      rw [hmap_E, image_image]
      ext e'
      simp only [mem_image]
      constructor
      · intro he'
        exact ⟨e', he', preimage_image_eq e' Subtype.val_injective⟩
      · rintro ⟨e₀, he₀, rfl⟩
        rwa [preimage_image_eq e₀ Subtype.val_injective]
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨x, hxS_sub⟩
      simp only [mem_sdiff]
      change (x ∈ (D.interSet S_sub).V ∧ ⟨x, hxS_sub⟩ ∉ W_pull) ↔
        (x ∈ (D'.interSet S_sub).V ∧ ⟨x, hxS_sub⟩ ∉ W_pull)
      rw [GM11.mem_interSet_V_iff hS_sub_closed, GM11.mem_interSet_V_iff hS_sub_closed]
      constructor
      · rintro ⟨⟨hxV, _⟩, hxW⟩
        have hxR : x ∉ R ∩ S_sub := fun h => hxW (hR_sub_W h)
        have hxV' : x ∈ D'.V \ (R ∩ S_sub) := hVar.V_diff_eq ▸ ⟨hxV, hxR⟩
        exact ⟨⟨hxV'.1, hxS_sub⟩, hxW⟩
      · rintro ⟨⟨hxV', _⟩, hxW⟩
        have hxR : x ∉ R ∩ S_sub := fun h => hxW (hR_sub_W h)
        have hxV : x ∈ D.V \ (R ∩ S_sub) := hVar.V_diff_eq.symm ▸ ⟨hxV', hxR⟩
        exact ⟨⟨hxV.1, hxS_sub⟩, hxW⟩
    · rintro e' ⟨he'D, he'D'⟩
      rw [hE_pull (D.interSet S_sub) (GM11.interSet_U_subset hS_sub_closed)] at he'D
      rw [hE_pull (D'.interSet S_sub) (GM11.interSet_U_subset hS_sub_closed)] at he'D'
      obtain ⟨e, he, rfl⟩ := he'D
      rw [GM11.mem_interSet_E_iff] at he
      have he_not_D' : e ∉ D'.E := fun he' =>
        he'D' ⟨e, GM11.mem_interSet_E_iff.mpr ⟨he', he.2⟩, rfl⟩
      have hcl_e : closure e ⊆ R ∩ S_sub :=
        hVar.edge_subset_of_mem_diff_left e ⟨he.1, he_not_D'⟩
      refine Subset.trans ?_ hR_sub_W
      intro z hz
      exact hcl_e (continuous_subtype_val.closure_preimage_subset e hz)
    · rintro e' ⟨he'D', he'D⟩
      rw [hE_pull (D'.interSet S_sub) (GM11.interSet_U_subset hS_sub_closed)] at he'D'
      rw [hE_pull (D.interSet S_sub) (GM11.interSet_U_subset hS_sub_closed)] at he'D
      obtain ⟨e, he', rfl⟩ := he'D'
      rw [GM11.mem_interSet_E_iff] at he'
      have he_not_D : e ∉ D.E := fun he =>
        he'D ⟨e, GM11.mem_interSet_E_iff.mpr ⟨he, he'.2⟩, rfl⟩
      have hcl_e : closure e ⊆ R ∩ S_sub :=
        hVar.edge_subset_of_mem_diff_right e ⟨he'.1, he_not_D⟩
      refine Subset.trans ?_ hR_sub_W
      intro z hz
      exact hcl_e (continuous_subtype_val.closure_preimage_subset e hz)
  have hZ_sub_42 : Z ⊆ V(K) ∪ ιV' '' (D_pull.V ∩ bd ↥S_sub) := by
    intro z hz
    rcases hZ_le hz with ⟨x, ⟨hxF, hxV⟩, rfl⟩ | hzK
    · right
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxF
      have hxS_sub : x ∈ S_sub := hbW i hxi
      refine ⟨⟨x, hxS_sub⟩, ⟨GM11.mem_interSet_V hxV hxS_sub, ?_⟩, rfl⟩
      rw [hbd_eq]
      exact mem_iUnion.mpr ⟨i, hxi⟩
    · exact Or.inl hzK
  exact h42 ↥S_sub S hS'_surf cap G Γ_sub K G' Γ'_sub L'
    hVG hEG hVG' hEG' hΓG hKG hVG_union hEG_union hΓ'G' hKG' hVG'_union hEG'_union hInter
    D_pull D'_pull ιV' ιE' hΓ_pull hΓ'_pull hD_pull_bd hDV_bd_eq
    S_sleeve hSleeve hSleeve_disj hPaths hSleeve_T hVar_pull Z hZ_sub_42 hZp hL'

/-- **5.3** (Graph Minors XXII, page 540):
"For every integer $p \ge 0$ there exists $\theta > p$ with the following property. Let $\Gamma, K$
be subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathcal{T}$ be a respectful tangle in $\Gamma$ of order
$\ge \theta$, with metric $d$. Let $Z \subseteq V(\Gamma \cup K)$ with $|Z| \le p$, and let
$F_1, \ldots, F_t$ be $\Gamma$-normal $O$-arcs, such that
$$(F_1 \cup \cdots \cup F_t) \cap V(\Gamma) \subseteq Z \subseteq
((F_1 \cup \cdots \cup F_t) \cap V(\Gamma)) \cup V(K)$$
and $\text{ins}(F_1), \ldots, \text{ins}(F_t)$ are mutually disjoint. Suppose that
(i) for $1 \le i \le t$, there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with
$|F \cap V(\Gamma)| < |F_i \cap V(\Gamma)|$ and $\text{ins}(F_i) \subseteq \text{ins}(F)$,
(ii) for $1 \le i < j \le t$, $d(\text{ins}(F_i), \text{ins}(F_j)) \ge \theta$,
(iii) for $1 \le i \le k$, $d(\text{ins}(F_i), v) \ge \theta$ for every $v \in V(\Gamma \cap K)$.
Let $R$ be the union of all atoms $z$ of $\Gamma$ with $d(z, v) \ge \theta$ for all
$v \in V(\Gamma \cap K)$, and let
$$\Sigma' = \Sigma \setminus \bigcup_{1 \le i \le t} (\text{ins}(F_i) \setminus F_i).$$
Let $\Gamma'$ be an $(R \cap \Sigma')$-variant of $\Gamma$ in $\Sigma$ with
$\Gamma' \cap K = \Gamma \cap K$ and with $\Gamma \cap \text{ins}(F_i) =
\Gamma' \cap \text{ins}(F_i)$ ($1 \le i \le t$), and let $L' \subseteq (\Gamma' \cap \Sigma') \cup K$.
Then there exists $L \subseteq (\Gamma \cap \Sigma') \cup K$ with the same effect on $Z$ as $L'$,
such that $L \cap K \subseteq L'$." -/
theorem theorem_5_3_proof
     (p : ℕ) :
    ∃ θ : ℕ, p < θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
        {α : Type u} {β : Type v}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (Γ Γ' : Surface.Drawing S) (K L' : Graph α β)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (Z : Set α) (t : ℕ) (F : Fin t → Set S),
        IsClosedSurface S →
        V(K).Finite → E(K).Finite →
        (Γ.toEmbeddedGraph ιV ιE).Compatible K →
        Γ.IsTwoCell →
        θ ≤ ord →
        HasTangleMetric Γ ord T d →
        (∀ F₀ : Set S, IsOArc F₀ → Γ.IsNormal F₀ → (F₀ ∩ Γ.V).ncard < ord →
          IsTangleIns Γ T F₀ (ins F₀)) →
        Z ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) K) →
        Z.ncard ≤ p →
        (∀ i : Fin t, IsOArc (F i) ∧ Γ.IsNormal (F i)) →
        ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ⊆ Z →
        Z ⊆ ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ∪ V(K) →
        Pairwise (fun i j : Fin t => Disjoint (ins (F i)) (ins (F j))) →
        (∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ Γ.IsNormal F₀ ∧
          (F₀ ∩ Γ.V).ncard < (F i ∩ Γ.V).ncard ∧ ins (F i) ⊆ ins F₀) →
        (∀ i j : Fin t, i ≠ j → θ ≤ subsetTangleDist Γ ord d (ins (F i)) (ins (F j))) →
        (∀ i : Fin t, ∀ v ∈ Γ.V, ιV v ∈ V(K) →
          θ ≤ subsetTangleDist Γ ord d (ins (F i)) {v}) →
        let R := ⋃ z ∈ {z ∈ Γ.A | ∀ v ∈ Γ.V, ιV v ∈ V(K) → θ ≤ d z {v}}, z
        let S' := Set.univ \ ⋃ i : Fin t, (ins (F i) \ F i)
        IsVariant Γ Γ' (R ∩ S') →
        (Γ'.toEmbeddedGraph ιV ιE).Compatible K →
        (Γ'.toEmbeddedGraph ιV ιE) ⊓ K = (Γ.toEmbeddedGraph ιV ιE) ⊓ K →
        (∀ i : Fin t, Γ.interSet (ins (F i)) = Γ'.interSet (ins (F i))) →
        L' ≤ graphUnion ((Γ'.interSet S').toEmbeddedGraph ιV ιE) K →
        ∃ L ≤ graphUnion ((Γ.interSet S').toEmbeddedGraph ιV ιE) K,
          effectOn L Z = effectOn L' Z ∧ L ⊓ K ≤ L' := by
  classical
  obtain ⟨θ, hθ, h53⟩ := lemma_5_3_aux.{u, v, w} p
  refine ⟨θ, hθ, ?_⟩
  intro S _ _ hConn α β ιV ιE Γ Γ' K L' ord T ins d Z t F
    hS hVK_fin hEK_fin hComp _ hord hMetric hIns_fn _ hZp
    hF_props hZ_ge hZ_le hIns_disj h_i h_ii h_iii R S'
    hVar hComp' hInter_full hInter_ins hL'
  set S_sub : Set S := (⋃ i : Fin t, (ins (F i) \ F i))ᶜ
  have hS'_eq : S' = S_sub := by
    ext x
    simp [S', S_sub]
  let Γ_sub : Graph α β := (Γ.interSet S_sub).toEmbeddedGraph ιV ιE
  let Γ'_sub : Graph α β := (Γ'.interSet S_sub).toEmbeddedGraph ιV ιE
  let G : Graph α β := graphUnion Γ_sub K
  let G' : Graph α β := graphUnion Γ'_sub K
  have hF_card : ∀ i : Fin t, (F i ∩ Γ.V).ncard ≤ p := fun i => by
    have hsub : ιV '' (F i ∩ Γ.V) ⊆ Z :=
      (image_mono (inter_subset_inter_left Γ.V (subset_iUnion F i))).trans hZ_ge
    have hfinZ : Z.Finite :=
      ((Γ.finite_V.subset inter_subset_right).image ιV |>.union hVK_fin).subset hZ_le
    rw [← ncard_image_of_injective _ ιV.injective]
    exact (ncard_le_ncard hsub hfinZ).trans hZp
  have hIns : ∀ i : Fin t, IsTangleIns Γ T (F i) (ins (F i)) := fun i => by
    refine hIns_fn (F i) (hF_props i).1 (hF_props i).2 ?_
    have := hF_card i
    omega
  have hF_discBd : ∀ i : Fin t, discBd (ins (F i)) = F i := fun i => by
    rw [← IsClosedDisc.subBd_eq_discBd hS (hIns i).1, (hIns i).2.1]
  have hS_sub_eq : S_sub = (⋃ i : Fin t, discInt (ins (F i)))ᶜ := by
    change (⋃ i : Fin t, (ins (F i) \ F i))ᶜ = (⋃ i : Fin t, (ins (F i) \ discBd (ins (F i))))ᶜ
    simp_rw [hF_discBd]
  have hSurf_S : IsSurface S := ⟨hS.1, hS.2.1, fun x => (hS.2.2 x).isManifoldPoint⟩
  obtain ⟨hS_sub_closed, _, _, _, _⟩ :=
    remove_discs_univ hSurf_S hS.2.2 (fun i => (hIns i).1) hIns_disj
  rw [← hS_sub_eq] at hS_sub_closed
  have hΓ_sub_le : Γ_sub ≤ Γ.toEmbeddedGraph ιV ιE :=
    interSet_toEmbeddedGraph_le Γ hS_sub_closed ιV ιE
  have hΓ'_sub_le : Γ'_sub ≤ Γ'.toEmbeddedGraph ιV ιE :=
    interSet_toEmbeddedGraph_le Γ' hS_sub_closed ιV ιE
  have hComp_sub : Γ_sub.Compatible K :=
    fun e he₁ he₂ x y => (hΓ_sub_le.isLink_iff he₁).trans (hComp (hΓ_sub_le.edgeSet_mono he₁) he₂ x y)
  have hComp'_sub : Γ'_sub.Compatible K :=
    fun e he₁ he₂ x y => (hΓ'_sub_le.isLink_iff he₁).trans (hComp' (hΓ'_sub_le.edgeSet_mono he₁) he₂ x y)
  have hΓG : Γ_sub ≤ G := le_graphUnion_left Γ_sub K
  have hKG : K ≤ G := le_graphUnion_right hComp_sub
  have hΓ'G' : Γ'_sub ≤ G' := le_graphUnion_left Γ'_sub K
  have hKG' : K ≤ G' := le_graphUnion_right hComp'_sub
  have hVG_fin : V(G).Finite := ((Γ.interSet S_sub).finite_V.image ιV).union hVK_fin
  have hEG_fin : E(G).Finite := ((Γ.interSet S_sub).finite_edges.image ιE).union hEK_fin
  have hVG'_fin : V(G').Finite := ((Γ'.interSet S_sub).finite_V.image ιV).union hVK_fin
  have hEG'_fin : E(G').Finite := ((Γ'.interSet S_sub).finite_edges.image ιE).union hEK_fin
  have hInter_sub : GM09.subgraphInter G Γ_sub K = GM09.subgraphInter G' Γ'_sub K := by
    refine Graph.ext ?_ fun e x y => ?_
    · change V(Γ_sub) ∩ V(K) = V(Γ'_sub) ∩ V(K)
      ext v
      simp only [Γ_sub, Γ'_sub, Drawing.toEmbeddedGraph, mem_inter_iff, mem_image,
        GM11.mem_interSet_V_iff hS_sub_closed]
      constructor
      · rintro ⟨⟨x, ⟨hxV, hxS⟩, rfl⟩, hxK⟩
        have hv_inter : ιV x ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ K) := ⟨⟨x, hxV, rfl⟩, hxK⟩
        rw [← hInter_full] at hv_inter
        obtain ⟨⟨x', hx'V, hx'_eq⟩, _⟩ := hv_inter
        have hxx' : x' = x := ιV.injective hx'_eq
        subst hxx'
        exact ⟨⟨x', ⟨hx'V, hxS⟩, rfl⟩, hxK⟩
      · rintro ⟨⟨x, ⟨hx'V, hxS⟩, rfl⟩, hxK⟩
        have hv_inter : ιV x ∈ V((Γ'.toEmbeddedGraph ιV ιE) ⊓ K) := ⟨⟨x, hx'V, rfl⟩, hxK⟩
        rw [hInter_full] at hv_inter
        obtain ⟨⟨x', hxV, hx'_eq⟩, _⟩ := hv_inter
        have hxx' : x' = x := ιV.injective hx'_eq
        subst hxx'
        exact ⟨⟨x', ⟨hxV, hxS⟩, rfl⟩, hxK⟩
    · rw [GM09.subgraphInter_isLink hΓG hKG, GM09.subgraphInter_isLink hΓ'G' hKG']
      constructor
      · rintro ⟨hl_sub, hlK⟩
        have hl_full : ((Γ.toEmbeddedGraph ιV ιE) ⊓ K).IsLink e x y :=
          ⟨hΓ_sub_le.isLink_mono hl_sub, hlK⟩
        rw [← hInter_full] at hl_full
        have he_sub : e ∈ E(Γ'_sub) := by
          obtain ⟨e₀, he₀, rfl⟩ := hl_sub.edge_mem
          rw [GM11.mem_interSet_E_iff] at he₀
          obtain ⟨e₁, he₁, he_eq⟩ := hl_full.1.edge_mem
          have he₁₀ : e₁ = e₀ := ιE.injective he_eq
          subst he₁₀
          exact ⟨e₁, GM11.mem_interSet_E_iff.mpr ⟨he₁, he₀.2⟩, rfl⟩
        exact ⟨(hΓ'_sub_le.isLink_iff he_sub).mpr hl_full.1, hlK⟩
      · rintro ⟨hl'_sub, hlK⟩
        have hl'_full : ((Γ'.toEmbeddedGraph ιV ιE) ⊓ K).IsLink e x y :=
          ⟨hΓ'_sub_le.isLink_mono hl'_sub, hlK⟩
        rw [hInter_full] at hl'_full
        have he_sub : e ∈ E(Γ_sub) := by
          obtain ⟨e₀, he₀, rfl⟩ := hl'_sub.edge_mem
          rw [GM11.mem_interSet_E_iff] at he₀
          obtain ⟨e₁, he₁, he_eq⟩ := hl'_full.1.edge_mem
          have he₁₀ : e₁ = e₀ := ιE.injective he_eq
          subst he₁₀
          exact ⟨e₁, GM11.mem_interSet_E_iff.mpr ⟨he₁, he₀.2⟩, rfl⟩
        exact ⟨(hΓ_sub_le.isLink_iff he_sub).mpr hl'_full.1, hlK⟩
  have hR_eq : R = {x : S | ∃ z ∈ Γ.A, x ∈ z ∧ ∀ v ∈ Γ.V ∩ ιV ⁻¹' V(K), θ ≤ d z {v}} := by
    ext x
    simp only [R, mem_iUnion, mem_setOf_eq, exists_prop, mem_inter_iff, mem_preimage]
    exact ⟨fun ⟨z, ⟨hzA, hz_dist⟩, hxz⟩ => ⟨z, hzA, hxz, fun v ⟨hvV, hvK⟩ => hz_dist v hvV hvK⟩,
      fun ⟨z, hzA, hxz, hz_dist⟩ => ⟨z, ⟨hzA, fun v hvV hvK => hz_dist v ⟨hvV, hvK⟩⟩, hxz⟩⟩
  have hD_ins_eq : ∀ i : Fin t, Γ.V ∩ ins (F i) = Γ'.V ∩ ins (F i) := fun i => by
    have hcl_i : IsClosed (ins (F i)) := (hIns i).1.isClosed
    ext x
    simp only [mem_inter_iff, ← GM11.mem_interSet_V_iff hcl_i, hInter_ins i]
  have hVar' : IsVariant Γ Γ' ({x : S | ∃ z ∈ Γ.A, x ∈ z ∧ ∀ v ∈ Γ.V ∩ ιV ⁻¹' V(K), θ ≤ d z {v}} ∩ S_sub) := by
    rwa [← hR_eq, ← hS'_eq]
  have hL'_G' : L' ≤ G' := by
    change L' ≤ graphUnion ((Γ'.interSet S_sub).toEmbeddedGraph ιV ιE) K
    rwa [← hS'_eq]
  obtain ⟨L, hLG, heff, hLK⟩ := h53 hS hConn Γ Γ' ord t T ins d F ιV ιE G Γ_sub K G' Γ'_sub L' Z
    hMetric hord hIns_fn hF_props hIns_disj hZ_ge hZ_le hZp h_i h_ii
    (fun i v ⟨hvV, hvK⟩ => h_iii i v hvV hvK)
    hVG_fin hEG_fin hVG'_fin hEG'_fin
    hΓG hKG rfl rfl hΓ'G' hKG' rfl rfl hInter_sub rfl rfl hVar' hD_ins_eq hL'_G'
  refine ⟨L, ?_, heff, ?_⟩
  · rwa [hS'_eq]
  · have hLK_eq : L ⊓ K = GM09.subgraphInter G L K := by
      refine Graph.ext rfl fun e x y => ?_
      rw [inf_isLink, GM09.subgraphInter_isLink hLG hKG]
    rwa [hLK_eq]

end GraphMinor.GM22
