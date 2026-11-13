module

public import GraphMinor.GM22.Defs
public import GraphMinor.GM09.Basic
import GraphMinor.GM11.CitedResults
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM12.Section79

/-!
# Graph Minors XXII, Section 7: Lemma 7.1 (pages 546–547)

This file formalizes **7.1** (`theorem_7_1`) from Section 7 of:
N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM12 GraphMinor.GM14 Hypergraph

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## Helper lemmas on `subsetTangleDist` and `SystemJ1ToJ6` -/

omit [T2Space S] in
/-- If $a, b \in A(\Gamma)$ have $(a \cap X).\text{Nonempty}$ and $(b \cap Y).\text{Nonempty}$,
then $\text{subsetTangleDist }\Gamma\text{ ord }d\ X\ Y \le d\ a\ b$. -/
theorem subsetTangleDist_le_of_mem {Γ : Drawing S} {ord : ℕ} {d : Set S → Set S → ℕ}
    {X Y a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A)
    (haX : (a ∩ X).Nonempty) (hbY : (b ∩ Y).Nonempty) :
    subsetTangleDist Γ ord d X Y ≤ d a b := by
  classical
  have hex : ∃ a' ∈ Γ.A, ∃ b' ∈ Γ.A, (a' ∩ X).Nonempty ∧ (b' ∩ Y).Nonempty :=
    ⟨a, ha, b, hb, haX, hbY⟩
  simp only [subsetTangleDist, hex, ↓reduceIte]
  exact Nat.sInf_le ⟨a, ha, b, hb, haX, hbY, rfl⟩

omit [T2Space S] in
/-- Monotonicity of `subsetTangleDist`: if $X' \subseteq X$ and $Y' \subseteq Y$, then
$\text{subsetTangleDist }\Gamma\text{ ord }d\ X\ Y \le \text{subsetTangleDist }\Gamma\text{ ord }d\ X'\ Y'$
provided $\forall a \in \Gamma.A, \forall b \in \Gamma.A, d\ a\ b \le \text{ord}$. -/
theorem subsetTangleDist_anti {Γ : Drawing S} {ord : ℕ} {d : Set S → Set S → ℕ}
    (hle : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, d a b ≤ ord)
    {X X' Y Y' : Set S} (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    subsetTangleDist Γ ord d X Y ≤ subsetTangleDist Γ ord d X' Y' := by
  classical
  by_cases hex' : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X').Nonempty ∧ (b ∩ Y').Nonempty
  · have hex : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty := by
      rcases hex' with ⟨a, ha, b, hb, haX', hbY'⟩
      exact ⟨a, ha, b, hb, haX'.mono (inter_subset_inter_right a hX),
        hbY'.mono (inter_subset_inter_right b hY)⟩
    simp only [subsetTangleDist, hex, hex', ↓reduceIte]
    have hne : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
        (a ∩ X').Nonempty ∧ (b ∩ Y').Nonempty ∧ d a b = k}.Nonempty := by
      rcases hex' with ⟨a, ha, b, hb, haX', hbY'⟩
      exact ⟨d a b, a, ha, b, hb, haX', hbY', rfl⟩
    rcases Nat.sInf_mem hne with ⟨a, ha, b, hb, haX', hbY', hdab⟩
    rw [← hdab]
    exact Nat.sInf_le ⟨a, ha, b, hb, haX'.mono (inter_subset_inter_right a hX),
      hbY'.mono (inter_subset_inter_right b hY), rfl⟩
  · simp only [subsetTangleDist, hex', ↓reduceIte]
    split_ifs with hex
    · have hne : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k}.Nonempty := by
        rcases hex with ⟨a, ha, b, hb, haX, hbY⟩
        exact ⟨d a b, a, ha, b, hb, haX, hbY, rfl⟩
      rcases Nat.sInf_mem hne with ⟨a, ha, b, hb, -, -, hdab⟩
      rw [← hdab]
      exact hle a ha b hb
    · exact le_rfl

/-- Under `HasTangleMetric Γ ord T d`, for all $a, b \in A(\Gamma)$, $d(a, b) \le \text{ord}$. -/
theorem HasTangleMetric.le_ord {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) :
    d a b ≤ ord := by
  obtain ⟨-, K, ins, hK, -, hdeq⟩ := hM
  rw [hdeq a ha b hb]
  exact GM11.tangleMetric_le_order hK.2.1 a b

/-- Under `HasTangleMetric Γ ord T d`, $d$ is symmetric on $A(\Gamma)$. -/
theorem HasTangleMetric.comm {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {a b : Set S} (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) :
    d a b = d b a := by
  obtain ⟨-, K, ins, -, -, hdeq⟩ := hM
  rw [hdeq a ha b hb, hdeq b hb a ha]
  exact GM11.tangleMetric_comm Γ K ins ord a b

/-- Under `HasTangleMetric Γ ord T d` on a connected closed surface, $d$ satisfies the triangle
inequality on $A(\Gamma)$. -/
theorem HasTangleMetric.triangle (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) {a b c : Set S}
    (ha : a ∈ Γ.A) (hb : b ∈ Γ.A) (hc : c ∈ Γ.A) :
    d a c ≤ d a b + d b c := by
  obtain ⟨hResp, K, ins, hK, hd, hdeq⟩ := hM
  have hT' : IsPretangle (PaintingOrDrawing.drawing Γ).toHypergraph ord T :=
    hResp.2.1.isPretangle
  have hs := GM11.isSlope_of_derived hS hT' hK.2.1.1 hd
  rw [hdeq a ha c hc, hdeq a ha b hb, hdeq b hb c hc]
  exact GM11.tangleMetric_triangle hS hK.2.1 hs a b c

/-- Under `(J1)`–`(J6)`, for any $A \in \mathcal{A}$ and any atoms $y, z \in A(\Gamma)$ meeting
$D(A)$, we have $d(y, z) \le 3$. -/
theorem SystemJ1ToJ6.dist_le_three_of_meets_D {q : ℕ}
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
    {A : Graph α β} (hA : A ∈ 𝒜) {y z : Set S} (hy : y ∈ Γ.A) (hz : z ∈ Γ.A)
    (hyD : (y ∩ D A).Nonempty) (hzD : (z ∩ D A).Nonempty) :
    d y z ≤ 3 := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  obtain ⟨hDisc, hNorm, hDA_eq⟩ := hJ.disc_D A hA
  have hOArc : IsOArc (subBd (D A)) := by
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS hDisc]
    exact hDisc.isOArc_discBd
  have hV_sub : Γ.V ⊆ ιV ⁻¹' V(R_G.G.toGraph) := by
    intro v hv
    have hvEmb : ιV v ∈ V(Γ.toEmbeddedGraph ιV ιE) := ⟨v, hv, rfl⟩
    have hvDel : ιV v ∈ V(R_G.G.toGraph.deleteVerts W) := hJ.Γ_le.vertexSet_mono hvEmb
    exact (R_G.G.toGraph.deleteVerts_le).vertexSet_mono hvDel
  have hbd_sub : subBd (D A) ∩ Γ.V ⊆ Set.range (πS A) := by
    rw [hJ.π_bar_eq_bd_inter A hA]
    exact inter_subset_inter_right (subBd (D A)) hV_sub
  have hcard_le : (subBd (D A) ∩ Γ.V).ncard ≤ 3 := by
    calc (subBd (D A) ∩ Γ.V).ncard
      _ ≤ (Set.range (πS A)).ncard :=
          ncard_le_ncard hbd_sub (Set.finite_range (πS A))
      _ = πLen A := by
          rw [Set.ncard_range_of_injective (hJ.π_valid A hA).2.2.1, Nat.card_fin]
      _ ≤ 3 := (hJ.π_valid A hA).2.1
  have hcard_lt : (subBd (D A) ∩ Γ.V).ncard < ord := by
    have := hJ.four_le_θ
    have := hJ.θ_le_ord
    omega
  obtain ⟨_, hbd_ins, hmem_T⟩ := hJ.ins_spec (subBd (D A)) hOArc hNorm hcard_lt
  rw [← hDA_eq] at hbd_ins hmem_T
  have hd_le := GM12.dist_le_of_oarc_disc hS hJ.hasMetric hOArc hNorm hcard_lt
    hDisc hbd_ins hmem_T hy hz hyD hzD
  exact hd_le.trans hcard_le

/-- **Graph Minors XXII, (7.1)** (pages 546–547):
"Let (J1)–(J6) hold, and let $K_1 = K \cup \bigcup(A \in \mathcal{A} : d(D(A), \Sigma \setminus \Delta) \ge \theta)$. Then
(i) $d(V(\Gamma \cap K_1), \Sigma \setminus \Delta) \ge \theta$,
(ii) for $A \in \mathcal{A}$, if $d(D(A), \Sigma \setminus \Delta) < \theta$ then $E(A \cap K_1) = \emptyset$ and $V(A \cap K_1) \subseteq \bar{\pi}(A) \cup W$,
(iii) for $A \in \mathcal{A}$, if $d(D(A), \Sigma \setminus \Delta) < \theta - 3$ then $A \cap K_1 = N_W$."

The proof of (iii) follows the print (pages 546–547): "By (J4), $D(A) \cap D(A') \ne \emptyset$. Choose
$z \in Z(\Gamma)$ with $D(A) \cap D(A') \cap z \ne \emptyset$. Since $d(D(A), \Sigma \setminus \Delta) < \theta - 3$,
there exists $y \in A(\Gamma)$ with $y \cap D(A) \ne \emptyset$ such that
$d(y, \Sigma \setminus \Delta) < \theta - 3$. Now $y, z$ both intersect $D(A)$, …". Here $Z(\Gamma)$ is a
misprint for $A(\Gamma)$, and the Lean takes $z$ to be an atom of $\Gamma$ (see the correction to
the proof of (7.1) in `corrections/GM22.md`).
The common point of $D(A)$ and $D(A')$ is a vertex of $\bar{\pi}(A) \cap \bar{\pi}(A')$, as in the print,
and $z$ is the atom that contains it. -/
theorem theorem_7_1_proof {q : ℕ}
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
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE) :
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph
      {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)})
    ((∀ v ∈ Γ.V, ιV v ∈ V(K₁) → θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ)) ∧
      θ ≤ subsetTangleDist Γ ord d {v ∈ Γ.V | ιV v ∈ V(K₁)} (Set.univ \ Δ)) ∧
    (∀ A ∈ 𝒜, subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ →
      E(A ⊓ K₁) = ∅ ∧ V(A ⊓ K₁) ⊆ (ιV '' Set.range (πS A)) ∪ W) ∧
    (∀ A ∈ 𝒜, subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ - 3 →
      A ⊓ K₁ = Graph.noEdge W β) := by
  classical
  intro K₁
  have h_i_pt : ∀ v ∈ Γ.V, ιV v ∈ V(K₁) → θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ) := by
    intro v hv hvK₁
    rcases hvK₁ with hvK | hvU
    · exact hJ.dist_Γ_inter_K v hv hvK
    · rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hvU
      rcases hvU with ⟨A, ⟨hA, hAdist⟩, hvA⟩
      have hv_inter : ιV v ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A) := ⟨⟨v, hv, rfl⟩, hvA⟩
      rw [← hJ.Γ_inter_D A hA] at hv_inter
      rcases hv_inter with ⟨v', hv', hvv'⟩
      have hv_eq : v' = v := ιV.injective hvv'
      subst v'
      have hvD_mem : v ∈ D A := by
        rcases hv' with ⟨⟨_, hvD⟩, _⟩ | hvE
        · exact hvD
        · rw [mem_iUnion₂] at hvE
          rcases hvE with ⟨e, ⟨⟨_, heD⟩, _⟩, hve, _⟩
          exact (hJ.disc_D A hA).1.isClosed.closure_subset_iff.mpr heD hve
      have hvD : ({v} : Set S) ⊆ D A := singleton_subset_iff.mpr hvD_mem
      exact hAdist.trans (subsetTangleDist_anti
        (fun a ha b hb => HasTangleMetric.le_ord hJ.hasMetric ha hb) hvD Subset.rfl)
  have h_i_set : θ ≤ subsetTangleDist Γ ord d {v ∈ Γ.V | ιV v ∈ V(K₁)} (Set.univ \ Δ) := by
    unfold subsetTangleDist
    split_ifs with hex
    · have hne : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ {v ∈ Γ.V | ιV v ∈ V(K₁)}).Nonempty ∧
          (b ∩ (Set.univ \ Δ)).Nonempty ∧ d a b = k}.Nonempty := by
        rcases hex with ⟨a, ha, b, hb, haX, hbY⟩
        exact ⟨d a b, a, ha, b, hb, haX, hbY, rfl⟩
      rcases Nat.sInf_mem hne with ⟨a, ha, b, hb, ⟨v, hva, hv, hvK₁⟩, hbY, hdab⟩
      rw [← hdab]
      have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
      have ha_eq : a = {v} := GM12.atom_eq_of_inter_nonempty ha hvA ⟨v, hva, rfl⟩
      subst ha_eq
      exact (h_i_pt v hv hvK₁).trans
        (subsetTangleDist_le_of_mem hvA hb ⟨v, rfl, rfl⟩ hbY)
    · exact hJ.θ_le_ord
  have hP_le : ∀ A' ∈ {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)},
      A' ≤ R_G.G.toGraph := fun A' hA' => hJ.le_of_mem_𝒜 A' hA'.1
  have h_ii : ∀ A ∈ 𝒜, subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ →
      E(A ⊓ K₁) = ∅ ∧ V(A ⊓ K₁) ⊆ (ιV '' Set.range (πS A)) ∪ W := by
    intro A hA hlt
    have hAK : A ⊓ K = Graph.noEdge W β := by
      by_contra hne
      exact not_le_of_gt hlt (hJ.dist_D_of_inter_K A hA hne)
    have hAK_E : ∀ e ∈ E(A), e ∉ E(K) := by
      intro e heA heK
      obtain ⟨x, y, hxyA⟩ := A.exists_isLink_of_mem_edgeSet heA
      have hxyG : R_G.G.toGraph.IsLink e x y := hxyA.mono (hJ.le_of_mem_𝒜 A hA)
      have hxyK : K.IsLink e x y := (hJ.sep_NK.1.2.1.isLink_iff heK).mpr hxyG
      have hxyAK : (A ⊓ K).IsLink e x y := ⟨hxyA, hxyK⟩
      rw [hAK] at hxyAK
      exact hxyAK
    have hAK_V : V(A) ∩ V(K) = W := by
      have := congrArg Graph.vertexSet hAK
      simpa using this
    constructor
    · refine Subset.antisymm (fun e he => ?_) (empty_subset _)
      obtain ⟨x, y, hxyA, hxyK₁⟩ := (A ⊓ K₁).exists_isLink_of_mem_edgeSet he
      have heA : e ∈ E(A) := hxyA.edge_mem
      have heK₁ : e ∈ E(K₁) := hxyK₁.edge_mem
      rcases heK₁ with heK | heU
      · exact (hAK_E e heA heK).elim
      · rw [edgeSet_subgraphSUnion hP_le, mem_iUnion₂] at heU
        rcases heU with ⟨A', ⟨hA', hA'dist⟩, heA'⟩
        have hne : A ≠ A' := by
          rintro rfl
          exact not_le_of_gt hlt hA'dist
        exact Disjoint.le_bot (hJ.edge_disjoint_𝒜 A hA A' hA' hne) ⟨heA, heA'⟩
    · rintro x ⟨hxA, hxK₁⟩
      rcases hxK₁ with hxK | hxU
      · have : x ∈ V(A) ∩ V(K) := ⟨hxA, hxK⟩
        rw [hAK_V] at this
        exact Or.inr this
      · rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hxU
        rcases hxU with ⟨A', ⟨hA', hA'dist⟩, hxA'⟩
        have hne : A ≠ A' := by
          rintro rfl
          exact not_le_of_gt hlt hA'dist
        have hx_inter : x ∈ V(A) ∩ V(A') := ⟨hxA, hxA'⟩
        rw [hJ.vertex_inter_𝒜 A hA A' hA' hne] at hx_inter
        rcases hx_inter with ⟨hxπ, -⟩ | hxW
        · exact Or.inl hxπ
        · exact Or.inr hxW
  refine ⟨⟨h_i_pt, h_i_set⟩, h_ii, fun A hA hlt3 => ?_⟩
  have hlt : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < θ := by
    have := hJ.four_le_θ
    omega
  obtain ⟨hE_empty, -⟩ := h_ii A hA hlt
  have hAK : A ⊓ K = Graph.noEdge W β := by
    by_contra hne
    exact not_le_of_gt hlt (hJ.dist_D_of_inter_K A hA hne)
  have hAK_V : V(A) ∩ V(K) = W := by
    have := congrArg Graph.vertexSet hAK
    simpa using this
  have hW_sub : W ⊆ V(A ⊓ K₁) := by
    intro w hw
    exact ⟨hJ.W_subset_V A hA hw, Or.inl (hJ.sep_NK.2 hw).2⟩
  by_contra hne_noEdge
  have hV_ne : V(A ⊓ K₁) ≠ W := by
    intro hV_eq
    apply hne_noEdge
    refine Graph.ext hV_eq fun e x y => ?_
    simp only [Graph.noEdge_isLink, iff_false]
    intro hlink
    have : e ∈ E(A ⊓ K₁) := hlink.edge_mem
    rw [hE_empty] at this
    exact this
  have hex_x : ∃ x ∈ V(A ⊓ K₁), x ∉ W := by
    by_contra! hsub
    exact hV_ne (Subset.antisymm hsub hW_sub)
  rcases hex_x with ⟨x, ⟨hxA, hxK₁⟩, hxW⟩
  rcases hxK₁ with hxK | hxU
  · have : x ∈ V(A) ∩ V(K) := ⟨hxA, hxK⟩
    rw [hAK_V] at this
    exact hxW this
  · rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hxU
    rcases hxU with ⟨A', ⟨hA', hA'dist⟩, hxA'⟩
    have hAA' : A ≠ A' := by
      rintro rfl
      exact not_le_of_gt hlt hA'dist
    have hx_inter : x ∈ V(A) ∩ V(A') := ⟨hxA, hxA'⟩
    rw [hJ.vertex_inter_𝒜 A hA A' hA' hAA'] at hx_inter
    rcases hx_inter with ⟨⟨z, hzA, rfl⟩, ⟨z', hzA', hzz'⟩⟩ | hxW'
    · have hz_eq : z' = z := ιV.injective hzz'
      subst z'
      have hzD : z ∈ D A ∩ D A' := by
        rw [hJ.D_inter_eq A hA A' hA' hAA']
        exact ⟨hzA, hzA'⟩
      obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
      obtain ⟨a_z, ha_z, hza⟩ := GM11.exists_atom Γ z
      have hlt_ord : subsetTangleDist Γ ord d (D A) (Set.univ \ Δ) < ord := by
        have := hJ.θ_le_ord
        omega
      have hex_dist : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ D A).Nonempty ∧ (b ∩ (Set.univ \ Δ)).Nonempty := by
        by_contra hno
        simp only [subsetTangleDist, hno, ↓reduceIte] at hlt_ord
        exact Nat.lt_irrefl _ hlt_ord
      have hne_set : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ D A).Nonempty ∧ (b ∩ (Set.univ \ Δ)).Nonempty ∧ d a b = k}.Nonempty := by
        rcases hex_dist with ⟨a, ha, b, hb, haD, hbΔ⟩
        exact ⟨d a b, a, ha, b, hb, haD, hbΔ, rfl⟩
      have hsInf_lt : sInf {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ D A).Nonempty ∧ (b ∩ (Set.univ \ Δ)).Nonempty ∧ d a b = k} < θ - 3 := by
        simpa only [subsetTangleDist, hex_dist, ↓reduceIte] using hlt3
      rcases Nat.sInf_mem hne_set with ⟨y, hy, b, hb, hyD, hbΔ, hdyb⟩
      have hdyb_lt : d y b < θ - 3 := hdyb ▸ hsInf_lt
      have hd_zy : d a_z y ≤ 3 :=
        hJ.dist_le_three_of_meets_D hA ha_z hy ⟨z, hza, hzD.1⟩ hyD
      have hd_zb_ge : θ ≤ d a_z b :=
        hA'dist.trans (subsetTangleDist_le_of_mem ha_z hb ⟨z, hza, hzD.2⟩ hbΔ)
      have hd_tri : d a_z b ≤ d a_z y + d y b :=
        HasTangleMetric.triangle hS hJ.hasMetric ha_z hy hb
      have := hJ.four_le_θ
      omega
    · exact hxW hxW'

end GraphMinor.GM22
