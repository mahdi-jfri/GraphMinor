module

public import GraphMinor.GM22.Section7cAnnulus
public import GraphMinor.GM16.SpanTransport
public import GraphMinor.GM16.DrawingAtoms
public import GraphMinor.GM16.Section9Zones
public import GraphMinor.GM11.CitedResults

/-!
# Graph Minors XXII, Section 7 (Part 3b): Claims (6)–(7) of Theorem 7.3

This file formalizes the construction of the modified drawings `Γ₀`, `Γ₁`, `Γ₂`, `Γ₃` and proves
Claims (6) and (7) of the proof of **7.3** (`theorem_7_3`, page 549) from
N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563:
- Action of a surface homeomorphism `β : S ≃ₜ S` on graphs `Graph α β` via embeddings
  `ιV : S ↪ α` and `ιE : Set S ↪ β` (`homeoVertEquiv`, `homeoEdgeEquiv`, `mapGraphEquiv`).
- Construction of the annulus routing family `M_fam` and drawings `Γ₀`, `Γ₁`, `Γ₂`, `Γ₃`, and proof
  of Claim `(6)` (`lemma_7_3_claim_6`).
- Proof of Claim `(7)` (`lemma_7_3_claim_7`) and invariance of `K₁` under `mapGraphEquiv`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM16

universe u v w u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Transporting Graphs Along Equivalences Induced by a Surface Homeomorphism -/

/-- The image of a graph `G : Graph α β` under equivalences `eV : α ≃ α'` and `eE : β ≃ β'`. -/
def mapGraphEquiv {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β') (G : Graph α β) :
    Graph α' β' where
  vertexSet := eV '' V(G)
  edgeSet := eE '' E(G)
  IsLink e' x' y' := G.IsLink (eE.symm e') (eV.symm x') (eV.symm y')
  isLink_symm _ _ := ⟨fun _ _ h => h.symm⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := by
    rcases h₁.left_eq_or_eq h₂ with h | h
    · exact Or.inl (eV.symm.injective h)
    · exact Or.inr (eV.symm.injective h)
  edge_mem_iff_exists_isLink e' := by
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨x, y, hl⟩ := G.exists_isLink_of_mem_edgeSet he
      refine ⟨eV x, eV y, ?_⟩
      simpa using hl
    · rintro ⟨x', y', hl⟩
      exact ⟨eE.symm e', hl.edge_mem, eE.apply_symm_apply e'⟩
  left_mem_of_isLink _ x' _ hl := ⟨eV.symm x', hl.left_mem, eV.apply_symm_apply x'⟩

@[simp]
theorem vertexSet_mapGraphEquiv {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G : Graph α β) : V(mapGraphEquiv eV eE G) = eV '' V(G) := rfl

@[simp]
theorem edgeSet_mapGraphEquiv {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G : Graph α β) : E(mapGraphEquiv eV eE G) = eE '' E(G) := rfl

@[simp]
theorem mapGraphEquiv_isLink {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G : Graph α β) (e' : β') (x' y' : α') :
    (mapGraphEquiv eV eE G).IsLink e' x' y' ↔
      G.IsLink (eE.symm e') (eV.symm x') (eV.symm y') := Iff.rfl

@[simp]
theorem mapGraphEquiv_isLink_apply {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G : Graph α β) (e : β) (x y : α) :
    (mapGraphEquiv eV eE G).IsLink (eE e) (eV x) (eV y) ↔ G.IsLink e x y := by
  simp [mapGraphEquiv_isLink]

theorem mapGraphEquiv_mono {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    {G₁ G₂ : Graph α β} (h : G₁ ≤ G₂) :
    mapGraphEquiv eV eE G₁ ≤ mapGraphEquiv eV eE G₂ :=
  ⟨image_mono h.vertexSet_mono, fun _ _ _ hl => h.2 hl⟩

theorem mapGraphEquiv_symm_apply {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G : Graph α β) :
    mapGraphEquiv eV.symm eE.symm (mapGraphEquiv eV eE G) = G := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext x
    simp
  · simp [mapGraphEquiv_isLink]

theorem mapGraphEquiv_graphUnion {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G₁ G₂ : Graph α β) :
    mapGraphEquiv eV eE (graphUnion G₁ G₂) =
      graphUnion (mapGraphEquiv eV eE G₁) (mapGraphEquiv eV eE G₂) := by
  refine Graph.ext ?_ fun e' x' y' => ?_
  · simp [vertexSet_graphUnion, image_union]
  · change (G₁.IsLink (eE.symm e') (eV.symm x') (eV.symm y') ∨
        eE.symm e' ∉ E(G₁) ∧ G₂.IsLink (eE.symm e') (eV.symm x') (eV.symm y')) ↔
      (G₁.IsLink (eE.symm e') (eV.symm x') (eV.symm y') ∨
        e' ∉ eE '' E(G₁) ∧ G₂.IsLink (eE.symm e') (eV.symm x') (eV.symm y'))
    refine or_congr Iff.rfl (and_congr ?_ Iff.rfl)
    constructor
    · intro h ⟨e, he, heq⟩
      exact h (by simpa [← heq] using he)
    · intro h he
      exact h ⟨eE.symm e', he, eE.apply_symm_apply e'⟩

theorem mapGraphEquiv_eq_self {eV : α ≃ α} {eE : β ≃ β} {G : Graph α β}
    (hV : ∀ x ∈ V(G), eV x = x) (hE : ∀ e ∈ E(G), eE e = e) :
    mapGraphEquiv eV eE G = G := by
  have hV_symm : ∀ x ∈ V(G), eV.symm x = x := by
    intro x hx
    exact eV.injective (by rw [eV.apply_symm_apply, hV x hx])
  have hE_symm : ∀ e ∈ E(G), eE.symm e = e := by
    intro e he
    exact eE.injective (by rw [eE.apply_symm_apply, hE e he])
  refine Graph.ext ?_ fun e x y => ?_
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [hV y hy]
    · intro hx
      exact ⟨x, hx, hV x hx⟩
  · simp only [mapGraphEquiv_isLink]
    constructor
    · intro hl
      have he : eE.symm e = e := by
        have := hl.edge_mem
        have he' : e ∈ E(G) := by
          have h1 := hE (eE.symm e) this
          rw [eE.apply_symm_apply] at h1
          exact h1 ▸ this
        exact hE_symm e he'
      have hx : eV.symm x = x := by
        have := hl.left_mem
        have hx' : x ∈ V(G) := by
          have h1 := hV (eV.symm x) this
          rw [eV.apply_symm_apply] at h1
          exact h1 ▸ this
        exact hV_symm x hx'
      have hy : eV.symm y = y := by
        have := hl.right_mem
        have hy' : y ∈ V(G) := by
          have h1 := hV (eV.symm y) this
          rw [eV.apply_symm_apply] at h1
          exact h1 ▸ this
        exact hV_symm y hy'
      rwa [he, hx, hy] at hl
    · intro hl
      rwa [hE_symm e hl.edge_mem, hV_symm x hl.left_mem, hV_symm y hl.right_mem]

private theorem areConnectedIn_mapGraphEquiv {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G : Graph α β) {x y : α} (hconn : AreConnectedIn G x y) :
    AreConnectedIn (mapGraphEquiv eV eE G) (eV x) (eV y) := by
  rw [areConnectedIn_iff_walk] at hconn ⊢
  rcases hconn with ⟨hx, hy, ⟨W⟩⟩
  refine ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ?_⟩
  have hwalk : ∀ {a b : α}, GraphWalk G a b →
      Nonempty (GraphWalk (mapGraphEquiv eV eE G) (eV a) (eV b)) := by
    intro a b W₀
    induction W₀ with
    | nil ha => exact ⟨.nil ⟨_, ha, rfl⟩⟩
    | @cons a₁ m₁ b₁ e hl rest ih =>
      obtain ⟨W_rest⟩ := ih
      have hl' : (mapGraphEquiv eV eE G).IsLink (eE e) (eV a₁) (eV m₁) := by
        rwa [mapGraphEquiv_isLink_apply]
      exact ⟨.cons hl' W_rest⟩
  exact hwalk W

theorem areConnectedIn_mapGraphEquiv_iff {α' : Type*} {β' : Type*} (eV : α ≃ α') (eE : β ≃ β')
    (G : Graph α β) (x y : α) :
    AreConnectedIn (mapGraphEquiv eV eE G) (eV x) (eV y) ↔ AreConnectedIn G x y := by
  constructor
  · intro h
    have h' := areConnectedIn_mapGraphEquiv eV.symm eE.symm (mapGraphEquiv eV eE G) h
    simpa [mapGraphEquiv_symm_apply] using h'
  · exact areConnectedIn_mapGraphEquiv eV eE G

/-- Given `ιV : S ↪ α` and a homeomorphism `β_homeo : S ≃ₜ S`, the induced permutation on `α`
acting as `β_homeo` on `range ιV` and identity outside. -/
noncomputable def homeoVertEquiv (ιV : S ↪ α) (β_homeo : S ≃ₜ S) : α ≃ α :=
  open Classical in
  Equiv.Perm.extendDomain β_homeo.toEquiv (Equiv.ofInjective ιV ιV.injective)

/-- Given `ιE : Set S ↪ β` and a homeomorphism `β_homeo : S ≃ₜ S`, the induced permutation on `β`
acting as `image β_homeo` on `range ιE` and identity outside. -/
noncomputable def homeoEdgeEquiv (ιE : Set S ↪ β) (β_homeo : S ≃ₜ S) : β ≃ β :=
  open Classical in
  let imgEquiv : Set S ≃ Set S :=
    { toFun := image β_homeo
      invFun := image β_homeo.symm
      left_inv := fun s => by simp [image_image]
      right_inv := fun s => by simp [image_image] }
  Equiv.Perm.extendDomain imgEquiv (Equiv.ofInjective ιE ιE.injective)

omit [T2Space S] in
@[simp]
theorem homeoVertEquiv_apply_ιV (ιV : S ↪ α) (β_homeo : S ≃ₜ S) (x : S) :
    homeoVertEquiv ιV β_homeo (ιV x) = ιV (β_homeo x) := by
  classical
  unfold homeoVertEquiv
  change Equiv.Perm.extendDomain β_homeo.toEquiv (Equiv.ofInjective ιV ιV.injective)
    (Equiv.ofInjective ιV ιV.injective x) = _
  rw [Equiv.Perm.extendDomain_apply_image]
  rfl

omit [T2Space S] in
theorem homeoVertEquiv_apply_of_not_mem (ιV : S ↪ α) (β_homeo : S ≃ₜ S) {a : α}
    (ha : a ∉ Set.range ιV) : homeoVertEquiv ιV β_homeo a = a := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ ha

omit [T2Space S] in
@[simp]
theorem homeoVertEquiv_symm (ιV : S ↪ α) (β_homeo : S ≃ₜ S) :
    (homeoVertEquiv ιV β_homeo).symm = homeoVertEquiv ιV β_homeo.symm := by
  ext a
  by_cases ha : a ∈ Set.range ιV
  · rcases ha with ⟨x, rfl⟩
    apply (homeoVertEquiv ιV β_homeo).injective
    rw [Equiv.apply_symm_apply, homeoVertEquiv_apply_ιV, homeoVertEquiv_apply_ιV,
      β_homeo.apply_symm_apply]
  · rw [homeoVertEquiv_apply_of_not_mem ιV β_homeo.symm ha]
    apply (homeoVertEquiv ιV β_homeo).injective
    rw [Equiv.apply_symm_apply, homeoVertEquiv_apply_of_not_mem ιV β_homeo ha]

omit [T2Space S] in
@[simp]
theorem homeoEdgeEquiv_apply_ιE (ιE : Set S ↪ β) (β_homeo : S ≃ₜ S) (s : Set S) :
    homeoEdgeEquiv ιE β_homeo (ιE s) = ιE (β_homeo '' s) := by
  classical
  unfold homeoEdgeEquiv
  change Equiv.Perm.extendDomain _ (Equiv.ofInjective ιE ιE.injective)
    (Equiv.ofInjective ιE ιE.injective s) = _
  rw [Equiv.Perm.extendDomain_apply_image]
  rfl

omit [T2Space S] in
theorem homeoEdgeEquiv_apply_of_not_mem (ιE : Set S ↪ β) (β_homeo : S ≃ₜ S) {b : β}
    (hb : b ∉ Set.range ιE) : homeoEdgeEquiv ιE β_homeo b = b := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hb

omit [T2Space S] in
@[simp]
theorem homeoEdgeEquiv_symm (ιE : Set S ↪ β) (β_homeo : S ≃ₜ S) :
    (homeoEdgeEquiv ιE β_homeo).symm = homeoEdgeEquiv ιE β_homeo.symm := by
  ext b
  by_cases hb : b ∈ Set.range ιE
  · rcases hb with ⟨s, rfl⟩
    apply (homeoEdgeEquiv ιE β_homeo).injective
    rw [Equiv.apply_symm_apply, homeoEdgeEquiv_apply_ιE, homeoEdgeEquiv_apply_ιE,
      image_symm_image]
  · rw [homeoEdgeEquiv_apply_of_not_mem ιE β_homeo.symm hb]
    apply (homeoEdgeEquiv ιE β_homeo).injective
    rw [Equiv.apply_symm_apply, homeoEdgeEquiv_apply_of_not_mem ιE β_homeo hb]

omit [T2Space S] in
/-- Transporting `D.toEmbeddedGraph ιV ιE` along `homeoVertEquiv` and `homeoEdgeEquiv` gives
`(mapDrawingHomeo β_homeo D).toEmbeddedGraph ιV ιE`. -/
theorem mapGraphEquiv_toEmbeddedGraph (ιV : S ↪ α) (ιE : Set S ↪ β) (β_homeo : S ≃ₜ S)
    (D : Drawing S) :
    mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo)
      (D.toEmbeddedGraph ιV ιE) = (mapDrawingHomeo β_homeo D).toEmbeddedGraph ιV ιE := by
  refine Graph.ext ?_ fun e x y => ?_
  · change homeoVertEquiv ιV β_homeo '' (ιV '' D.V) = ιV '' (β_homeo '' D.V)
    rw [← image_comp, ← image_comp]
    congr 1
    funext s
    exact homeoVertEquiv_apply_ιV ιV β_homeo s
  · simp only [mapGraphEquiv_isLink, homeoVertEquiv_symm, homeoEdgeEquiv_symm,
      Drawing.toEmbeddedGraph]
    constructor
    · rintro ⟨e₀, x₀, y₀, hl, he, hx, hy⟩
      have he' : e = ιE (β_homeo '' e₀) := by
        have := congrArg (homeoEdgeEquiv ιE β_homeo) he.symm
        simpa [← homeoEdgeEquiv_symm] using this
      have hx' : x = ιV (β_homeo x₀) := by
        have := congrArg (homeoVertEquiv ιV β_homeo) hx.symm
        simpa [← homeoVertEquiv_symm] using this
      have hy' : y = ιV (β_homeo y₀) := by
        have := congrArg (homeoVertEquiv ιV β_homeo) hy.symm
        simpa [← homeoVertEquiv_symm] using this
      exact ⟨β_homeo '' e₀, β_homeo x₀, β_homeo y₀,
        isLink_mapDrawingHomeo β_homeo D hl, he'.symm, hx'.symm, hy'.symm⟩
    · rintro ⟨e₁, x₁, y₁, hl, rfl, rfl, rfl⟩
      refine ⟨β_homeo.symm '' e₁, β_homeo.symm x₁, β_homeo.symm y₁, ?_,
        (homeoEdgeEquiv_apply_ιE ιE β_homeo.symm e₁).symm,
        (homeoVertEquiv_apply_ιV ιV β_homeo.symm x₁).symm,
        (homeoVertEquiv_apply_ιV ιV β_homeo.symm y₁).symm⟩
      have hl' := isLink_mapDrawingHomeo β_homeo.symm (mapDrawingHomeo β_homeo D) hl
      have hD : mapDrawingHomeo β_homeo.symm (mapDrawingHomeo β_homeo D) = D := by
        apply Drawing.ext_of_V_E
        · change β_homeo.symm '' (β_homeo '' D.V) = D.V
          exact symm_image_image β_homeo D.V
        · rw [mapDrawingHomeo_edges, mapDrawingHomeo_edges]
          ext s
          simp [symm_image_image]
      rwa [hD] at hl'

/-! ## 2. Annulus Routing Family and Proof of Claim (6) of 7.3 -/

omit [T2Space S] in
/-- Cyclic rotation and antisymmetry properties of `orient.pos D` on three distinct points of
`discBd D`. -/
theorem orient_pos_rot_and_not_swap (orient : GM19.SurfaceOrientation S) {D : Set S}
    (hD : IsClosedDisc D) {x y z : S}
    (hx : x ∈ discBd D) (hy : y ∈ discBd D) (hz : z ∈ discBd D)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxyz : orient.pos D x y z) :
    orient.pos D y z x ∧ ¬ orient.pos D x z y := by
  obtain ⟨φ, _, hφi, hφr, hφpos⟩ := orient.isDirection D hD
  obtain ⟨a, rfl⟩ : x ∈ range φ := hφr ▸ hx
  obtain ⟨b, rfl⟩ : y ∈ range φ := hφr ▸ hy
  obtain ⟨c, rfl⟩ : z ∈ range φ := hφr ▸ hz
  have hab : a ≠ b := fun h => hxy (congrArg φ h)
  have hbc : b ≠ c := fun h => hyz (congrArg φ h)
  have hac : a ≠ c := fun h => hxz (congrArg φ h)
  have habc := (hφpos a b c hab hbc hac).mp hxyz
  rw [hφpos b c a hbc hac.symm hab.symm, hφpos a c b hac hbc.symm hab]
  exact ⟨habc.rotate, fun hacb => GM19.not_circleCyclic_both habc hacb⟩

/-- Existence of the annulus routing drawings `M_fam i` in `D (A_fam i)` for `1 ≤ i ≤ t`
(Graph Minors XXII, page 549). -/
theorem exists_annulus_family_7_3 {q t : ℕ}
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
    {A_fam A_fam' : Fin t → Graph α β}
    (hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i))
    (h_ii : ∀ i : Fin t, Disjoint (D (A_fam i)) Δ)
    {D_in : Fin t → Set S}
    (hD_in : ∀ i : Fin t, IsClosedDisc (D_in i) ∧ D_in i ⊆ D (A_fam i) \ subBd (D (A_fam i)))
    {β_homeo : S ≃ₜ S}
    (hβ_img : ∀ i : Fin t, β_homeo '' D_in i = D (A_fam' i))
    (hβ_pres : orient.IsPreservedBy β_homeo) :
    let π_in : ∀ i : Fin t, Fin (πLen (A_fam i)) → S :=
      fun i j => β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))
    ∃ (M_fam : Fin t → Drawing S) (L_arc : ∀ i : Fin t, Fin (πLen (A_fam i)) → Set S),
      ∀ i : Fin t,
        (M_fam i).U = (⋃ j : Fin (πLen (A_fam i)), L_arc i j) ∧
        (M_fam i).V = Set.range (π_in i) ∪ Set.range (πS (A_fam i)) ∧
        (M_fam i).E = Set.range (fun j : Fin (πLen (A_fam i)) =>
          L_arc i j \ {π_in i j, πS (A_fam i) j}) ∧
        (M_fam i).U ⊆ D (A_fam i) ∧
        (M_fam i).U ∩ D_in i = Set.range (π_in i) ∧
        (M_fam i).U ∩ subBd (D (A_fam i)) = Set.range (πS (A_fam i)) ∧
        (∀ j : Fin (πLen (A_fam i)),
          IsLineWithEnds (L_arc i j) (π_in i j) (πS (A_fam i) j)) ∧
        (∀ j : Fin (πLen (A_fam i)), π_in i j ≠ πS (A_fam i) j) ∧
        Pairwise (fun j₁ j₂ : Fin (πLen (A_fam i)) => Disjoint (L_arc i j₁) (L_arc i j₂)) ∧
        (∀ j : Fin (πLen (A_fam i)),
          L_arc i j \ {π_in i j, πS (A_fam i) j} ⊆
            (D (A_fam i) \ subBd (D (A_fam i))) \ D_in i) ∧
        (∀ j : Fin (πLen (A_fam i)), L_arc i j ∩ D_in i = {π_in i j}) ∧
        (∀ j : Fin (πLen (A_fam i)), L_arc i j ∩ subBd (D (A_fam i)) = {πS (A_fam i) j}) := by
  intro π_in
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hex : ∀ i : Fin t,
      ∃ (M : Drawing S) (L : Fin (πLen (A_fam i)) → Set S),
        M.U = (⋃ j : Fin (πLen (A_fam i)), L j) ∧
        M.V = Set.range (π_in i) ∪ Set.range (πS (A_fam i)) ∧
        M.E = Set.range (fun j : Fin (πLen (A_fam i)) =>
          L j \ {π_in i j, πS (A_fam i) j}) ∧
        M.U ⊆ D (A_fam i) ∧
        M.U ∩ D_in i = Set.range (π_in i) ∧
        M.U ∩ subBd (D (A_fam i)) = Set.range (πS (A_fam i)) ∧
        (∀ j : Fin (πLen (A_fam i)),
          IsLineWithEnds (L j) (π_in i j) (πS (A_fam i) j)) ∧
        (∀ j : Fin (πLen (A_fam i)), π_in i j ≠ πS (A_fam i) j) ∧
        Pairwise (fun j₁ j₂ : Fin (πLen (A_fam i)) => Disjoint (L j₁) (L j₂)) ∧
        (∀ j : Fin (πLen (A_fam i)),
          L j \ {π_in i j, πS (A_fam i) j} ⊆
            (D (A_fam i) \ subBd (D (A_fam i))) \ D_in i) ∧
        (∀ j : Fin (πLen (A_fam i)), L j ∩ D_in i = {π_in i j}) ∧
        (∀ j : Fin (πLen (A_fam i)), L j ∩ subBd (D (A_fam i)) = {πS (A_fam i) j}) := by
    intro i
    have h5 := lemma_7_3_claim_5 hJ hA_mem hA'_mem hlen (fun k => (hD_in k).1) hβ_img i
    have hπ_in_bd : Set.range (π_in i) ⊆ subBd (D_in i) := by
      rintro _ ⟨j, rfl⟩
      exact h5.1 ⟨Fin.cast (hlen i).symm j, rfl⟩
    have hπ_in_inj : Function.Injective (π_in i) :=
      fun j₁ j₂ heq => Fin.cast_injective (hlen i).symm (h5.2.1 heq)
    have hπ_out_bd : Set.range (πS (A_fam i)) ⊆ subBd (D (A_fam i)) :=
      (hJ.range_πS_subset_D_and_ncard (hA_mem i)).1
    have hπ_out_inj : Function.Injective (πS (A_fam i)) :=
      (hJ.π_valid (A_fam i) (hA_mem i)).2.2.1
    refine exists_annulus_drawing hS orient (hD_in i).1 (hJ.disc_D (A_fam i) (hA_mem i)).1
      hJ.disc_Δ.1 (hD_in i).2 (h_ii i) (π_in i) (πS (A_fam i))
      hπ_in_bd hπ_in_inj hπ_out_bd hπ_out_inj ?_
    intro j₁ j₂ j₃ h12 h23 h13
    have hle3 : πLen (A_fam i) ≤ 3 := (hJ.π_valid (A_fam i) (hA_mem i)).2.1
    have hr3 : πLen (A_fam i) = 3 := by
      have := j₁.2; have := j₂.2; have := j₃.2
      have : j₁.1 ≠ j₂.1 := Fin.val_ne_of_ne h12
      have : j₂.1 ≠ j₃.1 := Fin.val_ne_of_ne h23
      have : j₁.1 ≠ j₃.1 := Fin.val_ne_of_ne h13
      omega
    have hr3' : πLen (A_fam' i) = 3 := (hlen i).trans hr3
    have hbd_in : subBd (D_in i) = discBd (D_in i) :=
      IsClosedDisc.subBd_eq_discBd hS (hD_in i).1
    have hbd_out : subBd (D (A_fam i)) = discBd (D (A_fam i)) :=
      IsClosedDisc.subBd_eq_discBd hS (hJ.disc_D (A_fam i) (hA_mem i)).1
    have hmem_in : ∀ j, π_in i j ∈ discBd (D_in i) :=
      fun j => hbd_in ▸ hπ_in_bd ⟨j, rfl⟩
    have hmem_out : ∀ j, πS (A_fam i) j ∈ discBd (D (A_fam i)) :=
      fun j => hbd_out ▸ hπ_out_bd ⟨j, rfl⟩
    let i0 : Fin (πLen (A_fam i)) := ⟨0, by omega⟩
    let i1 : Fin (πLen (A_fam i)) := ⟨1, by omega⟩
    let i2 : Fin (πLen (A_fam i)) := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := fun h => by have := congrArg Fin.val h; simp [i0, i1] at this
    have h12_0 : i1 ≠ i2 := fun h => by have := congrArg Fin.val h; simp [i1, i2] at this
    have h02 : i0 ≠ i2 := fun h => by have := congrArg Fin.val h; simp [i0, i2] at this
    have hpos_in_012 : orient.pos (D_in i) (π_in i i0) (π_in i i1) (π_in i i2) := by
      have hpres0 := hβ_pres (D_in i) (hD_in i).1 (π_in i i0) (π_in i i1) (π_in i i2)
        (hmem_in i0) (hmem_in i1) (hmem_in i2)
        (hπ_in_inj.ne h01) (hπ_in_inj.ne h12_0) (hπ_in_inj.ne h02)
      rw [hβ_img i] at hpres0
      have hβ_π : ∀ j, β_homeo (π_in i j) = πS (A_fam' i) (Fin.cast (hlen i).symm j) :=
        fun j => β_homeo.apply_symm_apply _
      rw [hβ_π i0, hβ_π i1, hβ_π i2] at hpres0
      exact hpres0.mp (hJ.π_clockwise (A_fam' i) (hA'_mem i) hr3')
    have hpos_out_012 :
        orient.pos (D (A_fam i)) (πS (A_fam i) i0) (πS (A_fam i) i1) (πS (A_fam i) i2) :=
      hJ.π_clockwise (A_fam i) (hA_mem i) hr3
    have hiff : ∀ {E : Set S} (hE : IsClosedDisc E) (p : Fin (πLen (A_fam i)) → S),
        (∀ j, p j ∈ discBd E) → Function.Injective p →
        orient.pos E (p i0) (p i1) (p i2) →
        (orient.pos E (p j₁) (p j₂) (p j₃) ↔
          (j₁.1 = 0 ∧ j₂.1 = 1 ∧ j₃.1 = 2) ∨
          (j₁.1 = 1 ∧ j₂.1 = 2 ∧ j₃.1 = 0) ∨
          (j₁.1 = 2 ∧ j₂.1 = 0 ∧ j₃.1 = 1)) := by
      intro E hE p hp hp_inj h012
      obtain ⟨hrot1, hnot021⟩ := orient_pos_rot_and_not_swap orient hE (hp i0) (hp i1) (hp i2)
        (hp_inj.ne h01) (hp_inj.ne h12_0) (hp_inj.ne h02) h012
      obtain ⟨hrot2, hnot102⟩ := orient_pos_rot_and_not_swap orient hE (hp i1) (hp i2) (hp i0)
        (hp_inj.ne h12_0) (hp_inj.ne h02.symm) (hp_inj.ne h01.symm) hrot1
      obtain ⟨_, hnot210⟩ := orient_pos_rot_and_not_swap orient hE (hp i2) (hp i0) (hp i1)
        (hp_inj.ne h02.symm) (hp_inj.ne h01) (hp_inj.ne h12_0.symm) hrot2
      have hcases :
          (j₁ = i0 ∧ j₂ = i1 ∧ j₃ = i2) ∨
          (j₁ = i1 ∧ j₂ = i2 ∧ j₃ = i0) ∨
          (j₁ = i2 ∧ j₂ = i0 ∧ j₃ = i1) ∨
          (j₁ = i0 ∧ j₂ = i2 ∧ j₃ = i1) ∨
          (j₁ = i1 ∧ j₂ = i0 ∧ j₃ = i2) ∨
          (j₁ = i2 ∧ j₂ = i1 ∧ j₃ = i0) := by
        have hj₁ := j₁.2; have hj₂ := j₂.2; have hj₃ := j₃.2
        have : j₁.1 ≠ j₂.1 := Fin.val_ne_of_ne h12
        have : j₂.1 ≠ j₃.1 := Fin.val_ne_of_ne h23
        have : j₁.1 ≠ j₃.1 := Fin.val_ne_of_ne h13
        simp only [Fin.ext_iff, i0, i1, i2]
        omega
      rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · exact ⟨fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun _ => h012⟩
      · exact ⟨fun _ => Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), fun _ => hrot1⟩
      · exact ⟨fun _ => Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), fun _ => hrot2⟩
      · exact ⟨fun h => (hnot021 h).elim, fun h => by simp [i0, i1, i2] at h⟩
      · exact ⟨fun h => (hnot102 h).elim, fun h => by simp [i0, i1, i2] at h⟩
      · exact ⟨fun h => (hnot210 h).elim, fun h => by simp [i0, i1, i2] at h⟩
    rw [hiff (hD_in i).1 (π_in i) hmem_in hπ_in_inj hpos_in_012,
      hiff (hJ.disc_D (A_fam i) (hA_mem i)).1 (πS (A_fam i)) hmem_out hπ_out_inj hpos_out_012]
  choose M_fam L_arc hML using hex
  exact ⟨M_fam, L_arc, hML⟩

omit [T2Space S] in
/-- For any finite family of sets `X : Fin t → Set S`, the complement of the union of their
interiors `X i \ subBd (X i)` is closed. -/
theorem isClosed_compl_iUnion_discInt {t : ℕ} (X : Fin t → Set S) :
    IsClosed (Set.univ \ ⋃ i : Fin t, (X i \ subBd (X i))) := by
  refine isClosed_univ.sdiff (isOpen_iUnion fun i => ?_)
  rw [subBd_eq_frontier, self_sdiff_frontier]
  exact isOpen_interior

/-- Construction of the drawings `M_union`, `Γ₁`, `Γ₂`, `Γ₃` on page 549 of Graph Minors XXII. -/
theorem exists_drawings_7_3 {q t : ℕ}
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
    {A_fam A_fam' : Fin t → Graph α β}
    (hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜)
    (hA_inj : Function.Injective A_fam)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i))
    (h_iv : ∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j)))
    (h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F)
    {D_in : Fin t → Set S}
    (hD_in : ∀ i : Fin t, IsClosedDisc (D_in i) ∧ D_in i ⊆ D (A_fam i) \ subBd (D (A_fam i)))
    {β_homeo : S ≃ₜ S}
    (hβ_img : ∀ i : Fin t, β_homeo '' D_in i = D (A_fam' i))
    {M_fam : Fin t → Drawing S}
    (hM_V : ∀ i : Fin t, (M_fam i).V =
      Set.range (fun j : Fin (πLen (A_fam i)) =>
        β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))) ∪
      Set.range (πS (A_fam i)))
    (hM_U_sub : ∀ i : Fin t, (M_fam i).U ⊆ D (A_fam i))
    (hM_U_in : ∀ i : Fin t, (M_fam i).U ∩ D_in i =
      Set.range (fun j : Fin (πLen (A_fam i)) =>
        β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j)))) :
    let S₀ : Set S := Set.univ \ ⋃ i : Fin t, (D (A_fam i) \ subBd (D (A_fam i)))
    let Γ₀ : Drawing S := Γ.interSet S₀
    let F_fam : Fin t → Set S := fun i => subBd (D (A_fam' i))
    ∃ (M_union Γ₁ Γ₃ : Drawing S),
      M_union.U = (⋃ i : Fin t, (M_fam i).U) ∧
      M_union.V = (⋃ i : Fin t, (M_fam i).V) ∧
      M_union.E = (⋃ i : Fin t, (M_fam i).E) ∧
      Γ₁.U = Γ₀.U ∪ M_union.U ∧
      Γ₁.V = Γ₀.V ∪ M_union.V ∧
      Γ₁.E = Γ₀.E ∪ M_union.E ∧
      (∀ i : Fin t, (mapDrawingHomeo β_homeo Γ₁).U ∩ D (A_fam' i) = Set.range (πS (A_fam' i))) ∧
      (∀ i : Fin t, Set.range (πS (A_fam' i)) ⊆ (mapDrawingHomeo β_homeo Γ₁).V) ∧
      Γ₃.U = (mapDrawingHomeo β_homeo Γ₁).U ∪ ⋃ i : Fin t, (Γ.interSet (ins (F_fam i))).U ∧
      Γ₃.V = (mapDrawingHomeo β_homeo Γ₁).V ∪ ⋃ i : Fin t, (Γ.interSet (ins (F_fam i))).V ∧
      Γ₃.E = (mapDrawingHomeo β_homeo Γ₁).E ∪ ⋃ i : Fin t, (Γ.interSet (ins (F_fam i))).E := by
  intro S₀ Γ₀ F_fam
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  -- 1. Glue `M_fam` into `M_union`:
  have hM_disj : ∀ i j : Fin t, i ≠ j →
      (M_fam i).U ∩ (M_fam j).U ⊆ (M_fam i).V ∩ (M_fam j).V := by
    intro i j hij x ⟨hxi, hxj⟩
    have hcap : x ∈ D (A_fam i) ∩ D (A_fam j) := ⟨hM_U_sub i hxi, hM_U_sub j hxj⟩
    rw [hJ.D_inter_eq (A_fam i) (hA_mem i) (A_fam j) (hA_mem j) (hA_inj.ne hij)] at hcap
    rw [hM_V i, hM_V j]
    exact ⟨Or.inr hcap.1, Or.inr hcap.2⟩
  obtain ⟨M_union, hMU_U, hMU_V, hMU_E⟩ := exists_glue_fin M_fam hM_disj
  -- 2. Glue `Γ₀` and `M_union` into `Γ₁`:
  have hS₀_closed : IsClosed S₀ := isClosed_compl_iUnion_discInt _
  have hΓ₀_U_sub_S₀ : Γ₀.U ⊆ S₀ := interSet_U_subset hS₀_closed
  have hΓ₀_sub_Γ : Γ₀.IsSubdrawing Γ := interSet_isSub
  have hΓ₀_M : Γ₀.U ∩ M_union.U ⊆ Γ₀.V ∩ M_union.V := by
    rintro x ⟨hxΓ₀, hxM⟩
    rw [hMU_U, mem_iUnion] at hxM
    rcases hxM with ⟨i, hxi⟩
    have hxD : x ∈ D (A_fam i) := hM_U_sub i hxi
    have hxS₀ : x ∈ S₀ := hΓ₀_U_sub_S₀ hxΓ₀
    have hx_bd : x ∈ subBd (D (A_fam i)) := by
      by_contra hx_not_bd
      exact hxS₀.2 (mem_iUnion.mpr ⟨i, hxD, hx_not_bd⟩)
    have hx_ΓU : x ∈ Γ.U := hΓ₀_sub_Γ.U_subset hxΓ₀
    have hx_ΓV : x ∈ Γ.V := (hJ.disc_D (A_fam i) (hA_mem i)).2.1 ⟨hx_bd, hx_ΓU⟩
    have hx_π : x ∈ Set.range (πS (A_fam i)) := by
      rw [hJ.π_bar_eq_bd_inter (A_fam i) (hA_mem i)]
      exact ⟨hx_bd, (hJ.Γ_le.trans deleteVerts_le).vertexSet_mono ⟨x, hx_ΓV, rfl⟩⟩
    refine ⟨mem_interSet_V hx_ΓV hxS₀, ?_⟩
    rw [hMU_V, mem_iUnion]
    exact ⟨i, (hM_V i).symm ▸ Or.inr hx_π⟩
  let Γ₁ := Γ₀.glue M_union hΓ₀_M
  have hΓ₁_U : Γ₁.U = Γ₀.U ∪ M_union.U := rfl
  have hΓ₁_V : Γ₁.V = Γ₀.V ∪ M_union.V := rfl
  have hΓ₁_E : Γ₁.E = Γ₀.E ∪ M_union.E := Drawing.glue_E hΓ₀_M
  -- 3. Compute `(mapDrawingHomeo β_homeo Γ₁).U ∩ D (A_fam' i)`:
  let Γ₂ := mapDrawingHomeo β_homeo Γ₁
  have hΓ₁_inter_Din : ∀ i : Fin t, Γ₁.U ∩ D_in i =
      Set.range (fun j : Fin (πLen (A_fam i)) =>
        β_homeo.symm (πS (A_fam' i) (Fin.cast (hlen i).symm j))) := by
    intro i
    rw [hΓ₁_U, union_inter_distrib_right, hMU_U, iUnion_inter]
    have hΓ₀_Din : Γ₀.U ∩ D_in i = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro x ⟨hxΓ₀, hxDin⟩
      exact (hΓ₀_U_sub_S₀ hxΓ₀).2 (mem_iUnion.mpr ⟨i, (hD_in i).2 hxDin⟩)
    rw [hΓ₀_Din, empty_union]
    apply Subset.antisymm
    · rintro x hx
      rw [mem_iUnion] at hx
      rcases hx with ⟨k, hxk⟩
      by_cases hki : k = i
      · subst hki
        rwa [← hM_U_in k]
      · exfalso
        have hxDk : x ∈ D (A_fam k) := hM_U_sub k hxk.1
        have hxDi_int := (hD_in i).2 hxk.2
        have hcap : x ∈ D (A_fam i) ∩ D (A_fam k) := ⟨hxDi_int.1, hxDk⟩
        rw [hJ.D_inter_eq (A_fam i) (hA_mem i) (A_fam k) (hA_mem k) (hA_inj.ne (Ne.symm hki))] at hcap
        exact hxDi_int.2 ((hJ.range_πS_subset_D_and_ncard (hA_mem i)).1 hcap.1)
    · intro x hx
      rw [mem_iUnion]
      exact ⟨i, (hM_U_in i).symm ▸ hx⟩
  have hΓ₂_inter_DA' : ∀ i : Fin t, Γ₂.U ∩ D (A_fam' i) = Set.range (πS (A_fam' i)) := by
    intro i
    change (β_homeo '' Γ₁.U) ∩ D (A_fam' i) = _
    rw [← hβ_img i, ← image_inter β_homeo.injective, hΓ₁_inter_Din i]
    ext x
    simp only [mem_image, mem_range]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨Fin.cast (hlen i).symm j, (β_homeo.apply_symm_apply _).symm⟩
    · rintro ⟨j', rfl⟩
      exact ⟨_, ⟨Fin.cast (hlen i) j', rfl⟩, by simp [β_homeo.apply_symm_apply]⟩
  -- 4. Glue `Γ₂` and `fun i => Γ.interSet (ins (F_fam i))` into `Γ₃`:
  let N'_fam : Fin t → Drawing S := fun i => Γ.interSet (ins (F_fam i))
  have hins_eq : ∀ i : Fin t, ins (F_fam i) = D (A_fam' i) :=
    fun i => (hJ.disc_D (A_fam' i) (hA'_mem i)).2.2.symm
  have hDA'_disj : Pairwise (fun i j : Fin t => Disjoint (D (A_fam' i)) (D (A_fam' j))) := by
    intro i j hij
    have h4 := hJ.four_le_θ
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hd := h_iv i j hlt
      exact disjoint_of_one_le_subsetTangleDist hJ.hasMetric (by omega)
    · have hd := h_iv j i hgt
      exact (disjoint_of_one_le_subsetTangleDist hJ.hasMetric (by omega)).symm
  have hN'_disj : ∀ i j : Fin t, i ≠ j →
      (N'_fam i).U ∩ (N'_fam j).U ⊆ (N'_fam i).V ∩ (N'_fam j).V := by
    intro i j hij x ⟨hxi, hxj⟩
    have hci : IsClosed (ins (F_fam i)) := hins_eq i ▸ (hJ.disc_D (A_fam' i) (hA'_mem i)).1.isClosed
    have hcj : IsClosed (ins (F_fam j)) := hins_eq j ▸ (hJ.disc_D (A_fam' j) (hA'_mem j)).1.isClosed
    have hxDi : x ∈ D (A_fam' i) := hins_eq i ▸ interSet_U_subset hci hxi
    have hxDj : x ∈ D (A_fam' j) := hins_eq j ▸ interSet_U_subset hcj hxj
    exact (Set.disjoint_left.mp (hDA'_disj hij) hxDi hxDj).elim
  obtain ⟨N'_union, hN'_U, hN'_V, hN'_E⟩ := exists_glue_fin N'_fam hN'_disj
  have hΓ₂_V_DA' : ∀ i : Fin t, Set.range (πS (A_fam' i)) ⊆ Γ₂.V := by
    intro i x hx_π'
    change x ∈ β_homeo '' Γ₁.V
    rcases hx_π' with ⟨j', rfl⟩
    refine ⟨β_homeo.symm (πS (A_fam' i) j'), ?_, β_homeo.apply_symm_apply _⟩
    rw [hΓ₁_V, hMU_V]
    refine Or.inr (mem_iUnion.mpr ⟨i, ?_⟩)
    rw [hM_V i]
    exact Or.inl ⟨Fin.cast (hlen i) j', by simp⟩
  have hΓ₂_N' : Γ₂.U ∩ N'_union.U ⊆ Γ₂.V ∩ N'_union.V := by
    rintro x ⟨hxΓ₂, hxN'⟩
    rw [hN'_U, mem_iUnion] at hxN'
    rcases hxN' with ⟨i, hxi⟩
    have hci : IsClosed (ins (F_fam i)) := hins_eq i ▸ (hJ.disc_D (A_fam' i) (hA'_mem i)).1.isClosed
    have hxDi : x ∈ D (A_fam' i) := hins_eq i ▸ interSet_U_subset hci hxi
    have hx_π' : x ∈ Set.range (πS (A_fam' i)) := by
      rw [← hΓ₂_inter_DA' i]
      exact ⟨hxΓ₂, hxDi⟩
    have h3 := lemma_7_3_claim_3 hJ hA'_mem h_v i
    have hx_F_ΓV : x ∈ F_fam i ∩ Γ.V := h3.symm ▸ hx_π'
    refine ⟨hΓ₂_V_DA' i hx_π', ?_⟩
    rw [hN'_V, mem_iUnion]
    exact ⟨i, mem_interSet_V hx_F_ΓV.2 (hins_eq i ▸ hxDi)⟩
  let Γ₃ := Γ₂.glue N'_union hΓ₂_N'
  have hΓ₃_U : Γ₃.U = Γ₂.U ∪ N'_union.U := rfl
  have hΓ₃_V : Γ₃.V = Γ₂.V ∪ N'_union.V := rfl
  have hΓ₃_E : Γ₃.E = Γ₂.E ∪ N'_union.E := Drawing.glue_E hΓ₂_N'
  refine ⟨M_union, Γ₁, Γ₃, hMU_U, hMU_V, hMU_E, hΓ₁_U, hΓ₁_V, hΓ₁_E, hΓ₂_inter_DA', hΓ₂_V_DA',
    by rw [hΓ₃_U, hN'_U], by rw [hΓ₃_V, hN'_V], by rw [hΓ₃_E, hN'_E]⟩

omit [T2Space S] in
/-- If a preconnected set `e` is disjoint from `frontier D` for a closed set `D` and meets `D`,
then `e ⊆ D`. -/
private theorem isPreconnected_subset_of_disjoint_frontier {e D : Set S} (he : IsPreconnected e)
    (hD : IsClosed D) (hdisj : Disjoint e (frontier D)) {x : S} (hxe : x ∈ e) (hxD : x ∈ D) :
    e ⊆ D := by
  intro z hze
  by_contra hzD
  obtain ⟨w, _, hw1, hw2⟩ := he (interior D) Dᶜ isOpen_interior hD.isOpen_compl
    (fun y hye => by
      by_cases hyD : y ∈ D
      · refine Or.inl (by_contra fun hy_int => ?_)
        exact Set.disjoint_left.mp hdisj hye ⟨subset_closure hyD, hy_int⟩
      · exact Or.inr hyD)
    ⟨x, hxe, by_contra fun hx_int =>
      Set.disjoint_left.mp hdisj hxe ⟨subset_closure hxD, hx_int⟩⟩
    ⟨z, hze, hzD⟩
  exact hw2 (interior_subset hw1)

/-- **Graph Minors XXII, (7.3) Claim (6)** (page 549):
(6) *$\Gamma_3$ is a $(\Sigma \setminus \Delta)$-variant of $\Gamma$, and hence an
$(R \cap \Sigma')$-variant of $\Gamma$, and
$\Gamma \cap \operatorname{ins}(F_i) = \Gamma_3 \cap \operatorname{ins}(F_i)$ for $1 \le i \le t$.* -/
theorem lemma_7_3_claim_6 {q t : ℕ}
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
    {A_fam A_fam' : Fin t → Graph α β}
    (_hA_mem : ∀ i : Fin t, A_fam i ∈ 𝒜)
    (hA'_mem : ∀ i : Fin t, A_fam' i ∈ 𝒜)
    (h_ii : ∀ i : Fin t, Disjoint (D (A_fam i)) Δ)
    (h_v : ∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
      (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F)
    {D_in : Fin t → Set S}
    {β_homeo : S ≃ₜ S}
    (hβ_fix : ∀ z ∈ Δ, β_homeo z = z)
    {M_fam : Fin t → Drawing S}
    (hM_U_sub : ∀ i : Fin t, (M_fam i).U ⊆ D (A_fam i))
    (hM_E : ∀ i : Fin t, ∀ e ∈ (M_fam i).E, e ⊆ (D (A_fam i) \ subBd (D (A_fam i))) \ D_in i)
    {M_union Γ₁ Γ₃ : Drawing S}
    (hMU_V : M_union.V = ⋃ i : Fin t, (M_fam i).V)
    (hMU_E : M_union.E = ⋃ i : Fin t, (M_fam i).E)
    (hΓ₁_V : Γ₁.V = (Γ.interSet (Set.univ \ ⋃ i : Fin t, (D (A_fam i) \ subBd (D (A_fam i))))).V ∪ M_union.V)
    (hΓ₁_E : Γ₁.E = (Γ.interSet (Set.univ \ ⋃ i : Fin t, (D (A_fam i) \ subBd (D (A_fam i))))).E ∪ M_union.E)
    (hΓ₂_inter_DA' : ∀ i : Fin t, (mapDrawingHomeo β_homeo Γ₁).U ∩ D (A_fam' i) = Set.range (πS (A_fam' i)))
    (hΓ₂_V_DA' : ∀ i : Fin t, Set.range (πS (A_fam' i)) ⊆ (mapDrawingHomeo β_homeo Γ₁).V)
    (hΓ₃_V : Γ₃.V = (mapDrawingHomeo β_homeo Γ₁).V ∪ ⋃ i : Fin t, (Γ.interSet (ins (subBd (D (A_fam' i))))).V)
    (hΓ₃_E : Γ₃.E = (mapDrawingHomeo β_homeo Γ₁).E ∪ ⋃ i : Fin t, (Γ.interSet (ins (subBd (D (A_fam' i))))).E)
    {θ' : ℕ} (hθ' : θ' + 2 ≤ θ) :
    let F_fam : Fin t → Set S := fun i => subBd (D (A_fam' i))
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    let R := ⋃ z ∈ {z ∈ Γ.A | ∀ v ∈ Γ.V, ιV v ∈ V(K₁) → θ' ≤ d z {v}}, z
    let S_prime := Set.univ \ ⋃ i : Fin t, (ins (F_fam i) \ F_fam i)
    Γ.V \ (Set.univ \ Δ) = Γ₃.V \ (Set.univ \ Δ) ∧
      (∀ e ∈ Γ.E, e ⊆ Δ → e ∈ Γ₃.E) ∧
      (∀ e ∈ Γ.E \ Γ₃.E, e ⊆ Set.univ \ Δ) ∧
      (∀ e ∈ Γ₃.E \ Γ.E, e ⊆ Set.univ \ Δ) ∧
      IsVariant Γ Γ₃ (closure (Set.univ \ Δ)) ∧
      (∀ i : Fin t, Γ.interSet (ins (F_fam i)) = Γ₃.interSet (ins (F_fam i))) ∧
      Γ₃.interSet S_prime = mapDrawingHomeo β_homeo Γ₁ ∧
      IsVariant Γ Γ₃ R ∧
      IsVariant Γ Γ₃ (R ∩ S_prime) := by
  intro F_fam 𝒜_far K₁ R S_prime
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  let S₀ : Set S := Set.univ \ ⋃ i : Fin t, (D (A_fam i) \ subBd (D (A_fam i)))
  let Γ₀ := Γ.interSet S₀
  let Γ₂ := mapDrawingHomeo β_homeo Γ₁
  have hS₀_closed : IsClosed S₀ := isClosed_compl_iUnion_discInt _
  have hins_eq : ∀ i : Fin t, ins (F_fam i) = D (A_fam' i) :=
    fun i => (hJ.disc_D (A_fam' i) (hA'_mem i)).2.2.symm
  have hS_prime_closed : IsClosed S_prime := by
    have : S_prime = Set.univ \ ⋃ i : Fin t, (D (A_fam' i) \ subBd (D (A_fam' i))) := by
      simp only [S_prime, hins_eq, F_fam]
    rw [this]
    exact isClosed_compl_iUnion_discInt _
  have hΔ_sub_S₀ : Δ ⊆ S₀ := by
    intro x hxΔ
    refine ⟨trivial, ?_⟩
    rw [mem_iUnion]
    rintro ⟨i, hxDi, _⟩
    exact Set.disjoint_left.mp (h_ii i) hxDi hxΔ
  have hβ_symm_fix : ∀ z ∈ Δ, β_homeo.symm z = z :=
    fun z hz => β_homeo.injective (by rw [β_homeo.apply_symm_apply, hβ_fix z hz])
  -- 1. `Γ.V \ (Set.univ \ Δ) = Γ₃.V \ (Set.univ \ Δ)`:
  have hV_diff_Δ : Γ.V \ (Set.univ \ Δ) = Γ₃.V \ (Set.univ \ Δ) := by
    ext x
    simp only [mem_sdiff, mem_univ, true_and, not_not]
    constructor
    · rintro ⟨hxΓ, hxΔ⟩
      refine ⟨?_, hxΔ⟩
      rw [hΓ₃_V]
      left
      change x ∈ β_homeo '' Γ₁.V
      refine ⟨x, ?_, hβ_fix x hxΔ⟩
      rw [hΓ₁_V]
      exact Or.inl (mem_interSet_V hxΓ (hΔ_sub_S₀ hxΔ))
    · rintro ⟨hxΓ₃, hxΔ⟩
      refine ⟨?_, hxΔ⟩
      rw [hΓ₃_V] at hxΓ₃
      rcases hxΓ₃ with hxΓ₂ | hxN'
      · rcases hxΓ₂ with ⟨y, hyΓ₁, rfl⟩
        have hyΔ : y ∈ Δ := by
          have := hβ_symm_fix (β_homeo y) hxΔ
          rw [β_homeo.symm_apply_apply] at this
          exact this.symm ▸ hxΔ
        have hy_eq : β_homeo y = y := hβ_fix y hyΔ
        rw [hy_eq]
        rw [hΓ₁_V] at hyΓ₁
        rcases hyΓ₁ with hyΓ₀ | hyM
        · exact (mem_interSet_V_iff hS₀_closed).mp hyΓ₀ |>.1
        · rw [hMU_V, mem_iUnion] at hyM
          rcases hyM with ⟨i, hyMi⟩
          have hyDi : y ∈ D (A_fam i) := hM_U_sub i ((M_fam i).V_subset_U hyMi)
          exact (Set.disjoint_left.mp (h_ii i) hyDi hyΔ).elim
      · rw [mem_iUnion] at hxN'
        rcases hxN' with ⟨i, hxi⟩
        exact (interSet_isSub.1 hxi)
  -- 2. `∀ e ∈ Γ.E, e ⊆ Δ → e ∈ Γ₃.E`:
  have hE_sub_Δ : ∀ e ∈ Γ.E, e ⊆ Δ → e ∈ Γ₃.E := by
    intro e heΓ heΔ
    rw [hΓ₃_E]
    left
    rw [mapDrawingHomeo_edges]
    refine ⟨e, ?_, ?_⟩
    · rw [hΓ₁_E]
      left
      rw [mem_interSet_E_iff]
      exact ⟨heΓ, heΔ.trans hΔ_sub_S₀⟩
    · ext x
      constructor
      · rintro ⟨y, hye, rfl⟩
        rw [hβ_fix y (heΔ hye)]
        exact hye
      · intro hxe
        exact ⟨x, hxe, hβ_fix x (heΔ hxe)⟩
  -- Helper: any edge `e ∈ Γ.E` meeting `Δ` is contained in `Δ`
  have hE_meet_Δ : ∀ e ∈ Γ.E, ∀ x ∈ e, x ∈ Δ → e ⊆ Δ := by
    intro e heΓ x hxe hxΔ
    by_contra hnot
    obtain ⟨z, hze, hz_not_Δ⟩ := not_subset.mp hnot
    have hdisj_fr : Disjoint e (frontier Δ) := by
      rw [← subBd_eq_frontier, Set.disjoint_left]
      intro w hwe hw_bd
      have hOArc_Δ : IsOArc (subBd Δ) := by
        rw [IsClosedDisc.subBd_eq_discBd hS hJ.disc_Δ.1]
        exact hJ.disc_Δ.1.isOArc_discBd
      have hCU : subBd Δ ⊆ (Γ.interSet (subBd Δ)).U :=
        GM16.oArc_subset_interSet_U hOArc_Δ hJ.disc_Δ.2 Subset.rfl
      have hw_CU : w ∈ (Γ.interSet (subBd Δ)).U := hCU hw_bd
      have hw_not_V : w ∉ (Γ.interSet (subBd Δ)).V :=
        fun hwV => (heΓ.2.1 hwe).2 (interSet_isSub.1 hwV)
      obtain ⟨e', he'C, hwe'⟩ := (Γ.interSet (subBd Δ)).exists_edge_of_mem hw_CU hw_not_V
      have he'_Γ : e' ∈ Γ.E ∧ e' ⊆ subBd Δ := mem_interSet_E_iff.mp he'C
      have he_eq : e' = e := Γ.edge_eq_of_mem he'_Γ.1 heΓ hwe' hwe
      have hz_bd : z ∈ subBd Δ := (he_eq ▸ he'_Γ.2) hze
      rw [subBd_eq_frontier] at hz_bd
      exact hz_not_Δ (hJ.disc_Δ.1.isClosed.frontier_subset hz_bd)
    exact hz_not_Δ (isPreconnected_subset_of_disjoint_frontier heΓ.2.2.1.isConnected.isPreconnected
      hJ.disc_Δ.1.isClosed hdisj_fr hxe hxΔ hze)
  -- 3. `∀ e ∈ Γ.E \ Γ₃.E, e ⊆ Set.univ \ Δ`:
  have hE_diff_left : ∀ e ∈ Γ.E \ Γ₃.E, e ⊆ Set.univ \ Δ := by
    rintro e ⟨heΓ, he_not_Γ₃⟩ x hxe
    exact ⟨trivial, fun hxΔ => he_not_Γ₃ (hE_sub_Δ e heΓ (hE_meet_Δ e heΓ x hxe hxΔ))⟩
  -- 4. `∀ e ∈ Γ₃.E \ Γ.E, e ⊆ Set.univ \ Δ`:
  have hE_diff_right : ∀ e ∈ Γ₃.E \ Γ.E, e ⊆ Set.univ \ Δ := by
    rintro e ⟨heΓ₃, he_not_Γ⟩ x hxe
    refine ⟨trivial, fun hxΔ => ?_⟩
    rw [hΓ₃_E] at heΓ₃
    rcases heΓ₃ with heΓ₂ | heN'
    · rw [mapDrawingHomeo_edges] at heΓ₂
      rcases heΓ₂ with ⟨e₁, he₁, rfl⟩
      rcases hxe with ⟨y, hye₁, rfl⟩
      have hyΔ : y ∈ Δ := by
        have := hβ_symm_fix (β_homeo y) hxΔ
        rw [β_homeo.symm_apply_apply] at this
        exact this.symm ▸ hxΔ
      rw [hΓ₁_E] at he₁
      rcases he₁ with heΓ₀ | heM
      · have he₁_Γ : e₁ ∈ Γ.E := (mem_interSet_E_iff.mp heΓ₀).1
        have he₁_sub_Δ : e₁ ⊆ Δ := hE_meet_Δ e₁ he₁_Γ y hye₁ hyΔ
        have hβe₁ : β_homeo '' e₁ = e₁ := by
          ext z
          constructor
          · rintro ⟨w, hwe₁, rfl⟩
            rw [hβ_fix w (he₁_sub_Δ hwe₁)]
            exact hwe₁
          · intro hze₁
            exact ⟨z, hze₁, hβ_fix z (he₁_sub_Δ hze₁)⟩
        rw [hβe₁] at he_not_Γ
        exact he_not_Γ he₁_Γ
      · rw [hMU_E, mem_iUnion] at heM
        rcases heM with ⟨i, heMi⟩
        have hyDi : y ∈ D (A_fam i) := ((hM_E i e₁ heMi hye₁).1).1
        exact Set.disjoint_left.mp (h_ii i) hyDi hyΔ
    · rw [mem_iUnion] at heN'
      rcases heN' with ⟨i, hei⟩
      exact he_not_Γ (mem_interSet_E_iff.mp hei).1
  -- 5. `IsVariant Γ Γ₃ (closure (Set.univ \ Δ))`:
  have hVar_clΔ : IsVariant Γ Γ₃ (closure (Set.univ \ Δ)) := by
    refine ⟨?_, fun e he => closure_mono (hE_diff_left e he),
      fun e he => closure_mono (hE_diff_right e he)⟩
    ext x
    simp only [mem_sdiff]
    constructor
    · rintro ⟨hxΓ, hx_not_cl⟩
      have hxΔ : x ∈ Δ := by
        by_contra hx_not_Δ
        exact hx_not_cl (subset_closure ⟨trivial, hx_not_Δ⟩)
      have hx_diff : x ∈ Γ.V \ (Set.univ \ Δ) := ⟨hxΓ, fun h => h.2 hxΔ⟩
      rw [hV_diff_Δ] at hx_diff
      exact ⟨hx_diff.1, hx_not_cl⟩
    · rintro ⟨hxΓ₃, hx_not_cl⟩
      have hxΔ : x ∈ Δ := by
        by_contra hx_not_Δ
        exact hx_not_cl (subset_closure ⟨trivial, hx_not_Δ⟩)
      have hx_diff : x ∈ Γ₃.V \ (Set.univ \ Δ) := ⟨hxΓ₃, fun h => h.2 hxΔ⟩
      rw [← hV_diff_Δ] at hx_diff
      exact ⟨hx_diff.1, hx_not_cl⟩
  -- 6. `∀ i : Fin t, Γ.interSet (ins (F_fam i)) = Γ₃.interSet (ins (F_fam i))`:
  have hΓ_inter_ins : ∀ i : Fin t, Γ.interSet (ins (F_fam i)) = Γ₃.interSet (ins (F_fam i)) := by
    intro i
    have hci : IsClosed (ins (F_fam i)) := hins_eq i ▸ (hJ.disc_D (A_fam' i) (hA'_mem i)).1.isClosed
    have h3 := lemma_7_3_claim_3 hJ hA'_mem h_v i
    apply Drawing.ext_of_V_E
    · ext x
      rw [mem_interSet_V_iff hci, mem_interSet_V_iff hci]
      constructor
      · rintro ⟨hxΓ, hx_ins⟩
        refine ⟨?_, hx_ins⟩
        rw [hΓ₃_V]
        exact Or.inr (mem_iUnion.mpr ⟨i, mem_interSet_V hxΓ hx_ins⟩)
      · rintro ⟨hxΓ₃, hx_ins⟩
        refine ⟨?_, hx_ins⟩
        rw [hΓ₃_V] at hxΓ₃
        rcases hxΓ₃ with hxΓ₂ | hxN'
        · have hxU : x ∈ Γ₂.U ∩ D (A_fam' i) := ⟨Γ₂.V_subset_U hxΓ₂, hins_eq i ▸ hx_ins⟩
          rw [hΓ₂_inter_DA' i, ← h3] at hxU
          exact hxU.2
        · rw [mem_iUnion] at hxN'
          rcases hxN' with ⟨j, hxj⟩
          exact interSet_isSub.1 hxj
    · ext e
      rw [mem_interSet_E_iff, mem_interSet_E_iff]
      constructor
      · rintro ⟨heΓ, he_sub⟩
        refine ⟨?_, he_sub⟩
        rw [hΓ₃_E]
        exact Or.inr (mem_iUnion.mpr ⟨i, mem_interSet_E_iff.mpr ⟨heΓ, he_sub⟩⟩)
      · rintro ⟨heΓ₃, he_sub⟩
        refine ⟨?_, he_sub⟩
        rw [hΓ₃_E] at heΓ₃
        rcases heΓ₃ with heΓ₂ | heN'
        · exfalso
          obtain ⟨z, hze⟩ := heΓ₂.1
          have hz_U : z ∈ Γ₂.U ∩ D (A_fam' i) := ⟨(heΓ₂.2.1 hze).1, hins_eq i ▸ he_sub hze⟩
          rw [hΓ₂_inter_DA' i] at hz_U
          exact (heΓ₂.2.1 hze).2 (hΓ₂_V_DA' i hz_U)
        · rw [mem_iUnion] at heN'
          rcases heN' with ⟨j, hej⟩
          exact (mem_interSet_E_iff.mp hej).1
  -- 7. `Γ₃.interSet S_prime = mapDrawingHomeo β_homeo Γ₁`:
  have hΓ₂_U_sub_S_prime : Γ₂.U ⊆ S_prime := by
    intro x hxΓ₂
    refine ⟨trivial, ?_⟩
    rw [mem_iUnion]
    rintro ⟨i, hx_ins, hx_not_F⟩
    have hxU : x ∈ Γ₂.U ∩ D (A_fam' i) := ⟨hxΓ₂, hins_eq i ▸ hx_ins⟩
    rw [hΓ₂_inter_DA' i] at hxU
    exact hx_not_F ((hJ.range_πS_subset_D_and_ncard (hA'_mem i)).1 hxU)
  have hΓ₃_inter_S_prime : Γ₃.interSet S_prime = Γ₂ := by
    apply Drawing.ext_of_V_E
    · ext x
      rw [mem_interSet_V_iff hS_prime_closed]
      constructor
      · rintro ⟨hxΓ₃, hxS_prime⟩
        rw [hΓ₃_V] at hxΓ₃
        rcases hxΓ₃ with hxΓ₂ | hxN'
        · exact hxΓ₂
        · rw [mem_iUnion] at hxN'
          rcases hxN' with ⟨i, hxi⟩
          have hci : IsClosed (ins (F_fam i)) := hins_eq i ▸ (hJ.disc_D (A_fam' i) (hA'_mem i)).1.isClosed
          have hx_V_ins := (mem_interSet_V_iff hci).mp hxi
          have hx_F : x ∈ F_fam i := by
            by_contra hx_not_F
            exact hxS_prime.2 (mem_iUnion.mpr ⟨i, hx_V_ins.2, hx_not_F⟩)
          have h3 := lemma_7_3_claim_3 hJ hA'_mem h_v i
          have hx_π' : x ∈ Set.range (πS (A_fam' i)) := h3 ▸ ⟨hx_F, hx_V_ins.1⟩
          exact hΓ₂_V_DA' i hx_π'
      · intro hxΓ₂
        refine ⟨?_, hΓ₂_U_sub_S_prime (Γ₂.V_subset_U hxΓ₂)⟩
        rw [hΓ₃_V]
        exact Or.inl hxΓ₂
    · ext e
      rw [mem_interSet_E_iff]
      constructor
      · rintro ⟨heΓ₃, heS_prime⟩
        rw [hΓ₃_E] at heΓ₃
        rcases heΓ₃ with heΓ₂ | heN'
        · exact heΓ₂
        · exfalso
          rw [mem_iUnion] at heN'
          rcases heN' with ⟨i, hei⟩
          have he_Γ_ins := mem_interSet_E_iff.mp hei
          obtain ⟨z, hze⟩ := he_Γ_ins.1.1
          have hz_F : z ∈ F_fam i := by
            by_contra hz_not_F
            exact (heS_prime hze).2 (mem_iUnion.mpr ⟨i, he_Γ_ins.2 hze, hz_not_F⟩)
          have hz_V : z ∈ Γ.V :=
            (hJ.disc_D (A_fam' i) (hA'_mem i)).2.1 ⟨hz_F, (he_Γ_ins.1.2.1 hze).1⟩
          exact (he_Γ_ins.1.2.1 hze).2 hz_V
      · intro heΓ₂
        refine ⟨?_, fun x hxe => hΓ₂_U_sub_S_prime (heΓ₂.2.1 hxe).1⟩
        rw [hΓ₃_E]
        exact Or.inl heΓ₂
  -- 8. `IsVariant Γ Γ₃ R ∧ IsVariant Γ Γ₃ (R ∩ S_prime)`:
  have h71 := (theorem_7_1_proof hJ).1.1
  have hAtom_R : ∀ a ∈ Γ.A, (a ∩ (Set.univ \ Δ)).Nonempty →
      ∀ v ∈ Γ.V, ιV v ∈ V(K₁) → θ ≤ d a {v} := by
    intro a ha ha_ne v hvΓ hvK₁
    have hθ_dist : θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ) := h71 v hvΓ hvK₁
    have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hvΓ, rfl⟩)
    have hex : ∃ a' ∈ Γ.A, ∃ b' ∈ Γ.A, (a' ∩ {v}).Nonempty ∧ (b' ∩ (Set.univ \ Δ)).Nonempty :=
      ⟨{v}, hvA, a, ha, ⟨v, rfl, rfl⟩, ha_ne⟩
    have hle : subsetTangleDist Γ ord d {v} (Set.univ \ Δ) ≤ d {v} a := by
      unfold subsetTangleDist
      simp only [hex, ↓reduceIte]
      exact Nat.sInf_le ⟨{v}, hvA, a, ha, ⟨v, rfl, rfl⟩, ha_ne, rfl⟩
    rw [HasTangleMetric.comm hJ.hasMetric hvA ha] at hle
    exact hθ_dist.trans hle
  have hCompl_sub_R : Set.univ \ Δ ⊆ R := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := exists_atom Γ x
    refine Set.mem_biUnion (x := a) ?_ hxa
    refine ⟨ha, fun v hvΓ hvK₁ => ?_⟩
    have := hAtom_R a ha ⟨x, hxa, hx⟩ v hvΓ hvK₁
    omega
  have hV_cl_sub_R : Γ.V ∩ closure (Set.univ \ Δ) ⊆ R := by
    rintro x ⟨hxΓ, hx_cl⟩
    have hxA : ({x} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨x, hxΓ, rfl⟩)
    obtain ⟨a, ha, hx_cla, ha_ne⟩ := GM16.exists_atom_meeting_of_mem_closure hS Γ hx_cl
    have hd_xa : d {x} a ≤ 2 :=
      GM16.vertex_atom_dist_le_two hS hJ.hasMetric x hxΓ a ha hx_cla
    refine Set.mem_biUnion (x := {x}) ?_ rfl
    refine ⟨hxA, fun v hvΓ hvK₁ => ?_⟩
    have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hvΓ, rfl⟩)
    have hd_av : θ ≤ d a {v} := hAtom_R a ha ha_ne v hvΓ hvK₁
    have htri : d a {v} ≤ d a {x} + d {x} {v} :=
      HasTangleMetric.triangle hS hJ.hasMetric ha hxA hvA
    rw [HasTangleMetric.comm hJ.hasMetric ha hxA] at htri
    omega
  have hVar_R : IsVariant Γ Γ₃ R := by
    refine ⟨?_, ?_, ?_⟩
    · ext x
      simp only [mem_sdiff]
      constructor
      · rintro ⟨hxΓ, hx_not_R⟩
        have hx_diff : x ∈ Γ.V \ (Set.univ \ Δ) :=
          ⟨hxΓ, fun hx_c => hx_not_R (hCompl_sub_R hx_c)⟩
        rw [hV_diff_Δ] at hx_diff
        exact ⟨hx_diff.1, hx_not_R⟩
      · rintro ⟨hxΓ₃, hx_not_R⟩
        have hx_diff : x ∈ Γ₃.V \ (Set.univ \ Δ) :=
          ⟨hxΓ₃, fun hx_c => hx_not_R (hCompl_sub_R hx_c)⟩
        rw [← hV_diff_Δ] at hx_diff
        exact ⟨hx_diff.1, hx_not_R⟩
    · intro e he x hx_cl
      have he_c : e ⊆ Set.univ \ Δ := hE_diff_left e he
      by_cases hxe : x ∈ e
      · exact hCompl_sub_R (he_c hxe)
      · have hxV : x ∈ Γ.V := by
          by_contra hx_not_V
          exact hxe (Γ.closure_diff_V he.1 ▸ ⟨hx_cl, hx_not_V⟩)
        exact hV_cl_sub_R ⟨hxV, closure_mono he_c hx_cl⟩
    · intro e he x hx_cl
      have he_c : e ⊆ Set.univ \ Δ := hE_diff_right e he
      by_cases hx_c : x ∈ Set.univ \ Δ
      · exact hCompl_sub_R hx_c
      · have hxe : x ∉ e := fun h => hx_c (he_c h)
        have hxV₃ : x ∈ Γ₃.V := by
          by_contra hx_not_V₃
          exact hxe (Γ₃.closure_diff_V he.1 ▸ ⟨hx_cl, hx_not_V₃⟩)
        have hx_diff : x ∈ Γ₃.V \ (Set.univ \ Δ) := ⟨hxV₃, hx_c⟩
        rw [← hV_diff_Δ] at hx_diff
        exact hV_cl_sub_R ⟨hx_diff.1, closure_mono he_c hx_cl⟩
  have hVar_RS_prime : IsVariant Γ Γ₃ (R ∩ S_prime) := by
    refine ⟨?_, ?_, ?_⟩
    · ext x
      simp only [mem_sdiff, mem_inter_iff, not_and_or]
      constructor
      · rintro ⟨hxΓ, hx_not_R | hx_not_S_prime⟩
        · have hx_diff : x ∈ Γ.V \ R := ⟨hxΓ, hx_not_R⟩
          rw [hVar_R.V_diff_eq] at hx_diff
          exact ⟨hx_diff.1, Or.inl hx_not_R⟩
        · refine ⟨?_, Or.inr hx_not_S_prime⟩
          simp only [S_prime, mem_sdiff, mem_univ, true_and, not_not, mem_iUnion] at hx_not_S_prime
          rcases hx_not_S_prime with ⟨i, hx_ins, _⟩
          rw [hΓ₃_V]
          exact Or.inr (mem_iUnion.mpr ⟨i, mem_interSet_V hxΓ hx_ins⟩)
      · rintro ⟨hxΓ₃, hx_not_R | hx_not_S_prime⟩
        · have hx_diff : x ∈ Γ₃.V \ R := ⟨hxΓ₃, hx_not_R⟩
          rw [← hVar_R.V_diff_eq] at hx_diff
          exact ⟨hx_diff.1, Or.inl hx_not_R⟩
        · refine ⟨?_, Or.inr hx_not_S_prime⟩
          rw [hΓ₃_V] at hxΓ₃
          rcases hxΓ₃ with hxΓ₂ | hxN'
          · exact (hx_not_S_prime (hΓ₂_U_sub_S_prime (Γ₂.V_subset_U hxΓ₂))).elim
          · rw [mem_iUnion] at hxN'
            rcases hxN' with ⟨i, hxi⟩
            exact interSet_isSub.1 hxi
    · intro e he x hx_cl
      refine ⟨hVar_R.edge_subset_of_mem_diff_left e he hx_cl, ?_⟩
      have he_sub_S_prime : e ⊆ S_prime := by
        intro y hye
        refine ⟨trivial, ?_⟩
        rw [mem_iUnion]
        rintro ⟨i, hy_ins, hy_not_F⟩
        have hdisj_fr : Disjoint e (frontier (D (A_fam' i))) := by
          rw [← subBd_eq_frontier, Set.disjoint_left]
          intro w hwe hw_F
          have hw_V : w ∈ Γ.V :=
            (hJ.disc_D (A_fam' i) (hA'_mem i)).2.1 ⟨hw_F, (he.1.2.1 hwe).1⟩
          exact (he.1.2.1 hwe).2 hw_V
        have he_sub_D : e ⊆ D (A_fam' i) :=
          isPreconnected_subset_of_disjoint_frontier he.1.2.2.1.isConnected.isPreconnected
            (hJ.disc_D (A_fam' i) (hA'_mem i)).1.isClosed hdisj_fr hye (hins_eq i ▸ hy_ins)
        apply he.2
        rw [hΓ₃_E]
        exact Or.inr (mem_iUnion.mpr ⟨i, mem_interSet_E_iff.mpr ⟨he.1, (hins_eq i).symm ▸ he_sub_D⟩⟩)
      exact hS_prime_closed.closure_subset_iff.mpr he_sub_S_prime hx_cl
    · intro e he x hx_cl
      refine ⟨hVar_R.edge_subset_of_mem_diff_right e he hx_cl, ?_⟩
      have he_sub_S_prime : e ⊆ S_prime := by
        have heΓ₃ := he.1
        rw [hΓ₃_E] at heΓ₃
        rcases heΓ₃ with heΓ₂ | heN'
        · exact fun y hye => hΓ₂_U_sub_S_prime (heΓ₂.2.1 hye).1
        · rw [mem_iUnion] at heN'
          rcases heN' with ⟨i, hei⟩
          exact (he.2 (mem_interSet_E_iff.mp hei).1).elim
      exact hS_prime_closed.closure_subset_iff.mpr he_sub_S_prime hx_cl
  exact ⟨hV_diff_Δ, hE_sub_Δ, hE_diff_left, hE_diff_right, hVar_clΔ,
    hΓ_inter_ins, hΓ₃_inter_S_prime, hVar_R, hVar_RS_prime⟩

/-- **Graph Minors XXII, (7.3) Claim (7)** (page 549):
(7) *$\Gamma_3$ and $K_1$ are compatible; $\Gamma_3 \cap K_1 = \Gamma \cap K_1$; and
$\beta(H) = H$ for every subgraph $H$ of $K_1$.* -/
theorem lemma_7_3_claim_7 {q : ℕ}
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
    (hCleanV : ιV ⁻¹' V(R_G.G.toGraph) ⊆ Γ.V ∪ ⋃ A ∈ 𝒜, Set.range (πS A))
    (hCleanE : ιE ⁻¹' E(R_G.G.toGraph) ⊆ Γ.E)
    {β_homeo : S ≃ₜ S}
    (hβ_fix : ∀ z ∈ Δ, β_homeo z = z)
    {Γ₃ : Drawing S}
    (hV_diff_Δ : Γ.V \ (Set.univ \ Δ) = Γ₃.V \ (Set.univ \ Δ))
    (hE_sub_Δ : ∀ e ∈ Γ.E, e ⊆ Δ → e ∈ Γ₃.E) :
    let 𝒜_far := {A ∈ 𝒜 | θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)}
    let K₁ := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜_far)
    (Γ₃.toEmbeddedGraph ιV ιE).Compatible K₁ ∧
      (Γ₃.toEmbeddedGraph ιV ιE) ⊓ K₁ = (Γ.toEmbeddedGraph ιV ιE) ⊓ K₁ ∧
      (∀ H : Graph α β, H ≤ K₁ →
        mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo) H = H) := by
  intro 𝒜_far K₁
  have hK_le : K ≤ R_G.G.toGraph := hJ.sep_NK.1.2.1
  have hfar_le : ∀ A ∈ 𝒜_far, A ≤ R_G.G.toGraph := fun A hA => hJ.le_of_mem_𝒜 A hA.1
  have hK₁_le : K₁ ≤ R_G.G.toGraph := graphUnion_le hK_le (subgraphSUnion_le hfar_le)
  have hΓ_le : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph := hJ.Γ_le.trans deleteVerts_le
  have h2 := lemma_7_3_claim_2 hJ hCleanV
  have hv_K₁_Δ : ιV ⁻¹' V(K₁) ⊆ Δ := h2.2.2
  -- Any edge `e ∈ ιE ⁻¹' E(K₁)` has `e ∈ Γ.E` and `closure e ⊆ Δ`:
  have he_K₁_Δ : ∀ e : Set S, ιE e ∈ E(K₁) → e ∈ Γ.E ∧ closure e ⊆ Δ := by
    intro e heK₁
    have heG : e ∈ ιE ⁻¹' E(R_G.G.toGraph) := hK₁_le.edgeSet_mono heK₁
    have heΓ : e ∈ Γ.E := hCleanE heG
    refine ⟨heΓ, ?_⟩
    obtain ⟨u, v, huvK₁⟩ := K₁.exists_isLink_of_mem_edgeSet heK₁
    have huvG : R_G.G.toGraph.IsLink (ιE e) u v := huvK₁.mono hK₁_le
    have huvΓ : (Γ.toEmbeddedGraph ιV ιE).IsLink (ιE e) u v :=
      ((Compatible.of_le_le hΓ_le le_rfl).isLink_congr (mem_image_of_mem ιE heΓ) huvG.edge_mem).mpr huvG
    rcases huvΓ with ⟨e₀, x, y, ⟨he₀, hxΓ, hyΓ, hcl⟩, he₀_eq, rfl, rfl⟩
    have he₀_eq' : e₀ = e := ιE.injective he₀_eq
    subst he₀_eq'
    have hx_K₁ : x ∈ ιV ⁻¹' V(K₁) := huvK₁.left_mem
    have hx_e : x ∈ closure e₀ := by
      have : x ∈ closure e₀ ∩ Γ.V := by rw [hcl]; exact Set.mem_insert x {y}
      exact this.1
    have he_sub : e₀ ⊆ Δ := by
      by_contra hnot
      obtain ⟨z, hze, hz_not_Δ⟩ := not_subset.mp hnot
      obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
      have hxA : ({x} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨x, hxΓ, rfl⟩)
      have heA : e₀ ∈ Γ.A := Or.inl (Or.inr heΓ)
      have hd_xe : d {x} e₀ ≤ 2 :=
        GM16.vertex_atom_dist_le_two hS hJ.hasMetric x hxΓ e₀ heA hx_e
      have hθ_dist : θ ≤ subsetTangleDist Γ ord d {x} (Set.univ \ Δ) := h2.1 x hx_K₁
      have hex : ∃ a' ∈ Γ.A, ∃ b' ∈ Γ.A, (a' ∩ {x}).Nonempty ∧ (b' ∩ (Set.univ \ Δ)).Nonempty :=
        ⟨{x}, hxA, e₀, heA, ⟨x, rfl, rfl⟩, ⟨z, hze, trivial, hz_not_Δ⟩⟩
      have hle : subsetTangleDist Γ ord d {x} (Set.univ \ Δ) ≤ d {x} e₀ := by
        unfold subsetTangleDist
        simp only [hex, ↓reduceIte]
        exact Nat.sInf_le ⟨{x}, hxA, e₀, heA, ⟨x, rfl, rfl⟩, ⟨z, hze, trivial, hz_not_Δ⟩, rfl⟩
      have h4 := hJ.four_le_θ
      omega
    exact hJ.disc_Δ.1.isClosed.closure_subset_iff.mpr he_sub
  -- Helper: `Γ₃.V ∩ Δ = Γ.V ∩ Δ`
  have hV_inter_Δ : ∀ x ∈ Δ, x ∈ Γ₃.V ↔ x ∈ Γ.V := by
    intro x hxΔ
    have hx_not_c : x ∉ Set.univ \ Δ := fun h => h.2 hxΔ
    constructor
    · intro hxΓ₃
      have hx_diff : x ∈ Γ₃.V \ (Set.univ \ Δ) := ⟨hxΓ₃, hx_not_c⟩
      rw [← hV_diff_Δ] at hx_diff
      exact hx_diff.1
    · intro hxΓ
      have hx_diff : x ∈ Γ.V \ (Set.univ \ Δ) := ⟨hxΓ, hx_not_c⟩
      rw [hV_diff_Δ] at hx_diff
      exact hx_diff.1
  -- Helper: for `e ∈ E(K₁)`, `Γ₃.toEmbeddedGraph` and `Γ.toEmbeddedGraph` have the same `IsLink e`:
  have hIsLink_K₁ : ∀ e ∈ E(K₁), ∀ u v : α,
      (Γ₃.toEmbeddedGraph ιV ιE).IsLink e u v ↔ (Γ.toEmbeddedGraph ιV ιE).IsLink e u v := by
    intro e heK₁ u v
    change (∃ e₀ x y, Γ₃.toGraph.IsLink e₀ x y ∧ ιE e₀ = e ∧ ιV x = u ∧ ιV y = v) ↔
      (∃ e₀ x y, Γ.toGraph.IsLink e₀ x y ∧ ιE e₀ = e ∧ ιV x = u ∧ ιV y = v)
    constructor
    · rintro ⟨e₀, x, y, ⟨he₀₃, hx₃, hy₃, hcl⟩, rfl, rfl, rfl⟩
      have he₀_K₁ := he_K₁_Δ e₀ heK₁
      have hx_Δ : x ∈ Δ := he₀_K₁.2 ((by rw [hcl]; exact Set.mem_insert x {y} : x ∈ closure e₀ ∩ Γ₃.V).1)
      have hy_Δ : y ∈ Δ := he₀_K₁.2 ((by rw [hcl]; exact Set.mem_insert_of_mem x rfl : y ∈ closure e₀ ∩ Γ₃.V).1)
      have hcl_eq : closure e₀ ∩ Γ.V = closure e₀ ∩ Γ₃.V := by
        ext z
        simp only [mem_inter_iff]
        exact and_congr_right fun hz => (hV_inter_Δ z (he₀_K₁.2 hz)).symm
      exact ⟨e₀, x, y, ⟨he₀_K₁.1, (hV_inter_Δ x hx_Δ).mp hx₃, (hV_inter_Δ y hy_Δ).mp hy₃,
        hcl_eq.trans hcl⟩, rfl, rfl, rfl⟩
    · rintro ⟨e₀, x, y, ⟨he₀, hx, hy, hcl⟩, rfl, rfl, rfl⟩
      have he₀_K₁ := he_K₁_Δ e₀ heK₁
      have hx_Δ : x ∈ Δ := he₀_K₁.2 ((by rw [hcl]; exact Set.mem_insert x {y} : x ∈ closure e₀ ∩ Γ.V).1)
      have hy_Δ : y ∈ Δ := he₀_K₁.2 ((by rw [hcl]; exact Set.mem_insert_of_mem x rfl : y ∈ closure e₀ ∩ Γ.V).1)
      have he₀₃ : e₀ ∈ Γ₃.E := hE_sub_Δ e₀ he₀ (subset_closure.trans he₀_K₁.2)
      have hcl_eq : closure e₀ ∩ Γ₃.V = closure e₀ ∩ Γ.V := by
        ext z
        simp only [mem_inter_iff]
        exact and_congr_right fun hz => hV_inter_Δ z (he₀_K₁.2 hz)
      exact ⟨e₀, x, y, ⟨he₀₃, (hV_inter_Δ x hx_Δ).mpr hx, (hV_inter_Δ y hy_Δ).mpr hy,
        hcl_eq.trans hcl⟩, rfl, rfl, rfl⟩
  -- 1. `(Γ₃.toEmbeddedGraph ιV ιE).Compatible K₁`:
  have hCompat_Γ_K₁ : (Γ.toEmbeddedGraph ιV ιE).Compatible K₁ := Compatible.of_le_le hΓ_le hK₁_le
  have hCompat : (Γ₃.toEmbeddedGraph ιV ιE).Compatible K₁ := by
    intro e he₃ heK₁ u v
    rw [hIsLink_K₁ e heK₁ u v]
    rcases he₃ with ⟨e₀, _, rfl⟩
    have heΓ : ιE e₀ ∈ E(Γ.toEmbeddedGraph ιV ιE) := ⟨e₀, (he_K₁_Δ e₀ heK₁).1, rfl⟩
    exact hCompat_Γ_K₁.isLink_congr heΓ heK₁
  -- 2. `(Γ₃.toEmbeddedGraph ιV ιE) ⊓ K₁ = (Γ.toEmbeddedGraph ιV ιE) ⊓ K₁`:
  have hInter_eq : (Γ₃.toEmbeddedGraph ιV ιE) ⊓ K₁ = (Γ.toEmbeddedGraph ιV ιE) ⊓ K₁ := by
    refine Graph.ext ?_ fun e u v => ?_
    · ext u
      simp only [vertexSet_inf, mem_inter_iff]
      change (u ∈ ιV '' Γ₃.V ∧ u ∈ V(K₁)) ↔ (u ∈ ιV '' Γ.V ∧ u ∈ V(K₁))
      constructor
      · rintro ⟨⟨x, hx₃, rfl⟩, huK₁⟩
        exact ⟨⟨x, (hV_inter_Δ x (hv_K₁_Δ huK₁)).mp hx₃, rfl⟩, huK₁⟩
      · rintro ⟨⟨x, hx, rfl⟩, huK₁⟩
        exact ⟨⟨x, (hV_inter_Δ x (hv_K₁_Δ huK₁)).mpr hx, rfl⟩, huK₁⟩
    · rw [inf_isLink, inf_isLink]
      exact and_congr_left fun huvK₁ => hIsLink_K₁ e huvK₁.edge_mem u v
  -- 3. `∀ H ≤ K₁, mapGraphEquiv ... H = H`:
  have hMap_eq : ∀ H : Graph α β, H ≤ K₁ →
      mapGraphEquiv (homeoVertEquiv ιV β_homeo) (homeoEdgeEquiv ιE β_homeo) H = H := by
    intro H hH
    apply mapGraphEquiv_eq_self
    · intro u huH
      by_cases hu : u ∈ Set.range ιV
      · rcases hu with ⟨x, rfl⟩
        rw [homeoVertEquiv_apply_ιV]
        have hxΔ : x ∈ Δ := hv_K₁_Δ (hH.vertexSet_mono huH)
        rw [hβ_fix x hxΔ]
      · exact homeoVertEquiv_apply_of_not_mem ιV β_homeo hu
    · intro e heH
      by_cases he : e ∈ Set.range ιE
      · rcases he with ⟨e₀, rfl⟩
        rw [homeoEdgeEquiv_apply_ιE]
        have he₀_Δ : e₀ ⊆ Δ := subset_closure.trans (he_K₁_Δ e₀ (hH.edgeSet_mono heH)).2
        congr 1
        ext x
        constructor
        · rintro ⟨y, hye₀, rfl⟩
          rw [hβ_fix y (he₀_Δ hye₀)]
          exact hye₀
        · intro hxe₀
          exact ⟨x, hxe₀, hβ_fix x (he₀_Δ hxe₀)⟩
      · exact homeoEdgeEquiv_apply_of_not_mem ιE β_homeo he
  exact ⟨hCompat, hInter_eq, hMap_eq⟩

end GraphMinor.GM22
