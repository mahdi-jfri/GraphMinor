module

public import GraphMinor.GM08.Section15Tube
public import GraphMinor.GM08.Section14Sim
import GraphMinor.GM07.SideDisc
import GraphMinor.GM07.CylinderCap
import GraphMinor.Menger.Basic
import GraphMinor.Thomas.Separator

/-!
# Graph Minors VIII, Section 15: Framing Sub-grafts and Menger Across Laminar Hoops

This file develops the sub-graft and sub-framing induced on $\Sigma(F_1', F_2')$ by a framing
$(\Gamma, F_1, F_2)$ of a graft $(G, T)$, and proves the Menger path-existence step across
possibly-touching $\Gamma$-normal laminar hoops $H_1, H_2 \subseteq \Sigma(F_1, F_2)$ in a tube of
width $\ge r$ when neither $H_1$ nor $H_2$ is cut-trivial (used in the proof of (15.1)).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Topology Classical Graph GraphMinor.Surface GraphMinor.GM11

universe u v w

/-! ## 1. Subdrawings Between Normal Laminar Hoops -/

section SubdrawingBetweenHoops

variable {S : Type w} [TopologicalSpace S]

theorem CylinderSphereCap.swap_disc₁_disc₂ (cap : CylinderSphereCap S) (hS : IsSurface S)
    {F : Set S} (hF : IsHoop F) :
    cap.swap.disc₁ hS hF = cap.disc₂ hS hF ∧ cap.swap.disc₂ hS hF = cap.disc₁ hS hF := by
  obtain ⟨h1, h2, hb1, hb2, _, hcap, hD1, hD2⟩ := cap.disc₁_disc₂_spec hS hF
  obtain ⟨h1', h2', hb1', hb2', _, _, hD1', hD2'⟩ := cap.swap.disc₁_disc₂_spec hS hF
  exact cap.swap.hoop_discs_unique h2 h1 hb2 hb1 (by rw [inter_comm, hcap]) hD2 hD1
    h1' h2' hb1' hb2' hD1' hD2'

theorem CylinderSphereCap.exists_oriented (hS : IsCylinder S) {F₁ F₂ : Set S}
    (hF₁ : IsHoop F₁) (hF₂ : IsHoop F₂) (hlam : AreLaminarHoops F₁ F₂) :
    ∃ cap : CylinderSphereCap S, cap.disc₁ hS.1 hF₁ ⊆ cap.disc₁ hS.1 hF₂ := by
  obtain ⟨cap₀⟩ := CylinderSphereCap.exists_of_isCylinder hS
  rcases (cap₀.areLaminarHoops_iff hS hF₁ hF₂).mp hlam with hle | hge
  · exact ⟨cap₀, hle⟩
  · refine ⟨cap₀.swap, ?_⟩
    rw [(cap₀.swap_disc₁_disc₂ hS.1 hF₁).1, (cap₀.swap_disc₁_disc₂ hS.1 hF₂).1]
    exact (cap₀.disc₂_subset_iff_disc₁_subset hS.1 hF₂ hF₁).mpr hge

/-- Cap-free edge dichotomy: if `H` is a `Γ`-normal hoop in `Σ(F₁, F₂)` for laminar hoops `F₁, F₂`,
every edge `e ∈ Γ.E` contained in `Σ(F₁, F₂)` lies either in `Σ(F₁, H)` or in `Σ(H, F₂)`, and
never in both. -/
theorem edge_subset_cylinderBetween_left_or_right (Γ : Drawing S) {F₁ H F₂ e : Set S}
    (hlam : AreLaminarHoops F₁ F₂) (hH : IsHoop H) (hsub : H ⊆ cylinderBetween F₁ F₂)
    (hNH : Γ.IsNormal H) (he : e ∈ Γ.E) (he_sub : e ⊆ cylinderBetween F₁ F₂) :
    (e ⊆ cylinderBetween F₁ H ∧ ¬ e ⊆ cylinderBetween H F₂) ∨
      (e ⊆ cylinderBetween H F₂ ∧ ¬ e ⊆ cylinderBetween F₁ H) := by
  obtain ⟨hS, hF₁, hF₂, -⟩ := id hlam
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented hS hF₁ hF₂ hlam
  obtain ⟨hle1, hle2⟩ := (cap.hoop_subset_cylinderBetween_iff hS hF₁ hF₂ hH hle).mp hsub
  exact cap.edge_subset_left_or_right hS Γ hF₁ hH hF₂ hle1 hle2 hNH he he_sub

/-- When `F₁, F₂` are `Γ`-normal laminar hoops in a cylinder `S`, the point-set of
`Γ.interSet (cylinderBetween F₁ F₂)` is exactly `Γ.U ∩ cylinderBetween F₁ F₂`. -/
theorem interSet_U_eq_of_laminar_normal [T1Space S] (Γ : Drawing S) {F₁ F₂ : Set S}
    (hlam : AreLaminarHoops F₁ F₂) (hN₁ : Γ.IsNormal F₁) (hN₂ : Γ.IsNormal F₂) :
    (Γ.interSet (cylinderBetween F₁ F₂)).U = Γ.U ∩ cylinderBetween F₁ F₂ := by
  obtain ⟨hS, hF₁, hF₂, -⟩ := id hlam
  have hcl : IsClosed (cylinderBetween F₁ F₂) := isClosed_cylinderBetween hlam
  apply Subset.antisymm (interSet_U_subset_of_isClosed Γ hcl)
  rintro x ⟨hxU, hxB⟩
  by_cases hxV : x ∈ Γ.V
  · exact (Γ.interSet _).V_subset_U ((interSet_V_of_isClosed Γ hcl).symm ▸ ⟨hxV, hxB⟩)
  · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
    obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented hS hF₁ hF₂ hlam
    have he_dis₁ : Disjoint e F₁ :=
      disjoint_left.mpr fun y hye hyF => (he.2.1 hye).2 (hN₁ ⟨hyF, (he.2.1 hye).1⟩)
    have he_dis₂ : Disjoint e F₂ :=
      disjoint_left.mpr fun y hye hyF => (he.2.1 hye).2 (hN₂ ⟨hyF, (he.2.1 hye).1⟩)
    have he_prec : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
    have hx_cyl := cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ hle ▸ hxB
    have hx_s₂ : x ∈ cap.side₂ hS.1 hF₁ := by
      rw [cap.side₂_eq_preimage_diff hS.1 hF₁]
      exact ⟨hx_cyl.2, fun ⟨y, hy, heq⟩ => disjoint_left.mp he_dis₁ hxe (cap.inj heq ▸ hy)⟩
    have hx_s₁ : x ∈ cap.side₁ hS.1 hF₂ := by
      rw [cap.side₁_eq_preimage_diff hS.1 hF₂]
      exact ⟨hx_cyl.1, fun ⟨y, hy, heq⟩ => disjoint_left.mp he_dis₂ hxe (cap.inj heq ▸ hy)⟩
    have he_cov₁ : e ⊆ cap.side₁ hS.1 hF₁ ∪ cap.side₂ hS.1 hF₁ := by
      rw [cap.side₁_union_side₂ hS.1 hF₁]
      exact fun y hye => ⟨mem_univ y, disjoint_left.mp he_dis₁ hye⟩
    have he_cov₂ : e ⊆ cap.side₁ hS.1 hF₂ ∪ cap.side₂ hS.1 hF₂ := by
      rw [cap.side₁_union_side₂ hS.1 hF₂]
      exact fun y hye => ⟨mem_univ y, disjoint_left.mp he_dis₂ hye⟩
    have he_s₂ : e ⊆ cap.side₂ hS.1 hF₁ := by
      intro y hye
      rcases he_cov₁ hye with hy1 | hy2
      · obtain ⟨w, _, hw1, hw2⟩ := he_prec _ _ (cap.isOpen_side₁ hS.1 hF₁)
          (cap.isOpen_side₂ hS.1 hF₁) he_cov₁ ⟨y, hye, hy1⟩ ⟨x, hxe, hx_s₂⟩
        exact absurd hw2 (disjoint_left.mp (cap.disjoint_side₁_side₂ hS.1 hF₁) hw1)
      · exact hy2
    have he_s₁ : e ⊆ cap.side₁ hS.1 hF₂ := by
      intro y hye
      rcases he_cov₂ hye with hy1 | hy2
      · exact hy1
      · obtain ⟨w, _, hw1, hw2⟩ := he_prec _ _ (cap.isOpen_side₁ hS.1 hF₂)
          (cap.isOpen_side₂ hS.1 hF₂) he_cov₂ ⟨x, hxe, hx_s₁⟩ ⟨y, hye, hy2⟩
        exact absurd hw2 (disjoint_left.mp (cap.disjoint_side₁_side₂ hS.1 hF₂) hw1)
    have he_sub : e ⊆ cylinderBetween F₁ F₂ := by
      rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ hle]
      exact fun y hye =>
        ⟨(cap.side₁_eq_preimage_diff hS.1 hF₂ ▸ he_s₁ hye).1,
         (cap.side₂_eq_preimage_diff hS.1 hF₁ ▸ he_s₂ hye).1⟩
    have he_mem : e ∈ (Γ.interSet (cylinderBetween F₁ F₂)).E :=
      (interSet_E Γ _).symm ▸ ⟨he, he_sub⟩
    exact (Γ.interSet _).closure_subset_U he_mem (subset_closure hxe)

end SubdrawingBetweenHoops

/-! ## 2. Sub-graphs, Sub-grafts, and Sub-framings Induced by Laminar Hoops -/

namespace Tube.Framing

variable {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
  {τ : Tube S} {X : Graft α β}

/-- The set of vertices of `X.G` mapped into `A ⊆ S` by a framing `fr : τ.Framing X`. -/
def vertsIn (fr : τ.Framing X) (A : Set S) : Set α :=
  {v : α | ∃ hv : v ∈ V(X.G), (fr.iso.vertexEquiv ⟨v, hv⟩).1 ∈ A}

/-- The set of edges of `X.G` whose corresponding edge in `τ.Γ.E` is contained in `A ⊆ S`. -/
def edgesIn (fr : τ.Framing X) (A : Set S) : Set β :=
  {e : β | ∃ he : e ∈ E(X.G), (fr.iso.edgeEquiv ⟨e, he⟩).1 ⊆ A}

theorem vertsIn_subset_V (fr : τ.Framing X) (A : Set S) : fr.vertsIn A ⊆ V(X.G) :=
  fun _ ⟨hv, _⟩ => hv

theorem edgesIn_subset_E (fr : τ.Framing X) (A : Set S) : fr.edgesIn A ⊆ E(X.G) :=
  fun _ ⟨he, _⟩ => he

theorem mem_vertsIn_iff (fr : τ.Framing X) (A : Set S) (v : V(X.G)) :
    v.1 ∈ fr.vertsIn A ↔ (fr.iso.vertexEquiv v).1 ∈ A :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.2, h⟩⟩

theorem vertsIn_mono (fr : τ.Framing X) {A B : Set S} (h : A ⊆ B) :
    fr.vertsIn A ⊆ fr.vertsIn B :=
  fun _ ⟨hv, hm⟩ => ⟨hv, h hm⟩

theorem edgesIn_mono (fr : τ.Framing X) {A B : Set S} (h : A ⊆ B) :
    fr.edgesIn A ⊆ fr.edgesIn B :=
  fun _ ⟨he, hm⟩ => ⟨he, hm.trans h⟩

theorem vertsIn_union (fr : τ.Framing X) (A B : Set S) :
    fr.vertsIn (A ∪ B) = fr.vertsIn A ∪ fr.vertsIn B := by
  ext v
  exact ⟨fun ⟨hv, h⟩ => h.imp (fun ha => ⟨hv, ha⟩) (fun hb => ⟨hv, hb⟩),
    fun h => h.elim (fun ⟨hv, ha⟩ => ⟨hv, Or.inl ha⟩) (fun ⟨hv, hb⟩ => ⟨hv, Or.inr hb⟩)⟩

theorem vertsIn_inter (fr : τ.Framing X) (A B : Set S) :
    fr.vertsIn (A ∩ B) = fr.vertsIn A ∩ fr.vertsIn B := by
  ext v
  exact ⟨fun ⟨hv, ha, hb⟩ => ⟨⟨hv, ha⟩, ⟨hv, hb⟩⟩,
    fun ⟨⟨hv, ha⟩, ⟨_, hb⟩⟩ => ⟨hv, ha, hb⟩⟩

theorem vertsIn_F_union (fr : τ.Framing X) :
    fr.vertsIn τ.F₁ ∪ fr.vertsIn τ.F₂ = X.T := by
  rw [← fr.vertsIn_union]
  ext v
  constructor
  · rintro ⟨hv, h⟩
    exact (fr.mem_F_iff ⟨v, hv⟩).mp h
  · intro hvT
    have hv : v ∈ V(X.G) := X.T_subset hvT
    exact ⟨hv, (fr.mem_F_iff ⟨v, hv⟩).mpr hvT⟩

theorem vertsIn_cylinderBetween_F (fr : τ.Framing X) :
    fr.vertsIn (cylinderBetween τ.F₁ τ.F₂) = V(X.G) := by
  apply Subset.antisymm (fr.vertsIn_subset_V _)
  intro v hv
  exact ⟨hv, τ.U_subset (τ.Γ.V_subset_U (fr.iso.vertexEquiv ⟨v, hv⟩).2)⟩

theorem edgesIn_cylinderBetween_F (fr : τ.Framing X) :
    fr.edgesIn (cylinderBetween τ.F₁ τ.F₂) = E(X.G) := by
  apply Subset.antisymm (fr.edgesIn_subset_E _)
  intro e he
  refine ⟨he, fun x hx => ?_⟩
  exact τ.U_subset (((fr.iso.edgeEquiv ⟨e, he⟩).2.2.1 hx).1)

theorem ncard_vertsIn (fr : τ.Framing X) (A : Set S) :
    (fr.vertsIn A).ncard = (A ∩ τ.Γ.V).ncard := by
  let f : fr.vertsIn A ≃ ↑(A ∩ τ.Γ.V) :=
    { toFun := fun v =>
        let hv : v.1 ∈ V(X.G) := v.2.1
        ⟨(fr.iso.vertexEquiv ⟨v.1, hv⟩).1, v.2.2, (fr.iso.vertexEquiv ⟨v.1, hv⟩).2⟩
      invFun := fun z =>
        let hz : z.1 ∈ A ∧ z.1 ∈ τ.Γ.V := z.2
        let z' : V(τ.Γ.toGraph) := ⟨z.1, hz.2⟩
        ⟨(fr.iso.vertexEquiv.symm z').1, (fr.iso.vertexEquiv.symm z').2, by
          change (fr.iso.vertexEquiv (fr.iso.vertexEquiv.symm z')).1 ∈ A
          rw [fr.iso.vertexEquiv.apply_symm_apply]
          exact hz.1⟩
      left_inv := fun v => by
        apply Subtype.ext
        change (fr.iso.vertexEquiv.symm (fr.iso.vertexEquiv ⟨v.1, v.2.1⟩)).1 = v.1
        rw [fr.iso.vertexEquiv.symm_apply_apply]
      right_inv := fun z => by
        apply Subtype.ext
        have hz : z.1 ∈ A ∧ z.1 ∈ τ.Γ.V := z.2
        change (fr.iso.vertexEquiv (fr.iso.vertexEquiv.symm ⟨z.1, hz.2⟩)).1 = z.1
        rw [fr.iso.vertexEquiv.apply_symm_apply] }
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr f

theorem ends_mem_vertsIn_of_isClosed (fr : τ.Framing X) {A : Set S} (hA : IsClosed A)
    {e : β} {x y : α} (he : e ∈ fr.edgesIn A) (hl : X.G.IsLink e x y) :
    x ∈ fr.vertsIn A ∧ y ∈ fr.vertsIn A := by
  obtain ⟨heE, heA⟩ := he
  let x₀ : V(X.G) := ⟨x, hl.left_mem⟩
  let y₀ : V(X.G) := ⟨y, hl.right_mem⟩
  have hl' := (fr.iso.isLink_iff ⟨e, heE⟩ x₀ y₀).mp hl
  have hclA : closure (fr.iso.edgeEquiv ⟨e, heE⟩).1 ⊆ A := closure_minimal heA hA
  have hx_cl : (fr.iso.vertexEquiv x₀).1 ∈ closure (fr.iso.edgeEquiv ⟨e, heE⟩).1 ∩ τ.Γ.V :=
    hl'.2.2.2 ▸ mem_insert _ _
  have hy_cl : (fr.iso.vertexEquiv y₀).1 ∈ closure (fr.iso.edgeEquiv ⟨e, heE⟩).1 ∩ τ.Γ.V :=
    hl'.2.2.2 ▸ mem_insert_of_mem _ rfl
  exact ⟨⟨x₀.2, hclA hx_cl.1⟩, ⟨y₀.2, hclA hy_cl.1⟩⟩

/-- The subgraph of `X.G` drawn inside a closed subset `A ⊆ S`. -/
def subGraph (fr : τ.Framing X) (A : Set S) (hA : IsClosed A) : Graph α β :=
  subgraphOfVertsEdges X.G (fr.vertsIn A) (fr.edgesIn A) (fr.vertsIn_subset_V A)
    (fun _ _ _ he hl => fr.ends_mem_vertsIn_of_isClosed hA he hl)

@[simp]
theorem subGraph_vertexSet (fr : τ.Framing X) (A : Set S) (hA : IsClosed A) :
    V(fr.subGraph A hA) = fr.vertsIn A :=
  rfl

@[simp]
theorem subGraph_isLink (fr : τ.Framing X) (A : Set S) (hA : IsClosed A)
    (e : β) (x y : α) :
    (fr.subGraph A hA).IsLink e x y ↔ e ∈ fr.edgesIn A ∧ X.G.IsLink e x y :=
  Iff.rfl

theorem subGraph_edgeSet (fr : τ.Framing X) (A : Set S) (hA : IsClosed A) :
    E(fr.subGraph A hA) = fr.edgesIn A := by
  ext e
  rw [(fr.subGraph A hA).edge_mem_iff_exists_isLink]
  constructor
  · rintro ⟨_, _, he, _⟩; exact he
  · intro he
    obtain ⟨x, y, hl⟩ := (X.G.edge_mem_iff_exists_isLink e).mp he.1
    exact ⟨x, y, he, hl⟩

theorem subGraph_le (fr : τ.Framing X) (A : Set S) (hA : IsClosed A) :
    fr.subGraph A hA ≤ X.G :=
  subgraphOfVertsEdges_le _ _ _ _ _

/-- The sub-graft of `X` cut out by laminar hoops `H₁, H₂`, with graph `fr.subGraph Σ(H₁, H₂)` and
root set `(H₁ ∪ H₂)`-vertices. -/
def subGraft (fr : τ.Framing X) {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂) : Graft α β where
  G := fr.subGraph (cylinderBetween H₁ H₂) (isClosed_cylinderBetween hlam)
  T := fr.vertsIn H₁ ∪ fr.vertsIn H₂
  T_subset := union_subset
    (fr.vertsIn_mono (subset_cylinderBetween_left hlam))
    (fr.vertsIn_mono (subset_cylinderBetween_right hlam))
  finite_G := ⟨X.finite_G.1.subset (fr.vertsIn_subset_V _),
    X.finite_G.2.subset ((fr.subGraph_edgeSet _ _).trans_subset (fr.edgesIn_subset_E _))⟩

/-- The induced framing `(τ.subTube hlam hN₁ hN₂).Framing (fr.subGraft hlam)`. -/
noncomputable def subFraming (fr : τ.Framing X) {H₁ H₂ : Set S}
    (hlam : AreLaminarHoops H₁ H₂) (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂) :
    (τ.subTube hlam hN₁ hN₂).Framing (fr.subGraft hlam) :=
  letI : T2Space S := τ.t2Space
  let A := cylinderBetween H₁ H₂
  have hA : IsClosed A := isClosed_cylinderBetween hlam
  have hVEq : (τ.Γ.interSet A).V = τ.Γ.V ∩ A := interSet_V_of_isClosed τ.Γ hA
  have hEEq : (τ.Γ.interSet A).E = {ed ∈ τ.Γ.E | ed ⊆ A} := interSet_E τ.Γ A
  have hEG : E((fr.subGraft hlam).G) = fr.edgesIn A := fr.subGraph_edgeSet A hA
  { iso :=
      { vertexEquiv :=
          { toFun := fun v =>
              let v₀ : V(X.G) := ⟨v.1, v.2.1⟩
              ⟨(fr.iso.vertexEquiv v₀).1, by
                change (fr.iso.vertexEquiv v₀).1 ∈ (τ.Γ.interSet A).V
                rw [hVEq]
                exact ⟨(fr.iso.vertexEquiv v₀).2, v.2.2⟩⟩
            invFun := fun z =>
              have hz : z.1 ∈ τ.Γ.V ∩ A := hVEq ▸ (show z.1 ∈ (τ.Γ.interSet A).V from z.2)
              let z' : V(τ.Γ.toGraph) := ⟨z.1, hz.1⟩
              ⟨(fr.iso.vertexEquiv.symm z').1, (fr.iso.vertexEquiv.symm z').2, by
                change (fr.iso.vertexEquiv (fr.iso.vertexEquiv.symm z')).1 ∈ A
                rw [fr.iso.vertexEquiv.apply_symm_apply]
                exact hz.2⟩
            left_inv := fun v => by
              apply Subtype.ext
              change (fr.iso.vertexEquiv.symm (fr.iso.vertexEquiv ⟨v.1, v.2.1⟩)).1 = v.1
              rw [fr.iso.vertexEquiv.symm_apply_apply]
            right_inv := fun z => by
              apply Subtype.ext
              have hz : z.1 ∈ τ.Γ.V ∩ A := hVEq ▸ (show z.1 ∈ (τ.Γ.interSet A).V from z.2)
              change (fr.iso.vertexEquiv (fr.iso.vertexEquiv.symm ⟨z.1, hz.1⟩)).1 = z.1
              rw [fr.iso.vertexEquiv.apply_symm_apply] }
        edgeEquiv :=
          { toFun := fun e =>
              have he : e.1 ∈ fr.edgesIn A := hEG ▸ e.2
              let e₀ : E(X.G) := ⟨e.1, he.1⟩
              ⟨(fr.iso.edgeEquiv e₀).1, by
                change (fr.iso.edgeEquiv e₀).1 ∈ (τ.Γ.interSet A).E
                rw [hEEq]
                exact ⟨(fr.iso.edgeEquiv e₀).2, he.2⟩⟩
            invFun := fun ed =>
              have hed : ed.1 ∈ {ed | ed ∈ τ.Γ.E ∧ ed ⊆ A} :=
                hEEq ▸ (show ed.1 ∈ (τ.Γ.interSet A).E from ed.2)
              let ed' : E(τ.Γ.toGraph) := ⟨ed.1, hed.1⟩
              ⟨(fr.iso.edgeEquiv.symm ed').1, hEG.symm ▸ ⟨(fr.iso.edgeEquiv.symm ed').2, by
                change (fr.iso.edgeEquiv (fr.iso.edgeEquiv.symm ed')).1 ⊆ A
                rw [fr.iso.edgeEquiv.apply_symm_apply]
                exact hed.2⟩⟩
            left_inv := fun e => by
              apply Subtype.ext
              have he : e.1 ∈ fr.edgesIn A := hEG ▸ e.2
              change (fr.iso.edgeEquiv.symm (fr.iso.edgeEquiv ⟨e.1, he.1⟩)).1 = e.1
              rw [fr.iso.edgeEquiv.symm_apply_apply]
            right_inv := fun ed => by
              apply Subtype.ext
              have hed : ed.1 ∈ {ed | ed ∈ τ.Γ.E ∧ ed ⊆ A} :=
                hEEq ▸ (show ed.1 ∈ (τ.Γ.interSet A).E from ed.2)
              change (fr.iso.edgeEquiv (fr.iso.edgeEquiv.symm ⟨ed.1, hed.1⟩)).1 = ed.1
              rw [fr.iso.edgeEquiv.apply_symm_apply] }
        isLink_iff := fun e x y => by
          have he : e.1 ∈ fr.edgesIn A := hEG ▸ e.2
          change ((fr.subGraph A hA).IsLink e.1 x.1 y.1) ↔
            (τ.Γ.interSet A).toGraph.IsLink (fr.iso.edgeEquiv ⟨e.1, he.1⟩).1
              (fr.iso.vertexEquiv ⟨x.1, x.2.1⟩).1 (fr.iso.vertexEquiv ⟨y.1, y.2.1⟩).1
          rw [subGraph_isLink, interSet_isLink_iff_of_isClosed τ.Γ hA]
          exact ⟨fun ⟨_, hl⟩ => ⟨he.2, (fr.iso.isLink_iff ⟨e.1, he.1⟩
              ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩).mp hl⟩,
            fun ⟨_, hl⟩ => ⟨he, (fr.iso.isLink_iff ⟨e.1, he.1⟩
              ⟨x.1, x.2.1⟩ ⟨y.1, y.2.1⟩).mpr hl⟩⟩ }
    mem_F_iff := fun v => by
      change (fr.iso.vertexEquiv ⟨v.1, v.2.1⟩).1 ∈ H₁ ∪ H₂ ↔
        v.1 ∈ fr.vertsIn H₁ ∪ fr.vertsIn H₂
      rw [← fr.vertsIn_union]
      exact ⟨fun h => ⟨v.2.1, h⟩, fun ⟨_, h⟩ => h⟩ }

theorem isFraming_subTube (fr : τ.Framing X) {H₁ H₂ : Set S}
    (hlam : AreLaminarHoops H₁ H₂) (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂) :
    (τ.subTube hlam hN₁ hN₂).IsFraming (fr.subGraft hlam) :=
  ⟨fr.subFraming hlam hN₁ hN₂⟩

end Tube.Framing

/-! ## 3. Menger Across Possibly-Touching Laminar Hoops -/

section TouchingMenger

private theorem exists_disc_of_side_touching {T : Type} [TopologicalSpace T]
    (hS : IsClosedSurface T) (hsph : IsSphere T) (Γ : Drawing T) {B₀ E₀ X K : Set T}
    (hB₀ : IsClosedDisc B₀) (hE₀ : IsClosedDisc E₀)
    (hd₁ : Disjoint B₀ (discInt E₀)) (hinterU : (discBd B₀ ∩ E₀) ∩ Γ.U ⊆ X)
    (hbd : Γ.U ∩ discBd B₀ ⊆ Γ.V) (hint : Disjoint Γ.U (discInt B₀))
    (hEU : Γ.U ∩ E₀ ⊆ Γ.V) (hEint : Disjoint Γ.U (discInt E₀))
    (hKV : K ⊆ Γ.V) (hXV : X ⊆ Γ.V) (hXK : Disjoint X K)
    (hcuff : Γ.V ∩ discBd B₀ ⊆ K ∪ X) (hKE : Disjoint K E₀)
    (hedge : ∀ e ∈ Γ.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ Γ.V, w ∈ closure e → w ∈ K ∪ X)
    {ρ : T → ℕ}
    (hreach : ∀ u ∈ K, u ∉ discBd B₀ →
      ∃ e ∈ Γ.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧ w ∈ closure e ∧ (w ∉ discBd B₀ → ρ w < ρ u)) :
    ∃ B, IsClosedDisc B ∧ B₀ ⊆ B ∧ Disjoint (discInt E₀) B ∧ discBd B ∩ Γ.U ⊆ X := by
  classical
  have ht2 : T2Space T := hS.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  by_cases hA : (Γ.V ∩ discBd B₀).Nonempty
  swap
  · refine ⟨B₀, hB₀, Subset.rfl, hd₁.symm, fun x hx => ?_⟩
    exact absurd ⟨x, hbd ⟨hx.2, hx.1⟩, hx.1⟩ hA
  obtain ⟨D, hDU, hDV⟩ := exists_drawing_on_oArc hB₀.isOArc_discBd
    (Γ.finite_V.subset inter_subset_left) hA inter_subset_right
  have hmeet : Γ.U ∩ D.U ⊆ Γ.V ∩ D.V := fun x hx => by
    have hx2 : x ∈ discBd B₀ := hDU ▸ hx.2
    have hxV := hbd ⟨hx.1, hx2⟩
    exact ⟨hxV, hDV ▸ ⟨hxV, hx2⟩⟩
  have hE₁ : Γ.E ⊆ (Γ.glue D hmeet).E := by
    rw [Drawing.glue_E]; exact subset_union_left
  have hD₁ : D.E ⊆ (Γ.glue D hmeet).E := by
    rw [Drawing.glue_E]; exact subset_union_right
  have hV₁ : Γ.V ⊆ (Γ.glue D hmeet).V := subset_union_left
  have hDV₁ : D.V ⊆ (Γ.glue D hmeet).V := subset_union_right
  have hB₀V : ∀ x ∈ Γ.U, x ∈ B₀ → x ∈ discBd B₀ ∧ x ∈ Γ.V := fun x hx h => by
    have h1 : x ∈ discBd B₀ := by
      by_contra hn
      exact disjoint_left.mp hint hx ⟨h, hn⟩
    exact ⟨h1, hbd ⟨hx, h1⟩⟩
  have hclV : ∀ g ∈ Γ.E, ∀ x ∈ closure g, x ∉ Γ.V → x ∈ g := fun g hg x hx hn => by
    obtain ⟨c, h1, h2, h3, h4, h5⟩ := exists_edge_param Γ hg
    have hc : GM07.EdgeParam Γ g c := ⟨h1, h2, h3, h4, h5⟩
    rw [hc.closure_eq] at hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨h6, h7⟩ := hc.pos_of_ne hg hn
    exact hc.mem_edge h6 h7
  have hclU : ∀ g ∈ Γ.E, closure g ⊆ Γ.U :=
    fun g hg => closure_minimal (fun x hx => (hg.2.1 hx).1) Γ.isClosed_U
  let 𝓔 : Set (Set T) := {e ∈ Γ.E | ∃ u ∈ K, u ∈ closure e}
  have h𝓔 : 𝓔.Finite := Γ.finite_edges.subset (sep_subset _ _)
  have hor : ∀ e ∈ 𝓔, ∃ c, GM07.EdgeParam Γ e c ∧ c 0 ∈ K := fun e he => by
    obtain ⟨u, hu, huc⟩ := he.2
    obtain ⟨c, h1, h2⟩ := GM07.EdgeParam.exists_orient he.1 huc (hKV hu)
    exact ⟨c, h1, h2 ▸ hu⟩
  have : Nonempty (unitInterval → T) := ⟨fun _ => hA.some⟩
  choose! γ hγ hγK using hor
  have hzex : ∀ v : T, ∃ z ∈ discBd B₀, z ≠ v := fun v => hB₀.isOArc_discBd.exists_ne v
  choose z hz hzv using hzex
  have hq1 : GM07.quarter₂ < (1 : unitInterval) := unitInterval.lt_one_iff_ne_one.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [GM07.quarter₂] at h1
  have hq0 : (0 : unitInterval) < GM07.quarter₂ := unitInterval.pos_iff_ne_zero.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [GM07.quarter₂] at h1
  let P : T → Set T := fun v =>
    (Γ.V \ {v}) ∪ (⋃ e ∈ {e ∈ Γ.E | v ∉ closure e}, closure e) ∪
      ((fun e => γ e GM07.quarter₂) '' 𝓔) ∪ E₀ ∪ (if v ∈ discBd B₀ then {z v} else B₀)
  have hPc : ∀ v ∈ K, IsClosed (P v) := fun v _ => by
    refine (((((Γ.finite_V.subset sdiff_subset).isClosed).union
      ((Γ.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun e _ => isClosed_closure)).union
      (h𝓔.image _).isClosed).union hE₀.isClosed).union ?_
    split_ifs
    · exact isClosed_singleton
    · exact hB₀.isClosed
  have hvP : ∀ v ∈ K, v ∉ P v := fun v hv => by
    rintro ((((h | h) | ⟨e, he, h⟩) | h) | h)
    · exact h.2 rfl
    · obtain ⟨e, he, h1⟩ := mem_iUnion₂.mp h
      exact he.2 h1
    · have h' : γ e GM07.quarter₂ = v := h
      exact (hγ e he).not_V he.1 hq0 hq1 (h'.symm ▸ hKV hv)
    · exact disjoint_left.mp hKE hv h
    · split_ifs at h with h2
      · exact hzv v h.symm
      · exact h2 (hB₀V v (Γ.V_subset_U (hKV hv)) h).1
  obtain ⟨R, hR, hRd⟩ := GM07.exists_star_family hS (Γ.glue D hmeet) (hKV.trans hV₁) hPc hvP
  have hRP : ∀ v ∈ K, ∀ x ∈ R v, x ∉ P v :=
    fun v hv x hx h => disjoint_left.mp (hR v hv).2 hx h
  have hoffV : ∀ v ∈ K, ∀ w ∈ Γ.V, w ≠ v → w ∉ R v :=
    fun v hv w hw hne h => hRP v hv w h (.inl (.inl (.inl (.inl ⟨hw, hne⟩))))
  have hcloff : ∀ v ∈ K, ∀ e ∈ Γ.E, v ∉ closure e → Disjoint (R v) (closure e) :=
    fun v hv e he hn => disjoint_left.mpr fun x hx h =>
      hRP v hv x hx (.inl (.inl (.inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hn⟩, h⟩)))))
  have hRE : ∀ v ∈ K, Disjoint (R v) E₀ :=
    fun v hv => disjoint_left.mpr fun x hx h => hRP v hv x hx (.inl (.inr h))
  have hRB₀ : ∀ v ∈ K, v ∉ discBd B₀ → Disjoint (R v) B₀ :=
    fun v hv hn => disjoint_left.mpr fun x hx h => hRP v hv x hx (.inr (by simp [hn, h]))
  have hpiece : ∀ e ∈ 𝓔, ∃ L a b, GM07.IsPiece Γ K X R e L a b (γ e 0) (γ e 1) := fun e he =>
    GM07.exists_piece hman hE₁ hV₁ hKV (fun v hv => (hR v hv).1) (hγ e he) he.1 (hγK e he)
      (fun v hv h => hRP v hv _ h (.inl (.inl (.inr ⟨e, he, rfl⟩))))
      hoffV (fun v hv ⟨y, h1, h2⟩ => by
        by_contra hn
        exact disjoint_left.mp (hcloff v hv e he.1 hn) h1 h2)
      (hedge e he.1 _ (hγK e he) ((hγ e he).closure_eq ▸ mem_range_self _) _ (hγ e he).mem1
        ((hγ e he).closure_eq ▸ mem_range_self _)) hXK
  have : Nonempty T := ⟨hA.some⟩
  choose! L a b hL using hpiece
  have hLU : ∀ e ∈ 𝓔, L e ⊆ Γ.U := fun e he x hx => hclU e he.1 ((hL e he).sub hx)
  have hLVmem : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ Γ.V → x = b e ∧ b e ∈ X :=
    fun e he x hx hv => (hL e he).vertex x hx hv
  have hmeetV : ∀ e ∈ 𝓔, ∀ f ∈ 𝓔, e ≠ f → ∀ x ∈ L e, x ∈ L f → x ∈ Γ.V :=
    fun e he f hf hef x hx hy => by
      rcases (hL e he).onEdge x hx with h1 | h1
      · rcases (hL f hf).onEdge x hy with h2 | h2
        · exact absurd h2 (disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he.1 hf.1 hef) h1)
        · exact h2
      · exact h1
  have hKfin : K.Finite := Γ.finite_V.subset hKV
  have hchord : ∀ v ∈ K ∩ discBd B₀, ∃ F y₁ y₂,
      IsLineWithEnds F y₁ y₂ ∧ y₁ ≠ y₂ ∧ F ⊆ R v ∧ F ∩ discBd (R v) = {y₁, y₂} ∧
        R v ∩ discBd B₀ = F ∧ v ∈ F := fun v hv => by
    have hst := (hR v hv.1).1
    refine GM07.exists_star_chord hB₀.isOArc_discBd hv.2 hst.disc (hst.disc.isOpen_discInt hman)
      hst.mem (hz v) (fun h => ?_) (fun y hy => ?_)
    · exact hRP v hv.1 _ h (.inr (by simp [hv.2]))
    · exact hst.star _ hB₀.isOArc_discBd.isCompact.isClosed
        (hDU ▸ GM07.isGammaNice_of_U hD₁ hDV₁) y hy
  choose! F y₁ y₂ hF₁ hF₂ hF₃ hF₄ hF₅ hF₆ using hchord
  have hK₀ : (K ∩ discBd B₀).Finite := hKfin.subset inter_subset_left
  have hmemK₀ : ∀ {v}, v ∈ hK₀.toFinset → v ∈ K ∩ discBd B₀ := fun {v} h => hK₀.mem_toFinset.mp h
  obtain ⟨B₁, hB₁, h1a, h1b, h1c, h1d, h1e, h1f, h1g⟩ :=
    GM07.exists_blob (R := R) (F := F) (y₁ := y₁) (y₂ := y₂) (v := id) hS hB₀ hK₀.toFinset
      (fun v hv => (hR v (hmemK₀ hv).1).1.disc)
      (fun v hv => hF₁ v (hmemK₀ hv)) (fun v hv => hF₂ v (hmemK₀ hv))
      (fun v hv => hF₃ v (hmemK₀ hv)) (fun v hv => hF₄ v (hmemK₀ hv))
      (fun v hv => hF₅ v (hmemK₀ hv)) (fun v hv => hF₆ v (hmemK₀ hv))
      (fun v hv => (hR v (hmemK₀ hv).1).1.mem)
      (fun u hu v hv huv => hRd u (hmemK₀ hu).1 v (hmemK₀ hv).1 huv)
  have hB₁cases : ∀ x ∈ B₁, x ∈ B₀ ∨ ∃ v ∈ K, v ∈ discBd B₀ ∧ x ∈ R v := fun x hx => by
    rcases h1c hx with h | h
    · exact .inl h
    · obtain ⟨v, hv, h2⟩ := mem_iUnion₂.mp h
      exact .inr ⟨v, (hmemK₀ hv).1, (hmemK₀ hv).2, h2⟩
  have hbB₁ : ∀ v ∈ K, v ∈ discBd B₀ → ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → x ∈ discBd B₁ :=
    fun v hv hvb x hx h2 h3 =>
      h1f v (hK₀.mem_toFinset.mpr ⟨hv, hvb⟩) ⟨hx, fun h => h2 (hB₀V x h3 h).2⟩
  have hintR : ∀ v ∈ K, v ∈ discBd B₀ → discInt (R v) ⊆ discInt B₁ := fun v hv hvb x hx => by
    have hm := hK₀.mem_toFinset.mpr ⟨hv, hvb⟩
    exact ⟨h1b v hm hx.1, fun h => disjoint_left.mp (h1e v hm) h hx⟩
  have hLB₁ : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ B₁ → x = a e ∨ x = b e := fun e he x hx hxB => by
    rcases hB₁cases x hxB with h | ⟨v, hv, -, h⟩
    · exact .inr (hLVmem e he x hx (hB₀V x (hLU e he hx) h).2).1
    · exact (hL e he).disc v hv x hx h
  have hvert : ∀ e ∈ 𝓔, ∀ x ∈ closure e, x ∈ Γ.V → x = γ e 0 ∨ x = γ e 1 := fun e he x hx hv => by
    rw [(hγ e he).closure_eq] at hx
    obtain ⟨y, rfl⟩ := hx
    by_contra hn
    push Not at hn
    have h1 : 0 < y := unitInterval.pos_iff_ne_zero.mpr fun e' => hn.1 (by rw [e'])
    have h2 : y < 1 := unitInterval.lt_one_iff_ne_one.mpr fun e' => hn.2 (by rw [e'])
    exact (hγ e he).not_V he.1 h1 h2 hv
  have hnoV : ∀ e ∈ 𝓔, γ e 1 ∈ K → ∀ x ∈ L e, x ∉ Γ.V := fun e he h1 x hx hv => by
    obtain ⟨-, h2⟩ := hLVmem e he x hx hv
    rcases (hL e he).b_mem with ⟨-, -, h3⟩ | ⟨h3, -⟩
    · exact h3 (hXV h2)
    · exact h3 h1
  have hbK : ∀ e ∈ 𝓔, γ e 1 ∈ K → b e ∈ discBd (R (γ e 1)) ∧ b e ∉ Γ.V := fun e he h1 => by
    rcases (hL e he).b_mem with ⟨-, h3, h4⟩ | ⟨h3, -⟩
    · exact ⟨h3, h4⟩
    · exact absurd h1 h3
  let N : Type := ↥(K \ discBd B₀)
  have htree : ∀ u : N, ∃ e ∈ 𝓔, ∃ w ∈ K, w ≠ u.1 ∧ u.1 ∈ closure e ∧ w ∈ closure e ∧
      (w ∉ discBd B₀ → ρ w < ρ u.1) := fun u => by
    obtain ⟨e, he, w, hw, h1, h2, h3, h4⟩ := hreach u.1 u.2.1 u.2.2
    exact ⟨e, ⟨he, u.1, u.2.1, h2⟩, w, hw, h1, h2, h3, h4⟩
  choose eT heT wT hwT hwne huc hwc hrk using htree
  have hTends : ∀ u : N,
      (γ (eT u) 0 = u.1 ∧ γ (eT u) 1 = wT u) ∨ (γ (eT u) 0 = wT u ∧ γ (eT u) 1 = u.1) := fun u => by
    rcases hvert _ (heT u) _ (huc u) (hKV u.2.1) with h1 | h1 <;>
      rcases hvert _ (heT u) _ (hwc u) (hKV (hwT u)) with h2 | h2
    · exact absurd (h2.trans h1.symm) (hwne u)
    · exact .inl ⟨h1.symm, h2.symm⟩
    · exact .inr ⟨h2.symm, h1.symm⟩
    · exact absurd (h2.trans h1.symm) (hwne u)
  have hT1 : ∀ u : N, γ (eT u) 1 ∈ K := fun u => by
    rcases hTends u with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ▸ hwT u
    · exact h ▸ u.2.1
  have hpq : ∀ u : N, ∃ p q, IsLineWithEnds (L (eT u)) p q ∧ p ∈ discBd (R u.1) ∧
      q ∈ discBd (R (wT u)) ∧ ({p, q} : Set T) = {a (eT u), b (eT u)} := fun u => by
    have hP := hL _ (heT u)
    have hb' := (hbK _ (heT u) (hT1 u)).1
    rcases hTends u with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a _, b _, hP.line, h1 ▸ hP.a_bd, h2 ▸ hb', rfl⟩
    · exact ⟨b _, a _, hP.line.symm, h2 ▸ hb', h1 ▸ hP.a_bd, pair_comm _ _⟩
  choose p q hpql hpb hqb hpq_ends using hpq
  let par : N → Option N := fun u => if h : wT u ∉ discBd B₀ then some ⟨wT u, hwT u, h⟩ else none
  let c₀ : Option N → Set T := fun n => n.elim B₁ fun u => R u.1
  have hRB₁ : ∀ u : N, Disjoint (R u.1) B₁ := fun u => disjoint_left.mpr fun x hx h => by
    rcases hB₁cases x h with h1 | ⟨v, hv, hvb, h1⟩
    · exact disjoint_left.mp (hRB₀ u.1 u.2.1 u.2.2) hx h1
    · exact disjoint_left.mp (hRd u.1 u.2.1 v hv fun e => u.2.2 (e ▸ hvb)) hx h1
  have hd' : ∀ n, IsClosedDisc (c₀ n) := fun n => by
    cases n with
    | none => exact hB₁
    | some u => exact (hR u.1 u.2.1).1.disc
  have hdj' : ∀ m n, m ≠ n → Disjoint (c₀ m) (c₀ n) := fun m n hmn => by
    cases m with
    | none =>
      cases n with
      | none => exact absurd rfl hmn
      | some u => exact (hRB₁ u).symm
    | some u =>
      cases n with
      | none => exact hRB₁ u
      | some v => exact hRd u.1 u.2.1 v.1 v.2.1 fun e => hmn (congrArg some (Subtype.ext e))
  have hρ' : ∀ u v, par u = some v → ρ v.1 < ρ u.1 := fun u v h => by
    dsimp only [par] at h
    by_cases h1 : wT u ∉ discBd B₀
    · rw [dite_eq_left h1] at h
      injection h with h
      subst h
      exact hrk u h1
    · rw [dite_eq_right h1] at h
      cases h
  have hq' : ∀ u, q u ∈ discBd (c₀ (par u)) := fun u => by
    have hqU : q u ∈ L (eT u) := (hpql u).right_mem
    dsimp only [par]
    by_cases h1 : wT u ∉ discBd B₀
    · rw [dite_eq_left h1]
      exact hqb u
    · rw [dite_eq_right h1]
      exact hbB₁ _ (hwT u) (not_not.mp h1) _ (hqb u)
        (hnoV _ (heT u) (hT1 u) _ hqU) (hLU _ (heT u) hqU)
  have hLc' : ∀ u n, L (eT u) ∩ c₀ n ⊆ {p u, q u} := fun u n x hx => by
    rw [hpq_ends u]
    cases n with
    | none => exact hLB₁ _ (heT u) x hx.1 hx.2
    | some v => exact (hL _ (heT u)).disc v.1 v.2.1 x hx.1 hx.2
  have hLL' : ∀ u v, u ≠ v → Disjoint (L (eT u)) (L (eT v)) := fun u v huv => by
    have hne : eT u ≠ eT v := fun he => by
      have hvu : u.1 ≠ v.1 := fun e => huv (Subtype.ext e)
      have h1 := hvert _ (heT u) _ (huc u) (hKV u.2.1)
      have h2 := hvert _ (heT u) _ (hwc u) (hKV (hwT u))
      have h3 := hvert _ (heT u) _ (he ▸ huc v) (hKV v.2.1)
      have h4 := hvert _ (heT u) _ (he ▸ hwc v) (hKV (hwT v))
      have hw1 : wT u = v.1 := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
        · exact absurd (h2.trans h1.symm) (hwne u)
        · exact absurd (h2.trans h1.symm) (hwne u)
        · exact absurd (h1.trans h3.symm) hvu
        · exact h2.trans h3.symm
        · exact h2.trans h3.symm
        · exact absurd (h1.trans h3.symm) hvu
        · exact absurd (h2.trans h1.symm) (hwne u)
        · exact absurd (h2.trans h1.symm) (hwne u)
      have hw2 : wT v = u.1 := by
        rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
        · exact absurd (h1.trans h3.symm) hvu
        · exact absurd (h1.trans h3.symm) hvu
        · exact h4.trans h1.symm
        · exact absurd (h4.trans h3.symm) (hwne v)
        · exact absurd (h4.trans h3.symm) (hwne v)
        · exact h4.trans h1.symm
        · exact absurd (h1.trans h3.symm) hvu
        · exact absurd (h1.trans h3.symm) hvu
      have h5 := hrk u (hw1 ▸ v.2.2)
      have h6 := hrk v (hw2 ▸ u.2.2)
      rw [hw1] at h5; rw [hw2] at h6
      omega
    refine disjoint_left.mpr fun x hx hy => ?_
    exact hnoV _ (heT u) (hT1 u) x hx (hmeetV _ (heT u) _ (heT v) hne x hx hy)
  have hfin : (𝓔 \ range eT).Finite := h𝓔.subset sdiff_subset
  set s := hfin.toFinset
  have hmem : ∀ {e}, e ∈ s → e ∈ 𝓔 ∧ ∀ u, eT u ≠ e := fun {e} h => by
    obtain ⟨h1, h2⟩ := hfin.mem_toFinset.mp h
    exact ⟨h1, fun u hu => h2 ⟨u, hu⟩⟩
  have hXfin : X.Finite := Γ.finite_V.subset hXV
  set Y : Set T := X ∪ (Γ.V \ K) ∪ (⋃ f ∈ Γ.E \ 𝓔, closure f) ∪ E₀
  have hYc : IsClosed Y := ((hXfin.isClosed.union (Γ.finite_V.subset sdiff_subset).isClosed).union
    ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun e _ => isClosed_closure)).union
    hE₀.isClosed
  have hclf : ∀ f ∈ Γ.E \ 𝓔, ∀ v ∈ K, v ∉ closure f := fun f hf v hv h => hf.2 ⟨hf.1, v, hv, h⟩
  have hYR : ∀ v ∈ K, ∀ x ∈ R v, x ∉ Y := fun v hv x hx => by
    rintro (((h | h) | h) | h)
    · exact hoffV v hv x (hXV h) (fun e => disjoint_left.mp hXK h (e ▸ hv)) hx
    · exact hoffV v hv x h.1 (fun e => h.2 (e ▸ hv)) hx
    · obtain ⟨f, hf, h1⟩ := mem_iUnion₂.mp h
      exact disjoint_left.mp (hcloff v hv f hf.1 (hclf f hf v hv)) hx h1
    · exact disjoint_left.mp (hRE v hv) hx h
  have hYL : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ Y → x ∈ Γ.V := fun e he x hx => by
    rintro (((h | h) | h) | h)
    · exact hXV h
    · exact h.1
    · obtain ⟨f, hf, h1⟩ := mem_iUnion₂.mp h
      by_contra hn
      have h2 := hclV f hf.1 x h1 hn
      rcases (hL e he).onEdge x hx with h3 | h3
      · have hef : e = f := by
          by_contra hne
          exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he.1 hf.1 hne) h3 h2
        exact hf.2 (hef ▸ he)
      · exact hn h3
    · exact hEU ⟨hLU e he hx, h⟩
  set X' : Set T := X ∪ (discBd B₀ ∩ E₀)
  have hX'U : X' ∩ Γ.U ⊆ X := by
    rintro x ⟨hx | hx, hxU⟩
    · exact hx
    · exact hinterU ⟨hx, hxU⟩
  have hint' : IsPreconnected (discInt E₀) := hE₀.isPreconnected_discInt
  have hYne : (discInt E₀).Nonempty := hE₀.nonempty_discInt
  have hX'Y₀ : Disjoint X' (discInt E₀) := by
    refine disjoint_left.mpr fun x hx h => ?_
    rcases hx with hx | hx
    · exact disjoint_left.mp hEint (Γ.V_subset_U (hXV hx)) h
    · exact disjoint_left.mp hd₁ (Surface.discBd_subset _ hx.1) h
  have hY₀Y : discInt E₀ ⊆ Y := fun x hx => .inr hx.1
  have hLY' : ∀ u, Disjoint (L (eT u)) Y := fun u => disjoint_left.mpr fun x hx h =>
    hnoV _ (heT u) (hT1 u) x hx (hYL _ (heT u) x hx h)
  have hLℓ : ∀ u, ∀ e ∈ s, Disjoint (L (eT u)) (L e) :=
    fun u e he => disjoint_left.mpr fun x hx h =>
      hnoV _ (heT u) (hT1 u) x hx (hmeetV _ (heT u) _ (hmem he).1 ((hmem he).2 u) x hx h)
  have hcY₀ : ∀ n, Disjoint (discInt E₀) (c₀ n) := fun n => by
    cases n with
    | none =>
      refine disjoint_left.mpr fun x hx h => ?_
      rcases hB₁cases x h with h1 | ⟨v, hv, -, h1⟩
      · exact disjoint_left.mp hd₁ h1 hx
      · exact disjoint_left.mp (hRE v hv) h1 hx.1
    | some u => exact ((hRE u.1 u.2.1).mono_right fun x hx => hx.1).symm
  have hbY : ∀ n, discBd (c₀ n) ∩ Y ⊆ X' := fun n => by
    cases n with
    | none =>
      rintro x ⟨hx, hy⟩
      rcases h1d hx with h | h
      · have hxB := h
        rcases hy with ((h1 | h1) | h1) | h1
        · exact Or.inl h1
        · rcases h1 with ⟨h2, h3⟩
          exact Or.inl ((hcuff ⟨h2, hxB⟩).resolve_left h3)
        · obtain ⟨f, hf, h2⟩ := mem_iUnion₂.mp h1
          have h3 := hbd ⟨hclU f hf.1 h2, hxB⟩
          rcases hcuff ⟨h3, hxB⟩ with h4 | h4
          · exact absurd h2 (hclf f hf x h4)
          · exact Or.inl h4
        · exact Or.inr ⟨hxB, h1⟩
      · obtain ⟨v, hv, h2⟩ := mem_iUnion₂.mp h
        exact absurd hy (hYR v (hmemK₀ hv).1 x (Surface.discBd_subset _ h2))
    | some u =>
      rintro x ⟨hx, hy⟩
      exact absurd hy (hYR u.1 u.2.1 x (Surface.discBd_subset _ hx))
  have hbon : ∀ v ∈ K, ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → ∃ n, x ∈ discBd (c₀ n) :=
    fun v hv x hx h2 h3 => by
      by_cases h1 : v ∈ discBd B₀
      · exact ⟨none, hbB₁ v hv h1 x hx h2 h3⟩
      · exact ⟨some ⟨v, hv, h1⟩, hx⟩
  have : Finite N := (hKfin.subset sdiff_subset).to_subtype
  obtain ⟨B, hB, hc, hLint, hY₀B, hbdY, hbdL⟩ :=
    GM07.exists_disc_of_tree hS hsph (c₀ := c₀) (L := fun u => L (eT u)) (p := p) (q := q)
      (par := par) (ρ := fun u => ρ u.1) hd' hdj' hρ' hpql hpb hq' hLc' hLL'
      s L a b (X := X') (Y := Y) (Y₀ := discInt E₀) hint' hYne hX'Y₀ hYc hY₀Y hLY' hLℓ hcY₀ hbY
      (fun e he => (hL e (hmem he).1).line) (fun e he => (hL e (hmem he).1).ne)
      (fun e he h => (hL e (hmem he).1).a_notV
        (hXV (hX'U ⟨h, hLU e (hmem he).1 (hL e (hmem he).1).line.left_mem⟩)))
      (fun e he => hbon _ (hγK e (hmem he).1) _ (hL e (hmem he).1).a_bd (hL e (hmem he).1).a_notV
        (hLU e (hmem he).1 (hL e (hmem he).1).line.left_mem))
      (fun e he => by
        have h𝓔e := (hmem he).1
        rcases (hL e h𝓔e).b_mem with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact .inl (hbon _ h1 _ h2 h3 (hLU e h𝓔e (hL e h𝓔e).line.right_mem))
        · have hbU := hLU e h𝓔e (hL e h𝓔e).line.right_mem
          have hbR : ∀ v ∈ K, b e ∉ R v := fun v hv h => hYR v hv _ h (.inl (.inl (.inl h2)))
          by_cases h3 : b e ∈ discBd B₀
          · refine .inl ⟨none, h1g ⟨h3, fun h => ?_⟩⟩
            obtain ⟨v, hv, h4⟩ := mem_iUnion₂.mp h
            exact hbR v (hmemK₀ hv).1 h4
          · refine .inr ⟨Or.inl h2, fun n h => ?_⟩
            cases n with
            | none =>
              rcases hB₁cases _ h with h4 | ⟨v, hv, -, h4⟩
              · exact h3 (hB₀V _ hbU h4).1
              · exact hbR v hv h4
            | some u => exact hbR u.1 u.2.1 h)
      (fun e he n x hx => by
        have h𝓔e := (hmem he).1
        cases n with
        | none => exact hLB₁ e h𝓔e x hx.1 hx.2
        | some v => exact (hL e h𝓔e).disc v.1 v.2.1 x hx.1 hx.2)
      (fun e he x hx => Or.inl ((hLVmem e (hmem he).1 x hx.1 (hYL e (hmem he).1 x hx.1 hx.2)).1 ▸
        (hLVmem e (hmem he).1 x hx.1 (hYL e (hmem he).1 x hx.1 hx.2)).2))
      (fun e he => disjoint_left.mpr fun x hx h =>
        hx.2 (.inr (hLVmem e (hmem he).1 x hx.1
          (hXV (hX'U ⟨h, hLU e (hmem he).1 hx.1⟩))).1))
      (fun e he f hf hef x hx => by
        have h2 := hmeetV e (hmem he).1 f (hmem hf).1 hef x hx.1 hx.2
        have h3 := hLVmem e (hmem he).1 x hx.1 h2
        exact Or.inl (h3.1 ▸ h3.2))
  have hRint : ∀ v ∈ K, discInt (R v) ⊆ discInt B := fun v hv x hx => by
    by_cases h1 : v ∈ discBd B₀
    · exact (hc none).2 (hintR v hv h1 hx)
    · exact (hc (some ⟨v, hv, h1⟩)).2 hx
  refine ⟨B, hB, h1a.trans (hc none).1, hY₀B, ?_⟩
  rintro x ⟨hx, hU⟩
  refine hX'U ⟨?_, hU⟩
  have hnotint : x ∉ discInt B := fun h => h.2 hx
  by_cases hV : x ∈ Γ.V
  · by_cases hK : x ∈ K
    · exact absurd (hRint x hK (hR x hK).1.mem) hnotint
    · exact hbdY ⟨hx, .inl (.inl (.inr ⟨hV, hK⟩))⟩
  obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hU hV
  by_cases h𝓔e : e ∈ 𝓔
  · by_cases hxL : x ∈ L e
    · by_cases hmemT : e ∈ range eT
      · obtain ⟨u, rfl⟩ := hmemT
        exact absurd (hLint u hxL) hnotint
      · exact hbdL e (hfin.mem_toFinset.mpr ⟨h𝓔e, hmemT⟩) ⟨hx, hxL⟩
    · obtain ⟨w, hw, h1⟩ := (hL e h𝓔e).rest x hxe hxL
      exact absurd (hRint w hw h1) hnotint
  · exact hbdY ⟨hx, .inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, h𝓔e⟩, subset_closure hxe⟩))⟩

private theorem pull_walk_matched {S : Type w} [TopologicalSpace S]
    {T : Type} [TopologicalSpace T] {G : Drawing S} {Γ : Drawing T} {j : S → T}
    (hj : IsClosedEmbedding j) (hm : GM07.IsMatched G Γ j ∅) :
    ∀ {uZ vZ : T} (wZ : Γ.toHypergraph.skeleton.Walk uZ vZ) {u v : S},
      j u = uZ → j v = vZ →
      ∃ w : G.toHypergraph.skeleton.Walk u v, wZ.support = w.support.map j := by
  have hVZ : Γ.V = j '' G.V := by simpa using hm.image_V.symm
  have hcl : ∀ e : Set S, closure (j '' e) = j '' closure e := fun e =>
    (image_closure_subset_closure_image hj.continuous).antisymm'
      (closure_minimal (image_mono subset_closure) (hj.isClosedMap _ isClosed_closure))
  intro uZ vZ wZ
  induction wZ with
  | nil =>
    intro u v hu hv
    obtain rfl : u = v := hj.injective (hu.trans hv.symm)
    exact ⟨SimpleGraph.Walk.nil, by simp [hu]⟩
  | @cons aZ bZ cZ hadj rest ih =>
    intro u v hu hv
    obtain ⟨hneZ, eZ, ⟨heZ, haVZ, haclZ⟩, ⟨_, hbVZ, hbclZ⟩⟩ := id hadj
    obtain ⟨b, hbV, rfl⟩ := hVZ ▸ hbVZ
    obtain ⟨e, he, rfl⟩ := hm.image_E ▸ heZ
    have huV : u ∈ G.V := by
      obtain ⟨u', hu'V, heq⟩ := hVZ ▸ haVZ
      exact hj.injective (heq.trans hu.symm) ▸ hu'V
    have hucl : u ∈ closure e := by
      rw [← hu, hcl] at haclZ
      obtain ⟨u', hu'cl, heq⟩ := haclZ
      exact hj.injective heq ▸ hu'cl
    have hbcl : b ∈ closure e := by
      rw [hcl] at hbclZ
      obtain ⟨b', hb'cl, heq⟩ := hbclZ
      exact hj.injective heq ▸ hb'cl
    have hadjG : G.toHypergraph.skeleton.Adj u b :=
      ⟨fun h => hneZ (hu ▸ h ▸ rfl), e, ⟨he, huV, hucl⟩, ⟨he, hbV, hbcl⟩⟩
    obtain ⟨w', hw'⟩ := ih rfl hv
    exact ⟨SimpleGraph.Walk.cons hadjG w', by simp [hu, hw']⟩

private theorem exists_tube_oriented {S : Type w} [TopologicalSpace S]
    (τ : Tube S) (cap : CylinderSphereCap S) :
    ∃ σ : Tube S, σ.Γ = τ.Γ ∧ cylinderBetween σ.F₁ σ.F₂ = cylinderBetween τ.F₁ τ.F₂ ∧
      σ.width = τ.width ∧ (∀ F, σ.IsCutTrivial F ↔ τ.IsCutTrivial F) ∧
      cap.disc₁ τ.isCylinder.1 σ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 σ.isHoop_F₂ := by
  rcases (cap.areLaminarHoops_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂).mp τ.laminar with h | h
  · exact ⟨τ, rfl, rfl, rfl, fun _ => Iff.rfl, h⟩
  · exact ⟨τ.symm, rfl, cylinderBetween_comm _ _, τ.width_symm, fun _ => τ.isCutTrivial_symm, h⟩

/-- **Menger across laminar normal hoops in a cylinder from a hoop-cut lower bound.**
If `H₁, H₂` are `τ.Γ`-normal laminar hoops in `S` and every `τ.Γ`-normal hoop
`H ⊆ cylinderBetween H₁ H₂` meets `τ.Γ.V` in at least `r` vertices, then the subdrawing in
`cylinderBetween H₁ H₂` contains `r` mutually vertex-disjoint skeleton paths from `H₁` to `H₂`. -/
theorem Tube.hasDisjointPaths_subTube_of_forall_hoop_ncard_ge {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r : ℕ}
    {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween H₁ H₂ →
      r ≤ (τ.Γ.V ∩ H).ncard) :
    HasDisjointPaths (τ.subTube hlam hN₁ hN₂).Γ.toHypergraph.skeleton
      ((τ.subTube hlam hN₁ hN₂).Γ.V ∩ H₁) ((τ.subTube hlam hN₁ hN₂).Γ.V ∩ H₂) r := by
  have : T2Space S := τ.t2Space
  have : CompactSpace S := τ.isCylinder.1.1
  have : Nonempty S := τ.isCylinder.nonempty
  let Γ' : Drawing S := (τ.subTube hlam hN₁ hN₂).Γ
  change HasDisjointPaths Γ'.toHypergraph.skeleton (Γ'.V ∩ H₁) (Γ'.V ∩ H₂) r
  obtain ⟨_, hH₁, hH₂, -⟩ := id hlam
  obtain ⟨cap, hle12⟩ := CylinderSphereCap.exists_oriented τ.isCylinder hH₁ hH₂ hlam
  have : T2Space cap.Z := cap.t2Space_Z
  set E₁ := cap.disc₁ τ.isCylinder.1 hH₁
  set E₂ := cap.disc₂ τ.isCylinder.1 hH₁
  set G₁ := cap.disc₁ τ.isCylinder.1 hH₂
  set G₂ := cap.disc₂ τ.isCylinder.1 hH₂
  obtain ⟨hE₁, hE₂, hbE₁, hbE₂, hcupE, hcapE, hD₁E, _⟩ :=
    cap.disc₁_disc₂_spec τ.isCylinder.1 hH₁
  obtain ⟨hG₁, hG₂, hbG₁, hbG₂, hcupG, hcapG, _, hD₂G⟩ :=
    cap.disc₁_disc₂_spec τ.isCylinder.1 hH₂
  have hcl_cyl : IsClosed (cylinderBetween H₁ H₂) := isClosed_cylinderBetween hlam
  have hΓ'_V : Γ'.V = τ.Γ.V ∩ cylinderBetween H₁ H₂ := interSet_V_of_isClosed τ.Γ hcl_cyl
  have hΓ'_U : Γ'.U = τ.Γ.U ∩ cylinderBetween H₁ H₂ :=
    interSet_U_eq_of_laminar_normal τ.Γ hlam hN₁ hN₂
  have hΓ'_N₁ : Γ'.IsNormal H₁ := (τ.subTube hlam hN₁ hN₂).isNormal_F₁
  have hΓ'_N₂ : Γ'.IsNormal H₂ := (τ.subTube hlam hN₁ hN₂).isNormal_F₂
  obtain ⟨Γ'Z, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding Γ'
  have hUZ : Γ'Z.U = cap.j '' Γ'.U := by simpa using hm.image_U.symm
  have hVZ : Γ'Z.V = cap.j '' Γ'.V := by simpa using hm.image_V.symm
  have hUZ_sub : Γ'Z.U ⊆ G₁ ∩ E₂ := by
    rw [hUZ, hΓ'_U]
    rintro _ ⟨x, ⟨_, hxB⟩, rfl⟩
    rwa [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder hH₁ hH₂ hle12] at hxB
  set Z₁ := Γ'Z.V ∩ E₁
  set Z₂ := Γ'Z.V ∩ G₂
  have hZ₁_eq : Z₁ = cap.j '' (Γ'.V ∩ H₁) := by
    apply Subset.antisymm
    · rintro z ⟨hzV, hxE₁⟩
      rw [hVZ] at hzV
      obtain ⟨x, hxV, rfl⟩ := hzV
      have hxE₂ : cap.j x ∈ E₂ := (hUZ_sub (hUZ ▸ mem_image_of_mem _ (Γ'.V_subset_U hxV))).2
      have hx_inter : cap.j x ∈ cap.j '' H₁ := hcapE ▸ (⟨hxE₁, hxE₂⟩ : cap.j x ∈ E₁ ∩ E₂)
      obtain ⟨y, hyH₁, heq⟩ := hx_inter
      exact ⟨x, ⟨hxV, cap.inj heq ▸ hyH₁⟩, rfl⟩
    · rintro _ ⟨x, ⟨hxV, hxH₁⟩, rfl⟩
      exact ⟨hVZ ▸ mem_image_of_mem _ hxV,
        Surface.discBd_subset _ (hbE₁ ▸ mem_image_of_mem _ hxH₁)⟩
  have hZ₂_eq : Z₂ = cap.j '' (Γ'.V ∩ H₂) := by
    apply Subset.antisymm
    · rintro z ⟨hzV, hxG₂⟩
      rw [hVZ] at hzV
      obtain ⟨x, hxV, rfl⟩ := hzV
      have hxG₁ : cap.j x ∈ G₁ := (hUZ_sub (hUZ ▸ mem_image_of_mem _ (Γ'.V_subset_U hxV))).1
      have hx_inter : cap.j x ∈ cap.j '' H₂ := hcapG ▸ (⟨hxG₁, hxG₂⟩ : cap.j x ∈ G₁ ∩ G₂)
      obtain ⟨y, hyH₂, heq⟩ := hx_inter
      exact ⟨x, ⟨hxV, cap.inj heq ▸ hyH₂⟩, rfl⟩
    · rintro _ ⟨x, ⟨hxV, hxH₂⟩, rfl⟩
      exact ⟨hVZ ▸ mem_image_of_mem _ hxV,
        Surface.discBd_subset _ (hbG₂ ▸ mem_image_of_mem _ hxH₂)⟩
  by_cases hpZ : HasDisjointPaths Γ'Z.toHypergraph.skeleton Z₁ Z₂ r
  · obtain ⟨QZ, hQZ⟩ := hpZ
    have hex : ∀ i : Fin r, ∃ P : PathFromTo Γ'.toHypergraph.skeleton (Γ'.V ∩ H₁) (Γ'.V ∩ H₂),
        (QZ i).walk.support = P.walk.support.map cap.j := fun i => by
      have hfm : (QZ i).first ∈ cap.j '' (Γ'.V ∩ H₁) := hZ₁_eq ▸ (QZ i).first_mem
      have hlm : (QZ i).last ∈ cap.j '' (Γ'.V ∩ H₂) := hZ₂_eq ▸ (QZ i).last_mem
      obtain ⟨u, hu, hu_eq⟩ := hfm
      obtain ⟨v, hv, hv_eq⟩ := hlm
      obtain ⟨w, hw_supp⟩ := pull_walk_matched cap.isClosedEmbedding hm (QZ i).walk hu_eq hv_eq
      have hw_path : w.IsPath := by
        rw [SimpleGraph.Walk.isPath_def]
        have hndZ : (QZ i).walk.support.Nodup := (QZ i).isPath.support_nodup
        rw [hw_supp] at hndZ
        exact List.Nodup.of_map _ hndZ
      exact ⟨⟨u, v, w, hw_path, hu, hv⟩, hw_supp⟩
    choose P hP_supp using hex
    refine ⟨P, fun i j hij => disjoint_left.mpr fun x hxi hxj => ?_⟩
    exact disjoint_left.mp (hQZ hij)
      ((hP_supp i).symm ▸ List.mem_map_of_mem (f := cap.j) hxi)
      ((hP_supp j).symm ▸ List.mem_map_of_mem (f := cap.j) hxj)
  · exfalso
    obtain ⟨X₀, hsep, hlt⟩ := Thomas.exists_separates_lt_of_not_hasDisjointPaths
      Γ'Z.toHypergraph inter_subset_left inter_subset_left hpZ
    set K₀ := Γ'Z.toHypergraph.skeleton
    set K := Thomas.sepCompLeft K₀ Γ'Z.V X₀ Z₁
    have hX₀V : X₀ ⊆ Γ'Z.V := hsep.1
    let P_rk : cap.Z → ℕ → Prop := fun u n =>
      ∃ z ∈ Z₁ \ X₀, ∃ p : K₀.Walk z u, (∀ w ∈ p.support, w ∈ Γ'Z.V \ X₀) ∧ p.length = n
    have hne : ∀ u ∈ K, ∃ n, P_rk u n := fun u ⟨_, z, hz, p, hp⟩ => ⟨_, z, hz, p, hp, rfl⟩
    let ρ : cap.Z → ℕ := fun u => sInf {n | P_rk u n}
    have hρ : ∀ u ∈ K, P_rk u (ρ u) := fun u hu => Nat.sInf_mem (hne u hu)
    have hKsub : K ⊆ Γ'Z.V \ X₀ := Thomas.sepCompLeft_subset_sdiff _ _ _ _
    have hedge : ∀ e ∈ Γ'Z.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ Γ'Z.V, w ∈ closure e → w ∈ K ∪ X₀ :=
      fun e he u hu hue w hw hwe => by
        by_cases huw : u = w
        · exact .inl (huw ▸ hu)
        by_contra hn
        have hw' : w ∈ Thomas.sepCompRight K₀ Γ'Z.V X₀ Z₁ :=
          ⟨⟨hw, fun h => hn (.inr h)⟩, fun h => hn (.inl h)⟩
        exact Thomas.not_adj_sepCompLeft_sepCompRight hu hw'
          ⟨huw, e, ⟨he, (hKsub hu).1, hue⟩, ⟨he, hw, hwe⟩⟩
    have hi₁ : Disjoint Γ'Z.U (discInt E₁) :=
      disjoint_left.mpr fun z hzU hzInt => hzInt.2 (hbE₁ ▸ hcapE ▸ ⟨hzInt.1, (hUZ_sub hzU).2⟩)
    have hi₂ : Disjoint Γ'Z.U (discInt G₂) :=
      disjoint_left.mpr fun z hzU hzInt => hzInt.2 (hbG₂ ▸ hcapG ▸ ⟨(hUZ_sub hzU).1, hzInt.1⟩)
    have hbdE₁ : Γ'Z.U ∩ discBd E₁ ⊆ Γ'Z.V := by
      rw [hUZ, hVZ, hbE₁]
      rintro _ ⟨⟨x, hxU, rfl⟩, ⟨y, hyH₁, heq⟩⟩
      exact ⟨x, hΓ'_N₁ ⟨cap.inj heq ▸ hyH₁, hxU⟩, rfl⟩
    have hUG₂ : Γ'Z.U ∩ G₂ ⊆ Γ'Z.V := by
      rintro z ⟨hzU, hzG₂⟩
      have hzH₂ : z ∈ cap.j '' H₂ := hcapG ▸ ⟨(hUZ_sub hzU).1, hzG₂⟩
      obtain ⟨x, hxU, rfl⟩ := hUZ ▸ hzU
      obtain ⟨y, hyH₂, heq⟩ := hzH₂
      exact hVZ ▸ ⟨x, hΓ'_N₂ ⟨cap.inj heq ▸ hyH₂, hxU⟩, rfl⟩
    have hd₁ : Disjoint E₁ (discInt G₂) :=
      disjoint_left.mpr fun z hzE₁ hzInt => hzInt.2 (hbG₂ ▸ hcapG ▸ ⟨hle12 hzE₁, hzInt.1⟩)
    have hinterU : (discBd E₁ ∩ G₂) ∩ Γ'Z.U ⊆ X₀ := by
      rintro z ⟨⟨hzBd, hzG₂⟩, hzU⟩
      have hzV : z ∈ Γ'Z.V := hbdE₁ ⟨hzU, hzBd⟩
      have hz₁ : z ∈ Z₁ := ⟨hzV, Surface.discBd_subset _ hzBd⟩
      have hz₂ : z ∈ Z₂ := ⟨hzV, hzG₂⟩
      obtain ⟨w, hw_supp, hwX⟩ := hsep.2 hz₁ hz₂ SimpleGraph.Walk.nil (fun w hw => by
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
        exact hw ▸ hzV)
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw_supp
      exact hw_supp ▸ hwX
    have hZbd : ∀ {z}, z ∈ Z₁ → z ∈ discBd E₁ := fun {z} hz => by
      by_contra hn
      exact disjoint_left.mp hi₁ (Γ'Z.V_subset_U hz.1) ⟨hz.2, hn⟩
    have hreach : ∀ u ∈ K, u ∉ discBd E₁ → ∃ e ∈ Γ'Z.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧
        w ∈ closure e ∧ (w ∉ discBd E₁ → ρ w < ρ u) := fun u hu hub => by
      obtain ⟨z, hz, p, hp, hl⟩ := hρ u hu
      have huz : u ≠ z := fun h => hub (h ▸ hZbd hz.1)
      obtain ⟨w, hadj, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huz p.reverse
      obtain ⟨huw, e, h1, h2⟩ := id hadj
      have hsup : ∀ y ∈ q.support, y ∈ Γ'Z.V \ X₀ := fun y hy => hp y (by
        have : y ∈ p.reverse.support := by
          rw [hq]; exact List.mem_cons_of_mem _ hy
        rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this)
      have hsup' : ∀ y ∈ q.reverse.support, y ∈ Γ'Z.V \ X₀ :=
        fun y hy => hsup y (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy)
      have hw' : w ∈ K := ⟨hsup w q.start_mem_support, z, hz, q.reverse, hsup'⟩
      refine ⟨e, h1.1, w, hw', huw.symm, h1.2.2, h2.2.2, fun _ => ?_⟩
      have hle_rk : ρ w ≤ q.reverse.length := Nat.sInf_le ⟨z, hz, q.reverse, hsup', rfl⟩
      have hlen : q.length + 1 = p.length := by
        have h3 : p.reverse.length = q.length + 1 := by rw [hq]; rfl
        rw [SimpleGraph.Walk.length_reverse] at h3
        exact h3.symm
      rw [SimpleGraph.Walk.length_reverse] at hle_rk
      omega
    have hc : Γ'Z.V ∩ discBd E₁ ⊆ K ∪ X₀ := fun x hx => by
      by_cases hxX : x ∈ X₀
      · exact .inr hxX
      · have hz : x ∈ Z₁ := ⟨hx.1, Surface.discBd_subset _ hx.2⟩
        exact .inl ⟨⟨hx.1, hxX⟩, x, ⟨hz, hxX⟩, SimpleGraph.Walk.nil, fun w hw => by
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          exact hw ▸ ⟨hx.1, hxX⟩⟩
    have hke : Disjoint K G₂ := disjoint_left.mpr fun u hu hu₂ => by
      obtain ⟨hV, z, hz, p, hp⟩ := hu
      obtain ⟨x, hx, hxX⟩ := hsep.2 hz.1 (⟨hV.1, hu₂⟩ : u ∈ Z₂) p (fun w hw => (hp w hw).1)
      exact (hp x hx).2 hxX
    obtain ⟨B, hB, hsubB, hdisB, hbdB⟩ := exists_disc_of_side_touching (K := K) (X := X₀) (ρ := ρ)
      cap.isClosedSurface cap.isSphere Γ'Z hE₁ hG₂ hd₁ hinterU hbdE₁ hi₁ hUG₂ hi₂
      (fun x hx => (hKsub hx).1) hX₀V (Thomas.disjoint_sepCompLeft_sep _ _ _ _).symm
      hc hke hedge hreach
    have hD₁B : cap.D₁ ⊆ B := hD₁E.trans hsubB
    have hdis_bd_D₁ : Disjoint (discBd B) (discInt cap.D₁) := by
      refine disjoint_left.mpr fun z hzBd hzInt => ?_
      exact (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₁ hD₁B hzInt).2 hzBd
    have hdis_D₂_B : Disjoint (discInt cap.D₂) B :=
      hdisB.mono_left (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₂ hD₂G)
    have hsubr : discBd B ⊆ range cap.j :=
      cap.subset_range_of_disjoint_discInts hdis_bd_D₁
        (hdis_D₂_B.symm.mono_left (Surface.discBd_subset B))
    let H : Set S := cap.j ⁻¹' discBd B
    have hjH : cap.j '' H = discBd B := image_preimage_eq_of_subset hsubr
    have hHO : IsOArc H := GM07.pull_oArc cap.isClosedEmbedding.isEmbedding hB.isOArc_discBd hsubr
    obtain ⟨Δ₁, Δ₂, hΔ_ne, hΔ₁, hΔ₂, hbΔ₁, hbΔ₂, hcupΔ, hcapΔ, -, huniqΔ⟩ :=
      sphere_disc cap.Z cap.isSphere (discBd B) hB.isOArc_discBd
    have hB'_ex : ∃ B' : Set cap.Z, IsClosedDisc B' ∧ discBd B' = cap.j '' H ∧
        B ∪ B' = univ ∧ B ∩ B' = cap.j '' H := by
      rcases huniqΔ B hB rfl with hB1 | hB2
      · subst hB1
        exact ⟨Δ₂, hΔ₂, hbΔ₂.trans hjH.symm, hcupΔ, hcapΔ.trans hjH.symm⟩
      · subst hB2
        exact ⟨Δ₁, hΔ₁, hbΔ₁.trans hjH.symm, by rw [union_comm, hcupΔ],
          by rw [inter_comm, hcapΔ, hjH]⟩
    obtain ⟨B', hB'_disc, hbB', hcupBB', hcapBB'⟩ := hB'_ex
    have hD₂B' : cap.D₂ ⊆ B' := by
      have hint_sub : discInt cap.D₂ ⊆ B' := fun z hz =>
        (hcupBB' ▸ mem_univ z).resolve_left (disjoint_left.mp hdis_D₂_B hz)
      exact cap.isClosedDisc_D₂.subset_closure_discInt.trans
        (closure_minimal hint_sub hB'_disc.isCompact.isClosed)
    have hH : IsHoop H := (cap.isHoop_iff_exists_discs τ.isCylinder.1 hHO).mpr
      ⟨B, B', hB, hB'_disc, hjH.symm, hbB', hcupBB', hcapBB', hD₁B, hD₂B'⟩
    have hB_eq_disc₁ : B = cap.disc₁ τ.isCylinder.1 hH := by
      obtain ⟨hd1, hd2, hbd1, hbd2, _, hcap12, hD1', hD2'⟩ :=
        cap.disc₁_disc₂_spec τ.isCylinder.1 hH
      exact (cap.hoop_discs_unique hd1 hd2 hbd1 hbd2 hcap12 hD1' hD2'
        hB hB'_disc hjH.symm hbB' hD₁B hD₂B').1
    have hBG₁ : B ⊆ G₁ := fun z hzB => by
      rcases (hcupG ▸ mem_univ z : z ∈ G₁ ∪ G₂) with hz1 | hz2
      · exact hz1
      · by_cases hzBd : z ∈ discBd G₂
        · exact Surface.discBd_subset _ (hbG₁ ▸ hbG₂ ▸ hzBd)
        · exact absurd hzB (disjoint_left.mp hdisB ⟨hz2, hzBd⟩)
    have hle_H1_H : cap.disc₁ τ.isCylinder.1 hH₁ ⊆ cap.disc₁ τ.isCylinder.1 hH :=
      hB_eq_disc₁ ▸ hsubB
    have hle_H_H2 : cap.disc₁ τ.isCylinder.1 hH ⊆ cap.disc₁ τ.isCylinder.1 hH₂ :=
      hB_eq_disc₁ ▸ hBG₁
    have hH_sub12 : H ⊆ cylinderBetween H₁ H₂ :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hH₁ hH₂ hH hle12).mpr ⟨hle_H1_H, hle_H_H2⟩
    have hNH : τ.Γ.IsNormal H := by
      rintro x ⟨hxH, hxU⟩
      have hxj : cap.j x ∈ discBd B ∩ Γ'Z.U :=
        ⟨hxH, hUZ ▸ mem_image_of_mem _ (hΓ'_U ▸ ⟨hxU, hH_sub12 hxH⟩)⟩
      obtain ⟨y, hyV, heq⟩ := hVZ ▸ hX₀V (hbdB hxj)
      exact (hΓ'_V ▸ cap.inj heq ▸ hyV).1
    have hjHV_sub : cap.j '' (τ.Γ.V ∩ H) ⊆ X₀ := by
      rintro _ ⟨x, ⟨hxV, hxH⟩, rfl⟩
      exact hbdB ⟨hxH, hUZ ▸ mem_image_of_mem _ (hΓ'_U ▸ ⟨τ.Γ.V_subset_U hxV, hH_sub12 hxH⟩)⟩
    have hH_lt : (τ.Γ.V ∩ H).ncard < r := by
      have h1 : (τ.Γ.V ∩ H).ncard = (cap.j '' (τ.Γ.V ∩ H)).ncard :=
        (ncard_image_of_injective _ cap.inj).symm
      have h2 : (cap.j '' (τ.Γ.V ∩ H)).ncard ≤ X₀.ncard :=
        ncard_le_ncard hjHV_sub (Γ'Z.finite_V.subset hX₀V)
      omega
    have hge := hmin H hH hNH hH_sub12
    omega

/-- Consequence of `Tube.hasDisjointPaths_subTube_of_forall_hoop_ncard_ge` on the full skeleton
`τ.Γ.toHypergraph.skeleton`. -/
theorem Tube.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r : ℕ}
    {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween H₁ H₂ →
      r ≤ (τ.Γ.V ∩ H).ncard) :
    HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ H₁) (τ.Γ.V ∩ H₂) r := by
  have : T2Space S := τ.t2Space
  obtain ⟨Q, hQ⟩ := τ.hasDisjointPaths_subTube_of_forall_hoop_ncard_ge hlam hN₁ hN₂ hmin
  let Γ' : Drawing S := (τ.subTube hlam hN₁ hN₂).Γ
  have hcl : IsClosed (cylinderBetween H₁ H₂) := isClosed_cylinderBetween hlam
  have hVEq : Γ'.V = τ.Γ.V ∩ cylinderBetween H₁ H₂ := interSet_V_of_isClosed τ.Γ hcl
  have hEEq : Γ'.E = {ed ∈ τ.Γ.E | ed ⊆ cylinderBetween H₁ H₂} :=
    interSet_E τ.Γ (cylinderBetween H₁ H₂)
  have hle : Γ'.toHypergraph.skeleton ≤ τ.Γ.toHypergraph.skeleton := by
    intro x y hadj
    obtain ⟨hne, ed, ⟨hed, hxV, hxcl⟩, ⟨_, hyV, hycl⟩⟩ := id hadj
    have hed' : ed ∈ τ.Γ.E := (hEEq ▸ hed).1
    exact ⟨hne, ed, ⟨hed', (hVEq ▸ hxV).1, hxcl⟩, ⟨hed', (hVEq ▸ hyV).1, hycl⟩⟩
  have hsupp_mapLe : ∀ {u v : S} (w : Γ'.toHypergraph.skeleton.Walk u v),
      (w.mapLe hle).support = w.support := by
    intro u v w
    induction w with
    | nil => rfl
    | cons _ _ ih => simp [SimpleGraph.Walk.mapLe, ih]
  refine ⟨fun i =>
    { first := (Q i).first
      last := (Q i).last
      walk := (Q i).walk.mapLe hle
      isPath := by
        rw [SimpleGraph.Walk.isPath_def, hsupp_mapLe]
        exact (Q i).isPath.support_nodup
      first_mem := ⟨(hVEq.subset (Q i).first_mem.1).1, (Q i).first_mem.2⟩
      last_mem := ⟨(hVEq.subset (Q i).last_mem.1).1, (Q i).last_mem.2⟩ },
    fun i j hij => ?_⟩
  dsimp only
  rw [hsupp_mapLe, hsupp_mapLe]
  exact hQ hij

private theorem hasDisjointPaths_skeleton_of_laminar_hoops {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r : ℕ} (hw : (r : ℕ∞) ≤ τ.width)
    {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hsub₁ : H₁ ⊆ cylinderBetween τ.F₁ τ.F₂) (hsub₂ : H₂ ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hnt₁ : ¬ τ.IsCutTrivial H₁) (hnt₂ : ¬ τ.IsCutTrivial H₂) :
    HasDisjointPaths (τ.subTube hlam hN₁ hN₂).Γ.toHypergraph.skeleton
      ((τ.subTube hlam hN₁ hN₂).Γ.V ∩ H₁) ((τ.subTube hlam hN₁ hN₂).Γ.V ∩ H₂) r := by
  refine τ.hasDisjointPaths_subTube_of_forall_hoop_ncard_ge hlam hN₁ hN₂ fun H hH hNH hH_sub12 => ?_
  obtain ⟨_, hH₁, hH₂, -⟩ := id hlam
  obtain ⟨cap, hle12⟩ := CylinderSphereCap.exists_oriented τ.isCylinder hH₁ hH₂ hlam
  obtain ⟨σ, hσ_Γ, hσ_cyl, hσ_w_eq, hσ_ct, hleF⟩ := exists_tube_oriented τ cap
  have hσ_width : (r : ℕ∞) ≤ σ.width := hσ_w_eq ▸ hw
  obtain ⟨hle_F1_H1, _⟩ := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    σ.isHoop_F₁ σ.isHoop_F₂ hH₁ hleF).mp (hσ_cyl.symm ▸ hsub₁)
  obtain ⟨_, hle_H2_F2⟩ := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    σ.isHoop_F₁ σ.isHoop_F₂ hH₂ hleF).mp (hσ_cyl.symm ▸ hsub₂)
  obtain ⟨hle_H1_H, hle_H_H2⟩ :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hH₁ hH₂ hH hle12).mp hH_sub12
  have hle_F1_H := hle_F1_H1.trans hle_H1_H
  have hle_H_F2 := hle_H_H2.trans hle_H2_F2
  have hH_subF : H ⊆ cylinderBetween σ.F₁ σ.F₂ :=
    (cap.hoop_subset_cylinderBetween_iff τ.isCylinder σ.isHoop_F₁ σ.isHoop_F₂ hH hleF).mpr
      ⟨hle_F1_H, hle_H_F2⟩
  have hr_H₁ : r ≤ (H₁ ∩ σ.Γ.V).ncard := by
    have hor := (σ.le_width_iff.mp hσ_width) H₁ hH₁ (hσ_Γ ▸ hN₁) (hσ_cyl.symm ▸ hsub₁)
    exact Nat.cast_le (α := ℕ∞).mp (hor.resolve_left ((hσ_ct H₁).not.mpr hnt₁))
  have hr_H₂ : r ≤ (H₂ ∩ σ.Γ.V).ncard := by
    have hor := (σ.le_width_iff.mp hσ_width) H₂ hH₂ (hσ_Γ ▸ hN₂) (hσ_cyl.symm ▸ hsub₂)
    exact Nat.cast_le (α := ℕ∞).mp (hor.resolve_left ((hσ_ct H₂).not.mpr hnt₂))
  have hcomm : (H ∩ σ.Γ.V).ncard = (τ.Γ.V ∩ H).ncard := by rw [hσ_Γ, inter_comm]
  rcases (σ.le_width_iff.mp hσ_width) H hH (hσ_Γ ▸ hNH) hH_subF with hct | hge
  · rcases hct with ⟨hU_right, _⟩ | ⟨hU_left, _⟩
    · have hH₁_sub_FH : H₁ ⊆ cylinderBetween σ.F₁ H :=
        (cap.hoop_subset_cylinderBetween_iff τ.isCylinder σ.isHoop_F₁ hH hH₁ hle_F1_H).mpr
          ⟨hle_F1_H1, hle_H1_H⟩
      have hsubV : H₁ ∩ σ.Γ.V ⊆ H ∩ σ.Γ.V := fun x ⟨hx1, hxV⟩ =>
        ⟨cap.cylinderBetween_inter τ.isCylinder σ.isHoop_F₁ hH σ.isHoop_F₂ hle_F1_H hle_H_F2 ▸
          ⟨hH₁_sub_FH hx1, hU_right (σ.Γ.V_subset_U hxV)⟩, hxV⟩
      have hleV := ncard_le_ncard hsubV (σ.Γ.finite_V.subset inter_subset_right)
      omega
    · have hH₂_sub_HF : H₂ ⊆ cylinderBetween H σ.F₂ :=
        (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hH σ.isHoop_F₂ hH₂ hle_H_F2).mpr
          ⟨hle_H_H2, hle_H2_F2⟩
      have hsubV : H₂ ∩ σ.Γ.V ⊆ H ∩ σ.Γ.V := fun x ⟨hx2, hxV⟩ =>
        ⟨cap.cylinderBetween_inter τ.isCylinder σ.isHoop_F₁ hH σ.isHoop_F₂ hle_F1_H hle_H_F2 ▸
          ⟨hU_left (σ.Γ.V_subset_U hxV), hH₂_sub_HF hx2⟩, hxV⟩
      have hleV := ncard_le_ncard hsubV (σ.Γ.finite_V.subset inter_subset_right)
      omega
  · have := Nat.cast_le (α := ℕ∞).mp hge
    omega

end TouchingMenger

/-! ## 4. Lifting Skeleton Paths to `GraphPathIn` and `HasDisjointGraphPathsFromTo` -/

section LiftSkeletonPaths

private theorem walk_support_nonempty {V : Type*} {K : SimpleGraph V} {u v : V}
    (w : K.Walk u v) : 1 ≤ w.support.length := by
  cases w <;> simp

private theorem walk_support_head {V : Type*} {K : SimpleGraph V} {u v : V}
    (w : K.Walk u v) : w.support[0]'(walk_support_nonempty w) = u := by
  cases w <;> rfl

private theorem walk_support_last {V : Type*} {K : SimpleGraph V} {u v : V}
    (w : K.Walk u v) :
    w.support[w.support.length - 1]'(Nat.sub_lt (walk_support_nonempty w) Nat.one_pos) = v := by
  induction w with
  | nil => rfl
  | @cons a b c _ rest ih =>
    have hlen : 1 ≤ rest.support.length := walk_support_nonempty rest
    simp only [SimpleGraph.Walk.support_cons]
    have : (a :: rest.support)[(a :: rest.support).length - 1]'(by simp) =
        rest.support[rest.support.length - 1]'(by omega) := by
      rcases rest with _ | _ <;> rfl
    exact this.trans ih

private theorem walk_support_mem_V_and_adj {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) {u v : S} (hu : u ∈ Γ.V)
    (w : Γ.toHypergraph.skeleton.Walk u v) :
    (∀ z ∈ w.support, z ∈ Γ.V) ∧
      ∀ (s : ℕ) (hs : s + 1 < w.support.length),
        Γ.toHypergraph.skeleton.Adj (w.support[s]'(by omega)) (w.support[s + 1]'hs) := by
  induction w with
  | nil =>
    refine ⟨fun z hz => ?_, fun s hs => by simp at hs⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ hu
  | @cons a b c hadj rest ih =>
    obtain ⟨_, _, _, _, hbV, _⟩ := id hadj
    obtain ⟨hV_rest, hadj_rest⟩ := ih hbV
    refine ⟨fun z hz => ?_, fun s hs => ?_⟩
    · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      exact hz.elim (fun h => h ▸ hu) (hV_rest z)
    · cases s with
      | zero =>
        simp only [SimpleGraph.Walk.support_cons, List.getElem_cons_zero, List.getElem_cons_succ]
        rw [walk_support_head rest]
        exact hadj
      | succ s' =>
        simp only [SimpleGraph.Walk.support_cons, List.length_cons] at hs
        simp only [SimpleGraph.Walk.support_cons, List.getElem_cons_succ]
        exact hadj_rest s' (by omega)

private theorem toGraph_isLink_of_skeleton_adj {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) {x y : S} (hadj : Γ.toHypergraph.skeleton.Adj x y) :
    ∃ ed : Γ.E, Γ.toGraph.IsLink ed.1 x y := by
  obtain ⟨hne, ed, ⟨hed, hxV, hxcl⟩, ⟨_, hyV, hycl⟩⟩ := id hadj
  refine ⟨⟨ed, hed⟩, hed, hxV, hyV, ?_⟩
  rcases Γ.edge_cond ed hed with ⟨u, v, _, hcap, _⟩ | ⟨u, hcap, _⟩
  · have hx_uv : x ∈ ({u, v} : Set S) := hcap ▸ ⟨hxcl, hxV⟩
    have hy_uv : y ∈ ({u, v} : Set S) := hcap ▸ ⟨hycl, hyV⟩
    rw [hcap]
    rcases mem_insert_iff.mp hx_uv with rfl | hx_eq <;>
      rcases mem_insert_iff.mp hy_uv with rfl | hy_eq
    · exact absurd rfl hne
    · rw [mem_singleton_iff.mp hy_eq]
    · rw [mem_singleton_iff.mp hx_eq, pair_comm]
    · exact absurd ((mem_singleton_iff.mp hx_eq).trans (mem_singleton_iff.mp hy_eq).symm) hne
  · exfalso
    have hx_u : x = u := mem_singleton_iff.mp (hcap ▸ ⟨hxcl, hxV⟩)
    have hy_u : y = u := mem_singleton_iff.mp (hcap ▸ ⟨hycl, hyV⟩)
    exact hne (hx_u.trans hy_u.symm)

/-- A skeleton walk lifts to a walk of the drawing with the same vertex
support. This turns the linking paths of VIII Section 16 into the
path drawings used by VII (9.3). -/
theorem exists_graphWalk_of_skeleton_walk {S : Type w} [TopologicalSpace S]
    (Γ : Drawing S) {a b : S} (ha : a ∈ Γ.V)
    (W : Γ.toHypergraph.skeleton.Walk a b) :
    ∃ P : GraphWalk Γ.toGraph a b, P.support = W.support := by
  induction W with
  | nil => exact ⟨.nil ha, rfl⟩
  | @cons a c b hac W ih =>
    obtain ⟨e, he⟩ := toGraph_isLink_of_skeleton_adj Γ hac
    obtain ⟨P, hP⟩ := ih he.right_mem
    exact ⟨.cons he P, congrArg (List.cons a) hP⟩

theorem hasDisjointGraphPathsFromTo_of_le {α : Type u} {β : Type v}
    {G₀ G : Graph α β} (hle : G₀ ≤ G) {A B : Set α} {r : ℕ}
    (h : HasDisjointGraphPathsFromTo G₀ A B r) :
    HasDisjointGraphPathsFromTo G A B r := by
  obtain ⟨P, hP, hdis⟩ := h
  refine ⟨P, fun i => ?_, hdis⟩
  obtain ⟨u, hu, v, hv, ⟨wp⟩⟩ := hP i
  exact ⟨u, hu, v, hv, ⟨{ wp with le_G := wp.le_G.trans hle }⟩⟩

/-- Lifting `HasDisjointPaths` on `Γ.toHypergraph.skeleton` across a graph isomorphism
`iso : Iso G Γ.toGraph` to `HasDisjointGraphPathsFromTo G A B r`. -/
theorem hasDisjointGraphPathsFromTo_of_iso_drawing {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {G : Graph α β} {Γ : Drawing S} (iso : Iso G Γ.toGraph)
    {A B : Set α} {Z₁ Z₂ : Set S} {r : ℕ} (hZ₁V : Z₁ ⊆ Γ.V)
    (hA : ∀ z : Γ.V, z.1 ∈ Z₁ → (iso.vertexEquiv.symm z).1 ∈ A)
    (hB : ∀ z : Γ.V, z.1 ∈ Z₂ → (iso.vertexEquiv.symm z).1 ∈ B)
    (hp : HasDisjointPaths Γ.toHypergraph.skeleton Z₁ Z₂ r) :
    HasDisjointGraphPathsFromTo G A B r := by
  obtain ⟨Q, hQ⟩ := hp
  have hex : ∀ i : Fin r, ∃ P : Graph α β,
      IsGraphPathFromTo G P A B ∧
        V(P) = {x : α | ∃ (z : S) (hz : z ∈ (Q i).walk.support),
          (iso.vertexEquiv.symm ⟨z, (walk_support_mem_V_and_adj Γ (hZ₁V (Q i).first_mem)
            (Q i).walk).1 z hz⟩).1 = x} := fun i => by
    obtain ⟨hsuppV, hadj⟩ := walk_support_mem_V_and_adj Γ (hZ₁V (Q i).first_mem) (Q i).walk
    let L := (Q i).walk.support
    have hL_pos : 1 ≤ L.length := walk_support_nonempty (Q i).walk
    let m : ℕ := L.length - 1
    have hLm : L.length = m + 1 := by omega
    let fV : {z // z ∈ L} → α := fun z => (iso.vertexEquiv.symm ⟨z.1, hsuppV z.1 z.2⟩).1
    have hfV_inj : Injective fV := by
      intro z₁ z₂ heq
      have hsub : iso.vertexEquiv.symm ⟨z₁.1, hsuppV z₁.1 z₁.2⟩ =
          iso.vertexEquiv.symm ⟨z₂.1, hsuppV z₂.1 z₂.2⟩ := Subtype.ext heq
      have hsub2 : (⟨z₁.1, hsuppV z₁.1 z₁.2⟩ : V(Γ.toGraph)) = ⟨z₂.1, hsuppV z₂.1 z₂.2⟩ :=
        iso.vertexEquiv.symm.injective hsub
      exact Subtype.ext (congrArg (Subtype.val : V(Γ.toGraph) → S) hsub2)
    let verts : List α := L.attach.map fV
    have hverts_len : verts.length = m + 1 := by simp [verts, hLm]
    have hverts_nd : verts.Nodup :=
      (List.nodup_attach.mpr (Q i).isPath.support_nodup).map hfV_inj
    have hverts_get : ∀ (s : ℕ) (hs : s < m + 1),
        verts[s]'(by omega) =
          (iso.vertexEquiv.symm ⟨L[s]'(by omega), hsuppV _ (List.getElem_mem _)⟩).1 :=
      fun s hs => by simp [verts, fV]
    have hstep_link : ∀ s : Fin m, ∃ e : E(G),
        G.IsLink e.1 (verts[s.1]'(by have := s.2; omega))
          (verts[s.1 + 1]'(by have := s.2; omega)) := fun s => by
      have hs_lt : s.1 < m := s.2
      obtain ⟨ed, hlinkZ⟩ := toGraph_isLink_of_skeleton_adj Γ
        (hadj s.1 (by change s.1 + 1 < L.length; omega))
      let ed' : E(Γ.toGraph) := ⟨ed.1, ed.2⟩
      let z₀ : V(Γ.toGraph) := ⟨L[s.1]'(by omega), hsuppV _ (List.getElem_mem _)⟩
      let z₁ : V(Γ.toGraph) := ⟨L[s.1 + 1]'(by omega), hsuppV _ (List.getElem_mem _)⟩
      let e := iso.edgeEquiv.symm ed'
      let x₀ := iso.vertexEquiv.symm z₀
      let y₀ := iso.vertexEquiv.symm z₁
      refine ⟨e, ?_⟩
      rw [hverts_get s.1 (by omega), hverts_get (s.1 + 1) (by omega)]
      change G.IsLink e.1 x₀.1 y₀.1
      rw [iso.isLink_iff e x₀ y₀]
      change Γ.toGraph.IsLink (iso.edgeEquiv (iso.edgeEquiv.symm ed')).1
        (iso.vertexEquiv (iso.vertexEquiv.symm z₀)).1
        (iso.vertexEquiv (iso.vertexEquiv.symm z₁)).1
      rw [iso.edgeEquiv.apply_symm_apply, iso.vertexEquiv.apply_symm_apply,
        iso.vertexEquiv.apply_symm_apply]
      exact hlinkZ
    choose e_step he_step using hstep_link
    let edges : List β := List.ofFn (fun s : Fin m => (e_step s).1)
    have hedges_len : edges.length = m := List.length_ofFn
    let V₀ : Set α := {x | x ∈ verts}
    let E₀ : Set β := {e | e ∈ edges}
    have hV₀ : V₀ ⊆ V(G) := by
      rintro x hx
      simp only [V₀, mem_ofPred_eq, verts, List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨z, rfl⟩ := hx
      exact (iso.vertexEquiv.symm _).2
    have hE₀ : ∀ ⦃e x y⦄, e ∈ E₀ → G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀ := by
      rintro e x y he hl
      simp only [E₀, mem_ofPred_eq, edges, List.mem_ofFn] at he
      obtain ⟨s, rfl⟩ := he
      have hls := he_step s
      have hx_or := G.eq_or_eq_of_isLink_of_isLink hl hls
      have hy_or := G.eq_or_eq_of_isLink_of_isLink hl.symm hls
      refine ⟨?_, ?_⟩
      · rcases hx_or with rfl | rfl <;> exact List.getElem_mem _
      · rcases hy_or with rfl | rfl <;> exact List.getElem_mem _
    let P := subgraphOfVertsEdges G V₀ E₀ hV₀ hE₀
    have hEP : E(P) = E₀ := by
      ext e
      rw [P.edge_mem_iff_exists_isLink]
      constructor
      · rintro ⟨_, _, he, _⟩; exact he
      · intro he
        have he' : e ∈ edges := he
        rw [List.mem_ofFn] at he'
        obtain ⟨s, rfl⟩ := he'
        exact ⟨_, _, he, he_step s⟩
    let u₀ : α := verts[0]'(by omega)
    let v₀ : α := verts[m]'(by omega)
    have hu₀A : u₀ ∈ A := by
      dsimp only [u₀]
      rw [hverts_get 0 (by omega)]
      have h0 : L[0]'(by omega) = (Q i).first := walk_support_head (Q i).walk
      exact hA ⟨L[0]'(by omega), hsuppV _ (List.getElem_mem _)⟩ (h0 ▸ (Q i).first_mem)
    have hv₀B : v₀ ∈ B := by
      dsimp only [v₀]
      rw [hverts_get m (by omega)]
      have hm_eq : m = L.length - 1 := rfl
      have hlast : L[m]'(by omega) = (Q i).last := walk_support_last (Q i).walk
      exact hB ⟨L[m]'(by omega), hsuppV _ (List.getElem_mem _)⟩ (hlast ▸ (Q i).last_mem)
    have wp : GraphPathIn G P u₀ v₀ :=
      { verts := verts
        edges := edges
        le_G := subgraphOfVertsEdges_le _ _ _ _ _
        length_verts := by omega
        nodup_verts := hverts_nd
        head_eq := rfl
        last_eq := by simp [hedges_len, v₀]
        vertexSet_eq := rfl
        edgeSet_eq := hEP
        isLink_step := fun s hs => by
          have hs' : s < m := hedges_len ▸ hs
          have hget_e : edges[s]'hs = (e_step ⟨s, hs'⟩).1 := by simp [edges]
          rw [hget_e]
          exact ⟨by simp [E₀, edges], he_step ⟨s, hs'⟩⟩ }
    refine ⟨P, ⟨u₀, hu₀A, v₀, hv₀B, ⟨wp⟩⟩, ?_⟩
    ext x
    simp only [P, subgraphOfVertsEdges_vertexSet, V₀, mem_ofPred_eq, verts, List.mem_map,
      List.mem_attach, true_and, Subtype.exists, fV, L]
  choose P hP hPV using hex
  refine ⟨P, hP, fun i j hij => disjoint_left.mpr fun x hxi hxj => ?_⟩
  rw [hPV i] at hxi
  rw [hPV j] at hxj
  obtain ⟨z₁, hz₁, rfl⟩ := hxi
  obtain ⟨z₂, hz₂, heq⟩ := hxj
  have hsub := iso.vertexEquiv.symm.injective (Subtype.ext heq)
  have hz_eq : z₁ = z₂ := (congrArg Subtype.val hsub).symm
  exact disjoint_left.mp (hQ hij) hz₁ (hz_eq ▸ hz₂)

/-- **Menger across laminar hoops in a framing.**
If `fr : τ.Framing X` and `(r : ℕ∞) ≤ τ.width`, then for any `τ.Γ`-normal laminar hoops
`H₁, H₂ ⊆ Σ(τ.F₁, τ.F₂)` that are not cut-trivial in `τ`, there are `r` mutually vertex-disjoint
paths in `(fr.subGraft hlam).G` (and hence in `X.G`) from `fr.vertsIn H₁` to `fr.vertsIn H₂`. -/
theorem Tube.Framing.hasDisjointGraphPaths_subGraft {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {τ : Tube S} {X : Graft α β} (fr : τ.Framing X)
    {r : ℕ} (hw : (r : ℕ∞) ≤ τ.width)
    {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hsub₁ : H₁ ⊆ cylinderBetween τ.F₁ τ.F₂) (hsub₂ : H₂ ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hnt₁ : ¬ τ.IsCutTrivial H₁) (hnt₂ : ¬ τ.IsCutTrivial H₂) :
    HasDisjointGraphPathsFromTo (fr.subGraft hlam).G (fr.vertsIn H₁) (fr.vertsIn H₂) r := by
  have : T2Space S := τ.t2Space
  have hp := hasDisjointPaths_skeleton_of_laminar_hoops τ hw hlam hsub₁ hsub₂ hN₁ hN₂ hnt₁ hnt₂
  let subFr := fr.subFraming hlam hN₁ hN₂
  have hcl : IsClosed (cylinderBetween H₁ H₂) := isClosed_cylinderBetween hlam
  have hVEq : (τ.Γ.interSet (cylinderBetween H₁ H₂)).V = τ.Γ.V ∩ cylinderBetween H₁ H₂ :=
    interSet_V_of_isClosed τ.Γ hcl
  refine hasDisjointGraphPathsFromTo_of_iso_drawing subFr.iso inter_subset_left ?_ ?_ hp
  · rintro z ⟨_, hzH₁⟩
    have hz : z.1 ∈ τ.Γ.V ∩ cylinderBetween H₁ H₂ :=
      hVEq ▸ (show z.1 ∈ (τ.Γ.interSet (cylinderBetween H₁ H₂)).V from z.2)
    let z' : V(τ.Γ.toGraph) := ⟨z.1, hz.1⟩
    change (fr.iso.vertexEquiv.symm z').1 ∈ fr.vertsIn H₁
    refine ⟨(fr.iso.vertexEquiv.symm z').2, ?_⟩
    change (fr.iso.vertexEquiv (fr.iso.vertexEquiv.symm z')).1 ∈ H₁
    rw [fr.iso.vertexEquiv.apply_symm_apply]
    exact hzH₁
  · rintro z ⟨_, hzH₂⟩
    have hz : z.1 ∈ τ.Γ.V ∩ cylinderBetween H₁ H₂ :=
      hVEq ▸ (show z.1 ∈ (τ.Γ.interSet (cylinderBetween H₁ H₂)).V from z.2)
    let z' : V(τ.Γ.toGraph) := ⟨z.1, hz.1⟩
    change (fr.iso.vertexEquiv.symm z').1 ∈ fr.vertsIn H₂
    refine ⟨(fr.iso.vertexEquiv.symm z').2, ?_⟩
    change (fr.iso.vertexEquiv (fr.iso.vertexEquiv.symm z')).1 ∈ H₂
    rw [fr.iso.vertexEquiv.apply_symm_apply]
    exact hzH₂

theorem Tube.Framing.hasDisjointGraphPaths_of_laminar_hoops {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {τ : Tube S} {X : Graft α β} (fr : τ.Framing X)
    {r : ℕ} (hw : (r : ℕ∞) ≤ τ.width)
    {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hsub₁ : H₁ ⊆ cylinderBetween τ.F₁ τ.F₂) (hsub₂ : H₂ ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (hnt₁ : ¬ τ.IsCutTrivial H₁) (hnt₂ : ¬ τ.IsCutTrivial H₂) :
    HasDisjointGraphPathsFromTo X.G (fr.vertsIn H₁) (fr.vertsIn H₂) r :=
  hasDisjointGraphPathsFromTo_of_le
    (fr.subGraph_le (cylinderBetween H₁ H₂) (isClosed_cylinderBetween hlam))
    (fr.hasDisjointGraphPaths_subGraft hw hlam hsub₁ hsub₂ hN₁ hN₂ hnt₁ hnt₂)

end LiftSkeletonPaths

end GraphMinor.GM08
