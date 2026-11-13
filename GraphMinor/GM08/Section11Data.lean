module

public import GraphMinor.GM08.Section11RingModel

/-!
# The hypotheses of `ModelSetting` from the portraits

Let `P_1` and `P_2` be portraits derived from `(G_1, τ_1)` and `(G_2, τ_2)` via `Γ_1` and `Γ_2`,
and let `(Ξ, σ)` be a simulation of `P_1` in `P_2` (Graph Minors VIII, (11.2)). Here we prove the
hypotheses of `ModelSetting` from these data (`exists_modelSetting`).

* The image under `σ` of the cell of a ring `F_i` of `Γ_1` is the cell of a ring `F'_{π i}` of
  `Γ_2`, since the labels are not `*` (`ring_image`). Then `π` is injective.
* The image under `σ` of the cell of an edge `e` of `Γ_0` is the cell of an edge `e'` of `Γ'_0`,
  since the labels are `*` (`edge_image`). The ends of `e` and `e'` correspond through the orders
  `μ` of the two cells.
* An edge `f` of `Ξ` lies in a cell of `P_2`. By condition (iv) of a simulation this is not the
  image of a cell of `P_1`. So either `f` lies in the cell of a ring `F'_j` with `j` not in the
  image of `π`, or `f` joins the ends of an edge of `Γ'_0` that is not an image edge
  (`step_of`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface Graph

universe u u' v'

variable {S : Type u} [TopologicalSpace S] [T1Space S]

/-- Distinct rings have distinct cells. -/
theorem ringCell_injective (hS : IsClosedDisc (univ : Set S)) {Γ : Drawing S} {t : ℕ}
    {F : Fin t → Set S} (hF : IsFoundation Γ univ F) :
    Function.Injective (fun i : Fin t => (F i ∪ insideSet (F i)) \ ringNodes Γ F) := by
  intro i i' heq
  simp only at heq
  obtain ⟨x, hx⟩ := insideSet_nonempty hS (hF.isOArc i)
  have hxc : x ∈ (F i ∪ insideSet (F i)) \ ringNodes Γ F := ⟨Or.inr hx, fun hN => hN.2 i hx⟩
  rw [heq] at hxc
  exact disc_eq_of_inside hS hF hxc.1 hx

theorem length_eq_ncard {l : List S} (hl : l.Nodup) : l.length = {x | x ∈ l}.ncard := by
  classical
  have : {x | x ∈ l} = (l.toFinset : Set S) := by
    ext
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hl]

/-- An edge with two distinct ends links them. -/
theorem isLink_of_inc_of_ne {α β : Type*} {G : Graph α β} {e : β} {p q : α} (hp : G.Inc e p)
    (hq : G.Inc e q) (hne : p ≠ q) : G.IsLink e p q := by
  obtain ⟨y, hy⟩ := hp
  rcases hq.eq_or_eq_of_isLink hy with h | h
  · exact absurd h.symm hne
  · rw [h]
    exact hy

variable {α : Type u'} {β : Type v'} {k : ℕ} {X₁ X₂ : RootedGraph α β}
  {gd₁ : GraftDrawing X₁.G X₁.toGraft.T S} {gd₂ : GraftDrawing X₂.G X₂.toGraft.T S}
  {t₁ t₂ : ℕ} {F₁ : Fin t₁ → Set S} {F₂ : Fin t₂ → Set S}
  {P₁ P₂ : QPortrait (QKElem α β S ((k : ℤ) - 1)) S} {Ξ : Drawing S}
  {σv : S → Graph S (Set S)} {σe : Set S → Set S}

/-- The image of the cell of a ring of `Γ_1` is the cell of a ring of `Γ_2`, and the label of
the first is simulated in the label of the second. -/
theorem ring_image (hS : IsClosedDisc (univ : Set S)) (hP₁ : IsDerivedPortraitVia X₁ gd₁ F₁ P₁)
    (hP₂ : IsDerivedPortraitVia X₂ gd₂ F₂ P₂)
    (hsim : IsPortraitSimulation (qkLE S ((k : ℤ) - 1)) P₁ P₂ Ξ σv σe) (i : Fin t₁) :
    ∃ (j : Fin t₂) (Y₁ Y₂ : RootedGraph α β),
      σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁) =
        (F₂ j ∪ insideSet (F₂ j)) \ ringNodes gd₂.drawing F₂ ∧
      IsRingGraph X₁ gd₁ (F₁ i) Y₁ (P₁.μ ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁)) ∧
      IsRingGraph X₂ gd₂ (F₂ j) Y₂
        (P₂.μ (σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁))) ∧
      IsRootedGraphSimulatedIn Y₁ Y₂ := by
  obtain ⟨-, -, -, hmaps, -, -, -, -, -, -, -, hle⟩ := hsim
  obtain ⟨hc, -, y, hy⟩ := hP₁.ring_cell_mem i
  obtain ⟨i', hi', -, hR₁⟩ := hP₁.ring_cell hc hy
  have hii : i = i' := ringCell_injective hS hP₁.foundation hi'
  subst hii
  have hc₂ := hmaps hc
  have hl := hle _ hc
  rw [hy] at hl
  cases h2 : P₂.φ (σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁)) with
  | none =>
    rw [h2] at hl
    exact hl.elim
  | some y' =>
    rw [h2] at hl
    obtain ⟨j, hj, -, hR₂⟩ := hP₂.ring_cell hc₂ h2
    exact ⟨j, y.1, y'.1, hj, hR₁, hR₂, hl⟩

/-- The image of the cell of an edge `e` of `Γ_0` is the cell of an edge `e'` of `Γ'_0`. -/
theorem edge_image (hS : IsClosedDisc (univ : Set S)) (hP₁ : IsDerivedPortraitVia X₁ gd₁ F₁ P₁)
    (hP₂ : IsDerivedPortraitVia X₂ gd₂ F₂ P₂)
    (hsim : IsPortraitSimulation (qkLE S ((k : ℤ) - 1)) P₁ P₂ Ξ σv σe) {e : Set S}
    (he : e ∈ ringEdges gd₁.drawing F₁) :
    ∃ c ∈ P₁.painting.cells, ∃ e' ∈ ringEdges gd₂.drawing F₂, e ⊆ c ∧ e' ⊆ σe c ∧
      closure c ∩ gd₁.drawing.U = closure e ∧ closure c \ c = closure e ∩ gd₁.drawing.V ∧
      closure (σe c) \ σe c = closure e' ∩ gd₂.drawing.V := by
  obtain ⟨-, -, -, hmaps, -, -, -, -, -, -, -, hle⟩ := hsim
  obtain ⟨c, hc, hφ, hec⟩ := hP₁.edge_cell_mem he
  obtain ⟨e₀, he₀, -, hcl₀, hends₀⟩ := hP₁.edge_cell hS hc hφ
  have he₀e : e = e₀ := eq_of_subset_closure_inter he.1 he₀.1 hec hcl₀
  subst he₀e
  have hc₂ := hmaps hc
  have hl := hle c hc
  rw [hφ] at hl
  cases h2 : P₂.φ (σe c) with
  | some y' =>
    rw [h2] at hl
    exact hl.elim
  | none =>
    obtain ⟨e', he', he'c, -, hends'⟩ := hP₂.edge_cell hS hc₂ h2
    exact ⟨c, hc, e', he', hec, he'c, hcl₀, hends₀, hends'⟩

/-- An edge of a tree `σ(s)` either has equal ends, or joins the ends of an edge of `Γ'_0` that
is not an image edge, or lies in the cell of a ring of `Γ_2` that is not an image ring. -/
theorem step_of (hS : IsClosedDisc (univ : Set S)) (hP₁ : IsDerivedPortraitVia X₁ gd₁ F₁ P₁)
    (hP₂ : IsDerivedPortraitVia X₂ gd₂ F₂ P₂)
    (hsim : IsPortraitSimulation (qkLE S ((k : ℤ) - 1)) P₁ P₂ Ξ σv σe) {π : Fin t₁ → Fin t₂}
    (hπ : ∀ i, σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁) =
      (F₂ (π i) ∪ insideSet (F₂ (π i))) \ ringNodes gd₂.drawing F₂)
    {cell partner : Set S → Set S}
    (hpart : ∀ e ∈ ringEdges gd₁.drawing F₁, cell e ∈ P₁.painting.cells ∧
      partner e ∈ ringEdges gd₂.drawing F₂ ∧ partner e ⊆ σe (cell e)) :
    ∀ s ∈ ringNodes gd₁.drawing F₁, ∀ f p q, (σv s).IsLink f p q → p = q ∨
      (∃ e' ∈ ringEdges gd₂.drawing F₂, e' ∉ partner '' ringEdges gd₁.drawing F₁ ∧
        gd₂.drawing.toGraph.IsLink e' p q) ∨
      ∃ j ∈ (range π)ᶜ, f ⊆ (F₂ j ∪ insideSet (F₂ j)) \ ringNodes gd₂.drawing F₂ ∧
        p ∈ F₂ j ∧ q ∈ F₂ j := by
  intro s hs f p q hl
  obtain ⟨hΞV, -, hcomp, hmaps, hΞcell, -, -, hiv, -, -, -, -⟩ := hsim
  have hsN : s ∈ P₁.painting.N := by
    rw [hP₁.nodes]
    exact hs
  have hfl : Ξ.toGraph.IsLink f p q := hl.mono (hcomp s hsN).1
  obtain ⟨c', hc', hfc'⟩ := hΞcell f hfl.1
  have hpN : p ∈ ringNodes gd₂.drawing F₂ := by
    rw [← hP₂.nodes, ← hΞV]
    exact hfl.2.1
  have hqN : q ∈ ringNodes gd₂.drawing F₂ := by
    rw [← hP₂.nodes, ← hΞV]
    exact hfl.2.2.1
  have hends : p ∈ closure f ∧ q ∈ closure f := by
    have hp : p ∈ closure f ∩ Ξ.V := by
      rw [hfl.2.2.2]
      exact mem_insert p {q}
    have hq : q ∈ closure f ∩ Ξ.V := by
      rw [hfl.2.2.2]
      exact mem_insert_of_mem p rfl
    exact ⟨hp.1, hq.1⟩
  obtain ⟨x, hx⟩ : f.Nonempty := hfl.1.1
  have hfE : f ∈ E(σv s) := hl.edge_mem
  have hiv' : ∀ c ∈ P₁.painting.cells, Disjoint f (σe c) := fun c hc =>
    hiv s hsN c hc f hfE
  cases h2 : P₂.φ c' with
  | some y =>
    obtain ⟨j, hj, hcl, -⟩ := hP₂.ring_cell hc' h2
    by_cases hjr : j ∈ range π
    · obtain ⟨i, rfl⟩ := hjr
      have hc := (hP₁.ring_cell_mem i).1
      have hd := hiv' _ hc
      rw [hπ i, ← hj] at hd
      exact absurd (hfc' hx) (Set.disjoint_left.mp hd hx)
    · refine Or.inr (Or.inr ⟨j, hjr, hj ▸ hfc', ?_, ?_⟩)
      · have hp : p ∈ (F₂ j ∪ insideSet (F₂ j)) ∩ ringNodes gd₂.drawing F₂ :=
          ⟨hcl ▸ closure_mono hfc' hends.1, hpN⟩
        rw [hP₂.foundation.ring_inter_nodes hS] at hp
        exact hp.2
      · have hq : q ∈ (F₂ j ∪ insideSet (F₂ j)) ∩ ringNodes gd₂.drawing F₂ :=
          ⟨hcl ▸ closure_mono hfc' hends.2, hqN⟩
        rw [hP₂.foundation.ring_inter_nodes hS] at hq
        exact hq.2
  | none =>
    obtain ⟨e', he', he'c, -, hends'⟩ := hP₂.edge_cell hS hc' h2
    have hnot : ∀ z ∈ ringNodes gd₂.drawing F₂, z ∉ c' := fun z hz hzc =>
      (PaintingInDisc.cell_subset hc' hzc).2 (by rw [hP₂.nodes]; exact hz)
    have hp' : p ∈ closure e' ∩ gd₂.drawing.V := by
      rw [← hends']
      exact ⟨closure_mono hfc' hends.1, hnot p hpN⟩
    have hq' : q ∈ closure e' ∩ gd₂.drawing.V := by
      rw [← hends']
      exact ⟨closure_mono hfc' hends.2, hnot q hqN⟩
    by_cases hpq : p = q
    · exact Or.inl hpq
    refine Or.inr (Or.inl ⟨e', he', ?_, isLink_of_inc_of_ne (toGraph_inc_iff.mpr ⟨he'.1, hp'⟩)
      (toGraph_inc_iff.mpr ⟨he'.1, hq'⟩) hpq⟩)
    rintro ⟨e₀, he₀, rfl⟩
    obtain ⟨hcell, hpm, hsub⟩ := hpart e₀ he₀
    obtain ⟨y, hy⟩ := hpm.1.1
    have hcc : σe (cell e₀) = c' := by
      rcases eq_or_disjoint_of_mem_componentsIn (hmaps hcell) hc' with h | h
      · exact h
      · exact absurd (he'c hy) (Set.disjoint_left.mp h (hsub hy))
    have hd := hiv' _ hcell
    rw [hcc] at hd
    exact absurd (hfc' hx) (Set.disjoint_left.mp hd hx)

/-- **The hypotheses of `ModelSetting`.** -/
theorem exists_modelSetting [Nonempty S] (hS : IsClosedDisc (univ : Set S))
    (hP₁ : IsDerivedPortraitVia X₁ gd₁ F₁ P₁) (hP₂ : IsDerivedPortraitVia X₂ gd₂ F₂ P₂)
    (hsim : IsPortraitSimulation (qkLE S ((k : ℤ) - 1)) P₁ P₂ Ξ σv σe) :
    ∃ (Ξ' : Fin t₂ → Drawing S) (π : Fin t₁ → Fin t₂) (R₁ : Fin t₁ → Graph S (Set S))
      (R₂ : Fin t₂ → Graph S (Set S)) (ηR : Fin t₁ → S → Set S) (εR : Fin t₁ → Set S → Set S)
      (partner : Set S → Set S),
      ModelSetting gd₁.drawing gd₂.drawing F₁ F₂ Ξ σv Ξ' π R₁ R₂ ηR εR partner := by
  classical
  have hsim' := hsim
  obtain ⟨hΞV, -, hcomp, hmaps, -, hinj, hσinj, -, hcount, hμ, -, -⟩ := hsim'
  have hΞV' : Ξ.V = ringNodes gd₂.drawing F₂ := hΞV.trans hP₂.nodes
  have hF₁ := hP₁.foundation
  have hF₂ := hP₂.foundation
  -- The forests `Ξ'_j` from (8.4).
  have hforest : ∀ j : Fin t₂, ∃ Ξ'j : Drawing S, Ξ'j.IsSubdrawing gd₂.drawing ∧
      Ξ'j.U ⊆ F₂ j ∪ insideSet (F₂ j) ∧ (∀ e ∈ Ξ'j.E, e ⊆ insideSet (F₂ j)) ∧
      ∀ u ∈ gd₂.drawing.V ∩ F₂ j, ∀ v ∈ gd₂.drawing.V ∩ F₂ j,
        (u ∈ (xiPart Ξ ((F₂ j ∪ insideSet (F₂ j)) \ ringNodes gd₂.drawing F₂)).V ∧
          v ∈ (xiPart Ξ ((F₂ j ∪ insideSet (F₂ j)) \ ringNodes gd₂.drawing F₂)).V ∧
          Nonempty (GraphWalk
            (xiPart Ξ ((F₂ j ∪ insideSet (F₂ j)) \ ringNodes gd₂.drawing F₂)).toGraph u v)) ↔
        (u ∈ Ξ'j.V ∧ v ∈ Ξ'j.V ∧ Nonempty (GraphWalk Ξ'j.toGraph u v)) := fun j =>
    exists_ring_forest hS hF₂ gd₂.isProper j (by rw [hΞV']; exact fun x hx => hx.1)
      (hP₂.ring_cell_mem j).2.1.subset
  choose Ξ' hΞ'sub hΞ'U hΞ'E hΞ'iff using hforest
  -- The rings.
  choose π Y₁ Y₂ hπ using ring_image hS hP₁ hP₂ hsim
  have hπinj : Function.Injective π := by
    intro i i' hii
    have h1 := (hP₁.ring_cell_mem i).1
    have h2 := (hP₁.ring_cell_mem i').1
    have heq : σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁) =
        σe ((F₁ i' ∪ insideSet (F₁ i')) \ ringNodes gd₁.drawing F₁) := by
      rw [(hπ i).1, (hπ i').1, hii]
    exact ringCell_injective hS hF₁ (hσinj h1 h2 heq)
  have hring : ∀ i, ∃ (ηRi : S → Set S) (εRi : Set S → Set S),
      IsMinorModel (ringGraph gd₁.drawing (F₁ i)) (ringGraph gd₂.drawing (F₂ (π i))) ηRi εRi ∧
      (P₁.μ ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁)).length =
        (P₂.μ (σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁))).length ∧
      ∀ (n : ℕ) (hn₁ : n < (P₁.μ ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁)).length)
        (hn₂ : n < (P₂.μ (σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁))).length),
        (P₂.μ (σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁)))[n] ∈
          ηRi (P₁.μ ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁))[n] := fun i =>
    exists_ring_model hS (hF₁.isOArc i) (hF₂.isOArc (π i)) (hπ i).2.1 (hπ i).2.2.1
      (hπ i).2.2.2
  choose ηR εR hηR hlen hroot using hring
  -- The roots of the rings.
  have hpair : ∀ i, ∀ z ∈ gd₂.drawing.V ∩ F₂ (π i), ∃ v ∈ gd₁.drawing.V ∩ F₁ i,
      z ∈ ηR i v ∧ z ∈ partA σv (ringNodes gd₁.drawing F₁) v := by
    intro i z hz
    have hz2 : z ∈ {x | x ∈ P₂.μ (σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁))} := by
      rw [(hπ i).2.2.1.2.2.2.2.1]
      exact hz
    obtain ⟨n, hn₂, rfl⟩ := List.getElem_of_mem hz2
    have hn₁ : n < (P₁.μ ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁)).length := by
      rw [hlen i]
      exact hn₂
    have hv : (P₁.μ ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁))[n] ∈
        gd₁.drawing.V ∩ F₁ i := by
      rw [← (hπ i).2.1.2.2.2.2.1]
      exact List.getElem_mem _
    refine ⟨_, hv, hroot i n hn₁ hn₂, ⟨hv.1, fun j => hF₁.not_inside_of_mem hS hv.2 j⟩, ?_⟩
    exact hμ _ (hP₁.ring_cell_mem i).1 n hn₁ hn₂
  have hjoin : ∀ i, ∀ v ∈ gd₁.drawing.V ∩ F₁ i, ∃ z ∈ ηR i v,
      z ∈ partA σv (ringNodes gd₁.drawing F₁) v := by
    intro i v hv
    have hv1 : v ∈ {x | x ∈ P₁.μ ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁)} := by
      rw [(hπ i).2.1.2.2.2.2.1]
      exact hv
    obtain ⟨n, hn₁, rfl⟩ := List.getElem_of_mem hv1
    have hn₂ : n < (P₂.μ (σe ((F₁ i ∪ insideSet (F₁ i)) \ ringNodes gd₁.drawing F₁))).length := by
      rw [← hlen i]
      exact hn₁
    exact ⟨_, hroot i n hn₁ hn₂, ⟨hv.1, fun j => hF₁.not_inside_of_mem hS hv.2 j⟩,
      hμ _ (hP₁.ring_cell_mem i).1 n hn₁ hn₂⟩
  -- The edges of `Γ_0`.
  have hedge : ∀ e : Set S, ∃ ce : Set S × Set S, e ∈ ringEdges gd₁.drawing F₁ →
      ce.1 ∈ P₁.painting.cells ∧ ce.2 ∈ ringEdges gd₂.drawing F₂ ∧ e ⊆ ce.1 ∧ ce.2 ⊆ σe ce.1 ∧
      closure ce.1 ∩ gd₁.drawing.U = closure e ∧
      closure ce.1 \ ce.1 = closure e ∩ gd₁.drawing.V ∧
      closure (σe ce.1) \ σe ce.1 = closure ce.2 ∩ gd₂.drawing.V := by
    intro e
    by_cases he : e ∈ ringEdges gd₁.drawing F₁
    · obtain ⟨c, hc, e', he', h1, h2, h3, h4, h5⟩ := edge_image hS hP₁ hP₂ hsim he
      exact ⟨(c, e'), fun _ => ⟨hc, he', h1, h2, h3, h4, h5⟩⟩
    · exact ⟨(∅, ∅), fun h => absurd h he⟩
  choose ce hce using hedge
  have hpart : ∀ e ∈ ringEdges gd₁.drawing F₁, (ce e).1 ∈ P₁.painting.cells ∧
      (ce e).2 ∈ ringEdges gd₂.drawing F₂ ∧ (ce e).2 ⊆ σe (ce e).1 := fun e he =>
    ⟨(hce e he).1, (hce e he).2.1, (hce e he).2.2.2.1⟩
  refine ⟨Ξ', π, fun i => ringGraph gd₁.drawing (F₁ i), fun j => ringGraph gd₂.drawing (F₂ j),
    ηR, εR, fun e => (ce e).2, ?_⟩
  exact
    { xi :=
        { hS := hS
          foundation := hF₂
          ΞV := hΞV'
          comp := fun s hs => hcomp s (by rw [hP₁.nodes]; exact hs)
          inj := fun s₁ hs₁ s₂ hs₂ hne => hinj s₁ (by rw [hP₁.nodes]; exact hs₁) s₂
            (by rw [hP₁.nodes]; exact hs₂) hne
          sub := fun j _ => hΞ'sub j
          U_sub := fun j _ => hΞ'U j
          iff := fun j _ => hΞ'iff j }
      foundation := hF₁
      π_inj := hπinj
      Ξ'_E := fun j _ => hΞ'E j
      R₁_le := fun _ => ringGraph_le
      R₁_V := fun _ => ringGraph_V
      R₁_E := fun i => ringGraph_E hS (hF₁.isOArc i)
      R₂_le := fun _ => ringGraph_le
      R₂_V := fun _ => ringGraph_V
      R₂_E := fun j => ringGraph_E hS (hF₂.isOArc j)
      ring := hηR
      ring_roots := hpair
      ring_join := hjoin
      partner_mem := fun e he => (hce e he).2.1
      partner_inj := by
        intro e₁ he₁ e₂ he₂ heq
        obtain ⟨hc₁, hp₁, hs₁, hsub₁, hcl₁, -⟩ := hce e₁ he₁
        obtain ⟨hc₂, -, hs₂, hsub₂, -⟩ := hce e₂ he₂
        simp only at heq
        obtain ⟨y, hy⟩ := hp₁.1.1
        have hσ : σe (ce e₁).1 = σe (ce e₂).1 := by
          rcases eq_or_disjoint_of_mem_componentsIn (hmaps hc₁) (hmaps hc₂) with h | h
          · exact h
          · exact absurd (hsub₂ (heq ▸ hy)) (Set.disjoint_left.mp h (hsub₁ hy))
        have hc := hσinj hc₁ hc₂ hσ
        rw [← hc] at hs₂
        exact (eq_of_subset_closure_inter he₂.1 he₁.1 hs₂ hcl₁).symm
      partner_ends := by
        intro e he
        obtain ⟨hc, -, -, -, -, hends₁, hends₂⟩ := hce e he
        refine ⟨P₁.μ (ce e).1, P₂.μ (σe (ce e).1), ?_, ?_, ?_, fun n h₁ h₂ => ?_⟩
        · rw [P₁.μ_set _ hc, hends₁]
        · rw [P₂.μ_set _ (hmaps hc), hends₂]
        · rw [length_eq_ncard (P₁.μ_nodup _ hc), length_eq_ncard (P₂.μ_nodup _ (hmaps hc)),
            P₁.μ_set _ hc, P₂.μ_set _ (hmaps hc), hcount _ hc]
        · have hmem : (P₁.μ (ce e).1)[n] ∈ closure e ∩ gd₁.drawing.V := by
            rw [← hends₁, ← P₁.μ_set _ hc]
            exact List.getElem_mem _
          exact ⟨hF₁.ends_subset_nodes hS he hmem, hμ _ hc n h₁ h₂⟩
      step := step_of hS hP₁ hP₂ hsim (fun i => (hπ i).1) hpart }

end GM08
end GraphMinor
