module

public import GraphMinor.GM05.Defs
public import GraphMinor.GM05.Section7Separations
import GraphMinor.GM05.Basic
import Mathlib.Data.Set.Card

/-!
# Graph Minors V, Section 7: The Grid Theorem (Theorem 7.3)

This file formalizes Theorem (7.3) of N. Robertson and P. D. Seymour,
*Graph Minors. V. Excluding a planar graph*, J. Combin. Theory Ser. B **41** (1986), 92–114
(pages 108–109):

- `GraphMinor.GM05.theorem_7_3_simple`: Graph Minors V, (7.3), for even `θ ≥ 6`, every finite graph
  `G ∈ 𝓕_θ` has tree-width at most `θ₉(θ)` (`TreeWidthLE G (θ₉ θ)`).
- `GraphMinor.GM05.theorem_7_3_treeWidth`: the same bound expressed using `treeWidth G ≤ θ₉ θ`.
- `GraphMinor.GM05.treeWidthLE_of_not_isIsoMinor` and
  `GraphMinor.GM05.treeWidth_le_of_not_isIsoMinor`: combining the reduction of Section 2
  (`mem_𝓕_of_not_isIsoMinor`) with Theorem (7.3), if `H` is isomorphic to a minor of the `θ`-grid
  and `G` has no minor isomorphic to `H`, then `G` has tree-width at most `θ₉(θ)`.
-/

namespace GraphMinor.GM05

open SimpleGraph Graph GM01

public section

universe u

variable {V : Type u} {ι₁ ι₂ : Type*}

/-! ## Gluing Tree-Decompositions Across a Separation -/

/-- Left embedding `ι₁ ↪ Option (ι₁ ⊕ ι₂)` sending `a ↦ some (Sum.inl a)`. -/
@[reducible] private def inlEmb (ι₁ ι₂ : Type*) : ι₁ ↪ Option (ι₁ ⊕ ι₂) :=
  ⟨fun a ↦ some (Sum.inl a), fun _ _ h ↦ Sum.inl.inj (Option.some.inj h)⟩

/-- Right embedding `ι₂ ↪ Option (ι₁ ⊕ ι₂)` sending `b ↦ some (Sum.inr b)`. -/
@[reducible] private def inrEmb (ι₁ ι₂ : Type*) : ι₂ ↪ Option (ι₁ ⊕ ι₂) :=
  ⟨fun b ↦ some (Sum.inr b), fun _ _ h ↦ Sum.inr.inj (Option.some.inj h)⟩

/-- The disjoint union of `T₁` and `T₂` on `Option (ι₁ ⊕ ι₂)` (with `none` isolated). -/
private def gluedForest (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂) :
    SimpleGraph (Option (ι₁ ⊕ ι₂)) :=
  T₁.map (inlEmb ι₁ ι₂) ⊔ T₂.map (inrEmb ι₁ ι₂)

/-- The glued tree `T` on `Option (ι₁ ⊕ ι₂)` in the proof of Theorem (7.3) (page 109), obtained
from disjoint copies of `T₁` and `T₂` by adding a new vertex `t₀ = none` adjacent to
`some (Sum.inl t₁)` and `some (Sum.inr t₂)`. -/
private def gluedTree (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂) (t₁ : ι₁) (t₂ : ι₂) :
    SimpleGraph (Option (ι₁ ⊕ ι₂)) :=
  gluedForest T₁ T₂ ⊔ edge none (some (Sum.inl t₁)) ⊔ edge none (some (Sum.inr t₂))

/-- The bag assignment on `Option (ι₁ ⊕ ι₂)` in the proof of Theorem (7.3) (page 109), with
`X_{t₀} = X ∪ (V₁ ∩ V₂)` at `none`. -/
private def gluedBag (X V₁ V₂ : Set V) (χ₁ : ι₁ → Set V) (χ₂ : ι₂ → Set V) :
    Option (ι₁ ⊕ ι₂) → Set V
  | none => X ∪ (V₁ ∩ V₂)
  | some (Sum.inl a) => χ₁ a
  | some (Sum.inr b) => χ₂ b

@[reducible] private def inlForestHom (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂) :
    T₁ →g gluedForest T₁ T₂ :=
  ⟨fun a ↦ some (Sum.inl a),
    fun {a a'} hadj ↦ Or.inl ⟨(inlEmb ι₁ ι₂).injective.ne hadj.ne, a, a', hadj, rfl, rfl⟩⟩

@[reducible] private def inrForestHom (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂) :
    T₂ →g gluedForest T₁ T₂ :=
  ⟨fun b ↦ some (Sum.inr b),
    fun {b b'} hadj ↦ Or.inr ⟨(inrEmb ι₁ ι₂).injective.ne hadj.ne, b, b', hadj, rfl, rfl⟩⟩

@[reducible] private def inlTreeHom (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂)
    (t₁ : ι₁) (t₂ : ι₂) : T₁ →g gluedTree T₁ T₂ t₁ t₂ :=
  ⟨fun a ↦ some (Sum.inl a), fun hadj ↦ Or.inl (Or.inl ((inlForestHom T₁ T₂).map_adj hadj))⟩

@[reducible] private def inrTreeHom (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂)
    (t₁ : ι₁) (t₂ : ι₂) : T₂ →g gluedTree T₁ T₂ t₁ t₂ :=
  ⟨fun b ↦ some (Sum.inr b), fun hadj ↦ Or.inl (Or.inl ((inrForestHom T₁ T₂).map_adj hadj))⟩

private lemma injective_inlTreeHom (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂)
    (t₁ : ι₁) (t₂ : ι₂) : Function.Injective (inlTreeHom T₁ T₂ t₁ t₂) :=
  fun _ _ h ↦ (inlEmb ι₁ ι₂).injective h

private lemma injective_inrTreeHom (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂)
    (t₁ : ι₁) (t₂ : ι₂) : Function.Injective (inrTreeHom T₁ T₂ t₁ t₂) :=
  fun _ _ h ↦ (inrEmb ι₁ ι₂).injective h

private lemma not_adj_gluedForest_none {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    {x : Option (ι₁ ⊕ ι₂)} : ¬ (gluedForest T₁ T₂).Adj none x := by
  rintro (⟨_, a, _, _, h, _⟩ | ⟨_, b, _, _, h, _⟩) <;> cases h

private lemma adj_gluedForest_inl_iff {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    {a : ι₁} {x : Option (ι₁ ⊕ ι₂)} :
    (gluedForest T₁ T₂).Adj (some (Sum.inl a)) x ↔
      ∃ a' : ι₁, x = some (Sum.inl a') ∧ T₁.Adj a a' := by
  constructor
  · rintro (⟨_, a₁, a₂, hadj, h1, h2⟩ | ⟨_, b₁, b₂, _, h1, _⟩)
    · have ha : a₁ = a := (inlEmb ι₁ ι₂).injective h1
      exact ⟨a₂, h2.symm, ha ▸ hadj⟩
    · cases Option.some.inj h1
  · rintro ⟨a', rfl, hadj⟩
    exact (inlForestHom T₁ T₂).map_adj hadj

private lemma adj_gluedForest_inr_iff {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    {b : ι₂} {x : Option (ι₁ ⊕ ι₂)} :
    (gluedForest T₁ T₂).Adj (some (Sum.inr b)) x ↔
      ∃ b' : ι₂, x = some (Sum.inr b') ∧ T₂.Adj b b' := by
  constructor
  · rintro (⟨_, a₁, a₂, _, h1, _⟩ | ⟨_, b₁, b₂, hadj, h1, h2⟩)
    · cases Option.some.inj h1
    · have hb : b₁ = b := (inrEmb ι₁ ι₂).injective h1
      exact ⟨b₂, h2.symm, hb ▸ hadj⟩
  · rintro ⟨b', rfl, hadj⟩
    exact (inrForestHom T₁ T₂).map_adj hadj

private lemma walk_gluedForest_inl {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    {x y : Option (ι₁ ⊕ ι₂)} (p : (gluedForest T₁ T₂).Walk x y) :
    ∀ (a : ι₁) (hx : x = some (Sum.inl a)),
      ∃ (a' : ι₁) (hy : y = some (Sum.inl a')) (q : T₁.Walk a a'),
        p = (q.map (inlForestHom T₁ T₂)).copy hx.symm hy.symm := by
  induction p with
  | nil =>
    intro a hx
    exact ⟨a, hx, .nil, by subst hx; rfl⟩
  | @cons u v w hadj p' ih =>
    intro a hx
    subst hx
    obtain ⟨a₂, rfl, hadj₁⟩ := adj_gluedForest_inl_iff.1 hadj
    obtain ⟨a', hy, q', hq'⟩ := ih a₂ rfl
    subst hy
    refine ⟨a', rfl, .cons hadj₁ q', ?_⟩
    rw [hq']
    rfl

private lemma walk_gluedForest_inr {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    {x y : Option (ι₁ ⊕ ι₂)} (p : (gluedForest T₁ T₂).Walk x y) :
    ∀ (b : ι₂) (hx : x = some (Sum.inr b)),
      ∃ (b' : ι₂) (hy : y = some (Sum.inr b')) (q : T₂.Walk b b'),
        p = (q.map (inrForestHom T₁ T₂)).copy hx.symm hy.symm := by
  induction p with
  | nil =>
    intro b hx
    exact ⟨b, hx, .nil, by subst hx; rfl⟩
  | @cons u v w hadj p' ih =>
    intro b hx
    subst hx
    obtain ⟨b₂, rfl, hadj₂⟩ := adj_gluedForest_inr_iff.1 hadj
    obtain ⟨b', hy, q', hq'⟩ := ih b₂ rfl
    subst hy
    refine ⟨b', rfl, .cons hadj₂ q', ?_⟩
    rw [hq']
    rfl

private lemma isAcyclic_gluedForest {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    (hT₁ : T₁.IsAcyclic) (hT₂ : T₂.IsAcyclic) :
    (gluedForest T₁ T₂).IsAcyclic := by
  intro x c hc
  cases x with
  | none =>
    cases c with
    | nil => exact hc.ne_nil rfl
    | cons hadj _ => exact not_adj_gluedForest_none hadj
  | some s =>
    cases s with
    | inl a =>
      obtain ⟨a', hy, q, hq⟩ := walk_gluedForest_inl c a rfl
      have ha' : a' = a := (inlEmb ι₁ ι₂).injective hy.symm
      subst ha'
      rw [hq] at hc
      exact hT₁ q hc.of_map
    | inr b =>
      obtain ⟨b', hy, q, hq⟩ := walk_gluedForest_inr c b rfl
      have hb' : b' = b := (inrEmb ι₁ ι₂).injective hy.symm
      subst hb'
      rw [hq] at hc
      exact hT₂ q hc.of_map

private lemma walk_closed_of_adj_closed {α : Type*} {H : SimpleGraph α} {S : Set α}
    (hclosed : ∀ ⦃u v : α⦄, H.Adj u v → u ∈ S → v ∈ S) {u v : α} (p : H.Walk u v) (hu : u ∈ S) :
    v ∈ S := by
  induction p with
  | nil => exact hu
  | cons hadj p' ih => exact ih (hclosed hadj hu)

private lemma isTree_gluedTree {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂} {t₁ : ι₁} {t₂ : ι₂}
    (hT₁ : T₁.IsTree) (hT₂ : T₂.IsTree) :
    (gluedTree T₁ T₂ t₁ t₂).IsTree := by
  have hacyc₀ : (gluedForest T₁ T₂).IsAcyclic :=
    isAcyclic_gluedForest hT₁.isAcyclic hT₂.isAcyclic
  have hnreach₁ : ¬ (gluedForest T₁ T₂).Reachable none (some (Sum.inl t₁)) := by
    rintro ⟨p⟩
    have hmem : some (Sum.inl t₁) ∈ ({none} : Set (Option (ι₁ ⊕ ι₂))) := by
      refine @walk_closed_of_adj_closed _ _ ({none} : Set (Option (ι₁ ⊕ ι₂)))
        (fun u v hadj hu ↦ ?_) _ _ p (Set.mem_singleton none)
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact False.elim (not_adj_gluedForest_none hadj)
    cases Set.mem_singleton_iff.1 hmem
  have hacyc₁ : (gluedForest T₁ T₂ ⊔ edge none (some (Sum.inl t₁))).IsAcyclic :=
    hacyc₀.sup_edge_of_not_reachable hnreach₁
  have hnreach₂ : ¬ (gluedForest T₁ T₂ ⊔ edge none (some (Sum.inl t₁))).Reachable
      none (some (Sum.inr t₂)) := by
    rintro ⟨p⟩
    let S : Set (Option (ι₁ ⊕ ι₂)) := {x | ∀ b : ι₂, x ≠ some (Sum.inr b)}
    have hmem : some (Sum.inr t₂) ∈ S := by
      refine @walk_closed_of_adj_closed _ _ S (fun u v hadj hu b hvb ↦ ?_) _ _ p
        (by intro b h; cases h)
      subst hvb
      rcases hadj with hadjF | hadjE
      · obtain ⟨b', rfl, _⟩ := adj_gluedForest_inr_iff.1 hadjF.symm
        exact hu b' rfl
      · simp only [edge_adj] at hadjE
        rcases hadjE.1 with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    exact hmem t₂ rfl
  have hacyc₂ : (gluedTree T₁ T₂ t₁ t₂).IsAcyclic :=
    hacyc₁.sup_edge_of_not_reachable hnreach₂
  have hadj_t₁ : (gluedTree T₁ T₂ t₁ t₂).Adj none (some (Sum.inl t₁)) :=
    Or.inl (Or.inr (by simp [edge_adj]))
  have hadj_t₂ : (gluedTree T₁ T₂ t₁ t₂).Adj none (some (Sum.inr t₂)) :=
    Or.inr (by simp [edge_adj])
  have hreach_none : ∀ x : Option (ι₁ ⊕ ι₂), (gluedTree T₁ T₂ t₁ t₂).Reachable x none := by
    intro x
    cases x with
    | none => exact Reachable.refl none
    | some s =>
      cases s with
      | inl a =>
        obtain ⟨p₁⟩ := hT₁.connected a t₁
        exact ⟨(p₁.map (inlTreeHom T₁ T₂ t₁ t₂)).concat hadj_t₁.symm⟩
      | inr b =>
        obtain ⟨p₂⟩ := hT₂.connected b t₂
        exact ⟨(p₂.map (inrTreeHom T₁ T₂ t₁ t₂)).concat hadj_t₂.symm⟩
  exact ⟨Connected.mk (fun u v ↦ (hreach_none u).trans (hreach_none v).symm), hacyc₂⟩

private lemma onTreePath_symm {α : Type*} {T : SimpleGraph α} {u w v : α}
    (h : OnTreePath T u w v) : OnTreePath T w u v := by
  intro p hp
  have hrev := h p.reverse hp.reverse
  rwa [Walk.support_reverse, List.mem_reverse] at hrev

private lemma onTreePath_of_mem_isPath {α : Type*} {T : SimpleGraph α} (hT : T.IsTree)
    {u w v : α} {p : T.Walk u w} (hp : p.IsPath) (hv : v ∈ p.support) :
    OnTreePath T u w v := by
  intro q hq
  have heq : q = p :=
    Subtype.ext_iff.1 ((hT.isAcyclic.subsingleton_path u w).elim ⟨q, hq⟩ ⟨p, hp⟩)
  exact heq ▸ hv

private lemma subset_verts_of_isTreeDecomposition [Fintype ι₁]
    {H : (⊤ : SimpleGraph V).Subgraph} {T : SimpleGraph ι₁} {χ : ι₁ → Set V}
    (hTD : IsTreeDecomposition H T χ) (t : ι₁) : χ t ⊆ H.verts := by
  rw [← hTD.iUnion_eq]
  exact Set.subset_iUnion χ t

/-- Gluing tree-decompositions `(T₁, χ₁)` of `G.induce V₁` and `(T₂, χ₂)` of `G.induce V₂` across
a separation `(V₁, V₂)` of `G` via a new central vertex `t₀ = none` with bag
`X ∪ (V₁ ∩ V₂)` yields a tree-decomposition of `G` (Graph Minors V, proof of (7.3), page 109). -/
private lemma isTreeDecomposition_gluedTree [Fintype ι₁] [Fintype ι₂]
    {G : (⊤ : SimpleGraph V).Subgraph} {V₁ V₂ X : Set V}
    {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    {χ₁ : ι₁ → Set V} {χ₂ : ι₂ → Set V} {t₁ : ι₁} {t₂ : ι₂}
    (hsep : IsSeparation G V₁ V₂) (hX : X ⊆ G.verts)
    (hTD₁ : IsTreeDecomposition (G.induce V₁) T₁ χ₁)
    (hTD₂ : IsTreeDecomposition (G.induce V₂) T₂ χ₂)
    (hX₁ : ((V₁ \ V₂) ∩ X) ∪ (V₁ ∩ V₂) ⊆ χ₁ t₁)
    (hX₂ : ((V₂ \ V₁) ∩ X) ∪ (V₁ ∩ V₂) ⊆ χ₂ t₂) :
    IsTreeDecomposition G (gluedTree T₁ T₂ t₁ t₂) (gluedBag X V₁ V₂ χ₁ χ₂) := by
  classical
  have hχ₁_sub : ∀ a : ι₁, χ₁ a ⊆ V₁ := by
    intro a
    have h := subset_verts_of_isTreeDecomposition hTD₁ a
    rwa [Subgraph.induce_verts] at h
  have hχ₂_sub : ∀ b : ι₂, χ₂ b ⊆ V₂ := by
    intro b
    have h := subset_verts_of_isTreeDecomposition hTD₂ b
    rwa [Subgraph.induce_verts] at h
  have hinter_t₁ : ∀ a : ι₁, χ₁ a ∩ (X ∪ (V₁ ∩ V₂)) ⊆ χ₁ t₁ := by
    intro a v ⟨hva, hv₀⟩
    have hvV₁ : v ∈ V₁ := hχ₁_sub a hva
    apply hX₁
    rcases hv₀ with hvX | hv12
    · by_cases hvV₂ : v ∈ V₂
      · exact Or.inr ⟨hvV₁, hvV₂⟩
      · exact Or.inl ⟨⟨hvV₁, hvV₂⟩, hvX⟩
    · exact Or.inr hv12
  have hinter_t₂ : ∀ b : ι₂, χ₂ b ∩ (X ∪ (V₁ ∩ V₂)) ⊆ χ₂ t₂ := by
    intro b v ⟨hvb, hv₀⟩
    have hvV₂ : v ∈ V₂ := hχ₂_sub b hvb
    apply hX₂
    rcases hv₀ with hvX | hv12
    · by_cases hvV₁ : v ∈ V₁
      · exact Or.inr ⟨hvV₁, hvV₂⟩
      · exact Or.inl ⟨⟨hvV₂, hvV₁⟩, hvX⟩
    · exact Or.inr hv12
  have hinter_12 : ∀ (a : ι₁) (b : ι₂), χ₁ a ∩ χ₂ b ⊆ V₁ ∩ V₂ :=
    fun a b _ ⟨h₁, h₂⟩ ↦ ⟨hχ₁_sub a h₁, hχ₂_sub b h₂⟩
  have hadj_t₁ : (gluedTree T₁ T₂ t₁ t₂).Adj none (some (Sum.inl t₁)) :=
    Or.inl (Or.inr (by simp [edge_adj]))
  have hadj_t₂ : (gluedTree T₁ T₂ t₁ t₂).Adj none (some (Sum.inr t₂)) :=
    Or.inr (by simp [edge_adj])
  have h_inl_inl : ∀ (a₁ a₂ : ι₁) (v : Option (ι₁ ⊕ ι₂)),
      OnTreePath (gluedTree T₁ T₂ t₁ t₂) (some (Sum.inl a₁)) (some (Sum.inl a₂)) v →
      χ₁ a₁ ∩ χ₁ a₂ ⊆ gluedBag X V₁ V₂ χ₁ χ₂ v := by
    intro a₁ a₂ v hp
    let q₁ := (hTD₁.isTree.connected a₁ a₂).some.toPath
    have hp_path : (q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).IsPath :=
      q₁.2.map (injective_inlTreeHom T₁ T₂ t₁ t₂)
    have hv := hp _ hp_path
    rw [Walk.support_map, List.mem_map] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    exact hTD₁.inter_subset (onTreePath_of_mem_isPath hTD₁.isTree q₁.2 hc)
  have h_inr_inr : ∀ (b₁ b₂ : ι₂) (v : Option (ι₁ ⊕ ι₂)),
      OnTreePath (gluedTree T₁ T₂ t₁ t₂) (some (Sum.inr b₁)) (some (Sum.inr b₂)) v →
      χ₂ b₁ ∩ χ₂ b₂ ⊆ gluedBag X V₁ V₂ χ₁ χ₂ v := by
    intro b₁ b₂ v hp
    let q₂ := (hTD₂.isTree.connected b₁ b₂).some.toPath
    have hp_path : (q₂.1.map (inrTreeHom T₁ T₂ t₁ t₂)).IsPath :=
      q₂.2.map (injective_inrTreeHom T₁ T₂ t₁ t₂)
    have hv := hp _ hp_path
    rw [Walk.support_map, List.mem_map] at hv
    obtain ⟨c, hc, rfl⟩ := hv
    exact hTD₂.inter_subset (onTreePath_of_mem_isPath hTD₂.isTree q₂.2 hc)
  have h_inl_none : ∀ (a : ι₁) (v : Option (ι₁ ⊕ ι₂)),
      OnTreePath (gluedTree T₁ T₂ t₁ t₂) (some (Sum.inl a)) none v →
      χ₁ a ∩ (X ∪ (V₁ ∩ V₂)) ⊆ gluedBag X V₁ V₂ χ₁ χ₂ v := by
    intro a v hp
    let q₁ := (hTD₁.isTree.connected a t₁).some.toPath
    have hp₁_path : (q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).IsPath :=
      q₁.2.map (injective_inlTreeHom T₁ T₂ t₁ t₂)
    have hnone_notMem : none ∉ (q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).support := by
      rw [Walk.support_map, List.mem_map]
      rintro ⟨c, _, h⟩
      cases h
    have hp_path : ((q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).concat hadj_t₁.symm).IsPath :=
      hp₁_path.concat hnone_notMem hadj_t₁.symm
    have hv := hp _ hp_path
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv₁ | rfl
    · rw [Walk.support_map, List.mem_map] at hv₁
      obtain ⟨c, hc, rfl⟩ := hv₁
      have hsub₁ : χ₁ a ∩ χ₁ t₁ ⊆ χ₁ c :=
        hTD₁.inter_subset (onTreePath_of_mem_isPath hTD₁.isTree q₁.2 hc)
      exact (Set.subset_inter Set.inter_subset_left (hinter_t₁ a)).trans hsub₁
    · exact Set.inter_subset_right
  have h_inr_none : ∀ (b : ι₂) (v : Option (ι₁ ⊕ ι₂)),
      OnTreePath (gluedTree T₁ T₂ t₁ t₂) (some (Sum.inr b)) none v →
      χ₂ b ∩ (X ∪ (V₁ ∩ V₂)) ⊆ gluedBag X V₁ V₂ χ₁ χ₂ v := by
    intro b v hp
    let q₂ := (hTD₂.isTree.connected b t₂).some.toPath
    have hp₂_path : (q₂.1.map (inrTreeHom T₁ T₂ t₁ t₂)).IsPath :=
      q₂.2.map (injective_inrTreeHom T₁ T₂ t₁ t₂)
    have hnone_notMem : none ∉ (q₂.1.map (inrTreeHom T₁ T₂ t₁ t₂)).support := by
      rw [Walk.support_map, List.mem_map]
      rintro ⟨c, _, h⟩
      cases h
    have hp_path : ((q₂.1.map (inrTreeHom T₁ T₂ t₁ t₂)).concat hadj_t₂.symm).IsPath :=
      hp₂_path.concat hnone_notMem hadj_t₂.symm
    have hv := hp _ hp_path
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv₂ | rfl
    · rw [Walk.support_map, List.mem_map] at hv₂
      obtain ⟨c, hc, rfl⟩ := hv₂
      have hsub₂ : χ₂ b ∩ χ₂ t₂ ⊆ χ₂ c :=
        hTD₂.inter_subset (onTreePath_of_mem_isPath hTD₂.isTree q₂.2 hc)
      exact (Set.subset_inter Set.inter_subset_left (hinter_t₂ b)).trans hsub₂
    · exact Set.inter_subset_right
  have h_inl_inr : ∀ (a : ι₁) (b : ι₂) (v : Option (ι₁ ⊕ ι₂)),
      OnTreePath (gluedTree T₁ T₂ t₁ t₂) (some (Sum.inl a)) (some (Sum.inr b)) v →
      χ₁ a ∩ χ₂ b ⊆ gluedBag X V₁ V₂ χ₁ χ₂ v := by
    intro a b v hp
    let q₁ := (hTD₁.isTree.connected a t₁).some.toPath
    have hp₁_0_path : (q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).IsPath :=
      q₁.2.map (injective_inlTreeHom T₁ T₂ t₁ t₂)
    have hnone_notMem₁ : none ∉ (q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).support := by
      rw [Walk.support_map, List.mem_map]
      rintro ⟨c, _, h⟩
      cases h
    have hp₁_path : ((q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).concat hadj_t₁.symm).IsPath :=
      hp₁_0_path.concat hnone_notMem₁ hadj_t₁.symm
    let q₂ := (hTD₂.isTree.connected t₂ b).some.toPath
    have hp₂_0_path : (q₂.1.map (inrTreeHom T₁ T₂ t₁ t₂)).IsPath :=
      q₂.2.map (injective_inrTreeHom T₁ T₂ t₁ t₂)
    have hp_path : (((q₁.1.map (inlTreeHom T₁ T₂ t₁ t₂)).concat hadj_t₁.symm).append
        (Walk.cons hadj_t₂ (q₂.1.map (inrTreeHom T₁ T₂ t₁ t₂)))).IsPath := by
      rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons,
        List.nodup_append]
      refine ⟨hp₁_path.support_nodup, hp₂_0_path.support_nodup, ?_⟩
      intro x hx₁ y hx₂ hxy
      subst hxy
      rw [Walk.support_map, List.mem_map] at hx₂
      obtain ⟨c₂, _, rfl⟩ := hx₂
      rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx₁
      rcases hx₁ with hx₁ | h
      · rw [Walk.support_map, List.mem_map] at hx₁
        obtain ⟨c₁, _, h⟩ := hx₁
        cases Option.some.inj h
      · cases h
    have hv := hp _ hp_path
    rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append] at hv
    rcases hv with hv₁ | hv₂
    · rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hv₁
      rcases hv₁ with hv₁ | rfl
      · rw [Walk.support_map, List.mem_map] at hv₁
        obtain ⟨c, hc, rfl⟩ := hv₁
        have hsub₁ : χ₁ a ∩ χ₁ t₁ ⊆ χ₁ c :=
          hTD₁.inter_subset (onTreePath_of_mem_isPath hTD₁.isTree q₁.2 hc)
        have hsub_t₁ : χ₁ a ∩ χ₂ b ⊆ χ₁ a ∩ χ₁ t₁ :=
          Set.subset_inter Set.inter_subset_left
            ((hinter_12 a b).trans (Set.subset_union_right.trans hX₁))
        exact hsub_t₁.trans hsub₁
      · exact (hinter_12 a b).trans Set.subset_union_right
    · rw [Walk.support_map, List.mem_map] at hv₂
      obtain ⟨c, hc, rfl⟩ := hv₂
      have hsub₂ : χ₂ t₂ ∩ χ₂ b ⊆ χ₂ c :=
        hTD₂.inter_subset (onTreePath_of_mem_isPath hTD₂.isTree q₂.2 hc)
      have hsub_t₂ : χ₁ a ∩ χ₂ b ⊆ χ₂ t₂ ∩ χ₂ b :=
        Set.subset_inter ((hinter_12 a b).trans (Set.subset_union_right.trans hX₂))
          Set.inter_subset_right
      exact hsub_t₂.trans hsub₂
  refine {
    isTree := isTree_gluedTree hTD₁.isTree hTD₂.isTree
    iUnion_eq := ?_
    adj_mem := ?_
    inter_subset := ?_
  }
  · apply Set.Subset.antisymm
    · refine Set.iUnion_subset (fun t ↦ ?_)
      cases t with
      | none =>
        exact Set.union_subset hX (Set.inter_subset_left.trans hsep.subset_left)
      | some s =>
        cases s with
        | inl a => exact (hχ₁_sub a).trans hsep.subset_left
        | inr b => exact (hχ₂_sub b).trans hsep.subset_right
    · intro x hx
      rw [← hsep.union_eq] at hx
      rcases hx with hx₁ | hx₂
      · have hx₁' : x ∈ ⋃ a : ι₁, χ₁ a := by
          rw [hTD₁.iUnion_eq, Subgraph.induce_verts]
          exact hx₁
        obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hx₁'
        exact Set.mem_iUnion.2 ⟨some (Sum.inl a), ha⟩
      · have hx₂' : x ∈ ⋃ b : ι₂, χ₂ b := by
          rw [hTD₂.iUnion_eq, Subgraph.induce_verts]
          exact hx₂
        obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hx₂'
        exact Set.mem_iUnion.2 ⟨some (Sum.inr b), hb⟩
  · intro u v hadj
    have hu : u ∈ V₁ ∪ V₂ := hsep.union_eq.symm ▸ hadj.fst_mem
    have hv : v ∈ V₁ ∪ V₂ := hsep.union_eq.symm ▸ hadj.snd_mem
    by_cases hu₁ : u ∈ V₁ <;> by_cases hv₁ : v ∈ V₁
    · obtain ⟨a, ha⟩ := hTD₁.adj_mem ⟨hu₁, hv₁, hadj⟩
      exact ⟨some (Sum.inl a), ha⟩
    · have hv₂ : v ∈ V₂ := hv.resolve_left hv₁
      have hu₂ : u ∈ V₂ := by
        by_contra hu₂
        exact hsep.not_adj ⟨hu₁, hu₂⟩ ⟨hv₂, hv₁⟩ hadj
      obtain ⟨b, hb⟩ := hTD₂.adj_mem ⟨hu₂, hv₂, hadj⟩
      exact ⟨some (Sum.inr b), hb⟩
    · have hu₂ : u ∈ V₂ := hu.resolve_left hu₁
      have hv₂ : v ∈ V₂ := by
        by_contra hv₂
        exact hsep.not_adj ⟨hv₁, hv₂⟩ ⟨hu₂, hu₁⟩ hadj.symm
      obtain ⟨b, hb⟩ := hTD₂.adj_mem ⟨hu₂, hv₂, hadj⟩
      exact ⟨some (Sum.inr b), hb⟩
    · have hu₂ : u ∈ V₂ := hu.resolve_left hu₁
      have hv₂ : v ∈ V₂ := hv.resolve_left hv₁
      obtain ⟨b, hb⟩ := hTD₂.adj_mem ⟨hu₂, hv₂, hadj⟩
      exact ⟨some (Sum.inr b), hb⟩
  · intro u v w hp
    cases u with
    | none =>
      cases w with
      | none =>
        have hv := hp Walk.nil Walk.IsPath.nil
        simp only [Walk.support_nil, List.mem_singleton] at hv
        subst hv
        exact Set.inter_subset_left
      | some s₂ =>
        cases s₂ with
        | inl a₂ =>
          rw [Set.inter_comm]
          exact h_inl_none a₂ v (onTreePath_symm hp)
        | inr b₂ =>
          rw [Set.inter_comm]
          exact h_inr_none b₂ v (onTreePath_symm hp)
    | some s₁ =>
      cases s₁ with
      | inl a₁ =>
        cases w with
        | none => exact h_inl_none a₁ v hp
        | some s₂ =>
          cases s₂ with
          | inl a₂ => exact h_inl_inl a₁ a₂ v hp
          | inr b₂ => exact h_inl_inr a₁ b₂ v hp
      | inr b₁ =>
        cases w with
        | none => exact h_inr_none b₁ v hp
        | some s₂ =>
          cases s₂ with
          | inl a₂ =>
            rw [Set.inter_comm]
            exact h_inl_inr a₂ b₁ v (onTreePath_symm hp)
          | inr b₂ => exact h_inr_inr b₁ b₂ v hp

private lemma widthLE_gluedBag {X V₁ V₂ : Set V} {χ₁ : ι₁ → Set V} {χ₂ : ι₂ → Set V} {w : ℕ}
    (hw₀ : (X ∪ (V₁ ∩ V₂)).ncard ≤ w + 1) (hw₁ : WidthLE χ₁ w) (hw₂ : WidthLE χ₂ w) :
    WidthLE (gluedBag X V₁ V₂ χ₁ χ₂) w := by
  intro t
  cases t with
  | none => exact hw₀
  | some s =>
    cases s with
    | inl a => exact hw₁ a
    | inr b => exact hw₂ b

private lemma isTreeDecomposition_bot_unit (G : (⊤ : SimpleGraph V).Subgraph) :
    IsTreeDecomposition G (⊥ : SimpleGraph Unit) (fun _ ↦ G.verts) where
  isTree := IsTree.of_subsingleton
  iUnion_eq := Set.iUnion_const G.verts
  adj_mem _ _ hadj := ⟨(), hadj.fst_mem, hadj.snd_mem⟩
  inter_subset _ _ _ _ := Set.inter_subset_left

/-! ## Proof of Theorem (7.3) -/

private lemma sdiff_inter_le_of_mul_le {θ s : ℕ} (h3 : 3 ≤ θ₈ θ)
    (hmul : θ₈ θ * s ≤ (θ₈ θ - 1) * (θ₇ θ * θ₈ θ + 1)) :
    s ≤ (θ₈ θ - 1) * θ₇ θ := by
  by_contra! hlt
  have h1 : (θ₈ θ - 1) * θ₇ θ + 1 ≤ s := hlt
  have h2 : θ₈ θ * ((θ₈ θ - 1) * θ₇ θ + 1) ≤ θ₈ θ * s := Nat.mul_le_mul_left (θ₈ θ) h1
  have h3' : (θ₈ θ - 1) * (θ₇ θ * θ₈ θ + 1) < θ₈ θ * ((θ₈ θ - 1) * θ₇ θ + 1) := by
    calc (θ₈ θ - 1) * (θ₇ θ * θ₈ θ + 1)
        = (θ₈ θ - 1) * (θ₇ θ * θ₈ θ) + (θ₈ θ - 1) := Nat.mul_add_one _ _
      _ = θ₈ θ * ((θ₈ θ - 1) * θ₇ θ) + (θ₈ θ - 1) := by
        rw [Nat.mul_comm (θ₇ θ) (θ₈ θ), ← Nat.mul_assoc, Nat.mul_comm (θ₈ θ - 1) (θ₈ θ),
          Nat.mul_assoc]
      _ < θ₈ θ * ((θ₈ θ - 1) * θ₇ θ) + θ₈ θ := by omega
      _ = θ₈ θ * ((θ₈ θ - 1) * θ₇ θ + 1) := (Nat.mul_add_one _ _).symm
  omega

/-- Inductive form of Graph Minors V, (7.3) (pages 108–109):
"We show, by induction on $|V(G)|$, that if $G \in \mathcal{F}_\theta$ and $X \subseteq V(G)$
and $|X| \le \theta_7 \theta_8 + 1$, then $G$ has a tree-decomposition $(T, (X_t : t \in
V(T)))$ of width $\le \theta_9$, such that $X \subseteq X_t$, for some $t \in V(T)$." -/
private lemma theorem_7_3_ind
    {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    ∀ (n : ℕ) (G : (⊤ : SimpleGraph V).Subgraph),
      G.verts.Finite → G ∈ 𝓕 θ → G.verts.ncard = n →
      ∀ (X : Set V), X ⊆ G.verts → X.ncard ≤ θ₇ θ * θ₈ θ + 1 →
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (χ : ι → Set V) (t₀ : ι),
        IsTreeDecomposition G T χ ∧ WidthLE χ (θ₉ θ) ∧ X ⊆ χ t₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hG_fin hG hG_card X hX_sub hX_le
    have hθ₉_eq : θ₉ θ = θ₇ θ * θ₈ θ + θ₇ θ + 1 := by
      unfold θ₉
      rw [Nat.mul_add_one, Nat.add_assoc]
    by_cases hbase : G.verts.ncard ≤ θ₉ θ + 1
    · refine ⟨Unit, inferInstance, ⊥, fun _ ↦ G.verts, (),
        isTreeDecomposition_bot_unit G, fun _ ↦ hbase, hX_sub⟩
    · push Not at hbase
      have h3_le_θ₈ : 3 ≤ θ₈ θ := three_le_θ₈ hθ heven
      have htarget_le : θ₇ θ * θ₈ θ + 1 ≤ G.verts.ncard := by omega
      obtain ⟨X', hXX', hX'_sub, hX'_card⟩ :=
        Set.exists_subsuperset_card_eq hX_sub hX_le htarget_le
      obtain ⟨V₁, V₂, hsep, hinter_le, hdiff₁, hdiff₂⟩ :=
        theorem_7_2_simple hθ heven hG_fin hG hX'_sub
      rw [hX'_card] at hdiff₁ hdiff₂
      have hs₁ : ((V₁ \ V₂) ∩ X').ncard ≤ (θ₈ θ - 1) * θ₇ θ :=
        sdiff_inter_le_of_mul_le h3_le_θ₈ hdiff₁
      have hs₂ : ((V₂ \ V₁) ∩ X').ncard ≤ (θ₈ θ - 1) * θ₇ θ :=
        sdiff_inter_le_of_mul_le h3_le_θ₈ hdiff₂
      let X₁ : Set V := ((V₁ \ V₂) ∩ X') ∪ (V₁ ∩ V₂)
      let X₂ : Set V := ((V₂ \ V₁) ∩ X') ∪ (V₁ ∩ V₂)
      have hX₁_sub : X₁ ⊆ V₁ :=
        Set.union_subset (Set.inter_subset_left.trans Set.sdiff_subset) Set.inter_subset_left
      have hX₂_sub : X₂ ⊆ V₂ :=
        Set.union_subset (Set.inter_subset_left.trans Set.sdiff_subset) Set.inter_subset_right
      have hθ₈_mul : (θ₈ θ - 1) * θ₇ θ + θ₇ θ = θ₇ θ * θ₈ θ := by
        calc (θ₈ θ - 1) * θ₇ θ + θ₇ θ
            = (θ₈ θ - 1) * θ₇ θ + 1 * θ₇ θ := by rw [one_mul]
          _ = (θ₈ θ - 1 + 1) * θ₇ θ := (Nat.add_mul _ _ _).symm
          _ = θ₈ θ * θ₇ θ := by rw [Nat.sub_add_cancel (by omega)]
          _ = θ₇ θ * θ₈ θ := Nat.mul_comm _ _
      have hX₁_card : X₁.ncard ≤ θ₇ θ * θ₈ θ := by
        calc X₁.ncard
            ≤ ((V₁ \ V₂) ∩ X').ncard + (V₁ ∩ V₂).ncard := Set.ncard_union_le _ _
          _ ≤ (θ₈ θ - 1) * θ₇ θ + θ₇ θ := Nat.add_le_add hs₁ hinter_le
          _ = θ₇ θ * θ₈ θ := hθ₈_mul
      have hX₂_card : X₂.ncard ≤ θ₇ θ * θ₈ θ := by
        calc X₂.ncard
            ≤ ((V₂ \ V₁) ∩ X').ncard + (V₁ ∩ V₂).ncard := Set.ncard_union_le _ _
          _ ≤ (θ₈ θ - 1) * θ₇ θ + θ₇ θ := Nat.add_le_add hs₂ hinter_le
          _ = θ₇ θ * θ₈ θ := hθ₈_mul
      have hV₁_lt : V₁.ncard < G.verts.ncard := by
        refine Set.ncard_lt_ncard ⟨hsep.subset_left, fun hG_sub_V₁ ↦ ?_⟩ hG_fin
        have hX'_sub_X₁ : X' ⊆ X₁ := by
          intro x hx'
          have hxV₁ : x ∈ V₁ := hG_sub_V₁ (hX'_sub hx')
          by_cases hxV₂ : x ∈ V₂
          · exact Or.inr ⟨hxV₁, hxV₂⟩
          · exact Or.inl ⟨⟨hxV₁, hxV₂⟩, hx'⟩
        have hle := Set.ncard_le_ncard hX'_sub_X₁ ((hG_fin.subset hsep.subset_left).subset hX₁_sub)
        omega
      have hV₂_lt : V₂.ncard < G.verts.ncard := by
        refine Set.ncard_lt_ncard ⟨hsep.subset_right, fun hG_sub_V₂ ↦ ?_⟩ hG_fin
        have hX'_sub_X₂ : X' ⊆ X₂ := by
          intro x hx'
          have hxV₂ : x ∈ V₂ := hG_sub_V₂ (hX'_sub hx')
          by_cases hxV₁ : x ∈ V₁
          · exact Or.inr ⟨hxV₁, hxV₂⟩
          · exact Or.inl ⟨⟨hxV₂, hxV₁⟩, hx'⟩
        have hle := Set.ncard_le_ncard hX'_sub_X₂ ((hG_fin.subset hsep.subset_right).subset hX₂_sub)
        omega
      let G₁ := G.induce V₁
      let G₂ := G.induce V₂
      have hG₁_verts : G₁.verts = V₁ := Subgraph.induce_verts G V₁
      have hG₂_verts : G₂.verts = V₂ := Subgraph.induce_verts G V₂
      have hG₁_fin : G₁.verts.Finite := hG₁_verts ▸ hG_fin.subset hsep.subset_left
      have hG₂_fin : G₂.verts.Finite := hG₂_verts ▸ hG_fin.subset hsep.subset_right
      have hG₁_mem : G₁ ∈ 𝓕 θ :=
        mem_𝓕_of_le ⟨hsep.subset_left, fun _ _ h ↦ h.2.2⟩ hG
      have hG₂_mem : G₂ ∈ 𝓕 θ :=
        mem_𝓕_of_le ⟨hsep.subset_right, fun _ _ h ↦ h.2.2⟩ hG
      obtain ⟨ι₁, hfin₁, T₁, χ₁, t₁, hTD₁, hw₁, hX₁_t₁⟩ :=
        ih V₁.ncard (hG_card ▸ hV₁_lt) G₁ hG₁_fin hG₁_mem (congrArg Set.ncard hG₁_verts)
          X₁ (hG₁_verts ▸ hX₁_sub) (by omega)
      obtain ⟨ι₂, hfin₂, T₂, χ₂, t₂, hTD₂, hw₂, hX₂_t₂⟩ :=
        ih V₂.ncard (hG_card ▸ hV₂_lt) G₂ hG₂_fin hG₂_mem (congrArg Set.ncard hG₂_verts)
          X₂ (hG₂_verts ▸ hX₂_sub) (by omega)
      have hw₀ : (X' ∪ (V₁ ∩ V₂)).ncard ≤ θ₉ θ + 1 := by
        calc (X' ∪ (V₁ ∩ V₂)).ncard
            ≤ X'.ncard + (V₁ ∩ V₂).ncard := Set.ncard_union_le _ _
          _ ≤ (θ₇ θ * θ₈ θ + 1) + θ₇ θ := by omega
          _ ≤ θ₉ θ + 1 := by omega
      refine ⟨Option (ι₁ ⊕ ι₂), inferInstance, gluedTree T₁ T₂ t₁ t₂,
        gluedBag X' V₁ V₂ χ₁ χ₂, none,
        isTreeDecomposition_gluedTree hsep hX'_sub hTD₁ hTD₂ hX₁_t₁ hX₂_t₂,
        widthLE_gluedBag hw₀ hw₁ hw₂,
        hXX'.trans Set.subset_union_left⟩

/-- Graph Minors V, (7.3) (page 108):
"If $G \in \mathcal{F}_\theta$ then $G$ has tree-width at most $\theta_9$." -/
theorem theorem_7_3_simple
    {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    TreeWidthLE G (θ₉ θ) := by
  obtain ⟨ι, hfin, T, χ, _, hTD, hw, _⟩ :=
    theorem_7_3_ind hθ heven G.verts.ncard G hG_fin hG rfl ∅
      (Set.empty_subset _) (by simp)
  exact ⟨ι, hfin, T, χ, hTD, hw⟩

/-- Graph Minors V, (7.3) (page 108), expressed using `treeWidth G ≤ θ₉ θ`. -/
theorem theorem_7_3_treeWidth
    {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    treeWidth G ≤ θ₉ θ :=
  Nat.sInf_le (theorem_7_3_simple hθ heven hG_fin hG)

/-- Combining the reduction in Graph Minors V, Section 2 (page 95, `mem_𝓕_of_not_isIsoMinor`) with
Theorem (7.3) (page 108): if `H` is isomorphic to a minor of the `θ`-grid (for even `θ ≥ 6`) and a
finite graph `G` has no minor isomorphic to `H`, then `G` has tree-width at most `θ₉(θ)`. -/
theorem treeWidthLE_of_not_isIsoMinor {α' β' : Type*}
    {H : Graph α' β'} {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite)
    (hG_no_H : ¬ IsIsoMinor H (toGraph G)) (hH_grid : IsIsoMinor H (gridGraph θ)) :
    TreeWidthLE G (θ₉ θ) :=
  theorem_7_3_simple hθ heven hG_fin (mem_𝓕_of_not_isIsoMinor hG_no_H hH_grid)

/-- Combining the reduction in Graph Minors V, Section 2 (page 95, `mem_𝓕_of_not_isIsoMinor`) with
Theorem (7.3) (page 108), expressed using `treeWidth G ≤ θ₉ θ`. -/
theorem treeWidth_le_of_not_isIsoMinor {α' β' : Type*}
    {H : Graph α' β'} {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite)
    (hG_no_H : ¬ IsIsoMinor H (toGraph G)) (hH_grid : IsIsoMinor H (gridGraph θ)) :
    treeWidth G ≤ θ₉ θ :=
  Nat.sInf_le (treeWidthLE_of_not_isIsoMinor hθ heven hG_fin hG_no_H hH_grid)

end

end GraphMinor.GM05
