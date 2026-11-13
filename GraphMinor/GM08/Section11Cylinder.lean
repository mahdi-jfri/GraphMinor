module

public import GraphMinor.GM03.Section3

/-!
# Contracting a sleeve onto the cylinder

Graph Minors VIII proves (11.1) (page 273) from a strengthening of Graph Minors III, (3.8)
(`GM03.theorem_3_8_strong`), "by applying it to each $G_i$ in turn". The strengthened (3.8) is about
a graph `H` glued to the `r × s` cylinder along its central circle. In a truncation, the inside of
each O-arc is a sleeve, not a cylinder. So we contract the sleeve onto the cylinder and keep the
vertices of `H` fixed.

Here we do the graph part of this. Let `G` be a graph, `H` the graph induced on `W ⊆ V(G)`, and
let `Z p` (`p` a vertex of the cylinder) be pairwise disjoint connected vertex sets of `G` with
`Z (i, s - 1)` meeting `W` in `v i` and no other `Z p` meeting `W`. Suppose that, for every edge of
the cylinder between two distinct vertices `p, q`, there is an edge of `G` between `Z p` and `Z q`.
Then `H` glued to the cylinder (`glueGraph`) is a minor of `G`, so a tree-decomposition of `G`
passes to it (`GM03.isTreeDecomposition_of_connected_subgraphs`), and the strengthened (3.8)
gives the decomposition of `H` (`exists_decomposition_of_cylinder_model`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Graph GM03 GM06

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}

/-- The edges of `H` glued to the `r × s` cylinder: the edges of `H` and those of the cylinder. -/
abbrev GlueEdge (β : Type v) (r s : ℕ) : Type v := β ⊕ ((Fin r × Fin s) ⊕ (Fin r × Fin s))

/-- The links of `H` glued to the cylinder, where the cylinder vertex `p` is put at `c p`. -/
@[expose] def glueLink (H : Graph α β) {r s : ℕ} (c : Fin r × Fin s → α) :
    GlueEdge β r s → α → α → Prop
  | .inl f, x, y => H.IsLink f x y
  | .inr f, x, y => ∃ p q, (cylinderGraph r s).IsLink f p q ∧ x = c p ∧ y = c q

theorem glueLink_symm (H : Graph α β) {r s : ℕ} (c : Fin r × Fin s → α) {e : GlueEdge β r s}
    {x y : α} (h : glueLink H c e x y) : glueLink H c e y x := by
  cases e with
  | inl f => exact H.isLink_comm.mp h
  | inr f =>
    obtain ⟨p, q, hl, rfl, rfl⟩ := h
    exact ⟨q, p, (cylinderGraph r s).isLink_comm.mp hl, rfl, rfl⟩

theorem glueLink_eq (H : Graph α β) {r s : ℕ} (c : Fin r × Fin s → α) {e : GlueEdge β r s}
    {x y x' y' : α} (h : glueLink H c e x y) (h' : glueLink H c e x' y') : x = x' ∨ x = y' := by
  cases e with
  | inl f => exact H.eq_or_eq_of_isLink_of_isLink h h'
  | inr f =>
    obtain ⟨p, q, hl, rfl, rfl⟩ := h
    obtain ⟨p', q', hl', rfl, rfl⟩ := h'
    rcases (cylinderGraph r s).eq_or_eq_of_isLink_of_isLink hl hl' with h | h
    · exact Or.inl (congrArg c h)
    · exact Or.inr (congrArg c h)

/-- `H` glued to the cylinder: the vertices of `H` and the points `c p`, with the edges of `H` and
those of the cylinder. -/
@[expose] def glueGraph (H : Graph α β) {r s : ℕ} (c : Fin r × Fin s → α) :
    Graph α (GlueEdge β r s) where
  vertexSet := V(H) ∪ range c
  IsLink := glueLink H c
  isLink_symm _ _ := ⟨fun _ _ h => glueLink_symm H c h⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := glueLink_eq H c h h'
  left_mem_of_isLink e x y h := by
    cases e with
    | inl f => exact Or.inl h.left_mem
    | inr f =>
      obtain ⟨p, q, -, rfl, -⟩ := h
      exact Or.inr ⟨p, rfl⟩

/-- The copy of `H` in `glueGraph H c`. -/
@[expose] def glueLeft (H : Graph α β) (r s : ℕ) : Graph α (GlueEdge β r s) where
  vertexSet := V(H)
  IsLink e x y := ∃ f, e = .inl f ∧ H.IsLink f x y
  isLink_symm _ _ := ⟨fun _ _ ⟨f, hf, h⟩ => ⟨f, hf, h.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := by
    obtain ⟨f, rfl, h⟩ := h
    obtain ⟨f', hf', h'⟩ := h'
    cases hf'
    exact H.eq_or_eq_of_isLink_of_isLink h h'
  left_mem_of_isLink _ _ _ h := by
    obtain ⟨f, -, h⟩ := h
    exact h.left_mem

/-- The copy of the cylinder in `glueGraph H c`. -/
@[expose] def glueRight {r s : ℕ} (c : Fin r × Fin s → α) : Graph α (GlueEdge β r s) where
  vertexSet := range c
  IsLink e x y := ∃ f p q, e = .inr f ∧ (cylinderGraph r s).IsLink f p q ∧ x = c p ∧ y = c q
  isLink_symm _ _ := ⟨fun _ _ ⟨f, p, q, hf, h, hx, hy⟩ =>
    ⟨f, q, p, hf, (cylinderGraph r s).isLink_comm.mp h, hy, hx⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := by
    obtain ⟨f, p, q, rfl, hl, rfl, rfl⟩ := h
    obtain ⟨f', p', q', hf', hl', rfl, rfl⟩ := h'
    cases hf'
    rcases (cylinderGraph r s).eq_or_eq_of_isLink_of_isLink hl hl' with h | h
    · exact Or.inl (congrArg c h)
    · exact Or.inr (congrArg c h)
  left_mem_of_isLink _ _ _ h := by
    obtain ⟨f, p, q, -, -, rfl, -⟩ := h
    exact ⟨p, rfl⟩

variable {H : Graph α β} {r s : ℕ} {c : Fin r × Fin s → α}

theorem glueLeft_le : glueLeft H r s ≤ glueGraph H c :=
  ⟨subset_union_left, fun e x y ⟨f, hf, h⟩ => by subst hf; exact h⟩

theorem glueRight_le : glueRight (β := β) c ≤ glueGraph H c :=
  ⟨subset_union_right, fun e x y ⟨f, p, q, hf, h, hx, hy⟩ => by subst hf; exact ⟨p, q, h, hx, hy⟩⟩

theorem isGraphSeparation_glue :
    IsGraphSeparation (glueGraph H c) (glueLeft H r s) (glueRight c) := by
  refine ⟨glueLeft_le, glueRight_le, rfl, ?_, ?_⟩
  · ext e
    constructor
    · rintro (he | he)
      · exact glueLeft_le.edgeSet_mono he
      · exact glueRight_le.edgeSet_mono he
    · intro he
      obtain ⟨x, y, h⟩ := (glueGraph H c).exists_isLink_of_mem_edgeSet he
      cases e with
      | inl f => exact Or.inl ⟨x, y, f, rfl, h⟩
      | inr f =>
        obtain ⟨p, q, hl, hx, hy⟩ := h
        exact Or.inr ⟨x, y, f, p, q, rfl, hl, hx, hy⟩
  · refine Set.disjoint_left.mpr fun e he he' => ?_
    obtain ⟨x, y, f, rfl, -⟩ := he
    obtain ⟨x', y', f', p, q, hf, -⟩ := he'
    cases hf

/-- `H` is isomorphic to its copy in `glueGraph H c`; the vertex map is the identity. -/
@[expose] noncomputable def isoGlueLeft (H : Graph α β) (r s : ℕ) : Iso H (glueLeft H r s) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.ofBijective (fun e => ⟨.inl e.1, by
      obtain ⟨x, y, h⟩ := H.exists_isLink_of_mem_edgeSet e.2
      exact ⟨x, y, e.1, rfl, h⟩⟩)
    ⟨fun _ _ h => Subtype.ext (Sum.inl.inj (congrArg Subtype.val h)),
      fun ⟨e, x, y, f, hf, h⟩ => ⟨⟨f, h.edge_mem⟩, Subtype.ext hf.symm⟩⟩
  isLink_iff e x y := by
    constructor
    · intro h
      exact ⟨e.1, rfl, h⟩
    · rintro ⟨f, hf, h⟩
      cases hf
      exact h

theorem isoGlueLeft_vertex (H : Graph α β) (r s : ℕ) (x : V(H)) :
    ((isoGlueLeft H r s).vertexEquiv x).1 = x.1 := rfl

/-- The edge of `glueRight c` that is a copy of an edge of the cylinder. -/
@[expose] def glueRightEdge (c : Fin r × Fin s → α) (e : E(cylinderGraph r s)) :
    E(glueRight (β := β) c) :=
  ⟨.inr e.1, by
    obtain ⟨p, q, h⟩ := (cylinderGraph r s).exists_isLink_of_mem_edgeSet e.2
    exact ⟨c p, c q, e.1, p, q, rfl, h, rfl, rfl⟩⟩

theorem glueRightEdge_bijective (c : Fin r × Fin s → α) :
    Function.Bijective (glueRightEdge (β := β) c) := by
  refine ⟨fun e e' h => Subtype.ext (Sum.inr.inj (congrArg Subtype.val h)), ?_⟩
  rintro ⟨e, x, y, f, p, q, hf, h, -⟩
  exact ⟨⟨f, h.edge_mem⟩, Subtype.ext hf.symm⟩

/-- The vertex of `glueRight c` that is a copy of a vertex of the cylinder. -/
@[expose] def glueRightVertex (c : Fin r × Fin s → α) (p : V(cylinderGraph r s)) :
    V(glueRight (β := β) c) :=
  ⟨c p.1, p.1, rfl⟩

theorem glueRightVertex_bijective {c : Fin r × Fin s → α} (hc : Function.Injective c) :
    Function.Bijective (glueRightVertex (β := β) c) := by
  refine ⟨fun p q h => Subtype.ext (hc (congrArg Subtype.val h)), ?_⟩
  rintro ⟨_, p, rfl⟩
  exact ⟨⟨p, mem_univ p⟩, rfl⟩

/-- The cylinder is isomorphic to its copy in `glueGraph H c` when `c` is injective. -/
@[expose] noncomputable def isoGlueRight {c : Fin r × Fin s → α} (hc : Function.Injective c) :
    Iso (cylinderGraph r s) (glueRight (β := β) c) where
  vertexEquiv := Equiv.ofBijective _ (glueRightVertex_bijective hc)
  edgeEquiv := Equiv.ofBijective _ (glueRightEdge_bijective c)
  isLink_iff e x y := by
    simp only [Equiv.ofBijective_apply, glueRightVertex, glueRightEdge]
    constructor
    · intro h
      exact ⟨e.1, x.1, y.1, rfl, h, rfl, rfl⟩
    · rintro ⟨f, p, q, hf, h, hx, hy⟩
      cases hf
      rw [hc hx, hc hy]
      exact h

theorem isoGlueRight_vertex {c : Fin r × Fin s → α} (hc : Function.Injective c)
    (p : V(cylinderGraph r s)) : ((isoGlueRight (β := β) hc).vertexEquiv p).1 = c p.1 := rfl

/-- The graph part of the proof of Graph Minors VIII, (11.1) (page 273). Let `H` be the graph
induced on `W ⊆ V(G)`. Let `Z p`, for `p` a vertex of the `r × s` cylinder, be pairwise disjoint
connected vertex sets of `G` such that `Z (i, s - 1)` meets `W` only in `v i` and no other `Z p`
meets `W`, and such that for every edge of the cylinder between distinct `p, q` some edge of `G`
joins `Z p` and `Z q`. Then a tree-decomposition `(T, Y)` of `G` gives a tree-decomposition
`(T, X)` of `H` of no larger width, with `Y_t ∩ W ⊆ X_t` for every `t` and
`{v_1, …, v_r} ⊆ X_{t_0}` for some `t_0`. This is the strengthened III (3.8), applied to `H` glued
to the cylinder, which is a minor of `G`. -/
theorem exists_decomposition_of_cylinder_model {G : Graph α β} (hVG : V(G).Finite) [Fintype ι]
    {T : SimpleGraph ι} {Y : ι → Set α} (hTD : IsTreeDecomposition G T Y) {W : Set α}
    (hW : W ⊆ V(G)) (hs : 0 < s) (hrs : r ≤ 2 * s) (Z : Fin r × Fin s → Set α)
    (hZG : ∀ p, Z p ⊆ V(G)) (hZconn : ∀ p, IsGraphConnected (G.induce (Z p)))
    (hZdisj : Pairwise fun p q => Disjoint (Z p) (Z q)) (v : Fin r → α)
    (hvZ : ∀ i, v i ∈ Z (i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)) (hvW : ∀ i, v i ∈ W)
    (hZW : ∀ p, ∀ x ∈ Z p, x ∈ W → p.2.1 = s - 1 ∧ x = v p.1)
    (hZedge : ∀ e p q, (cylinderGraph r s).IsLink e p q → p ≠ q →
      ∃ x ∈ Z p, ∃ y ∈ Z q, ∃ f, G.IsLink f x y) :
    ∃ X : ι → Set α, IsTreeDecomposition (G.induce W) T X ∧
      (∀ w : ℕ, TreeDecompHasWidthLE Y w → TreeDecompHasWidthLE X w) ∧
      (∀ t, Y t ∩ W ⊆ X t) ∧ ∃ t₀, range v ⊆ X t₀ := by
  classical
  set last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ with hlast
  -- The cylinder vertex `p` is put at `c p`: at `v i` on the central circle, and at some vertex
  -- of `Z p` otherwise.
  let c : Fin r × Fin s → α := fun p => if p.2.1 = s - 1 then v p.1 else (hZconn p).1.some
  have hcZ : ∀ p, c p ∈ Z p := by
    intro p
    by_cases h : p.2.1 = s - 1
    · have hp : p = (p.1, last) := Prod.ext rfl (Fin.ext h)
      simp only [c, h, ite_true]
      rw [hp]
      exact hvZ p.1
    · simp only [c, h, ite_false]
      exact (hZconn p).1.some_mem
  have hc_inj : Function.Injective c := by
    intro p q h
    by_contra hne
    exact Set.disjoint_left.mp (hZdisj hne) (hcZ p) (h ▸ hcZ q)
  have hc_last : ∀ i, c (i, last) = v i := fun i => by simp [c, hlast]
  -- The vertices of `G` glued from `H` and the cylinder.
  set H := G.induce W with hH
  set G' := glueGraph H c with hG'
  -- The vertex `u` of `G'` is contracted from `Z' u`.
  let Z' : α → Graph α β := fun u => if h : ∃ p, c p = u then G.induce (Z h.choose) else
    G.induce {u}
  have hZ'c : ∀ p, Z' (c p) = G.induce (Z p) := by
    intro p
    have h : ∃ q, c q = c p := ⟨p, rfl⟩
    simp only [Z']
    rw [dite_eq_left h]
    rw [hc_inj h.choose_spec]
  have hZ'n : ∀ u, (¬ ∃ p, c p = u) → Z' u = G.induce {u} := fun u h => by
    simp only [Z']
    rw [dite_eq_right h]
  have hmem : ∀ u ∈ V(G'), u ∈ V(Z' u) := by
    intro u hu
    by_cases h : ∃ p, c p = u
    · obtain ⟨p, rfl⟩ := h
      rw [hZ'c]
      exact hcZ p
    · rw [hZ'n u h]
      exact mem_singleton u
  -- A vertex of `W` in some `Z p` is `c p`.
  have hWc : ∀ p, ∀ x ∈ Z p, x ∈ W → x = c p := by
    intro p x hx hxW
    obtain ⟨h1, h2⟩ := hZW p x hx hxW
    have hp : p = (p.1, last) := Prod.ext rfl (Fin.ext h1)
    rw [h2, hp, hc_last]
  have hle : ∀ u ∈ V(G'), Z' u ≤ G := by
    intro u hu
    by_cases h : ∃ p, c p = u
    · obtain ⟨p, rfl⟩ := h
      rw [hZ'c]
      exact induce_le (hZG p)
    · rw [hZ'n u h]
      rcases hu with hu | ⟨p, hp⟩
      · exact induce_le (singleton_subset_iff.mpr (hW hu))
      · exact absurd ⟨p, hp⟩ h
  have hconn : ∀ u ∈ V(G'), IsGraphConnected (Z' u) := by
    intro u hu
    by_cases h : ∃ p, c p = u
    · obtain ⟨p, rfl⟩ := h
      rw [hZ'c]
      exact hZconn p
    · rw [hZ'n u h]
      refine ⟨⟨u, rfl⟩, ?_⟩
      rintro x rfl y rfl
      exact ⟨.nil rfl⟩
  have hdisj : ∀ u₁ ∈ V(G'), ∀ u₂ ∈ V(G'), u₁ ≠ u₂ → Disjoint V(Z' u₁) V(Z' u₂) := by
    -- A vertex `u` of `W` outside the range of `c` is in no `Z p`.
    have hout : ∀ u ∈ V(G'), (¬ ∃ p, c p = u) → ∀ p, u ∉ Z p := by
      intro u hu h p hup
      rcases hu with hu | hu
      · exact h ⟨p, (hWc p u hup hu).symm⟩
      · exact h hu
    intro u₁ hu₁ u₂ hu₂ hne
    by_cases h₁ : ∃ p, c p = u₁ <;> by_cases h₂ : ∃ p, c p = u₂
    · obtain ⟨p₁, rfl⟩ := h₁
      obtain ⟨p₂, rfl⟩ := h₂
      rw [hZ'c, hZ'c]
      exact hZdisj fun h => hne (congrArg c h)
    · obtain ⟨p₁, rfl⟩ := h₁
      rw [hZ'c, hZ'n u₂ h₂]
      exact Set.disjoint_right.mpr fun x hx hxZ => hout u₂ hu₂ h₂ p₁ (hx ▸ hxZ)
    · obtain ⟨p₂, rfl⟩ := h₂
      rw [hZ'c, hZ'n u₁ h₁]
      exact Set.disjoint_left.mpr fun x hx hxZ => hout u₁ hu₁ h₁ p₂ (hx ▸ hxZ)
    · rw [hZ'n u₁ h₁, hZ'n u₂ h₂]
      exact disjoint_singleton.mpr hne
  have hedge : ∀ ⦃e : GlueEdge β r s⦄ ⦃u w : α⦄, G'.IsLink e u w →
      ∃ t : ι, (Y t ∩ V(Z' u)).Nonempty ∧ (Y t ∩ V(Z' w)).Nonempty := by
    intro e u w hl
    cases e with
    | inl f =>
      have hl' : H.IsLink f u w := hl
      obtain ⟨t, hut, hwt⟩ := hTD.edge_in_bag hl'.1
      exact ⟨t, ⟨u, hut, hmem u (Or.inl hl'.2.1)⟩, ⟨w, hwt, hmem w (Or.inl hl'.2.2)⟩⟩
    | inr f =>
      obtain ⟨p, q, hpq, rfl, rfl⟩ := hl
      rw [hZ'c, hZ'c]
      by_cases hne : p = q
      · subst hne
        have hx : c p ∈ V(G) := hZG p (hcZ p)
        rw [← hTD.iUnion_bags, mem_iUnion] at hx
        obtain ⟨t, ht⟩ := hx
        exact ⟨t, ⟨c p, ht, hcZ p⟩, ⟨c p, ht, hcZ p⟩⟩
      · obtain ⟨x, hx, y, hy, f', hf'⟩ := hZedge f p q hpq hne
        obtain ⟨t, hxt, hyt⟩ := hTD.edge_in_bag hf'
        exact ⟨t, ⟨x, hxt, hx⟩, ⟨y, hyt, hy⟩⟩
  obtain ⟨hTD', hw'⟩ := isTreeDecomposition_of_connected_subgraphs hVG hTD Z' hle hconn hdisj hedge
  set Y' : ι → Set α := fun t => {u ∈ V(G') | (Y t ∩ V(Z' u)).Nonempty} with hY'
  have hVG' : V(G').Finite := by
    refine (hVG.subset hW).union (finite_range c)
  -- The width of `(T, Y)`.
  set w₀ : ℕ := (Finset.univ.sup fun t => (Y t).ncard) - 1 with hw₀
  have hYw₀ : TreeDecompHasWidthLE Y w₀ := by
    intro t
    have := Finset.le_sup (f := fun t => (Y t).ncard) (Finset.mem_univ t)
    omega
  have hinter : V(glueLeft H r s) ∩ V(glueRight (β := β) c) =
      range (fun i : Fin r => ((isoGlueLeft H r s).vertexEquiv ⟨v i, hvW i⟩).1) := by
    ext x
    constructor
    · rintro ⟨hxW, p, rfl⟩
      obtain ⟨h1, h2⟩ := hZW p (c p) (hcZ p) hxW
      exact ⟨p.1, h2.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨hvW i, (i, last), hc_last i⟩
  obtain ⟨X, t₀, hX, hXw, hYX, hX₀⟩ :=
    theorem_3_8_strong hVG' s hs hrs v (fun i j h => by
        by_contra hne
        have : (i, last) ≠ (j, last) := fun h' => hne (congrArg Prod.fst h')
        exact Set.disjoint_left.mp (hZdisj this) (hvZ i) (h ▸ hvZ j))
      hvW (isoGlueLeft H r s) (isoGlueRight hc_inj) isGraphSeparation_glue hinter
      (fun i => hc_last i) hTD' (hw' w₀ hYw₀)
  refine ⟨X, hX, fun w hw t => ?_, fun t x ⟨hxY, hxW⟩ => ?_, t₀, hX₀⟩
  · have hsup : (Finset.univ.sup fun t => (Y t).ncard) ≤ w + 1 :=
      Finset.sup_le fun t _ => hw t
    have := hXw t
    omega
  · exact hYX t x hxW ⟨Or.inl hxW, x, hxY, hmem x (Or.inl hxW)⟩

end GM08
end GraphMinor
