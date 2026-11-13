module

public import GraphMinor.GM21.Section6FourSides
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import GraphMinor.GM21.Section6LastLines
import GraphMinor.GM21.Section6DiscSides
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM06.RegionLocal
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Walks

/-!
# Graph Minors XXI, proof of (6.4): the tree of regions

The last step of the proof of (6.4) (page 25 of the preprint): "Let us say that two distinct
regions $r_1, r_2$ of $\Gamma$ in $\Sigma$ *touch* if there is an edge $e$ of $\Gamma$ with
$e \subseteq \bar{r}_1 \cap \bar{r}_2$. It follows that if $r_1, r_2$ touch then
$\bar{r}_1 \cap \bar{r}_2 = U(J)$ for some $\Sigma$-jump $J$, and if they do not touch then
$|\bar{r}_1 \cap \bar{r}_2| \le 1$. In particular, the touching relation defines a graph $T$ with
vertex set the set of regions of $\Gamma$ in $\Sigma$, and it is a tree. ... But $E(T)$ is in 1-1
correspondence with the $\Sigma$-jumps".

`touchGraph Γ` is the graph `T`. Fix the two sides `P J` (inner) and `Q J` (outer) of each jump
`J` (`Section6FourSides`). We say that `ρ₁, ρ₂` lie *across* `J` if they lie on different sides
of `J` and both hold `U(J)` in their closures (`Across`).

* Two regions touch exactly when they lie across some jump (`exists_across_of_touch`,
  `touch_of_across`). An edge `e` in both closures lies in a jump `J`; a region next to `e` holds
  all of `U(J)` in its closure, and on each side of `J` only one region is next to `e`. This is the
  part of "$\bar{r}_1 \cap \bar{r}_2 = U(J)$" that we use.
* The two regions across a jump are unique (`across_eq`), and the regions across another jump
  `J'` lie on the same side of `J`, since an edge of `J'` misses `U(J)`
  (`across_iff_of_ne`).
* So a walk of `T` that does not use the edge across `J` stays on one side of `J`
  (`subset_iff_of_walk`), every edge of `T` is a bridge, and `T` is acyclic
  (`touchGraph_isAcyclic`).
* `T` is connected (`touchGraph_preconnected`). `Σ` without the finitely many vertices of `Γ` is
  connected, and it is covered by the closures of the regions. If the regions reachable from one
  region were not all, their closures and the closures of the other regions would meet at a point
  off `V(Γ)`. That point lies in an edge, which then lies in the closure of a region of each kind,
  so these two regions touch.
* The map that sends a jump to the edge of `T` across it is a bijection
  (`ncard_jumpSet_eq_ncard_edgeSet`): "$E(T)$ is in 1-1 correspondence with the
  $\Sigma$-jumps".
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace RegionTree

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM21.DiscCut

universe u v w

section graph

variable {S : Type w} [TopologicalSpace S]

/-- Two regions *touch* if they are different and some edge of `Γ` lies in both closures. -/
def Touch (Γ : Drawing S) (ρ₁ ρ₂ : Set S) : Prop :=
  ρ₁ ≠ ρ₂ ∧ ∃ e ∈ Γ.E, e ⊆ closure ρ₁ ∧ e ⊆ closure ρ₂

theorem Touch.symm {Γ : Drawing S} {ρ₁ ρ₂ : Set S} (h : Touch Γ ρ₁ ρ₂) : Touch Γ ρ₂ ρ₁ :=
  ⟨h.1.symm, let ⟨e, he, h1, h2⟩ := h.2; ⟨e, he, h2, h1⟩⟩

/-- **The graph `T` of the proof of (6.4)**: its vertices are the regions of `Γ`, and two regions
are adjacent if they touch. -/
def touchGraph (Γ : Drawing S) : SimpleGraph Γ.R where
  Adj ρ₁ ρ₂ := Touch Γ ρ₁.1 ρ₂.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **`T` is connected**, for a proper drawing in a disc. -/
theorem touchGraph_preconnected (hD : GM06.IsClosedDiscSpace S) {Γ : Drawing S}
    (hprop : Γ.IsProper) : (touchGraph Γ).Preconnected := by
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have : ConnectedSpace S := Side.connectedSpace_of_isClosedDiscSpace hD
  have hfin : Finite Γ.R := (GM06.disc_finite_R hD Γ hprop).to_subtype
  intro x y
  by_contra hxy
  set C : Set Γ.R := {ρ | (touchGraph Γ).Reachable x ρ} with hC
  set X : Set S := ⋃ ρ : {ρ : Γ.R // ρ ∈ C}, closure ρ.1.1 with hX
  set Y : Set S := ⋃ ρ : {ρ : Γ.R // ρ ∉ C}, closure ρ.1.1 with hY
  have hXc : IsClosed X := isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hYc : IsClosed Y := isClosed_iUnion_of_finite fun _ => isClosed_closure
  have hconn : IsPreconnected (univ \ Γ.V) :=
    GM06.disc_isPreconnected_sdiff_finite hD isOpen_univ isPreconnected_univ Γ.finite_V
  -- Every point of a region lies off `V(Γ)`.
  have hoff : ∀ ρ : Γ.R, ∀ z ∈ ρ.1, z ∈ univ \ Γ.V := fun ρ z hz =>
    ⟨mem_univ z, fun hzV => GM11.region_subset ρ.2 hz (Γ.V_subset_U hzV)⟩
  have hin : ∀ ρ : Γ.R, ∀ z ∈ closure ρ.1, z ∈ X ∪ Y := by
    intro ρ z hz
    by_cases hρ : ρ ∈ C
    · exact Or.inl (mem_iUnion.2 ⟨⟨ρ, hρ⟩, hz⟩)
    · exact Or.inr (mem_iUnion.2 ⟨⟨ρ, hρ⟩, hz⟩)
  have hcov : univ \ Γ.V ⊆ X ∪ Y := by
    rintro z ⟨-, hzV⟩
    by_cases hzU : z ∈ Γ.U
    · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hzU hzV
      obtain ⟨ρ, hρ, heρ⟩ := GM06.disc_exists_region_incident hD hprop he
      exact hin ⟨ρ, hρ⟩ z (heρ hze)
    · obtain ⟨ρ, hρ, hzρ⟩ := GM11.exists_region_of_notMem hzU
      exact hin ⟨ρ, hρ⟩ z (subset_closure hzρ)
  have hX : ((univ \ Γ.V) ∩ X).Nonempty := by
    obtain ⟨z, hz⟩ := GM11.region_nonempty x.2
    exact ⟨z, hoff x z hz, mem_iUnion.2 ⟨⟨x, SimpleGraph.Reachable.refl x⟩, subset_closure hz⟩⟩
  have hY : ((univ \ Γ.V) ∩ Y).Nonempty := by
    obtain ⟨z, hz⟩ := GM11.region_nonempty y.2
    exact ⟨z, hoff y z hz, mem_iUnion.2 ⟨⟨y, hxy⟩, subset_closure hz⟩⟩
  obtain ⟨z, ⟨-, hzV⟩, hzX, hzY⟩ := isPreconnected_closed_iff.1 hconn X Y hXc hYc hcov hX hY
  obtain ⟨⟨ρ₁, hρ₁⟩, hz₁⟩ := mem_iUnion.1 hzX
  obtain ⟨⟨ρ₂, hρ₂⟩, hz₂⟩ := mem_iUnion.1 hzY
  have hne : ρ₁ ≠ ρ₂ := fun h => hρ₂ (h ▸ hρ₁)
  by_cases hzU : z ∈ Γ.U
  · -- The point lies in an edge, which lies in both closures.
    obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hzU hzV
    have h₁ := GM06.disc_edge_subset_closure_of_incident hD hprop he ρ₁.2 ⟨z, hze, hz₁⟩
    have h₂ := GM06.disc_edge_subset_closure_of_incident hD hprop he ρ₂.2 ⟨z, hze, hz₂⟩
    have hadj : (touchGraph Γ).Adj ρ₁ ρ₂ := ⟨fun h => hne (Subtype.ext h), e, he, h₁, h₂⟩
    exact hρ₂ (SimpleGraph.Reachable.trans hρ₁ hadj.reachable)
  · -- The point lies in a region, which meets both regions.
    obtain ⟨σ, hσ, hzσ⟩ := GM11.exists_region_of_notMem hzU
    have hσo := GM06.isOpen_region hD Γ hσ
    obtain ⟨p₁, hp₁σ, hp₁⟩ := mem_closure_iff.mp hz₁ σ hσo hzσ
    obtain ⟨p₂, hp₂σ, hp₂⟩ := mem_closure_iff.mp hz₂ σ hσo hzσ
    have e₁ := GM11.region_eq_of_mem hσ ρ₁.2 hp₁σ hp₁
    have e₂ := GM11.region_eq_of_mem hσ ρ₂.2 hp₂σ hp₂
    exact hne (Subtype.ext (e₁.symm.trans e₂))

end graph

section jumps

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  (hK : IsLinkage G Γ_sub)
  (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)
  (hD : GM06.IsClosedDiscSpace S) {P Q : Hypergraph α β → Set S}

set_option hygiene false in
local notation "𝒯" => jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))
set_option hygiene false in
local notation "UJ" => LastStep.jumpLine Γ ιE

/-- The regions `ρ₁, ρ₂` lie *across* the jump `J`: on different sides, and both with `U(J)` in
their closures. -/
def Across (Γ : Drawing S) (ιE : Set S → β) (P Q : Hypergraph α β → Set S) (J : Hypergraph α β)
    (ρ₁ ρ₂ : Set S) : Prop :=
  (ρ₁ ⊆ (Q J)ᶜ ∧ ρ₂ ⊆ (P J)ᶜ ∨ ρ₁ ⊆ (P J)ᶜ ∧ ρ₂ ⊆ (Q J)ᶜ) ∧
    LastStep.jumpLine Γ ιE J ⊆ closure ρ₁ ∧ LastStep.jumpLine Γ ιE J ⊆ closure ρ₂

theorem Across.symm {J : Hypergraph α β} {ρ₁ ρ₂ : Set S}
    (h : Across Γ ιE P Q J ρ₁ ρ₂) : Across Γ ιE P Q J ρ₂ ρ₁ :=
  ⟨h.1.elim (fun h' => Or.inr ⟨h'.2, h'.1⟩) (fun h' => Or.inl ⟨h'.2, h'.1⟩), h.2.2, h.2.1⟩

variable (hPQ : ∀ J ∈ 𝒯, Halves (UJ J) (P J) (Q J))

include h_pres hPQ hD

omit hD in
/-- Two regions across a jump touch. -/
theorem touch_of_across {J : Hypergraph α β} (hJ : J ∈ 𝒯) {ρ₁ ρ₂ : Set S} (hρ₁ : ρ₁ ∈ Γ.R)
    (h : Across Γ ιE P Q J ρ₁ ρ₂) : Touch Γ ρ₁ ρ₂ := by
  obtain ⟨e, he, heJ⟩ := exists_edge_of_jump h_pres hJ
  have heU : e ⊆ UJ J := subset_closure.trans (closure_subset_jumpLine he heJ)
  refine ⟨?_, e, he, heU.trans h.2.1, heU.trans h.2.2⟩
  rintro rfl
  rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (hPQ J hJ).region_not_subset_both hρ₁ h1 h2
  · exact (hPQ J hJ).region_not_subset_both hρ₁ h2 h1

omit hK hdeg in
/-- **The regions across a jump are unique.** -/
theorem across_eq {J : Hypergraph α β} (hJ : J ∈ 𝒯) {ρ₁ ρ₂ ρ₃ ρ₄ : Set S} (hρ₁ : ρ₁ ∈ Γ.R)
    (hρ₂ : ρ₂ ∈ Γ.R) (hρ₃ : ρ₃ ∈ Γ.R) (hρ₄ : ρ₄ ∈ Γ.R) (h : Across Γ ιE P Q J ρ₁ ρ₂)
    (h' : Across Γ ιE P Q J ρ₃ ρ₄) : s(ρ₁, ρ₂) = s(ρ₃, ρ₄) := by
  have hs := hPQ J hJ
  have eQ := fun {σ σ'} (hσ : σ ∈ Γ.R) (hσ' : σ' ∈ Γ.R) => region_eq_of_jump h_pres hD hJ hs hσ hσ'
  have eP := fun {σ σ'} (hσ : σ ∈ Γ.R) (hσ' : σ' ∈ Γ.R) =>
    region_eq_of_jump h_pres hD hJ hs.symm hσ hσ'
  obtain ⟨hside, h1, h2⟩ := h
  obtain ⟨hside', h3, h4⟩ := h'
  rcases hside with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hside' with ⟨a3, a4⟩ | ⟨a3, a4⟩
  · rw [eQ hρ₁ hρ₃ a1 a3 h1 h3, eP hρ₂ hρ₄ a2 a4 h2 h4]
  · rw [eQ hρ₁ hρ₄ a1 a4 h1 h4, eP hρ₂ hρ₃ a2 a3 h2 h3, Sym2.eq_swap]
  · rw [eP hρ₁ hρ₄ a1 a4 h1 h4, eQ hρ₂ hρ₃ a2 a3 h2 h3, Sym2.eq_swap]
  · rw [eP hρ₁ hρ₃ a1 a3 h1 h3, eQ hρ₂ hρ₄ a2 a4 h2 h4]

include hK hdeg

/-- **Touching regions lie across a jump.** -/
theorem exists_across_of_touch {ρ₁ ρ₂ : Set S} (hρ₁ : ρ₁ ∈ Γ.R) (hρ₂ : ρ₂ ∈ Γ.R)
    (h : Touch Γ ρ₁ ρ₂) : ∃ J ∈ 𝒯, Across Γ ιE P Q J ρ₁ ρ₂ := by
  obtain ⟨hne, e, he, h1, h2⟩ := h
  have hiso := h_pres.drawing_iso
  obtain ⟨J, hJ, heJ⟩ := exists_jump_of_edge hK hdeg (B := ιV '' (Γ.V ∩ bd S))
    (hiso.ιE_image ▸ mem_image_of_mem ιE he)
  have hs := hPQ J hJ
  have hU := fun {σ : Set S} (hσ : σ ∈ Γ.R) (heσ : e ⊆ closure σ) =>
    jumpLine_subset_closure h_pres hK hdeg hD hJ hσ he heJ heσ
  have hU₁ := hU hρ₁ h1
  have hU₂ := hU hρ₂ h2
  refine ⟨J, hJ, ?_, hU₁, hU₂⟩
  have hUΓ := jumpLine_subset_U (Γ := Γ) (ιE := ιE) J
  rcases hs.region_subset_or hUΓ hρ₁ with a1 | a1 <;>
    rcases hs.region_subset_or hUΓ hρ₂ with a2 | a2
  · exact (hne (region_eq_of_jump h_pres hD hJ hs hρ₁ hρ₂ a1 a2 hU₁ hU₂)).elim
  · exact Or.inl ⟨a1, a2⟩
  · exact Or.inr ⟨a1, a2⟩
  · exact (hne (region_eq_of_jump h_pres hD hJ hs.symm hρ₁ hρ₂ a1 a2 hU₁ hU₂)).elim

omit hK hD hPQ in
/-- An edge of a jump `J'` misses the line of another jump `J`. -/
theorem disjoint_jumpLine_of_ne {J J' : Hypergraph α β} (hJ : J ∈ 𝒯) (hJ' : J' ∈ 𝒯)
    (hne : J ≠ J') {e' : Set S} (he' : e' ∈ Γ.E) (he'J : ιE e' ∈ J'.edgeSet) :
    Disjoint e' (UJ J) := by
  have : T2Space S := h_pres.is_surface.2.1
  rw [disjoint_left]
  intro z hze' hz
  obtain ⟨e, he, heJ, hze⟩ := LastStep.mem_jumpLine.1 hz
  have hee : e ≠ e' := by
    rintro rfl
    exact hne (jump_eq_of_edge hdeg hJ hJ' heJ he'J)
  have hzV := LastStep.closure_inter_closure_subset Γ he he' hee ⟨hze, subset_closure hze'⟩
  exact (he'.2.1 hze').2 hzV

omit hK hD in
/-- **The regions across another jump lie on one side.** If `ρ₁, ρ₂` lie across `J' ≠ J`, then
both or neither lie off the outer side of `J`. -/
theorem across_iff_of_ne {J J' : Hypergraph α β} (hJ : J ∈ 𝒯) (hJ' : J' ∈ 𝒯) (hne : J ≠ J')
    {ρ₁ ρ₂ : Set S} (hρ₁ : ρ₁ ∈ Γ.R) (hρ₂ : ρ₂ ∈ Γ.R) (h : Across Γ ιE P Q J' ρ₁ ρ₂) :
    (ρ₁ ⊆ (Q J)ᶜ ↔ ρ₂ ⊆ (Q J)ᶜ) := by
  have hs := hPQ J hJ
  have hUΓ := jumpLine_subset_U (Γ := Γ) (ιE := ιE) J
  obtain ⟨e', he', he'J⟩ := exists_edge_of_jump h_pres hJ'
  have he'U : e' ⊆ UJ J' := subset_closure.trans (closure_subset_jumpLine he' he'J)
  obtain ⟨p, hp⟩ := he'.1
  have hcl₁ : p ∈ closure ρ₁ := h.2.1 (he'U hp)
  have hcl₂ : p ∈ closure ρ₂ := h.2.2 (he'U hp)
  rcases hs.subset_or_subset he'.2.2.1.isConnected.isPreconnected
      (disjoint_jumpLine_of_ne h_pres hdeg hJ hJ' hne he' he'J) with h' | h'
  · exact iff_of_true (hs.region_subset_right_of_closure hUΓ hρ₁ hcl₁ (h' hp))
      (hs.region_subset_right_of_closure hUΓ hρ₂ hcl₂ (h' hp))
  · have k₁ := hs.symm.region_subset_right_of_closure hUΓ hρ₁ hcl₁ (h' hp)
    have k₂ := hs.symm.region_subset_right_of_closure hUΓ hρ₂ hcl₂ (h' hp)
    exact iff_of_false (fun k => hs.region_not_subset_both hρ₁ k k₁)
      (fun k => hs.region_not_subset_both hρ₂ k k₂)

omit h_pres hK hdeg hD hPQ in
/-- A pair of regions as an unordered pair of vertices of `T`. -/
theorem sym2_eq_of_val {x y z t : Γ.R} (h : s(x.1, y.1) = s(z.1, t.1)) : s(x, y) = s(z, t) := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Subtype.ext h1, Subtype.ext h2]
  · rw [Subtype.ext h1, Subtype.ext h2, Sym2.eq_swap]

/-- **A walk that does not cross a jump stays on one side of it.** -/
theorem subset_iff_of_walk {J : Hypergraph α β} (hJ : J ∈ 𝒯) {ρa ρb : Γ.R}
    (hab : Across Γ ιE P Q J ρa.1 ρb.1) :
    ∀ {x y : Γ.R} (p : (touchGraph Γ).Walk x y), s(ρa, ρb) ∉ p.edges →
      (x.1 ⊆ (Q J)ᶜ ↔ y.1 ⊆ (Q J)ᶜ) := by
  intro x y p
  induction p with
  | nil => exact fun _ => Iff.rfl
  | @cons x z y hadj p' ih =>
    intro hp
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at hp
    obtain ⟨J', hJ', hacr⟩ := exists_across_of_touch h_pres hK hdeg hD hPQ x.2 z.2 hadj
    refine Iff.trans ?_ (ih hp.2)
    by_cases hJJ : J = J'
    · subst hJJ
      exact (hp.1 (sym2_eq_of_val
        (across_eq h_pres hD hPQ hJ ρa.2 ρb.2 x.2 z.2 hab hacr))).elim
    · exact across_iff_of_ne h_pres hdeg hPQ hJ hJ' hJJ x.2 z.2 hacr

/-- **`T` is acyclic**: every edge is a bridge, since the edge across `J` is the only way from one
side of `J` to the other. -/
theorem touchGraph_isAcyclic : (touchGraph Γ).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro x y hadj
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  intro p
  by_contra hp
  obtain ⟨J, hJ, hacr⟩ := exists_across_of_touch h_pres hK hdeg hD hPQ x.2 y.2 hadj
  have hiff := subset_iff_of_walk h_pres hK hdeg hD hPQ hJ hacr p hp
  have hs := hPQ J hJ
  rcases hacr.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hs.region_not_subset_both y.2 (hiff.1 h1) h2
  · exact hs.region_not_subset_both x.2 (hiff.2 h2) h1

/-- **`T` is a tree.** -/
theorem touchGraph_isTree [Nonempty Γ.R] : (touchGraph Γ).IsTree :=
  ⟨⟨touchGraph_preconnected hD h_pres.is_proper_drawing⟩,
    touchGraph_isAcyclic h_pres hK hdeg hD hPQ⟩

/-- For each jump, a region on each side across it. -/
theorem exists_across {J : Hypergraph α β} (hJ : J ∈ 𝒯) :
    ∃ ρ₁ ∈ Γ.R, ∃ ρ₂ ∈ Γ.R, Across Γ ιE P Q J ρ₁ ρ₂ := by
  obtain ⟨ρ₁, hρ₁, h1, hU₁⟩ := exists_region_of_jump h_pres hK hdeg hD hJ (hPQ J hJ)
  obtain ⟨ρ₂, hρ₂, h2, hU₂⟩ := exists_region_of_jump h_pres hK hdeg hD hJ (hPQ J hJ).symm
  exact ⟨ρ₁, hρ₁, ρ₂, hρ₂, Or.inl ⟨h1, h2⟩, hU₁, hU₂⟩

/-- **"$E(T)$ is in 1-1 correspondence with the $\Sigma$-jumps."** The jump `J` goes to the edge of
`T` across `J`. -/
theorem ncard_jumpSet_eq_ncard_edgeSet : Set.ncard 𝒯 = (touchGraph Γ).edgeSet.ncard := by
  classical
  let φ : (J : Hypergraph α β) → J ∈ 𝒯 → Sym2 Γ.R := fun J hJ =>
    s(⟨(exists_across h_pres hK hdeg hD hPQ hJ).choose,
        (exists_across h_pres hK hdeg hD hPQ hJ).choose_spec.1⟩,
      ⟨(exists_across h_pres hK hdeg hD hPQ hJ).choose_spec.2.choose,
        (exists_across h_pres hK hdeg hD hPQ hJ).choose_spec.2.choose_spec.1⟩)
  have hφ : ∀ J (hJ : J ∈ 𝒯), ∃ x y : Γ.R, φ J hJ = s(x, y) ∧ Across Γ ιE P Q J x.1 y.1 :=
    fun J hJ => ⟨_, _, rfl, (exists_across h_pres hK hdeg hD hPQ hJ).choose_spec.2.choose_spec.2⟩
  apply Set.ncard_congr φ
  · intro J hJ
    obtain ⟨x, y, hxy, hacr⟩ := hφ J hJ
    rw [hxy, SimpleGraph.mem_edgeSet]
    exact touch_of_across h_pres hPQ hJ x.2 hacr
  · intro J J' hJ hJ' heq
    by_contra hne
    obtain ⟨x, y, hxy, hacr⟩ := hφ J hJ
    obtain ⟨x', y', hxy', hacr'⟩ := hφ J' hJ'
    rw [hxy, hxy'] at heq
    -- `x, y` lie across `J'` too, so on one side of `J`.
    have hacr'' : Across Γ ιE P Q J' x.1 y.1 := by
      rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hacr'
      · rw [h1, h2]; exact hacr'.symm
    have hiff := across_iff_of_ne h_pres hdeg hPQ hJ hJ' hne x.2 y.2 hacr''
    have hs := hPQ J hJ
    rcases hacr.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hs.region_not_subset_both y.2 (hiff.1 h1) h2
    · exact hs.region_not_subset_both x.2 (hiff.2 h2) h1
  · intro e he
    induction e using Sym2.ind with
    | h x y =>
      obtain ⟨J, hJ, hacr⟩ := exists_across_of_touch h_pres hK hdeg hD hPQ x.2 y.2 he
      obtain ⟨x', y', hxy', hacr'⟩ := hφ J hJ
      refine ⟨J, hJ, ?_⟩
      rw [hxy']
      exact sym2_eq_of_val
        (across_eq h_pres hD hPQ hJ x'.2 y'.2 x.2 y.2 hacr' hacr)

end jumps

end RegionTree
end GM21
end GraphMinor
