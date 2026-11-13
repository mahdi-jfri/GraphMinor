module

public import GraphMinor.GM21.Section6SideSupports
public import GraphMinor.GM21.Section6Separation
public import GraphMinor.GM21.Section4
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, Section 6: a presentation restricted to one side of a line

The proofs of (6.5), (6.6), (6.7) and claim (4) of the proof of (6.3) in *Graph Minors XXI*
(pages 25–29 of the preprint) all cut the surface `Σ` along a line `F` and use a presentation of the
part of `G` on one side. Claim (4) says it this way: "Let $\Sigma_1, \Sigma_2 \subseteq \Sigma$ be
surfaces with $\Sigma_1 \cup \Sigma_2 = \Sigma$ and $\Sigma_1 \cap \Sigma_2 = F$. For $i = 1, 2$ let
$\Gamma_i = \Gamma \cap \Sigma_i$ ... there is a presentation of $G_i$ in $\Sigma_i$ of depth $\le q$
... using $\Gamma_i$". This file builds that presentation.

The setting (`IsSideOfLine`): `F` is a proper line of `Σ` whose ends `a, b` are vertices of `Γ` and
which has no other point in `U(Γ)`, and `Σ₁, Σ₂ ⊆ Σ` are surfaces with `Σ₁ ∪ Σ₂ = Σ` and
`Σ₁ ∩ Σ₂ = F`. The new presentation lives in the space `↥Σ₁`.

* `sideSub` is `Γ ∩ Σ₁` as a subgraph of `Γ`, and `sideGraph` is the graph
  `G₁ = (Γ ∩ Σ₁) ∪ μ(bd(Σ) ∩ Σ₁)`, where `μ(bd(Σ) ∩ Σ₁)` is the union of the graphs
  `μ(F_j* ∩ Σ₁)`.
* The supports of the new presentation are the sets `F_j* ∩ Σ₁` that are not empty. We ask that
  each of them be a support (that is, connected), and index them by an injective map
  `σ : Fin r₁ → Fin r`. This holds in (6.5), (6.6) and (6.7). In claim (4) of (6.3) it can fail,
  when both ends of `F` lie in one support (see the correction to the proof of (6.3) in
  `corrections/GM21.md`).
* `presentationHasDepthLe_side`: `Γ ∩ Σ₁`, the supports `F_{σ i}* ∩ Σ₁`, the graphs
  `μ(F_{σ i}* ∩ Σ₁)` and the restriction of `μ` form a presentation of `G₁` in `Σ₁`, of depth at
  most the depth of the given one.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface GraphMinor.GM21.Supports Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- The setting of a side of a line (Graph Minors XXI, proof of (6.3), claim (4), page 29 of the
preprint, and the proofs of (6.5)–(6.7)): `F` is a proper line in `S` with ends `a, b ∈ V(Γ)` and no
other point in `U(Γ)`, and `S₁, S₂ ⊆ S` are surfaces with `S₁ ∪ S₂ = S` and `S₁ ∩ S₂ = F`. -/
structure IsSideOfLine (Γ : Drawing S) (S₁ S₂ F : Set S) (a b : S) : Prop where
  surface_left : IsSurface S₁
  surface_right : IsSurface S₂
  union_eq : S₁ ∪ S₂ = univ
  inter_eq : S₁ ∩ S₂ = F
  proper : IsProperLineInSurface F a b
  left_mem : a ∈ Γ.V
  right_mem : b ∈ Γ.V
  inter_U : F ∩ Γ.U ⊆ {a, b}

namespace IsSideOfLine

variable {Γ : Drawing S} {S₁ S₂ F : Set S} {a b : S}
  (h : IsSideOfLine Γ S₁ S₂ F a b)
include h

theorem isClosed_left [T2Space S] : IsClosed S₁ := isClosed_of_isSurface h.surface_left

theorem isClosed_right [T2Space S] : IsClosed S₂ := isClosed_of_isSurface h.surface_right

theorem isClosed_line [T2Space S] : IsClosed F := h.proper.1.isCompact.isClosed

theorem inter_bd : F ∩ bd S = {a, b} := h.proper.inter_bd_eq

/-- The other side. -/
theorem symm : IsSideOfLine Γ S₂ S₁ F a b :=
  ⟨h.surface_right, h.surface_left, by rw [Set.union_comm]; exact h.union_eq,
    by rw [Set.inter_comm]; exact h.inter_eq, h.proper, h.left_mem, h.right_mem, h.inter_U⟩

theorem line_subset_left : F ⊆ S₁ := h.inter_eq ▸ inter_subset_left

theorem line_subset_right : F ⊆ S₂ := h.inter_eq ▸ inter_subset_right

/-- The ends of `F` are boundary points of `S`. -/
theorem ends_mem_bd : a ∈ bd S ∧ b ∈ bd S := ⟨h.proper.2.1, h.proper.2.2.1⟩

/-- A vertex of `Γ` on `F` is an end of `F`. -/
theorem mem_ends_of_mem_V {x : S} (hxF : x ∈ F) (hxV : x ∈ Γ.V) : x = a ∨ x = b :=
  h.inter_U ⟨hxF, Γ.V_subset_U hxV⟩

/-- A vertex of `Γ` on `F` is in `bd(S)`. -/
theorem mem_bd_of_mem_V {x : S} (hxF : x ∈ F) (hxV : x ∈ Γ.V) : x ∈ bd S := by
  rcases h.mem_ends_of_mem_V hxF hxV with rfl | rfl
  · exact h.ends_mem_bd.1
  · exact h.ends_mem_bd.2

/-- `F ∩ bd(S) ⊆ V(Γ)`. -/
theorem inter_bd_subset_V : F ∩ bd S ⊆ Γ.V := by
  rw [h.inter_bd]
  rintro x (rfl | rfl)
  · exact h.left_mem
  · exact h.right_mem

/-- Each edge of `Γ` lies in `S₁` or misses it. -/
theorem edge_subset_or_disjoint [T2Space S] {e : Set S} (he : e ∈ Γ.E) : e ⊆ S₁ ∨ Disjoint e S₁ := by
  refine subset_or_disjoint_side h.isClosed_left h.isClosed_right h.union_eq h.inter_eq
    he.2.2.1.isConnected.isPreconnected ?_
  rw [disjoint_left]
  intro x hxe hxF
  have hxUV := he.2.1 hxe
  rcases h.mem_ends_of_mem_V hxF (by
    rcases h.inter_U ⟨hxF, hxUV.1⟩ with rfl | rfl
    · exact h.left_mem
    · exact h.right_mem) with rfl | rfl
  · exact hxUV.2 h.left_mem
  · exact hxUV.2 h.right_mem

/-- The closure of an edge of `Γ` that misses `S₁` lies in `S₂`. -/
theorem closure_subset_right_of_disjoint [T2Space S] {e : Set S} (he : Disjoint e S₁) : closure e ⊆ S₂ :=
  closure_minimal (subset_two_of_disjoint h.union_eq he) h.isClosed_right

/-- Each space of `Γ` lies in `S₁` or misses it. -/
theorem space_subset_or_disjoint [T2Space S] {s : Set S} (hs : s ∈ drawingSpaces Γ) :
    s ⊆ S₁ ∨ Disjoint s S₁ := by
  refine subset_or_disjoint_side h.isClosed_left h.isClosed_right h.union_eq h.inter_eq
    (isConnected_of_mem_drawingSpaces hs).isPreconnected ?_
  rw [disjoint_left]
  intro x hxs hxF
  have hx := subset_bd_diff_of_mem_drawingSpaces hs hxs
  exact hx.2 (h.inter_bd_subset_V ⟨hxF, hx.1⟩)

end IsSideOfLine

/-! ## The graph of one side -/

/-- `Γ ∩ S₁` as a subgraph of `Γ_sub`: the vertices `ιV u` with `u ∈ V(Γ) ∩ S₁`, and the edges
`ιE e` with `e ∈ E(Γ)`, `e ⊆ S₁`. -/
def sideSub (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) (ιE : Set S → β)
    (S₁ : Set S) : Hypergraph α β :=
  subOn Γ_sub (ιV '' (Γ.V ∩ S₁)) (ιE '' {e | e ∈ Γ.E ∧ e ⊆ S₁})

/-- The graph `G₁ = (Γ ∩ S₁) ∪ μ(bd(S) ∩ S₁)` of claim (4) of the proof of (6.3) (page 29 of the
preprint): the subgraph of `G` with the vertices and edges of `Γ ∩ S₁` and of the graphs
`μ(F_j* ∩ S₁)`. -/
def sideGraph (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
    (ιE : Set S → β) {r : ℕ} (F_star : Fin r → Set S) (μ : BoundaryUnit S → Hypergraph α β)
    (S₁ : Set S) : Hypergraph α β :=
  subOn G ((sideSub Γ Γ_sub ιV ιE S₁).vertexSet ∪
      ⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet)
    ((sideSub Γ Γ_sub ιV ιE S₁).edgeSet ∪ ⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet)

/-- The restriction of `μ` to the units of `↥S₁`. -/
def sideMu (μ : BoundaryUnit S → Hypergraph α β) (S₁ : Set S) :
    BoundaryUnit S₁ → Hypergraph α β
  | .vertex u => μ (.vertex u.1)
  | .space s => μ (.space (Subtype.val '' s))

/-- The ends in `G` of an edge of a subgraph `A ≤ G` are vertices of `A`. -/
theorem ends_subset_of_le {A G : Hypergraph α β} (hA : A ≤ G) {e : β} (he : e ∈ A.edgeSet) :
    G.ends e ⊆ A.vertexSet := by
  rw [hA.ends_eq e he]
  intro x hx
  exact A.vertex_mem_of_inc hx

/-- A subgraph of a graph is a graph. -/
theorem isGraph_of_le {A G : Hypergraph α β} (hA : A ≤ G) (hG : G.IsGraph) : A.IsGraph := by
  intro e he
  rw [← hA.ends_eq e he]
  exact hG e (hA.edgeSet_subset he)

section Graph

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
  {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  {S₁ S₂ F : Set S} {a b : S}

/-- The ends of an edge `ιE e` with `e ⊆ S₁` are the images of vertices of `Γ` in `S₁`. -/
theorem ends_ιE_subset (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h₁ : IsClosed S₁)
    {e : Set S} (he : e ∈ Γ.E) (heS : e ⊆ S₁) :
    Γ_sub.ends (ιE e) ⊆ ιV '' (Γ.V ∩ S₁) := by
  intro x hx
  have hxV : x ∈ Γ_sub.vertexSet := Γ_sub.vertex_mem_of_inc hx
  rw [← hP.ιV_image] at hxV
  obtain ⟨u, huV, rfl⟩ := hxV
  have hu : u ∈ closure e := (hP.inc_iff e he u huV).mp hx
  exact ⟨u, ⟨huV, closure_minimal heS h₁ hu⟩, rfl⟩

theorem sideSub_le (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h₁ : IsClosed S₁) :
    sideSub Γ Γ_sub ιV ιE S₁ ≤ Γ_sub := by
  apply subOn_le
  rintro _ ⟨e, ⟨he, heS⟩, rfl⟩ -
  exact ends_ιE_subset hP h₁ he heS

theorem sideSub_le_G (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h₁ : IsClosed S₁) :
    sideSub Γ Γ_sub ιV ιE S₁ ≤ G :=
  (sideSub_le hP h₁).trans hP.drawing_subgraph

/-- `μ(F_j* ∩ S₁)` is a subgraph of `G`. -/
theorem supportGraph_inter_le (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r) :
    supportGraph G Γ μ (F_star j ∩ S₁) ≤ G :=
  supportGraph_le hP j inter_subset_left

/-- `G₁` is a subgraph of `G`. -/
theorem sideGraph_le (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h₁ : IsClosed S₁) :
    sideGraph G Γ Γ_sub ιV ιE F_star μ S₁ ≤ G := by
  apply subOn_le
  rintro e (he | he) -
  · exact (ends_subset_of_le (sideSub_le_G hP h₁) he).trans subset_union_left
  · obtain ⟨j, hj⟩ := mem_iUnion.mp he
    exact (ends_subset_of_le (supportGraph_inter_le hP j) hj).trans
      (subset_union_of_subset_right
        (subset_iUnion (fun j => (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet) j) _)

theorem sideSub_le_sideGraph (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h₁ : IsClosed S₁) :
    sideSub Γ Γ_sub ιV ιE S₁ ≤ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁ :=
  le_subOn (sideSub_le_G hP h₁) subset_union_left subset_union_left

theorem supportGraph_inter_le_sideGraph (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) :
    supportGraph G Γ μ (F_star j ∩ S₁) ≤ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁ :=
  le_subOn (supportGraph_inter_le hP j)
    (subset_union_of_subset_right
      (subset_iUnion (fun j => (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet) j) _)
    (subset_union_of_subset_right
      (subset_iUnion (fun j => (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet) j) _)

theorem vertexSet_sideGraph (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h₁ : IsClosed S₁) :
    (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁).vertexSet =
      (sideSub Γ Γ_sub ιV ιE S₁).vertexSet ∪
        ⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet := by
  apply Subset.antisymm (fun x hx => hx.1)
  intro x hx
  refine ⟨hx, ?_⟩
  rcases hx with hx | hx
  · exact (sideSub_le_G hP h₁).vertexSet_subset hx
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact (supportGraph_inter_le hP j).vertexSet_subset hj

theorem edgeSet_sideGraph (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h₁ : IsClosed S₁) :
    (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁).edgeSet =
      (sideSub Γ Γ_sub ιV ιE S₁).edgeSet ∪
        ⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet := by
  apply Subset.antisymm (fun x hx => hx.1)
  intro x hx
  refine ⟨hx, ?_⟩
  rcases hx with hx | hx
  · exact (sideSub_le_G hP h₁).edgeSet_subset hx
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact (supportGraph_inter_le hP j).edgeSet_subset hj

end Graph

end Side
end GM21
end GraphMinor
