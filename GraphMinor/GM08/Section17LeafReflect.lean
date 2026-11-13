module

public import GraphMinor.GM08.Section17RootLeaves
import GraphMinor.GM08.Section4
import GraphMinor.GM08.Section17LeafSimulation
import GraphMinor.GM08.Section17LeafCanonical
import GraphMinor.GM08.Section17LeafNeighbor
import GraphMinor.GM08.Section17MapModel
import GraphMinor.GM08.Section17DeleteLoops

/-!
# Removing the root leaves from a simulation

In the proof of VIII (17.2) we add, at each root of both grafts, a new leaf
joined to the root by a new edge. The new leaves lie on the boundary of a larger
cylinder, and VII (9.3) gives a simulation of the extended target in the
extended host. Here we show that this gives a simulation of the original
target in the original host.

First the target is simulated in its extension, by putting each root together
with its new leaf in one branch (`GM08.rootLeafContractionSimulation`).
Compose this with the given simulation. Then identify each new leaf of the
host with its root. A new leaf of the host always lies in the same branch as
its root, so distinct branches stay disjoint. The new edges of the host become
loops, which no edge of the target uses, and we delete them. What remains is
the original host.
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v

variable {α : Type u} {β : Type v}

private theorem rootLeafGraph_inr_isLink {X : Graft α β} {t : α} {a b : α ⊕ α}
    (h : (rootLeafGraph X).IsLink (Sum.inr t) a b) :
    (a = Sum.inl t ∧ b = Sum.inr t) ∨ (a = Sum.inr t ∧ b = Sum.inl t) := by
  change rootLeafLink X (Sum.inr t) a b at h
  cases a <;> cases b <;> simp only [rootLeafLink] at h
  · obtain ⟨_, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨_, rfl, rfl⟩ := h
    exact Or.inr ⟨rfl, rfl⟩

private theorem rootLeafGraph_inl_isLink {X : Graft α β} {f : β} {a b : α ⊕ α} :
    (rootLeafGraph X).IsLink (Sum.inl f) a b ↔
      ∃ x y, a = Sum.inl x ∧ b = Sum.inl y ∧ X.G.IsLink f x y := by
  change rootLeafLink X (Sum.inl f) a b ↔ _
  cases a <;> cases b <;> simp [rootLeafLink]

private theorem inc_inr_new_leaf {X : Graft α β} {ε : β ⊕ α} {t : α}
    (h : (rootLeafGraph X).Inc ε (Sum.inr t)) : ε = Sum.inr t := by
  obtain ⟨z, hz⟩ := h
  cases ε with
  | inl f =>
    obtain ⟨x, y, hx, _, _⟩ := rootLeafGraph_inl_isLink.mp hz
    cases hx
  | inr s =>
    rcases rootLeafGraph_inr_isLink hz with ⟨h1, _⟩ | ⟨h1, _⟩
    · cases h1
    · cases h1; rfl

/-- In a simulation between root-leaf extensions, a new leaf of the host lies
in the branch of a vertex `w` of the target extension, and its old root lies in
the branch of `w`, or `w` is a new leaf `inr y` and the old root lies in the
branch of `inl y`. -/
private theorem old_root_near_new_leaf {Y X : Graft α β}
    {ηv : α ⊕ α → Set (α ⊕ α)} {ηe : β ⊕ α → β ⊕ α}
    (σ : IsGraftSimulation (rootLeafGraft Y) (rootLeafGraft X) ηv ηe)
    {w : α ⊕ α} (hw : w ∈ V((rootLeafGraft Y).G)) {t : α} (ht : Sum.inr t ∈ ηv w) :
    Sum.inl t ∈ ηv w ∨ ∃ y, w = Sum.inr y ∧ Sum.inl t ∈ ηv (Sum.inl y) := by
  have htV : Sum.inr t ∈ V((rootLeafGraft X).G) := σ.1.vertex_subset w hw ht
  have htT : t ∈ X.T := (inr_mem_rootLeafGraph_vertexSet X t).mp htV
  obtain ⟨K, hK, hKV, hconn⟩ := σ.1.connected w hw
  have hKle : K ≤ rootLeafGraph X := hK.trans Graph.deleteEdges_le
  by_cases hold : ∃ y : α, Sum.inl y ∈ V(K)
  · left
    rw [← hKV] at ht ⊢
    exact old_root_mem_of_connected_with_leaf X hKle hconn hold ht
  · push Not at hold
    right
    cases w with
    | inl u =>
      have huV : u ∈ V(Y.G) := (inl_mem_rootLeafGraph_vertexSet Y u).mp hw
      exact absurd ht (new_leaf_not_mem_old_vertex_branch σ huV htT)
    | inr y =>
      refine ⟨y, rfl, ?_⟩
      have hyT : y ∈ Y.T := (inr_mem_rootLeafGraph_vertexSet Y y).mp hw
      have heY : Sum.inr y ∈ E((rootLeafGraft Y).G) :=
        (inr_mem_rootLeafGraph_edgeSet Y y).mpr hyT
      have hlinkY : (rootLeafGraft Y).G.IsLink (Sum.inr y) (Sum.inl y) (Sum.inr y) := by
        change rootLeafLink Y (Sum.inr y) (Sum.inl y) (Sum.inr y)
        exact ⟨hyT, rfl, rfl⟩
      obtain ⟨x, hx, hxinc⟩ := (σ.1.inc_iff (Sum.inr y) hw (Sum.inr y) heY).mp
        hlinkY.inc_right
      -- every vertex of this branch is a new leaf, and the branch is `{inr t}`
      have hxK : x ∈ V(K) := hKV ▸ hx
      cases x with
      | inl x' => exact absurd hxK (hold x')
      | inr t' =>
        have hεeq := inc_inr_new_leaf hxinc
        have htt : t' = t := by
          have hwalk := hconn.2 (Sum.inr t') hxK (Sum.inr t) (hKV ▸ ht)
          rcases hwalk.cases_tail with heq | ⟨z, hzK, hz⟩
          · exact Sum.inr_injective heq.symm
          · obtain ⟨e, he⟩ := hz
            have hzeq := eq_old_root_of_adj_new_leaf X ⟨e, hKle.isLink_mono he⟩
            subst hzeq
            exact absurd (he.left_mem) (hold t)
        subst htt
        have hwY : Sum.inl y ∈ V((rootLeafGraft Y).G) :=
          (inl_mem_rootLeafGraph_vertexSet Y y).mpr (Y.T_subset hyT)
        obtain ⟨x'', hx'', hinc''⟩ := (σ.1.inc_iff (Sum.inl y) hwY (Sum.inr y) heY).mp
          hlinkY.inc_left
        rw [hεeq] at hinc''
        obtain ⟨z, hz⟩ := hinc''
        rcases rootLeafGraph_inr_isLink hz with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1 ▸ hx''
        · subst h1
          have hne : Sum.inl y ≠ (Sum.inr y : α ⊕ α) := Sum.inl_ne_inr
          exact absurd hx (disjoint_left.mp
            (σ.1.vertex_disjoint _ hwY _ hw hne) hx'')

/-- The graph obtained from the root-leaf extension by identifying each new
leaf with its root and deleting the new edges. -/
private abbrev collapsedLeafGraph (X : Graft α β) : Graph α (β ⊕ α) :=
  ((rootLeafGraph X).map rootLeafCollapse).deleteEdges (range Sum.inr)

private theorem collapsedLeafGraph_vertexSet (X : Graft α β) :
    V(collapsedLeafGraph X) = V(X.G) := by
  ext x
  change x ∈ rootLeafCollapse '' V(rootLeafGraph X) ↔ _
  constructor
  · rintro ⟨z, hz, rfl⟩
    cases z with
    | inl a => exact (inl_mem_rootLeafGraph_vertexSet X a).mp hz
    | inr a => exact X.T_subset ((inr_mem_rootLeafGraph_vertexSet X a).mp hz)
  · intro hx
    exact ⟨Sum.inl x, (inl_mem_rootLeafGraph_vertexSet X x).mpr hx, rfl⟩

private theorem collapsedLeafGraph_isLink (X : Graft α β) {ε : β ⊕ α} {x y : α} :
    (collapsedLeafGraph X).IsLink ε x y ↔ ∃ f, ε = Sum.inl f ∧ X.G.IsLink f x y := by
  simp only [collapsedLeafGraph, Graph.deleteEdges_isLink, Graph.map_isLink]
  constructor
  · rintro ⟨⟨a, b, hab, rfl, rfl⟩, hε⟩
    cases ε with
    | inr t => exact absurd ⟨t, rfl⟩ hε
    | inl f =>
      obtain ⟨x, y, rfl, rfl, hxy⟩ := rootLeafGraph_inl_isLink.mp hab
      exact ⟨f, rfl, hxy⟩
  · rintro ⟨f, rfl, hxy⟩
    refine ⟨⟨Sum.inl x, Sum.inl y, rootLeafGraph_inl_isLink.mpr ⟨x, y, rfl, rfl, hxy⟩,
      rfl, rfl⟩, ?_⟩
    rintro ⟨t, ht⟩
    exact Sum.inr_ne_inl ht

private theorem collapsedLeafGraph_inc (X : Graft α β) {f : β} {x : α} :
    (collapsedLeafGraph X).Inc (Sum.inl f) x ↔ X.G.Inc f x := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨f', hf', h⟩ := (collapsedLeafGraph_isLink X).mp hy
    cases Sum.inl_injective hf'
    exact ⟨y, h⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (collapsedLeafGraph_isLink X).mpr ⟨f, rfl, hy⟩⟩

/-- A simulation into the collapsed root-leaf extension whose edges are old
edges is a simulation into the original host. -/
private theorem isGraphSimulation_of_collapsed {X : Graft α β} {H : Graph α β}
    {ηv : α → Set α} {ηe : β → β ⊕ α}
    (h : IsGraphSimulation H (collapsedLeafGraph X) ηv ηe)
    (g : β → β) (hg : ∀ e ∈ E(H), ηe e = Sum.inl (g e)) :
    IsGraphSimulation H X.G ηv g := by
  have hV := collapsedLeafGraph_vertexSet X
  refine {
    vertex_nonempty := h.vertex_nonempty
    vertex_subset := fun v hv => hV ▸ h.vertex_subset v hv
    edge_mem := ?_
    vertex_disjoint := h.vertex_disjoint
    edge_injOn := ?_
    inc_iff := ?_
    isLoopAt_iff := ?_
    connected := ?_ }
  · intro e he
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet (h.edge_mem e he)
    obtain ⟨f, hf, hl⟩ := (collapsedLeafGraph_isLink X).mp hxy
    rw [hg e he] at hf
    cases Sum.inl_injective hf
    exact hl.edge_mem
  · intro e he e' he' heq
    apply h.edge_injOn he he'
    rw [hg e he, hg e' he', heq]
  · intro v hv e he
    rw [h.inc_iff v hv e he, hg e he]
    simp only [collapsedLeafGraph_inc]
  · intro v hv e he
    rw [h.isLoopAt_iff v hv e he, hg e he]
    simp only [collapsedLeafGraph_inc]
  · intro v hv
    obtain ⟨K, hK, hKV, hconn⟩ := h.connected v hv
    let D := X.G.deleteEdges (g '' E(H))
    have hsub : ηv v ⊆ V(D) := by
      change ηv v ⊆ V(X.G)
      exact hV ▸ h.vertex_subset v hv
    refine ⟨D.induce (ηv v), Graph.induce_le hsub, rfl, ?_⟩
    refine ⟨hKV ▸ hconn.1, ?_⟩
    intro x hx y hy
    have hwalk := hconn.2 x (hKV ▸ hx) y (hKV ▸ hy)
    clear hx hy
    induction hwalk with
    | refl => exact .refl
    | @tail z w _ hadj ih =>
      obtain ⟨ε, hε⟩ := hadj
      have hε' := hK.isLink_mono hε
      rw [Graph.deleteEdges_isLink] at hε'
      obtain ⟨hlink, hεnot⟩ := hε'
      obtain ⟨f, rfl, hf⟩ := (collapsedLeafGraph_isLink X).mp hlink
      refine ih.tail ⟨f, ?_⟩
      refine ⟨⟨hf, ?_⟩, hKV ▸ hε.left_mem, hKV ▸ hε.right_mem⟩
      rintro ⟨e, he, rfl⟩
      exact hεnot ⟨e, he, hg e he⟩

/-- If the root-leaf extension of `Y` is simulated in the root-leaf extension
of `X`, then `Y` is simulated in `X`. This removes the collar leaves used in the
proof of VIII (17.2), page 284. -/
theorem isGraftSimulatedIn_of_rootLeafGraft {Y X : Graft α β}
    (h : IsGraftSimulatedIn (rootLeafGraft Y) (rootLeafGraft X)) :
    IsGraftSimulatedIn Y X := by
  classical
  obtain ⟨ηv, ηe, σ⟩ := h
  have σ₁ := isGraftSimulation_comp (rootLeafContractionSimulation Y) σ
  set B : α → Set (α ⊕ α) := fun v => ⋃ v' ∈ rootLeafContractionBranches Y v, ηv v'
    with hB
  -- an old root lies in the same composite branch as its new leaf
  have hmemV : ∀ u ∈ V(Y.G), ∀ w ∈ rootLeafContractionBranches Y u,
      w ∈ V((rootLeafGraft Y).G) := by
    intro u hu w hw
    simp only [rootLeafContractionBranches, mem_union, mem_singleton_iff] at hw
    rcases hw with rfl | hw
    · exact (inl_mem_rootLeafGraph_vertexSet Y u).mpr hu
    · split_ifs at hw with huT
      · rw [mem_singleton_iff] at hw
        subst hw
        exact (inr_mem_rootLeafGraph_vertexSet Y u).mpr huT
      · exact absurd hw (notMem_empty _)
  have hinl_mem : ∀ u : α, Sum.inl u ∈ rootLeafContractionBranches Y u := by
    intro u
    simp [rootLeafContractionBranches]
  have hpair : ∀ u ∈ V(Y.G), ∀ t, Sum.inr t ∈ B u → Sum.inl t ∈ B u := by
    intro u hu t ht
    simp only [hB, mem_iUnion] at ht ⊢
    obtain ⟨w, hw, htw⟩ := ht
    rcases old_root_near_new_leaf σ (hmemV u hu w hw) htw with h1 | ⟨y, rfl, h2⟩
    · exact ⟨w, hw, h1⟩
    · have hyu : y = u := by
        simp only [rootLeafContractionBranches, mem_union, mem_singleton_iff] at hw
        rcases hw with hw | hw
        · cases hw
        · split_ifs at hw
          · exact Sum.inr_injective (mem_singleton_iff.mp hw)
          · exact absurd hw (notMem_empty _)
      subst hyu
      exact ⟨Sum.inl y, hinl_mem y, h2⟩
  have hdis : ∀ a ∈ V(Y.G), ∀ b ∈ V(Y.G), a ≠ b →
      Disjoint (rootLeafCollapse '' B a) (rootLeafCollapse '' B b) := by
    intro a ha b hb hab
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz⟩
    have hold : ∀ u ∈ V(Y.G), ∀ z ∈ B u, Sum.inl (rootLeafCollapse z) ∈ B u := by
      intro u hu z hz
      cases z with
      | inl x => exact hz
      | inr x => exact hpair u hu x hz
    have h1 := hold a ha z hz
    have h2 := hold b hb z' hz'
    rw [hzz] at h2
    exact disjoint_left.mp (σ₁.1.vertex_disjoint a ha b hb hab) h1 h2
  have σ₂ := σ₁.1.map_host_of_disjoint_images rootLeafCollapse hdis
  have hold_edge : ∀ e ∈ E(Y.G), ∃ f ∈ E(X.G), ηe (Sum.inl e) = Sum.inl f :=
    fun e he => old_edge_image_is_old σ he
  have σ₃ := σ₂.delete_host_loops (range Sum.inr)
    (fun e he => by
      obtain ⟨f, _, hf⟩ := hold_edge e he
      rintro ⟨t, ht⟩
      change Sum.inr t = ηe (Sum.inl e) at ht
      rw [hf] at ht
      exact Sum.inr_ne_inl ht)
    (fun ε hε x y hxy => by
      obtain ⟨t, rfl⟩ := hε
      obtain ⟨a, b, hab, rfl, rfl⟩ := hxy
      rcases rootLeafGraph_inr_isLink hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl)
  let g : β → β := fun e => Sum.elim id (fun _ => e) (ηe (Sum.inl e))
  have hg : ∀ e ∈ E(Y.G), (ηe ∘ Sum.inl) e = Sum.inl (g e) := by
    intro e he
    obtain ⟨f, _, hf⟩ := hold_edge e he
    simp only [Function.comp_apply, g, hf, Sum.elim_inl, id_eq]
  have σ₄ := isGraphSimulation_of_collapsed (X := X) σ₃ g hg
  refine ⟨_, g, σ₄, ?_, ?_⟩
  · have hidx := σ.2.1
    rw [show (rootLeafGraft X).T.ncard = (rootLeafGraft X).index from rfl,
      show (rootLeafGraft Y).T.ncard = (rootLeafGraft Y).index from rfl,
      rootLeafGraft_index, rootLeafGraft_index] at hidx
    exact hidx
  · intro u hu
    obtain ⟨z, hzB, hzT⟩ := σ₁.2.2 u hu
    change z ∈ (rootLeafGraft X).T at hzT
    simp only [rootLeafGraft, mem_image] at hzT
    obtain ⟨t, htT, rfl⟩ := hzT
    exact ⟨t, ⟨Sum.inr t, hzB, rfl⟩, htT⟩

end GraphMinor.GM08
