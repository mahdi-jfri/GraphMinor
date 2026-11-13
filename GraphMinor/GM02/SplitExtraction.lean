module

public import GraphMinor.GM02.SplitSuppression
public import GraphMinor.GM02.ModelAttachments
public import GraphMinor.GM02.TreeValency
import GraphMinor.GM02.PrunedBranchTree
import GraphMinor.GM02.RestrictMinorModel
import GraphMinor.GM02.BranchTreeCounts

/-!
# A split of `H` inside a graph with an `H` minor

This file proves the main step of II (4.8): if `G` has a minor isomorphic to
`H`, then `G` topologically contains a split of `H`
(`exists_split_topological_pattern`).

Take a model of `H` in `G`. Call a vertex a mark if it is an end of an edge
that represents an edge of `H`. In each branch set that has a mark, take a
tree inside the branch set whose leaves are marks and that contains all
marks of the branch set. In each other branch set, take one vertex. Keep
these trees and the representing edges (`exists_splitSource_of_model`).
In the result every branch set spans a tree, and every vertex of a branch set
with at least two vertices has valency at least two: a vertex that is not a
mark is not a leaf, and a mark has its representing edge and a tree edge.

Then suppress the vertices of valency two in the branch trees
(`IsSplitSource.reduce`) and contract the branch trees
(`IsSplitSource.isSplitOf`).
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Classical

universe u v u' v'

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- A model of `H` in a finite graph `G` gives a subgraph `P` of `G` with a
model of `H` whose branch sets span trees, whose other edges represent edges
of `H`, and in which every vertex of a branch set with at least two vertices
has valency at least two. -/
theorem exists_splitSource_of_model {G : Graph α β} {H : Graph α' β'}
    {ηv : α' → Set α} {ηe : β' → β} (hm : IsMinorModel H G ηv ηe)
    (hVG : V(G).Finite) (hEG : E(G).Finite) :
    ∃ P ≤ G, V(P).Finite ∧ E(P).Finite ∧ ∃ ν : α' → Set α, IsSplitSource H P ν ηe 2 := by
  let A := representingEnds H G ηe
  have heach : ∀ u : V(H), ∃ K : Graph α β,
      K ≤ G.deleteEdges (ηe '' E(H)) ∧ V(K) ⊆ ηv u.val ∧ GraphConnected K ∧
      ηv u.val ∩ A ⊆ V(K) ∧ E(K).ncard + 1 = V(K).ncard ∧
      ∀ x ∈ V(K) \ A, 2 ≤ V(K).ncard → 2 ≤ valency K x := by
    intro u
    obtain ⟨C, hC, hVC, hconnC⟩ := hm.connected u.val u.property
    by_cases hmarks : (ηv u.val ∩ A).Nonempty
    · have hCfin := hVG.subset (hC.trans Graph.deleteEdges_le).vertexSet_mono
      have hmarkC : ηv u.val ∩ A ⊆ V(C) := fun _ h => hVC ▸ h.1
      obtain ⟨S, hS, hkeep, T, K, hT, hKC, hVK, hconnK, ⟨φ, hφ⟩, hleaf⟩ :=
        exists_pruned_branch_tree C hCfin hconnC (ηv u.val ∩ A) hmarks hmarkC
      let : Fintype S := (hCfin.subset hS).fintype
      have hkeepK : ηv u.val ∩ A ⊆ V(K) := fun _ h => hVK ▸ hkeep h
      have hsubK : V(K) ⊆ ηv u.val := fun x hx => hVC ▸ hKC.vertexSet_mono hx
      obtain ⟨r, hr⟩ := hmarks
      refine ⟨K, hKC.trans hC, hsubK, hconnK, hkeepK,
        ncard_edges_add_one_of_iso_tree hT φ, ?_⟩
      intro x hx _
      exact two_le_valency_of_tree_leaf_condition hT φ hφ (ηv u.val ∩ A)
        ⟨r, hkeepK hr, hr⟩ (fun a ha => hleaf a ha) ⟨hx.1, fun h => hx.2 h.2⟩
    · obtain ⟨r, hr⟩ := hm.vertex_nonempty u.val u.property
      refine ⟨Graph.noEdge {r} β, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact Graph.noEdge_le_iff.2 (by
          rw [vertexSet_deleteEdges]
          exact singleton_subset_iff.2 (hm.vertex_subset u.val u.property hr))
      · simpa only [vertexSet_noEdge, singleton_subset_iff] using hr
      · refine ⟨⟨r, by simp⟩, ?_⟩
        intro x hx y hy
        simp only [vertexSet_noEdge, mem_singleton_iff] at hx hy
        subst hx hy
        exact Relation.ReflTransGen.refl
      · intro x hx
        exact (hmarks ⟨x, hx⟩).elim
      · simp
      · intro x _ h2
        simp at h2
  choose K hK hKsub hKconn hKkeep hKcount hKdegree using heach
  let K' : α' → Graph α β := fun u =>
    if hu : u ∈ V(H) then K ⟨u, hu⟩ else Graph.noEdge ∅ β
  have hKeq : ∀ u (hu : u ∈ V(H)), K' u = K ⟨u, hu⟩ := by
    intro u hu
    simp only [K', hu, ↓reduceDIte]
  have hKle : ∀ u ∈ V(H), K' u ≤ G.deleteEdges (ηe '' E(H)) := by
    intro u hu
    rw [hKeq u hu]
    exact hK ⟨u, hu⟩
  have hsub : ∀ u ∈ V(H), V(K' u) ⊆ ηv u := by
    intro u hu
    rw [hKeq u hu]
    exact hKsub ⟨u, hu⟩
  have hconn : ∀ u ∈ V(H), GraphConnected (K' u) := by
    intro u hu
    rw [hKeq u hu]
    exact hKconn ⟨u, hu⟩
  have hkeep : ∀ u ∈ V(H), ηv u ∩ A ⊆ V(K' u) := by
    intro u hu
    rw [hKeq u hu]
    exact hKkeep ⟨u, hu⟩
  have hcounts : ∀ u ∈ V(H), E(K' u).ncard + 1 = V(K' u).ncard := by
    intro u hu
    rw [hKeq u hu]
    exact hKcount ⟨u, hu⟩
  have hdegree : ∀ u ∈ V(H), ∀ x ∈ V(K' u) \ A, 2 ≤ V(K' u).ncard → 2 ≤ valency (K' u) x := by
    intro u hu
    rw [hKeq u hu]
    exact hKdegree ⟨u, hu⟩
  have hrepr : ∀ u ∈ V(H), ∀ e ∈ E(H), ∀ x ∈ ηv u,
      G.Inc (ηe e) x → x ∈ V(K' u) := by
    intro u hu e he x hx hxe
    exact hkeep u hu ⟨hx, ⟨e, he, hxe⟩⟩
  obtain ⟨P, hPG, hmP, hVP, hEP⟩ :=
    GraphMinor.GM02.IsMinorModel.restrict_to_branch_subgraphs hm K' hKle hconn hsub hrepr
  have hPfinV := hVG.subset hPG.vertexSet_mono
  have hPfinE := hEG.subset hPG.edgeSet_mono
  have hKmem : ∀ u ∈ V(H), V(K' u) ⊆ V(P) := by
    intro u hu x hx
    rw [hVP]
    exact Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨hu, hx⟩⟩
  have hKEmem : ∀ u ∈ V(H), E(K' u) ⊆ E(P) := by
    intro u hu e he
    rw [hEP]
    exact Or.inr (Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨hu, he⟩⟩)
  have hKtoP : ∀ u ∈ V(H), K' u ≤ P.deleteEdges (ηe '' E(H)) := by
    intro u hu
    constructor
    · exact hKmem u hu
    · intro e a b hab
      have hKG := (hKle u hu).isLink_mono hab
      exact ⟨(hPG.isLink_iff (hKEmem u hu hab.edge_mem)).2 hKG.1, hKG.2⟩
  have hdis : ∀ u ∈ V(H), ∀ v ∈ V(H), u ≠ v → Disjoint V(K' u) V(K' v) :=
    fun u hu v hv hne => (hm.vertex_disjoint u hu v hv hne).mono (hsub u hu) (hsub v hv)
  -- Every non-representing edge of `P` is an edge of one of the trees.
  have hcases : ∀ e ∈ E(P), e ∉ ηe '' E(H) → ∃ u ∈ V(H), e ∈ E(K' u) := by
    intro e he hnot
    rw [hEP] at he
    rcases he with he | he
    · exact (hnot he).elim
    · obtain ⟨u, hu⟩ := Set.mem_iUnion.1 he
      obtain ⟨hu, hku⟩ := Set.mem_iUnion.1 hu
      exact ⟨u, hu, hku⟩
  have hends : ∀ u ∈ V(H), ∀ e ∈ E(K' u), ∀ x, P.Inc e x → x ∈ V(K' u) := by
    intro u hu e he x hx
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have hPab := ((hKtoP u hu).trans Graph.deleteEdges_le).isLink_mono hab
    rcases hx.eq_or_eq_of_isLink hPab with rfl | rfl
    · exact hab.left_mem
    · exact hab.right_mem
  refine ⟨P, hPG, hPfinV, hPfinE, fun u => V(K' u), hmP, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hVP] at hx
    obtain ⟨u, hu⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hu, hxu⟩ := Set.mem_iUnion.1 hu
    exact ⟨u, hu, hxu⟩
  · intro e he hnot
    obtain ⟨u, hu, hku⟩ := hcases e he hnot
    exact ⟨u, hu, hends u hu e hku⟩
  · intro u hu
    have hsubE : branchEdges H P (fun u => V(K' u)) ηe u ⊆ E(K' u) := by
      rintro e ⟨he, hnot, hall⟩
      obtain ⟨w, hw, hkw⟩ := hcases e he hnot
      obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet hkw
      have hPab := ((hKtoP w hw).trans Graph.deleteEdges_le).isLink_mono hab
      have hau : a ∈ V(K' u) := hall a hPab.inc_left
      have hwu : w = u := by
        by_contra hne
        exact Set.disjoint_left.1 (hdis w hw u hu hne) hab.left_mem hau
      exact hwu ▸ hkw
    have hle := Set.ncard_le_ncard hsubE (hPfinE.subset (hKEmem u hu))
    have := hcounts u hu
    show (branchEdges H P (fun u => V(K' u)) ηe u).ncard + 1 ≤ V(K' u).ncard
    omega
  · intro u hu x hx h2
    by_cases hxA : x ∈ A
    · -- A mark has its representing edge and an edge of its tree.
      obtain ⟨e, he, hxe⟩ := hxA
      have hheP : ηe e ∈ E(P) := hmP.edge_mem e he
      obtain ⟨y, hy⟩ := hxe
      have hPe : P.Inc (ηe e) x := ⟨y, (hPG.isLink_iff hheP).2 hy⟩
      have hνfin : V(K' u).Finite := hPfinV.subset (hKmem u hu)
      obtain ⟨b, hb, hxb⟩ : ∃ b ∈ V(K' u), x ≠ b := by
        obtain ⟨a, a', ha, ha', haa⟩ := (Set.one_lt_ncard_iff hνfin).1 (by omega)
        by_cases hxa : x = a
        · exact ⟨a', ha', hxa ▸ haa⟩
        · exact ⟨a, ha, hxa⟩
      obtain ⟨z, ⟨t, ht⟩, -⟩ := exists_step_ne_of_reflTransGen ((hconn u hu).2 x hx b hb) hxb
      have hPt := (hKtoP u hu).isLink_mono ht
      rw [deleteEdges_isLink] at hPt
      have hte : t ≠ ηe e := fun h => hPt.2 (h ▸ ⟨e, he, rfl⟩)
      have hpair : ({t, ηe e} : Set β) ⊆ incidentEdges P x := by
        rintro g (rfl | rfl)
        · exact hPt.1.inc_left
        · exact hPe
      have hi := Set.ncard_le_ncard hpair (incidentEdges_finite hPfinE x)
      rw [Set.ncard_pair hte] at hi
      change 2 ≤ (incidentEdges P x).ncard + (loopEdges P x).ncard
      omega
    · exact (hdegree u hu x ⟨hx, hxA⟩ h2).trans
        (valency_le_of_subgraph ((hKtoP u hu).trans Graph.deleteEdges_le) hPfinE x)

/-- Graph Minors II, (4.8), the main step: if `G` has a minor isomorphic to
`H`, then `G` topologically contains a split of `H`. -/
theorem exists_split_topological_pattern [Nonempty β] {G : Graph α β} {H : Graph α' β'}
    (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hm : IsIsoMinor H G) :
    ∃ L : Graph α β, TopologicallyContains G L ∧ IsSplitOf H L := by
  obtain ⟨ηv, ηe, hmodel⟩ := exists_isMinorModel_of_isIsoMinor hVG hEG hm
  obtain ⟨P, hPG, hVP, hEP, ν, hs⟩ := exists_splitSource_of_model hmodel hVG hEG
  obtain ⟨L, hsL, hVL, hEL, ν', hs'⟩ := hs.reduce hVP hEP
  exact ⟨L, ⟨P, hPG, L, hsL, ⟨Equiv.refl _, Equiv.refl _, fun _ _ _ => Iff.rfl⟩, fun _ => rfl⟩,
    hs'.isSplitOf hVL hEL⟩

end GraphMinor.GM02
