module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.Minor.Basic
import GraphMinor.GM10.TreeWidthBasic

/-!
# Transferring the bags of II along a minor model

To recognize a fixed tree-width bound using XIII, the class must be closed
under minors. Replace a bag by the branch sets that it meets. A connected
branch set meets a connected set of bags: otherwise a tree path through a
missing bag would separate two vertices of that branch set. Disjointness of
the branch sets bounds the new bag size by the old bag size.
-/

namespace GraphMinor.GM02

open Graph Set SimpleGraph

universe u v u' v' w

variable {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}

private theorem tree_walk_avoiding_of_vertex (hD : IsTreeDecomposition G T X)
    {a : α} {i k j : ι} (hi : a ∈ X i) (hk : a ∈ X k) (hj : a ∉ X j) :
    ∃ p : T.Walk i k, j ∉ p.support := by
  obtain ⟨p, hp⟩ := hD.isTree.connected.exists_isPath i k
  refine ⟨p, fun hmem => hj ?_⟩
  exact hD.inter_subset ((GM10.onTreePath_iff_of_isPath hD.isTree hp).2 hmem) ⟨hi, hk⟩

private theorem tree_walk_avoiding_of_reachable (hD : IsTreeDecomposition G T X)
    {K : Graph α β} (hKG : K ≤ G) {j : ι}
    (hj : Disjoint V(K) (X j)) {a b : α} (hab : Relation.ReflTransGen K.Adj a b)
    (ha : a ∈ V(K)) :
    ∀ {i k : ι}, a ∈ X i → b ∈ X k → ∃ p : T.Walk i k, j ∉ p.support := by
  induction hab with
  | refl =>
    intro i k hi hk
    exact tree_walk_avoiding_of_vertex hD hi hk (fun h => Set.disjoint_left.1 hj ha h)
  | @tail b c hab hbc ih =>
    intro i k hi hk
    obtain ⟨e, he⟩ := hbc
    obtain ⟨t, hb, hc⟩ := hD.edge_mem (hKG.isLink_mono he)
    obtain ⟨p, hp⟩ := ih hi hb
    obtain ⟨q, hq⟩ := tree_walk_avoiding_of_vertex hD hc hk
      (fun h => Set.disjoint_left.1 hj he.right_mem h)
    refine ⟨p.append q, ?_⟩
    rw [Walk.support_append, List.mem_append]
    exact fun h => h.elim hp (fun h => hq (List.mem_of_mem_tail h))

/-- A connected subgraph meets every bag on the tree path between two bags
that it meets. This is the connectedness fact used when transferring a
vertex-bag decomposition to a minor model. -/
public theorem IsTreeDecomposition.inter_nonempty_of_connected
    (hD : IsTreeDecomposition G T X) {K : Graph α β}
    (hKG : K ≤ G) (hK : GraphConnected K) {i k j : ι}
    (hi : (V(K) ∩ X i).Nonempty) (hk : (V(K) ∩ X k).Nonempty)
    (hp : GM10.OnTreePath T i k j) : (V(K) ∩ X j).Nonempty := by
  classical
  by_contra hn
  have hd : Disjoint V(K) (X j) := Set.disjoint_left.2 (fun a ha hx => hn ⟨a, ha, hx⟩)
  obtain ⟨a, ha, hai⟩ := hi
  obtain ⟨b, hb, hbk⟩ := hk
  obtain ⟨p, havoid⟩ := tree_walk_avoiding_of_reachable hD hKG hd (hK.2 a ha b hb) ha hai hbk
  exact havoid (GM10.mem_support_of_onTreePath hp p)


/-- Replacing each bag by the branch sets of a minor model that it meets
preserves the tree-decomposition conditions and never increases bag sizes. -/
public theorem TreeWidthLE.of_minorModel
    {α' : Type u'} {β' : Type v'} {H : Graph α' β'}
    {ηv : α' → Set α} {ηe : β' → β} (hm : IsMinorModel H G ηv ηe)
    (hV : V(G).Finite) {w : ℕ} (hwidth : TreeWidthLE G w) : TreeWidthLE H w := by
  classical
  obtain ⟨ι, _, T, X, hD, hw⟩ := hwidth
  let Y : ι → Set α' := fun i => {v | v ∈ V(H) ∧ (ηv v ∩ X i).Nonempty}
  have hXY : ∀ i, (Y i).ncard ≤ (X i).ncard := by
    intro i
    have hXi : (X i).Finite := hV.subset (fun x hx => by
      rw [← hD.iUnion_eq]
      exact Set.mem_iUnion.2 ⟨i, hx⟩)
    let f : Y i → X i := fun v => ⟨v.property.2.choose, v.property.2.choose_spec.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      by_contra hn
      have hd := hm.vertex_disjoint a a.property.1 b b.property.1 hn
      exact Set.disjoint_left.1 hd a.property.2.choose_spec.1
        (by
          have heq : a.property.2.choose = b.property.2.choose := congrArg Subtype.val hab
          rw [heq]
          exact b.property.2.choose_spec.1)
    let : Finite (X i) := hXi.to_subtype
    simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf
  refine ⟨ι, inferInstance, T, Y, ⟨hD.isTree, ?_, ?_, ?_⟩,
    fun i => (hXY i).trans (hw i)⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hv
      exact hi.1
    · intro hv
      obtain ⟨a, ha⟩ := hm.vertex_nonempty v hv
      have haG := hm.vertex_subset v hv ha
      rw [← hD.iUnion_eq] at haG
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 haG
      exact Set.mem_iUnion.2 ⟨i, hv, a, ha, hi⟩
  · intro e v z hvz
    have hv := hvz.left_mem
    have hz := hvz.right_mem
    obtain ⟨a, ha, hae⟩ := (hm.inc_iff v hv e hvz.edge_mem).1 hvz.inc_left
    obtain ⟨b, hb, hbe⟩ := (hm.inc_iff z hz e hvz.edge_mem).1 hvz.inc_right
    by_cases hvz' : v = z
    · obtain ⟨i, hai, _⟩ := hD.edge_mem hae.isLink_other
      subst z
      exact ⟨i, ⟨hv, a, ha, hai⟩, ⟨hv, a, ha, hai⟩⟩
    · have hab : a ≠ b := by
        intro hab
        exact Set.disjoint_left.1 (hm.vertex_disjoint v hv z hz hvz') ha (hab ▸ hb)
      have heab : G.IsLink (ηe e) a b := by
        apply Graph.isLink_iff_inc.2
        refine ⟨hae, hbe, fun c hc => ?_⟩
        rcases hc.eq_or_eq_or_eq hae hbe with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hab h).elim
      obtain ⟨i, hai, hbi⟩ := hD.edge_mem heab
      exact ⟨i, ⟨hv, a, ha, hai⟩, ⟨hz, b, hb, hbi⟩⟩
  · intro i j k hp v hv
    obtain ⟨K, hK, hKv, hconn⟩ := hm.connected v hv.1.1
    have hKX : (V(K) ∩ X j).Nonempty := hD.inter_nonempty_of_connected
      (hK.trans Graph.deleteEdges_le) hconn (hKv ▸ hv.1.2) (hKv ▸ hv.2.2) hp
    exact ⟨hv.1.1, hKv ▸ hKX⟩

/-- The bounded-width class used for II (1.2) is closed under isomorphic
minors. The proof transfers the bags along a model of the minor. -/
public theorem TreeWidthLE.of_isIsoMinor
    {α' : Type u'} {β' : Type v'} [Nonempty β] {H : Graph α' β'}
    (hV : V(G).Finite) (hE : E(G).Finite) (hminor : IsIsoMinor H G)
    {w : ℕ} (hwidth : TreeWidthLE G w) : TreeWidthLE H w := by
  obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor hV hE hminor
  exact hwidth.of_minorModel hm hV

end GraphMinor.GM02
