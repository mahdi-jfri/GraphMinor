module

public import GraphMinor.LRPlanarity.Defs
import GraphMinor.LRPlanarity.TreeNeighborhoodForest
import Mathlib.Data.Finset.Max

/-!
# Removing a leaf from a finite rooted subtree

Part IV, Section 7b of the planarity note attaches a strip and its new
vertex polygon at each step. In reverse order, remove a vertex of greatest
search depth. Its parent stays in the subtree, and no remaining vertex
loses its parent. This gives the finite induction order for disc gluing.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Part IV, Section 7b: a nontrivial finite parent-closed subtree has a
nonroot leaf whose deletion leaves a parent-closed subtree with the same root. -/
theorem exists_leaf_erase_subtree {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (root : Fin N) (S : Finset (Fin N))
    (hroot : root ∈ S) (hancestor : ∀ v ∈ S, T.Ancestor root v)
    (hparent : ∀ v ∈ S, v ≠ root → ∃ p ∈ S, T.parent v = some p)
    (hother : ∃ w ∈ S, w ≠ root) :
    ∃ leaf ∈ S, leaf ≠ root ∧
      (∀ v ∈ S, T.parent v ≠ some leaf) ∧
      root ∈ S.erase leaf ∧
      (∀ v ∈ S.erase leaf, T.Ancestor root v) ∧
      (∀ v ∈ S.erase leaf, v ≠ root →
        ∃ p ∈ S.erase leaf, T.parent v = some p) := by
  classical
  obtain ⟨leaf, hleaf, hmax⟩ := S.exists_max_image T.depth ⟨root, hroot⟩
  obtain ⟨w, hw, hwr⟩ := hother
  have hstrict := strict_ancestor_depth_lt hT (hancestor w hw) (Ne.symm hwr)
  have hleafroot : leaf ≠ root := by
    intro he
    have hle := hmax w hw
    rw [he] at hle
    exact (not_lt_of_ge hle) hstrict
  have hchild : ∀ v ∈ S, T.parent v ≠ some leaf := by
    intro v hv hp
    have hle := hmax v hv
    rw [(hT.2.1 leaf v hp).2] at hle
    exact Nat.not_succ_le_self _ hle
  refine ⟨leaf, hleaf, hleafroot, hchild,
    Finset.mem_erase.mpr ⟨Ne.symm hleafroot, hroot⟩, ?_, ?_⟩
  · intro v hv
    exact hancestor v (Finset.mem_of_mem_erase hv)
  · intro v hv hvr
    have hvS := Finset.mem_of_mem_erase hv
    obtain ⟨p, hp, hvp⟩ := hparent v hvS hvr
    have hpl : p ≠ leaf := by
      intro he
      exact hchild v hvS (he ▸ hvp)
    exact ⟨p, Finset.mem_erase.mpr ⟨hpl, hp⟩, hvp⟩

/-- Every nonroot descendant has a parent which is also a descendant. -/
theorem ancestor_parent_of_ne {N : ℕ} {T : Forest N} {root v : Fin N}
    (h : T.Ancestor root v) (hne : v ≠ root) :
    ∃ p, T.Ancestor root p ∧ T.parent v = some p := by
  cases h with
  | refl => exact (hne rfl).elim
  | @tail p v hpath hparent => exact ⟨p, hpath, hparent⟩

/-- Distinct directed parent edges have distinct unordered endpoint pairs.
The reverse pair cannot also be a parent edge, since depth increases. -/
theorem parent_edge_unordered_injective {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} (hT : T.IsDFS G) :
    Function.Injective (fun e : {e : Fin N × Fin N // T.parent e.2 = some e.1} =>
      s(e.val.1, e.val.2)) := by
  intro e f he
  rcases Sym2.eq_iff.mp he with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · exact Subtype.ext (Prod.ext hsource htarget)
  · have hedepth := (hT.2.1 e.val.1 e.val.2 e.property).2
    have hfdepth := (hT.2.1 f.val.1 f.val.2 f.property).2
    rw [hsource, htarget] at hedepth
    have hlt : T.depth f.val.1 < T.depth f.val.2 := by
      rw [hfdepth]
      exact Nat.lt_succ_self _
    rw [hedepth] at hlt
    exact (Nat.not_succ_le_self _ hlt.le).elim

/-- Every ancestor of a vertex in a rooted component is in that component.
Uniqueness of the parent makes the two ancestor paths agree backwards. -/
theorem root_ancestor_of_ancestor {N : ℕ} {T : Forest N} {root v u : Fin N}
    (hroot : T.parent root = none) (hpath : T.Ancestor root v)
    (hanc : T.Ancestor u v) : T.Ancestor root u := by
  induction hpath generalizing u with
  | refl =>
    cases hanc with
    | refl => exact Relation.ReflTransGen.refl
    | @tail p root hprefix hparent =>
      rw [hroot] at hparent
      cases hparent
  | @tail w v hprefix hparent ih =>
    cases hanc with
    | refl => exact hprefix.tail hparent
    | @tail p v hp hpv =>
      have he : p = w := Option.some.inj (hpv.symm.trans hparent)
      subst p
      exact ih hp

/-- A cotree back edge is distinct as an unordered pair from every parent
edge. One orientation contradicts depth increase, the other is excluded
in the definition of a back edge. -/
theorem backEdge_ne_parent_unordered {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} (hT : T.IsDFS G) {b : Arc N} (hb : T.BackEdge G b)
    {u v : Fin N} (hp : T.parent v = some u) : s(b.1, b.2) ≠ s(u,v) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [← hs, ← ht] at hp
    have hdepth := (hT.2.1 b.1 b.2 hp).2
    have hlt := hb.2.2.1
    rw [hdepth] at hlt
    exact (Nat.not_succ_le_self _ hlt.le).elim
  · rw [← ht, ← hs] at hp
    exact hb.2.2.2 hp

/-- Distinct back edges have distinct unordered endpoint pairs, since the
reverse orientation would require depth to decrease both ways. -/
theorem backEdge_unordered_ne {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    {b c : Arc N} (hb : T.BackEdge G b) (hc : T.BackEdge G c) (hne : b ≠ c) :
    s(b.1,b.2) ≠ s(c.1,c.2) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · exact hne (Prod.ext hs ht)
  · have hdepth := hb.2.2.1
    rw [hs,ht] at hdepth
    exact Nat.lt_asymm hdepth hc.2.2.1

end GraphMinor.LRPlanarity
