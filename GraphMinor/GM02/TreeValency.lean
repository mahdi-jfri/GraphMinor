module

public import GraphMinor.GM02.ValencyIso
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.GM02.ValencyTwo
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Reading tree degrees as multigraph valencies

A simple graph has no loops, and its incident edges correspond to its
neighbors. Its valency is therefore its usual degree. Transfer this fact
along the isomorphism realizing a branch tree. A non-attachment vertex is
not a leaf and has positive degree because its branch contains a different
marked vertex, so its valency is at least two.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- A simple graph's valency agrees with its degree. -/
theorem valency_ofSimpleGraph_eq_degree {α : Type*} [Fintype α]
    (T : SimpleGraph α) (x : α) : valency (Graph.ofSimpleGraph T) x = T.degree x := by
  have hnoloop : ∀ e, ¬ (Graph.ofSimpleGraph T).IsLoopAt e x := by
    intro e he
    have hlink : (Graph.ofSimpleGraph T).IsLink e x x := he
    change e = s(x, x) ∧ e ∈ T.edgeSet at hlink
    exact T.loopless.irrefl x ((SimpleGraph.mem_edgeSet _).1 (hlink.1 ▸ hlink.2))
  rw [valency_eq_incidentEdges_of_not_loop hnoloop]
  have hset : incidentEdges (Graph.ofSimpleGraph T) x = T.incidenceSet x := by
    ext e
    constructor
    · rintro ⟨y, hxy⟩
      change e = s(x, y) ∧ e ∈ T.edgeSet at hxy
      exact ⟨hxy.2, hxy.1 ▸ Sym2.mem_mk_left x y⟩
    · induction e using Sym2.inductionOn with
      | hf a b =>
        intro he
        rcases (T.mk'_mem_incidenceSet_iff).1 he with ⟨hab, rfl | rfl⟩
        · exact ⟨b, ⟨rfl, (SimpleGraph.mem_edgeSet _).2 hab⟩⟩
        · exact ⟨a, ⟨Sym2.eq_swap, (SimpleGraph.mem_edgeSet _).2 hab⟩⟩
  rw [hset, T.ncard_incidenceSet]

/-- Passing to a larger finite graph cannot lower valency. -/
theorem valency_le_of_subgraph {α : Type u} {β : Type v}
    {K P : Graph α β} (hKP : K ≤ P) (hEP : E(P).Finite) (x : α) :
    valency K x ≤ valency P x := by
  have hi : incidentEdges K x ⊆ incidentEdges P x := fun _ h => h.mono hKP
  have hl : loopEdges K x ⊆ loopEdges P x := fun _ h => h.mono hKP
  exact Nat.add_le_add (Set.ncard_le_ncard hi (incidentEdges_finite hEP x))
    (Set.ncard_le_ncard hl (loopEdges_finite hEP x))

/-- A realized branch tree with no unmarked leaves has valency at least
two at each unmarked vertex, provided the tree has a marked vertex. -/
theorem two_le_valency_of_tree_leaf_condition {α : Type u} {β : Type v}
    {S : Set α} [Fintype S] {T : SimpleGraph S} {K : Graph α β}
    (hT : T.IsTree) (φ : Iso (Graph.ofSimpleGraph T) K)
    (hφ : ∀ x : V(Graph.ofSimpleGraph T), (φ.vertexEquiv x).val = x.val.val)
    (A : Set α) (hroot : ∃ r ∈ V(K), r ∈ A)
    (hleaf : ∀ x : S, (T.neighborSet x).ncard = 1 → x.val ∈ A)
    {a : α} (ha : a ∈ V(K) \ A) : 2 ≤ valency K a := by
  let x := φ.vertexEquiv.symm ⟨a, ha.1⟩
  have hxa : x.val.val = a :=
    (hφ x).symm.trans (congrArg Subtype.val (φ.vertexEquiv.apply_symm_apply ⟨a, ha.1⟩))
  obtain ⟨r, hr, hrA⟩ := hroot
  let y := φ.vertexEquiv.symm ⟨r, hr⟩
  have hyr : y.val.val = r :=
    (hφ y).symm.trans (congrArg Subtype.val (φ.vertexEquiv.apply_symm_apply ⟨r, hr⟩))
  have hxy : x.val ≠ y.val := by
    intro h
    have har : a = r := hxa.symm.trans ((congrArg Subtype.val h).trans hyr)
    exact ha.2 (har ▸ hrA)
  let : Nontrivial S := nontrivial_of_ne x.val y.val hxy
  have hpos := hT.connected.preconnected.degree_pos_of_nontrivial x.val
  have hnotone : T.degree x.val ≠ 1 := by
    intro h
    have hA := hleaf x.val (by simpa only [SimpleGraph.ncard_neighborSet] using h)
    exact ha.2 (hxa ▸ hA)
  have hdegree : 2 ≤ T.degree x.val := by omega
  have heq := valency_eq_of_iso φ x
  have htarget : (φ.vertexEquiv x).val = a :=
    congrArg Subtype.val (φ.vertexEquiv.apply_symm_apply ⟨a, ha.1⟩)
  rw [htarget, valency_ofSimpleGraph_eq_degree] at heq
  exact heq ▸ hdegree

end GraphMinor.GM02
