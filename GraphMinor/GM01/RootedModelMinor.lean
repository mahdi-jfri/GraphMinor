module

public import GraphMinor.GM01.RootedGraphs
public import Mathlib.Combinatorics.Graph.Simple
import GraphMinor.Minor.Basic

/-!
# Forgetting the root of a simple-source minor model

The proof of Graph Minors I, (1.1), uses a subdivision of a rooted path
configuration in its positive-height induction. The library's subdivision
construction takes an ordinary minor model. For a simple source, the
rooted model conditions (M1)–(M4) give such a model: every represented
source edge crosses two different branches, so no represented edge is
needed for connectivity inside a branch. We prove that fact here.
-/

public section

namespace GraphMinor.GM01

open Graph SimpleGraph

universe u v w

/-- Forget the root of a rooted model whose source is simple. A target edge
label is used only to extend the edge map to unused source labels. In the
positive-height argument a represented source edge supplies that label. -/
theorem RootedMinorModel.exists_isMinorModel_of_simple_with_branches
    {α : Type u} {γ : Type v} {δ : Type w} [Nonempty δ]
    (S : SimpleGraph α) (root : α) (G : RootedGraph γ δ)
    (M : RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, Set.mem_univ _⟩⟩ : RootedGraph α (Sym2 α)) G) :
    ∃ (ηv : α → Set γ) (ηe : Sym2 α → δ),
      (∀ x, ηv x = M.branch ⟨x, Set.mem_univ _⟩) ∧
      (∀ e (he : e ∈ S.edgeSet), ηe e = (M.edgeMap ⟨e, he⟩).val) ∧
      IsMinorModel (Graph.ofSimpleGraph S) G.graph ηv ηe := by
  classical
  let ηv (x : α) := M.branch ⟨x, Set.mem_univ _⟩
  let ηe (e : Sym2 α) := if he : e ∈ S.edgeSet then (M.edgeMap ⟨e, he⟩).val
    else Classical.choice (inferInstance : Nonempty δ)
  have spec (e : Sym2 α) (he : e ∈ S.edgeSet) : ηe e = (M.edgeMap ⟨e, he⟩).val := by
    simp only [ηe, he, ↓reduceDIte]
  have common {x y : α} {z : γ} (hx : z ∈ ηv x) (hy : z ∈ ηv y) : x = y := by
    by_contra hxy
    have hne : (⟨x, Set.mem_univ _⟩ : V(Graph.ofSimpleGraph S)) ≠ ⟨y, Set.mem_univ _⟩ :=
      fun h ↦ hxy (congrArg Subtype.val h)
    exact Set.disjoint_left.mp (M.branch_disjoint hne) hx hy
  have represented {e : Sym2 α} (he : e ∈ S.edgeSet) {x y : α}
      (hxy : (Graph.ofSimpleGraph S).IsLink e x y) :
      ∃ a ∈ ηv x, ∃ b ∈ ηv y, G.graph.IsLink (ηe e) a b := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.edge_links ⟨e, he⟩
      ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ hxy
    exact ⟨a, ha, b, hb, (spec e he).symm ▸ hab⟩
  have no_internal_edge (v : α) {edge : δ} {a b : γ}
      (hlink : G.graph.IsLink edge a b) (ha : a ∈ ηv v) (hb : b ∈ ηv v) :
      edge ∉ ηe '' E(Graph.ofSimpleGraph S) := by
    rintro ⟨e, he, heq⟩
    obtain ⟨x, y, hxy⟩ := (Graph.ofSimpleGraph S).exists_isLink_of_mem_edgeSet he
    have hSxy : S.Adj x y := by
      have he' := he
      rw [hxy.1] at he'
      exact he'
    obtain ⟨c, hc, d, hd, hcd⟩ := represented he hxy
    have hab : G.graph.IsLink (ηe e) a b := heq.symm ▸ hlink
    rcases hab.eq_and_eq_or_eq_and_eq hcd with h | h
    · have hc' : c ∈ ηv v := h.1 ▸ ha
      have hd' : d ∈ ηv v := h.2 ▸ hb
      exact hSxy.ne ((common hc hc').trans (common hd hd').symm)
    · have hc' : c ∈ ηv v := h.2 ▸ hb
      have hd' : d ∈ ηv v := h.1 ▸ ha
      exact hSxy.ne ((common hc hc').trans (common hd hd').symm)
  refine ⟨ηv, ηe, fun _ ↦ rfl, spec,
    { vertex_nonempty := ?_
      vertex_subset := ?_
      edge_mem := ?_
      vertex_disjoint := ?_
      edge_injOn := ?_
      inc_iff := ?_
      isLoopAt_iff := ?_
      connected := ?_ }⟩
  · intro x hx
    exact (M.branch_connected ⟨x, hx⟩).1
  · intro x hx
    exact M.branch_subset ⟨x, hx⟩
  · intro e he
    rw [spec e he]
    exact (M.edgeMap ⟨e, he⟩).property
  · intro x hx y hy hxy
    apply M.branch_disjoint
    intro heq
    exact hxy (congrArg Subtype.val heq)
  · intro e he e' he' heq
    have hmaps : M.edgeMap ⟨e, he⟩ = M.edgeMap ⟨e', he'⟩ := Subtype.ext (by
      simpa only [spec e he, spec e' he'] using heq)
    exact congrArg Subtype.val (M.edgeMap.injective hmaps)
  · intro v hv e he
    obtain ⟨x, y, hxy⟩ := (Graph.ofSimpleGraph S).exists_isLink_of_mem_edgeSet he
    obtain ⟨a, ha, b, hb, hab⟩ := represented he hxy
    constructor
    · intro hinc
      rcases hinc.eq_or_eq_of_isLink hxy with rfl | rfl
      · exact ⟨a, ha, hab.inc_left⟩
      · exact ⟨b, hb, hab.inc_right⟩
    · rintro ⟨z, hz, hinc⟩
      rcases hinc.eq_or_eq_of_isLink hab with rfl | rfl
      · have hvx : v = x := common hz ha
        exact hvx.symm ▸ hxy.inc_left
      · have hvy : v = y := common hz hb
        exact hvy.symm ▸ hxy.inc_right
  · intro v hv e he
    obtain ⟨x, y, hxy⟩ := (Graph.ofSimpleGraph S).exists_isLink_of_mem_edgeSet he
    have hSxy : S.Adj x y := by
      have he' := he
      rw [hxy.1] at he'
      exact he'
    obtain ⟨a, ha, b, hb, hab⟩ := represented he hxy
    constructor
    · intro hloop
      have hloopmem := he
      rw [hloop.1] at hloopmem
      exact False.elim (hloopmem.ne rfl)
    · intro hall
      have hax := hall a hab.inc_left
      have hby := hall b hab.inc_right
      have hfalse := hSxy.ne ((common ha hax).trans (common hb hby).symm)
      exact False.elim hfalse
  · intro v hv
    let K := G.graph.induce (ηv v)
    refine ⟨K, ?_, rfl, M.branch_connected ⟨v, hv⟩⟩
    constructor
    · exact M.branch_subset ⟨v, hv⟩
    · intro e a b he
      exact ⟨he.1, no_internal_edge v he.1 he.2.1 he.2.2⟩

/-- The ordinary minor model obtained by forgetting the root of a
simple-source rooted model. -/
theorem RootedMinorModel.exists_isMinorModel_of_simple
    {α : Type u} {γ : Type v} {δ : Type w} [Nonempty δ]
    (S : SimpleGraph α) (root : α) (G : RootedGraph γ δ)
    (M : RootedMinorModel
      (⟨Graph.ofSimpleGraph S, ⟨root, Set.mem_univ _⟩⟩ : RootedGraph α (Sym2 α)) G) :
    ∃ (ηv : α → Set γ) (ηe : Sym2 α → δ),
      IsMinorModel (Graph.ofSimpleGraph S) G.graph ηv ηe := by
  obtain ⟨ηv, ηe, _, _, hm⟩ := M.exists_isMinorModel_of_simple_with_branches S root G
  exact ⟨ηv, ηe, hm⟩

end GraphMinor.GM01
