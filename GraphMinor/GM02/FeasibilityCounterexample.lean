module

public import GraphMinor.GM02.Feasibility
public import GraphMinor.GM02.CrossingScheme
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.Graph.Delete
public import Mathlib.Combinatorics.SimpleGraph.Star
import GraphMinor.GM02.TerminationPairPaths
import Mathlib.Tactic.FinCases

/-!
# A four-vertex test of II (2.9)

Let the star have center `0` and leaves `1`, `2`, `3`. The original pairs
are `2,3` and `0,1`. Put the two edges joining `2,3` in the first spanning
subgraph and the edge `0,1` in the second. The first induced problem can
use the original terminal `0` internally, while the second uses it as an
endpoint. The reservations printed in II, page 315, do not remove an
original terminal from either side.
-/

@[expose] public section
namespace GraphMinor.GM02.FeasibilityCounterexample
open Graph SimpleGraph Set

/-- The four-vertex star centered at the original terminal `0`. -/
def star : Graph (Fin 4) (Sym2 (Fin 4)) := Graph.ofSimpleGraph (SimpleGraph.starGraph 0)

/-- The first spanning subgraph has the two edges joining leaves `2,3`. -/
def leftGraph := star.deleteEdges {s(0, 1)}

/-- The second spanning subgraph has just the edge joining `0,1`. -/
def rightGraph := star.restrict {s(0, 1)}

/-- A single pair of distinct star vertices. -/
def singletonTermination (a b : Fin 4) (hab : a ≠ b) : Termination V(star) where
  pairs := {s(a, b)}
  not_diag p hp := by
    have hp' : p = s(a, b) := Finset.mem_singleton.1 hp
    subst p
    exact fun h => hab (Sym2.mk_isDiag_iff.1 h)
  vertex_mem _ _ _ _ := Set.mem_univ _
  disjoint p hp q hq hne := by
    have hp' := Finset.mem_singleton.1 hp
    have hq' := Finset.mem_singleton.1 hq
    exact (hne (hp'.trans hq'.symm)).elim

/-- The original pair set is `{2,3}` and `{0,1}`. -/
def originals : Termination V(star) where
  pairs := {s(2, 3), s(0, 1)}
  not_diag p hp := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> decide
  vertex_mem _ _ _ _ := Set.mem_univ _
  disjoint p hp q hq hne := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact (hne rfl).elim
    · apply Set.disjoint_left.2
      intro v hv hv'
      fin_cases v <;> simp [Sym2.mem_iff] at hv hv'
    · apply Set.disjoint_left.2
      intro v hv hv'
      fin_cases v <;> simp [Sym2.mem_iff] at hv hv'
    · exact (hne rfl).elim

/-- The first side has just the pair of leaves `2,3`. -/
def leftTermination := singletonTermination 2 3 (by decide)

/-- The second side has just the center-leaf pair `0,1`. -/
def rightTermination := singletonTermination 0 1 (by decide)

/-- The two spanning subgraphs partition the star's edges. -/
theorem isSeparation : IsSeparation star leftGraph rightGraph := by
  refine ⟨Graph.deleteEdges_le, Graph.restrict_le, ?_, ?_, ?_⟩
  · exact Set.union_self _
  · change (E(star) \ {s(0, 1)}) ∪ (E(star) ∩ {s(0, 1)}) = E(star)
    exact Set.sdiff_union_inter _ _
  · exact Set.disjoint_sdiff_left.mono_right Set.inter_subset_right

/-- The original termination uses all four vertices. -/
theorem originals_support : originals.support = Set.univ := by
  ext v
  fin_cases v <;> simp [originals, Termination.support]

/-- Support of the first new termination. -/
theorem left_support : leftTermination.support = {2, 3} := by
  ext v
  simp [leftTermination, singletonTermination, Termination.support]

/-- Support of the second new termination. -/
theorem right_support : rightTermination.support = {0, 1} := by
  ext v
  simp [rightTermination, singletonTermination, Termination.support]

/-- Both spanning subgraphs have all vertices in their separator. -/
theorem separator : V(leftGraph) ∩ V(rightGraph) = Set.univ := Set.univ_inter _

/-- The two one-pair terminations with no reservations satisfy the four
printed crossing-scheme conditions in II, page 315. -/
def scheme : CrossingScheme star leftGraph rightGraph originals where
  left := leftTermination
  right := rightTermination
  reservedLeft := ∅
  reservedRight := ∅
  reservedLeft_subset := Set.empty_subset _
  reservedRight_subset := Set.empty_subset _
  left_support := by
    rw [separator, Set.sdiff_univ]
    change ∅ = originals.support ∩ (Set.univ \ Set.univ)
    simp
  right_support := by
    rw [separator, Set.sdiff_univ]
    change ∅ = originals.support ∩ (Set.univ \ Set.univ)
    simp
  even_support := by
    intro x _
    rw [originals_support, left_support, right_support]
    fin_cases x <;> simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff,
      ↓reduceIte] <;> exact ⟨1, rfl⟩
  reserved_disjoint := by simp
  reserved_union := by rw [separator, originals_support]; simp
  path_union := by
    classical
    simp only [Finset.coe_union]
    have hgraph : SimpleGraph.fromEdgeSet ((leftTermination.pairs : Set (Sym2 (Fin 4))) ∪
        (rightTermination.pairs : Set (Sym2 (Fin 4)))) =
        originals.pairGraph := by
      ext a b
      simp [Termination.pairGraph, leftTermination, rightTermination, singletonTermination, originals, or_comm, or_assoc]
    apply Eq.mpr (congrArg (fun F => IsPairPathUnion originals F
      (leftTermination.support ∪ rightTermination.support)) hgraph)
    have hs : leftTermination.support ∪ rightTermination.support = originals.support := by
      rw [left_support, right_support, originals_support]
      ext v
      fin_cases v <;> simp
    rw [hs]
    exact originals.isPairPathUnion

private theorem left_adj {a b : Fin 4} (hab : (SimpleGraph.starGraph (0 : Fin 4)).Adj a b)
    (hne : s(a, b) ≠ s(0, 1)) : (pathGraph leftGraph).Adj a b := by
  refine ⟨⟨s(a, b), ?_⟩, hab.ne⟩
  change (s(a, b) = s(a, b) ∧ s(a, b) ∈ (SimpleGraph.starGraph (0 : Fin 4)).edgeSet) ∧
    s(a, b) ∉ ({s(0, 1)} : Set (Sym2 (Fin 4)))
  exact ⟨⟨rfl, (SimpleGraph.mem_edgeSet _).2 hab⟩, hne⟩

/-- The first induced graph has the path `2,0,3`. -/
theorem left_feasible : leftTermination.Feasible leftGraph := by
  have h20 : (pathGraph leftGraph).Adj 2 0 := left_adj (by decide) (by decide)
  have h03 : (pathGraph leftGraph).Adj 0 3 := left_adj (by decide) (by decide)
  let P : PairPath (pathGraph leftGraph) s(2, 3) :=
    ⟨2, 3, rfl, Walk.cons h20 (Walk.cons h03 Walk.nil), Walk.IsPath.mk' (by change ([2, 0, 3] : List (Fin 4)).Nodup; decide)⟩
  have hp : ∀ p : {p // p ∈ leftTermination.pairs}, p.val = s(2, 3) :=
    fun p => Finset.mem_singleton.1 p.property
  refine ⟨fun p => (hp p).symm ▸ P, ?_⟩
  intro p q hpq
  exact (hpq (Subtype.ext ((hp p).trans (hp q).symm))).elim

/-- The second induced graph has the one-edge path `0,1`. -/
theorem right_feasible : rightTermination.Feasible rightGraph := by
  have h01 : (pathGraph rightGraph).Adj 0 1 := by
    refine ⟨⟨s(0, 1), ?_⟩, by decide⟩
    change s(0, 1) ∈ ({s(0, 1)} : Set (Sym2 (Fin 4))) ∧
      s(0, 1) = s(0, 1) ∧ s(0, 1) ∈ (SimpleGraph.starGraph (0 : Fin 4)).edgeSet
    exact ⟨rfl, rfl, (SimpleGraph.mem_edgeSet _).2 (by decide)⟩
  let P : PairPath (pathGraph rightGraph) s(0, 1) :=
    ⟨0, 1, rfl, h01.toWalk, Walk.IsPath.of_adj h01⟩
  have hp : ∀ p : {p // p ∈ rightTermination.pairs}, p.val = s(0, 1) :=
    fun p => Finset.mem_singleton.1 p.property
  refine ⟨fun p => (hp p).symm ▸ P, ?_⟩
  intro p q hpq
  exact (hpq (Subtype.ext ((hp p).trans (hp q).symm))).elim

private theorem center_mem_walk {a b : Fin 4} (hne : a ≠ 0) (hab : a ≠ b)
    (p : (pathGraph star).Walk a b) : (0 : Fin 4) ∈ p.support := by
  cases p with
  | nil => exact (hab rfl).elim
  | @cons _ x _ h q =>
    have hstar := (Graph.ofSimpleGraph_adj_iff _ _).1 h.1
    have hx : x = 0 := ((SimpleGraph.starGraph_adj.1 hstar).2).resolve_left hne
    change (0 : Fin 4) ∈ a :: q.support
    exact List.mem_cons_of_mem a (hx ▸ q.start_mem_support)

/-- The original pairs cannot be joined disjointly: the path between
leaves `2,3` must use `0`, an endpoint of the other prescribed pair. -/
theorem not_originals_feasible : ¬originals.Feasible star := by
  rintro ⟨P, hP⟩
  let p : {p // p ∈ originals.pairs} := ⟨s(2, 3), by decide⟩
  let q : {p // p ∈ originals.pairs} := ⟨s(0, 1), by decide⟩
  have hstart : (P p).start ≠ 0 := by
    have hm : (P p).start ∈ s((2 : Fin 4), 3) :=
      (congrArg (fun e : Sym2 (Fin 4) => (P p).start ∈ e) (P p).ends_eq).mp
        (Sym2.mem_mk_left _ _)
    rcases Sym2.mem_iff.1 hm with h | h <;> omega
  have hne : (P p).start ≠ (P p).finish := by
    intro heq
    have hd := Sym2.mk_isDiag_iff.2 heq
    rw [(P p).ends_eq] at hd
    exact (by decide : ¬s((2 : Fin 4), 3).IsDiag) hd
  have hp0 : (0 : Fin 4) ∈ (P p).vertices := center_mem_walk hstart hne (P p).walk
  have hq0 : (0 : Fin 4) ∈ (P q).vertices := (P q).endpoint_mem (by decide)
  have hpq : p ≠ q := by
    intro heq
    have h := congrArg Subtype.val heq
    exact (by decide : s((2 : Fin 4), 3) ≠ s(0, 1)) h
  exact Set.disjoint_left.1 (hP p q hpq) hp0 hq0

/-- A crossing scheme satisfying the printed definition has both induced
terminated graphs feasible, although the original terminated graph is not.
Thus II (2.9), page 315, is false without a correction at original terminals. -/
theorem counterexample_2_9 :
    IsSeparation star leftGraph rightGraph ∧
      ¬originals.Feasible star ∧
      scheme.left.Feasible (leftGraph.deleteVerts scheme.reservedLeft) ∧
      scheme.right.Feasible (rightGraph.deleteVerts scheme.reservedRight) := by
  refine ⟨isSeparation, not_originals_feasible, ?_, ?_⟩
  · change leftTermination.Feasible (leftGraph.deleteVerts ∅)
    rw [Graph.deleteVerts_empty]
    exact left_feasible
  · change rightTermination.Feasible (rightGraph.deleteVerts ∅)
    rw [Graph.deleteVerts_empty]
    exact right_feasible

end GraphMinor.GM02.FeasibilityCounterexample
