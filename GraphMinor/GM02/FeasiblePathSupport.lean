module

public import GraphMinor.GM02.Feasibility
public import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Vertex support of feasible path families

For the corrected (2.9), paths in an induced graph must stay in its vertex
set. A nontrivial path in the simple shadow has this property. In a
feasible family, a vertex which is also a termination endpoint can occur
only on the path of that endpoint's pair. These facts control intersections
between the two induced families before they are joined.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

private theorem support_subset_of_start_mem {α : Type u} {β : Type v}
    {G : Graph α β} {a b : α} (p : (pathGraph G).Walk a b) (ha : a ∈ V(G)) :
    ∀ x ∈ p.support, x ∈ V(G) := by
  induction p with
  | nil => intro x hx; exact (List.mem_singleton.1 hx) ▸ ha
  | @cons a b c hab q ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ha
    · exact ih hab.1.right_mem x hx

private theorem start_mem_of_ne {α : Type u} {β : Type v} {G : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (hne : a ≠ b) : a ∈ V(G) := by
  cases p with
  | nil => exact (hne rfl).elim
  | cons hab _ => exact hab.1.left_mem

/-- A path joining distinct endpoints stays in the graph's vertex set,
even when the simple shadow uses a larger ambient vertex type. -/
theorem PairPath.vertices_subset {α : Type u} {β : Type v} {G : Graph α β}
    {p : Sym2 α} (P : PairPath (pathGraph G) p) (hp : ¬p.IsDiag) :
    P.vertices ⊆ V(G) := by
  have hne : P.start ≠ P.finish := by
    intro h
    apply hp
    rw [← P.ends_eq, Sym2.mk_isDiag_iff]
    exact h
  have hstart := start_mem_of_ne P.walk hne
  exact support_subset_of_start_mem P.walk hstart

/-- Graph inclusion induces inclusion of the simple shadows used for paths. -/
theorem pathGraph_mono {α : Type u} {β : Type v} {K G : Graph α β} (hKG : K ≤ G) :
    pathGraph K ≤ pathGraph G :=
  fun _ _ h => ⟨Graph.Adj.mono hKG h.1, h.2⟩

/-- Regard a pair path in a subgraph as a pair path in the larger graph. -/
noncomputable def PairPath.mapLe {α : Type u} {β : Type v} {K G : Graph α β}
    (hKG : K ≤ G) {p : Sym2 α} (P : PairPath (pathGraph K) p) : PairPath (pathGraph G) p where
  start := P.start
  finish := P.finish
  ends_eq := P.ends_eq
  walk := P.walk.mapLe (pathGraph_mono hKG)
  isPath := P.isPath.mapLe _

/-- Inclusion preserves the vertex support of a pair path. -/
theorem PairPath.vertices_mapLe {α : Type u} {β : Type v} {K G : Graph α β}
    (hKG : K ≤ G) {p : Sym2 α} (P : PairPath (pathGraph K) p) :
    (P.mapLe hKG).vertices = P.vertices := by
  ext x
  simp only [PairPath.mapLe, PairPath.vertices, Walk.support_mapLe_eq_support]

/-- In a vertex-disjoint family, a termination endpoint lies only on its
own pair's path. This applies to internal vertices as well as endpoints. -/
theorem endpoint_pair_eq_of_mem_family {α : Type u} {β : Type v} {G : Graph α β}
    {S : Set α} (A : Termination S)
    (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
    {p q : {p // p ∈ A.pairs}} {a : α} (ha : a ∈ (P p).vertices) (haq : a ∈ q.val) : p = q := by
  by_contra hne
  exact Set.disjoint_left.1 (hP p q hne) ha ((P q).endpoint_mem haq)

/-- A termination endpoint on a path of a feasible family is an endpoint
of that very path. -/
theorem mem_pair_of_mem_support_of_mem_family {α : Type u} {β : Type v} {G : Graph α β}
    {S : Set α} (A : Termination S)
    (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
    {p : {p // p ∈ A.pairs}} {a : α} (ha : a ∈ (P p).vertices) (haS : a ∈ A.support) :
    a ∈ p.val := by
  obtain ⟨q, hqa⟩ := Set.mem_iUnion.1 haS
  obtain ⟨hq, haq⟩ := Set.mem_iUnion.1 hqa
  have heq := endpoint_pair_eq_of_mem_family A P hP ha (q := ⟨q, hq⟩) haq
  exact heq.symm ▸ haq

end GraphMinor.GM02
