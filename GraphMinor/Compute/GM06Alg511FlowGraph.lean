module

public import GraphMinor.Compute.GM06Alg511Input
public import GraphMinor.Compute.GM06SuccessorGraphRep
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

/-!
# The finite graph for the initial maximum-flow search in VI (5.11)

Checking (5.10)(ii) on page 134 uses vertex-disjoint paths between the
two cuffs. Read consecutive endpoint labels from the supplied array.
For this search, forget loops and identify parallel edges. Adjacency
between distinct labels is exactly adjacency in the original graph.
The proof retains the supplied vertex and edge bijections, so no
geometric choices enter the finite graph sent to maximum flow.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the supplied consecutive endpoint pairs. An unmatched last
word is ignored. Valid drawing inputs have no unmatched word. -/
def gm06Alg511ReadPairs : List ℕ → List (ℕ × ℕ)
  | a :: b :: rest => (a, b) :: gm06Alg511ReadPairs rest
  | _ => []

/-- Reading the endpoint words recovers every edge position, including
loops and repeated endpoint pairs. -/
theorem gm06Alg511ReadPairs_endpointWords (pairs : List (ℕ × ℕ)) :
    gm06Alg511ReadPairs (gm06EndpointWords pairs) = pairs := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simpa only [gm06EndpointWords, List.flatMap_cons, List.cons_append,
      List.nil_append, gm06Alg511ReadPairs, List.cons.injEq, true_and] using ih

/-- The simple graph used only for finding an initial cuff-to-cuff linkage. -/
def GM06Alg511Input.flowGraph (x : GM06Alg511Input) : SimpleGraph (Fin x.vertexCount) where
  Adj a b := a ≠ b ∧
    ((a.val, b.val) ∈ gm06Alg511ReadPairs x.endpoints ∨
      (b.val, a.val) ∈ gm06Alg511ReadPairs x.endpoints)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (x : GM06Alg511Input) : DecidableRel x.flowGraph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∈ _ ∨ _ ∈ _)))

/-- Under the supplied endpoint interpretation, the flow graph has
exactly the non-loop adjacencies of the actual graph. -/
theorem GM06Alg511Input.flowGraph_adj_iff (x : GM06Alg511Input)
    {α : Type*} {β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G)
    (a b : Fin x.vertexCount) :
    x.flowGraph.Adj a b ↔ a ≠ b ∧ G.Adj (rep.vertex a).val (rep.vertex b).val := by
  have hend : x.endpoints = gm06EndpointWords
      (rep.pairs.map fun p => (p.1.val, p.2.val)) := rep.endpoints
  have hpairs : gm06Alg511ReadPairs x.endpoints =
      rep.pairs.map (fun p => (p.1.val, p.2.val)) := by
    rw [hend, gm06Alg511ReadPairs_endpointWords]
  change (a ≠ b ∧ ((a.val, b.val) ∈ gm06Alg511ReadPairs x.endpoints ∨
      (b.val, a.val) ∈ gm06Alg511ReadPairs x.endpoints)) ↔ _
  rw [hpairs]
  constructor
  · rintro ⟨hne, h | h⟩
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp h
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
      have hpa : p.1 = a := Fin.ext (congrArg Prod.fst he)
      have hpb : p.2 = b := Fin.ext (congrArg Prod.snd he)
      have hl := rep.link j
      rw [show rep.pairs[j.val] = p from hj, hpa, hpb] at hl
      exact ⟨hne, ⟨(rep.edge j).val, hl⟩⟩
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp h
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hp
      have hpa : p.1 = b := Fin.ext (congrArg Prod.fst he)
      have hpb : p.2 = a := Fin.ext (congrArg Prod.snd he)
      have hl := rep.link j
      rw [show rep.pairs[j.val] = p from hj, hpa, hpb] at hl
      exact ⟨hne, ⟨(rep.edge j).val, hl.symm⟩⟩
  · rintro ⟨hne, e, he⟩
    obtain ⟨j, hj⟩ := rep.edge.surjective ⟨e, he.edge_mem⟩
    have hje : (rep.edge j).val = e := congrArg Subtype.val hj
    have hl := rep.link j
    rw [hje] at hl
    have hends := hl.eq_and_eq_or_eq_and_eq he
    have hinj : Function.Injective (fun i => (rep.vertex i).val) :=
      Subtype.val_injective.comp rep.vertex.injective
    refine ⟨hne, ?_⟩
    rcases hends with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left
      apply List.mem_map.mpr
      refine ⟨rep.pairs[j.val], List.getElem_mem j.isLt, ?_⟩
      rw [hinj ha, hinj hb]
    · right
      apply List.mem_map.mpr
      refine ⟨rep.pairs[j.val], List.getElem_mem j.isLt, ?_⟩
      rw [hinj ha, hinj hb]

end GraphMinor.Compute
