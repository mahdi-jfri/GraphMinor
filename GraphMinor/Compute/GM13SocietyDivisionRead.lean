module

public import GraphMinor.Compute.GM13SocietyDivisionLift
public import GraphMinor.Compute.GM13SocietyInput

/-!
# Reading the restored division

The reader parses the simple member records and the computed loop-owner
indices. Each recorded simple edge denotes its full parallel class in the
original graph. The loop owner is looked up by index. No reachability,
component computation, or member choice is performed by the reader.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph GM13 GM09

/-- Read the merged members from the simple division output. -/
noncomputable def gm13ReadSimpleMembers (x : GM13SocietyInput) (out : List ℕ) :
    List (Alg86Subgraph x.G.toSimpleGraph) :=
  let rest₁ := (decAlg86SubgraphWords x.n out.tail).2
  let rest₂ := (decAlg86PairListWords x.n rest₁).2
  (decAlg86PairListWords x.n rest₂).1.map (alg86SubgraphOfDecoded x.G.toSimpleGraph)

/-- Look up the member receiving the loops at each vertex. -/
noncomputable def gm13ReadLoops {n : ℕ} (D : MultiDigraph n)
    (members : List (Alg86Subgraph D.toSimpleGraph)) (owners : List ℕ)
    (A : Alg86Subgraph D.toSimpleGraph) : Finset (Fin n) :=
  open Classical in
  Finset.univ.filter (fun v => owners.getD v.1 0 ≠ 0 ∧
    members[owners.getD v.1 0 - 1]? = some A)

/-- The actual multigraph division decoded from its records and loop table. -/
noncomputable def gm13ReadRecordedDivision {n : ℕ} (D : MultiDigraph n)
    (members : List (Alg86Subgraph D.toSimpleGraph)) (owners : List ℕ) :
    Set (Graph ℕ (ℕ × ℕ × ℕ)) :=
  (fun A => case3LiftMember D A (gm13ReadLoops D members owners A)) '' {A | A ∈ members}

/-- The complete output predicate refers to the parsed division of the given
multigraph society, with all its loops and parallel edges. -/
def GM13ActualRuralOutput (x : GM13SocietyInput) (s : State) : Prop :=
  IsRuralDivision (case3MultigraphSociety x.G x.omega x.nodup_omega)
    (gm13ReadRecordedDivision x.G (gm13ReadSimpleMembers x (s.arrs 65)) (s.arrs 30))

/-- The reader recovers exactly the merged records, ignoring the supplied
core, raw records, and any output-buffer padding. -/
theorem gm13ReadSimpleMembers_code (x : GM13SocietyInput)
    (core : Finset (Fin x.n) × List (Fin x.n × Fin x.n))
    (raw div : List (Finset (Fin x.n) × List (Fin x.n × Fin x.n))) (suf : List ℕ) :
    gm13ReadSimpleMembers x ([0] ++ encAlg86Subgraph core.1 core.2 ++
      encAlg86PairList raw ++ encAlg86PairList div ++ suf) =
      div.map (alg86SubgraphOfPair x.G.toSimpleGraph) := by
  simp only [gm13ReadSimpleMembers, List.singleton_append, List.cons_append,
    List.nil_append, List.tail_cons, List.append_assoc, decAlg86SubgraphWords_append,
    decAlg86PairListWords_append, List.map_map]
  rfl

/-- Looking up a mapped record is exactly the explicit pair-record lookup. -/
theorem gm13ReadRecordedDivision_map {n : ℕ} (D : MultiDigraph n)
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (owners : List ℕ) :
    gm13ReadRecordedDivision D (L.map (alg86SubgraphOfPair D.toSimpleGraph)) owners =
      gm13RecordedDivision D L owners := by
  have hloops : ∀ A, gm13ReadLoops D (L.map (alg86SubgraphOfPair D.toSimpleGraph)) owners A =
      gm13RecordLoops D L owners A := by
    intro A
    classical
    ext v
    simp only [gm13ReadLoops, gm13RecordLoops, Finset.mem_filter, Finset.mem_univ,
      true_and, List.getElem?_map]
    cases he : L[owners.getD v.1 0 - 1]? <;> simp [he]
  unfold gm13ReadRecordedDivision gm13RecordedDivision gm13RecordFamily
  congr 1
  funext A
  rw [hloops]

end GraphMinor.Compute
