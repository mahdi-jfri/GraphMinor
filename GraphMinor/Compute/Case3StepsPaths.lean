module

public import GraphMinor.Compute.Case3StepsLift

/-!
# Paths in lifted division members

Conditions (iii) and (iv) of a division in Graph Minors XIII, Section 8,
page 96, require paths. For every edge of a simple path we choose one of its
multigraph copies. The resulting path has exactly the same vertices, renamed
by `Fin.val`. Thus the operation preserves disjointness and avoidance of
boundary vertices.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.Surface GraphMinor.GM09

/-- A simple member edge has a chosen multigraph copy in the lifted member. -/
theorem case3LiftLink {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    {e : Sym2 (Fin n)} {u v : Fin n} (hlink : A.toGMGraph.IsLink e u v) :
    (case3LiftMember D A loops).IsLink
      (adjEdgeTriple (case3MemberMultiDigraph D A loops) u v) u.1 v.1 := by
  have hadj := (A.isLink_toGMGraph_iff.mp hlink).2
  have hMD : (case3MemberMultiDigraph D A loops).toSimpleGraph.Adj u v := by
    rw [case3MemberMultiDigraph_toSimpleGraph]
    exact hadj
  have hu := A.adj_verts u v hadj
  exact ⟨isLink_adjEdgeTriple hMD, ⟨u, hu.1, rfl⟩, ⟨v, hu.2, rfl⟩⟩

/-- Lift a walk in a simple member by choosing one copy of each traversed edge. -/
noncomputable def case3LiftWalk {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    {P : Graph (Fin n) (Sym2 (Fin n))} (hP : P ≤ A.toGMGraph) :
    ∀ {a b : Fin n}, GraphWalk P a b → GraphWalk (case3LiftMember D A loops) a.1 b.1
  | _, _, .nil hu => .nil ⟨_, hP.vertexSet_mono hu, rfl⟩
  | _, _, .cons hl rest => .cons (case3LiftLink D A loops (hl.mono hP))
      (case3LiftWalk D A loops hP rest)

/-- Lifting a walk changes its labels but neither its vertex list nor its order. -/
theorem case3LiftWalk_support {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    {P : Graph (Fin n) (Sym2 (Fin n))} (hP : P ≤ A.toGMGraph)
    {a b : Fin n} (W : GraphWalk P a b) :
    (case3LiftWalk D A loops hP W).support = W.support.map Fin.val := by
  induction W with
  | nil => rfl
  | cons hl rest ih =>
    change _ :: (case3LiftWalk D A loops hP rest).support = _ :: _
    rw [ih]

/-- A path in a simple member lifts to a path with exactly the renamed vertex
set. In particular, no extra boundary vertex is introduced. -/
theorem case3LiftPath {n : ℕ} (D : MultiDigraph n)
    (A : Alg86Subgraph D.toSimpleGraph) (loops : Finset (Fin n))
    {P : Graph (Fin n) (Sym2 (Fin n))} {a b : Fin n}
    (hP : IsGraphPathWithEnds A.toGMGraph P a b) :
    ∃ Q : Graph ℕ (ℕ × ℕ × ℕ),
      IsGraphPathWithEnds (case3LiftMember D A loops) Q a.1 b.1 ∧
        V(Q) = Fin.val '' V(P) := by
  obtain ⟨hsub, W, hsimple, hverts, _⟩ := hP
  let W' := case3LiftWalk D A loops hsub W
  have hs : W'.IsSimple := by
    change W'.support.Nodup
    rw [case3LiftWalk_support]
    exact hsimple.map Fin.val_injective
  refine ⟨walkSubgraph W', isGraphPathWithEnds_walkSubgraph hs, ?_⟩
  rw [vertexSet_walkSubgraph, case3LiftWalk_support, hverts]
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_image]

/-- The lifted graph determines its simple member, independently of the loop
assignment. This ensures that renaming the members is a bijection. -/
theorem case3LiftMember_eq_imp {n : ℕ} (D : MultiDigraph n)
    {A B : Alg86Subgraph D.toSimpleGraph} (loopsA loopsB : Finset (Fin n))
    (hAB : case3LiftMember D A loopsA = case3LiftMember D B loopsB) : A = B := by
  have hV : Fin.val '' (A.verts : Set (Fin n)) = Fin.val '' (B.verts : Set (Fin n)) :=
    congrArg Graph.vertexSet hAB
  have hv : A.verts = B.verts :=
    Finset.coe_inj.mp (Set.image_injective.mpr Fin.val_injective hV)
  have hadj : ∀ (A B : Alg86Subgraph D.toSimpleGraph) (LA LB : Finset (Fin n)),
      case3LiftMember D A LA = case3LiftMember D B LB →
      ∀ u v, A.graph.Adj u v → B.graph.Adj u v := by
    intro A B LA LB heq u v huv
    have hl := case3LiftLink D A LA
      ((A.isLink_toGMGraph_iff).mpr ⟨rfl, huv⟩)
    rw [heq] at hl
    have hMD := WallOfHeight.adj_toSimpleGraph_of_isLink_toGMDigraph hl.1
      (show (⟨u.1, hl.1.left_mem⟩ : Fin n) ≠ ⟨v.1, hl.1.right_mem⟩ from
        fun h => (A.graph.ne_of_adj huv) h)
    rw [case3MemberMultiDigraph_toSimpleGraph] at hMD
    exact hMD
  ext u v
  · exact Finset.ext_iff.mp hv u
  · exact ⟨hadj A B loopsA loopsB hAB u v, hadj B A loopsB loopsA hAB.symm u v⟩

private def case3WholeSimpleMember {n : ℕ} (D : MultiDigraph n) :
    Alg86Subgraph D.toSimpleGraph where
  verts := Finset.univ
  graph := D.toSimpleGraph
  sub := le_rfl
  adj_verts _ _ _ := ⟨Finset.mem_univ _, Finset.mem_univ _⟩

private theorem case3WholeSimpleMember_toGMGraph {n : ℕ} (D : MultiDigraph n) :
    (case3WholeSimpleMember D).toGMGraph = Graph.ofSimpleGraph D.toSimpleGraph := by
  apply Graph.ext
  · exact Set.ext (fun _ => by simp [case3WholeSimpleMember, Alg86Subgraph.vertexSet_toGMGraph])
  · intro e u v
    rw [Alg86Subgraph.isLink_toGMGraph_iff]
    change (e = s(u, v) ∧ D.toSimpleGraph.Adj u v) ↔
      (e = s(u, v) ∧ e ∈ D.toSimpleGraph.edgeSet)
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, D.toSimpleGraph.mem_edgeSet.mpr h⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, D.toSimpleGraph.mem_edgeSet.mp h⟩

/-- A path in the simple graph underlying the whole multigraph lifts with the
same vertex set. This supplies the paths from member boundaries to the society
boundary in condition (iii). -/
theorem case3LiftPath_ambient {n : ℕ} (D : MultiDigraph n)
    {P : Graph (Fin n) (Sym2 (Fin n))} {a b : Fin n}
    (hP : IsGraphPathWithEnds (Graph.ofSimpleGraph D.toSimpleGraph) P a b) :
    ∃ Q : Graph ℕ (ℕ × ℕ × ℕ),
      IsGraphPathWithEnds D.toGMDigraph.toGraph Q a.1 b.1 ∧ V(Q) = Fin.val '' V(P) := by
  have hP' : IsGraphPathWithEnds (case3WholeSimpleMember D).toGMGraph P a b := by
    rw [case3WholeSimpleMember_toGMGraph]
    exact hP
  obtain ⟨Q, hQ, hV⟩ := case3LiftPath D (case3WholeSimpleMember D) ∅ hP'
  exact ⟨Q, hQ.mono (case3LiftMember_le D (case3WholeSimpleMember D) ∅), hV⟩

end GraphMinor.Compute
