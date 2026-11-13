module

public import GraphMinor.Compute.GM06Alg34VertexGraph
public import GraphMinor.Compute.GM06Alg34MatrixMarks
public import GraphMinor.Compute.Graph

/-!
# The adjacency matrix computed from supplied endpoints

For each non-loop edge, mark its two directed matrix entries. Repeated
parallel edges simply mark the same positions again. The folded row
writer therefore yields exactly the adjacency matrix of the finite
vertex graph, without enumerating geometric edges or choosing witnesses.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Two row marks for a supplied non-loop edge, and no marks for a loop. -/
def gm06VertexEdgeRows {n : ℕ} (e : Fin n × Fin n) : List (ℕ × List ℕ) :=
  if e.1 = e.2 then [] else [(e.1.val, [e.2.val]), (e.2.val, [e.1.val])]

private theorem edge_rows_incidence {n : ℕ} (e : Fin n × Fin n) (a b : Fin n) :
    (∃ p ∈ gm06VertexEdgeRows e, p.1 = a.val ∧ b.val ∈ p.2) ↔
      a ≠ b ∧ (e = (a, b) ∨ e = (b, a)) := by
  by_cases he : e.1 = e.2
  · simp only [gm06VertexEdgeRows, he, ↓reduceIte, List.not_mem_nil, false_and,
      exists_false, false_iff, not_and, not_or]
    intro hab
    constructor <;> intro hpair
    · have hh := congrArg Prod.fst hpair
      have ht := congrArg Prod.snd hpair
      exact hab (hh.symm.trans (he.trans ht))
    · have hh := congrArg Prod.fst hpair
      have ht := congrArg Prod.snd hpair
      exact hab (ht.symm.trans (he.symm.trans hh))
  · simp only [gm06VertexEdgeRows, he, ↓reduceIte, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_singleton]
    constructor
    · rintro ⟨p, hp, hpa, hpb⟩
      rcases hp with rfl | rfl
      · have ha : e.1 = a := Fin.ext hpa
        have hb : b = e.2 := Fin.ext (List.mem_singleton.mp hpb)
        refine ⟨?_, Or.inl (Prod.ext ha hb.symm)⟩
        intro hab
        exact he (ha.trans (hab.trans hb))
      · have ha : e.2 = a := Fin.ext hpa
        have hb : b = e.1 := Fin.ext (List.mem_singleton.mp hpb)
        refine ⟨?_, Or.inr (Prod.ext hb.symm ha)⟩
        intro hab
        exact he (hb.symm.trans (hab.symm.trans ha.symm))
    · rintro ⟨_, hpair | hpair⟩
      · subst e
        exact ⟨(a.val, [b.val]), Or.inl rfl, rfl, List.mem_singleton_self _⟩
      · subst e
        exact ⟨(a.val, [b.val]), Or.inr rfl, rfl, List.mem_singleton_self _⟩

/-- The finite adjacency matrix obtained by marking the supplied edges. -/
def gm06VertexMatrixData (x : GM06DrawingData) : List ℕ :=
  (x.ends.flatMap gm06VertexEdgeRows).foldl (gm06MatrixMarkRow x.n)
    (List.replicate (x.n * x.n) 0)

/-- The endpoint-marking matrix has exactly the allocated square size. -/
theorem gm06VertexMatrixData_length (x : GM06DrawingData) :
    (gm06VertexMatrixData x).length = x.n * x.n := by
  simp only [gm06VertexMatrixData, gm06MatrixMarkRows_length, List.length_replicate]

/-- The exact finite endpoint marks give the vertex graph's adjacency matrix. -/
theorem gm06VertexMatrixData_isAdjMatrixList (x : GM06DrawingData) :
    IsAdjMatrixList x.vertexGraph (gm06VertexMatrixData x) := by
  refine ⟨gm06VertexMatrixData_length x, ?_⟩
  intro a b
  have hcols : ∀ p ∈ x.ends.flatMap gm06VertexEdgeRows, ∀ v ∈ p.2, v < x.n := by
    intro p hp v hv
    obtain ⟨e, _, hp⟩ := List.mem_flatMap.mp hp
    by_cases he : e.1 = e.2
    · simp [gm06VertexEdgeRows, he] at hp
    · simp only [gm06VertexEdgeRows, he, ↓reduceIte, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl
      · have hv' := List.mem_singleton.mp hv
        rw [hv']; exact e.2.isLt
      · have hv' := List.mem_singleton.mp hv
        rw [hv']; exact e.1.isLt
  have hentry := gm06MatrixMarkRows_replicate_getElem x.n
    (x.ends.flatMap gm06VertexEdgeRows) a.val b.val a.isLt b.isLt hcols
  have hinc : (∃ p ∈ x.ends.flatMap gm06VertexEdgeRows, p.1 = a.val ∧ b.val ∈ p.2) ↔
      x.vertexGraph.Adj a b := by
    constructor
    · rintro ⟨p, hp, hpa, hpb⟩
      obtain ⟨e, he, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨hne, hpair⟩ := (edge_rows_incidence e a b).mp ⟨p, hp, hpa, hpb⟩
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
      refine ⟨hne, ⟨i, hi⟩, ?_⟩
      rcases hpair with hpair | hpair
      · exact Or.inl ⟨by simp [heq, hpair], by simp [heq, hpair]⟩
      · exact Or.inr ⟨by simp [heq, hpair], by simp [heq, hpair]⟩
    · rintro ⟨hne, e, he⟩
      have hpair : x.ends[e] = (a, b) ∨ x.ends[e] = (b, a) :=
        he.elim (fun h => Or.inl (Prod.ext h.1.symm h.2.symm))
          (fun h => Or.inr (Prod.ext h.2.symm h.1.symm))
      obtain ⟨p, hp, hpa, hpb⟩ := (edge_rows_incidence x.ends[e] a b).mpr ⟨hne, hpair⟩
      exact ⟨p, List.mem_flatMap.mpr ⟨x.ends[e], List.getElem_mem e.isLt, hp⟩, hpa, hpb⟩
  have haddr : x.n * a.val + b.val = a.val * x.n + b.val := by rw [Nat.mul_comm x.n a.val]
  have he : (gm06VertexMatrixData x)[a.val * x.n + b.val]'(by
      rw [gm06VertexMatrixData_length, Nat.mul_comm a.val x.n]
      exact (Nat.add_lt_add_left b.isLt _).trans_le (by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left x.n a.isLt)) =
      if x.vertexGraph.Adj a b then 1 else 0 := by
    simpa only [gm06VertexMatrixData, haddr, hinc] using hentry
  rw [he]
  by_cases hadj : x.vertexGraph.Adj a b <;> simp [hadj]

end GraphMinor.Compute
