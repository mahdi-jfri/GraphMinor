module

public import GraphMinor.GM06.Alg57CandidateGraph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The candidate graph with labels

The search `FIND_4` of the Word RAM program (`gm06Find4`, with `gm06Find4_sound` and
`gm06Find4_none_iff`) runs a breadth-first search in a simple graph on vertex labels `Fin n`
(`gm06CandidateGraph`). Its answer is reachability in that graph. Here we connect that reachability
with the candidate graph `A_{i,v}` of the drawing (`IsReduction4CandidateVertex`,
`IsReduction4CandidateEdge`).

The interface is one hypothesis on the labelled graph `H`: two different labels are adjacent
exactly when their vertices are linked by a candidate edge (`Reduction4CandidateStep`). This is
what `gm06CandidateEdges_mem_iff` gives once the lists `ends`, `incV`, `incE`, `upper`
and `path` represent the drawing. Loops and parallel edges do not matter for reachability.

* `exists_candidate_walk_iff_reflTransGen`: a walk in `A_{i,v}` is a chain of candidate steps.
* `reachable_iff_reflTransGen_step`: reachability in `H` is a chain of candidate steps.
* `exists_reduction4_path_iff_reachable`: formula (12) with labels. A path `Q` as in Lemma 13
  exists exactly when `sᵢ` is a candidate vertex and its label reaches the label of `v` in `H`.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

variable {k : ℕ} {G : Drawing ClosedCylinder}

/-- One step of the candidate graph `A_{i,v}`: a candidate edge linking `x` and `y`. -/
@[expose] def Reduction4CandidateStep (L : CylinderLinkage k G) (i : Fin k) (T : Drawing ClosedCylinder)
    (v x y : ClosedCylinder) : Prop :=
  ∃ e, IsReduction4CandidateEdge L i T v e ∧ G.toGraph.IsLink e x y

/-- Both ends of a candidate step are candidate vertices. -/
theorem Reduction4CandidateStep.vertices {L : CylinderLinkage k G} {i : Fin k}
    {T : Drawing ClosedCylinder} {v x y : ClosedCylinder}
    (h : Reduction4CandidateStep L i T v x y) :
    IsReduction4CandidateVertex L i T v x ∧ IsReduction4CandidateVertex L i T v y := by
  obtain ⟨e, he, hl⟩ := h
  have hends : closure e ∩ G.V = {x, y} := hl.2.2.2
  exact ⟨he.2.2 x (hends ▸ mem_insert _ _),
    he.2.2 y (hends ▸ mem_insert_of_mem _ (mem_singleton _))⟩

/-- A walk of `G` in the candidate graph is a chain of candidate steps from a candidate vertex. -/
theorem exists_candidate_walk_iff_reflTransGen (L : CylinderLinkage k G) (i : Fin k)
    (T : Drawing ClosedCylinder) (v a b : ClosedCylinder) :
    (∃ W : GraphWalk G.toGraph a b,
        (∀ x ∈ W.support, IsReduction4CandidateVertex L i T v x) ∧
        ∀ e ∈ W.edges, IsReduction4CandidateEdge L i T v e) ↔
      IsReduction4CandidateVertex L i T v a ∧
        Relation.ReflTransGen (Reduction4CandidateStep L i T v) a b := by
  constructor
  · rintro ⟨W, hV, hE⟩
    refine ⟨hV a W.start_mem_support, ?_⟩
    clear hV
    induction W with
    | nil _ => exact Relation.ReflTransGen.refl
    | @cons u x w e hlink rest ih =>
      refine Relation.ReflTransGen.head ⟨e, hE e (List.mem_cons_self), hlink⟩ ?_
      exact ih fun e he => hE e (List.mem_cons_of_mem _ he)
  · rintro ⟨ha, h⟩
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      refine ⟨GraphWalk.nil ha.1, fun x hx => ?_, by simp [GraphWalk.edges]⟩
      rw [List.mem_singleton.mp hx]
      exact ha
    | head hstep _ ih =>
      obtain ⟨e, he, hl⟩ := hstep
      obtain ⟨W, hV, hE⟩ := ih (Reduction4CandidateStep.vertices ⟨e, he, hl⟩).2
      refine ⟨GraphWalk.cons hl W, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (Reduction4CandidateStep.vertices ⟨e, he, hl⟩).1
        · exact hV x hx
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact he
        · exact hE e' he'

/-- **Labels.** Let `H` be a simple graph on distinct labels whose adjacency is exactly a candidate step
between different labels, and let every candidate vertex have a label. Then reachability in `H`
is a chain of candidate steps between the labelled vertices. -/
theorem reachable_iff_reflTransGen_step (L : CylinderLinkage k G) (i : Fin k)
    (T : Drawing ClosedCylinder) (v : ClosedCylinder) {n : ℕ} (H : SimpleGraph (Fin n))
    {lab : Fin n → ClosedCylinder} (hinj : Function.Injective lab)
    (hcov : ∀ x, IsReduction4CandidateVertex L i T v x → ∃ y, lab y = x)
    (hadj : ∀ u w, H.Adj u w ↔ u ≠ w ∧ Reduction4CandidateStep L i T v (lab u) (lab w))
    (a b : Fin n) :
    H.Reachable a b ↔ Relation.ReflTransGen (Reduction4CandidateStep L i T v) (lab a) (lab b) := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ huw ih => exact ih.tail ((hadj _ _).mp huw).2
  · intro h
    have key : ∀ z, Relation.ReflTransGen (Reduction4CandidateStep L i T v) (lab a) z →
        ∀ c, lab c = z → Relation.ReflTransGen H.Adj a c := by
      intro z hz
      induction hz with
      | refl =>
        intro c hc
        rw [hinj hc]
      | tail _ hstep ih =>
        intro c hc
        obtain ⟨c', hc'⟩ := hcov _ hstep.vertices.1
        have h1 := ih c' hc'
        by_cases hcc : c' = c
        · rw [← hcc]; exact h1
        · refine h1.tail ((hadj c' c).mpr ⟨hcc, ?_⟩)
          rw [hc', hc]
          exact hstep
    exact key _ h b rfl

/-- **Formula (12) with labels** (`k ≥ 2`). For a contact `v ≠ sᵢ` with tail `T`, and a labelled
graph `H` representing the candidate graph as in `reachable_iff_reflTransGen_step`, a path `Q`
as in Lemma 13 exists exactly when `sᵢ` is a candidate vertex and the label of `sᵢ` reaches the
label of `v` in `H`. -/
theorem exists_reduction4_path_iff_reachable (L : CylinderLinkage k G) (i : Fin k)
    {T : Drawing ClosedCylinder} (hTG : T.IsSubdrawing G) {v : ClosedCylinder}
    (hsv : cylinderM1Point k i ≠ v) {n : ℕ} (H : SimpleGraph (Fin n))
    {lab : Fin n → ClosedCylinder} (hinj : Function.Injective lab)
    (hcov : ∀ x, IsReduction4CandidateVertex L i T v x → ∃ y, lab y = x)
    (hadj : ∀ u w, H.Adj u w ↔ u ≠ w ∧ Reduction4CandidateStep L i T v (lab u) (lab w))
    {a b : Fin n} (ha : lab a = cylinderM1Point k i) (hb : lab b = v) :
    (∃ Q : Drawing ClosedCylinder, Q.IsSubdrawing G ∧
        IsPathDrawing Q (cylinderM1Point k i) v ∧ Q.U ⊆ closure (cylinderRegion k G i) ∧
        Q.U ∩ T.U ⊆ {v} ∧ ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U) ↔
      IsReduction4CandidateVertex L i T v (cylinderM1Point k i) ∧ H.Reachable a b := by
  rw [exists_candidate_walk_iff L i hTG hsv, exists_candidate_walk_iff_reflTransGen,
    reachable_iff_reflTransGen_step L i T v H hinj hcov hadj, ha, hb]

end GraphMinor.GM06
