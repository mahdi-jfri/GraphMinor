module

public import GraphMinor.GM06.Alg511NormalizedEdge
public import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Adding the finite turn data along a simple walk

For the winding computation in VI (5.11), page 134, sum the interpreted
integer edge labels in traversal order. Join the oriented edge paths
provided by the normalized geometric input. Internal reference angles
cancel at each join. The resulting curve lies in the walk drawing
and has the computed relative turn. Simplicity excludes loop edges,
whose turn entries are not used by the algorithm.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set Real

/-- Integer turn sum of an actual graph walk under the supplied edge
interpretation. This is the mathematical counterpart of the dart sum. -/
noncomputable def alg511InterpretedWalkTurn {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ) :
    ∀ {u v : ClosedCylinder}, GraphWalk G.toGraph u v → ℤ
  | _, _, .nil _ => 0
  | _, _, .cons he W => alg511InterpretedEdgeTurn rep turns he + alg511InterpretedWalkTurn rep turns W

/-- The sum of the edge turns describes a path through every simple
walk, for the same reference-angle witnesses as the supplied input. -/
theorem alg511_normalized_walk_paths {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (turns : List ℤ) (hrep : Alg511NormalizedTurnsRep rep turns) :
    ∃ reference : ClosedCylinder → ℝ,
      (∀ p, Circle.exp (reference p) = p.val.2) ∧
      (∀ i : Fin x.pathCount,
        reference (cylinderM1Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
      (∀ i : Fin x.pathCount,
        reference (cylinderM2Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
      ∀ {u v : ClosedCylinder} (W : GraphWalk G.toGraph u v), W.IsSimple →
        ∃ p : Path u v, range p ⊆ (walkDrawing G W).U ∧
          Alg511RelativeCurveTurn p.toContinuousMap (reference u) (reference v)
            (alg511InterpretedWalkTurn rep turns W) := by
  obtain ⟨reference, hexp, hM1, hM2, hedge⟩ := alg511_normalized_edge_paths rep turns hrep
  refine ⟨reference, hexp, hM1, hM2, ?_⟩
  intro u v W
  induction W with
  | @nil u hu =>
    intro _
    refine ⟨Path.refl _, ?_, ?_⟩
    · rintro z ⟨t, rfl⟩
      apply (mem_walkDrawing_U G (.nil hu)).mpr
      exact Or.inl (by simp)
    · apply alg511_relative_curveTurn_iff.mpr
      have hc : Curve.IsConstant (Path.refl u).toContinuousMap := ⟨u, fun _ => rfl⟩
      rw [windingNumber_const hc]
      simp [alg511InterpretedWalkTurn]
  | @cons u c v e he W ih =>
    intro hs
    have hnd : (u :: W.support).Nodup := hs
    have huc : u ≠ c := fun h =>
      (List.nodup_cons.mp hnd).1 (h ▸ W.start_mem_support)
    obtain ⟨p, hpRange, hpTurn⟩ := hedge he huc
    obtain ⟨q, hqRange, hqTurn⟩ := ih (List.nodup_cons.mp hnd).2
    refine ⟨p.trans q, ?_, alg511_relative_curveTurn_trans p q hpTurn hqTurn⟩
    rw [Path.trans_range]
    apply union_subset
    · intro z hz
      apply (mem_walkDrawing_U G (.cons he W)).mpr
      exact Or.inr ⟨e, by simp, hpRange ▸ hz⟩
    · intro z hz
      apply (mem_walkDrawing_U G (.cons he W)).mpr
      rcases (mem_walkDrawing_U G W).mp (hqRange hz) with hV | ⟨f, hf, hzf⟩
      · exact Or.inl (by simp [hV])
      · exact Or.inr ⟨f, by simp [hf], hzf⟩

end GraphMinor.GM06
