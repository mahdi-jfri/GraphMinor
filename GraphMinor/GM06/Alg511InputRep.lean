module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511FiniteFeasible
public import GraphMinor.GM06.Alg511NormalizedTurns
import GraphMinor.GM06.Alg511FiniteSound
import GraphMinor.GM06.Alg511FiniteComplete
import GraphMinor.GM06.Section5Red
import GraphMinor.Compute.GM06Alg511FlowGraph
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# The graph and turn input determines absolute feasibility

Interpret the supplied vertex and edge labels, the ordered cuff lists,
and the normalized integer edge turns by actual geometry. These are
input correspondence conditions, not a linkage or a feasibility claim.
The finite path predicate is equivalent to actual feasibility in both
directions. The endpoint rows uniquely determine the finite edge list,
and the cuff rows uniquely determine their label maps. Consequently
any two drawings represented by the same supplied data have exactly
the same feasible windings, as required for VI (5.11), page 134.

Rotation and region-boundary fields are not interpreted by this
relation. They remain separate inputs to the successor program.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Graph incidence, ordered cuffs and normalized edge-turn
interpretation of a supplied finite cylinder input. -/
structure GM06Alg511GraphTurnRep (x : GM06Alg511WindingInput) (G : Drawing ClosedCylinder) where
  graph : GM06SuccessorGraphRep (x.drawing.withLinkage []) G.toGraph
  source : Fin x.drawing.pathCount → Fin x.drawing.vertexCount
  target : Fin x.drawing.pathCount → Fin x.drawing.vertexCount
  inner : x.drawing.innerCuff = List.ofFn (fun i => (source i).val)
  outer : x.drawing.outerCuff = List.ofFn (fun i => (target i).val)
  source_point : ∀ i, (graph.vertex (source i)).val = cylinderM1Point x.drawing.pathCount i
  target_point : ∀ i, (graph.vertex (target i)).val = cylinderM2Point x.drawing.pathCount i
  turns : Alg511NormalizedTurnsRep graph x.edgeTurns

namespace GM06Alg511GraphTurnRep

/-- The ordered inner cuff words have exactly their stated geometric membership. -/
theorem inner_mem_iff {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (a : Fin x.drawing.vertexCount) :
    a.val ∈ x.drawing.innerCuff ↔ (rep.graph.vertex a).val ∈ cylinderM1 x.drawing.pathCount := by
  rw [rep.inner, List.mem_ofFn]
  have hinj : Function.Injective (fun j => (rep.graph.vertex j).val) :=
    Subtype.val_injective.comp rep.graph.vertex.injective
  constructor
  · rintro ⟨i, hi⟩
    have he : rep.source i = a := Fin.ext hi
    exact ⟨i, (rep.source_point i).symm.trans (congrArg (fun j => (rep.graph.vertex j).val) he)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, congrArg Fin.val (hinj ((rep.source_point i).trans hi))⟩

/-- The ordered outer cuff words have exactly their stated geometric membership. -/
theorem outer_mem_iff {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (a : Fin x.drawing.vertexCount) :
    a.val ∈ x.drawing.outerCuff ↔ (rep.graph.vertex a).val ∈ cylinderM2 x.drawing.pathCount := by
  rw [rep.outer, List.mem_ofFn]
  have hinj : Function.Injective (fun j => (rep.graph.vertex j).val) :=
    Subtype.val_injective.comp rep.graph.vertex.injective
  constructor
  · rintro ⟨i, hi⟩
    have he : rep.target i = a := Fin.ext hi
    exact ⟨i, (rep.target_point i).symm.trans (congrArg (fun j => (rep.graph.vertex j).val) he)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, congrArg Fin.val (hinj ((rep.target_point i).trans hi))⟩

/-- Distinct prescribed cuff points have distinct supplied source labels. -/
theorem source_injective {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount) :
    Function.Injective rep.source := by
  intro i j hij
  apply cylinderM1Point_injective hk
  rw [← rep.source_point i, ← rep.source_point j, hij]

/-- The requested path count is at most the number of supplied vertices. -/
theorem pathCount_le_vertexCount {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount) :
    x.drawing.pathCount ≤ x.drawing.vertexCount := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective rep.source (rep.source_injective hk)

/-- Actual feasibility is exactly the finite path predicate on the
supplied edge, cuff and turn labels. -/
theorem feasible_iff_finite {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount) (theta : ℝ) :
    IsThetaFeasible x.drawing.pathCount G theta ↔
      GM06Alg511FiniteFeasible rep.graph.pairs x.edgeTurns rep.source rep.target theta := by
  exact ⟨alg511_finite_of_feasible hk rep.graph x.edgeTurns rep.turns rep.source rep.target
      rep.source_point rep.target_point theta,
    alg511_feasible_of_finite hk rep.graph x.edgeTurns rep.turns rep.source rep.target
      rep.source_point rep.target_point theta⟩

private theorem pairs_eq {x : GM06Alg511WindingInput} {G H : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (rep' : GM06Alg511GraphTurnRep x H) :
    rep.graph.pairs = rep'.graph.pairs := by
  have he := rep.graph.endpoints.symm.trans rep'.graph.endpoints
  have hp := congrArg gm06Alg511ReadPairs he
  simp only [gm06Alg511ReadPairs_endpointWords] at hp
  have hinj : Function.Injective
      (fun p : Fin x.drawing.vertexCount × Fin x.drawing.vertexCount => (p.1.val, p.2.val)) := by
    intro p q h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  exact (List.map_injective_iff.mpr hinj) hp

private theorem source_eq {x : GM06Alg511WindingInput} {G H : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (rep' : GM06Alg511GraphTurnRep x H) :
    rep.source = rep'.source := by
  have he := List.ofFn_injective (rep.inner.symm.trans rep'.inner)
  funext i
  exact Fin.ext (congrFun he i)

private theorem target_eq {x : GM06Alg511WindingInput} {G H : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (rep' : GM06Alg511GraphTurnRep x H) :
    rep.target = rep'.target := by
  have he := List.ofFn_injective (rep.outer.symm.trans rep'.outer)
  funext i
  exact Fin.ext (congrFun he i)

/-- The supplied finite data determine every feasible winding,
independently of the drawing realizing those data. -/
theorem feasible_iff {x : GM06Alg511WindingInput} {G H : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (rep' : GM06Alg511GraphTurnRep x H)
    (hk : 0 < x.drawing.pathCount) (theta : ℝ) :
    IsThetaFeasible x.drawing.pathCount G theta ↔ IsThetaFeasible x.drawing.pathCount H theta := by
  rw [rep.feasible_iff_finite hk theta, rep'.feasible_iff_finite hk theta]
  rw [pairs_eq rep rep', source_eq rep rep', target_eq rep rep']

end GM06Alg511GraphTurnRep
end GraphMinor.GM06
