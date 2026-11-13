module

public import GraphMinor.Compute.FolioStatement
import GraphMinor.Compute.FolioReduction
import GraphMinor.Compute.DPToDCS
import GraphMinor.Compute.GM13ProgramsClosed
import GraphMinor.Compute.Join13

/-! The proved XIII programs supply folio computation. The established reductions
then give connected-subgraph and disjoint-path algorithms without statement inputs. -/

public section
namespace GraphMinor.Compute

/-- The proved (4.1) and (9.9) programs supply the folio assembly. -/
theorem folioStatement_proved (δ ξ : ℕ) : FolioStatement δ ξ :=
  folioStatement_of_claim41_and_algorithm99 claim41_proved gm13_algorithm_9_9 δ ξ

/-- The zero-detail folio algorithm supplies the connected-subgraph reduction. -/
theorem dcs_of_zero_folio_proved : DisjointConnectedSubgraphsStatement :=
  dcs_of_zero_folio (folioStatement_proved 0)

/-- Disjoint paths follow from the proved zero-detail folio programs. -/
theorem dp_of_zero_folio_proved : DisjointPathsStatement :=
  dp_of_zero_folio (folioStatement_proved 0)

/-- Disjoint paths follow from the proved folio programs. -/
theorem dp_of_folio_proved : DisjointPathsStatement :=
  dp_of_folio folioStatement_proved

/-- The connected-subgraph algorithm supplies the disjoint-path reduction. -/
theorem dp_of_dcs_proved : DisjointPathsStatement :=
  dp_of_dcs dcs_of_zero_folio_proved

end GraphMinor.Compute
