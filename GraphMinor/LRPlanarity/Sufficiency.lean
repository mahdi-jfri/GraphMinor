module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.ContourDrawing

/-!
# Sufficiency of an aligned fork coloring

Part IV of `docs/planarity/planarity_test.tex` shows that an aligned fork coloring gives a plane
embedding. Sections 2 to 4 build the signed contour from the coloring and show that its port
pairs do not alternate. This is `SignedContourStatement`, a hypothesis here. Section 5 turns a
nonalternating contour into a plane drawing. This is `contourDrawing_proved`
(`ContourDrawing.lean`), proved without hypotheses.
-/

public section

namespace GraphMinor.LRPlanarity

/-- Part IV, Sections 1 to 5 of `docs/planarity/planarity_test.tex`: a coloring that satisfies all
fork constraints and all weak alignments gives a plane embedding. The signed contour of
Sections 2 to 4 is valid and nonalternating by the hypothesis `hSC`, and Section 5
(`contourDrawing_proved`) draws it. -/
theorem sufficiencyStatement_of (hSC : SignedContourStatement) : SufficiencyStatement := by
  intro N G T color hT hFork hAlign
  obtain ⟨hValid, hPort, hNon⟩ := hSC N G T color hT hFork hAlign
  obtain ⟨drawing, -⟩ :=
    contourDrawing_proved N G T (signedContourOrder T G color) hT hValid hPort hNon
  exact ⟨drawing⟩

end GraphMinor.LRPlanarity
