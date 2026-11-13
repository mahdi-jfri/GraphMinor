module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5HelixReduction1
import GraphMinor.GM06.Section5HelixReduction2
import GraphMinor.GM06.Section5HelixReduction3
import GraphMinor.GM06.Section5Helix

/-!
# Helix potential under all four reductions

Graph Minors VI (5.5), page 130, pulls a helix back through each
reduction without increasing its potential. Reduction 1 uses the
paper's last-region-contact surgery, including claim (1). Reduction 2
uses the constructed finite enclosure detours, with clockwise exhaustion
and a cut disc for one path. Reduction 3 lifts through the contraction
and controls attachment visits. Reduction 4 keeps the same drawing.
-/

public section
namespace GraphMinor.GM06

/-- Graph Minors VI (5.5), page 130: every reduction admits a
helix pullback with no increase in potential. The reductions use
the corrections for one path in `corrections/GM06.md`. -/
theorem theorem_5_5_proof : Statement55 := by
  intro k G G' L L' f hG hG' hRed hf
  rcases hRed with h1 | h2 | h3 | h4
  · exact theorem_5_5_red1 L L' hG hG' h1 f hf
  · exact theorem_5_5_red2 L L' hG hG' h2 f hf
  · exact theorem_5_5_red3 L L' hG hG' h3 f hf
  · exact theorem_5_5_red4 k G G' L L' h4 f hf

end GraphMinor.GM06
