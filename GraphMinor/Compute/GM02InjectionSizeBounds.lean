module

public import GraphMinor.Compute.GM02InjectedInputLength
import Mathlib.Tactic.Linarith

/-!
# Linear size bounds for the labelled candidate inputs

For a fixed pattern, each candidate adds a fixed number of words to
the host's edge-list encoding. A fixed multiple of one plus the host
size bounds the resulting length, including on an empty host.
-/

public section
namespace GraphMinor.Compute

/-- A fixed factor bounds every constructed labelled input length by the host size plus one. -/
theorem gm02InjectedInputLength_le_linear (G H : GM02EdgeListInput) :
    gm02InjectedInputLength G H ≤ (6 + H.n + 2 * H.edges.length) * (G.size + 1) := by
  unfold gm02InjectedInputLength GM02EdgeListInput.size
  nlinarith [Nat.zero_le ((H.n + 2 * H.edges.length) * (G.n + G.edges.length))]

end GraphMinor.Compute
