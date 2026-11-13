module

public import GraphMinor.Compute.GM02InjectedPattern
import GraphMinor.Compute.GM02TopologicalEncoding

/-!
# Size bounds independent of the chosen injection

Changing the injection changes only vertex and endpoint words. Both
the graph-pair size and its encoding length depend only on the host
counts and the fixed pattern counts. Thus every candidate can use the
same allocation, time, and logarithmic word bounds.
-/

public section
namespace GraphMinor.Compute

/-- The length of each constructed labelled input. -/
@[expose] def gm02InjectedInputLength (G H : GM02EdgeListInput) : ℕ :=
  4 + 2 * G.edges.length + H.n + 2 * H.edges.length

/-- Every injection has the same ordinary labelled encoding length. -/
theorem gm02InjectedPattern_enc_length (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) :
    (gm02InjectedPattern G H f).enc.length = gm02InjectedInputLength G H := by
  rw [GM02TopologicalInput.enc_length, gm02InjectedPattern_vertices_card,
    gm02InjectedPattern_edges_length]
  rfl

end GraphMinor.Compute
