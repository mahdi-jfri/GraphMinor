module

public import GraphMinor.Compute.Case3StepsParsedCompass
public import GraphMinor.Compute.Case3StepsCompassLift

/-!
# The parsed society is the original wall society

The block's compass lists restore the compact compass. Its cyclic order
is the order of the four corners of its wall section. These are exactly
the graph and cyclic order of the original-label compass society used in
the rural-division lift.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

private theorem society_eq {S T : GM09.Society ℕ (ℕ × ℕ × ℕ)}
    (hG : S.G = T.G) (hΩ : S.Ω = T.Ω) : S = T := by
  cases S
  cases T
  cases hG
  cases hΩ
  rfl

/-- The compact compass renamed to original labels lies in the deleted
ambient graph of a parsed wall section. -/
theorem case3ParsedWall_compass_le {N : ℕ} (G : MultiDigraph N) (X : Finset (Fin N))
    (pw : ParsedWallSection (G.deleteVertices X) X) :
    relabelGraph (origVertexEmb (compassEmb pw.W) (compassEmb pw.W).injective)
      (origEdgeEmb (compassEmb pw.W) (compassEmb pw.W).injective)
      (case3CompactCompassMultigraph (G.deleteVertices X) pw.W).toGMDigraph.toGraph ≤
        delGraph G X := by
  have hs := case3CompassSociety_isWallSociety_delGraph pw.W pw.h2 pw.he pw.hW rfl
  change (case3CompassSociety (G.deleteVertices X) pw.W pw.h2 pw.he pw.hW).G ≤ _
  rw [hs.1]
  exact GM13.wallCompass_le pw.toGMWall_le_delGraph

/-- The parsed graph and corner order recover the same society to which
the computed rural division was lifted. -/
theorem case3ParsedBlock_toSociety {N : ℕ} (G : MultiDigraph N) (X : Finset (Fin N))
    (p : ParsedCase3Block (G.deleteVertices X) X)
    (hv : p.K_vList = List.ofFn (fun u : Fin (compassCard p.wallSec.W) =>
      (compassEmb p.wallSec.W u).1))
    (he : p.K_eList = (case3CompactCompassMultigraph (G.deleteVertices X) p.wallSec.W).multiEdgeTriples.map
      (origEdgeEmb (compassEmb p.wallSec.W) (compassEmb p.wallSec.W).injective)) :
    p.toSociety = case3CompassSociety (G.deleteVertices X) p.wallSec.W
      p.wallSec.h2 p.wallSec.he p.wallSec.hW := by
  have hg := case3ParsedBlock_toCompassGraph
    (case3CompactCompassMultigraph (G.deleteVertices X) p.wallSec.W) G X p
    ⟨compassEmb p.wallSec.W, (compassEmb p.wallSec.W).injective⟩
    (case3ParsedWall_compass_le G X p.wallSec) hv he
  have hs := case3CompassSociety_isWallSociety_delGraph p.wallSec.W p.wallSec.h2
    p.wallSec.he p.wallSec.hW rfl
  apply society_eq hg
  exact hs.2.symm

/-- Consequently the decoded society satisfies the wall-society conditions
in the deleted original graph. -/
theorem case3ParsedBlock_isWallSociety {N : ℕ} (G : MultiDigraph N) (X : Finset (Fin N))
    (p : ParsedCase3Block (G.deleteVertices X) X)
    (hv : p.K_vList = List.ofFn (fun u : Fin (compassCard p.wallSec.W) =>
      (compassEmb p.wallSec.W u).1))
    (he : p.K_eList = (case3CompactCompassMultigraph (G.deleteVertices X) p.wallSec.W).multiEdgeTriples.map
      (origEdgeEmb (compassEmb p.wallSec.W) (compassEmb p.wallSec.W).injective)) :
    GM13.IsWallSociety (delGraph G X) p.toGMWall p.toSociety := by
  rw [case3ParsedBlock_toSociety G X p hv he]
  exact case3CompassSociety_isWallSociety_delGraph p.wallSec.W p.wallSec.h2
    p.wallSec.he p.wallSec.hW rfl

end GraphMinor.Compute
