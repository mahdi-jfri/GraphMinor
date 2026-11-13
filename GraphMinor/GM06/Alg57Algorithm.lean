module

public import GraphMinor.Compute.GM06Algorithm57
public import GraphMinor.Compute.GM06SuccessorDegreeTime
public import GraphMinor.GM06.Alg57InputRep
import GraphMinor.Compute.GM06Algorithm57Loop

/-!
# Graph Minors VI, algorithm (5.7)

The concrete Word RAM program reads a cuff-augmented drawing and its
reference linkage. It applies the four reductions, preserving the
next-winding feasibility question. At a terminal drawing it tests
valency, constructs the successor paths when feasible, and reverses
the recorded contractions to return paths in the original labels.

The proved measure `2μ+b` bounds the number of rounds. The actual
executions of the scans, the two whole phases and UNDO give a
fifth-degree time bound with logarithmic machine words. The proof
covers every positive path count, including the one-path cut disc.

## Outline of the proof

The paper states (5.7) in two sentences and leaves the details to the reader. Our proof of (5.7)
has numbered sections and lemmas, and the docstrings of the files `GraphMinor/GM06/Alg57*.lean`
and `GraphMinor/Compute/GM06*.lean` refer to them by these numbers. Here `G⁺` is the drawing with
both cuffs added, and the rotation rows give, at each vertex, its edge ends in counterclockwise
order.

* Sections 1 to 3: orientation conventions, the data kept from one iteration to the next, and two
  facts of plane topology. **Lemma 1**: near a vertex the drawing is a star of spokes in their
  cyclic order, and the middle of an edge has a band around it. **Lemma 2**: a crosscut of a
  closed disc cuts it into two sides, and the closure of each side meets the boundary only in its
  own boundary arc.
* Sections 4 and 5: regions from rotations. **Lemma 3**: for a finite connected graph with an edge,
  drawn in the sphere, the orbits of the face permutation `φ = σ⁻¹ τ` on the darts correspond to
  the regions. **Lemma 4**: if Reduction 2 does not apply, every component of `G` meets the
  linkage and `G⁺` is connected. **Lemma 5**: removing the two cap faces gives the regions of `G`.
* Sections 6 to 8: Reductions 1 to 3. **Lemma 6**: the rows after a deletion are correct.
  **Lemmas 7 and 8**: the contraction of Reduction 3, and the splice of the rotation rows and the
  update of the ends after it, are correct. **Lemma 9**: regions under contraction.
* Sections 9 to 13: Reduction 4. Section 9 cuts `G⁺` along the linkage: each vertex of a linkage
  path gets two copies, and each copy keeps a block of consecutive darts of the old row.
  **Lemma 10**: the cut construction is correct. **Lemma 11**: incidence with a region, read in
  the cut graph, agrees with the printed definition. **Lemma 12**: for one path, a witness of
  Reduction 4 avoids the opposite copy of the path. Section 12 builds the candidate graph of
  Reduction 4, and Section 13 searches it by breadth-first search (`FIND_4`). **Lemma 13**: `FIND_4`
  returns a witness exactly when Reduction 4 applies.
* Sections 14 to 16: the terminal linkage. **Lemma 14**: if Reductions 1 and 2 do not apply and
  `sᵢ` has valency at least two, the first edge of the path is not incident with the selected
  face. Section 15 follows the face walk of `c̄ᵢ` to its first contact with the paths and erases
  closed subwalks. **Lemma 15**: this gives a path `Qᵢ` with the required ends. **Lemma 16**: these
  paths, followed by tails of the linkage paths, form a linkage with winding `θ + 1/k`.
* Sections 17 and 18: undoing the contractions. **Lemma 17**: prepending a contracted edge to the
  path that starts at its end gives a linkage of the old graph with the same winding.
* Sections 19 to 21: the main loop (**Lemma 18**, its invariant), the decreasing measure `2μ+b`
  (**Lemma 19**, termination and the number of rounds), and the Word RAM time bound.
  **Theorem 20** puts these together: the program gives a correct answer in polynomial time.
-/

public section
namespace GraphMinor.GM06
open Compute GraphMinor.Surface

/-- Graph Minors VI, (5.7), page 133:

"(5.7) *Algorithm to decide if $\theta(\mathscr{L}) + 1/k$ is feasible.*"

The input consists of the ordinary graph, the augmented rotations,
both cuff orders and the given linkage rows. The output bit decides
next-winding feasibility. A positive answer includes ordinary directed
path rows encoding a successor linkage in the original graph. The
concrete program runs in polynomial time with logarithmic words. -/
theorem algorithm_5_7_proof
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (input : GM06SuccessorInputRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    {s : State} (hinput : s.arrs 0 = gm06EncodeSuccessorInput x) :
    ∃ sf t, Exec (wordSize 32 (gm06SuccessorInputSize x)) gm06Algorithm57Prog s sf t ∧
      t ≤ 85217050012103 * (gm06SuccessorInputSize x + 1) ^ 5 ∧
      GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by
  obtain ⟨sf, t, he, ht, _, _, hout⟩ := gm06Algorithm57_polynomial input hG hθ s hinput
  exact ⟨sf, t, he, ht, hout⟩

end GraphMinor.GM06
