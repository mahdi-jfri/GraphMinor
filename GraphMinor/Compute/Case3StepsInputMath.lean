module

public import GraphMinor.Compute.Case3StepsCompassGraph
public import GraphMinor.Compute.Algorithm99Relabel
import GraphMinor.Compute.Algorithm77Prog

/-!
# Values used to write the compact society input

Step (5) of XIII (9.9), page 104, numbers the compass vertices consecutively
and lists its four corners in the same order. The compact graph encoding is
obtained by deleting the complement of the compass. Its corner numbers are
read from the rank array at the original wall corner labels.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- Deleting the complement of the compass gives its compact multigraph encoding. -/
theorem case3CompactCompass_enc_eq {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) :
    (D.deleteVerticesCompact W.compassFinsetᶜ).enc =
      (case3CompactCompassMultigraph D W).enc := by
  unfold MultiDigraph.deleteVerticesCompact compactEmb case3CompactCompassMultigraph
    compassEmb compassCard
  exact congrArg (fun S : Finset (Fin n) => (D.induce (S.orderEmbOfFin rfl)).enc)
    (compl_compl W.compassFinset)

/-- The same compact numbering gives the simple graph's encoding. -/
theorem case3CompactCompass_simpleEnc_eq {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) :
    encGraph (D.deleteVerticesCompact W.compassFinsetᶜ).toSimpleGraph =
      encGraph (case3CompactCompassMultigraph D W).toSimpleGraph := by
  unfold MultiDigraph.deleteVerticesCompact compactEmb case3CompactCompassMultigraph
    compassEmb compassCard
  exact congrArg (fun S : Finset (Fin n) => encGraph (D.induce (S.orderEmbOfFin rfl)).toSimpleGraph)
    (compl_compl W.compassFinset)

/-- The rank of the `i`-th compass vertex is `i`. -/
theorem case3CompactRank_compassEmb {h n : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (i : Fin (compassCard W)) :
    compactRank W.compassFinsetᶜ (compassEmb W i).1 = i.1 := by
  have hcard : compassCard W = W.compassFinsetᶜᶜ.card := by
    rw [compl_compl]
    rfl
  have hemb : compactEmb W.compassFinsetᶜ (Fin.cast hcard i) = compassEmb W i := by
    unfold compactEmb compassEmb compassCard at *
    simp only [compl_compl] at *
    rfl
  have hr := compactRank_compactEmb W.compassFinsetᶜ (Fin.cast hcard i)
  rw [hemb] at hr
  exact hr

/-- Reading the rank array at a wall corner gives its compact corner number. -/
theorem case3CompactRank_corner {h n : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (i : Fin 4) :
    compactRank W.compassFinsetᶜ (W.cornerVert h2 i).1 = (compactCorner W h2 he i).1 := by
  rw [← compassEmb_compactCorner W h2 he i]
  exact case3CompactRank_compassEmb W _

/-- The original corner label occurs in the branch-vertex part of the wall
encoding, at a position depending only on the wall height. -/
theorem case3Corner_enc_getElem {h n : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (i : Fin 4) :
    W.encList[3 + (elemWallCornerIdx h2 i).1]? = some (W.cornerVert h2 i).1 := by
  exact getElem?_wallEncList_branchVert W (elemWallCornerIdx h2 i)

/-- Deleting `X` before restricting to vertices disjoint from `X` changes none
of the retained multiplicities. -/
theorem case3DeleteVerticesCompact_deleteVertices {n : ℕ} (G : MultiDigraph n)
    (X S : Finset (Fin n)) (hdisj : Disjoint S X) :
    (G.deleteVertices X).deleteVerticesCompact Sᶜ = G.deleteVerticesCompact Sᶜ := by
  ext u v
  rw [MultiDigraph.deleteVerticesCompact_edgeMult, MultiDigraph.deleteVerticesCompact_edgeMult,
    MultiDigraph.deleteVertices_edgeMult]
  have hu : compactEmb Sᶜ u ∈ S := by
    have h := compactEmb_not_mem Sᶜ u
    simpa only [Finset.mem_compl, not_not] using h
  have hv : compactEmb Sᶜ v ∈ S := by
    have h := compactEmb_not_mem Sᶜ v
    simpa only [Finset.mem_compl, not_not] using h
  have huX := Finset.disjoint_left.mp hdisj hu
  have hvX := Finset.disjoint_left.mp hdisj hv
  simp only [huX, hvX, not_false_eq_true, and_self, ↓reduceIte]

/-- The program may restrict `G` straight to the compass. It need not first
write the separate encoding of `G \\ X`. -/
theorem case3CompactCompass_enc_eq_of_deleteVertices {h n : ℕ}
    (G : MultiDigraph n) (X : Finset (Fin n))
    (W : WallOfHeight h (G.deleteVertices X)) (hdisj : Disjoint W.compassFinset X) :
    (G.deleteVerticesCompact W.compassFinsetᶜ).enc =
      (case3CompactCompassMultigraph (G.deleteVertices X) W).enc := by
  rw [← case3DeleteVerticesCompact_deleteVertices G X W.compassFinset hdisj]
  exact case3CompactCompass_enc_eq _ W

/-- The simple compass input may also be built straight from `G`, since all
retained vertices avoid `X`. -/
theorem case3CompactCompass_simpleEnc_eq_of_deleteVertices {h n : ℕ}
    (G : MultiDigraph n) (X : Finset (Fin n))
    (W : WallOfHeight h (G.deleteVertices X)) (hdisj : Disjoint W.compassFinset X) :
    encGraph (G.deleteVerticesCompact W.compassFinsetᶜ).toSimpleGraph =
      encGraph (case3CompactCompassMultigraph (G.deleteVertices X) W).toSimpleGraph := by
  rw [← case3DeleteVerticesCompact_deleteVertices G X W.compassFinset hdisj]
  exact case3CompactCompass_simpleEnc_eq _ W

end GraphMinor.Compute
