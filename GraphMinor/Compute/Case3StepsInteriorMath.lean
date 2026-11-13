module

public import GraphMinor.Compute.Case3StepsGatherBitsProg
public import GraphMinor.Compute.Case3StepsCompassLift

/-!
# The compact test is the original interior condition

The member and the perimeter are compared using compact compass labels.
Renaming the member back to original vertex labels preserves this test.
Thus the bitset disjointness scan checks the definition of an interior
member in XIII, Section 9, p. 104, using the entire perimeter.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- Disjoint finite sets remain disjoint after reading their natural-number
vertex labels. -/
theorem case3Disjoint_toNatSet {n : ℕ} (S P : Finset (Fin n)) (h : Disjoint S P) :
    Disjoint S.toNatSet P.toNatSet := by
  apply Set.disjoint_left.mpr
  rintro u ⟨a, ha, rfl⟩ ⟨b, hb, heq⟩
  have hba : b = a := Fin.val_injective heq
  exact Finset.disjoint_left.mp h ha (hba ▸ hb)

/-- The compact perimeter test is also equivalent to disjointness of
finite original-label vertex sets. -/
theorem case3PullbackBits_disjoint_image_iff {m n : ℕ} (e : Fin m → Fin n)
    (S : Finset (Fin m)) (P : Finset (Fin n)) :
    Disjoint S (case3PullbackBits e P) ↔ Disjoint (S.image e) P := by
  classical
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro u hu hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.disjoint_left.mp h hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
  · intro h
    apply Finset.disjoint_left.mpr
    intro v hv hp
    exact Finset.disjoint_left.mp h (Finset.mem_image.mpr ⟨v, hv, rfl⟩) (Finset.mem_filter.mp hp).2

/-- Disjointness of compact sets is equivalent to disjointness of their
original vertex labels when the second set is read through the label map. -/
theorem case3PullbackBits_disjoint_iff {m n : ℕ} (e : Fin m → Fin n)
    (S : Finset (Fin m)) (P : Finset (Fin n)) :
    Disjoint S (case3PullbackBits e P) ↔
      Disjoint ((fun i : Fin m => (e i).1) '' (S : Set (Fin m))) P.toNatSet := by
  classical
  rw [Finset.disjoint_left, Set.disjoint_left]
  constructor
  · intro h u hu hp
    rcases hu with ⟨i, hi, rfl⟩
    rcases hp with ⟨v, hv, heq⟩
    have hev : e i = v := Fin.ext heq.symm
    exact h hi (by simpa only [case3PullbackBits, Finset.mem_filter, Finset.mem_univ, true_and, hev, Finset.mem_coe] using hv)
  · intro h i hi hp
    have heP : e i ∈ P := (Finset.mem_filter.mp hp).2
    exact h ⟨i, hi, rfl⟩ ⟨e i, heP, rfl⟩

/-- The original-label image can equivalently be written using the total
vertex embedding used by graph transport. -/
theorem case3PullbackBits_disjoint_orig_iff {m n : ℕ} (e : Fin m → Fin n)
    (hinj : Function.Injective e) (S : Finset (Fin m)) (P : Finset (Fin n)) :
    Disjoint S (case3PullbackBits e P) ↔
      Disjoint (origVertexEmb e hinj '' S.toNatSet) P.toNatSet := by
  have himage : origVertexEmb e hinj '' S.toNatSet =
      (fun i : Fin m => (e i).1) '' (S : Set (Fin m)) := by
    ext u
    constructor
    · rintro ⟨v, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, (origVertexEmb_apply_val e hinj i).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.1, ⟨i, hi, rfl⟩, origVertexEmb_apply_val e hinj i⟩
  rw [himage]
  exact case3PullbackBits_disjoint_iff e S P

/-- Renaming a lifted member to original compass labels makes its compact
perimeter test exactly the vertex-disjointness part of the interior condition. -/
theorem case3LiftMember_disjoint_perimeter_iff {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (A : Alg86Subgraph (case3CompactCompassMultigraph D W).toSimpleGraph)
    (loops : Finset (Fin (compassCard W))) :
    Disjoint A.verts (case3PullbackBits (compassEmb W) W.perimeterFinset) ↔
      Disjoint
        V(relabelGraph (origVertexEmb (compassEmb W) (compassEmb W).injective)
          (origEdgeEmb (compassEmb W) (compassEmb W).injective)
          (case3LiftMember (case3CompactCompassMultigraph D W) A loops))
        V((W.toGMWall h2 he hW).perimeter) := by
  rw [vertexSet_relabelGraph, case3LiftMember_vertexSet,
    WallOfHeight.vertexSet_perimeter_toGMWall_eq]
  exact case3PullbackBits_disjoint_orig_iff (compassEmb W) (compassEmb W).injective A.verts W.perimeterFinset

/-- For a member of the renamed family, the compact test is the full
interior-member predicate, including membership in that family. -/
theorem case3LiftMember_isInteriorMember_iff {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (A : Alg86Subgraph (case3CompactCompassMultigraph D W).toSimpleGraph)
    (loops : Finset (Fin (compassCard W))) (F : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hmem : relabelGraph (origVertexEmb (compassEmb W) (compassEmb W).injective)
      (origEdgeEmb (compassEmb W) (compassEmb W).injective)
      (case3LiftMember (case3CompactCompassMultigraph D W) A loops) ∈ F) :
    GM13.IsInteriorMember (W.toGMWall h2 he hW) F
      (relabelGraph (origVertexEmb (compassEmb W) (compassEmb W).injective)
        (origEdgeEmb (compassEmb W) (compassEmb W).injective)
        (case3LiftMember (case3CompactCompassMultigraph D W) A loops)) ↔
      Disjoint A.verts (case3PullbackBits (compassEmb W) W.perimeterFinset) := by
  change (_ ∧ _) ↔ _
  rw [and_iff_right hmem]
  exact (case3LiftMember_disjoint_perimeter_iff D W h2 he hW A loops).symm

end GraphMinor.Compute
