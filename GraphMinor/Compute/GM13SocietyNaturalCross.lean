module

public import GraphMinor.Compute.GM13SocietyCorrectness
public import GraphMinor.Compute.Case3StepsCompassLift

/-!
# Crosses in the natural-number representation of the input

The integer names stored in the input are the values of its `Fin n` vertices.
The map `v ↦ v.val` identifies the finite-label society with the original
multigraph society used by the rural-division reader. It leaves every actual
edge triple unchanged.
-/

public section
namespace GraphMinor.Compute
open Graph Surface GM09 GM13 Transport

/-- Renaming the input vertices by their stored integer names recovers the
original multigraph graph. Actual edge labels are unchanged. -/
theorem gm13_relabel_graph (x : GM13SocietyInput) :
    relabelGraph ⟨Fin.val, Fin.val_injective⟩ (Function.Embedding.refl _) x.graph =
      x.G.toGMDigraph.toGraph := by
  apply Graph.ext
  · ext v
    rw [vertexSet_relabelGraph, x.vertexSet_graph]
    constructor
    · rintro ⟨u, _, rfl⟩
      exact u.2
    · intro hv
      exact ⟨⟨v, hv⟩, Set.mem_univ _, rfl⟩
  · intro e u v
    constructor
    · rintro ⟨e₀, u₀, v₀, hl, he, hu, hv⟩
      rw [← he, ← hu, ← hv]
      exact hl
    · intro hl
      exact ⟨e, ⟨u, hl.left_mem⟩, ⟨v, hl.right_mem⟩, hl, rfl, rfl, rfl⟩

/-- A cross with the finite input labels is the same cross on the integer
names appearing in the stored input. The map on edge triples is the identity. -/
theorem gm13Cross_natural (x : GM13SocietyInput)
    {P Q : Graph (Fin x.n) (ℕ × ℕ × ℕ)} (hc : x.society.IsCross P Q) :
    (case3MultigraphSociety x.G x.omega x.nodup_omega).IsCross
      (relabelGraph ⟨Fin.val, Fin.val_injective⟩ (Function.Embedding.refl _) P)
      (relabelGraph ⟨Fin.val, Fin.val_injective⟩ (Function.Embedding.refl _) Q) := by
  let f : Fin x.n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let g := Function.Embedding.refl (ℕ × ℕ × ℕ)
  obtain ⟨hd, a, b, c, d, hp, hq, ho⟩ := hc
  have hp' := isGraphPathWithEnds_relabelGraph f g hp.1
  have hq' := isGraphPathWithEnds_relabelGraph f g hq.1
  have hG : relabelGraph f g x.society.G = x.G.toGMDigraph.toGraph := gm13_relabel_graph x
  rw [hG] at hp' hq'
  have ho' : (relabelCyclicPerm f x.society.Ω).Crosses (f a) (f b) (f c) (f d) := by
    have h1 := isClockwiseSeq_relabelCyclicPerm_iff f x.society.Ω [a, c, b, d]
    have h2 := isClockwiseSeq_relabelCyclicPerm_iff f x.society.Ω [d, b, c, a]
    exact (show (relabelCyclicPerm f x.society.Ω).Crosses (f a) (f b) (f c) (f d) ↔
      x.society.Ω.Crosses a b c d by
      simpa only [CyclicPerm.Crosses, List.map_cons, List.map_nil] using or_congr h1 h2).mpr ho
  refine ⟨?_, f a, f b, f c, f d, ?_, ?_, ho'⟩
  · rw [vertexSet_relabelGraph, vertexSet_relabelGraph]
    exact (Set.disjoint_image_iff f.injective).mpr hd
  · exact ⟨hp', fun h => hp.2.1 (f.injective h), ⟨a, hp.2.2.1, rfl⟩, ⟨b, hp.2.2.2, rfl⟩⟩
  · exact ⟨hq', fun h => hq.2.1 (f.injective h), ⟨c, hq.2.2.1, rfl⟩, ⟨d, hq.2.2.2, rfl⟩⟩

end GraphMinor.Compute
