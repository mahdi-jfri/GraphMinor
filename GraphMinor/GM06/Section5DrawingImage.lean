module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks
import GraphMinor.GM19.Section6Contract
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Taking the image of a drawing injectively on its point set

For Reduction 3 of VI, page 129, first remove the initial vertex and
its sole edge. The contraction is injective on the remaining compact
drawing. Its image is therefore a drawing: the inverse is continuous
on the image point set, carries edge components back to edge
components, and transports the line or circle closure of each edge.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- A continuous map injective on a cylinder drawing's point set
carries it to a drawing with exactly the image vertices and edges.
The map need not be injective outside the drawing. -/
theorem exists_drawing_image_of_injOn_pointSet
    (G : Drawing ClosedCylinder) (π : C(ClosedCylinder, ClosedCylinder)) (hi : InjOn π G.U) :
    ∃ H : Drawing ClosedCylinder, H.U = π '' G.U ∧ H.V = π '' G.V ∧
      H.E = (image π) '' G.E := by
  classical
  have : Nonempty ClosedCylinder := ⟨cylinderM1Point 1 0⟩
  let g := Function.invFunOn π G.U
  have hleft : LeftInvOn g π G.U := hi.leftInvOn_invFunOn
  have hg : ContinuousOn g (π '' G.U) := by
    rw [continuousOn_iff_isClosed]
    intro C hC
    refine ⟨π '' (G.U ∩ C), ((G.isClosed_U.inter hC).isCompact.image π.continuous).isClosed, ?_⟩
    ext x
    constructor
    · rintro ⟨hx, z, hz, rfl⟩
      have hzC : z ∈ C := by
        change g (π z) ∈ C at hx
        rwa [hleft hz] at hx
      exact ⟨⟨z, ⟨hz, hzC⟩, rfl⟩, ⟨z, hz, rfl⟩⟩
    · rintro ⟨⟨z, hz, rfl⟩, hx⟩
      refine ⟨?_, hx⟩
      change g (π z) ∈ C
      rw [hleft hz.1]
      exact hz.2
  have hset : π '' G.U \ π '' G.V = π '' (G.U \ G.V) :=
    (hi.image_sdiff_subset G.V_subset_U).symm
  have hcomponents : arcComponentsIn (π '' (G.U \ G.V)) = (image π) '' G.E :=
    GM19.arcComponentsIn_image_eq π.continuous.continuousOn
      (hg.mono (image_mono sdiff_subset)) (hleft.mono sdiff_subset)
  have hclosures (e : Set ClosedCylinder) : closure (π '' e) = π '' closure e :=
    π.continuous.isClosedMap.closure_image_eq_of_continuous π.continuous e
  have hlinehomeo (e : Set ClosedCylinder) (he : e ∈ G.E) :
      ∃ h : closure e ≃ₜ (π '' closure e), ∀ x : closure e, (h x).1 = π x.1 := by
    let : CompactSpace (closure e) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
    let f : closure e → (π '' closure e) := fun x => ⟨π x.1, ⟨x.1, x.2, rfl⟩⟩
    have hc : Continuous f := (π.continuous.comp continuous_subtype_val).subtype_mk _
    have hf : Function.Bijective f := by
      constructor
      · intro x y heq
        apply Subtype.ext
        exact hi (G.closure_subset_U he x.2) (G.closure_subset_U he y.2) (congrArg Subtype.val heq)
      · rintro ⟨y, x, hx, heq⟩
        exact ⟨⟨x, hx⟩, Subtype.ext heq⟩
    let h : closure e ≃ₜ (π '' closure e) := Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective f hf) hc
    exact ⟨h, fun _ => rfl⟩
  let H : Drawing ClosedCylinder := {
    U := π '' G.U
    V := π '' G.V
    V_subset_U := image_mono G.V_subset_U
    isClosed_U := (G.isClosed_U.isCompact.image π.continuous).isClosed
    finite_V := G.finite_V.image π
    finite_edges := by
      rw [hset, hcomponents]
      exact G.finite_edges.image (image π)
    edge_cond := by
      intro e he
      rw [hset, hcomponents] at he
      obtain ⟨a, ha, rfl⟩ := he
      rw [hclosures, ← hi.image_inter (G.closure_subset_U ha) G.V_subset_U]
      obtain ⟨h, hh⟩ := hlinehomeo a ha
      rcases G.edge_cond a ha with ⟨u, v, huv, hcap, f, hf0, hf1⟩ | ⟨u, hcap, ⟨f⟩⟩
      · have hu : u ∈ G.U := G.V_subset_U
          (show u ∈ closure a ∩ G.V from hcap ▸ mem_insert u {v}).2
        have hv : v ∈ G.U := G.V_subset_U
          (show v ∈ closure a ∩ G.V from hcap ▸ mem_insert_of_mem u rfl).2
        refine Or.inl ⟨π u, π v, hi.ne hu hv huv, ?_, f.trans h, ?_, ?_⟩
        · rw [hcap, image_pair]
        · change (h (f 0)).1 = π u
          rw [hh, hf0]
        · change (h (f 1)).1 = π v
          rw [hh, hf1]
      · refine Or.inr ⟨π u, ?_, ⟨f.trans h⟩⟩
        rw [hcap, image_singleton] }
  refine ⟨H, rfl, rfl, ?_⟩
  change arcComponentsIn (π '' G.U \ π '' G.V) = _
  rw [hset, hcomponents]

end GraphMinor.GM06
