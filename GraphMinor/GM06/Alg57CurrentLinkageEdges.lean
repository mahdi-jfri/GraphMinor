module

public import GraphMinor.GM06.Alg57CurrentCutOrbit
import GraphMinor.GM06.Section5AdjoinedEdges

/-!
# Reading linkage and cuff edges from permanent labels

The local comparison for VI (5.7), page 133, keeps both directed ends
of each linkage edge and every cuff edge. Linkage membership is read
from the undirected indices of the actual path rows. The cuff labels
start after the fixed ordinary label space, including its unused slots.
-/

@[expose] public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Keep exactly the linkage and cuff ends for the local comparison
of the two sides of a linkage path in Lemma 10. -/
def gm06LinkageCuffKeep (m : ℕ) (paths : List (List ℕ)) (d : ℕ) : Bool :=
  decide (m ≤ d / 2 ∨ d / 2 ∈ paths.flatten.map (fun q => q / 2))

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- An active ordinary edge belongs to the linkage exactly when its
undirected permanent index occurs in the given linkage rows. -/
theorem ordinary_edge_mem_linkage_iff (j : Fin rep.tagged.length) (hj : rep.tagged[j].2 = 1) :
    (∃ i : Fin k, rep.edge j ∈ (L.pathDrawing i).E) ↔
      j.val ∈ x.linkage.flatten.map (fun d => d / 2) := by
  constructor
  · rintro ⟨i, he⟩
    obtain ⟨W, _, henc, hP⟩ := rep.linkage.path i
    rw [← hP, walkDrawing_E] at he
    obtain ⟨d, hd, hb, hde⟩ := (henc.edge_mem_iff _).mp he
    have hactive := (henc.active_words d hd).2
    have hindex := rep.edge_inj hactive hj hde
    apply List.mem_map.mpr
    refine ⟨d, List.mem_flatten.mpr ⟨_, List.getElem_mem _, hd⟩, ?_⟩
    exact congrArg Fin.val hindex
  · intro h
    obtain ⟨d, hd, hdj⟩ := List.mem_map.mp h
    obtain ⟨row, hr, hdr⟩ := List.mem_flatten.mp hd
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hr
    let a : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
    obtain ⟨W, _, henc, hP⟩ := rep.linkage.path a
    have hm : d ∈ x.linkage[a.val]'(by rw [rep.linkage.1]; exact a.isLt) := by
      simpa only [a, heq] using hdr
    obtain ⟨hb, _⟩ := henc.active_words d hm
    refine ⟨a, ?_⟩
    rw [← hP, walkDrawing_E]
    exact (henc.edge_mem_iff _).mpr ⟨d, hm, hb, congrArg rep.edge (Fin.ext hdj)⟩

/-- The numeric keep test for the comparison drawing retains exactly
its actual linkage and cuff edges, in either orientation. -/
theorem linkage_cuff_keep_iff (hG : IsCylinderSection5Drawing k G)
    (f : (cylinderSphereDrawing rep.cuffed).E) (e : rep.cuffed.E)
    (hfe : f.val = cylinderToSphere '' e.val) (b : Bool) :
    gm06LinkageCuffKeep rep.tagged.length x.linkage (2 * rep.label f + b.toNat) = true ↔
      (∃ i : Fin k, e.val ∈ (L.pathDrawing i).E) ∨ e.val ⊆ bd ClosedCylinder := by
  have hdiv : (2 * rep.label f + b.toNat) / 2 = rep.label f := by
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  simp only [gm06LinkageCuffKeep, hdiv, decide_eq_true_eq]
  by_cases hf : rep.label f < rep.tagged.length
  · obtain ⟨j, hj, hfj, hlabel⟩ := rep.ordinary_of_label_lt hG f hf
    have heq : e.val = rep.edge j :=
      Set.image_injective.mpr injective_cylinderToSphere (hfe.symm.trans hfj)
    have hbd : ¬ rep.edge j ⊆ bd ClosedCylinder := by
      intro heBd
      have heG := (rep.links j hj).1
      obtain ⟨p, hp⟩ := heG.1
      have hpV := hG.2.1 ⟨heBd hp, (heG.2.1 hp).1⟩
      exact (heG.2.1 hp).2 hpV
    rw [heq, hlabel, rep.ordinary_edge_mem_linkage_iff j hj]
    simp only [not_le.mpr j.isLt, false_or, hbd, or_false]
  · have hge : rep.tagged.length ≤ rep.label f := Nat.le_of_not_gt hf
    have hbd : e.val ⊆ bd ClosedCylinder := by
      rcases edge_mem_or_subset_boundary_of_adjoining rep.subdrawing rep.cuffed_U rep.cuffed_V e.property
          with heG | heBd
      · obtain ⟨j, hj, hje⟩ := rep.edge_cover e.val heG
        obtain ⟨f', hf', hl'⟩ := rep.ordinary_labels j hj
        have hff : f' = f := Subtype.ext (hf'.trans (by rw [hje]; exact hfe.symm))
        rw [← hff, hl'] at hge
        exact False.elim (Nat.not_le_of_lt j.isLt hge)
      · exact heBd
    exact iff_of_true (Or.inl hge) (Or.inr hbd)

end GM06CurrentDrawingRep
end GraphMinor.GM06
