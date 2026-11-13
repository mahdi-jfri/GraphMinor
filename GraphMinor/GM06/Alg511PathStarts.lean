module

public import GraphMinor.Compute.GM06Alg511Flow
public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Every inner cuff vertex starts a returned path

The full flow system in VI (5.11), page 134, has as many paths as
there are prescribed inner cuff vertices. Every path starts at one
of those vertices. Since the prescribed points are distinct, the
finite source set has exactly that size. The path start set is a
subset of it of the same size, so the two sets agree. This allows
the winding phase to follow the successor words from any prescribed
inner cuff vertex, without choosing a path from an existential family.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- A full returned path system uses every prescribed inner cuff
vertex as a path start. Its hypotheses describe the ordinary cuff
labels and the path-system properties produced by maximum flow. -/
theorem alg511_pathStarts_eq_cuff (x : GM06Alg511Input)
    {G : Drawing ClosedCylinder} (hk : 0 < x.pathCount)
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (source : Fin x.pathCount → Fin x.vertexCount)
    (hsource : ∀ a ∈ x.flowInput.A, ∃ i, source i = a)
    (hpoints : ∀ i, (rep.vertex (source i)).val = cylinderM1Point x.pathCount i)
    (hinner : ∀ a : Fin x.vertexCount,
      a.val ∈ x.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 x.pathCount)
    {used pred succ : Fin x.vertexCount → ℕ}
    (hsys : IsValidPathSystem x.flowGraph x.flowInput.A x.flowInput.B used pred succ)
    (hcount : (pathStarts used pred).card = x.pathCount) :
    pathStarts used pred = x.flowInput.A := by
  have hinj : Function.Injective source := by
    intro i j hij
    apply cylinderM1Point_injective hk
    rw [← hpoints i, ← hpoints j, hij]
  have himage : Finset.univ.image source = x.flowInput.A := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (hinner (source i)).mpr ?_⟩
      exact ⟨i, (hpoints i).symm⟩
    · exact hsource a
  have hAcard : x.flowInput.A.card = x.pathCount := by
    have hc : (Finset.univ.image source).card = x.pathCount := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact (congrArg Finset.card himage).symm.trans hc
  have hsub : pathStarts used pred ⊆ x.flowInput.A := by
    intro a ha
    obtain ⟨hused, hpred⟩ := (mem_pathStarts a).mp ha
    exact hsys.start_mem_A a hused hpred
  apply Finset.eq_of_subset_of_card_le hsub
  exact hAcard.le.trans hcount.ge

end GraphMinor.GM06
