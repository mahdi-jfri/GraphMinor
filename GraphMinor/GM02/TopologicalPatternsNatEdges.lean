module

public import GraphMinor.GM02.TopologicalPatterns
public import GraphMinor.GM02.EdgeRelabellingContainment
import Mathlib.Data.Nat.Pairing

/-!
# Applying the finite topological patterns to ordinary edge-list graphs

The proved (4.8) uses a standard triple edge type. Rename the host's
natural-number edge names by a fixed bijection to that type. Minor
containment is invariant under the resulting isomorphism, and the
suppression transport proves the same invariance for existence of a
topologically contained copy. Thus the identical finite pattern family
applies to the plain host graphs used by (4.7).
-/

public section
namespace GraphMinor.GM02
open Graph Set

/-- The finite family of (4.8) tests minor containment on natural-number edge names too. -/
theorem exists_topologicalPatterns_nat_edges {A B : Type*} (H : Graph A B)
    (hV : V(H).Finite) (hE : E(H).Finite) :
    ∃ F : Finset (Graph ℕ (ℕ × ℕ × ℕ)),
      (∀ J ∈ F, V(J).Finite ∧ E(J).Finite) ∧
      ∀ G : Graph ℕ ℕ, V(G).Finite → E(G).Finite →
        (IsIsoMinor H G ↔ ∃ J ∈ F, ∃ L : Graph ℕ ℕ,
          TopologicallyContains G L ∧ Nonempty (Iso J L)) := by
  obtain ⟨F, hsplit, -, hpatterns⟩ := theorem_4_8_proof H hV hE
  have hF : ∀ J ∈ F, V(J).Finite ∧ E(J).Finite := fun J hJ =>
    ⟨((hsplit J hJ).isIsoMinor hV hE).1, ((hsplit J hJ).isIsoMinor hV hE).2.1⟩
  let e : ℕ ≃ ℕ × ℕ × ℕ := Nat.pairEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl ℕ) Nat.pairEquiv.symm)
  refine ⟨F, hF, ?_⟩
  intro G hVG hEG
  have hVE : V(relabelEdges e G).Finite := hVG
  have hEE : E(relabelEdges e G).Finite := by
    change (e.symm ⁻¹' E(G)).Finite
    exact hEG.preimage e.symm.injective.injOn
  have hp := hpatterns (relabelEdges e G) hVE hEE
  constructor
  · intro hm
    have hm' := GraphMinor.Iso.isIsoMinor_right hm (relabelEdgesIso e G)
    obtain ⟨J, hJ, L, ht, hIso⟩ := hp.1 hm'
    obtain ⟨L', ht', hIso'⟩ := (exists_topologicallyContains_iso_relabelEdges_iff G J e).2 ⟨L, ht, hIso⟩
    exact ⟨J, hJ, L', ht', hIso'⟩
  · rintro ⟨J, hJ, L, ht, hIso⟩
    have hc := (exists_topologicallyContains_iso_relabelEdges_iff G J e).1 ⟨L, ht, hIso⟩
    have hm' := hp.2 ⟨J, hJ, hc⟩
    exact GraphMinor.Iso.isIsoMinor_right hm' (relabelEdgesIso e G).symm

end GraphMinor.GM02
