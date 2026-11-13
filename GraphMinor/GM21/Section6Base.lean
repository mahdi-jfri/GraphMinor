module

public import GraphMinor.GM21.Section6Induction
import GraphMinor.GM21.Section6Five
import GraphMinor.Surface.CutIArc

/-!
# Graph Minors XXI, (6.3): the two base cases of the induction

The proof of (6.3) (page 28 of the preprint) begins: "We proceed by induction on $\Sigma$ and
by (6.3), we may assume that $\Sigma$ is not a disc." The second "(6.3)" is a misprint for (6.7),
and Lean uses (6.7) (see the correction to the proof of (6.3) in `corrections/GM21.md`). In the
order of types (`Induction.HasType`)
there are two cases that need no inductive hypothesis.

* A surface with no cuff has no `Σ`-jumps, since a jump has its ends in `bd(Σ)`, which is empty
  (`boundForType_zero`).
* A surface of type `(0, 1)` is a closed disc, and (6.7) gives the bound (`boundForType_disc`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Induction

open Set Topology GraphMinor.Surface

universe u v

/-- A surface without cuffs has empty boundary. -/
theorem bd_eq_empty_of_cuffs {S : Type*} [TopologicalSpace S] (h : cuffs S = ∅) : bd S = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hx, rfl⟩
  rw [h] at this
  exact this

/-- If `bd(Σ) = ∅` there are no `Σ`-jumps: a jump has its ends in `bd(Σ)`. -/
theorem sigmaJumps_eq_empty_of_bd {α : Type*} {β : Type*} {S : Type*} [TopologicalSpace S]
    (hbd : bd S = ∅) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) :
    sigmaJumps Γ Γ_sub ιV = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun J hJ => ?_
  obtain ⟨-, -, u, hu, -⟩ := hJ
  rw [hbd, inter_empty] at hu
  exact hu

/-- **The base case without cuffs.** A surface of type `(n, 0)` has no cuffs, hence empty
boundary, hence no `Σ`-jumps. -/
theorem boundForType_zero (n : ℕ) : BoundForType.{u, v} n 0 := by
  intro p r q _
  refine ⟨0, fun S _ _ hS hT α β G Γ Γ_sub ιV ιE r' F_star H μ L _ _ _ _ _ => ?_⟩
  have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hc : cuffs S = ∅ := (ncard_eq_zero hfin).mp hT.ncard_cuffs
  rw [sigmaJumps_eq_empty_of_bd (bd_eq_empty_of_cuffs hc)]
  simp

/-- A surface of type `(0, 1)` is a closed disc: it is homeomorphic to `Σ(0, 0, 1)`. -/
theorem isClosedDiscSpace_of_hasType {S : Type} [TopologicalSpace S] (hT : HasType S 0 1) :
    GM06.IsClosedDiscSpace S := by
  obtain ⟨a, b, hab, ⟨e⟩⟩ := hT
  obtain rfl : a = 0 := by omega
  obtain rfl : b = 0 := by omega
  obtain ⟨d⟩ := nonempty_disc_homeo
  exact ⟨(e.trans d).symm⟩

/-- **The base case of a disc**, from (6.7): "by (6.3), we may assume that $\Sigma$ is not a
disc." The print's "(6.3)" is a misprint for (6.7) (see the correction to the proof of (6.3) in
`corrections/GM21.md`). -/
theorem boundForType_disc : BoundForType.{u, v} 0 1 := by
  intro p r q hq
  obtain ⟨lam, hlam⟩ := theorem_6_7_proof.{u, v, 0} p r q hq
  exact ⟨lam, fun S _ _ _ hT α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp =>
    hlam G Γ Γ_sub ιV ιE F_star H μ L hr (isClosedDiscSpace_of_hasType hT) hG hd hL hLp⟩

end Induction
end GM21
end GraphMinor
