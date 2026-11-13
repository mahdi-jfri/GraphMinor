module

public import GraphMinor.GM19.Defs3
import GraphMinor.GM07.Bridge
import GraphMinor.GM19.Section12e
import GraphMinor.GM19.Section12g

/-!
# Graph Minors XIX, (12.1)

This file states and proves **Graph Minors XIX, (12.1)** (page 362), using
`TangleDatum.exists_wheel` (`Section12e.lean`), `TangleDatum.isPreconnected_nearZone`
(`Section12g.lean`), and the proved theorem `GM07.gm07_theorem_11_10` (`GM07/Bridge.lean`).

(12.1) as printed fails at $\rho = 2$ (where a
3-vertex cell $e$ in a triangular lattice face leaves only digon regions around $H = \{r^*\}$, so no
wheel boundary off $r^*$ exists) and near a cuff when a 3-vertex edge $e \in E(\Gamma)$ meets
$\operatorname{bd}(\Sigma_\chi)$ (where the fifth condition of `Painting.Fits` does not restrict
regions incident with $e$). For $\rho \ge 3$, $\operatorname{rep}(\mathscr{T}) \ge 5\rho + 14$, and
3-vertex edges disjoint from $\operatorname{bd}(\Sigma_\chi)$, `theorem_12_1` gives a wheel $W$
having $H$ as a $W$-hub of radius $\rho$ (taking $Y = \emptyset$ in `TangleDatum.exists_wheel`).
See the correction to (12.1) in `corrections/GM19.md`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- **Graph Minors XIX, (12.1)** (page 362):
"**12.1.** *Let $\rho \ge 2$, even, let $rep(\mathcal{T}) \ge 5\rho + 12$, and let $H$ be a
subdrawing of $\Gamma^*$, satisfying the third condition in the definition of a wheel above. Then
there is a wheel $W$ such that $H$ is a $W$-hub of radius $\rho$.*"

Formalized with the corrected hypotheses: $\rho \ge 3$,
$\operatorname{rep}(\mathscr{T}) \ge 5\rho + 14$, and 3-vertex edges of $\Gamma$ disjoint from
$\operatorname{bd}(\Sigma_\chi)$ (for the version with an additional closed zone set $Y$ near cuffs
used in (12.4), see `TangleDatum.exists_wheel` in `Section12e.lean`). -/
theorem theorem_12_1_proof (D : TangleDatum cap χ) {H : Drawing Shat} {ρ : ℕ}
    (hρ : 3 ≤ ρ) (hrep : 5 * ρ + 14 ≤ D.rep) (hH : H.IsSubdrawing D.rad.G)
    (hhub : (H.V.ncard = 1 ∧ H.E = ∅ ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H'.E.ncard ≤ 4 * ρ + 4 →
        ¬ (H.V ⊆ D.ins H' \ H'.U)) ∨
      (IsEnclave D.tb D.ord D.𝒯 H ∧ H.E.ncard ≤ 4 * ρ + 4 ∧
      ∀ H' : Drawing Shat, IsEnclave D.tb D.ord D.𝒯 H' → H' ≠ H → H'.E.ncard ≤ 4 * ρ + 4 →
        ¬ (H.U ⊆ D.ins H')))
    (hcuff : ∀ e ∈ D.P.Γ.E, (tilde e).ncard = 3 → Disjoint (closure e) (bd S)) :
    ∃ W : Set Shat, D.IsWheel W ∧ D.IsWheelHubOfRadius W H ρ := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨k, rfl⟩ : ∃ k, k + 3 = ρ := ⟨ρ - 3, by omega⟩
  have hdata : ∃ z ∈ H.V, IsPreconnected H.U ∧
      ∀ h ∈ H.V, D.dist (D.rad.atomOf z) (D.rad.atomOf h) ≤ 2 * (k + 3) + 2 := by
    rcases hhub with ⟨hV1, hE0, -⟩ | ⟨⟨ord', 𝒯', _, hFc, _⟩, hEcard, -⟩
    · obtain ⟨z, hVz⟩ := ncard_eq_one.mp hV1
      have hz : z ∈ H.V := hVz.symm ▸ mem_singleton z
      have hU : H.U = {z} := by
        rw [H.U_eq, hVz, hE0, biUnion_empty, union_empty]
      refine ⟨z, hz, hU ▸ isPreconnected_singleton, fun h hh ↦ ?_⟩
      have hzh : h = z := mem_singleton_iff.mp (hVz ▸ hh)
      subst hzh
      have hlen0 : (GraphWalk.nil (G := D.rad.G.toGraph) (hH.1 hz)).length = 0 := rfl
      have h0 := D.dist_atomOf_le_of_walk (.nil (hH.1 hz)) (by omega)
      omega
    · obtain ⟨z, hz⟩ : H.V.Nonempty := by
        obtain ⟨u₀, W₀, -, -, hV₀, -⟩ := hFc.2
        exact ⟨u₀, hV₀ ▸ W₀.start_mem_support⟩
      have hc : IsPreconnected H.U := IsOArc.isPreconnected (IsCircuit.isOArc_U hFc.2)
      refine ⟨z, hz, hc, fun h hh ↦ ?_⟩
      obtain ⟨W, hWlen, -⟩ := TangleDatum.exists_walk_on_circuit hFc hz hh
      have hdist := D.dist_atomOf_le_of_walk W (by omega)
      omega
  obtain ⟨z, hz, hc, hdiam⟩ := hdata
  have hY : TangleDatum.IsZoneSet D H k ∅ :=
    { closed := isClosed_empty
      meet := fun _ _ ⟨_, _, hx⟩ ↦ hx.elim
      frontier_sub := by rw [frontier_empty]; exact empty_subset _
      cuff := fun _ _ e he _ h3 hb ↦
        absurd hb (not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp (hcuff e he h3))) }
  have hconn : IsPreconnected (TangleDatum.nearZone D H k ∪ ∅) := by
    rw [union_empty]
    exact TangleDatum.isPreconnected_nearZone hH hc ⟨z, hz⟩
  obtain ⟨W, hW, -, -⟩ := TangleDatum.exists_wheel
    hrep hH hz hY hconn hdiam (fun _ _ ⟨_, _, hx⟩ ↦ hx.elim) hhub
  exact ⟨W, ⟨H, k + 3, hW⟩, hW⟩

end GraphMinor.GM19
