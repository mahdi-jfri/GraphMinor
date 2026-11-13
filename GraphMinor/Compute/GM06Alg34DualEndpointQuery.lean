module

public import GraphMinor.Compute.GM06Alg34DualIncidentRegionsProg
public import GraphMinor.Compute.GM06Alg34DualEndChoice

/-!
# A complete RAM query for one dual endpoint pair

Select the primal edge's incident regions from the supplied matrix,
then choose its first two sides, repeating a sole region for a loop.
The result is exactly the endpoint pair used by the finite dual input.
Only the selected-list buffer and the query registers are changed.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the two dual endpoints of edge register 7600. -/
def gm06DualEndpointQueryProg : Cmd :=
  .seq gm06DualIncidentRegionsProg gm06DualEndChoiceProg

/-- One endpoint query returns the exact bounded finite dual pair with
linear incidence-scan work and a fixed outer memory frame. -/
theorem gm06DualEndpointQueryProg_exec {w : ℕ} (x : GM06DrawingData)
    (hR : 0 < x.regions.length) (e : Fin x.ends.length) {s : State}
    (hw : 2 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hspan : x.regions.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hedge : s.regs 7600 = e.val) (hsource : s.arrs 52 = List.range x.regions.length) :
    let p := (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩)
    ∃ s' t, Exec w gm06DualEndpointQueryProg s s' t ∧
      t ≤ 100 * (x.regions.length + 1) + 10 ∧
      s'.regs 7610 = p.1.val ∧ s'.regs 7611 = p.2.val ∧
      (∀ A : ℕ, A ≠ 54 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7601 ∨ 7611 < r → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hrN : x.regions.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hrw := hrN.trans_lt hN
  have hcount : (x.incidentRegions e).length ≤ x.regions.length := by
    simpa only [GM06DrawingData.incidentRegions, List.length_finRange] using
      List.length_filter_le (fun r => decide (e ∈ x.regions[r].edges)) (List.finRange x.regions.length)
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hc₁, ha₁, hg₁⟩ :=
    gm06DualIncidentRegionsProg_exec x e hw1 hN hsquare hspan hmat hstride hn hm hedge hsource
  obtain ⟨s₂, t₂, he₂, ht₂, hx₂, hy₂, ha₂, hg₂⟩ :=
    gm06DualEndChoiceProg_exec ((x.incidentRegions e).map Fin.val) hw hR hrw
      (by simpa only [List.length_map] using hcount)
      (by intro y hy; obtain ⟨r, _, rfl⟩ := List.mem_map.mp hy; exact r.isLt.trans hrw)
      (by simpa only [List.length_map] using hb₁)
      (by simpa only [List.length_map] using hc₁)
  have hp := gm06DualEndChoice_eq x hR e
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega,
    hx₂.trans (congrArg Prod.fst hp), hy₂.trans (congrArg Prod.snd hp), ?_, ?_⟩
  · intro A hA
    exact (ha₂ A).trans (ha₁ A hA)
  · intro r hr
    have h10 : r ≠ 7610 := by omega
    have h11 : r ≠ 7611 := by omega
    exact (hg₂ r h10 h11).trans (hg₁ r (by omega))

end GraphMinor.Compute
