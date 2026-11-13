module

public import GraphMinor.Compute.GM06Alg34DiscDualData
public import GraphMinor.GM06.Alg34DualGapCorrect
import GraphMinor.GM06.Alg34GapDiscLayout
import GraphMinor.GM06.DualExists

/-!
# Correctness of the dual update on plain disc inputs

The supplied first gap list agrees with the region function in the
input interpretation. Thus the plain finite update is the augmented
dual already interpreted above. Existence of an actual disc dual and
VI (3.2) then give feasibility preservation for this finite operation.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The plain finite dual step preserves the answer and yields another
proper represented disc instance with a division covering its boundary. -/
theorem discDualData_correct (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S)
    (hproper : G.IsProper) (hconn : IsGraphConnected G.toGraph)
    (hR : 0 < X.drawing.regions.length) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hCF : IsCrossFree (bd S) Δ) :
    ∃ D Δ', Nonempty (GM06GapInputRep X.discDualData D Δ') ∧ D.IsProper ∧
      IsDivision Δ' ∧ divisionUnion Δ' = D.V ∩ bd S ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔
        IsFeasible X.discDualData.drawing.graph X.discDualData.drawing.divisionSet) := by
  obtain ⟨L₀, R, hL₀, hgroups, hlen₀⟩ := h.disc_layout hS
  let c : Fin X.drawing.cuffs.length := ⟨0, by
    rw [hL₀]
    simp only [List.length_cons, List.length_nil]
    omega⟩
  let L := X.drawing.cuffs[c]
  have hget : L = L₀ := by
    simp only [L, Fin.getElem_fin, c, hL₀, List.getElem_cons_zero]
  have hL : X.drawing.cuffs = [L] := hL₀.trans (congrArg (fun l => [l]) hget.symm)
  have hlen : R.length = L.length := hlen₀.trans (congrArg List.length hget.symm)
  have hg : List.ofFn (h.gap c).region = R := by
    simpa only [c, hgroups, List.getElem_cons_zero] using (h.gap c).region_list
  have heq : X.discDualData = X.drawing.dualGapInput L hR (h.gap c).region :=
    X.discDualData_eq L R hL hgroups hR hlen (h.gap c).region hg
  obtain ⟨D, hd⟩ := exists_isDiscDualDrawing hS hproper hconn
  obtain ⟨hrep, hp, hdiv, hb, hf⟩ :=
    (h.gap c).dualGapInput_correct hS hconn hd hR hD hbd hCF
  refine ⟨D, dualDivision (bd S) (D.V ∩ bd S) Δ, ?_, hp, hdiv, hb, ?_⟩
  · rw [heq]
    exact hrep
  · rw [heq]
    exact hf

end GraphMinor.Compute.GM06GapInputRep
