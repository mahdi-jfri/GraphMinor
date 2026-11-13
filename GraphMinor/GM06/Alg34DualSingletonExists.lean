module

public import GraphMinor.GM06.Alg34SingletonReflection
public import GraphMinor.GM06.Alg34DualDataRep
import GraphMinor.GM06.Section2Dual

/-!
# Singleton search succeeds after the dual transition

VI (2.3) gives a singleton in either the old division or its dual.
Failure of the old finite search excludes the first case. Reflect the
remaining geometric singleton through the dual representation to show
that the next finite search succeeds. This is the progress step used
by the dual branch of VI (3.4).
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- In the nonempty boundary case, absence of old singleton blocks forces
the executable dual singleton search to succeed, by VI (2.3). -/
theorem dualData_findSingleton_exists (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (hconn : IsGraphConnected G.toGraph)
    (hd : IsDiscDualDrawing G D) (hR : 0 < x.regions.length)
    (hD : IsDivision Δ) (hbd : divisionUnion Δ = G.V ∩ bd S)
    (hne : (G.V ∩ bd S).Nonempty) (hnone : gm06FindSingleton x.division = none) :
    ∃ v, gm06FindSingleton (x.dualData x.cuffs[c] hR g.region).division = some v := by
  have hfin : (divisionUnion Δ).Finite := hbd.symm ▸ G.finite_V.inter_of_left _
  have hsub : divisionUnion Δ ⊆ bd S := hbd ▸ inter_subset_right
  have hU : IsDualPointSet (bd S) (divisionUnion Δ) (D.V ∩ bd S) :=
    hbd.symm ▸ hd.2.2.2.2.1
  have hW : (divisionUnion Δ ∪ (D.V ∩ bd S)).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, Or.inl (hbd.symm ▸ hp)⟩
  obtain ⟨A, hA, hcard⟩ := GraphMinor.GM06.theorem_2_3_proof (bd S) (D.V ∩ bd S) Δ
    hS.isOArc_bd hD hfin hsub hU hW
  obtain ⟨p, rfl⟩ := Set.ncard_eq_one.mp hcard
  have hp : {p} ∈ dualDivision (bd S) (D.V ∩ bd S) Δ :=
    hA.resolve_left ((h.findSingleton_none_iff).mp hnone p)
  let hy := g.dualDataRep hS hconn hd hR
  cases hs : gm06FindSingleton (x.dualData x.cuffs[c] hR g.region).division with
  | none => exact False.elim (((hy.findSingleton_none_iff).mp hs p) hp)
  | some v => exact ⟨v, rfl⟩

end GraphMinor.Compute.GM06CuffGapRep
