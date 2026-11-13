module

public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.Compute.GM06SuccessorDegreeScan

/-!
# Interpreting the initial-cuff RAM scan on the cylinder

The input's initial-cuff list is labelled by the canonical initial
points of Section 5. The graph correspondence identifies each endpoint
count with the actual valency at that point. Thus the RAM scan returns
either the exclusion of every valency-one initial point or an actual
index witnessing one. This is the valency test used in Reduction 3
and the terminal case of VI (5.7), page 133.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Surface GraphMinor.GM06

/-- The cuff scan tests actual valency at the supplied cylinder's initial points. -/
theorem gm06SuccessorDegreeScanProg_exec_on_cylinder {w k : ℕ}
    (x : GM06SuccessorInput) (G : Drawing ClosedCylinder)
    (rep : GM06SuccessorGraphRep x G.toGraph)
    (hlen : x.innerCuff.length = k) (label : Fin k → Fin x.vertexCount)
    (hlabels : ∀ i : Fin k,
      x.innerCuff[i.val]'(by rw [hlen]; exact i.isLt) = (label i).val)
    (hpoints : ∀ i : Fin k, (rep.vertex (label i)).val = cylinderM1Point k i)
    (s : State) (hw : 1 < 2 ^ w) (ha : s.arrs 0 = gm06EncodeSuccessorInput x)
    (hn : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeSuccessorInput x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06SuccessorDegreeScanProg s s' t ∧
      t ≤ 10 + 22 * (gm06EncodeSuccessorInput x).length +
        x.innerCuff.length * (24 + 14 * x.endpoints.length) ∧ s'.arrs 0 = s.arrs 0 ∧
      ((s'.regs 27 = 0 ∧ ∀ i : Fin k,
          vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) ∨
        (s'.regs 27 = 1 ∧ ∃ i : Fin k, s'.regs 28 = i.val ∧
          vertexValency G.toGraph (cylinderM1Point k i) = 1)) := by
  have hval (i : Fin k) : vertexValency G.toGraph (cylinderM1Point k i) =
      x.endpoints.count (x.innerCuff[i.val]'(by rw [hlen]; exact i.isLt)) := by
    rw [hlabels i]
    have hh := rep.vertexValency_eq (label i)
    rw [hpoints i] at hh
    exact hh
  obtain ⟨s', t, he, ht, hs, hd⟩ := gm06SuccessorDegreeScanProg_exec x s hw ha hn hwords
  refine ⟨s', t, he, ht, hs, ?_⟩
  rcases hd with hz | ho
  · refine Or.inl ⟨hz.1, ?_⟩
    intro i
    rw [hval i]
    exact hz.2 i.val (by rw [hlen]; exact i.isLt)
  · obtain ⟨hf, j, hj, hp, hd⟩ := ho
    let i : Fin k := ⟨j, by rw [← hlen]; exact hj⟩
    refine Or.inr ⟨hf, i, hp, ?_⟩
    rw [hval i]
    exact hd

end GraphMinor.Compute
