module

public import GraphMinor.Compute.GM02BalancedSeparationInput

/-!
# Completeness of the separation output encoding

Every separation on numbered vertices has two membership-bit arrays.
Decoding those arrays recovers its two vertex sets. Thus failure to find
any valid encoded output means exactly that no separation of the required
order and balance exists, as required by II (3.1), page 316.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- The two side arrays can encode every separation permitted by II (3.1). -/
theorem GM02Alg31Input.exists_validSides_iff (x : GM02Alg31Input) (w : ℤ) :
    (∃ left right, x.validSides w left right) ↔
    ∃ H H' : Graph (Fin x.n) (Sym2 (Fin x.n)),
      GM02.IsSeparation (Graph.ofSimpleGraph x.G) H H' ∧
      ((V(H) ∩ V(H')).ncard : ℤ) ≤ w ∧
      3 * ((V(H) \ V(H')) ∩ (x.Q : Set (Fin x.n))).ncard ≤
        2 * ((x.Q : Set (Fin x.n)) \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ (x.Q : Set (Fin x.n))).ncard ≤
        2 * ((x.Q : Set (Fin x.n)) \ (V(H) ∩ V(H'))).ncard := by
  constructor
  · rintro ⟨left, right, H, H', hsep, _, _, hw, hL, hR⟩
    exact ⟨H, H', hsep, hw, hL, hR⟩
  · rintro ⟨H, H', hsep, hw, hL, hR⟩
    let L := (Set.toFinite (V(H))).toFinset
    let R := (Set.toFinite (V(H'))).toFinset
    refine ⟨gm02VertexBits L, gm02VertexBits R, H, H', hsep, ?_, ?_, hw, hL, hR⟩
    · rw [gm02DecodedVertices_bits]
      exact (Set.Finite.coe_toFinset _).symm
    · rw [gm02DecodedVertices_bits]
      exact (Set.Finite.coe_toFinset _).symm

/-- Negative separator bounds give no separation, including on the empty graph. -/
theorem GM02Alg31Input.no_validSides_of_neg (x : GM02Alg31Input) {w : ℤ} (hw : w < 0) :
    ¬∃ left right, x.validSides w left right := by
  rintro ⟨left, right, H, H', _, _, _, hsize, _, _⟩
  exact (not_le_of_gt hw) ((Int.natCast_nonneg _).trans hsize)

/-- The negative-parameter branch of II (3.1) rejects in constant time. -/
theorem gm02Alg31_negative {w : ℤ} (hw : w < 0) :
    ComputesRelInTime gm02Alg31Size (fun x s => s.arrs inArr = x.enc)
      (fun x s => x.correct w s) (.assign outReg (.const 0)) (fun _ => 1) := by
  refine ⟨2, 1, by decide, le_rfl, ?_⟩
  intro x s _
  refine ⟨s.setReg outReg 0, 2, .assign ?_, le_rfl, Or.inr ?_⟩
  · simp only [Expr.eval, checkWord, ite_eq_left (Nat.two_pow_pos _)]
  · exact ⟨by simp, x.no_validSides_of_neg hw⟩

end GraphMinor.Compute
