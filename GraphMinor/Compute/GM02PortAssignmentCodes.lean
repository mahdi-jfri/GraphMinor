module

public import GraphMinor.Compute.GM02TopologicalInput
public import GraphMinor.Compute.GM02SeparatorCodes
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Enumerating incident-edge choices by integer codes

Use one slot for each end of each supplied pattern edge. A slot stores
a host edge position or the host edge-count sentinel. Encode the slots
in base one plus the host edge count. If the fixed pattern bound is `K`,
every assignment occurs below that base to the power `2K`, giving the
polynomial enumeration used by the corrected reduction in II (4.6).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Two incident-edge slots for each supplied pattern edge. -/
def gm02PortSlotEquiv (m : ℕ) : Fin m × Bool ≃ Fin (m * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finProdFinEquiv

/-- The two slots of edge `i` are positions `2i` and `2i + 1`. -/
theorem gm02PortSlotEquiv_val (m : ℕ) (p : Fin m × Bool) :
    (gm02PortSlotEquiv m p).val = 2 * p.1.val + (if p.2 then 1 else 0) := by
  rcases p with ⟨i, side⟩
  cases side <;> simp [gm02PortSlotEquiv, finProdFinEquiv, finTwoEquiv, Nat.add_comm]

/-- Raw choices of host edge positions, with the edge-count sentinel allowed. -/
abbrev GM02PortAssignment (x : GM02TopologicalInput) :=
  Fin x.edges.length × Bool → Fin (x.G.edges.length + 1)

/-- Decode one candidate assignment directly from its integer code. -/
def gm02PortAssignmentOfCode (x : GM02TopologicalInput) (code : ℕ) : GM02PortAssignment x :=
  fun p => ⟨gm02SeparatorDigit x.G.edges.length code (gm02PortSlotEquiv x.edges.length p).val,
    Nat.lt_succ_of_le (gm02SeparatorDigit_le ..)⟩

/-- The decoded host edge position is the indicated base digit of the code. -/
theorem gm02PortAssignmentOfCode_val (x : GM02TopologicalInput) (code : ℕ) (p : Fin x.edges.length × Bool) :
    (gm02PortAssignmentOfCode x code p).val =
      gm02SeparatorDigit x.G.edges.length code (2 * p.1.val + (if p.2 then 1 else 0)) := by
  rw [← gm02PortSlotEquiv_val]
  rfl

/-- Every raw incident-edge assignment occurs in the fixed polynomial code range. -/
theorem exists_gm02PortAssignmentCode (x : GM02TopologicalInput) (K : ℕ)
    (hK : x.edges.length ≤ K) (assignment : GM02PortAssignment x) :
    ∃ code < (x.G.edges.length + 1) ^ (2 * K), gm02PortAssignmentOfCode x code = assignment := by
  let f : Fin (x.edges.length * 2) → ℕ := fun i => (assignment ((gm02PortSlotEquiv x.edges.length).symm i)).val
  have hf : ∀ i, f i ≤ x.G.edges.length := fun i => Nat.le_of_lt_succ (assignment _).isLt
  refine ⟨gm02SeparatorCode x.G.edges.length f, ?_, ?_⟩
  · exact (gm02SeparatorCode_lt f hf).trans_le
      (Nat.pow_le_pow_right (by omega : 1 ≤ x.G.edges.length + 1) (by omega))
  · funext p
    apply Fin.ext
    change gm02SeparatorDigit x.G.edges.length (gm02SeparatorCode x.G.edges.length f)
      (gm02PortSlotEquiv x.edges.length p).val = _
    rw [gm02SeparatorDigit_code f hf]
    simp only [f, Equiv.symm_apply_apply]

end GraphMinor.Compute
