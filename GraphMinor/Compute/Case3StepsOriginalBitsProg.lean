module

public import GraphMinor.Compute.Case3StepsScatterVertexListProg
public import GraphMinor.Compute.Case3StepsMemberVertexOrder
public import GraphMinor.Compute.Case3StepsBoundaryMembership

/-!
# Original member and boundary bitsets for the wall output

The counted member vertex list and the occupied slots of its small boundary
key are scattered through the compass inverse list. This writes the two
original-label bitsets required by output (b) of XIII (9.9), step 6.
-/

@[expose] public section

namespace GraphMinor.Compute

private theorem boundaryVertices_finset {n : ℕ} (T : Finset (Fin n)) :
    (case3BoundaryVertices T).toFinset = T := by
  classical
  ext u
  simp [case3BoundaryVertices]

/-- Scatter the counted member vertex list into original member bitset 55. -/
def case3OriginalMemberBitsProg : Cmd := case3ScatterVertexListProg 31 55 0 62

/-- The original member bitset is computed from the retained ordered list,
with linear ambient allocation and linear work in the member's vertices. -/
theorem case3OriginalMemberBitsProg_exec {w n N : ℕ} (T : Finset (Fin n)) (orig : Fin n → Fin N)
    (hw : 1 < 2 ^ w) (hn : n + 1 < 2 ^ w) (hN : N < 2 ^ w)
    {s : State} (hrank : (s.arrs 2).length = N)
    (hmember : s.arrs 31 = (case3BoundaryVertices T).map Fin.val ++ List.replicate (n - T.card) 0)
    (hcount : s.regs 62 = T.card) (hlistlen : n ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin n, (s.arrs 32).getD u.1 0 = (orig u).1) :
    ∃ s' t, Exec w case3OriginalMemberBitsProg s s' t ∧ t ≤ N + 14 * T.card + 8 ∧
      IsBitSet (T.image orig) 55 s' ∧ (∀ a, a ≠ 55 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 90 → r ≠ 97 → s'.regs r = s.regs r) := by
  have hcard : T.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  obtain ⟨s', t, hex, ht, hbits, harr, hreg⟩ := case3ScatterVertexListProg_exec orig
    (case3BoundaryVertices T) 31 55 0 62 (by decide) (by decide) (by decide) (by decide) hw (by omega) hN
    (by rw [case3BoundaryVertices_length]; omega) hrank
    (by rw [hmember, List.length_append, List.length_map, case3BoundaryVertices_length, List.length_replicate]; omega)
    (by
      intro j
      rw [hmember, Nat.zero_add, List.getD_append _ _ _ _ (by rw [List.length_map]; exact j.2),
        List.getD_eq_getElem _ _ (by rw [List.length_map]; exact j.2), List.getElem_map])
    hlistlen hlist (by rw [case3BoundaryVertices_length]; exact hcount)
  refine ⟨s', t, hex, ?_, ?_, harr, hreg⟩
  · simpa only [case3BoundaryVertices_length] using ht
  · simpa only [boundaryVertices_finset] using hbits

/-- Read the boundary size and scatter its occupied key slots to bitset 56. -/
def case3OriginalBoundaryBitsProg : Cmd :=
  .seq (.assign 112 (.read 25 (.const 0))) (case3ScatterVertexListProg 25 56 1 112)

/-- The original boundary bitset is computed in at most `N + 53` steps for
a boundary of size at most three. Padding slots are never read as vertices. -/
theorem case3OriginalBoundaryBitsProg_exec {w n N : ℕ} (T : Finset (Fin n)) (hT : T.card ≤ 3)
    (orig : Fin n → Fin N) (hw : 6 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    {s : State} (hrank : (s.arrs 2).length = N) (hkey : s.arrs 25 = case3BoundaryKey T)
    (hlistlen : n ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin n, (s.arrs 32).getD u.1 0 = (orig u).1) :
    ∃ s' t, Exec w case3OriginalBoundaryBitsProg s s' t ∧ t ≤ N + 53 ∧
      IsBitSet (T.image orig) 56 s' ∧ (∀ a, a ≠ 56 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 90 → r ≠ 97 → r ≠ 112 → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have hcw : T.card < 2 ^ w := by omega
  let s₁ := s.setReg 112 T.card
  have hex₁ : Exec w (.assign 112 (.read 25 (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hkey, case3BoundaryKey, h0, hcw])
  obtain ⟨s₂, t₂, hex₂, ht₂, hbits₂, harr₂, hreg₂⟩ := case3ScatterVertexListProg_exec (w := w) orig
    (case3BoundaryVertices T) 25 56 1 112 (by decide) (by decide) (by decide) (by decide) (by omega) hn hN
    (by rw [case3BoundaryVertices_length]; omega) (s := s₁) hrank
    (by rw [State.setReg_arrs, hkey, case3BoundaryKey_length T hT, case3BoundaryVertices_length]; omega)
    (by
      intro j
      rw [State.setReg_arrs, hkey]
      have hj : j.1 < T.card := by simpa only [case3BoundaryVertices_length] using j.2
      simpa only [Nat.add_comm] using case3BoundaryKey_slot T j.1 hj)
    hlistlen hlist (by rw [State.setReg_regs_self, case3BoundaryVertices_length])
  refine ⟨s₂, 3 + t₂, .seq hex₁ hex₂, ?_, ?_, harr₂, ?_⟩
  · rw [case3BoundaryVertices_length] at ht₂
    omega
  · simpa only [boundaryVertices_finset] using hbits₂
  · intro r h90 h97 h112
    rw [hreg₂ r h90 h97, State.setReg_regs_ne _ _ h112]

end GraphMinor.Compute
