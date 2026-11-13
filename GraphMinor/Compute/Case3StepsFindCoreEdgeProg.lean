module

public import GraphMinor.Compute.Case3StepsPairKeyProg
public import GraphMinor.Compute.Case3StepsCoreEdgeRepresentatives
public import GraphMinor.Compute.Case3StepsFindBoundaryProg

/-!
# Matching a core edge with a component group

The endpoint pair is written as a target key and compared with every outside
component key. The search returns the least matching component seed, or the
vertex-count sentinel when the core edge needs its own group.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Match the ordered endpoints in registers 42 and 43 with the key table. -/
def case3FindCoreEdgeProg : Cmd :=
  .seq (case3PairKeyProg 25 42 43) (case3FindBoundaryProg 10 26 25 14 40 41)

/-- Matching one core-edge boundary takes at most `56 n + 21` steps. -/
theorem case3FindCoreEdgeProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (u v : Fin x.n) (huv : u < v)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    {s : State} (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hrn : s.regs 14 = x.n) (hru : s.regs 42 = u.1) (hrv : s.regs 43 = v.1) :
    ∃ s' t, Exec w case3FindCoreEdgeProg s s' t ∧ t ≤ 56 * x.n + 21 ∧
      s'.regs 41 = case3FirstIndex
        (fun z => z ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z z = {u, v}) ∧
      s'.arrs 25 = case3BoundaryKey ({u, v} : Finset (Fin x.n)) ∧
      (∀ a, a ≠ 25 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 40 → r ≠ 41 → s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have hcard : ({u, v} : Finset (Fin x.n)).card ≤ 3 := by
    rw [Finset.card_pair (ne_of_lt huv)]
    decide
  obtain ⟨s₁, hex₁, hkey₁, harr₁, hreg₁⟩ := case3PairKeyProg_exec u v huv 25 42 43 hw hnw hru hrv
  obtain ⟨s₂, t₂, hex₂, ht₂, hres₂, harr₂, hreg₂⟩ :=
    case3FindBoundaryProg_exec x d hd {u, v} hcard 10 26 25 14 40 41
      (by decide) (by decide) (by decide) hw hn hkeys
      (hZ.of_arr_eq (harr₁ 10 (by decide))) ((harr₁ 26 (by decide)).trans htab) hkey₁
      ((hreg₁ 14).trans hrn)
  refine ⟨s₂, 14 + t₂, .seq hex₁ hex₂, by omega, hres₂, ?_, ?_, ?_⟩
  · exact (harr₂ 25).trans hkey₁
  · intro a ha
    exact (harr₂ a).trans (harr₁ a ha)
  · intro r h40 h41
    exact (hreg₂ r h40 h41).trans (hreg₁ r)

end GraphMinor.Compute
