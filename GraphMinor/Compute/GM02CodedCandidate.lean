module

public import GraphMinor.Compute.GM02DecodeSlots
public import GraphMinor.Compute.GM02CandidateTest

/-!
# Testing a separator code on the RAM

Decode an integer code into its separator slots and run the complete
component test. The result flag describes exactly the decoded separator.
Only the slots and the declared component-test scratch locations change.
This is the operation repeated by the exhaustive search in II (3.1).
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths Classical

/-- Decode a candidate code and test the represented separator. -/
def gm02CodedCandidateProg (k : ℕ) : Cmd :=
  .seq (gm02DecodeSlots k) (gm02CandidateTestProg k)

/-- The component test for one code is correct and has a polynomial bound. -/
theorem gm02CodedCandidateProg_exec {n k w code : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q : Finset (Fin n)) (s : State)
    (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w) (hb : n + 1 < 2 ^ w)
    (hc : code < 2 ^ w) (hp : (n + 1) ^ k < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hq : s.arrs 5 = gm02VertexBits Q)
    (hcode : s.regs 190 = code) :
    ∃ s' t, Exec w (gm02CodedCandidateProg k) s s' t ∧
      t ≤ 23 + k * (8 + 4 * k) + n * (k * 6 + 36) +
        n * (91 + k * 6 + n * (k * 6 + 57) + 29 * totalAdjEntries lists) ∧
      Keeps (gm02SlotRegs k ++ gm02CandidateRegs) gm02ComponentArrays s s' ∧
      s'.regs 184 = if ∀ a : Fin n,
        a ∉ gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val) →
        3 * (GM02.deletedComponent (Graph.ofSimpleGraph G)
          (gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val) : Set (Fin n)) a ∩
            (Q : Set (Fin n))).ncard ≤
          2 * (Q \ gm02SlotVertices (n := n) (fun i : Fin k => gm02SeparatorDigit n code i.val)).card
        then 1 else 0 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hslots, hregs, harr⟩ := gm02DecodeSlots_exec k s hrn hcode hb hc hp
  let f : Fin k → ℕ := fun i => gm02SeparatorDigit n code i.val
  have hf : ∀ i, f i ≤ n := fun i => gm02SeparatorDigit_le n code i.val
  have hadj₁ : IsAdjList G 10 11 12 lists s₁ :=
    hadj.of_arrs_eq (congrFun harr _) (congrFun harr _) (congrFun harr _)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout⟩ := gm02CandidateTestProg_exec G lists Q f hf s₁ hw hn
    hadj₁ (by simpa only [harr] using hent) ((hregs _ (Or.inl (by decide))).trans hrn)
    ((congrFun harr _).trans hq) hslots
  have hk₁ : Keeps (gm02SlotRegs k ++ gm02CandidateRegs) gm02ComponentArrays s s₁ :=
    (gm02DecodeSlots_keeps hregs harr).mono (fun _ h => List.mem_append_left _ h) (by simp)
  have hk₂' : Keeps (gm02SlotRegs k ++ gm02CandidateRegs) gm02ComponentArrays s₁ s₂ :=
    hk₂.mono (fun _ h => List.mem_append_right _ h) (fun _ h => h)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_,
    hk₁.trans hk₂' (fun _ h => h) (fun _ h => h), hout⟩
  omega

end GraphMinor.Compute
