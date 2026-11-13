module

public import GraphMinor.Compute.Case3StepsMemberResultStore

/-!
# Remaining capacity after writing a branch record

The record buffer has a used prefix followed by zeroes. The returned code
bounds the next record's length. Split the unused portion at that length,
then apply the branch writer and retain the exact unused suffix.
-/

public section

namespace GraphMinor.Compute

/-- The member branch writer needs only the uniform record-capacity bound,
not its final record length in the initial buffer description. -/
theorem case3MemberResultStoreProg_branch_capacity_exec {w h n N B count remaining : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code pre : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hremaining : n + 6 * G.numEdges + 4 ≤ remaining)
    (hcapacity : pre.length + remaining < 2 ^ w)
    (hcount : count + 1 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ z ∈ code, z < 2 ^ w)
    {s : State} (hsrc : s.arrs 129 = 0 :: code) (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 57 = pre ++ List.replicate remaining 0)
    (hused : s.regs 1 = pre.length) (hnum : s.regs 2 = count) :
    ∃ s' t, Exec w (case3MemberResultStoreProg h) s s' t ∧
      t ≤ 1500 * (n + G.numEdges + G.numActivePairs + 1) ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
      s'.arrs 57 = pre ++ r.enc ++ List.replicate (remaining - r.enc.length) 0 ∧
      s'.regs 0 = 0 ∧ s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 → a ≠ 57 → s'.arrs a = s.arrs a) ∧
      (∀ r < 70, r ≠ 0 → r ≠ 1 → r ≠ 2 → s'.regs r = s.regs r) := by
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have hlenr : r.enc.length ≤ n + 6 * G.numEdges + 4 :=
    case3BranchRecord_enc_length_le G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code hcode
  have hfits : r.enc.length ≤ remaining := hlenr.trans hremaining
  have hsplit : List.replicate remaining (0 : ℕ) =
      List.replicate r.enc.length 0 ++ List.replicate (remaining - r.enc.length) 0 := by
    rw [← List.replicate_add, Nat.add_sub_of_le hfits]
  have hbuf' : s.arrs 57 = pre ++ List.replicate r.enc.length 0 ++
      List.replicate (remaining - r.enc.length) 0 := by
    rw [hbuf, hsplit, List.append_assoc]
  exact case3MemberResultStoreProg_branch_exec G orig hinj code pre
    (List.replicate (remaining - r.enc.length) 0) hcode hw hn hN hA (by omega)
    hcount hlen hwords hsrc hG hlabels hbuf' hused hnum

end GraphMinor.Compute
