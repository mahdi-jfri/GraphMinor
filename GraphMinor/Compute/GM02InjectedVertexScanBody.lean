module

public import GraphMinor.Compute.GM02InjectedVertexPrefix
public import GraphMinor.Compute.GM02InjectionMembership
public import GraphMinor.Compute.GM02AppendInjectedVertex

/-!
# One step of the host-order pattern-vertex scan

Use the fixed membership expression to test the current host position.
Append its number if some decoded pattern slot selects it. The prefix
recurrence proves the exact buffer after the position is scanned.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- Emit the current host vertex exactly when it is selected by the injection. -/
@[expose] def gm02InjectedVertexScanBody (p : ℕ) : Cmd :=
  .ite (gm02InjectionMembershipExpr p) gm02AppendInjectedVertexProg .skip

/-- One scan step maintains the exact vertex buffer and changes only its used-position register. -/
theorem gm02InjectedVertexScanBody_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (v : Fin G.n) (s : State)
    (hw : 1 < 2 ^ W) (hn : G.n + 1 < 2 ^ W)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val)
    (hscan : s.regs 194 = v.val)
    (hbuf : s.arrs 29 = gm02InjectedVertexBuffer G H f v.val)
    (hpos : s.regs 195 = (gm02InjectedVertexWords G H f v.val).length) :
    ∃ s' t, Exec W (gm02InjectedVertexScanBody H.n) s s' t ∧
      t ≤ (gm02InjectionMembershipExpr H.n).cost + 7 ∧
      s'.arrs 29 = gm02InjectedVertexBuffer G H f (v.val + 1) ∧
      s'.regs 195 = (gm02InjectedVertexWords G H f (v.val + 1)).length ∧
      (∀ a, a ≠ 29 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 195 → s'.regs r = s.regs r) := by
  have hvw : v.val < 2 ^ W := v.isLt.trans (by omega)
  have he := gm02InjectionMembershipExpr_eval s (fun i => (f i).val) v.val hw
    (fun i => (f i).isLt.trans (by omega)) hvw hslots hscan
  have hiff : (∃ i, (f i).val = v.val) ↔ ∃ i, f i = v := by simp only [Fin.ext_iff]
  have he' : (gm02InjectionMembershipExpr H.n).eval W s =
      some (if ∃ i, f i = v then 1 else 0) := by simpa only [hiff] using he
  by_cases hmem : ∃ i, f i = v
  · have hg : (gm02InjectionMembershipExpr H.n).eval W s = some 1 := by
      simpa only [ite_eq_left hmem] using he'
    let rem := G.n - ((gm02InjectedVertexPrefix G H f v.val).length + 1)
    have hb : s.arrs 29 = gm02InjectedVertexWords G H f v.val ++ List.replicate (rem + 1) 0 := by
      rw [hbuf, gm02InjectedVertexBuffer, gm02InjectedVertexBuffer_room]
    have hlen := gm02InjectedVertexPrefix_length_le G H f v.val
    have hposw : (gm02InjectedVertexWords G H f v.val).length + 1 < 2 ^ W := by
      simp only [gm02InjectedVertexWords, List.length_append, List.length_singleton]
      have hi := v.isLt
      omega
    obtain ⟨s', hex, hout, hpos', ha, hr⟩ := gm02AppendInjectedVertexProg_exec s
      (gm02InjectedVertexWords G H f v.val) rem v.val hw hposw hvw hb hpos hscan
    refine ⟨s', (gm02InjectionMembershipExpr H.n).cost + 7,
      .ite_true hg (by decide) hex, le_rfl, ?_, ?_, ha, hr⟩
    · simp only [gm02InjectedVertexBuffer, gm02InjectedVertexWords,
        gm02InjectedVertexPrefix_succ, ite_eq_left hmem, List.length_append,
        List.length_singleton, List.append_assoc] at hout ⊢
      exact hout
    · simpa only [gm02InjectedVertexWords, gm02InjectedVertexPrefix_succ,
        ite_eq_left hmem, List.append_assoc] using hpos'
  · have hg : (gm02InjectionMembershipExpr H.n).eval W s = some 0 := by
      simpa only [ite_eq_right hmem] using he'
    refine ⟨s, (gm02InjectionMembershipExpr H.n).cost + 1, .ite_false hg (.skip s),
      Nat.add_le_add_left (by decide) _, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa only [gm02InjectedVertexBuffer, gm02InjectedVertexWords,
        gm02InjectedVertexPrefix_succ, ite_eq_right hmem] using hbuf
    · simpa only [gm02InjectedVertexWords, gm02InjectedVertexPrefix_succ,
        ite_eq_right hmem] using hpos

end GraphMinor.Compute
