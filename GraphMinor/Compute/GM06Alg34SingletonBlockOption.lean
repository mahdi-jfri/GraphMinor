module

public import GraphMinor.Compute.GM06Alg34SingletonBlock
public import GraphMinor.Compute.GM06Alg34SingletonFind

/-!
# The block test returns the finite singleton candidate

Connect the RAM block flag and first-label register to the executable
option-valued singleton test. This gives the exact candidate interface
used when scanning all supplied division blocks, including empty lists
and repeated labels.
-/

public section
namespace GraphMinor.Compute

/-- The natural-number block flag records exactly whether singleton
label detection succeeds. -/
theorem gm06SingletonBlockFlag_eq_isSome (vs : List ℕ) :
    gm06SingletonBlockFlag vs = (gm06SingletonLabel vs).isSome := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    by_cases h : vs.all (fun a => a == v) = true
    · simp only [gm06SingletonBlockFlag, gm06SingletonLabel, h, ↓reduceIte, Option.isSome_some]
    · have hf : vs.all (fun a => a == v) = false := Bool.eq_false_iff.mpr h
      simp only [gm06SingletonBlockFlag, gm06SingletonLabel, hf, Bool.false_eq_true,
        ↓reduceIte, Option.isSome_none]

/-- A successful finite block test returns one of that block's supplied labels. -/
theorem gm06SingletonLabel_mem (vs : List ℕ) (v : ℕ)
    (h : gm06SingletonLabel vs = some v) : v ∈ vs := by
  cases vs with
  | nil => cases h
  | cons a vs =>
    simp only [gm06SingletonLabel] at h
    split at h
    · exact Option.some.inj h ▸ List.mem_cons_self
    · cases h

/-- The RAM block test returns exactly the finite optional candidate,
with the same linear bound and preservation properties. -/
theorem gm06SingletonBlockProg_exec_option {w off : ℕ} (vs tail : List ℕ)
    (hw : 1 < 2 ^ w) (hvalid : ∀ v ∈ vs, v < 2 ^ w)
    (hend : off + vs.length < 2 ^ w) {s : State}
    (hstream : AtStream 0 off (vs ++ tail) s)
    (hpos : s.regs 103 = off) (hcount : s.regs 108 = vs.length) :
    ∃ s' t, Exec w gm06SingletonBlockProg s s' t ∧ t ≤ 20 * vs.length + 20 ∧
      s'.regs 112 = (if (gm06SingletonLabel vs).isSome then 1 else 0) ∧
      (∀ v, gm06SingletonLabel vs = some v → s'.regs 111 = v) ∧
      s'.regs 103 = off + vs.length ∧ s'.regs 108 = 0 ∧
      AtStream 0 (off + vs.length) tail s' ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 111 → q ≠ 112 →
        s'.regs q = s.regs q) := by
  obtain ⟨s', t, hex, ht, hans, hfirst, hpos', hzero, hstream', harr, hreg⟩ :=
    gm06SingletonBlockProg_exec vs tail hw hvalid hend hstream hpos hcount
  refine ⟨s', t, hex, ht, hans.trans ?_, ?_, hpos', hzero, hstream', harr, hreg⟩
  · exact congrArg (fun b : Bool => if b then (1 : ℕ) else 0)
      (gm06SingletonBlockFlag_eq_isSome vs)
  · intro v hv
    cases vs with
    | nil => cases hv
    | cons a vs =>
      have ha : s'.regs 111 = a := hfirst a vs rfl
      simp only [gm06SingletonLabel] at hv
      split at hv
      · exact ha.trans (Option.some.inj hv)
      · cases hv

end GraphMinor.Compute
