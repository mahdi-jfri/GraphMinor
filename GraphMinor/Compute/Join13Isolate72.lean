module

public import GraphMinor.Compute.Join13Copy72
public import GraphMinor.Compute.Algorithm101Defs

/-!
# Isolating the adapter's memory

Input arrays are copied into an offset memory range. The internal command runs
there, and its two outputs are copied back. This construction preserves the
low registers and every low array other than the two designated outputs.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Run an internal adapter in offset memory and copy its two outputs back. -/
def isolateAdapter72Prog (Q : Cmd) : Cmd :=
  .seq (copyArray72Prog 12 32 10 20)
    (.seq (copyArray72Prog 13 33 10 20)
      (.seq (Q.shiftMem 10 20)
        (.seq (copyArray72Prog 35 15 10 20) (copyArray72Prog 36 16 10 20))))

/-- Offset execution gives the caller's required memory preservation. -/
theorem isolateAdapter72Prog_exec {w : ℕ} (Q : Cmd) (K : ℕ)
    (LG LBD LF LM : List ℕ)
    (hQ : ∀ s : State, s.arrs 12 = LG → s.arrs 13 = LBD →
      ∃ s' t, Exec w Q s s' t ∧ t ≤ K ∧ s'.arrs 15 = LF ∧ s'.arrs 16 = LM)
    (s : State) (hw : 1 < 2 ^ w)
    (hlenG : LG.length < 2 ^ w) (hlenBD : LBD.length < 2 ^ w)
    (hlenF : LF.length < 2 ^ w) (hlenM : LM.length < 2 ^ w)
    (hwordG : ∀ x ∈ LG, x < 2 ^ w) (hwordBD : ∀ x ∈ LBD, x < 2 ^ w)
    (hwordF : ∀ x ∈ LF, x < 2 ^ w) (hwordM : ∀ x ∈ LM, x < 2 ^ w)
    (hG : s.arrs 12 = LG) (hBD : s.arrs 13 = LBD) :
    ∃ s' t, Exec w (isolateAdapter72Prog Q) s s' t ∧
      t ≤ K + 16 * (LG.length + LBD.length + LF.length + LM.length) + 44 ∧
      s'.arrs 15 = LF ∧ s'.arrs 16 = LM ∧
      (∀ r < 10, s'.regs r = s.regs r) ∧
      (∀ a < 20, a ≠ 15 → a ≠ 16 → s'.arrs a = s.arrs a) := by
  obtain ⟨s₁, t₁, he₁, ht₁, ho₁, ha₁, hr₁⟩ :=
    copyArray72Prog_exec 12 32 10 20 (by decide) (by decide) LG s hw hlenG hwordG hG
  obtain ⟨s₂, t₂, he₂, ht₂, ho₂, ha₂, hr₂⟩ :=
    copyArray72Prog_exec 13 33 10 20 (by decide) (by decide) LBD s₁ hw hlenBD hwordBD
      ((ha₁ 13 (by decide)).trans hBD)
  obtain ⟨s₃, t₃, he₃, ht₃, ho₃F, ho₃M⟩ := hQ (s₂.shiftDown 10 20)
    ((ha₂ 32 (by decide)).trans ho₁) ho₂
  let s₄ := s₂.shiftUp 10 20 s₃
  have hF₄ : s₄.arrs 35 = LF := ho₃F
  have hM₄ : s₄.arrs 36 = LM := ho₃M
  obtain ⟨s₅, t₅, he₅, ht₅, ho₅, ha₅, hr₅⟩ :=
    copyArray72Prog_exec 35 15 10 20 (by decide) (by decide) LF s₄ hw hlenF hwordF hF₄
  obtain ⟨s₆, t₆, he₆, ht₆, ho₆, ha₆, hr₆⟩ :=
    copyArray72Prog_exec 36 16 10 20 (by decide) (by decide) LM s₅ hw hlenM hwordM
      ((ha₅ 36 (by decide)).trans hM₄)
  refine ⟨s₆, t₁ + (t₂ + (t₃ + (t₅ + t₆))),
    .seq he₁ (.seq he₂ (.seq he₃.shiftMem (.seq he₅ he₆))), by omega,
    (ha₆ 15 (by decide)).trans ho₅, ho₆, ?_, ?_⟩
  · intro r hr
    rw [hr₆ r hr, hr₅ r hr]
    change (s₂.shiftUp 10 20 s₃).regs r = _
    rw [State.regs_shiftUp_lt _ _ _ _ hr, hr₂ r hr, hr₁ r hr]
  · intro a ha h15 h16
    rw [ha₆ a h16, ha₅ a h15]
    change (s₂.shiftUp 10 20 s₃).arrs a = _
    rw [State.arrs_shiftUp_lt _ _ _ _ ha,
      ha₂ a (Nat.ne_of_lt (Nat.lt_trans ha (by decide))),
      ha₁ a (Nat.ne_of_lt (Nat.lt_trans ha (by decide)))]

end GraphMinor.Compute
