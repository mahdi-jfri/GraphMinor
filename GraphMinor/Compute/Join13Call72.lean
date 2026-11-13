module

public import GraphMinor.Compute.Join13CoreBounds72
public import GraphMinor.Compute.Algorithm101Defs
public import GraphMinor.Compute.Specs4

/-!
# Calling the core without changing the caller's saved data

The packed input is copied to a separate memory range. The core program runs
there with both register and array indices shifted. Its output appears in array
201, while the endpoint stream and graph sizes stay below the shifted range.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Copy the packed input, then execute the core in a disjoint memory range. -/
def callCore72Prog (P : Cmd) : Cmd :=
  .seq (.assign 98 (.len inArr))
    (.seq (copyFullArrProg inArr 200 98 100) (P.shiftMem 200 200))

/-- A shifted core call preserves the endpoint stream and size registers. -/
theorem callCore72Prog_exec {w ξ B δ : ℕ} (x : Alg41CoreInput ξ B) (P : Cmd)
    (C c : ℕ)
    (hP : ∀ (x : Alg41CoreInput ξ B) (s : State),
      s.arrs inArr = encAlg41CoreIn x →
      ∃ s' t, Exec (wordSize c (alg41CoreSize x)) P s s' t ∧
        t ≤ C * alg41CoreSize x ∧
        s'.arrs outArr =
          let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
          encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList)
    (s : State) (hw : wordSize c (alg41CoreSize x) ≤ w)
    (hsmall : 5 * alg41CoreSize x < 2 ^ w)
    (hin : s.arrs inArr = encAlg41CoreIn x) :
    ∃ s' t, Exec w (callCore72Prog P) s s' t ∧
      t ≤ (C + 100) * alg41CoreSize x ∧
      s'.arrs 201 =
        (let T := computeFolioDP x.G x.Z δ x.ht x.p x.hp x.τ
         encFolioSetRep T.toFolioSetRep ++ encRawCertModels T.toRawList) ∧
      (∀ a < 200, s'.arrs a = s.arrs a) ∧
      (∀ r < 98, s'.regs r = s.regs r) := by
  have hN : 0 < alg41CoreSize x := by dsimp [alg41CoreSize]; omega
  have h1 : 1 < 2 ^ w := by omega
  have hlen := length_encAlg41CoreIn_le x
  have hlenw : (encAlg41CoreIn x).length < 2 ^ w := by omega
  let s₁ := s.setReg 98 (encAlg41CoreIn x).length
  have he₁ : Exec w (.assign 98 (.len inArr)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hin, hlenw])
  obtain ⟨s₂, t₂, he₂, ht₂, ho₂, ha₂, hr₂⟩ :=
    copyFullArrProg_exec inArr 200 98 100 (by decide) (by decide)
      (encAlg41CoreIn x) rfl
      (fun a ha => (mem_encAlg41CoreIn_le x ha).trans_lt (by omega))
      h1 hlenw (s := s₁) (by simpa [s₁] using hin) (by simp [s₁])
  obtain ⟨s₃, t₃, he₃, ht₃, ho₃⟩ := hP x (s₂.shiftDown 200 200) (by
    change s₂.arrs (200 + inArr) = _
    exact ho₂)
  have he₃' : Exec w P (s₂.shiftDown 200 200) s₃ t₃ := he₃.mono_wordSize hw
  let s₄ := s₂.shiftUp 200 200 s₃
  refine ⟨s₄, 2 + (t₂ + t₃), .seq he₁ (.seq he₂ he₃'.shiftMem), ?_, ?_, ?_, ?_⟩
  · have hmul : (C + 100) * alg41CoreSize x = C * alg41CoreSize x + 100 * alg41CoreSize x := by ring
    omega
  · exact ho₃
  · intro a ha
    change (s₂.shiftUp 200 200 s₃).arrs a = _
    rw [State.arrs_shiftUp_lt _ _ _ _ ha, ha₂ a (Nat.ne_of_lt ha)]
    rfl
  · intro r hr
    change (s₂.shiftUp 200 200 s₃).regs r = _
    rw [State.regs_shiftUp_lt _ _ _ _ (Nat.lt_trans hr (by decide)), hr₂ r (Nat.lt_trans hr (by decide))]
    simp [s₁, Nat.ne_of_lt hr]

end GraphMinor.Compute
