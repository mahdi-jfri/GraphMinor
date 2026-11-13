module

public import GraphMinor.Compute.Case3StepsExtractKeyProg
public import GraphMinor.Compute.Case3StepsRepresentatives

/-!
# Writing one component representative

Core seeds receive the vertex-count sentinel. For an outside seed, the
program extracts its key and searches all component keys for the first match.
The selected seed and vertex-count registers are retained for the outer loop.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Store the representative of seed register 15 in array 27. -/
def case3RepresentativeBody : Cmd :=
  .ite (.read 10 (.reg 15)) (.write 27 (.reg 15) (.reg 14))
    (.seq case3ExtractKeyProg
      (.seq (case3FindBoundaryProg 10 26 25 14 40 41) (.write 27 (.reg 15) (.reg 41))))

/-- One representative-array iteration takes at most `56 n + 96` steps.
Only the target-key array and selected representative entry can change. -/
theorem case3RepresentativeBody_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d) (u : Fin x.n)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    {s : State} (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z) (hlen : (s.arrs 27).length = x.n)
    (hrn : s.regs 14 = x.n) (hru : s.regs 15 = u.1) (hr4 : s.regs 13 = 4) :
    ∃ s' t, Exec w case3RepresentativeBody s s' t ∧ t ≤ 56 * x.n + 96 ∧
      s'.arrs 27 = (s.arrs 27).set u.1
        (if u ∈ d.core.Z then x.n else case3ComponentRepresentative x d.core.Z u) ∧
      (∀ a, a ≠ 25 → a ≠ 27 → s'.arrs a = s.arrs a) ∧
      (∀ r < 36, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hnw
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hidx : u.1 < (s.arrs 10).length := by rw [hZ.1]; exact u.2
  have hbit : (s.arrs 10)[u.1]'hidx = if u ∈ d.core.Z then 1 else 0 := by
    simpa only [hZ.arr_eq_bitSetList] using getElem_bitSetList d.core.Z u.1 u.2
  by_cases hu : u ∈ d.core.Z
  · have hc : (Expr.read 10 (.reg 15)).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hru, huw, hidx, hbit, hu, h1]
    have hex : Exec w (.write 27 (.reg 15) (.reg 14)) s (s.writeArr 27 u.1 x.n) 3 :=
      .write (by simp only [Expr.eval, checkWord, hru, huw, ↓reduceIte])
        (by simp only [Expr.eval, checkWord, hrn, hnw, ↓reduceIte])
        (by rw [hlen]; exact u.2)
    refine ⟨s.writeArr 27 u.1 x.n, 5, .ite_true (t := 3) hc (by decide) hex,
      by omega, ?_, ?_, fun _ _ => rfl⟩
    · simp only [State.writeArr_arrs_self, hu, ↓reduceIte]
    · intro a _ ha
      exact State.writeArr_arrs_ne _ _ _ ha
  · have hc : (Expr.read 10 (.reg 15)).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hru, huw, hidx, hbit, hu, h0]
    obtain ⟨s₁, t₁, hex₁, ht₁, htarget₁, harr₁, hreg₁⟩ :=
      case3ExtractKeyProg_exec x d hd u hw hnw hkeys htab hru hr4
    obtain ⟨s₂, t₂, hex₂, ht₂, hres₂, harr₂, hreg₂⟩ :=
      case3FindBoundaryProg_exec x d hd (case3AttachmentRowSet x d.core.Z u)
        (case3AttachmentRowSet_card_le_three x d hd u) 10 26 25 14 40 41
        (by decide) (by decide) (by decide) hw hn hkeys
        (hZ.of_arr_eq (harr₁ 10 (by decide)))
        ((harr₁ 26 (by decide)).trans htab) htarget₁
        ((hreg₁ 14 (Or.inl (by decide))).trans hrn)
    have hru₂ : s₂.regs 15 = u.1 := by
      rw [hreg₂ 15 (by decide) (by decide), hreg₁ 15 (Or.inl (by decide)), hru]
    have hres : s₂.regs 41 = case3ComponentRepresentative x d.core.Z u := hres₂
    have hrepw : case3ComponentRepresentative x d.core.Z u < 2 ^ w :=
      (case3ComponentRepresentative_lt x d.core.Z u hu).trans hnw
    have harr27 : s₂.arrs 27 = s.arrs 27 := (harr₂ 27).trans (harr₁ 27 (by decide))
    have hex₃ : Exec w (.write 27 (.reg 15) (.reg 41)) s₂
        (s₂.writeArr 27 u.1 (case3ComponentRepresentative x d.core.Z u)) 3 :=
      .write (by simp only [Expr.eval, checkWord, hru₂, huw, ↓reduceIte])
        (by simp only [Expr.eval, checkWord, hres, hrepw, ↓reduceIte])
        (by rw [harr27, hlen]; exact u.2)
    refine ⟨s₂.writeArr 27 u.1 (case3ComponentRepresentative x d.core.Z u),
      2 + (t₁ + (t₂ + 3)), .ite_false hc (.seq hex₁ (.seq hex₂ hex₃)),
      by omega, ?_, ?_, ?_⟩
    · simp only [State.writeArr_arrs_self, harr27, hu, ↓reduceIte]
    · intro a h25 h27
      exact (State.writeArr_arrs_ne _ _ _ h27).trans ((harr₂ a).trans (harr₁ a h25))
    · intro r hr
      rw [State.writeArr_regs, hreg₂ r (by romega) (by romega)]
      exact hreg₁ r (Or.inl hr)

end GraphMinor.Compute
