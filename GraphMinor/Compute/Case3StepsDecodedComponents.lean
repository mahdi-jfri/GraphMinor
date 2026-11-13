module

public import GraphMinor.Compute.Case3StepsMultigraphComponents
public import GraphMinor.Compute.Case3StepsCoreBitsProg

/-!
# Recovering the core and its outside components

The program reads the raw (8.6) output, normalizes the decoded core, then
reconstructs the simple graph from the retained multigraph and computes all
outside-component rows. No syntax assumption on the raw output is needed.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Array 3 holds the compact multigraph and array 9 the returned division
code. The decoded core and component rows occupy arrays 10 and 12. -/
def case3DecodedComponentsProg : Cmd :=
  .seq (.assign 0 (.read 3 (.const 0)))
    (.seq (case3CoreBitsProg 9 10 0 1) case3MultigraphComponentsProg)

/-- Decode the actual core returned by (8.6) and compute its components. The
raw output, retained multigraph, and all arrays below 10 are preserved. -/
theorem case3DecodedComponentsProg_exec {w : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (hDG : D.toSimpleGraph = x.G)
    (out : List ℕ) (d : Alg86DivisionOutput x) (hdec : decAlg86Out x out = Sum.inr d)
    (hw : 3 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hm : 2 + 3 * D.numActivePairs < 2 ^ w) (hlen : out.length < 2 ^ w)
    {s : State} (hD : s.arrs 3 = D.enc) (hout : s.arrs 9 = out) :
    ∃ s' t, Exec w case3DecodedComponentsProg s s' t ∧
      t ≤ x.n * x.n + x.n * (38 * x.n + 52 * D.numActivePairs + 47) +
        87 * x.n + 236 * D.numActivePairs + 148 ∧
      s'.arrs 12 = case3ComponentRows x d.core.Z ∧ s'.arrs 10 = bitSetList d.core.Z ∧
      (∀ a < 10, s'.arrs a = s.arrs a) ∧
      IsAdjList x.G 19 20 21 (edgeNeighbors (edgeListOf x.G)) s' ∧
      (s'.arrs 21).length = 2 * (edgeListOf x.G).length ∧ s'.regs 14 = x.n := by
  have hnw : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  obtain ⟨hidx, hval⟩ := enc_getElem_zero D [] (by simpa only [List.append_nil] using hD)
  let s₁ := s.setReg 0 x.n
  have hex₁ : Exec w (.assign 0 (.read 3 (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0, hidx, hval, hnw])
  obtain ⟨s₂, t₂, hex₂, ht₂, hZ₂, harr₂, _⟩ :=
    case3CoreBitsProg_division_exec x out d hdec 9 10 0 1 (by decide) (by decide)
      hn hlen (s := s₁) hout (State.setReg_regs_self ..)
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃, hZ₃, harr₃, hadj₃, hlen₃, hr14₃⟩ :=
    case3MultigraphComponentsProg_exec x D hDG d.core.Z hw hn hsq hm
      (by rw [harr₂ 3 (by decide)]; exact hD)
      (IsBitSet.of_bitSetList _ _ _ hZ₂)
  refine ⟨s₃, 3 + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hdst₃, hZ₃, ?_, hadj₃, hlen₃, hr14₃⟩
  intro a ha
  rw [harr₃ a ha, harr₂ a (by romega)]
  rfl

/-- Run the decoded component computation in caller-selected scratch storage.
The output core and table have offsets 10 and 12. -/
theorem case3DecodedComponentsProg_shift_exec {w : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (hDG : D.toSimpleGraph = x.G)
    (out : List ℕ) (d : Alg86DivisionOutput x) (hdec : decAlg86Out x out = Sum.inr d)
    (a_base r_base : ℕ)
    (hw : 3 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hm : 2 + 3 * D.numActivePairs < 2 ^ w) (hlen : out.length < 2 ^ w)
    {s : State} (hD : s.arrs (3 + a_base) = D.enc) (hout : s.arrs (9 + a_base) = out) :
    ∃ s' t, Exec w (case3DecodedComponentsProg.shift a_base r_base) s s' t ∧
      t ≤ x.n * x.n + x.n * (38 * x.n + 52 * D.numActivePairs + 47) +
        87 * x.n + 236 * D.numActivePairs + 148 ∧
      s'.arrs (12 + a_base) = case3ComponentRows x d.core.Z ∧
      s'.arrs (10 + a_base) = bitSetList d.core.Z ∧
      (∀ a < a_base + 10, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      IsAdjList x.G (19 + a_base) (20 + a_base) (21 + a_base)
        (edgeNeighbors (edgeListOf x.G)) s' ∧
      (s'.arrs (21 + a_base)).length = 2 * (edgeListOf x.G).length ∧
      s'.regs (14 + r_base) = x.n := by
  obtain ⟨s_sub, t, hex, ht, hdst, hZ, harr, hadj, hentries, hr14⟩ :=
    case3DecodedComponentsProg_exec x D hDG out d hdec hw hn hsq hm hlen
      (s := s.unshift a_base r_base) hD hout
  refine ⟨s.applyShifted a_base r_base s_sub, t, Exec.shift_from a_base r_base hex, ht,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.applyShifted_arrs_add, hdst]
  · rw [State.applyShifted_arrs_add, hZ]
  · intro a ha
    by_cases hab : a_base ≤ a
    · change (if a_base ≤ a then s_sub.arrs (a - a_base) else s.arrs a) = _
      simp only [hab, ↓reduceIte]
      rw [harr (a - a_base) (by romega), State.unshift_arrs, Nat.sub_add_cancel hab]
    · exact State.applyShifted_arrs_lt a_base r_base s s_sub (by omega)
  · intro r hr
    exact State.applyShifted_regs_lt a_base r_base s s_sub hr
  · simpa only [IsAdjList, IsListFamily, IsListAt, State.applyShifted_arrs_add] using hadj
  · rw [State.applyShifted_arrs_add, hentries]
  · rw [State.applyShifted_regs_add, hr14]

end GraphMinor.Compute
