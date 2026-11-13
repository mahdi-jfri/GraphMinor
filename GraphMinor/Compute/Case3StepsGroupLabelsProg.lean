module

public import GraphMinor.Compute.Case3StepsRepresentativesProg
public import GraphMinor.Compute.Case3StepsCoreEdgesProg
public import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# Group labels for all raw members

The retained multigraph supplies the simple edge encoding. The core-edge
pass matches each boundary pair against component keys, and the component
pass chooses one seed for each attachment set. The two arrays together give
labels for all raw members in XIII (8.6), with no pairwise edge comparisons.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Compute component and core-edge representative arrays 27 and 28. -/
def case3GroupLabelsProg : Cmd :=
  .seq (toSimpleGraphEdgeListProg 3 14 16 32)
    (.seq case3CoreEdgesProg case3RepresentativesProg)

/-- All raw-member group labels can be computed in quadratic vertex work
plus vertex count times active-pair count. The core and attachment keys stay
available, as do the retained multigraph and original rank array. -/
theorem case3GroupLabelsProg_exec {w : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (hDG : D.toSimpleGraph = x.G)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 3 * D.numActivePairs < 2 ^ w) (hsum : x.n + D.numActivePairs < 2 ^ w)
    {s : State} (hD : s.arrs 3 = D.enc) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z) :
    ∃ s' t, Exec w case3GroupLabelsProg s s' t ∧
      t ≤ x.n + x.n * (56 * x.n + 103) + D.numActivePairs * (56 * x.n + 154) + 100 ∧
      s'.arrs 27 = case3ComponentRepList x d.core.Z ∧
      s'.arrs 28 = case3CoreEdgeRepList x d.core.Z ∧ s'.arrs 16 = encGraph x.G ∧
      (∀ a, a ≠ 14 → a ≠ 16 → a ≠ 25 → a ≠ 27 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r < 13, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have hsimp := case3InputEdges_length_le x D hDG
  obtain ⟨s₁, t₁, hex₁, ht₁, henc₁, _, _, harr₁, hreg₁⟩ :=
    toSimpleGraphEdgeListProg_exec D [] 3 14 16 32 (by decide) (by decide)
      (by omega) hnw hm (by simpa only [List.append_nil] using hD)
  have henc : s₁.arrs 16 = encGraph x.G := by simpa only [hDG] using henc₁
  obtain ⟨s₂, t₂, hex₂, ht₂, heRep₂, hrn₂, _, harr₂, hreg₂⟩ :=
    case3CoreEdgesProg_exec x d hd hw hn hkeys (by omega) (by omega) henc
      (hZ.of_arr_eq (harr₁ 10 (by decide) (by decide)))
      ((harr₁ 26 (by decide) (by decide)).trans htab)
  obtain ⟨s₃, t₃, hex₃, ht₃, hcRep₃, harr₃, hreg₃⟩ :=
    case3RepresentativesProg_exec x d hd hw hn hkeys
      (hZ.of_arr_eq ((harr₂ 10 (by decide) (by decide)).trans (harr₁ 10 (by decide) (by decide))))
      (((harr₂ 26 (by decide) (by decide)).trans (harr₁ 26 (by decide) (by decide))).trans htab)
      hrn₂
  have hmul := Nat.mul_le_mul_right (56 * x.n + 57) hsimp
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃),
    by nlinarith, hcRep₃, ?_, ?_, ?_, ?_⟩
  · exact (harr₃ 28 (by decide) (by decide)).trans heRep₂
  · exact ((harr₃ 16 (by decide) (by decide)).trans (harr₂ 16 (by decide) (by decide))).trans henc
  · intro a h14 h16 h25 h27 h28
    exact ((harr₃ a h25 h27).trans (harr₂ a h25 h28)).trans (harr₁ a h14 h16)
  · intro r hr
    rw [hreg₃ r hr, hreg₂ r (by romega), hreg₁ r (by romega)]

/-- Shift the complete group-label computation into caller scratch storage. -/
theorem case3GroupLabelsProg_shift_exec {w : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (hDG : D.toSimpleGraph = x.G)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d) (a_base r_base : ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 3 * D.numActivePairs < 2 ^ w) (hsum : x.n + D.numActivePairs < 2 ^ w)
    {s : State} (hD : s.arrs (3 + a_base) = D.enc)
    (hZ : s.arrs (10 + a_base) = bitSetList d.core.Z)
    (htab : s.arrs (26 + a_base) = case3AttachmentKeys x d.core.Z) :
    ∃ s' t, Exec w (case3GroupLabelsProg.shift a_base r_base) s s' t ∧
      t ≤ x.n + x.n * (56 * x.n + 103) + D.numActivePairs * (56 * x.n + 154) + 100 ∧
      s'.arrs (27 + a_base) = case3ComponentRepList x d.core.Z ∧
      s'.arrs (28 + a_base) = case3CoreEdgeRepList x d.core.Z ∧
      s'.arrs (16 + a_base) = encGraph x.G ∧
      (∀ a, a ≠ 14 + a_base → a ≠ 16 + a_base → a ≠ 25 + a_base →
        a ≠ 27 + a_base → a ≠ 28 + a_base → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  obtain ⟨s_sub, t, hex, ht, hcRep, heRep, henc, harr, _⟩ :=
    case3GroupLabelsProg_exec x D hDG d hd hw hn hkeys hm hsum
      (s := s.unshift a_base r_base) hD (IsBitSet.of_bitSetList _ _ _ hZ) htab
  refine ⟨s.applyShifted a_base r_base s_sub, t, Exec.shift_from a_base r_base hex,
    ht, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.applyShifted_arrs_add, hcRep]
  · rw [State.applyShifted_arrs_add, heRep]
  · rw [State.applyShifted_arrs_add, henc]
  · intro a h14 h16 h25 h27 h28
    by_cases hab : a_base ≤ a
    · change (if a_base ≤ a then s_sub.arrs (a - a_base) else s.arrs a) = _
      simp only [hab, ↓reduceIte]
      rw [harr (a - a_base) (by romega) (by romega) (by romega) (by romega) (by romega),
        State.unshift_arrs, Nat.sub_add_cancel hab]
    · exact State.applyShifted_arrs_lt a_base r_base s s_sub (by romega)
  · intro r hr
    exact State.applyShifted_regs_lt a_base r_base s s_sub hr

end GraphMinor.Compute
