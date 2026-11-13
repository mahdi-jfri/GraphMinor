module

public import GraphMinor.Compute.Case3StepsGroupingProg

/-!
# Relocating the routing passes into caller scratch storage

The local routing program runs above arbitrary array and register bases.
Its exact tables and traversal counts are preserved by the shift, while all
caller storage below the scratch bases remains unchanged.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The complete routing passes run at arbitrary scratch bases with exact
outputs and unchanged caller storage below the bases. -/
theorem case3GroupingProg_shift_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (a_base r_base : ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) {s : State}
    (hD : s.arrs (3 + a_base) = D.enc) (hin : s.arrs (16 + a_base) = encGraph x.G) (hZ : s.arrs (10 + a_base) = bitSetList d.core.Z)
    (htab : s.arrs (26 + a_base) = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs (27 + a_base) = case3ComponentRepList x d.core.Z)
    (hedges : s.arrs (28 + a_base) = case3CoreEdgeRepList x d.core.Z) :
    ∃ s' t, Exec w (case3GroupingProg.shift a_base r_base) s s' t ∧
      t ≤ x.n * x.n + 11 * x.n + 42 * (case3InputEdges x).length + 43 * D.numActivePairs +
        (x.n + (case3InputEdges x).length) * (77 * x.n + 141) + 58 ∧
      s'.arrs (29 + a_base) = bitSetList (case3GroupLabelSet x d.core.Z) ∧
      s'.arrs (33 + a_base) = List.ofFn (case3OrderedLoopLabel x d.core.Z) ∧
      s'.arrs (34 + a_base) = case3EdgeMatrixPrefix x d.core.Z (case3InputEdges x).length ∧
      s'.arrs (35 + a_base) = case3BucketHeads (case3ActivePairOwner x D d.core.Z)
        (x.n + (case3InputEdges x).length) 0 ∧
      s'.arrs (36 + a_base) = case3BucketNext (case3ActivePairOwner x D d.core.Z) 0 ∧
      s'.arrs (37 + a_base) = case3BucketCounts (case3ActivePairOwner x D d.core.Z)
        (x.n + (case3InputEdges x).length) 0 ∧
      s'.regs (14 + r_base) = x.n ∧ s'.regs (17 + r_base) = (case3InputEdges x).length ∧
      s'.regs (52 + r_base) = x.n + (case3InputEdges x).length ∧ s'.regs (64 + r_base) = D.numActivePairs ∧
      (∀ a, a ≠ 25 + a_base → a ≠ 29 + a_base → a ≠ 30 + a_base → a ≠ 33 + a_base → a ≠ 34 + a_base → a ≠ 35 + a_base → a ≠ 36 + a_base → a ≠ 37 + a_base →
        s'.arrs a = s.arrs a) ∧ (∀ r < r_base, s'.regs r = s.regs r) := by
  obtain ⟨s_sub, t, hex, ht, hmask, hloop, hmat, hheads, hnext, hcounts,
      hn', hm', hL', hA', harr, _⟩ :=
    case3GroupingProg_exec x D hG d hd hdiv hw hn hsquare hkeys hm hsize hA
      (s := s.unshift a_base r_base) hD hin (IsBitSet.of_bitSetList _ _ _ hZ) htab hreps hedges
  refine ⟨s.applyShifted a_base r_base s_sub, t, Exec.shift_from a_base r_base hex,
    ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.applyShifted_arrs_add, hmask]
  · rw [State.applyShifted_arrs_add, hloop]
  · rw [State.applyShifted_arrs_add, hmat]
  · rw [State.applyShifted_arrs_add, hheads]
  · rw [State.applyShifted_arrs_add, hnext]
  · rw [State.applyShifted_arrs_add, hcounts]
  · rw [State.applyShifted_regs_add, hn']
  · rw [State.applyShifted_regs_add, hm']
  · rw [State.applyShifted_regs_add, hL']
  · rw [State.applyShifted_regs_add, hA']
  · intro a h25 h29 h30 h33 h34 h35 h36 h37
    by_cases hab : a_base ≤ a
    · change (if a_base ≤ a then s_sub.arrs (a - a_base) else s.arrs a) = _
      simp only [hab, ↓reduceIte]
      rw [harr (a - a_base) (by romega) (by romega) (by romega) (by romega)
        (by romega) (by romega) (by romega) (by romega),
        State.unshift_arrs, Nat.sub_add_cancel hab]
    · exact State.applyShifted_arrs_lt a_base r_base s s_sub (by romega)
  · intro r hr
    exact State.applyShifted_regs_lt a_base r_base s s_sub hr

end GraphMinor.Compute
