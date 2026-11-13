module

public import GraphMinor.Compute.GM06Find4Program
public import GraphMinor.Compute.GM06RecoverDartsProgram

/-!
# FIND_4 with its actual directed path row

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns a
successful contact and an ordinary directed path. This program runs
the complete contact search, then recovers permanent dart labels for
its successful vertex row. The selected edge restriction is recomputed
from the saved contact, so no leftover scratch table is a hypothesis.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The exact contact and directed-edge output of FIND_4. -/
def gm06Find4Darts {n : ℕ} (m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) : Option (ℕ × List ℕ) :=
  (gm06Find4 (gm06CandidateEnds m origins) ordinary incV incE upper start steps).map (fun result =>
    (result.1, gm06PathDarts n origins
      (gm06CandidateDarts m origins ordinary incV incE upper (gm06Find4PathVertices start steps) result.1)
      result.2))

/-- Search, then materialize directed edges only on a successful branch. -/
def gm06Find4DartsProg : Cmd :=
  .seq gm06Find4Prog (.ite (.reg 646) gm06Find4RecoverProg .skip)

/-- Decode the returned contact and directed dart row. -/
def gm06Find4DartsResult (s : State) : Option (ℕ × List ℕ) :=
  if s.regs 646 = 0 then none else some (s.regs 678, s.arrs 635)

/-- Full register frame for the directed FIND_4 program. -/
def gm06Find4DartsRegs : List ℕ := gm06Find4Regs ++ gm06Find4RecoverRegs

/-- Full array frame for the directed FIND_4 program. -/
def gm06Find4DartsArrs : List ℕ := gm06Find4Arrs ++ gm06Find4RecoverArrs

/-- Cubic search cost plus the polynomial directed-label scan. -/
def gm06Find4DartsCost (n m r upperCount dartCount : ℕ) : ℕ :=
  gm06Find4Cost n m r upperCount dartCount + 127 + 100 * n + 350 * m +
    100 * (r + 1) + 100 * upperCount + n * (70 + 13 * (2 * m))

/-- A failed vertex-path decoder is exactly a zero success flag. -/
theorem gm06Find4Result_none_iff (s : State) : gm06Find4Result s = none ↔ s.regs 646 = 0 := by
  rw [gm06Find4Result, Option.map_eq_none_iff, gm06BfsPathResult_none_iff]

/-- Full RAM execution returns the exact pure directed FIND_4 output,
with no candidate, path, edge-key or continuation-result hypothesis. -/
theorem gm06Find4DartsProg_exec {w n m : ℕ} (data : GM06CutData) (ordinary : List Bool)
    (incV incE upper padding : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) (s : State)
    (hw : n + 4 < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : n * n + 2 < 2 ^ w) (hlen : data.rotations.length = n)
    (horgLen : data.origins.length = 2 * m) (hvalues : ∀ v ∈ data.origins, v < n)
    (hdarts : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hproper : ∀ d ∈ data.rotations.flatten, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD [])
    (hinc : ∀ e, e < m → incE[e]?.getD 0 ≠ 0 →
      2 * e ∈ data.rotations.flatten ∧ 2 * e + 1 ∈ data.rotations.flatten)
    (hVlen : incV.length = n) (hElen : incE.length = m) (hordinary : ordinary.length = m)
    (hVwords : ∀ x ∈ incV, x < 2 ^ w) (hEwords : ∀ x ∈ incE, x < 2 ^ w)
    (hstepsFit : steps.length + 2 < 2 ^ w) (hstepEdges : ∀ step ∈ steps, step.1 < m)
    (hupperLen : upper.length < 2 ^ w) (hupper : ∀ x ∈ upper, x < n)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE) (h608 : s.arrs 608 = upper)
    (h609 : s.arrs 609 = gm06Find4PathVertices start steps)
    (h610 : s.arrs 610 = steps.map Prod.fst) (h624 : s.arrs 624 = ordinary.map Bool.toNat)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins) (h620 : s.regs 620 = n) (h649 : s.regs 649 = m) :
    ∃ sf t, Exec w gm06Find4DartsProg s sf t ∧
      t ≤ gm06Find4DartsCost n m steps.length upper.length data.rotations.flatten.length ∧
      Keeps gm06Find4DartsRegs gm06Find4DartsArrs s sf ∧
      gm06Find4DartsResult sf = gm06Find4Darts m data.origins ordinary incV incE upper start steps := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hflag⟩ := gm06Find4Prog_exec data ordinary incV incE upper padding
    start steps s hw hm hfit hlen horgLen hvalues hdarts hproper hinc hVlen hElen hordinary
    hVwords hEwords hstepsFit hstepEdges hupperLen hupper h606 h607 h608 h609 h610 h624 h625
    hcode hwords h626 h620 h649
  have hn : n < 2 ^ w := by omega
  cases hans : gm06Find4 (gm06CandidateEnds m data.origins) ordinary incV incE upper start steps with
  | none =>
    have hf : s₁.regs 646 = 0 := (gm06Find4Result_none_iff s₁).mp (hd₁.trans hans)
    refine ⟨s₁, t₁ + 2, .seq he₁ (.ite_false
      (GraphMinor.Compute.Crossing.eval_reg hf (Nat.two_pow_pos w)) (.skip s₁)), ?_,
      hk₁.mono (by intro r hr; exact List.mem_append_left _ hr)
        (by intro a ha; exact List.mem_append_left _ ha), ?_⟩
    · unfold gm06Find4DartsCost
      omega
    · simp only [gm06Find4DartsResult, hf, ↓reduceIte, gm06Find4Darts, hans, Option.map_none]
  | some result =>
    obtain ⟨j, vertices⟩ := result
    have hresult : gm06Find4Result s₁ = some (j, vertices) := hd₁.trans hans
    obtain ⟨vertexRow, hrow, hpair⟩ := Option.map_eq_some_iff.mp hresult
    have h678 : s₁.regs 678 = j := congrArg Prod.fst hpair
    have hrowEq : vertexRow = vertices := congrArg Prod.snd hpair
    subst vertexRow
    have hf : s₁.regs 646 = 1 := by
      rcases hflag with hf | hf
      · have hnone := (gm06Find4Result_none_iff s₁).mpr hf
        rw [hresult] at hnone
        contradiction
      · exact hf
    have hvertexRow : s₁.arrs 634 ++ [s₁.regs 645] = vertices := by
      simpa only [gm06BfsPathResult, hf, one_ne_zero, ↓reduceIte, Option.some.injEq] using hrow
    obtain ⟨hc, p, hp, hpwords⟩ := gm06Find4_sound (gm06CandidateEnds m data.origins) ordinary incV incE upper
      start steps j vertices hans
    have hcBounds := gm06Reduction4Contacts_bounds incV incE start.val
      (steps.map (fun step => (step.1, step.2.val))) hc
    simp only [List.length_map] at hcBounds
    have hverts : ∀ x ∈ vertices, x < n := by
      intro x hx
      rw [← hpwords] at hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact v.isLt
    have hsupportLen : vertices.length ≤ n := by
      rw [← hpwords, List.length_map]
      simpa only [Fintype.card_fin] using hp.support_nodup.length_le_card
    have hbeforeLen : (s₁.arrs 634).length + 1 = vertices.length := by
      simpa only [List.length_append, List.length_singleton] using congrArg List.length hvertexRow
    have hbefore : ∀ x ∈ s₁.arrs 634, x < n := by
      intro x hx
      apply hverts x
      rw [← hvertexRow]
      exact List.mem_append_left _ hx
    have htarget : s₁.regs 645 < n := by
      apply hverts
      rw [← hvertexRow]
      exact List.mem_append_right _ List.mem_cons_self
    have hpathLen : (gm06Find4PathVertices start steps).length = steps.length + 1 := by
      simp only [gm06Find4PathVertices, List.length_cons, List.length_map]
    have hpath : ∀ x ∈ gm06Find4PathVertices start steps, x < n := by
      intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · exact hx ▸ start.isLt
      · obtain ⟨step, _, rfl⟩ := List.mem_map.mp hx
        exact step.2.isLt
    obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06Find4RecoverProg_exec data.origins ordinary incV incE upper
      (gm06Find4PathVertices start steps) (s₁.arrs 634) (s₁.regs 645) s₁ (by omega) hn hm (by omega)
      horgLen hvalues hordinary hVlen hElen hVwords hEwords (by rw [hpathLen]; omega) hupperLen
      (by rw [hpathLen]; omega) hpath hupper (by omega) hbefore htarget
      ((hk₁.2 606 (by decide)).trans h606) ((hk₁.2 607 (by decide)).trans h607)
      ((hk₁.2 608 (by decide)).trans h608) ((hk₁.2 609 (by decide)).trans h609)
      ((hk₁.2 624 (by decide)).trans h624) ((hk₁.2 626 (by decide)).trans h626) rfl
      ((hk₁.1 620 (by decide)).trans h620) rfl ((hk₁.1 649 (by decide)).trans h649) h678
    refine ⟨sf, t₁ + (1 + tf), .seq he₁ (.ite_true
      (GraphMinor.Compute.Crossing.eval_reg hf (by omega)) (by decide) hef), ?_,
      (hk₁.mono (by intro r hr; exact List.mem_append_left _ hr)
        (by intro a ha; exact List.mem_append_left _ ha)).trans hkf
        (by intro r hr; exact List.mem_append_right _ hr) (by intro a ha; exact List.mem_append_right _ ha), ?_⟩
    · have hmul := Nat.mul_le_mul_right (70 + 13 * (2 * m)) (by omega : (s₁.arrs 634).length ≤ n)
      rw [hpathLen] at htf
      unfold gm06Find4DartsCost
      omega
    · have hf' := (hkf.1 646 (by decide)).trans hf
      have hj' := (hkf.1 678 (by decide)).trans h678
      rw [hvertexRow] at hdf
      simp only [gm06Find4DartsResult, hf', one_ne_zero, ↓reduceIte, hj', hdf,
        gm06Find4Darts, hans, Option.map_some]

/-- A returned directed row is a simple source-to-contact path of
retained candidate darts, and its contact passes the prefix tests. -/
theorem gm06Find4Darts_sound {n m : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n))
    (hlen : origins.length = 2 * m) (hvalues : ∀ x ∈ origins, x < n)
    (j : ℕ) (ds : List ℕ) (h : gm06Find4Darts m origins ordinary incV incE upper start steps = some (j, ds)) :
    j ∈ gm06Reduction4Contacts incV incE start.val (steps.map (fun step => (step.1, step.2.val))) ∧
      GM06DartWalk (fun d => origins[d]?.getD 0) (gm06CutNeighbourHead origins)
        start.val ds (gm06Find4Target start steps j).val ∧
      (gm06WalkVertices (gm06CutNeighbourHead origins) start.val ds).Nodup ∧
      ∀ d ∈ ds, d ∈ gm06CandidateDarts m origins ordinary incV incE upper (gm06Find4PathVertices start steps) j := by
  obtain ⟨⟨q, vertices⟩, hfind, heq⟩ := Option.map_eq_some_iff.mp h
  have hq : q = j := congrArg Prod.fst heq
  subst q
  have hds : gm06PathDarts n origins
      (gm06CandidateDarts m origins ordinary incV incE upper (gm06Find4PathVertices start steps) j)
      vertices = ds := congrArg Prod.snd heq
  obtain ⟨hc, p, hp, hpwords⟩ := gm06Find4_sound (gm06CandidateEnds m origins) ordinary incV incE upper
    start steps j vertices hfind
  rw [← hds, ← hpwords]
  have hwalk := gm06PathDarts_candidate_walk origins ordinary incV incE upper
    (gm06Find4PathVertices start steps) j hlen hvalues p
  exact ⟨hc, hwalk.1, gm06PathDarts_candidate_nodup origins ordinary incV incE upper
    (gm06Find4PathVertices start steps) j hlen hvalues p hp, fun d hd => (hwalk.2.2 d hd).2⟩

/-- Directed FIND_4 fails exactly when every eligible contact is
unreachable in its corresponding exact candidate graph. -/
theorem gm06Find4Darts_none_iff {n : ℕ} (m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper : List ℕ) (start : Fin n) (steps : List (ℕ × Fin n)) :
    gm06Find4Darts m origins ordinary incV incE upper start steps = none ↔
      ∀ j ∈ gm06Reduction4Contacts incV incE start.val (steps.map (fun step => (step.1, step.2.val))),
        ¬ (gm06Find4Graph (gm06CandidateEnds m origins) ordinary incV incE upper start steps j).Reachable
          start (gm06Find4Target start steps j) := by
  rw [gm06Find4Darts, Option.map_eq_none_iff]
  exact gm06Find4_none_iff (gm06CandidateEnds m origins) ordinary incV incE upper start steps

end GraphMinor.Compute
