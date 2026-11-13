module

public import GraphMinor.Compute.GM06CandidateCSR
public import GraphMinor.Compute.GM06BfsBuffered
public import GraphMinor.Compute.GM06Find4

/-!
# One actual candidate search in FIND_4

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) tries BFS
only after a contact passes the prefix test. This file proves the bounds
on those contact positions and connects the complete candidate-graph
construction to the exact BFS function. The source and target are
read from the linkage row. Neither adjacency arrays nor a path are
supplied as a result hypothesis.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Every eligible contact is a positive position in the linkage row. -/
theorem gm06Reduction4Contacts_bounds (incV incE : List ℕ) (start : ℕ)
    (steps : List (ℕ × ℕ)) {j : ℕ} (hj : j ∈ gm06Reduction4Contacts incV incE start steps) :
    0 < j ∧ j ≤ steps.length := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hj
  have hq' := List.mem_range.mp (List.mem_filter.mp hq).1
  omega

/-- A valid positive contact indexes the same arrival in the full
vertex row as in the pure FIND_4 target function. -/
theorem gm06Find4PathVertices_target {n : ℕ} (start : Fin n)
    (steps : List (ℕ × Fin n)) {j : ℕ} (hj : 0 < j) (hjr : j ≤ steps.length) :
    (gm06Find4PathVertices start steps)[j]?.getD 0 = (gm06Find4Target start steps j).val := by
  have hi : j - 1 < steps.length := by omega
  have hjs : j = (j - 1) + 1 := by omega
  rw [gm06Find4PathVertices, hjs, List.getElem?_cons_succ, List.getElem?_map,
    List.getElem?_eq_getElem hi]
  have hjsub : ((j - 1) + 1) - 1 = j - 1 := by omega
  simp only [gm06Find4Target, hjsub, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

/-- Build A_(i,j), read both terminals, and run the buffered BFS. -/
def gm06Try4Prog : Cmd :=
  .seq gm06CandidateCSRProg
    (.seq (.assign 644 (.read 609 (.const 0)))
      (.seq (.assign 645 (.read 609 (.reg 673))) gm06BfsBufferedProg))

/-- Complete scratch-register frame for one candidate attempt. -/
def gm06Try4Regs : List ℕ :=
  gm06CandidateCSRRegs ++ ([644, 645] ++ ([650] ++ List.range' 630 14 ++ [646, 647]))

/-- The candidate search keeps its input rotations, origins and linkage. -/
def gm06Try4Arrs : List ℕ := gm06CandidateCSRArrs ++ ([613, 622] ++ List.range' 630 5)

/-- One complete RAM attempt computes exactly BFS on the exact candidate
graph. Failure and successful simple paths therefore have the existing
BFS specification, with a quadratic bound for constructing and searching
this candidate. -/
theorem gm06Try4Prog_exec {w n m j : ℕ} (data : GM06CutData) (ordinary : List Bool)
    (incV incE upper path padding : List ℕ) (source target : Fin n) (s : State)
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
    (hpathLen : path.length < 2 ^ w) (hupperLen : upper.length < 2 ^ w) (hj : j < path.length)
    (hpath : ∀ x ∈ path, x < n) (hupper : ∀ x ∈ upper, x < n)
    (hsource : path[0]?.getD 0 = source.val) (htarget : path[j]?.getD 0 = target.val)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE) (h608 : s.arrs 608 = upper)
    (h609 : s.arrs 609 = path) (h624 : s.arrs 624 = ordinary.map Bool.toNat)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins) (h620 : s.regs 620 = n)
    (h649 : s.regs 649 = m) (h673 : s.regs 673 = j) :
    let G := gm06CandidateGraph n (gm06CandidateEnds m data.origins) ordinary incV incE upper path j
    ∃ sf t, Exec w gm06Try4Prog s sf t ∧
      t ≤ 320 + 251 * n + 150 * m + 100 * path.length + 100 * upper.length +
        78 * (n * n) + 129 * data.rotations.flatten.length ∧
      Keeps gm06Try4Regs gm06Try4Arrs s sf ∧
      gm06BfsPathResult sf = gm06BfsPathWords G (gm06OrderedNeighbours G) source target ∧
      (sf.regs 646 = 0 ∨ sf.regs 646 = 1) ∧
      sf.arrs 627 = gm06IncidenceBits (2 * m)
        (gm06CandidateDarts m data.origins ordinary incV incE upper path j) := by
  have hn : n < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hadj, hentries, hbits, hgs, hge, hbuf⟩ :=
    gm06CandidateCSRProg_exec data ordinary incV incE upper path padding s (by omega) hn hm hfit hlen
      horgLen hvalues hdarts hproper hinc hVlen hElen hordinary hVwords hEwords
      hpathLen hupperLen hj hpath hupper h606 h607 h608 h609 h624 h625 hcode hwords h626 h620 h649 h673
  let G := gm06CandidateGraph n (gm06CandidateEnds m data.origins) ordinary incV incE upper path j
  have h0 : 0 < path.length := by omega
  have hsource' : path[0] = source.val := by
    simpa only [List.getElem?_eq_getElem h0, Option.getD_some] using hsource
  have htarget' : path[j] = target.val := by
    simpa only [List.getElem?_eq_getElem hj, Option.getD_some] using htarget
  have hpath₁ : s₁.arrs 609 = path := (hk₁.2 609 (by
    simp [gm06CandidateCSRArrs, gm06CutAdjacencyArrs])).trans h609
  let s₂ := s₁.setReg 644 source.val
  let s₃ := s₂.setReg 645 target.val
  have he₂ : Exec w (.assign 644 (.read 609 (.const 0))) s₁ s₂ 3 := by
    apply Exec.assign
    have he := GraphMinor.Compute.Crossing.eval_read (w := w) (s := s₁) (a := 609)
      (GraphMinor.Compute.Crossing.eval_const (c := 0) (Nat.two_pow_pos w))
      (by simpa only [hpath₁] using h0) (by simpa only [hpath₁, hsource'] using source.isLt.trans hn)
    simpa only [hpath₁, hsource'] using he
  have he₃ : Exec w (.assign 645 (.read 609 (.reg 673))) s₂ s₃ 3 := by
    apply Exec.assign
    have hidx : s₂.regs 673 = j := by
      simpa only [s₂, State.setReg_regs_ne _ _ (by decide : 673 ≠ 644)] using
        (hk₁.1 673 (by simp [gm06CandidateCSRRegs, gm06CutAdjacencyRegs,
          gm06CutAdjacencyRowsRegs])).trans h673
    have ha : s₂.arrs 609 = path := hpath₁
    have he := GraphMinor.Compute.Crossing.eval_read (a := 609)
      (GraphMinor.Compute.Crossing.eval_reg hidx (hj.trans hpathLen))
      (by simpa only [ha] using hj) (by simpa only [ha, htarget'] using target.isLt.trans hn)
    simpa only [ha, htarget'] using he
  have hk₂₃ : Keeps [644, 645] [] s₁ s₃ :=
    ((Keeps.refl _ _ s₁).setReg (by simp) _).setReg (by simp) _
  have htotal := totalAdjEntries_le (gm06OrderedNeighbours_spec G)
  have hcanonicalLen : (encodeLists (gm06OrderedNeighbours G)).2.2.length < 2 ^ w := by
    rw [gm06EncodeLists_entries_length]
    omega
  obtain ⟨sf, tf, hef, htf, hkf, hdf, hflag⟩ := gm06BfsBufferedProg_exec
    G (gm06OrderedNeighbours G) (gm06OrderedNeighbours_spec G) source target s₃ hw hcanonicalLen
    ((hk₂₃.1 620 (by decide)).trans ((hk₁.1 620 (by
      simp [gm06CandidateCSRRegs, gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs])).trans h620))
    (by simp [s₃, s₂]) (by simp [s₃]) hgs hge
    (by simpa [GraphMinor.Compute.Crossing.IsBuf, s₃, s₂] using hbuf)
  have hk₁₃ : Keeps gm06Try4Regs gm06Try4Arrs s s₃ :=
    (hk₁.mono (by intro r hr; exact List.mem_append_left _ hr)
      (by intro a ha; exact List.mem_append_left _ ha)).trans hk₂₃
      (by intro r hr; exact List.mem_append_right _ (List.mem_append_left _ hr))
      (by simp)
  refine ⟨sf, t₁ + (3 + (3 + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    hk₁₃.trans hkf
      (by intro r hr; exact List.mem_append_right _ (List.mem_append_right _ hr))
      (by intro a ha; exact List.mem_append_right _ ha), hdf, hflag,
    (hkf.2 627 (by simp [List.mem_range'_1])).trans hbits⟩
  omega

end GraphMinor.Compute
