module

public import GraphMinor.Compute.GM06FirstSuccessLoop
public import GraphMinor.Compute.GM06Reduction4ContactProgram

/-!
# FIND_4 on one cut component

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) first
computes the running prefix tests, then tries eligible contacts in order.
Each attempt builds its own exact candidate graph and runs BFS. This
file composes those verified programs and proves their exact pure
FIND_4 output. The loop contract is discharged by the actual candidate
and BFS execution theorem. The outer component loop belongs to the
caller, which supplies that component's face-incidence rows.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Scan eligible contacts and return the first successful exact BFS. -/
def gm06Find4Prog : Cmd :=
  .seq gm06Reduction4ContactsProg
    (.seq (.assign 676 (.const 0))
      (.seq (.assign 677 (.len 617))
        (.seq (.assign 646 (.const 0)) (gm06FirstSuccessLoop gm06Try4Prog))))

/-- Complete register frame of the prefix scan and first-success search. -/
def gm06Find4Regs : List ℕ :=
  [650, 652, 653, 672, 674] ++ ([673, 676, 677, 678] ++ gm06Try4Regs)

/-- Complete array frame of FIND_4. -/
def gm06Find4Arrs : List ℕ := [611, 617] ++ gm06Try4Arrs

/-- A cubic polynomial bound for the full contact scan and searches. -/
def gm06Find4Cost (n m r upperCount dartCount : ℕ) : ℕ :=
  36 + r * (523 + 251 * n + 150 * m + 100 * r + 100 * upperCount + 78 * (n * n) + 129 * dartCount)

/-- Actual FIND_4 computes the exact pure first-success function from
incidence, boundary, linkage and graph data. Its hypotheses describe
only those inputs and word/index bounds, and include no search result. -/
theorem gm06Find4Prog_exec {w n m : ℕ} (data : GM06CutData) (ordinary : List Bool)
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
    ∃ sf t, Exec w gm06Find4Prog s sf t ∧
      t ≤ gm06Find4Cost n m steps.length upper.length data.rotations.flatten.length ∧
      Keeps gm06Find4Regs gm06Find4Arrs s sf ∧
      gm06Find4Result sf = gm06Find4 (gm06CandidateEnds m data.origins) ordinary incV incE upper start steps ∧
      (sf.regs 646 = 0 ∨ sf.regs 646 = 1) := by
  have hn : n < 2 ^ w := by omega
  have hEfit : m < 2 ^ w := by omega
  let natSteps := steps.map (fun step => (step.1, step.2.val))
  let contacts := gm06Reduction4Contacts incV incE start.val natSteps
  let vertices := gm06Find4PathVertices start steps
  let search := gm06Find4Attempt (gm06CandidateEnds m data.origins) ordinary incV incE upper start steps
  let B := 320 + 251 * n + 150 * m + 100 * vertices.length + 100 * upper.length +
    78 * (n * n) + 129 * data.rotations.flatten.length
  have hnatLen : natSteps.length = steps.length := List.length_map _
  have hcontactsLen : contacts.length ≤ steps.length := by
    simpa only [hnatLen] using gm06Reduction4Contacts_length_le incV incE start.val natSteps
  have hverticesLen : vertices.length = steps.length + 1 := by
    simp only [vertices, gm06Find4PathVertices, List.length_cons, List.length_map]
  have hvertices : ∀ x ∈ vertices, x < n := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact h ▸ start.isLt
    · obtain ⟨step, _, rfl⟩ := List.mem_map.mp h
      exact step.2.isLt
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, _⟩ := gm06Reduction4ContactsProg_exec incV incE start.val natSteps s
    (by omega) (by simpa only [hnatLen] using hstepsFit) (hVlen ▸ hn) (hElen ▸ hEfit)
    (hVlen ▸ start.isLt)
    (fun step hs => by
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hs
      exact ⟨hElen ▸ hstepEdges original horiginal, hVlen ▸ original.2.isLt⟩) hVwords hEwords h606 h607
    (by simpa only [natSteps, gm06Find4PathVertices, List.map_map, Function.comp_def, Prod.snd] using h609)
    (by simpa only [natSteps, List.map_map, Function.comp_def, Prod.fst] using h610)
  let s₂ := s₁.setReg 676 0
  let s₃ := s₂.setReg 677 contacts.length
  let s₄ := s₃.setReg 646 0
  have he₂ : Exec w (.assign 676 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₃ : Exec w (.assign 677 (.len 617)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_len (w := w) (by simpa [s₂] using hd₁) (by omega))
  have he₄ : Exec w (.assign 646 (.const 0)) s₃ s₄ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₄ : Keeps gm06Find4Regs gm06Find4Arrs s s₄ :=
    (((hk₁.mono (by intro r hr; exact List.mem_append_left _ hr)
      (by intro a ha; exact List.mem_append_left _ ha)).setReg (by simp [gm06Find4Regs]) _).setReg
        (by simp [gm06Find4Regs]) _).setReg (by decide) _
  obtain ⟨sf, tf, hef, htf, hkf, hdf, hflags⟩ := gm06FirstSuccessLoop_exec (w := w) (B := B) gm06Try4Prog search gm06Try4Regs gm06Try4Arrs
    (by decide) (by decide) (by decide) (by decide) [] contacts s₄ (by omega)
    (by simp only [List.length_nil]; omega)
    (fun j hj => by
      have hb := gm06Reduction4Contacts_bounds incV incE start.val natSteps hj
      rw [hnatLen] at hb
      omega)
    (by simpa [s₄, s₃, s₂] using hd₁) (by simp [s₄, s₃, s₂]) (by simp [s₄, s₃]) (by simp [s₄])
    (fun j hj st hk hr => by
      have hc := gm06Reduction4Contacts_bounds incV incE start.val natSteps hj
      rw [hnatLen] at hc
      have hctx : Keeps gm06Find4Regs gm06Find4Arrs s st :=
        hk₄.trans hk (by intro r hr; exact List.mem_append_right _ hr)
          (by intro a ha; exact List.mem_append_right _ ha)
      obtain ⟨st', t', he', ht', hk', hd', hf', _⟩ := gm06Try4Prog_exec data ordinary incV incE upper
        vertices padding start (gm06Find4Target start steps j) st hw hm hfit hlen horgLen hvalues hdarts
        hproper hinc hVlen hElen hordinary hVwords hEwords
        (by rw [hverticesLen]; omega) hupperLen (by rw [hverticesLen]; omega) hvertices hupper
        (by simp [vertices, gm06Find4PathVertices]) (gm06Find4PathVertices_target start steps hc.1 hc.2)
        ((hctx.2 606 (by decide)).trans h606) ((hctx.2 607 (by decide)).trans h607)
        ((hctx.2 608 (by decide)).trans h608) ((hctx.2 609 (by decide)).trans h609)
        ((hctx.2 624 (by decide)).trans h624) ((hctx.2 625 (by decide)).trans h625)
        (by rw [hctx.2 625 (by decide)]; exact hcode)
        (by rw [hctx.2 625 (by decide)]; exact hwords)
        ((hctx.2 626 (by decide)).trans h626) ((hctx.1 620 (by decide)).trans h620)
        ((hctx.1 649 (by decide)).trans h649) hr
      exact ⟨st', t', he', ht', hk', by simpa only [search, gm06Find4Attempt, gm06Find4Graph, vertices] using hd', hf'⟩)
  refine ⟨sf, t₁ + (2 + (2 + (2 + tf))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef))), ?_,
    hk₄.trans hkf (by intro r hr; exact List.mem_append_right _ hr)
      (by intro a ha; exact List.mem_append_right _ ha), hdf, hflags⟩
  · rw [hnatLen] at ht₁
    have hmult := Nat.mul_le_mul_right (B + 18) hcontactsLen
    dsimp only [B] at htf hmult
    rw [hverticesLen] at htf hmult
    unfold gm06Find4Cost
    nlinarith only [ht₁, htf, hmult]

end GraphMinor.Compute
