module

public import GraphMinor.Compute.GM06CutComponentRowLoop

/-!
# Initialized cuff-order component membership program

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns the
cut components in inner cuff-gap order. This program allocates its own
membership-row buffer from the runtime number of inner cuff edges
and copied vertices. It initializes all counters and returns exactly
the encoded finite membership rows. The loop constructs every row
by a search from that cuff edge's computed origin.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Allocate membership-row storage and initialize cuff-order counters. -/
def gm06CutComponentRowsInitProg : Cmd :=
  .seq (.alloc 600 (.op .add (.const 1) (.op .mul (.len 609) (.op .add (.reg 620) (.const 1)))))
    (.seq (.write 600 (.const 0) (.len 609))
      (.seq (.assign 655 (.const 1))
        (.seq (.assign 667 (.const 0)) (.assign 668 (.len 609)))))

/-- Exact initialization from actual cuff count and permanent vertex count. -/
theorem gm06CutComponentRowsInitProg_exec {w n : ℕ} (inner : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (hfit : 3 + inner.length * (n + 1) < 2 ^ w)
    (h609 : s.arrs 609 = inner) (h620 : s.regs 620 = n) :
    ∃ sf t, Exec w gm06CutComponentRowsInitProg s sf t ∧ t = 17 + inner.length * (n + 1) ∧
      Keeps [655, 667, 668] [600] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 600 655 [inner.length] (inner.length * (n + 1)) sf ∧
      sf.regs 667 = 0 ∧ sf.regs 668 = inner.length := by
  let cap := inner.length * (n + 1)
  have hk : inner.length ≤ cap := by
    dsimp only [cap]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left inner.length (by omega : 1 ≤ n + 1)
  have hcap : cap < 2 ^ w := by dsimp only [cap]; omega
  have hkFit : inner.length < 2 ^ w := hk.trans_lt hcap
  let s₀ := s.setArr 600 (List.replicate (1 + cap) 0)
  let s₁ := s₀.writeArr 600 0 inner.length
  let s₂ := s₁.setReg 655 1
  let s₃ := s₂.setReg 667 0
  let sf := s₃.setReg 668 inner.length
  have he₀ : Exec w (.alloc 600 (.op .add (.const 1) (.op .mul (.len 609) (.op .add (.reg 620) (.const 1)))))
      s s₀ (7 + (1 + cap)) :=
    .alloc (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_const hw)
      (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_len h609 hkFit)
        (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg h620 (by omega))
          (GraphMinor.Compute.Crossing.eval_const hw) hn) hcap) (by omega))
  have he₁ : Exec w (.write 600 (.const 0) (.len 609)) s₀ s₁ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_len (by simpa [s₀] using h609) hkFit) (by simp [s₀])
  have he₂ : Exec w (.assign 655 (.const 1)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have he₃ : Exec w (.assign 667 (.const 0)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₄ : Exec w (.assign 668 (.len 609)) s₃ sf 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_len (by simpa [s₃, s₂, s₁, s₀, State.writeArr] using h609) hkFit)
  refine ⟨sf, (7 + (1 + cap)) + (3 + (2 + (2 + 2))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))),
    by dsimp only [cap]; omega, ?_, ?_, by simp [sf, s₃], by simp [sf]⟩
  · exact (((((Keeps.refl _ _ s).setArr (by simp) _).writeArr (by simp) _ _).setReg (by simp) _).setReg
      (by simp) _).setReg (by simp) _
  · have hrep : List.replicate (1 + cap) 0 = 0 :: List.replicate cap 0 := by
      rw [Nat.add_comm, List.replicate_succ]
    simp [GraphMinor.Compute.Crossing.IsBuf, sf, s₃, s₂, s₁, s₀, State.writeArr, hrep, cap]

/-- Initialize and search all inner cuff gaps in order. -/
def gm06CutComponentRowsProg : Cmd := .seq gm06CutComponentRowsInitProg gm06CutComponentRowsLoop

/-- Read the membership-row prefix produced by the cuff-order searches. -/
def gm06CutComponentRowsResult (s : State) : List ℕ := (s.arrs 600).take (s.regs 655)

/-- Exact initialized membership-row output, with a polynomial bound
in cuff count and the finite graph sizes. Every row comes from its
actual inner cuff dart. The original cut graph and CSR arrays survive. -/
theorem gm06CutComponentRowsProg_exec {w n m : ℕ} (data : GM06CutData) (inner : List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (hfit : 3 + inner.length * (n + 1) < 2 ^ w)
    (horgFit : data.origins.length < 2 ^ w)
    (hindices : ∀ i, i < inner.length → 4 * (m + i) < data.origins.length)
    (hvalues : ∀ v ∈ data.origins, v < n)
    (h609 : s.arrs 609 = inner) (h620 : s.regs 620 = n) (h649 : s.regs 649 = m)
    (h626 : s.arrs 626 = data.origins)
    (hadj : IsAdjList (gm06CutGraph n data) 620 621 622 (gm06CutAdjacencyLists n data) s)
    (hentries : (s.arrs 622).length < 2 ^ w) :
    ∃ sf t, Exec w gm06CutComponentRowsProg s sf t ∧
      t ≤ 18 + inner.length * (91 + 40 * n + 29 * totalAdjEntries (gm06CutAdjacencyLists n data)) ∧
      Keeps gm06CutComponentRowsRegs [600, 630, 631, 632, 633] s sf ∧
      gm06CutComponentRowsResult sf = gm06EncodeRows (gm06CutComponentBitsFrom n data m 0 inner.length) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hb₁, hi₁, hc₁⟩ := gm06CutComponentRowsInitProg_exec inner s hw1 hn hfit h609 h620
  have hcountFit : inner.length < 2 ^ w := by
    have hle : inner.length ≤ inner.length * (n + 1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left inner.length (by omega : 1 ≤ n + 1)
    omega
  obtain ⟨sf, tf, hef, htf, hkf, hbf, _, _⟩ := gm06CutComponentRowsLoop_exec
    (base := 0) (k := inner.length) (cap := inner.length * (n + 1)) data [inner.length] s₁
    hw (by omega) (by omega) horgFit (fun i _ hi => hindices i (by omega)) hvalues le_rfl
    (by simp only [List.length_singleton]; omega)
    ((hk₁.1 620 (by decide)).trans h620) ((hk₁.1 649 (by decide)).trans h649) hi₁ hc₁
    ((hk₁.2 626 (by decide)).trans h626)
    (hadj.of_arrs_eq (hk₁.2 620 (by decide)) (hk₁.2 621 (by decide)) (hk₁.2 622 (by decide)))
    (by rw [hk₁.2 622 (by decide)]; exact hentries) hb₁
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_,
    (hk₁.mono (by simp [gm06CutComponentRowsRegs]) (by simp)).trans hkf (fun _ h => h) (fun _ h => h), ?_⟩
  · nlinarith only [ht₁, htf]
  · rw [gm06CutComponentRowsResult, hbf.2, hbf.1, List.take_left]
    simp only [gm06EncodeRows, gm06CutComponentBitsFrom_length, List.singleton_append]

end GraphMinor.Compute
