module

public import GraphMinor.Compute.Algorithm99SpecBounds
public import GraphMinor.Compute.Algorithm99SpecPost
public import GraphMinor.Compute.Algorithm99SpecBD
public import GraphMinor.Compute.Algorithm99WordSize
import GraphMinor.Compute.Join13WordSize72
import GraphMinor.Compute.Algorithm91Parse

/-!
# The inner caller program for Algorithm (9.9)

After the core run, the program reads the tag. The decomposition branch writes
parents and reordered leaves. The other branches split the model or the vertex
set and case-three block. Register 27 holds the final tag, and register 30
holds the tree size in the decomposition case.
-/

@[expose] public section
namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The completed inner output, before shifting into the caller's memory. -/
def Alg99SpecInnerOut (pp h ω C_blk w : ℕ) {m : ℕ} (G : MultiDigraph m)
    (Z : Finset (Fin m)) (s : State) : Prop :=
  (s.regs 27 = 0 ∧ ∃ (t : ℕ) (par f_tau : ℕ → ℕ),
    s.regs 30 = t ∧ (s.arrs 2).length = t ∧
    (∀ z < t, (s.arrs 2).getD z 0 = par z) ∧
    (s.arrs 3).length = (G.deleteVertices Z).numEdges ∧
    (∀ e < (G.deleteVertices Z).numEdges, (s.arrs 3).getD e 0 = f_tau e) ∧
    IsWrittenDigraphBD ω (G.deleteVertices Z).toComputeDigraph t par f_tau) ∨
  (s.regs 27 = 1 ∧ Alg99SpecOutII pp G Z (s.arrs 2)) ∨
  (s.regs 27 = 2 ∧ Alg99SpecOutIII pp h ω C_blk w G Z (s.arrs 2) (s.arrs 3))

/-- Handle all three output tags after the core run. -/
def alg99SpecHandleProg (B Q : ℕ) : Cmd :=
  .seq (.assign 27 (.read outArr (.const 0)))
    (.ite (.reg 27)
      (.seq (alg99SpecPostProg Q) (.assign 27 (.reg (Q + 12))))
      (alg99SpecBDProg (B + 8)))

/-- Run the core and handle its output. -/
def alg99SpecInnerProg (P72 P97 P : Cmd) (pp h : ℕ) (h2 : 2 ≤ h)
    (h' : ℕ) (h2' : 2 ≤ h') (B Q : ℕ) : Cmd :=
  .seq (alg99SpecCoreProg P72 P97 P pp h h2 h' h2' B Q) (alg99SpecHandleProg B Q)

/-- Word-size constant for the linear-size caller interface. -/
def alg99SpecWordConst (pp h h' c72 c97 c C_blk : ℕ) : ℕ :=
  2 * (5 * c72 + alg99WordConst pp h h' c97 c C_blk) + pp + C_blk + 20

/-- Time constant for the completed inner caller program. -/
def alg99SpecInnerConst (pp h' C72 C97 K4 C C_blk : ℕ) : ℕ :=
  alg99SpecCoreConst pp h' C72 C97 K4 C C_blk + 40 * (pp + C_blk + 3) + 1500

/-- A compact-graph decomposition output is handled in linear time. -/
private theorem alg99SpecHandle_zero {w m pp h ω C_blk B Q : ℕ}
    (G : MultiDigraph m) (Z : Finset (Fin m)) (code : List ℕ)
    (hB : 40 ≤ B) (hn : m + 1 < 2 ^ w)
    (hm : 3 + 3 * (G.deleteVertices Z).numEdges < 2 ^ w)
    (henc : (G.deleteVertices Z).enc.length < 2 ^ w) (s : State)
    (hout : s.arrs outArr = 0 :: code)
    (hbd : IsValidBranchDecompCode ω ((G.deleteVertices Z).deleteVerticesCompact Z) code)
    (hsrc : s.arrs (B + 8) = (G.deleteVertices Z).enc) :
    ∃ s' t, Exec w (alg99SpecHandleProg B Q) s s' t ∧
      t ≤ 1400 * (m + (G.deleteVertices Z).numEdges + 1) + 4 ∧
      Alg99SpecInnerOut pp h ω C_blk w G Z s' := by
  let s₁ := s.setReg 27 0
  have he₁ : Exec w (.assign 27 (.read outArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hout])
  obtain ⟨s₂, t₂, he₂, ht₂, hdata, hregs⟩ :=
    alg99SpecBDProg_exec_compact G Z code hbd (B + 8) (by omega) hn hm henc s₁
      hsrc hout
  refine ⟨s₂, 3 + (1 + t₂), .seq he₁ (.ite_false
    (by simp [s₁, Expr.eval, checkWord]) he₂), by omega, Or.inl ⟨?_, hdata⟩⟩
  exact (hregs 27 (by decide)).trans (by simp [s₁])

/-- A loop output is split into the two caller arrays, with its tag in 27. -/
private theorem alg99SpecHandle_loop {w m pp h ω C_blk B Q : ℕ}
    (G : MultiDigraph m) (Z : Finset (Fin m)) (out : List ℕ) (hQ : 100 ≤ Q)
    (hw : 3 < 2 ^ w) (hlen : out.length < 2 ^ w) (hwords : ∀ v ∈ out, v < 2 ^ w)
    (s : State) (hout : s.arrs outArr = out) (hrm : s.regs (Q + 6) = m)
    (hcase : (∃ a2, out = 1 :: a2 ∧ Alg99SpecOutII pp G Z a2) ∨
      (∃ a2 a3, out = 2 :: (a2 ++ a3) ∧ a2.length = m ∧
        Alg99SpecOutIII pp h ω C_blk w G Z a2 a3)) :
    ∃ s' t, Exec w (alg99SpecHandleProg B Q) s s' t ∧
      t ≤ 40 * out.length + 66 ∧ Alg99SpecInnerOut pp h ω C_blk w G Z s' := by
  have htag : ∃ tag tail, out = tag :: tail ∧ (tag = 1 ∨ tag = 2) := by
    rcases hcase with ⟨a, ha, _⟩ | ⟨a, b, ha, _⟩
    · exact ⟨1, a, ha, Or.inl rfl⟩
    · exact ⟨2, a ++ b, ha, Or.inr rfl⟩
  obtain ⟨tag, tail, heq, htag⟩ := htag
  have htagw : tag < 2 ^ w := by rcases htag with rfl | rfl <;> omega
  have htag0 : tag ≠ 0 := by rcases htag with rfl | rfl <;> decide
  let s₁ := s.setReg 27 tag
  have he₁ : Exec w (.assign 27 (.read outArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hout, heq, htagw])
  obtain ⟨s₂, t₂, he₂, ht₂, ha₂, hr₂, hdata⟩ :=
    alg99SpecPostProg_exec Q (fun _ => False) (Alg99SpecOutII pp G Z)
      (Alg99SpecOutIII pp h ω C_blk w G Z) (s := s₁) hout
      (by simpa [s₁, show Q + 6 ≠ 27 by omega] using hrm)
      (Or.inr hcase) hw hlen hwords
  have hfinaltag : s₂.regs (Q + 12) = 1 ∨ s₂.regs (Q + 12) = 2 := by
    rcases hdata with ⟨_, code, _, hf⟩ | ⟨ht, _⟩ | ⟨ht, _⟩
    · exact hf.elim
    · exact Or.inl ht
    · exact Or.inr ht
  have htw : s₂.regs (Q + 12) < 2 ^ w := by
    rcases hfinaltag with ht | ht <;> rw [ht] <;> omega
  let s₃ := s₂.setReg 27 (s₂.regs (Q + 12))
  have he₃ : Exec w (.assign 27 (.reg (Q + 12))) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, htw])
  refine ⟨s₃, 3 + (1 + (t₂ + 2)), .seq he₁ (.ite_true
    (by simp [s₁, Expr.eval, checkWord, htagw]) htag0 (.seq he₂ he₃)), by omega, ?_⟩
  rcases hdata with ⟨_, code, _, hf⟩ | ⟨ht, hp⟩ | ⟨ht, hp⟩
  · exact hf.elim
  · exact Or.inr (Or.inl ⟨by simpa [s₃] using ht, hp⟩)
  · exact Or.inr (Or.inr ⟨by simpa [s₃] using ht, hp⟩)

/-- The core plus output handling meets all three inner output specifications
under the caller's linear-size word bound. -/
theorem alg99SpecInnerProg_exec {pp h h' ω C72 c72 C97 c97 C C_blk c K4 : ℕ}
    {h2 : 2 ≤ h} {he : Even h} {h2' : 2 ≤ h'} {he' : Even h'}
    {P72 P97 P : Cmd} {B Q : ℕ}
    (hP72 : RunsAsSubroutine algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
      (fun s => s) C72 c72)
    (hP97 : RunsAsSubroutine (alg97Size (h' := h')) (encAlg97In (h' := h'))
      (IsAlg97Output pp (pp.choose 2 + 5) h h') P97 (fun m => m) C97 c97)
    (hP : Case3StepsRuns h h' ω h2 he h2' he' C C_blk c 23 16 (B + 5) 33
      (B - 1) (B - 2) (B - 3) (B - 4) (B + 6) (Q + 7) (Q + 10) P)
    (hK4 : ∀ n m, alg99Step4Cost (pp.choose 2 + 5) h h' B n m ≤ K4 * (n + m + 1))
    (hB : 40 ≤ B) (hB72 : folioCallerArrBase P72 ≤ B) (hB97 : folioCallerArrBase P97 ≤ B)
    (hQ : 100 ≤ Q) (hQ72 : folioCallerRegBase P72 ≤ Q) (hQ97 : folioCallerRegBase P97 ≤ Q)
    {m w : ℕ} (G : MultiDigraph m) (Z : Finset (Fin m)) (s : State)
    (hw : wordSize (alg99SpecWordConst pp h h' c72 c97 c C_blk)
      (m + (G.deleteVertices Z).numEdges + 1) ≤ w)
    (hsrc : s.arrs inArr = (G.deleteVertices Z).enc) (hZ : s.arrs outArr = bitSetList Z) :
    ∃ s' time, Exec w (alg99SpecInnerProg P72 P97 P pp h h2 h' h2' B Q) s s' time ∧
      time ≤ alg99SpecInnerConst pp h' C72 C97 K4 C C_blk *
        ((m + 1) * (m + (G.deleteVertices Z).numEdges + 1)) ∧
      Alg99SpecInnerOut pp h ω C_blk w G Z s' := by
  let N := m + (G.deleteVertices Z).numEdges + 1
  let S := (m + 1) * N
  let cw := alg99SpecWordConst pp h h' c72 c97 c C_blk
  have hc : 0 < cw := by unfold cw alg99SpecWordConst; omega
  have hlin : ∀ D ≤ cw, D * (N + 1) < 2 ^ w := fun D hD =>
    linear_lt_wordSize72 hc hD hw
  have hc4 : 4 ≤ cw := by unfold cw alg99SpecWordConst; omega
  have h4 := hlin 4 hc4
  have hblk := hlin C_blk (by unfold cw alg99SpecWordConst; omega)
  have hlenout := hlin (pp + C_blk + 3) (by unfold cw alg99SpecWordConst; omega)
  have hcore : wordSize (5 * c72 + alg99WordConst pp h h' c97 c C_blk)
      ((m + 1) * ((G.deleteVertices Z).numEdges + m + 1)) ≤ w := by
    rw [Nat.add_comm (G.deleteVertices Z).numEdges m]
    exact alg99_wordSize_core (by omega)
      ((wordSize_mono_left (by unfold alg99SpecWordConst; omega) N).trans hw)
  obtain ⟨s₁, t₁, he₁, ht₁, hcase⟩ :=
    alg99SpecCoreProg_exec hP72 hP97 hP hK4 hB hB72 hB97 (by omega) hQ72 hQ97 G Z
      hcore hsrc hZ
  rw [Nat.add_comm (G.deleteVertices Z).numEdges m] at ht₁
  have hNS : N ≤ S := Nat.le_mul_of_pos_left N (by omega)
  have hSpos : 1 ≤ S := (show 1 ≤ N by unfold N; omega).trans hNS
  rcases hcase with ⟨code, hout, hbd, hsave⟩ | ⟨hmreg, hloop⟩
  · have henc : (G.deleteVertices Z).enc.length < 2 ^ w := by
      have ha := MultiDigraph.numActivePairs_le_numEdges (G.deleteVertices Z)
      rw [MultiDigraph.length_enc]
      unfold N at h4
      omega
    obtain ⟨s₂, t₂, he₂, ht₂, hfinal⟩ :=
      alg99SpecHandle_zero (pp := pp) (h := h) (C_blk := C_blk) (Q := Q)
        G Z code hB (by unfold N at h4; omega) (by unfold N at h4; omega)
        henc s₁ hout hbd hsave
    refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hfinal⟩
    unfold alg99SpecInnerConst
    change t₁ + t₂ ≤ (_ + 40 * (pp + C_blk + 3) + 1500) * S
    change t₁ ≤ _ * S at ht₁
    change t₂ ≤ 1400 * N + 4 at ht₂
    nlinarith
  · have hsplit := alg99SpecOut_of_loopOut hloop
      (by unfold N at h4; omega) (by unfold N at h4; omega)
      (lt_of_le_of_lt (Nat.mul_le_mul_left C_blk (Nat.le_succ N)) hblk)
    have hbounds := alg99SpecOut_bounds G Z (s₁.arrs outArr) (by unfold N at h4; omega) hsplit
    have hlen : (s₁.arrs outArr).length < 2 ^ w :=
      hbounds.1.trans_lt ((Nat.mul_le_mul_left _ (Nat.le_succ N)).trans_lt hlenout)
    obtain ⟨s₂, t₂, he₂, ht₂, hfinal⟩ :=
      alg99SpecHandle_loop G Z (s₁.arrs outArr) hQ (by unfold N at h4; omega)
        hlen hbounds.2 s₁ rfl hmreg hsplit
    refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hfinal⟩
    unfold alg99SpecInnerConst
    change t₁ + t₂ ≤ (_ + 40 * (pp + C_blk + 3) + 1500) * S
    change t₁ ≤ _ * S at ht₁
    have hl : (s₁.arrs outArr).length ≤ (pp + C_blk + 3) * N := hbounds.1
    nlinarith

end GraphMinor.Compute
