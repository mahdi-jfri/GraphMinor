module

public import GraphMinor.Compute.GM02SaveFirstChoice
public import GraphMinor.Compute.GM02PortAssignment
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Validating the two choices of one pattern edge

Check the first endpoint, save its data, and check the second endpoint.
The final expression combines the incidence bits and the loop condition.
Thus the command proves exactly the local data conditions of a split
choice, without assuming any path or containment conclusion.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Check both decoded choices for pattern position 43 and save validity in register 50. -/
@[expose] def gm02CheckPatternChoiceProg (src : Arr) : Cmd :=
  .seq (gm02CheckEndpointChoiceProg src false)
    (.seq gm02SaveFirstChoiceProg
      (.seq (gm02CheckEndpointChoiceProg src true) (.assign 50 gm02ChoicePairExpr)))

/-- The per-edge validator computes exactly incidence at both ends and distinct choices for a loop. -/
theorem gm02CheckPatternChoiceProg_exec {w K code : ℕ} (x : GM02TopologicalInput)
    (s : State) (src : Arr) (flags : List ℕ) (f : Fin x.edges.length)
    (hK : x.edges.length ≤ K) (hsrc : s.arrs src = x.enc)
    (harr : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (hflags : s.arrs 20 = flags) (hlen : flags.length = x.G.edges.length)
    (hbits : ∀ b ∈ flags, b ≤ 1) (hf : s.regs 43 = f.val)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hm : s.regs 11 = x.G.edges.length)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hKw : 2 * K < 2 ^ w)
    (hmw : x.G.edges.length + 1 < 2 ^ w) (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02CheckPatternChoiceProg src) s s' t ∧ t ≤ 124 ∧
      s'.regs 50 = (if
        (∀ side, (gm02ActiveGraph x.G.graph flags).Inc
          (gm02PortAssignmentOfCode x code (f, side)).val
          (if side then (x.ends f).2 else (x.ends f).1)) ∧
        ((x.ends f).1 = (x.ends f).2 →
          gm02PortAssignmentOfCode x code (f, false) ≠ gm02PortAssignmentOfCode x code (f, true))
        then 1 else 0) ∧ s'.arrs = s.arrs ∧ s'.regs 43 = s.regs 43 ∧
      (∀ r, r ≠ 32 → (r < 42 ∨ 50 < r) → s'.regs r = s.regs r) := by
  let a := (x.ends f).1
  let b := (x.ends f).2
  let e := (gm02PortAssignmentOfCode x code (f, false)).val
  let g := (gm02PortAssignmentOfCode x code (f, true)).val
  let P := (gm02ActiveGraph x.G.graph flags).Inc e a
  let Q := (gm02ActiveGraph x.G.graph flags).Inc g b
  have haw : a < 2 ^ w := (x.edges[f.val]'f.isLt).1.isLt.trans hn
  have hbw : b < 2 ^ w := (x.edges[f.val]'f.isLt).2.isLt.trans hn
  have hew : e < 2 ^ w := (gm02PortAssignmentOfCode x code (f, false)).isLt.trans hmw
  have hgw : g < 2 ^ w := (gm02PortAssignmentOfCode x code (f, true)).isLt.trans hmw
  have hpword : (if P then 1 else 0) < 2 ^ w := by split <;> omega
  obtain ⟨s₁, t₁, he₁, ht₁, hp, he, ha, ha₁, hr₁⟩ :=
    gm02CheckEndpointChoiceProg_exec x s src flags f false hK hsrc harr hflags hlen hbits hf hoff hm
      hw hn hKw hmw henc
  obtain ⟨s₂, he₂, hp₂, he₂val, ha₂val, ha₂, hr₂⟩ :=
    gm02SaveFirstChoiceProg_exec s₁ hp he ha hpword hew haw
  have hregs (r : Reg) (hr : r ≠ 32) (hrange : r < 42 ∨ 49 < r) : s₂.regs r = s.regs r := by
    have h₁ : r ≠ 42 ∧ r ≠ 44 ∧ r ≠ 45 ∧ r ≠ 46 := by dsimp only [Reg] at *; omega
    have h₂ : r ≠ 47 ∧ r ≠ 48 ∧ r ≠ 49 := by dsimp only [Reg] at *; omega
    exact (hr₂ r h₂.1 h₂.2.1 h₂.2.2).trans (hr₁ r hr h₁.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2)
  obtain ⟨s₃, t₃, he₃, ht₃, hq, hg, hb, ha₃, hr₃⟩ :=
    gm02CheckEndpointChoiceProg_exec x s₂ src flags f true hK
      ((congrFun ha₂ src).trans ((congrFun ha₁ src).trans hsrc))
      ((congrFun ha₂ 23).trans ((congrFun ha₁ 23).trans harr))
      ((congrFun ha₂ 20).trans ((congrFun ha₁ 20).trans hflags)) hlen hbits
      ((hr₂ 43 (by decide) (by decide) (by decide)).trans
        (hr₁ 43 (by decide) (by decide) (by decide) (by decide) (by decide)) |>.trans hf)
      ((hregs 16 (by decide) (Or.inl (by decide))).trans hoff)
      ((hregs 11 (by decide) (Or.inl (by decide))).trans hm) hw hn hKw hmw henc
  have hpair := gm02ChoicePairExpr_eval s₃ P Q a b e g
    ((hr₃ 47 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp₂) hq
    ((hr₃ 49 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha₂val) hb
    ((hr₃ 48 (by decide) (by decide) (by decide) (by decide) (by decide)).trans he₂val) hg
    (by omega) haw hbw hew hgw
  let bit := if P ∧ Q ∧ (a = b → e ≠ g) then 1 else 0
  let s₄ := s₃.setReg 50 bit
  have he₄ : Exec w (.assign 50 gm02ChoicePairExpr) s₃ s₄ 14 := .assign hpair
  refine ⟨s₄, t₁ + (6 + (t₃ + 14)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega, ?_,
    ha₃.trans (ha₂.trans ha₁), ?_, ?_⟩
  · rw [show s₄.regs 50 = bit from State.setReg_regs_self ..]
    dsimp only [bit]
    congr 1
    apply propext
    constructor
    · rintro ⟨hP, hQ, hloop⟩
      refine ⟨?_, ?_⟩
      · intro side
        cases side
        · exact hP
        · exact hQ
      · intro hab heq
        exact hloop hab (congrArg Fin.val heq)
    · rintro ⟨hinc, hloop⟩
      exact ⟨hinc false, hinc true, fun hab heq => hloop hab (Fin.ext heq)⟩
  · exact (State.setReg_regs_ne s₃ bit (by decide : (43 : Reg) ≠ 50)).trans
      ((hr₃ 43 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hr₂ 43 (by decide) (by decide) (by decide)).trans
          (hr₁ 43 (by decide) (by decide) (by decide) (by decide) (by decide))))
  · intro r hr hrange
    have hn₁ : r ≠ 42 ∧ r ≠ 44 ∧ r ≠ 45 ∧ r ≠ 46 ∧ r ≠ 50 := by dsimp only [Reg] at *; omega
    exact (State.setReg_regs_ne s₃ bit hn₁.2.2.2.2).trans
      ((hr₃ r hr hn₁.1 hn₁.2.1 hn₁.2.2.1 hn₁.2.2.2.1).trans
        (hregs r hr (by dsimp only [Reg] at *; omega)))

end GraphMinor.Compute
