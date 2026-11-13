module

public import GraphMinor.Compute.GM06LivePuncturedCandidate
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Finding a live component disjoint from the linkage

For Reduction 2 in VI (5.7), page 133, scan every vertex label.
For each live source, compute its component after removing the
chosen initial vertex and test its protected linkage vertices.
Keep the first successful source. A prefix invariant gives the
exact result of this search and a polynomial running time.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- The source candidates determined by the finite active graph and two vertex masks. -/
noncomputable def gm06PuncturedSourceCandidates {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (Q A : Finset (Fin n)) : List (Option ℕ) :=
  List.ofFn fun source : Fin n => if source ∈ A ∧
    (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0
    then some source.val else none

/-- Search all live sources, retaining the first successful one in 113/114. -/
def gm06FindPuncturedComponentProg (ends active guarded live : Arr) : Cmd :=
  .seq (.assign 113 (.const 0)) (.seq (.assign 187 (.const 0))
    (forUp 187 (.reg 100) (gm06LivePuncturedCandidateProg ends active guarded live)))

/-- The full source scan returns exactly the first live component
with zero protected intersection, in polynomial time. -/
theorem gm06FindPuncturedComponentProg_exec {w n : ℕ} (ends active guarded live : Arr)
    (he28 : ends < 28) (ha28 : active < 28) (hp28 : guarded < 28) (hl28 : live < 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (Q A : Finset (Fin n))
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd) (hQ : s.arrs guarded = gm02VertexBits Q)
    (hA : s.arrs live = gm02VertexBits A) (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w (gm06FindPuncturedComponentProg ends active guarded live) s s' t ∧
      t ≤ 7 + n * (53 * (n * n) + 64 * n + 48 * tagged.length + 78) ∧
      gm06SingletonRegs ((gm06PuncturedSourceCandidates tagged cut Q A).foldl Option.or none) s' ∧
      (∀ a : ℕ, a < 28 → s'.arrs a = s.arrs a) ∧ s'.regs 100 = n ∧ s'.regs 135 = cut.val := by
  classical
  let candidates := gm06PuncturedSourceCandidates tagged cut Q A
  let chosen := fun i => (candidates.take i).foldl Option.or none
  let budget := 53 * (n * n) + 64 * n + 48 * tagged.length + 71
  have hlen : candidates.length = n := List.length_ofFn
  let Inv : ℕ → State → Prop := fun i st => st.regs 187 = i ∧ st.regs 100 = n ∧
    st.regs 135 = cut.val ∧ (∀ a : ℕ, a < 28 → st.arrs a = s.arrs a) ∧
    gm06SingletonRegs (chosen i) st
  let s₁ := s.setReg 113 0
  let s₂ := s₁.setReg 187 0
  have he₁ : Exec w (.assign 113 (.const 0)) s s₁ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 187 (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂], by simpa [s₂, s₁] using hN,
      by simpa [s₂, s₁] using hcut, fun _ _ => rfl, ?_⟩
    simp [chosen, gm06SingletonRegs, s₂, s₁]
  obtain ⟨s', t, hex, ht, hInv⟩ := forUp_exec' (r_i := 187) (hi := .reg 100)
    (body := gm06LivePuncturedCandidateProg ends active guarded live) Inv n budget (by omega) hn
    (fun i _ st h => ⟨h.1, eval_reg h.2.1 hn⟩)
    (fun i hi st h => by
      let source : Fin n := ⟨i, hi⟩
      obtain ⟨st₁, t₁, he, ht₁, hf, harrays, hN₁, hcut₁, hsource₁⟩ :=
        gm06LivePuncturedCandidateProg_exec ends active guarded live he28 ha28 hp28 hl28
          tagged cut source Q A (chosen i) hw hn hsquare hm hbits
          ((h.2.2.2.1 ends he28).trans ha) ((h.2.2.2.1 active ha28).trans hb)
          ((h.2.2.2.1 guarded hp28).trans hQ) ((h.2.2.2.1 live hl28).trans hA)
          h.2.1 h.2.2.1 h.1 h.2.2.2.2
      have hchoose : chosen (i + 1) = (chosen i).or (candidates[i]'(hlen ▸ hi)) := by
        dsimp only [chosen]
        rw [List.take_add_one, List.getElem?_eq_getElem (hlen ▸ hi), Option.toList_some,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hci : candidates[i]'(hlen ▸ hi) = (if source ∈ A ∧
          (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0
          then some source.val else none) := by
        simp only [candidates, gm06PuncturedSourceCandidates, List.getElem_ofFn, source]
      refine ⟨st₁, t₁, he, ht₁, ⟨by simp, by simpa using hN₁, by simpa using hcut₁,
        fun a ha' => (harrays a ha').trans (h.2.2.2.1 a ha'), ?_⟩, hsource₁⟩
      rw [hchoose, hci]
      simpa only [gm06SingletonRegs, State.setReg_regs_ne _ _ (by decide : 113 ≠ 187),
        State.setReg_regs_ne _ _ (by decide : 114 ≠ 187)] using hf) s₂ hInv₀
  have heq : 1 + 6 + budget = 53 * (n * n) + 64 * n + 48 * tagged.length + 78 := by
    dsimp [budget]
    omega
  simp only [Expr.cost] at ht
  rw [heq] at ht
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ hex), by omega, ?_, hInv.2.2.2.1,
    hInv.2.1, hInv.2.2.1⟩
  simpa only [chosen, ← hlen, List.take_length] using hInv.2.2.2.2

end GraphMinor.Compute
