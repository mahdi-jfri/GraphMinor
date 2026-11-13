module

public import GraphMinor.Compute.GM06Reduction2Frames
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning all initial vertices for Reduction 2

The ordinary inner-cuff row lists the initial vertices. Test them
in that order. After the first successful loop or component update,
skip the remaining tests, so the resulting masks describe one
reduction of the input drawing. If every test fails, the exact
finite exclusions hold at every supplied initial vertex.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Scan the initial-vertex labels in array 6 and apply the first Reduction 2 update. -/
def gm06Reduction2ScanProg : Cmd :=
  .seq (.assign 294 (.const 0)) (.seq (.assign 290 (.const 0))
    (forUp 290 (.len 6)
      (.ite (.reg 294) .skip
        (.seq (.assign 135 (.read 6 (.reg 290))) gm06Reduction2AtVertexProg))))

/-- The scan excludes both finite tests at every supplied initial
vertex or performs exactly one of the verified mask updates. -/
theorem gm06Reduction2ScanProg_exec {w n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cuts : List (Fin n)) (Q A : Finset (Fin n))
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hcuts : cuts.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1) {s : State}
    (ha : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs 12 = tagged.map Prod.snd) (hc : s.arrs 6 = cuts.map Fin.val)
    (hQ : s.arrs 17 = gm02VertexBits Q) (hA : s.arrs 14 = gm02VertexBits A)
    (hN : s.regs 100 = n) :
    ∃ s' t, Exec w gm06Reduction2ScanProg s s' t ∧
      t ≤ 7 + cuts.length * (137 + n * (53 * (n * n) + 64 * n + 48 * tagged.length + 78) +
        53 * (n * n) + 93 * n + 129 * tagged.length) ∧
      (∀ a : ℕ, a < 28 → a ≠ 12 → a ≠ 14 → a ≠ 15 → a ≠ 16 → a ≠ 22 → a ≠ 23 →
        s'.arrs a = s.arrs a) ∧ s'.regs 100 = n ∧
      ((s'.regs 294 = 0 ∧ s'.arrs 14 = gm02VertexBits A ∧ s'.arrs 12 = tagged.map Prod.snd ∧
          ∀ cut ∈ cuts,
            (∀ source ∈ A,
              (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card ≠ 0) ∧
            ∀ j : Fin tagged.length, ¬ (tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut)) ∨
        ∃ cut ∈ cuts, s'.regs 135 = cut.val ∧
          ((s'.regs 294 = 1 ∧ s'.arrs 14 = gm02VertexBits A ∧
            ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut ∧
              s'.arrs 12 = (tagged.map Prod.snd).set j.val 0 ∧
              (s'.arrs 12).count 1 + 1 = (tagged.map Prod.snd).count 1) ∨
           (s'.regs 294 = 2 ∧ ∃ source : Fin n, source ∈ A ∧
            (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0 ∧
            s'.arrs 14 = gm02VertexBits (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
            s'.arrs 12 = gm06InducedEdgeBits tagged
              (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
            (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card < A.card))) := by
  let budget := 126 + n * (53 * (n * n) + 64 * n + 48 * tagged.length + 78) +
    53 * (n * n) + 93 * n + 129 * tagged.length
  let Failed := fun cut : Fin n =>
    (∀ source ∈ A, (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card ≠ 0) ∧
      ∀ j : Fin tagged.length, ¬ (tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut)
  let Outcome := fun st : State => ∃ cut ∈ cuts, st.regs 135 = cut.val ∧
    ((st.regs 294 = 1 ∧ st.arrs 14 = gm02VertexBits A ∧
      ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut ∧
        st.arrs 12 = (tagged.map Prod.snd).set j.val 0 ∧
        (st.arrs 12).count 1 + 1 = (tagged.map Prod.snd).count 1) ∨
     (st.regs 294 = 2 ∧ ∃ source : Fin n, source ∈ A ∧
      (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0 ∧
      st.arrs 14 = gm02VertexBits (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
      st.arrs 12 = gm06InducedEdgeBits tagged
        (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
      (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card < A.card))
  let Frame := fun st : State => ∀ a : ℕ, a < 28 → a ≠ 12 → a ≠ 14 → a ≠ 15 → a ≠ 16 →
    a ≠ 22 → a ≠ 23 → st.arrs a = s.arrs a
  let Inv : ℕ → State → Prop := fun i st => st.regs 290 = i ∧ st.regs 100 = n ∧ Frame st ∧
    ((st.regs 294 = 0 ∧ st.arrs 14 = gm02VertexBits A ∧ st.arrs 12 = tagged.map Prod.snd ∧
      ∀ j (hj : j < cuts.length), j < i → Failed cuts[j]) ∨ Outcome st)
  have hw1 : 1 < 2 ^ w := by omega
  let s₁ := s.setReg 294 0
  let s₂ := s₁.setReg 290 0
  have he₁ : Exec w (.assign 294 (.const 0)) s s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 290 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂], by simpa [s₂, s₁] using hN, fun _ _ _ _ _ _ _ _ => rfl,
      Or.inl ⟨by simp [s₂, s₁], hA, hb, ?_⟩⟩
    intro j hj hj0
    omega
  obtain ⟨s', t, he, ht, hInv⟩ := forUp_exec' (r_i := 290) (hi := .len 6)
    (body := .ite (.reg 294) .skip
      (.seq (.assign 135 (.read 6 (.reg 290))) gm06Reduction2AtVertexProg))
    Inv cuts.length (4 + budget) hw1 hcuts
    (fun i _ st h => ⟨h.1, by simpa only [List.length_map] using
      (GraphMinor.Compute.Crossing.eval_len
        ((h.2.2.1 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc)
        (by simpa only [List.length_map] using hcuts))⟩)
    (fun i hi st h => by
      rcases h with ⟨hidx, hsize, hframe, hcase⟩
      rcases hcase with ⟨hflag, hverts, hedges, hfailed⟩ | hsuccess
      · have hcSt : st.arrs 6 = cuts.map Fin.val :=
          (hframe 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
        let cut := cuts[i]
        have hread : (Expr.read 6 (.reg 290)).eval w st = some cut.val := by
          simpa only [hcSt, List.getElem_map] using
            (eval_read (a := 6) (eval_reg hidx (hi.trans hcuts))
              (by simpa only [hcSt, List.length_map] using hi)
              (by simpa only [hcSt, List.getElem_map] using cut.isLt.trans hn))
        let st₀ := st.setReg 135 cut.val
        have he₀ : Exec w (.assign 135 (.read 6 (.reg 290))) st st₀ 3 := .assign hread
        obtain ⟨st₁, t₁, he₁, ht₁, ha₁, hN₁, hcut₁, hout₁⟩ := gm06Reduction2AtVertexProg_exec
          (s := st₀) tagged cut Q A hw hn hsquare hm hbits
          ((hframe 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha)
          hedges ((hframe 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hQ)
          hverts (by simpa [st₀] using hsize) (by simp [st₀])
        have hcounter : st₁.regs 290 = i :=
          (gm06Reduction2AtVertexProg_reg290 he₁).trans (by simpa [st₀] using hidx)
        have hframe₁ : Frame st₁ := fun a ha' h12 h14 h15 h16 h22 h23 =>
          (ha₁ a ha' h12 h14 h15 h16 h22 h23).trans (hframe a ha' h12 h14 h15 h16 h22 h23)
        refine ⟨st₁, 1 + (3 + t₁), .ite_false (eval_reg hflag (Nat.two_pow_pos w)) (.seq he₀ he₁),
          by dsimp [budget] at *; omega, ⟨by simp, by simpa using hN₁, hframe₁, ?_⟩, hcounter⟩
        rcases hout₁ with ⟨hz, hv₁, he₁arr, hc₁, hl₁⟩ | hloop | hcomponent
        · left
          refine ⟨by simpa using hz, hv₁, he₁arr, ?_⟩
          intro j hj hji
          by_cases hji' : j = i
          · subst j
            exact ⟨hc₁, hl₁⟩
          · exact hfailed j hj (by omega)
        · right
          refine ⟨cut, List.getElem_mem hi, by simpa using hcut₁, Or.inl ?_⟩
          simpa only [State.setReg_regs_ne _ _ (by decide : 294 ≠ 290), State.setReg_arrs] using hloop
        · right
          refine ⟨cut, List.getElem_mem hi, by simpa using hcut₁, Or.inr ?_⟩
          simpa only [State.setReg_regs_ne _ _ (by decide : 294 ≠ 290), State.setReg_arrs] using hcomponent
      · have hflag : st.regs 294 = 1 ∨ st.regs 294 = 2 := by
          obtain ⟨cut, _, _, hh | hh⟩ := hsuccess
          · exact Or.inl hh.1
          · exact Or.inr hh.1
        have hword : st.regs 294 < 2 ^ w := hflag.elim (fun hh => hh ▸ hw1) (fun hh => hh ▸ hw)
        have hnz : st.regs 294 ≠ 0 := by rcases hflag with h | h <;> omega
        refine ⟨st, 2, .ite_true (eval_reg rfl hword) hnz (.skip st), by dsimp [budget]; omega,
          ⟨by simp, by simpa using hsize, hframe, Or.inr ?_⟩, hidx⟩
        simpa only [Outcome, State.setReg_regs_ne _ _ (by decide : 135 ≠ 290),
          State.setReg_regs_ne _ _ (by decide : 294 ≠ 290), State.setReg_arrs] using hsuccess) s₂ hInv₀
  have hbudget : 1 + 6 + (4 + budget) = 137 + n *
      (53 * (n * n) + 64 * n + 48 * tagged.length + 78) +
      53 * (n * n) + 93 * n + 129 * tagged.length := by dsimp [budget]; omega
  simp only [Expr.cost] at ht
  rw [hbudget] at ht
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ he), by omega, hInv.2.2.1, hInv.2.1, ?_⟩
  rcases hInv.2.2.2 with ⟨hz, hv, heArr, hfailed⟩ | hsuccess
  · left
    refine ⟨hz, hv, heArr, ?_⟩
    intro cut hcut
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hcut
    exact hfailed j hj hj
  · exact Or.inr hsuccess

end GraphMinor.Compute
