module

public import GraphMinor.Compute.Case3StepsCoreProg
public import GraphMinor.Compute.Case3StepsComponentBounds

/-!
# The core call followed by outside-component searches

The step (5) program writes the compact society input, runs (8.6), recovers
its returned core, and computes the outside components. The execution theorem
uses the supplied (8.6) computation theorem and one common word-size bound.
The retained multigraph and rank array remain available for writing members.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Construct the core and all outside-component rows in scratch storage. -/
def case3CoreComponentsProg {h : ℕ} (h2 : 2 ≤ h) (shiloachProg : Cmd)
    (a_G a_VK a_W a_base r_base : ℕ) : Cmd :=
  .seq (case3CoreProg h2 shiloachProg a_G a_VK a_W a_base r_base)
    (case3DecodedComponentsProg.shift a_base r_base)

/-- The core call and component searches obey the case (iii) time bound and
preserve caller storage below the scratch bases. -/
theorem case3CoreComponentsProg_exec (h : ℕ) (h2 : 2 ≤ h) (he : Even h) (shiloachProg : Cmd)
    (h86 : ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg86Output x (decAlg86Out x out))
      (alg86Prog shiloachProg) (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (a_G a_VK a_W a_base r_base : ℕ),
        a_G < a_base → a_VK < a_base → a_W < a_base →
        ∀ (w n : ℕ) (G : MultiDigraph n) (X : Finset (Fin n))
          (W : WallOfHeight h (G.deleteVertices X)) (hW : W.IsValid),
          W.IsFlatWall h2 → Disjoint W.compassFinset X →
          wordSize c ((n + 1) * (G.numEdges + n + 1)) ≤ w →
          ∀ s : State, s.arrs a_G = G.enc → s.arrs a_VK = bitSetList W.compassFinset →
            s.arrs a_W = W.encList →
            ∃ (s' : State) (t : ℕ)
              (d : Alg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)),
              Exec w (case3CoreComponentsProg h2 shiloachProg a_G a_VK a_W a_base r_base) s s' t ∧
              t ≤ C * (n + 1) * (G.numEdges + n + 1) ∧
              IsValidAlg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d ∧
              s'.arrs (a_base + 10) = bitSetList d.core.Z ∧
              s'.arrs (a_base + 12) = case3ComponentRows
                (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z ∧
              s'.arrs (a_base + 3) = (case3CompactCompassMultigraph (G.deleteVertices X) W).enc ∧
              s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1) ∧
              (∀ a < a_base, s'.arrs a = s.arrs a) ∧
              (∀ r < r_base, s'.regs r = s.regs r) ∧
              IsAdjList (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW).G
                (a_base + 19) (a_base + 20) (a_base + 21)
                (edgeNeighbors (case3InputEdges (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW))) s' ∧
              (s'.arrs (a_base + 21)).length =
                2 * (case3InputEdges (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)).length ∧
              s'.regs (r_base + 14) = compassCard W := by
  have hcore := case3CoreProg_exec h h2 he shiloachProg h86
  obtain ⟨C₀, c₀, hC₀, hc₀, hrun⟩ := hcore
  let c := max c₀ 3
  refine ⟨C₀ + 1000, c, by omega, by omega, ?_⟩
  intro a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj hw s hin hVK hWall
  let N := (n + 1) * (G.numEdges + n + 1)
  let x := case3CompactSocietyInput (G.deleteVertices X) W h2 he hW
  let D := case3CompactCompassMultigraph (G.deleteVertices X) W
  have hsize : n + G.numEdges + 1 ≤ N := by dsimp only [N]; nlinarith
  have hk : x.n ≤ n := by
    change W.compassFinset.card ≤ n
    exact (Finset.card_le_univ W.compassFinset).trans (Finset.card_fin n).le
  have ha : D.numActivePairs ≤ G.numEdges :=
    (case3CompactCompass_numActivePairs_le G X W hdisj).trans G.numActivePairs_le_numEdges
  have hpow : (N + 2) ^ c < 2 ^ w :=
    (pow_lt_two_pow_wordSize (by omega) N).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hpow₃ : (N + 2) ^ 3 < 2 ^ w :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ N + 2) (Nat.le_max_right c₀ 3)).trans_lt hpow
  obtain ⟨hw3, hkn, hsq, hm⟩ := case3Component_word_bounds hk ha hsize hpow₃
  obtain ⟨s₁, t₁, d, hex₁, ht₁, hdec, hd, hlen, hD, hrank, harr₁, hreg₁⟩ :=
    hrun a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj
      ((wordSize_mono_left (Nat.le_max_left c₀ 3) N).trans hw) s hin hVK hWall
  change Alg86DivisionOutput x at d
  change decAlg86Out x (s₁.arrs (a_base + 9)) = Sum.inr d at hdec
  have hD' : s₁.arrs (3 + a_base) = D.enc := by
    rw [Nat.add_comm 3 a_base]
    exact hD
  have hraw' : s₁.arrs (9 + a_base) = s₁.arrs (a_base + 9) := by
    rw [Nat.add_comm 9 a_base]
  have hDG : D.toSimpleGraph = x.G := rfl
  have hlocal := @case3DecodedComponentsProg_shift_exec w x D hDG
    (s₁.arrs (a_base + 9)) d hdec a_base r_base
  have hlocal₁ := hlocal hw3
  have hlocal₂ := hlocal₁ hkn
  have hlocal₃ := hlocal₂ hsq
  have hlocal₄ := hlocal₃ hm
  have hlocal₅ := hlocal₄ hlen (s := s₁)
  have hlocal₆ := hlocal₅ hD'
  have hlocal₇ := hlocal₆ hraw'
  obtain ⟨s₂, t₂, hex₂, ht₂, hrows, hZ, harr₂, hreg₂, hadj₂, hentries₂, hr14₂⟩ := hlocal₇
  have ht₂' : t₂ ≤ 1000 * N := ht₂.trans (case3Component_cost_le hk ha)
  refine ⟨s₂, t₁ + t₂, d, .seq hex₁ hex₂, ?_, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_assoc] at ht₁ ⊢
    rw [Nat.add_mul]
    exact Nat.add_le_add ht₁ ht₂'
  · simpa only [Nat.add_comm] using hZ
  · simpa only [Nat.add_comm] using hrows
  · exact (harr₂ (a_base + 3) (by omega)).trans hD
  · exact (harr₂ (a_base + 2) (by omega)).trans hrank
  · intro a ha'
    exact (harr₂ a (by romega)).trans (harr₁ a ha')
  · intro r hr
    exact (hreg₂ r hr).trans (hreg₁ r hr)
  · simpa only [case3InputEdges, Nat.add_comm 19 a_base, Nat.add_comm 20 a_base, Nat.add_comm 21 a_base] using hadj₂
  · simpa only [case3InputEdges, Nat.add_comm 21 a_base] using hentries₂
  · simpa only [Nat.add_comm 14 r_base] using hr14₂

end GraphMinor.Compute
