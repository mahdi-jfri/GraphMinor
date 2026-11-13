module

public import GraphMinor.Compute.Case3StepsCoreAttachmentKeysProg
public import GraphMinor.Compute.Case3StepsGroupLabelsProg

/-!
# The core and all raw-member group labels

The program constructs the compact society input, runs (8.6), computes its
core and attachment keys, and assigns labels to component and core-edge raw
members. The complete computation uses the case (iii) time and word bounds.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Construct the core and labels for all component and core-edge raw members. -/
def case3CoreGroupLabelsProg {h : ℕ} (h2 : 2 ≤ h) (shiloachProg : Cmd)
    (a_G a_VK a_W a_base r_base : ℕ) : Cmd :=
  .seq (case3CoreAttachmentKeysProg h2 shiloachProg a_G a_VK a_W a_base r_base)
    (case3GroupLabelsProg.shift a_base r_base)

/-- The core and all raw-member group labels obey one case (iii) time bound
and preserve caller storage below the scratch bases. -/
theorem case3CoreGroupLabelsProg_exec (h : ℕ) (h2 : 2 ≤ h) (he : Even h) (shiloachProg : Cmd)
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
              Exec w (case3CoreGroupLabelsProg h2 shiloachProg a_G a_VK a_W a_base r_base) s s' t ∧
              t ≤ C * (n + 1) * (G.numEdges + n + 1) ∧
              IsValidAlg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d ∧
              s'.arrs (a_base + 10) = bitSetList d.core.Z ∧
              s'.arrs (a_base + 12) = case3ComponentRows
                (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z ∧
              s'.arrs (a_base + 26) = case3AttachmentKeys
                (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z ∧
              s'.arrs (a_base + 27) = case3ComponentRepList
                (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z ∧
              s'.arrs (a_base + 28) = case3CoreEdgeRepList
                (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z ∧
              s'.arrs (a_base + 16) =
                [compassCard W, (case3InputEdges (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)).length] ++
                  flatEdges (case3InputEdges (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)) ∧
              s'.arrs (a_base + 3) = (case3CompactCompassMultigraph (G.deleteVertices X) W).enc ∧
              s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1) ∧
              (∀ a < a_base, s'.arrs a = s.arrs a) ∧
              (∀ r < r_base, s'.regs r = s.regs r) := by
  have hcore := case3CoreAttachmentKeysProg_exec h h2 he shiloachProg h86
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
  obtain ⟨_, hkn, _, hm⟩ := case3Component_word_bounds hk ha hsize hpow₃
  obtain ⟨hw4, hkeys⟩ := case3Attachment_word_bounds hk hsize hpow₃
  have hsum := case3GroupLabels_word_bound hk ha hsize hpow₃
  obtain ⟨s₁, t₁, d, hex₁, ht₁, hd, hZ, hrows, htab, hD, hrank, harr₁, hreg₁⟩ :=
    hrun a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj
      ((wordSize_mono_left (Nat.le_max_left c₀ 3) N).trans hw) s hin hVK hWall
  change Alg86DivisionOutput x at d
  change IsValidAlg86DivisionOutput x d at hd
  have hD' : s₁.arrs (3 + a_base) = D.enc := by rw [Nat.add_comm 3 a_base]; exact hD
  have hZ' : s₁.arrs (10 + a_base) = bitSetList d.core.Z := by rw [Nat.add_comm 10 a_base]; exact hZ
  have htab' : s₁.arrs (26 + a_base) = case3AttachmentKeys x d.core.Z := by
    rw [Nat.add_comm 26 a_base]
    exact htab
  have hcall := @case3GroupLabelsProg_shift_exec w x D rfl d hd a_base r_base hw4 hkn hkeys hm hsum s₁
  have hcall₁ := hcall hD'
  have hcall₂ := hcall₁ hZ'
  have hcall₃ := hcall₂ htab'
  obtain ⟨s₂, t₂, hex₂, ht₂, hcRep₂, heRep₂, henc₂, harr₂, hreg₂⟩ := hcall₃
  have ht₂' : t₂ ≤ 1000 * N := ht₂.trans (case3GroupLabels_cost_le hk ha)
  refine ⟨s₂, t₁ + t₂, d, .seq hex₁ hex₂, ?_, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_assoc] at ht₁ ⊢
    rw [Nat.add_mul]
    exact Nat.add_le_add ht₁ ht₂'
  · exact (harr₂ (a_base + 10) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hZ
  · exact (harr₂ (a_base + 12) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hrows
  · exact (harr₂ (a_base + 26) (by omega) (by omega) (by omega) (by omega) (by omega)).trans htab
  · simpa only [Nat.add_comm 27 a_base] using hcRep₂
  · simpa only [Nat.add_comm 28 a_base] using heRep₂
  · simpa only [Nat.add_comm 16 a_base, encGraph, case3InputEdges] using henc₂
  · exact (harr₂ (a_base + 3) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hD
  · exact (harr₂ (a_base + 2) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hrank
  · intro a ha'
    exact (harr₂ a (by romega) (by romega) (by romega) (by romega) (by romega)).trans (harr₁ a ha')
  · intro r hr
    exact (hreg₂ r hr).trans (hreg₁ r hr)

end GraphMinor.Compute
