module

public import GraphMinor.Compute.Case3StepsCoreComponentsProg
public import GraphMinor.Compute.Case3StepsAttachmentKeysProg

/-!
# The core and all component attachment keys

The program runs (8.6), recovers its core, computes the outside components,
and writes the four-word key of each component's attachment set. All these
steps share the case (iii) running-time and word-size bounds.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Construct the core, component rows, and attachment keys in scratch storage. -/
def case3CoreAttachmentKeysProg {h : ℕ} (h2 : 2 ≤ h) (shiloachProg : Cmd)
    (a_G a_VK a_W a_base r_base : ℕ) : Cmd :=
  .seq (case3CoreComponentsProg h2 shiloachProg a_G a_VK a_W a_base r_base)
    (case3AttachmentKeysProg.shift a_base r_base)

/-- The core, components, and their attachment keys obey the case (iii) time
bound and preserve caller storage below the scratch bases. -/
theorem case3CoreAttachmentKeysProg_exec (h : ℕ) (h2 : 2 ≤ h) (he : Even h) (shiloachProg : Cmd)
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
              Exec w (case3CoreAttachmentKeysProg h2 shiloachProg a_G a_VK a_W a_base r_base) s s' t ∧
              t ≤ C * (n + 1) * (G.numEdges + n + 1) ∧
              IsValidAlg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d ∧
              s'.arrs (a_base + 10) = bitSetList d.core.Z ∧
              s'.arrs (a_base + 12) = case3ComponentRows
                (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z ∧
              s'.arrs (a_base + 26) = case3AttachmentKeys
                (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d.core.Z ∧
              s'.arrs (a_base + 3) = (case3CompactCompassMultigraph (G.deleteVertices X) W).enc ∧
              s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1) ∧
              (∀ a < a_base, s'.arrs a = s.arrs a) ∧
              (∀ r < r_base, s'.regs r = s.regs r) := by
  have hcore := case3CoreComponentsProg_exec h h2 he shiloachProg h86
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
  have hmSimple : (case3InputEdges x).length ≤ D.numActivePairs := case3InputEdges_length_le x D rfl
  have hpow : (N + 2) ^ c < 2 ^ w :=
    (pow_lt_two_pow_wordSize (by omega) N).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hpow₃ : (N + 2) ^ 3 < 2 ^ w :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ N + 2) (Nat.le_max_right c₀ 3)).trans_lt hpow
  obtain ⟨_, hkn, hsq, hm⟩ := case3Component_word_bounds hk ha hsize hpow₃
  obtain ⟨hw4, hkeys⟩ := case3Attachment_word_bounds hk hsize hpow₃
  obtain ⟨s₁, t₁, d, hex₁, ht₁, hd, hZ, hrows, hD, hrank, harr₁, hreg₁,
      hadj, hentries, hr14⟩ :=
    hrun a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj
      ((wordSize_mono_left (Nat.le_max_left c₀ 3) N).trans hw) s hin hVK hWall
  change Alg86DivisionOutput x at d
  change IsValidAlg86DivisionOutput x d at hd
  have hadj' : IsAdjList x.G (19 + a_base) (20 + a_base) (21 + a_base)
      (edgeNeighbors (case3InputEdges x)) s₁ := by
    simpa only [Nat.add_comm 19 a_base, Nat.add_comm 20 a_base, Nat.add_comm 21 a_base] using hadj
  have hentries' : (s₁.arrs (21 + a_base)).length < 2 ^ w := by
    rw [Nat.add_comm 21 a_base, hentries]
    change 2 * (case3InputEdges x).length < 2 ^ w
    omega
  have hrows' : s₁.arrs (12 + a_base) = case3ComponentRows x d.core.Z := by
    rw [Nat.add_comm 12 a_base]
    exact hrows
  have hZ' : s₁.arrs (10 + a_base) = bitSetList d.core.Z := by
    rw [Nat.add_comm 10 a_base]
    exact hZ
  have hr14' : s₁.regs (14 + r_base) = x.n := by
    rw [Nat.add_comm 14 r_base]
    exact hr14
  have hcall := @case3AttachmentKeysProg_shift_exec w x d hd
    (edgeNeighbors (case3InputEdges x)) a_base r_base hw4 hkn hsq hkeys s₁
  have hcall₁ := hcall hrows'
  have hcall₂ := hcall₁ hZ'
  have hcall₃ := hcall₂ hadj'
  have hcall₄ := hcall₃ hentries'
  have hcall₅ := hcall₄ hr14'
  obtain ⟨s₂, t₂, hex₂, ht₂, hkeys₂, harr₂, hreg₂⟩ := hcall₅
  have htot : totalAdjEntries (edgeNeighbors (case3InputEdges x)) =
      2 * (case3InputEdges x).length :=
    totalAdjEntries_edgeNeighbors _ (isSimpleEdgeList_edgeListOf x.G).1
  rw [htot] at ht₂
  have ht₂' : t₂ ≤ 1000 * N := ht₂.trans (case3AttachmentKeys_cost_le hk (hmSimple.trans ha))
  refine ⟨s₂, t₁ + t₂, d, .seq hex₁ hex₂, ?_, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_assoc] at ht₁ ⊢
    rw [Nat.add_mul]
    exact Nat.add_le_add ht₁ ht₂'
  · exact (harr₂ (a_base + 10) (by omega)).trans hZ
  · exact (harr₂ (a_base + 12) (by omega)).trans hrows
  · simpa only [Nat.add_comm 26 a_base] using hkeys₂
  · exact (harr₂ (a_base + 3) (by omega)).trans hD
  · exact (harr₂ (a_base + 2) (by omega)).trans hrank
  · intro a ha'
    exact (harr₂ a (by romega)).trans (harr₁ a ha')
  · intro r hr
    exact (hreg₂ r hr).trans (hreg₁ r hr)

end GraphMinor.Compute
