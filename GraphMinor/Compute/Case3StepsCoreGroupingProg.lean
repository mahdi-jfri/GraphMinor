module

public import GraphMinor.Compute.Case3StepsCoreGroupLabelsProg
public import GraphMinor.Compute.Case3StepsGroupingShift
public import GraphMinor.Compute.Case3StepsRoutingData
public import GraphMinor.Compute.Case3StepsGroupingBounds
public import GraphMinor.Compute.Case3StepsCompactSelectedDivision

/-!
# Uniform computation of the compass division routing tables

The supplied (8.6) computation yields a valid compact compass division.
Its computed representative arrays feed all routing passes. Corner neighbors
supply division coverage, and the common polynomial word bound covers every
counter and table address. The complete computation has the case (iii) time
bound with constants chosen before the caller's storage indices.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Compute the compact division and all tables used to encode its members. -/
def case3CoreGroupingProg {h : ℕ} (h2 : 2 ≤ h) (shiloachProg : Cmd)
    (a_G a_VK a_W a_base r_base : ℕ) : Cmd :=
  .seq (case3CoreGroupLabelsProg h2 shiloachProg a_G a_VK a_W a_base r_base)
    (case3GroupingProg.shift a_base r_base)

/-- The compact division, selected members, and exact multigraph routing
tables are computed within one uniform case (iii) time and word-size bound. -/
theorem case3CoreGroupingProg_exec (h : ℕ) (h2 : 2 ≤ h) (he : Even h) (shiloachProg : Cmd)
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
            ∃ x : Alg81Input,
              x = case3CompactSocietyInput (G.deleteVertices X) W h2 he hW ∧
            ∃ D : MultiDigraph x.n,
              HEq D (case3CompactCompassMultigraph (G.deleteVertices X) W) ∧
            ∃ (s' : State) (t : ℕ)
              (d : Alg86DivisionOutput x),
              Exec w (case3CoreGroupingProg h2 shiloachProg a_G a_VK a_W a_base r_base) s s' t ∧
              t ≤ C * (n + 1) * (G.numEdges + n + 1) ∧
              IsValidAlg86DivisionOutput x d ∧
              (∀ a ∈ case3RoutingArrayIndices,
                s'.arrs (a_base + a) = case3RoutingArray x D d.core.Z a) ∧
              s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1) ∧
              (∀ r ∈ case3RoutingRegIndices, s'.regs (r_base + r) = case3RoutingReg x D r) ∧
              (∀ a < a_base, s'.arrs a = s.arrs a) ∧ (∀ r < r_base, s'.regs r = s.regs r) := by
  have hcore := case3CoreGroupLabelsProg_exec h h2 he shiloachProg h86
  obtain ⟨C₀, c₀, hC₀, hc₀, hrun⟩ := hcore
  let c := max c₀ 3
  refine ⟨C₀ + 1000, c, by omega, by omega, ?_⟩
  intro a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj hw s hin hVK hWall
  let N := (n + 1) * (G.numEdges + n + 1)
  let x : Alg81Input := case3CompactSocietyInput (G.deleteVertices X) W h2 he hW
  let D₀ := case3CompactCompassMultigraph (G.deleteVertices X) W
  let D : MultiDigraph x.n := D₀
  have hsize : n + G.numEdges + 1 ≤ N := by dsimp only [N]; nlinarith
  have hk : x.n ≤ n := by
    change W.compassFinset.card ≤ n
    exact (Finset.card_le_univ W.compassFinset).trans (Finset.card_fin n).le
  have ha : D.numActivePairs ≤ G.numEdges :=
    (case3CompactCompass_numActivePairs_le G X W hdisj).trans G.numActivePairs_le_numEdges
  have hmle := case3InputEdges_length_le x D rfl
  have hpow : (N + 2) ^ c < 2 ^ w :=
    (pow_lt_two_pow_wordSize (by omega) N).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hpow₃ : (N + 2) ^ 3 < 2 ^ w :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ N + 2) (Nat.le_max_right c₀ 3)).trans_lt hpow
  obtain ⟨_, hkn, hsq, hA⟩ := case3Component_word_bounds hk ha hsize hpow₃
  obtain ⟨hw4, hkeys⟩ := case3Attachment_word_bounds hk hsize hpow₃
  have hsum₀ := case3GroupLabels_word_bound hk ha hsize hpow₃
  have hsum : x.n + (case3InputEdges x).length < 2 ^ w := by omega
  have hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, d, hex₁, ht₁, hd, hZ, _, htab, hreps, hedges, henc, hD, hrank, harr₁, hreg₁⟩ :=
    hrun a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj
      ((wordSize_mono_left (Nat.le_max_left c₀ 3) N).trans hw) s hin hVK hWall
  change Alg86DivisionOutput x at d
  change IsValidAlg86DivisionOutput x d at hd
  have hR := case3CompactSelectedMembers_isRuralDivision (G.deleteVertices X) W h2 he hW d hd
  have hcall := @case3GroupingProg_shift_exec w x D rfl d hd hR.isDivision a_base r_base
    hw4 hkn hsq hkeys hm hsum hA s₁
  have hcall₁ := hcall (by simpa only [Nat.add_comm 3 a_base] using hD)
  have hcall₂ := hcall₁ (by simpa only [Nat.add_comm 16 a_base, encGraph, case3InputEdges] using henc)
  have hcall₃ := hcall₂ (by simpa only [Nat.add_comm 10 a_base] using hZ)
  have hcall₄ := hcall₃ (by simpa only [Nat.add_comm 26 a_base] using htab)
  have hcall₅ := hcall₄ (by simpa only [Nat.add_comm 27 a_base] using hreps)
  obtain ⟨s₂, t₂, hex₂, ht₂, hmask₂, hloop₂, hmat₂, hheads₂, hnext₂, hcounts₂,
      hn₂, hm₂, hL₂, hA₂, harr₂, hreg₂⟩ :=
    hcall₅ (by simpa only [Nat.add_comm 28 a_base] using hedges)
  have ht₂' : t₂ ≤ 1000 * N := ht₂.trans (case3Grouping_cost_le hk hmle ha)
  have hkeep (a : ℕ) (ha : a < a_base) : s₂.arrs a = s₁.arrs a :=
    harr₂ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨x, rfl, D, HEq.rfl, s₂, t₁ + t₂, d, .seq hex₁ hex₂, ?_, hd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_assoc] at ht₁ ⊢
    rw [Nat.add_mul]
    exact Nat.add_le_add ht₁ ht₂'
  · intro a ha
    simp only [case3RoutingArrayIndices, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals dsimp only [case3RoutingArray]
    · exact (harr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hD
    · exact (harr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hZ
    · have hs := (harr₂ (a_base + 16) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans henc
      simpa only [encGraph, case3InputEdges] using hs
    · exact (harr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans htab
    · exact (harr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hreps
    · exact (harr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hedges
    · simpa only [Nat.add_comm 29 a_base] using hmask₂
    · simpa only [Nat.add_comm 33 a_base] using hloop₂
    · simpa only [Nat.add_comm 34 a_base] using hmat₂
    · simpa only [Nat.add_comm 35 a_base] using hheads₂
    · simpa only [Nat.add_comm 36 a_base] using hnext₂
    · simpa only [Nat.add_comm 37 a_base] using hcounts₂
  · exact (harr₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hrank
  · intro r hr
    simp only [case3RoutingRegIndices, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals dsimp only [case3RoutingReg]
    · simpa only [Nat.add_comm 14 r_base] using hn₂
    · simpa only [Nat.add_comm 17 r_base] using hm₂
    · simpa only [Nat.add_comm 52 r_base] using hL₂
    · simpa only [Nat.add_comm 64 r_base] using hA₂
  · intro a ha
    exact (hkeep a ha).trans (harr₁ a ha)
  · intro r hr
    exact (hreg₂ r hr).trans (hreg₁ r hr)

end GraphMinor.Compute
