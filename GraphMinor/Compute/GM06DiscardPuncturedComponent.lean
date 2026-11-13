module

public import GraphMinor.Compute.GM06SelectPuncturedComponent
public import GraphMinor.Compute.GM06RetainComponentMasks
public import GraphMinor.Compute.GM06VertexReachBits
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Removing a computed linkage-disjoint component

For a fixed initial vertex in VI (5.7), page 133, search the
punctured active graph for a live component with no linkage vertex.
On success, install the induced live and active-edge masks. The
live vertex count strictly decreases. On failure, the working
masks remain unchanged and every live source meets the linkage.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Search at vertex 135 and discard the chosen linkage-disjoint component. -/
def gm06DiscardPuncturedComponentProg : Cmd :=
  .seq (gm06SelectPuncturedComponentProg 3 12 17 14)
    (.ite (.reg 113) gm06RetainComponentMasksProg .skip)

/-- The computed deletion branch installs exact induced masks and
strictly lowers the live vertex count, or excludes every eligible source. -/
theorem gm06DiscardPuncturedComponentProg_exec {w n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (Q A : Finset (Fin n))
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs 12 = tagged.map Prod.snd) (hQ : s.arrs 17 = gm02VertexBits Q)
    (hA : s.arrs 14 = gm02VertexBits A) (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w gm06DiscardPuncturedComponentProg s s' t ∧
      t ≤ 90 + n * (53 * (n * n) + 64 * n + 48 * tagged.length + 78) +
        53 * (n * n) + 78 * n + 88 * tagged.length ∧
      (∀ a : ℕ, a < 28 → a ≠ 12 → a ≠ 14 → a ≠ 15 → a ≠ 16 → s'.arrs a = s.arrs a) ∧
      s'.regs 100 = n ∧ s'.regs 135 = cut.val ∧
      ((s'.regs 113 = 0 ∧ s'.arrs 14 = gm02VertexBits A ∧ s'.arrs 12 = tagged.map Prod.snd ∧
          ∀ source ∈ A,
            (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card ≠ 0) ∨
        ∃ source : Fin n, s'.regs 113 = 1 ∧ s'.regs 114 = source.val ∧ source ∈ A ∧
          (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0 ∧
          s'.arrs 14 = gm02VertexBits (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
          s'.arrs 12 = gm06InducedEdgeBits tagged
            (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
          (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card < A.card) := by
  classical
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, ha₁, hN₁, hcut₁, hout₁⟩ :=
    gm06SelectPuncturedComponentProg_exec 3 12 17 14 (by decide) (by decide) (by decide) (by decide)
      tagged cut Q A hw hn hsquare hm hbits ha hb hQ hA hN hcut
  rcases hout₁ with ⟨hflag, hexclude⟩ | ⟨source, hflag, hlabel, hsourceA, hzero, hreach⟩
  · refine ⟨s₁, t₁ + 2, .seq he₁ (.ite_false (eval_reg hflag (Nat.two_pow_pos w)) (.skip s₁)),
      by omega, fun a ha' _ _ _ _ => ha₁ a ha', hN₁, hcut₁, Or.inl ?_⟩
    exact ⟨hflag, (ha₁ 14 (by decide)).trans hA, (ha₁ 12 (by decide)).trans hb, hexclude⟩
  · let R := reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source
    have hremoved : s₁.arrs 33 = gm02VertexBits R :=
      hreach.trans (gm06VertexReachData_eq_vertexBits (gm06PuncturedGraphData tagged cut) source)
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hA₂, hE₂⟩ := gm06RetainComponentMasksProg_exec tagged A R s₁
      hw hn hm hbits ((ha₁ 3 (by decide)).trans ha) ((ha₁ 12 (by decide)).trans hb)
      ((ha₁ 14 (by decide)).trans hA) hremoved
    have hstrict : (A \ R).card < A.card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.sdiff_subset, ?_⟩
      intro heq
      have hsourceR : source ∈ R := (mem_reachSet _ source source).mpr (.refl source)
      have hh : source ∈ A \ R := heq.symm ▸ hsourceA
      exact (Finset.mem_sdiff.mp hh).2 hsourceR
    refine ⟨s₂, t₁ + (1 + t₂), .seq he₁ (.ite_true (eval_reg hflag hw1) (by decide) he₂),
      by omega, ?_, ?_, ?_, Or.inr ?_⟩
    · intro a ha' h12 h14 h15 h16
      exact (hk₂.2 a (by simp [h12, h14, h15, h16])).trans (ha₁ a ha')
    · exact (hk₂.1 100 (by decide)).trans hN₁
    · exact (hk₂.1 135 (by decide)).trans hcut₁
    · exact ⟨source, (hk₂.1 113 (by decide)).trans hflag,
        (hk₂.1 114 (by decide)).trans hlabel, hsourceA, hzero, hA₂, hE₂, hstrict⟩

end GraphMinor.Compute
