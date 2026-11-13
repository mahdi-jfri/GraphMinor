module

public import GraphMinor.Compute.GM06PuncturedComponent
public import GraphMinor.Compute.GM02CountIntersection
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Counting linkage vertices in a punctured component

For Reduction 2 in VI (5.7), page 133, first compute the source
component after deleting the chosen initial vertex. Then count
its intersection with the guarded linkage vertices. The count
comes from the actual reachability bits, rather than a supplied
component certificate. A zero count tests whether this component
can be discarded without removing linkage vertices.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Search a punctured component and count its guarded vertices in 183. -/
def gm06PuncturedProtectedCountProg (ends active guarded : Arr) : Cmd :=
  .seq (gm06PuncturedComponentProg ends active)
    (.seq (.assign 40 (.reg 100)) (gm02CountIntersectionProg guarded 33))

/-- The query computes the exact guarded intersection size and
preserves the endpoint, activity, and linkage arrays. -/
theorem gm06PuncturedProtectedCountProg_exec {w n : ℕ} (ends active guarded : Arr)
    (he28 : ends < 28) (ha28 : active < 28) (hp28 : guarded < 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut source : Fin n) (Q : Finset (Fin n))
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd) (hQ : s.arrs guarded = gm02VertexBits Q)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) (hsource : s.regs 187 = source.val) :
    ∃ s' t, Exec w (gm06PuncturedProtectedCountProg ends active guarded) s s' t ∧
      t ≤ 53 * (n * n) + 64 * n + 48 * tagged.length + 57 ∧
      s'.regs 183 = (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card ∧
      s'.arrs 33 = gm06VertexReachData (gm06PuncturedGraphData tagged cut) source ∧
      (∀ a : ℕ, a < 28 → s'.arrs a = s.arrs a) ∧
      s'.regs 100 = n ∧ s'.regs 135 = cut.val ∧ s'.regs 187 = source.val := by
  classical
  let H : SimpleGraph (Fin n) := (gm06PuncturedGraphData tagged cut).vertexGraph
  let mask : Fin n → ℕ := fun v => if H.Reachable source v then 1 else 0
  obtain ⟨s₁, t₁, he₁, ht₁, hreach₁, ha₁, hN₁, hcut₁, hsource₁⟩ :=
    gm06PuncturedComponentProg_exec ends active he28 ha28 tagged cut source
      hw hn hsquare hm hbits ha hb hN hcut hsource
  let s₂ := s₁.setReg 40 n
  have he₂ : Exec w (.assign 40 (.reg 100)) s₁ s₂ 2 := .assign (eval_reg hN₁ hn)
  have hm₂ (v : Fin n) : mask v ≤ 2 := by dsimp [mask]; split <;> omega
  have hR (v : Fin n) : mask v = 1 ↔ v ∈ reachSet H source := by
    rw [GraphMinor.Compute.mem_reachSet]
    by_cases h : H.Reachable source v <;> simp [mask, h]
  have hlabels : s₂.arrs 33 = List.ofFn mask := by
    change s₁.arrs 33 = List.ofFn mask
    rw [hreach₁]
    dsimp only [gm06VertexReachData, gm06PuncturedGraphData, mask, H]
    congr 1
    funext v
    split_ifs with hv
    · exact (if_pos hv).symm
    · exact (if_neg hv).symm
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hcount₃⟩ := gm02CountIntersectionProg_exec Q
    (reachSet H source) mask 1 hm₂ hR guarded 33 s₂ hw hn
    (by simp [s₂]) (by simpa only [s₂, State.setReg_arrs] using (ha₁ guarded hp28).trans hQ)
    hlabels (by omega)
  refine ⟨s₃, t₁ + (2 + t₃), .seq he₁ (.seq he₂ he₃), by omega, hcount₃,
    (hk₃.2 33 (by simp)).trans hreach₁, ?_, ?_, ?_, ?_⟩
  · intro a ha'
    exact (hk₃.2 a (by simp)).trans (ha₁ a ha')
  · exact (hk₃.1 100 (by decide)).trans hN₁
  · exact (hk₃.1 135 (by decide)).trans hcut₁
  · exact (hk₃.1 187 (by decide)).trans hsource₁

end GraphMinor.Compute
