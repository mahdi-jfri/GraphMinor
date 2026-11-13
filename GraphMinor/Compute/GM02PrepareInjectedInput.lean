module

public import GraphMinor.Compute.GM02BuildInjectedVertices
public import GraphMinor.Compute.GM02BuildInjectedEdges
public import GraphMinor.Compute.GM02JoinInjectedInput
import GraphMinor.Compute.GM02TopologicalEncodingWords

/-!
# Constructing one complete labelled input from plain host data

Build the canonical injected vertex suffix, build the actual injected
edge suffix, and join both to the original host encoding. Every step
preserves the host input and outer candidate counter. Thus the input
for (4.6) is computed by the RAM, rather than supplied as a certificate.
-/

public section
namespace GraphMinor.Compute

/-- Construct the ordinary labelled graph-pair input in array 33. -/
@[expose] def gm02PrepareInjectedInputProg (H : GM02EdgeListInput) : Cmd :=
  .seq (gm02BuildInjectedVerticesProg H.n)
    (.seq (gm02BuildInjectedEdgesProg H) gm02JoinInjectedInputProg)

/-- Exact construction of a labelled test input from host words and decoded vertex choices. -/
theorem gm02PrepareInjectedInputProg_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hw : 1 < 2 ^ W) (hn : G.n + 1 < 2 ^ W)
    (hmG : G.edges.length < 2 ^ W) (hcap : 1 + 2 * H.edges.length < 2 ^ W)
    (hlen : (gm02InjectedPattern G H f).enc.length < 2 ^ W)
    (hG : s.arrs inArr = G.enc) (hrn : s.regs 40 = G.n)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val) :
    ∃ s' t, Exec W (gm02PrepareInjectedInputProg H) s s' t ∧
      t ≤ 85 + 16 * H.n + 8 * H.edges.length +
        G.n * ((gm02InjectionMembershipExpr H.n).cost + 15) +
        32 * (gm02InjectedPattern G H f).enc.length ∧
      s'.arrs 33 = (gm02InjectedPattern G H f).enc ∧
      (∀ a, a ≠ 29 → a ≠ 30 → a ≠ 31 → a ≠ 32 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r < 194, s'.regs r = s.regs r) := by
  obtain ⟨s₀, t₀, he₀, ht₀, hv₀, ha₀, hr₀⟩ :=
    gm02BuildInjectedVerticesProg_exec G H f s hw hn hrn hslots
  have hslots₀ (i : Fin H.n) : s₀.regs (200 + i.val) = (f i).val := by
    have hgt : 198 < 200 + i.val := (by decide : 198 < 200).trans_le (Nat.le_add_right 200 i.val)
    exact (hr₀ _ (Or.inr hgt)).trans (hslots i)
  obtain ⟨s₁, he₁, heWords₁, hr₁, ha₁⟩ :=
    gm02BuildInjectedEdgesProg_exec G H f s₀ (by omega) hcap hslots₀
  have hall : ∀ a ∈ (gm02InjectedPattern G H f).enc, a < 2 ^ W :=
    (gm02InjectedPattern G H f).enc_all_lt (by exact Nat.lt_of_succ_lt hn) hmG
      (by simpa only [gm02InjectedPattern_edges_length] using (by omega : H.edges.length < 2 ^ W))
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂, hr₂⟩ := gm02JoinInjectedInputProg_exec G H f s₁
    ((ha₁ inArr (by decide)).trans ((ha₀ inArr (by decide) (by decide)).trans hG))
    ((ha₁ 30 (by decide)).trans hv₀) heWords₁ hw hlen hall
  refine ⟨s₂, t₀ + ((6 + 8 * H.edges.length) + t₂), .seq he₀ (.seq he₁ he₂),
    by omega, hout, ?_, ?_⟩
  · intro a h29 h30 h31 h32 h33
    exact (ha₂ a h32 h33).trans ((ha₁ a h31).trans (ha₀ a h29 h30))
  · intro r hr
    have hr290 : r < 290 := hr.trans_le (by decide)
    exact (hr₂ r hr290).trans ((congrFun hr₁ r).trans (hr₀ r (Or.inl hr)))

end GraphMinor.Compute
