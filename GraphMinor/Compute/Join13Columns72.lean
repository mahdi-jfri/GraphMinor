module

public import GraphMinor.Compute.Join13Graph72
public import GraphMinor.Compute.Join13Project72

/-!
# Preparing the graph columns for the (7.2) core call

The caller's graph is expanded once. Two gathers then produce its head and tail
columns, while retaining the endpoint stream for converting the output models.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Prepare the endpoint stream and both columns at fixed internal addresses. -/
def prepareColumns72Prog : Cmd :=
  .seq (expandGraph72Prog 12 40 70)
    (.seq (projectEndpoint72Prog 1 40 66 28 90)
      (projectEndpoint72Prog 0 40 65 28 90))

/-- Graph-column preparation uses linear time and preserves the registers
holding the graph and tree sizes. -/
theorem prepareColumns72Prog_exec {w n : ℕ} (G : MultiDigraph n) (s : State)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * G.numEdges < 2 ^ w)
    (henc : G.enc.length < 2 ^ w) (hsrc : s.arrs 12 = G.enc)
    (hrm : s.regs 28 = G.numEdges) :
    ∃ s' t, Exec w prepareColumns72Prog s s' t ∧
      t ≤ 440 * (n + G.numEdges + 1) ∧
      s'.arrs 40 = endpointWords72 G.toMultiComputeDigraph ∧
      s'.arrs 66 = List.ofFn (fun e => (G.toMultiComputeDigraph.head e).1) ∧
      s'.arrs 65 = List.ofFn (fun e => (G.toMultiComputeDigraph.tail e).1) ∧
      Keeps [70, 71, 72, 73, 74, 75, 90] [40, 66, 65] s s' := by
  obtain ⟨s₁, t₁, he₁, ht₁, ho₁, hk₁⟩ :=
    expandGraph72Prog_exec G 12 40 70 (by decide) s hw hn hm henc hsrc hrm
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, ho₂⟩ :=
    projectEndpoint72Prog_exec G.toMultiComputeDigraph 1 40 66 28 90
      (by decide) (by decide) s₁ (by omega) hn hm ho₁
      ((hk₁.1 28 (by decide)).trans hrm)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, ho₃⟩ :=
    projectEndpoint72Prog_exec G.toMultiComputeDigraph 0 40 65 28 90
      (by decide) (by decide) s₂ (by omega) hn hm
      ((hk₂.2 40 (by decide)).trans ho₁)
      ((hk₂.1 28 (by decide)).trans ((hk₁.1 28 (by decide)).trans hrm))
  change t₂ ≤ 20 * (G.numEdges + 1) at ht₂
  change t₃ ≤ 20 * (G.numEdges + 1) at ht₃
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega, ?_, ?_, ?_, ?_⟩
  · exact (hk₃.2 40 (by decide)).trans ((hk₂.2 40 (by decide)).trans ho₁)
  · rw [hk₃.2 66 (by decide), ho₂]
    rfl
  · simpa using ho₃
  · constructor
    · intro j hj
      simp only [List.mem_cons, not_or] at hj
      rw [hk₃.1 j (by simpa using hj.2.2.2.2.2.2),
        hk₂.1 j (by simpa using hj.2.2.2.2.2.2)]
      exact hk₁.1 j (by simp_all)
    · intro a ha
      simp only [List.mem_cons, not_or] at ha
      rw [hk₃.2 a (by simpa using ha.2.2), hk₂.2 a (by simpa using ha.2.1)]
      exact hk₁.2 a (by simpa using ha.1)

end GraphMinor.Compute
