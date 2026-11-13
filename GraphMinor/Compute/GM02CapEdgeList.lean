module

public import GraphMinor.Compute.GM02MultiEdgeList
public import GraphMinor.Compute.Algorithm44
import GraphMinor.Compute.Specs4

/-!
# Running an edge-list program on the multigraph encoding

The recognition theorems of Graph Minors II read the multigraph encoding
`x.G.enc`, in which a multiplicity may be far larger than the input size. The
programs of II read an edge list instead. To run them, first cap every
multiplicity at a fixed bound `δ` (`capMultiDigraphProg`), then write out the
edges of the capped graph one by one (`multiEdgeListProg`). The capped graph has
at most `(δ + 1) n²` edges, so a polynomial edge-list program stays polynomial
in `(n + 1)²` (`ComputesRelInTime.capEdgeList`).
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set

/-- Cap the multiplicities of the graph in `inArr` at `δ` and replace the input
by the edge list of the capped graph. Array `501` and registers from `500` on
are scratch. -/
def capEdgeListProg (δ : ℕ) : Cmd :=
  .seq (capMultiDigraphProg δ inArr 500 501 500) (multiEdgeListProg 501 inArr 502 510)

private theorem wordSize_mul_cap (c : ℕ) {K M m : ℕ} (hK : 2 ≤ K) (hM : M ≤ K * m) :
    wordSize c M ≤ wordSize (c * K) m := by
  unfold wordSize
  have h1 : M + 2 ≤ K * (m + 1) := by nlinarith
  have h2 : M + 2 ≤ (m + 2) ^ K := le_trans h1 (mul_succ_le_pow_add_two K m)
  have h3 : (m + 2) ^ K < (2 ^ (Nat.log 2 (m + 2) + 1)) ^ K :=
    Nat.pow_lt_pow_left (lt_two_pow_log_succ m) (by omega)
  rw [← Nat.pow_mul, Nat.mul_comm _ K] at h3
  have hlog : Nat.log 2 (M + 2) < K * (Nat.log 2 (m + 2) + 1) :=
    Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt h2 h3)
  have hlog1 : Nat.log 2 (M + 2) + 1 ≤ K * (Nat.log 2 (m + 2) + 1) := by omega
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left c hlog1

/-- The capped graph has at most `(δ + 1) n²` edges. -/
theorem numEdges_cap_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) :
    (G.cap δ).numEdges ≤ (δ + 1) * (n + 1) ^ 2 := by
  have h := lemma_4_4_cap_numEdges_le δ G
  have hsq : n * n ≤ (n + 1) ^ 2 := by nlinarith
  exact h.trans (Nat.mul_le_mul_left _ hsq)

/-- The edge list of the capped graph has size at most `(δ + 2)(n + 1)²`. -/
theorem capEdgeList_size_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) :
    (G.cap δ).toEdgeListInput.size ≤ (δ + 2) * (n + 1) ^ 2 := by
  rw [MultiDigraph.toEdgeListInput_size]
  have h := numEdges_cap_le δ G
  have hn : n ≤ (n + 1) ^ 2 := by nlinarith
  nlinarith

/-- `capEdgeListProg δ` turns `G.enc` in `inArr` into the edge list of `G.cap δ`. -/
theorem capEdgeListProg_exec {w n : ℕ} (δ : ℕ) (G : MultiDigraph n)
    (hw : (4 * δ + 12) * (n + 1) ^ 2 < 2 ^ w) {s : State} (hs : s.arrs inArr = G.enc) :
    ∃ s' t, Exec w (capEdgeListProg δ) s s' t ∧
      t ≤ (300 + 50 * δ) * (n + 1) ^ 2 + 200 ∧
      s'.arrs inArr = (G.cap δ).toEdgeListInput.enc := by
  have hsq : n * n ≤ (n + 1) ^ 2 := by nlinarith
  have hn : n < (n + 1) ^ 2 := by nlinarith
  have hact := G.numActivePairs_le_sq
  have hact' := (G.cap δ).numActivePairs_le_sq
  have hE := numEdges_cap_le δ G
  generalize (n + 1) ^ 2 = S at hw hsq hn hE ⊢
  have hS : 1 ≤ S := by omega
  have e1 : (4 * δ + 12) * S = 4 * (δ * S) + 12 * S := by ring
  have e2 : (δ + 1) * S = δ * S + S := by ring
  have e3 : (300 + 50 * δ) * S = 300 * S + 50 * (δ * S) := by ring
  have hδS : δ ≤ δ * S := Nat.le_mul_of_pos_right _ hS
  rw [e1] at hw
  rw [e2] at hE
  rw [e3]
  generalize hAdef : δ * S = A at hw hE hδS ⊢
  have hw3 : 3 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hδ_w : δ + 1 < 2 ^ w := by omega
  have hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w := by omega
  have hm3_w' : 2 + 3 * (G.cap δ).numActivePairs < 2 ^ w := by omega
  have hE_w : (G.cap δ).numEdges < 2 ^ w := by omega
  have hE2_w : 2 + 2 * (G.cap δ).numEdges < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hdst₁, -, -, hreg₁, harr₁, -⟩ :=
    capMultiDigraphProg_exec G δ [] inArr 500 501 500 (by decide) (by decide)
      hw3 hn_w hδ_w hm3_w hE_w (by simpa using hs)
  obtain ⟨s₂, t₂, he₂, ht₂, hdst₂, -, -⟩ :=
    multiEdgeListProg_exec (M := δ + 1) (G.cap δ) [] 501 inArr 502 510 (by decide) (by decide)
      hw3 hn_w hm3_w' hE2_w (fun u v => (G.cap_edgeMult_le_succ δ u v)) hδ_w
      (by simpa using hdst₁) hreg₁
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hdst₂⟩
  have hmul : ((G.cap δ).numActivePairs + 1) * (40 + 21 * (δ + 1)) ≤ (S + 1) * (61 + 21 * δ) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e4 : (S + 1) * (61 + 21 * δ) = 61 * S + 21 * (δ * S) + 61 + 21 * δ := by ring
  rw [e4, hAdef] at hmul
  omega

/-- Run an edge-list program after `capEdgeListProg δ`. A program that is
polynomial in the edge-list size becomes polynomial in `(n + 1)²`; the exponent
grows by one. -/
theorem ComputesRelInTime.capEdgeList (δ : ℕ) {Q : GM02EdgeListInput → State → Prop}
    {P : Cmd} {c : ℕ}
    (h : ComputesRelInTime GM02EdgeListInput.size (fun y s => s.arrs inArr = y.enc) Q P
      (fun n => (n + 1) ^ c)) :
    ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
      (fun x s => Q (x.G.cap δ).toEdgeListInput s) (.seq (capEdgeListProg δ) P)
      (fun n => (n + 1) ^ (c + 1)) := by
  obtain ⟨C, cw, hC, hcw, run⟩ := h
  let K := δ + 2
  have hK : 2 ≤ K := by omega
  refine ⟨(500 + 50 * δ) + C * K ^ c, cw * K + 4 * δ + 12, by omega, by omega, ?_⟩
  intro x s hs
  obtain ⟨n, G⟩ := x
  have hsize : alg44Size ⟨n, G⟩ = (n + 1) ^ 2 := rfl
  let W := wordSize (cw * K + 4 * δ + 12) (alg44Size ⟨n, G⟩)
  have hW : (4 * δ + 12) * (n + 1) ^ 2 < 2 ^ W := by
    have h := mul_lt_two_pow_of_wordSize_le (c := cw * K + 4 * δ + 12) (m := (n + 1) ^ 2)
      (by omega) (by rw [← hsize])
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) h
  obtain ⟨s₁, t₁, he₁, ht₁, hdst₁⟩ := capEdgeListProg_exec δ G hW hs
  let y := (G.cap δ).toEdgeListInput
  have hy : y.size ≤ K * (n + 1) ^ 2 := capEdgeList_size_le δ G
  obtain ⟨s₂, t₂, he₂, ht₂, hQ⟩ := run y s₁ hdst₁
  have hword : wordSize cw y.size ≤ W := by
    calc wordSize cw y.size ≤ wordSize cw (K * (n + 1) ^ 2) := wordSize_mono_right cw hy
      _ ≤ wordSize (cw * K) ((n + 1) ^ 2) := wordSize_mul_cap cw hK le_rfl
      _ ≤ W := by
        rw [← hsize]
        exact wordSize_mono_left (by omega) _
  refine ⟨s₂, t₁ + t₂, .seq he₁ (Exec.mono_wordSize hword he₂), ?_, hQ⟩
  show t₁ + t₂ ≤ ((500 + 50 * δ) + C * K ^ c) * (alg44Size ⟨n, G⟩ + 1) ^ (c + 1)
  rw [hsize]
  generalize hS : (n + 1) ^ 2 = S at hy ht₁ ⊢
  have hS1 : 1 ≤ S := by rw [← hS]; exact Nat.one_le_pow _ _ (by omega)
  have hpow : (y.size + 1) ^ c ≤ K ^ c * (S + 1) ^ c := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) c
  have hc1 : (S + 1) ^ c ≤ (S + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hSc : S + 1 ≤ (S + 1) ^ (c + 1) := by
    calc S + 1 = (S + 1) ^ 1 := (pow_one _).symm
      _ ≤ (S + 1) ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have ht₂' : t₂ ≤ C * K ^ c * (S + 1) ^ (c + 1) := by
    calc t₂ ≤ C * (y.size + 1) ^ c := ht₂
      _ ≤ C * (K ^ c * (S + 1) ^ c) := Nat.mul_le_mul_left _ hpow
      _ = C * K ^ c * (S + 1) ^ c := by ring
      _ ≤ C * K ^ c * (S + 1) ^ (c + 1) := Nat.mul_le_mul_left _ hc1
  have ht₁' : t₁ ≤ (500 + 50 * δ) * (S + 1) := by nlinarith
  have ht₁'' : t₁ ≤ (500 + 50 * δ) * (S + 1) ^ (c + 1) :=
    ht₁'.trans (Nat.mul_le_mul_left _ hSc)
  calc t₁ + t₂ ≤ (500 + 50 * δ) * (S + 1) ^ (c + 1) + C * K ^ c * (S + 1) ^ (c + 1) :=
        Nat.add_le_add ht₁'' ht₂'
    _ = ((500 + 50 * δ) + C * K ^ c) * (S + 1) ^ (c + 1) := by ring

end GraphMinor.Compute
