module

public import GraphMinor.Compute.GM02BuildBalancedOutput
public import GraphMinor.Compute.GM02CodeSearchLoop
public import GraphMinor.Compute.GM02ParseBalancedInput
import GraphMinor.Compute.GM02CodeTestCorrectness

/-!
# The complete balanced-separation program

Parse the plain input, scan all separator codes, and either reject or
construct the balanced side arrays from the successful code. Correctness
combines the exhaustive component test with the explicit grouping and
edge-partition construction. This is the full program for II (3.1),
page 316, before replacing its detailed cost by a polynomial bound.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Detailed cost of parsing the graph and supplied subset. -/
def gm02BalancedParseTime (n m : ℕ) : ℕ := 43 * n + 88 * m + 33

/-- Detailed cost of the exhaustive separator-code scan. -/
def gm02BalancedSearchTime (k n m : ℕ) : ℕ := 7 + 4 * k + (n + 1) ^ k *
  (35 + 4 * k + k * (8 + 4 * k) + n * (k * 6 + 36) +
    n * (91 + k * 6 + n * (k * 6 + 57) + 58 * m))

/-- Detailed cost of constructing both side arrays after success. -/
def gm02BalancedOutputTime (k n m : ℕ) : ℕ := 44 + k * (8 + 4 * k) +
  n * (185 + 18 * k + n * (k * 6 + 94) + 58 * m)

/-- A uniform bound for both branches of the complete separator program. -/
def gm02BalancedTime (k n m : ℕ) : ℕ := gm02BalancedParseTime n m +
  gm02BalancedSearchTime k n m + 1 + gm02BalancedOutputTime k n m

/-- The complete graph-and-subset program of Graph Minors II (3.1). -/
def gm02BalancedSeparationProg (k : ℕ) : Cmd :=
  .seq gm02ParseBalancedInputProg (.seq (gm02CodeSearchLoop k)
    (.ite (.reg 186) (gm02BuildBalancedOutputProg k) (.assign outReg (.const 0))))

private theorem no_validSides_of_failed_codes (x : GM02Alg31Input) (k : ℕ)
    (hfail : ∀ code < (x.n + 1) ^ k, ¬∀ a : Fin x.n,
      a ∉ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit x.n code i.val) →
      3 * (GM02.deletedComponent (Graph.ofSimpleGraph x.G)
        (gm02SlotVertices (n := x.n) (fun i : Fin k => gm02SeparatorDigit x.n code i.val) : Set (Fin x.n)) a ∩
          (x.Q : Set (Fin x.n))).ncard ≤
        2 * (x.Q \ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit x.n code i.val)).card) :
    ¬∃ left right, x.validSides (k : ℤ) left right := by
  intro h
  obtain ⟨H, H', hsep, hsize, hL, hR⟩ := (x.exists_validSides_iff (k : ℤ)).1 h
  have hsizeNat : (V(H) ∩ V(H')).ncard ≤ k := by exact_mod_cast hsize
  obtain ⟨code, hc, hgood⟩ := (gm02BalancedSeparation_iff_code x.G x.Q k).1
    ⟨H, H', hsep, hsizeNat, hL, hR⟩
  exact hfail code hc hgood

/-- The full program reads the plain input and produces either the actual
balanced separation arrays or a valid rejection. All word bounds are on
input sizes and the fixed enumeration length. -/
theorem gm02BalancedSeparationProg_exec_bits {k w : ℕ} (x : GM02Alg31Input) (s : State)
    (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w) (hn : 3 * x.n < 2 ^ w)
    (hb : x.n + 1 < 2 ^ w) (hp : (x.n + 1) ^ k < 2 ^ w) (hin : s.arrs inArr = x.enc) :
    ∃ s' t, Exec w (gm02BalancedSeparationProg k) s s' t ∧
      t ≤ gm02BalancedTime k x.n (edgeListOf x.G).length ∧ x.correct (k : ℤ) s' ∧
      (s'.regs outReg = 1 → ∃ L R : Finset (Fin x.n),
        s'.arrs outArr = gm02VertexBits L ∧ s'.arrs 2 = gm02VertexBits R) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hrn₁, _, hadj₁, hent₁, hq₁, _⟩ :=
    gm02ParseBalancedInputProg_exec x s hw hlen hin
  have htot : totalAdjEntries (edgeNeighbors (edgeListOf x.G)) = 2 * (edgeListOf x.G).length :=
    totalAdjEntries_edgeNeighbors _ (isSimpleEdgeList_edgeListOf x.G).1
  have hentw : (s₁.arrs 12).length < 2 ^ w := by
    rw [hent₁]
    have hl := x.enc_length
    omega
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hresult⟩ := gm02CodeSearchLoop_exec x.G
    (edgeNeighbors (edgeListOf x.G)) x.Q s₁ hw hn hb hp hadj₁ hentw hrn₁ hq₁
  have h40 : 40 ∉ 190 :: gm02CodeSearchRegs k := by
    simp only [gm02CodeSearchRegs, List.mem_cons, List.mem_append, not_or]
    exact ⟨by decide, by decide, by decide, not_mem_gm02SlotRegs (by decide), by decide⟩
  have hadj₂ := hadj₁.of_arrs_eq (hk₂.2 _ (by decide))
    (hk₂.2 _ (by decide)) (hk₂.2 _ (by decide))
  have hrn₂ := (hk₂.1 _ h40).trans hrn₁
  have hq₂ := (hk₂.2 _ (by decide)).trans hq₁
  have hent₂ : (s₂.arrs 12).length < 2 ^ w := by simpa only [hk₂.2 12 (by decide)] using hentw
  have hsearch : t₂ ≤ gm02BalancedSearchTime k x.n (edgeListOf x.G).length := by
    simpa only [gm02BalancedSearchTime, htot, ← Nat.mul_assoc, Nat.reduceMul] using ht₂
  have hparse : t₁ ≤ gm02BalancedParseTime x.n (edgeListOf x.G).length := ht₁
  rcases hresult with ⟨hzero, hfail⟩ | ⟨hone, hcode, hgood⟩
  · let s₃ := s₂.setReg outReg 0
    have he₃ : Exec w (.assign outReg (.const 0)) s₂ s₃ 2 := .assign (eval_const (Nat.two_pow_pos w))
    refine ⟨s₃, t₁ + (t₂ + (1 + 2)), .seq he₁ (.seq he₂ (.ite_false
      (eval_reg hzero (Nat.two_pow_pos w)) he₃)), ?_, Or.inr ⟨by simp [s₃], ?_⟩, ?_⟩
    · have hbld : 2 ≤ gm02BalancedOutputTime k x.n (edgeListOf x.G).length := by
        unfold gm02BalancedOutputTime
        omega
      unfold gm02BalancedTime
      omega
    · exact no_validSides_of_failed_codes x k hfail
    · intro hbad
      have hz : s₃.regs outReg = 0 := by simp [s₃]
      omega
  · obtain ⟨s₃, t₃, he₃, ht₃, hcorrect, hbits⟩ := gm02BuildBalancedOutputProg_exec_bits x
      (edgeNeighbors (edgeListOf x.G)) s₂ hw hn hb hp hcode hadj₂ hent₂ hrn₂ hq₂ rfl hgood
    refine ⟨s₃, t₁ + (t₂ + (1 + t₃)), .seq he₁ (.seq he₂ (.ite_true
      (eval_reg hone (by omega)) (by decide) he₃)), ?_, hcorrect, fun _ => hbits⟩
    have hbuild : t₃ ≤ gm02BalancedOutputTime k x.n (edgeListOf x.G).length := by
      simpa only [gm02BalancedOutputTime, htot, ← Nat.mul_assoc, Nat.reduceMul] using ht₃
    unfold gm02BalancedTime
    omega

/-- The full separator program returns an actual valid separation or a valid rejection. -/
theorem gm02BalancedSeparationProg_exec {k w : ℕ} (x : GM02Alg31Input) (s : State)
    (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w) (hn : 3 * x.n < 2 ^ w)
    (hb : x.n + 1 < 2 ^ w) (hp : (x.n + 1) ^ k < 2 ^ w) (hin : s.arrs inArr = x.enc) :
    ∃ s' t, Exec w (gm02BalancedSeparationProg k) s s' t ∧
      t ≤ gm02BalancedTime k x.n (edgeListOf x.G).length ∧ x.correct (k : ℤ) s' := by
  obtain ⟨s', t, he, ht, hout, _⟩ := gm02BalancedSeparationProg_exec_bits x s hw hlen hn hb hp hin
  exact ⟨s', t, he, ht, hout⟩

end GraphMinor.Compute
