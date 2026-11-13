module

public import GraphMinor.Compute.GM02SavedFrameWords
public import GraphMinor.Compute.GM02TerminatedEncoding
public import GraphMinor.Compute.BitSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial space for saved recursive frames

A parent input and its two side arrays have quadratic total length in
the root vertex count. The alternating call measure bounds stack depth
by twice that count plus one. Reserve one further frame of space. The
resulting cubic capacity is bounded by a fixed fifth power and fits the
same logarithmic-word RAM model as the recursive programs.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A uniform bound for one saved parent frame under root size `n`. -/
def gm02SavedFrameSizeBound (n : ℕ) : ℕ := 12 + 2 * n * n + 3 * n

/-- Room for the alternating recursion depth and one additional frame. -/
def gm02SavedFrameCapacity (n : ℕ) : ℕ := (2 * n + 2) * gm02SavedFrameSizeBound n

/-- Every parent frame under a root vertex bound fits its uniform frame bound. -/
theorem gm02SavedFrameWords_length_le (x : GM02SimpleTerminatedInput) {n : ℕ} (hx : x.n ≤ n)
    (L R : Finset (Fin x.n)) (mode code aggregate leftAnswer catalogue start : ℕ) :
    (gm02SavedFrameWords x.enc (bitSetList L) (bitSetList R)
      mode code aggregate leftAnswer catalogue start).length ≤ gm02SavedFrameSizeBound n := by
  have he := x.enc_length_le hx
  rw [gm02SavedFrameWords_length, length_bitSetList, length_bitSetList]
  unfold gm02SavedFrameSizeBound
  have heq : 2 * n * n = 2 * (n * n) := by ring
  rw [heq]
  omega

private theorem flatten_length_le (frames : List (List ℕ)) (bound : ℕ)
    (h : ∀ f ∈ frames, f.length ≤ bound) : frames.flatten.length ≤ frames.length * bound := by
  induction frames with
  | nil => simp
  | cons f fs ih =>
    have hf := h f (List.mem_cons_self ..)
    have ht := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A bounded stack and one pending parent frame fit the reserved capacity. -/
theorem gm02SavedFrameCapacity_suffices (n : ℕ) (frames : List (List ℕ)) (next : List ℕ)
    (hdepth : frames.length ≤ 2 * n + 1)
    (hframes : ∀ f ∈ frames, f.length ≤ gm02SavedFrameSizeBound n)
    (hnext : next.length ≤ gm02SavedFrameSizeBound n) :
    frames.flatten.length + next.length ≤ gm02SavedFrameCapacity n := by
  have hflat := flatten_length_le frames (gm02SavedFrameSizeBound n) hframes
  have hd := Nat.mul_le_mul_right (gm02SavedFrameSizeBound n) hdepth
  calc
    frames.flatten.length + next.length ≤
        (2 * n + 1) * gm02SavedFrameSizeBound n + gm02SavedFrameSizeBound n :=
      Nat.add_le_add (hflat.trans hd) hnext
    _ = gm02SavedFrameCapacity n := by unfold gm02SavedFrameCapacity; ring

/-- The cubic capacity is bounded by a fixed fifth power of root size plus two. -/
theorem gm02SavedFrameCapacity_le_pow (n : ℕ) :
    gm02SavedFrameCapacity n ≤ (n + 2) ^ 5 := by
  have hcap : gm02SavedFrameCapacity n ≤ 4 * (n + 2) ^ 3 := by
    unfold gm02SavedFrameCapacity gm02SavedFrameSizeBound
    nlinarith
  have hsq : 4 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left (by omega : 2 ≤ n + 2) 2
  calc
    gm02SavedFrameCapacity n ≤ 4 * (n + 2) ^ 3 := hcap
    _ ≤ (n + 2) ^ 2 * (n + 2) ^ 3 := Nat.mul_le_mul_right _ hsq
    _ = (n + 2) ^ 5 := by rw [← pow_add]

/-- A fixed exponent at least five provides enough word range for every stack cursor. -/
theorem gm02SavedFrameCapacity_lt_wordSize {c : ℕ} (hc : 5 ≤ c) (n : ℕ) :
    gm02SavedFrameCapacity n < 2 ^ wordSize c n := by
  apply (gm02SavedFrameCapacity_le_pow n).trans_lt
  exact (Nat.pow_le_pow_right (by omega : 1 ≤ n + 2) hc).trans_lt
    (pow_lt_two_pow_wordSize (by omega : 1 ≤ c) n)

/-- A decreasing call measure leaves enough stack capacity after saving one bounded frame. -/
theorem gm02SavedFrame_remaining_capacity {measure next frame cap bound : ℕ}
    (hnext : next < measure) (hframe : frame ≤ bound)
    (hcap : (measure + 1) * bound ≤ cap) :
    frame ≤ cap ∧ (next + 1) * bound ≤ cap - frame := by
  have hbudget : (next + 1) * bound + frame ≤ cap := by
    calc
      (next + 1) * bound + frame ≤ (next + 1) * bound + bound := Nat.add_le_add_left hframe _
      _ = (next + 2) * bound := by ring
      _ ≤ (measure + 1) * bound := Nat.mul_le_mul_right _ (by omega)
      _ ≤ cap := hcap
  omega

end GraphMinor.Compute
