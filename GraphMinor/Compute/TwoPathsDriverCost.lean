module

public import Mathlib.Tactic.Linarith
public import GraphMinor.Compute.TwoPathsDriverSolve

/-!
# The driver of Algorithm 5.1: the counts of time and space

The driver of Algorithm 5.1 is proved correct by induction on the instances of a run
(`TwoPathsDriver.lean`). For each instance it proves a bound on the time spent on it and its
subinstances, and it needs a bound on the heap that the frames of its subinstances may fill. This
file defines the two bounds and proves the arithmetic that the induction needs.

Fix the number `N` of vertices, a word size, the constant `c` of the completion and extraction
steps, and a budget `E` of edges: every instance of the run has at most `E` edges. Write
`W = N + E + 1`. An instance has a vertex set `S` and a cycle `T`, with the two counts
`Φ = 2|S| - |T| - 3` and `Ψ = |S| - |T|`, and its array of adjacency entries has at most
`2E + N f` entries, where `f` is the length of the list of new edges of the split that made it.

* A frame has at most `drvFrame + N f` entries (`drvFrame = 112 + 8N + 2E + 100 c W`), and the
  heap the instance needs is `drvNeed = (Φ + 1) drvFrame + N (f + 3Φ + 2Ψ)`: its frame, and what
  its subinstances need, which have a smaller `Φ` (`need_split`).
* The time of the instance and its subinstances is at most
  `drvTime = K (2Φ + 1) + B Ψ + 48 N f`, plus `c N W` when the answer is `True`
  (`time_split`, `time_leaf`). Here `K = 13000 + 4000 W + 5000 c W` pays for the rounds of one
  split and `B = 600 N + 2 c W` pays for the new path `a m b` of a split: the completion step and
  the extraction step cost `c |P'| W` each, and the new edges cost `O(N)` each in the frames and
  the copies.

Since `Φ ≤ 2N` and `Ψ ≤ N`, the time is `O((c + 1) N W)`, which is `O(N (N + M))` when
`E = O(N + M)`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- The fixed part of the length of a frame. -/
def drvFrame (N E c : ℕ) : ℕ := 112 + 8 * N + 2 * E + 100 * (c * (N + E + 1))

/-- The heap that an instance with counts `Φ`, `Ψ` and `f` needs. -/
def drvNeed (N E c Φ Ψ f : ℕ) : ℕ := (Φ + 1) * drvFrame N E c + N * (f + 3 * Φ + 2 * Ψ)

/-- The cost of the rounds of one split. -/
def drvK (N E c : ℕ) : ℕ := 13000 + 4000 * (N + E + 1) + 5000 * (c * (N + E + 1))

/-- The cost of one vertex of a new path. -/
def drvB (N E c : ℕ) : ℕ := 600 * N + 2 * (c * (N + E + 1))

/-- The time of an instance with counts `Φ`, `Ψ` and `f`, without the answer `True`. -/
def drvTime (N E c Φ Ψ f : ℕ) : ℕ := drvK N E c * (2 * Φ + 1) + drvB N E c * Ψ + 48 * (N * f)

/-- **The heap of a split.** The frame and what a subinstance needs fit in what the instance
needs. -/
theorem need_split {N E c Φ Ψ f Φ' Ψ' m F fr : ℕ} (hΦ : Φ' + 1 ≤ Φ) (hΨ : Ψ' + m ≤ Ψ)
    (hF : F ≤ 2 * m + 3) (hfr : fr ≤ drvFrame N E c + N * f) :
    fr + drvNeed N E c Φ' Ψ' F ≤ drvNeed N E c Φ Ψ f := by
  unfold drvNeed
  have h1 : (Φ' + 1) * drvFrame N E c + drvFrame N E c ≤ (Φ + 1) * drvFrame N E c := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have h2 : N * (F + 3 * Φ' + 2 * Ψ') + N * f ≤ N * (f + 3 * Φ + 2 * Ψ) := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- The heap an instance needs holds its frame. -/
theorem frame_le_need (N E c Φ Ψ f : ℕ) :
    drvFrame N E c + N * f ≤ drvNeed N E c Φ Ψ f := by
  unfold drvNeed
  have h1 : drvFrame N E c ≤ (Φ + 1) * drvFrame N E c := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : N * f ≤ N * (f + 3 * Φ + 2 * Ψ) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The time of an instance that answers at once.** -/
theorem time_leaf {N E c M Φ Ψ f : ℕ} (hM : M ≤ E) :
    6 + leafCost N (2 * M) ≤ drvTime N E c Φ Ψ f := by
  unfold drvTime drvK leafCost
  have h1 : 13000 + 4000 * (N + E + 1) + 5000 * (c * (N + E + 1)) ≤
      (13000 + 4000 * (N + E + 1) + 5000 * (c * (N + E + 1))) * (2 * Φ + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The time of a split.** The three rounds of a split (the solve round, the return round of
side `1` and the return round of side `2`) and the times of the two subinstances fit in the time
of the instance. -/
theorem time_split {N E c M Φ Ψ f Φ₁ Φ₂ Ψ₁ Ψ₂ m F p enc : ℕ} (hM : M ≤ E) (hp : p ≤ m + 2)
    (hF : F ≤ 2 * m + 3) (henc : enc ≤ 109 + 8 * N + 2 * E + N * f + 100 * (c * (N + E + 1)))
    (hΦ : Φ₁ + Φ₂ + 1 = Φ) (hΨ : Ψ₁ + Ψ₂ + m = Ψ) :
    18 + (leafCost N (2 * M) + c * p * (N + M + 1) + 16 * enc + 90 * (N * F)) +
        (2200 + 250 * N + 80 * (2 * M) + 16 * enc + 90 * (N * F)) +
        (2200 + 150 * N + 16 * enc + c * p * (N + M + 1)) +
        drvTime N E c Φ₁ Ψ₁ F + drvTime N E c Φ₂ Ψ₂ F ≤ drvTime N E c Φ Ψ f := by
  have hcp : c * p * (N + M + 1) ≤ c * (m + 2) * (N + E + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) (by omega)
  have hNF : N * F ≤ N * (2 * m + 3) := Nat.mul_le_mul_left _ hF
  subst hΦ hΨ
  unfold drvTime drvK drvB leafCost
  have hNE : N ≤ N + E + 1 := by omega
  have hc : c * N ≤ c * (N + E + 1) := Nat.mul_le_mul_left _ hNE
  nlinarith [hcp, hNF, hc, henc]

/-- **The time of the first instance.** With `Φ ≤ 2N`, `Ψ ≤ N` and `f ≤ 8`, the time is
`O((c + 1) N W)`. -/
theorem drvTime_le {N E c Φ Ψ f : ℕ} (hΦ : Φ ≤ 2 * N) (hΨ : Ψ ≤ N) (hf : f ≤ 8) :
    drvTime N E c Φ Ψ f ≤ (70000 + 21000 * c) * ((N + 1) * (N + E + 1)) := by
  unfold drvTime drvK drvB
  set W := N + E + 1 with hWdef
  have hW : 1 ≤ W := by omega
  have hNW : N ≤ W := by omega
  have h0 : 13000 + 4000 * W + 5000 * (c * W) ≤ (17000 + 5000 * c) * W := by nlinarith
  have h1 : (13000 + 4000 * W + 5000 * (c * W)) * (2 * Φ + 1) ≤
      (17000 + 5000 * c) * W * (4 * (N + 1)) := Nat.mul_le_mul h0 (by omega)
  have h2 : (600 * N + 2 * (c * W)) * Ψ ≤ (600 * N + 2 * (c * W)) * N :=
    Nat.mul_le_mul_left _ hΨ
  have h3 : N * f ≤ N * 8 := Nat.mul_le_mul_left _ hf
  have h4 : N * N ≤ (N + 1) * W := Nat.mul_le_mul (by omega) hNW
  have h5 : c * W * N ≤ c * ((N + 1) * W) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by nlinarith)
  have h6 : N ≤ (N + 1) * W := by nlinarith
  nlinarith

end GraphMinor.Compute.TwoPaths
