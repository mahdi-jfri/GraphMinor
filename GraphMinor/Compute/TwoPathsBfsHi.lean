module

public import GraphMinor.Compute.TwoPathsBfs
public import GraphMinor.Compute.TwoPathsRename

/-!
# The search of the extraction, in the scratch space

The extraction program must leave every register below `300` and every array below `300` other
than `aQ`, `aR` unchanged (`CompletionStatement`). The search `bfsProg` (`TwoPathsBfs.lean`) reads
its graph from arrays `40`, `41`, `42` and register `40`, and it writes the registers `60 … 76` and
the arrays `60 … 64`. So the extraction runs a renamed copy, `bfsHiProg`: the involution `swapBfs`
exchanges `40, 41, 42` with `340, 341, 342` and `60 … 76` with `360 … 376`, on registers and arrays
alike. The copy reads the number of vertices from register `340`, the graph from arrays `340`,
`341`, `342`, the ends of the walk from registers `374`, `375` and the labels from array `360`. It
writes only registers `360 … 373`, `376` and arrays `360 … 364`, all at `300` or above.

This is cheaper than saving and restoring the arrays `60 … 64`: their old contents can be of any
length, so copying them has no bound in terms of the instance.

`bfsHiProg_bfsSearch` is `bfsProg_bfsSearch` for the copy, by `exec_renameCmd`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph

/-- The involution that moves the input arrays and the scratch space of `bfsProg` to `300` and
above: `40, 41, 42 ↔ 340, 341, 342` and `60 … 76 ↔ 360 … 376`. -/
def swapBfs (x : ℕ) : ℕ :=
  if 40 ≤ x ∧ x < 43 then x + 300
  else if 340 ≤ x ∧ x < 343 then x - 300
  else if 60 ≤ x ∧ x < 77 then x + 300
  else if 360 ≤ x ∧ x < 377 then x - 300
  else x

theorem swapBfs_involutive : Function.Involutive swapBfs := by
  intro x
  unfold swapBfs
  split_ifs <;> omega

/-- The search `bfsProg`, moved by `swapBfs`. -/
def bfsHiProg : Cmd := renameCmd swapBfs bfsProg

/-- Register holding the number of vertices for `bfsHiProg`. -/
abbrev rHiN : Reg := 340
/-- Register holding the start of the searched walk. -/
abbrev rHiU : Reg := 374
/-- Register holding the end of the searched walk. -/
abbrev rHiV : Reg := 375
/-- Register set to `1` when a walk was found. -/
abbrev rHiFound : Reg := 376
/-- Array of start offsets of the searched graph. -/
abbrev aHiS : Arr := 340
/-- Array of end offsets of the searched graph. -/
abbrev aHiE : Arr := 341
/-- Array of entries of the searched graph. -/
abbrev aHiEnt : Arr := 342
/-- Array of labels. -/
abbrev aHiLab : Arr := 360
/-- Array receiving the walk found, without its last vertex. -/
abbrev aHiWalk : Arr := 364

/-- The registers that `bfsHiProg` may change. -/
def bfsHiRegs : List ℕ := (List.range' 360 14) ++ [376]

/-- The arrays that `bfsHiProg` may change. -/
def bfsHiArrs : List ℕ := List.range' 360 5

variable {N : ℕ}

/-- **`bfsHiProg` computes the instance `bfsSearch lists`** on the graph `G` whose adjacency lists
`lists` are stored in the canonical layout in arrays `340`, `341`, `342`. It changes only the
registers `bfsHiRegs` and the arrays `bfsHiArrs`, all at `300` or above. -/
theorem bfsHiProg_bfsSearch {w : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    {lists : Fin N → List ℕ} (hG : IsAdjListFamily G lists) {allowed : List (Fin N)}
    {u v : Fin N} {s : State} (hN : s.regs rHiN = N) (hu : s.regs rHiU = u.1)
    (hv : s.regs rHiV = v.1) (hgs : s.arrs aHiS = (encodeLists lists).1)
    (hge : s.arrs aHiE = (encodeLists lists).2.1) (hgent : s.arrs aHiEnt = (encodeLists lists).2.2)
    (hlab : s.arrs aHiLab = List.ofFn (bfsLabel allowed u v))
    (hw : N + 4 < 2 ^ w) (hent : (encodeLists lists).2.2.length < 2 ^ w) :
    ∃ s' t, Exec w bfsHiProg s s' t ∧ t ≤ 150 + 50 * N + 29 * totalAdjEntries lists ∧
      (∀ r, r ∉ bfsHiRegs → s'.regs r = s.regs r) ∧
      (∀ a, a ∉ bfsHiArrs → s'.arrs a = s.arrs a) ∧
      ((∃ p, (bfsSearch lists).find G allowed u v = some p ∧ s'.regs rHiFound = 1 ∧
          s'.arrs aHiWalk ++ [v.1] = p.support.map Fin.val) ∨
        ((bfsSearch lists).find G allowed u v = none ∧ s'.regs rHiFound = 0)) := by
  set s₀ := renameState swapBfs s with hs₀
  obtain ⟨s₁, t, hex, ht, hr, ha, hres⟩ := bfsProg_bfsSearch (s := s₀) hG hN hu hv hgs hge hgent
    hlab hw hent
  have hinv : renameState swapBfs s₀ = s := by
    ext x <;> simp [s₀, renameState, swapBfs_involutive x]
  refine ⟨renameState swapBfs s₁, t, ?_, ht, fun r hr' => ?_, fun a ha' => ?_, ?_⟩
  · rw [← hinv]; exact exec_renameCmd swapBfs_involutive hex
  · change s₁.regs (swapBfs r) = s.regs r
    have hnot : swapBfs r ∉ bfsScratchRegs := by
      simp only [bfsHiRegs, List.mem_append, List.mem_range'_1, List.mem_singleton] at hr'
      simp only [bfsScratchRegs, List.mem_append, List.mem_range'_1, List.mem_singleton, rWFound,
        swapBfs]
      split_ifs <;> omega
    rw [hr _ hnot]
    change s.regs (swapBfs (swapBfs r)) = s.regs r
    rw [swapBfs_involutive r]
  · change s₁.arrs (swapBfs a) = s.arrs a
    have key : ∀ x : ℕ, ¬ (360 ≤ x ∧ x < 365) →
        swapBfs x ≠ 61 ∧ swapBfs x ≠ 62 ∧ swapBfs x ≠ 63 ∧ swapBfs x ≠ 64 ∧ swapBfs x ≠ 60 := by
      intro x hx
      unfold swapBfs
      split_ifs <;> omega
    have ha'' : ¬ (360 ≤ (a : ℕ) ∧ (a : ℕ) < 365) := by
      simpa [bfsHiArrs, List.mem_range'_1] using ha'
    obtain ⟨h1, h2, h3, h4, h5⟩ := key a ha''
    have hnot : swapBfs a ∉ bfsScratchArrs := by
      simp only [bfsScratchArrs, List.mem_cons, List.not_mem_nil, aPar, aQue, aSrc, aWalk]
      exact fun h => by rcases h with h | h | h | h | h <;> simp_all
    rw [ha _ hnot h5]
    change s.arrs (swapBfs (swapBfs a)) = s.arrs a
    rw [swapBfs_involutive a]
  · exact hres

end GraphMinor.Compute.TwoPaths
