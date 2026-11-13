module

public import GraphMinor.Compute.GM06Alg34GapUpdatePrepare
import GraphMinor.Compute.BitSet

/-!
# Installing the updated gap incidence list

Build the retained region words in a reserved buffer and copy its live
prefix into the gap input array. This finishes the numeric gap update
needed between complement preparation and base-payload replacement.
The program reads only finite arrays and has a cubic time bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Replace array 47 by the retained and reindexed gap region words. -/
def gm06GapUpdateProg : Cmd :=
  .seq gm06GapUpdatePrepareProg (readSliceProg 48 (.const 0) 47 (.reg 6404) 6500)

/-- The complete gap update installs exactly the finite augmented
payload's gap region list and preserves all base-payload input arrays. -/
theorem gm06GapUpdateProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (g : Fin L.length → Fin x.regions.length)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hK : L.length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hL : s.arrs 2 = L.map Fin.val)
    (hR : s.arrs 47 = List.ofFn (fun j => (g j).val)) (hv : s.arrs 4 = gm06VertexMask vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapUpdateProg s s' t ∧
      t ≤ 17 + L.length * (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 74) ∧
      s'.arrs 47 = (x.gapRegionsAfterDeletion vs L (List.ofFn g)).map Fin.val ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → A ≠ 47 → A ≠ 48 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 6500 → (q < 190 ∨ 197 ≤ q) → q ≠ 187 → q ≠ 6400 → q ≠ 6401 →
        q ≠ 6402 → q ≠ 6403 → q ≠ 6404 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hout, hcount, _, harr₁, hreg₁⟩ :=
    gm06GapUpdatePrepareProg_exec x vs L g hw hN hsquare hK hsize hn hm hL hR hv
      hlists hlen hmask hranks
  let words := gm06GapUpdatedWords x vs L g
  have hwordlen : words.length ≤ L.length := by
    simpa only [words, gm06GapUpdatedWords, List.length_finRange] using
      gm06BoundaryWords_length_le (fun i : Fin L.length => decide (L.get i ∈ vs))
        (fun i => (x.regionAfterDeletion vs (g i)).val) (List.finRange L.length)
  have hfit : ∀ a ∈ words, a < 2 ^ w := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    have hi : (x.regionAfterDeletion vs (g i)).val < (x.regionRoots vs).length := by
      simpa only [x.inducedData_regions_length vs] using (x.regionAfterDeletion vs (g i)).isLt
    have hrlen := gm06RootMask_sum_le x vs
    rw [gm06RootMask_sum] at hrlen
    exact (hi.trans_le hrlen).trans hN
  have hsrc : s₁.arrs 48 = [] ++ words ++ (s₁.arrs 48).drop words.length := by
    have hh := List.take_append_drop (s₁.regs 6404) (s₁.arrs 48)
    rw [hout, hcount] at hh
    exact hh.symm
  obtain ⟨s₂, t₂, he₂, ht₂, hresult, harr₂, hreg₂⟩ :=
    readSliceProg_exec (n := words.length) (off := 0) (s := s₁)
      48 47 (.const 0) 6404 6500 (by decide) (by decide)
      [] words ((s₁.arrs 48).drop words.length) rfl rfl hfit hw
      (by simpa only [Nat.zero_add] using hwordlen.trans_lt hK)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]) hsrc hcount
  have hcost : L.length * (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 74) =
      L.length * (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 58) + 16 * L.length := by
    rw [show 26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 74 =
      (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 58) + 16 by omega,
      Nat.mul_add, Nat.mul_comm L.length 16]
  simp only [Expr.cost] at ht₂
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by rw [hcost]; omega,
    hresult.trans (gm06GapUpdatedWords_eq x vs L g), ?_, ?_⟩
  · intro A hA hA' hA'' hA'''
    exact (harr₂ A hA'').trans (harr₁ A hA hA' hA''')
  · intro q hq hq' h187 h6400 h6401 h6402 h6403 h6404
    exact (hreg₂ q hq).trans (hreg₁ q hq' h187 h6400 h6401 h6402 h6403 h6404)

end GraphMinor.Compute
