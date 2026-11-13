module

public import GraphMinor.Compute.PlanarityRamCount
public import GraphMinor.Compute.PlanarityRamInit
import Mathlib.Tactic.Linarith

/-!
# Preparing the RAM depth-first search

The program first counts adjacency entries and then allocates the search
arenas. The execution theorem uses the input convention of the planarity
specification. The handshaking identity changes the adjacency-entry bound
into a bound in the number of undirected edges. All protected registers and
arrays are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- Count adjacency entries, allocate search arrays, and clear live counters. -/
def prepareSearchProg : Cmd := .seq countEntriesProg initializeSearchProg

/-- The fixed logarithmic word bound suffices for all search arena capacities. -/
theorem preparation_word_bound (size w : ℕ) (hw : wordSize 2 size ≤ w) :
    4 * size < 2 ^ w := by
  have h := lt_two_pow_wordSize_of_lt_pow (c := 2) (n := size)
    (k := 4 * size) (by decide) (by nlinarith)
  exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hw)

/-- Part V, Section 1: preparation runs in linear time on the given
adjacency representation and leaves the initial search and empty frames
represented in fixed-capacity arrays. This theorem does not run the DFS. -/
theorem prepareSearchProg_exec (N : ℕ) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (lists : Fin N → List ℕ) (w : ℕ) (s : State)
    (hw : wordSize 2 (G.edgeFinset.card + N + 1) ≤ w)
    (hadj : IsAdjList G 30 31 32 lists s)
    (hentries : (s.arrs 32).length < 2 ^ w) (hN : s.regs 30 = N) :
    ∃ s' t, Exec w prepareSearchProg s s' t ∧
      t ≤ 300 * (G.edgeFinset.card + N + 1) ∧
      SearchAt N (totalAdjEntries lists) s' (LRPlanarity.initialSearch N) ∧
      FramesAt N s' [] ∧ s'.regs 36 = totalAdjEntries lists ∧
      (∀ r < 30, s'.regs r = s.regs r) ∧
      (∀ a < 33, s'.arrs a = s.arrs a) := by
  have hbound := preparation_word_bound (G.edgeFinset.card + N + 1) w hw
  have htotal := totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2
  have hcap : 2 * (N + totalAdjEntries lists + 1) < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hm, ha, hr⟩ := countEntriesProg_exec s hadj hN
    (by omega) (by omega) (by omega) hentries
  have hn₁ : s₁.regs 30 = N := (hr 30 (by decide) (by decide)).trans hN
  obtain ⟨t₂, hex₂, ht₂⟩ := initializeSearchProg_exec N (totalAdjEntries lists) w s₁ hn₁ hm hcap
  let s₂ := initializedSearchState N (totalAdjEntries lists) s₁
  have hp := initializedSearchState_preserves N (totalAdjEntries lists) s₁
  refine ⟨s₂, t₁ + t₂, Exec.seq hex₁ hex₂, ?_,
    initializedSearchState_searchAt N (totalAdjEntries lists) s₁,
    initializedSearchState_framesAt N (totalAdjEntries lists) s₁, ?_, ?_, ?_⟩
  · omega
  · exact (hp.1 36 (by decide) (by decide) (by decide)).trans hm
  · intro r hlt
    have h36 : r ≠ (36 : ℕ) := Nat.ne_of_lt (Nat.lt_trans hlt (by decide : 30 < 36))
    have h37 : r ≠ (37 : ℕ) := Nat.ne_of_lt (Nat.lt_trans hlt (by decide : 30 < 37))
    have h38 : r ≠ (38 : ℕ) := Nat.ne_of_lt (Nat.lt_trans hlt (by decide : 30 < 38))
    have h39 : r ≠ (39 : ℕ) := Nat.ne_of_lt (Nat.lt_trans hlt (by decide : 30 < 39))
    have h40 : r ≠ (40 : ℕ) := Nat.ne_of_lt (Nat.lt_trans hlt (by decide : 30 < 40))
    exact (hp.1 r h37 h38 h39).trans (hr r h36 h40)
  · intro a hlt
    exact (hp.2 a hlt).trans (congrFun ha a)

end GraphMinor.Compute.PlanarityRam
