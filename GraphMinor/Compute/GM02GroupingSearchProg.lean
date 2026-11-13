module

public import GraphMinor.Compute.GM02GroupingGuard
public import GraphMinor.Compute.GM02ComponentRun
public import GraphMinor.Compute.GM02GroupingState

/-!
# Searching and grouping one new component

For an eligible vertex, search its component and count its terminals.
Choose it alone when its weight reaches a third. Otherwise add it to
the current side and update the threshold flag. The RAM outputs agree
with the data-only greedy step used in the proof of II (3.1).
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Scratch registers of a greedy component-grouping step. -/
def gm02GroupingRegs : List ℕ := 187 :: 188 :: gm02ComponentRegs

/-- Scratch arrays of a greedy component-grouping step. -/
def gm02GroupingArrays : List ℕ := 70 :: 71 :: gm02ComponentArrays

/-- Search an eligible component and take it alone or add it to the side. -/
def gm02GroupingSearchProg (k : ℕ) : Cmd :=
  .seq (gm02ComponentRunProg k) (.ite (gm02GroupingThresholdExpr 183)
    gm02TakeComponentProg gm02AddComponentProg)

/-- Searching an eligible component implements the exact greedy state
transition. Component closure makes the small-component count additive. -/
theorem gm02GroupingSearchProg_exec {n k w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (Q X Y : Finset (Fin n))
    (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n) (hX : X = gm02SlotVertices f)
    (a : Fin n) (haX : a ∉ X) (haY : a ∉ Y)
    (hclosed : ∀ v ∈ Y, gm02FiniteComponent G X v ⊆ Y)
    (s : State) (hw : 4 < 2 ^ w) (hn : 3 * n < 2 ^ w)
    (hadj : IsAdjList G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hra : s.regs 181 = a.val)
    (hq : s.arrs 5 = gm02VertexBits Q) (hslots : ∀ i, s.regs (200 + i.val) = f i)
    (hY : s.arrs 70 = gm02VertexBits Y) (hcountY : s.regs 187 = (Y ∩ Q).card)
    (hN : s.regs 185 = (Q \ X).card) :
    ∃ s' t, Exec w (gm02GroupingSearchProg k) s s' t ∧
      t ≤ 100 + n * (k * 6 + 94) + 29 * totalAdjEntries lists ∧
      Keeps gm02GroupingRegs gm02GroupingArrays s s' ∧
      let out := gm02GroupingStep G Q X a (Y, false)
      s'.arrs 70 = gm02VertexBits out.1 ∧ s'.regs 187 = (out.1 ∩ Q).card ∧
        s'.regs 188 = if out.2 then 1 else 0 := by
  have hn' : n < 2 ^ w := (show n ≤ 3 * n by omega).trans_lt hn
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hc₁, mask, hmask, hm, hmem⟩ :=
    gm02ComponentRunProg_exec G lists Q f hf a (by simpa only [hX] using haX)
      s hw hn' hadj hent hrn hra hq hslots
  let C := gm02FiniteComponent G X a
  have hC : ∀ v, mask v = 1 ↔ v ∈ C := by
    intro v
    simpa only [← hX, C, mem_gm02FiniteComponent] using hmem v
  have hc : s₁.regs 183 = (C ∩ Q).card := by
    rw [gm02FiniteComponent_count G Q X a]
    simpa only [← hX] using hc₁
  have hN₁ := (hk₁.1 185 (by decide)).trans hN
  have hNbound : (Q \ X).card ≤ n :=
    (Finset.card_le_card Finset.sdiff_subset).trans (by simpa using Finset.card_le_univ Q)
  have hCbound : (C ∩ Q).card ≤ n :=
    (Finset.card_le_card Finset.inter_subset_right).trans (by simpa using Finset.card_le_univ Q)
  have hecond := gm02GroupingThresholdExpr_eval s₁ 183 hw hn hNbound hCbound hN₁ hc
  have hk₁' : Keeps gm02GroupingRegs gm02GroupingArrays s s₁ :=
    hk₁.mono (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
      (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  by_cases hl : (Q \ X).card ≤ 3 * (C ∩ Q).card
  · have hecond' : (gm02GroupingThresholdExpr 183).eval w s₁ = some 1 := by
      simpa only [ite_eq_left hl] using hecond
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout, hcount, hready⟩ := gm02TakeComponentProg_exec Q C
      mask hm hC s₁ (by omega) hn' ((hk₁.1 _ (by decide)).trans hrn) hmask hc
    have hk₂' : Keeps gm02GroupingRegs gm02GroupingArrays s₁ s₂ :=
      hk₂.mono (by
        intro r hr
        simp at hr
        rcases hr with rfl | rfl | rfl <;> decide)
        (by intro b hb; obtain rfl := List.mem_singleton.1 hb; decide)
    refine ⟨s₂, t₁ + (5 + t₂), .seq he₁ (.ite_true hecond' (by decide) he₂), ?_,
      hk₁'.trans hk₂' (fun _ h => h) (fun _ h => h), ?_⟩
    · have hmul : n * (k * 6 + 94) = n * (k * 6 + 57) + n * 37 := by ring
      rw [hmul]
      have hn16 : n * 16 ≤ n * 37 := Nat.mul_le_mul_left n (by decide)
      omega
    · have hstep : gm02GroupingStep G Q X a (Y, false) = (C, true) := by
        have hl' : (Q \ X).card ≤ 3 * (gm02FiniteComponent G X a ∩ Q).card := hl
        simp [gm02GroupingStep, haX, haY, hl', C]
      rw [hstep]
      exact ⟨hout, hcount, hready⟩
  · have hecond' : (gm02GroupingThresholdExpr 183).eval w s₁ = some 0 := by
      simpa only [ite_eq_right hl] using hecond
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout, hcount, hready⟩ := gm02AddComponentProg_exec Q Y C
      (gm02FiniteComponent_disjoint_closed G X Y a haX haY hclosed) mask hm hC s₁ hw hn hNbound
      ((hk₁.1 _ (by decide)).trans hrn) hmask ((hk₁.2 _ (by decide)).trans hY)
      hc ((hk₁.1 _ (by decide)).trans hcountY) hN₁
    have hk₂' : Keeps gm02GroupingRegs gm02GroupingArrays s₁ s₂ :=
      hk₂.mono (by
        intro r hr
        simp at hr
        rcases hr with rfl | rfl | rfl <;> decide)
        (by intro b hb; rcases List.mem_cons.1 hb with rfl | hb
            · decide
            · obtain rfl := List.mem_singleton.1 hb; decide)
    refine ⟨s₂, t₁ + (5 + t₂), .seq he₁ (.ite_false hecond' he₂), ?_,
      hk₁'.trans hk₂' (fun _ h => h) (fun _ h => h), ?_⟩
    · have hmul : n * (k * 6 + 94) = n * (k * 6 + 57) + n * 37 := by ring
      rw [hmul]
      omega
    · have hstep : gm02GroupingStep G Q X a (Y, false) =
          (Y ∪ C, decide ((Q \ X).card ≤ 3 * ((Y ∪ C) ∩ Q).card)) := by
        simp [gm02GroupingStep, haX, haY, hl, C]
      rw [hstep]
      refine ⟨hout, hcount, ?_⟩
      simpa only [decide_eq_true_eq] using hready

end GraphMinor.Compute
