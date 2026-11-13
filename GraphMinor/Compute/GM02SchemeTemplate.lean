module

public import GraphMinor.Compute.GM02TemplatePairFields
public import GraphMinor.Compute.GM02BoundarySchemeCode

/-!
# The executable data fields of one fixed crossing-scheme template

A catalogue code fixes two pair sets and two reserved sets on a bounded
boundary. Flatten each matching in canonical edge order. Expand both
endpoint lists and their support bits, then expand the two reserved
sets. All parent names are read from the inverse boundary numbering.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Endpoint indices in canonical order for a fixed finite pair set. -/
noncomputable def gm02TemplatePairIndices {b : ℕ} (P : Finset (Sym2 (Fin b))) : List (Fin b) :=
  (edgeListOf (SimpleGraph.fromEdgeSet (P : Set (Sym2 (Fin b))))).flatMap
    (fun p => [p.1, p.2])

/-- Six data arrays for a fixed scheme template, with one shared scratch array. -/
noncomputable def gm02SchemeTemplateProg {b : ℕ} (D : GM02BoundarySchemeData b)
    (orig a : Arr) : Cmd :=
  .seq (gm02TemplatePairFieldsProg orig a (a + 1) (a + 2)
      ((gm02TemplatePairIndices D.1).map Fin.val))
    (.seq (gm02TemplatePairFieldsProg orig a (a + 3) (a + 4)
        ((gm02TemplatePairIndices D.2.1).map Fin.val))
      (.seq (gm02TemplateBitsProg orig (a + 5) (D.2.2.1.toList.map Fin.val))
        (gm02TemplateBitsProg orig (a + 6) (D.2.2.2.toList.map Fin.val))))

private theorem template_array_subsets (a : ℕ) :
    [a, a + 1, a + 2] ⊆ [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] ∧
    [a, a + 3, a + 4] ⊆ [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] ∧
    [a + 5] ⊆ [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] ∧
    [a + 6] ⊆ [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] := by
  simp only [List.subset_def, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Expanding the fixed data creates both matchings, both supports, and both reservations. -/
theorem gm02SchemeTemplateProg_exec {n b w : ℕ} (D : GM02BoundarySchemeData b)
    (f : Fin b → Fin n) (orig a : Arr) (hoa : orig < a) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b < 2 ^ w)
    (hl : (gm02TemplatePairIndices D.1).length < 2 ^ w)
    (hr : (gm02TemplatePairIndices D.2.1).length < 2 ^ w)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val)) (hcount : s.regs 40 = n) :
    ∃ s' t, Exec w (gm02SchemeTemplateProg D orig a) s s' t ∧
      t ≤ 44 + 21 * ((gm02TemplatePairIndices D.1).length +
        (gm02TemplatePairIndices D.2.1).length) +
        n * (60 + 7 * ((gm02TemplatePairIndices D.1).length +
          (gm02TemplatePairIndices D.2.1).length + D.2.2.1.card + D.2.2.2.card)) ∧
      s'.arrs (a + 1) = (gm02TemplatePairIndices D.1).map (fun i => (f i).val) ∧
      s'.arrs (a + 2) = bitSetList ((gm02TemplatePairIndices D.1).toFinset.image f) ∧
      s'.arrs (a + 3) = (gm02TemplatePairIndices D.2.1).map (fun i => (f i).val) ∧
      s'.arrs (a + 4) = bitSetList ((gm02TemplatePairIndices D.2.1).toFinset.image f) ∧
      s'.arrs (a + 5) = bitSetList (D.2.2.1.image f) ∧
      s'.arrs (a + 6) = bitSetList (D.2.2.2.image f) ∧
      Keeps [343, 342, 340] [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] s s' := by
  obtain ⟨s₁, t₁, he₁, ht₁, hL, hLS, hk₁⟩ :=
    gm02TemplatePairFieldsProg_exec f (gm02TemplatePairIndices D.1) orig a (a + 1) (a + 2)
      (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) s hw hn hb hl horig hcount
  have ho₁ := (hk₁.2 orig (by simp; dsimp only [Arr] at *; omega)).trans horig
  have hn₁ := (hk₁.1 40 (by decide)).trans hcount
  obtain ⟨s₂, t₂, he₂, ht₂, hR, hRS, hk₂⟩ :=
    gm02TemplatePairFieldsProg_exec f (gm02TemplatePairIndices D.2.1) orig a (a + 3) (a + 4)
      (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) (by dsimp only [Arr] at *; omega) s₁ hw hn hb hr ho₁ hn₁
  have ho₂ := (hk₂.2 orig (by simp; dsimp only [Arr] at *; omega)).trans ho₁
  have hn₂ := (hk₂.1 40 (by decide)).trans hn₁
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hZ⟩ := gm02TemplateBitsProg_exec f D.2.2.1.toList orig
    (a + 5) (by dsimp only [Arr] at *; omega) s₂ hw hn hb ho₂ hn₂
  have ho₃ := (hk₃.2 orig (by simp; dsimp only [Arr] at *; omega)).trans ho₂
  have hn₃ := (hk₃.1 40 (by decide)).trans hn₂
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hZ'⟩ := gm02TemplateBitsProg_exec f D.2.2.2.toList orig
    (a + 6) (by dsimp only [Arr] at *; omega) s₃ hw hn hb ho₃ hn₃
  have frame : Keeps [343, 342, 340] [a, a + 1, a + 2, a + 3, a + 4, a + 5, a + 6] s s₄ := by
    have hsub := template_array_subsets a
    have h₁ := hk₁.mono (R' := [343, 342, 340]) (fun _ h => h) hsub.1
    have h₂ := hk₂.mono (R' := [343, 342, 340]) (fun _ h => h) hsub.2.1
    have h₃ := hk₃.mono (R' := [343, 342, 340]) (by decide) hsub.2.2.1
    exact ((h₁.trans h₂ (fun _ h => h) (fun _ h => h)).trans h₃
      (fun _ h => h) (fun _ h => h)).trans hk₄ (by decide) hsub.2.2.2
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, frame⟩
  · simp only [Finset.length_toList] at ht₃ ht₄
    ring_nf at ht₁ ht₂ ht₃ ht₄ ⊢
    omega
  · rw [hk₄.2 (a + 1) (by simp), hk₃.2 (a + 1) (by simp), hk₂.2 (a + 1) (by simp)]
    exact hL
  · rw [hk₄.2 (a + 2) (by simp), hk₃.2 (a + 2) (by simp), hk₂.2 (a + 2) (by simp)]
    exact hLS
  · rw [hk₄.2 (a + 3) (by simp), hk₃.2 (a + 3) (by simp)]
    exact hR
  · rw [hk₄.2 (a + 4) (by simp), hk₃.2 (a + 4) (by simp)]
    exact hRS
  · rw [hk₄.2 (a + 5) (by simp)]
    simpa using hZ
  · simpa using hZ'

end GraphMinor.Compute
