module

public import GraphMinor.Compute.GM02WriteBalancedSides
public import GraphMinor.Compute.GM02BalancedSeparationOutput
public import GraphMinor.Compute.GM02DecodeSlots

/-!
# Building the successful balanced-separation output

Decode a successful separator code, recompute the remaining-terminal
count, run the proved greedy grouping scan, and write the two side arrays.
The resulting arrays encode the actual separation constructed from the
closed selected side. This supplies the successful output of II (3.1),
page 316, from the code found by the exhaustive search.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set TwoPaths GraphMinor.Compute.Crossing Classical

/-- Construct the balanced output from the successful code in register 191. -/
def gm02BuildBalancedOutputProg (k : ℕ) : Cmd :=
  .seq (.assign 190 (.reg 191)) (.seq (gm02DecodeSlots k)
    (.seq (gm02ComponentLabelsProg 200 k) (.seq (gm02CountIntersectionProg 5 aLab 0)
      (.seq (.assign 185 (.reg 183)) (.seq (gm02GroupingLoop k) (gm02WriteBalancedSidesProg k))))))

/-- A successful separator code produces the exact successful output
required by II (3.1), including the two encoded side vertex sets. -/
theorem gm02BuildBalancedOutputProg_exec_bits {k w code : ℕ} (x : GM02Alg31Input)
    (lists : Fin x.n → List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : 3 * x.n < 2 ^ w) (hb : x.n + 1 < 2 ^ w)
    (hp : (x.n + 1) ^ k < 2 ^ w) (hc : code < (x.n + 1) ^ k)
    (hadj : IsAdjList x.G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = x.n) (hq : s.arrs 5 = gm02VertexBits x.Q) (hcode : s.regs 191 = code)
    (hgood : ∀ a : Fin x.n,
      a ∉ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit x.n code i.val) →
      3 * (GM02.deletedComponent (Graph.ofSimpleGraph x.G)
        (gm02SlotVertices (n := x.n) (fun i : Fin k => gm02SeparatorDigit x.n code i.val) : Set (Fin x.n)) a ∩
          (x.Q : Set (Fin x.n))).ncard ≤
        2 * (x.Q \ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit x.n code i.val)).card) :
    ∃ s' t, Exec w (gm02BuildBalancedOutputProg k) s s' t ∧
      t ≤ 44 + k * (8 + 4 * k) + x.n *
        (185 + 18 * k + x.n * (k * 6 + 94) + 29 * totalAdjEntries lists) ∧ x.correct (k : ℤ) s' ∧
      ∃ L R : Finset (Fin x.n), s'.arrs outArr = gm02VertexBits L ∧ s'.arrs 2 = gm02VertexBits R := by
  let f : Fin k → ℕ := fun i => gm02SeparatorDigit x.n code i.val
  let X := gm02SlotVertices (n := x.n) f
  have hf : ∀ i, f i ≤ x.n := fun i => gm02SeparatorDigit_le x.n code i.val
  have hcomp : ∀ a ∉ X, 3 * (gm02FiniteComponent x.G X a ∩ x.Q).card ≤ 2 * (x.Q \ X).card := by
    intro a ha
    rw [gm02FiniteComponent_count]
    exact hgood a ha
  have hn' : x.n < 2 ^ w := (Nat.lt_succ_self x.n).trans hb
  have hcw : code < 2 ^ w := hc.trans hp
  let s₁ := s.setReg 190 code
  have he₁ : Exec w (.assign 190 (.reg 191)) s s₁ 2 := .assign (eval_reg hcode hcw)
  obtain ⟨s₂, t₂, he₂, ht₂, hslots₂, hframe₂, harr₂⟩ := gm02DecodeSlots_exec k s₁
    (by simpa [s₁] using hrn) (by simp [s₁]) hb hcw hp
  have hadj₂ : IsAdjList x.G 10 11 12 lists s₂ := hadj.of_arrs_eq
    (congrFun harr₂ _) (congrFun harr₂ _) (congrFun harr₂ _)
  have hrn₂ : s₂.regs 40 = x.n := (hframe₂ _ (Or.inl (by decide))).trans (by simpa [s₁] using hrn)
  have hq₂ : s₂.arrs 5 = gm02VertexBits x.Q := (congrFun harr₂ _).trans hq
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hl₃⟩ := gm02ComponentLabelsProg_exec 200 (by decide)
    f hf s₂ (by omega) hn' hrn₂ hslots₂
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hcount₄⟩ := gm02CountRemaining_exec x.Q X 5 aLab s₃
    (by omega) hn' ((hk₃.1 _ (by decide)).trans hrn₂) ((hk₃.2 _ (by decide)).trans hq₂) hl₃
  let s₅ := s₄.setReg 185 (x.Q \ X).card
  have hNw : (x.Q \ X).card < 2 ^ w :=
    ((Finset.card_le_card Finset.sdiff_subset).trans (by simpa using Finset.card_le_univ x.Q)).trans_lt hn'
  have he₅ : Exec w (.assign 185 (.reg 183)) s₄ s₅ 2 := .assign (eval_reg hcount₄ hNw)
  have hk₃' : Keeps [180, 182, 183, 185] [aLab] s₂ s₃ :=
    hk₃.mono (by intro r hr; obtain rfl := List.mem_singleton.1 hr; simp) (fun _ h => h)
  have hk₄' : Keeps [180, 182, 183, 185] [aLab] s₃ s₄ :=
    hk₄.mono (by intro r hr; simp at hr; rcases hr with rfl | rfl <;> simp) (by simp)
  have hk₅ : Keeps [180, 182, 183, 185] [aLab] s₂ s₅ :=
    (hk₃'.trans hk₄' (fun _ h => h) (fun _ h => h)).setReg (by simp) _
  have hslots₅ : ∀ i, s₅.regs (200 + i.val) = f i := by
    intro i
    apply (hk₅.1 _ ?_).trans (hslots₂ i)
    dsimp only [Reg]
    simp
    omega
  have hadj₅ : IsAdjList x.G 10 11 12 lists s₅ := hadj₂.of_arrs_eq
    (hk₅.2 _ (by decide)) (hk₅.2 _ (by decide)) (hk₅.2 _ (by decide))
  have hent₅ : (s₅.arrs 12).length < 2 ^ w := by simpa only [hk₅.2 12 (by decide), harr₂, s₁, State.setReg_arrs] using hent
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, hY₆, _, _⟩ := gm02GroupingLoop_exec x.G lists x.Q X f hf rfl
    hcomp s₅ hw hn hadj₅ hent₅ ((hk₅.1 _ (by decide)).trans hrn₂)
    ((hk₅.2 _ (by decide)).trans hq₂) hslots₅ (by simp [s₅])
  let Y := (gm02GroupingState x.G x.Q X x.n).1
  have hdis : Disjoint X Y := (gm02GroupingState_complete x.G x.Q X hcomp).2.1
  have hslots₆ : ∀ i, s₆.regs (200 + i.val) = f i := by
    intro i
    apply (hk₆.1 _ ?_).trans (hslots₅ i)
    dsimp only [Reg]
    simp [gm02GroupingRegs, gm02ComponentRegs]
    omega
  obtain ⟨s₇, t₇, he₇, ht₇, _, hflag, hleft, hright⟩ := gm02WriteBalancedSidesProg_exec X Y
    hdis f hf rfl s₆ (by omega) hn' ((hk₆.1 _ (by decide)).trans ((hk₅.1 _ (by decide)).trans hrn₂)) hY₆ hslots₆
  refine ⟨s₇, 2 + (t₂ + (t₃ + (t₄ + (2 + (t₆ + t₇))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇))))), ?_, Or.inl ⟨hflag, ?_⟩, ?_⟩
  · have heq : x.n * (185 + 18 * k + x.n * (k * 6 + 94) + 29 * totalAdjEntries lists) =
        x.n * (k * 6 + 19) + x.n * 17 + x.n +
          x.n * (114 + 6 * k + x.n * (k * 6 + 94) + 29 * totalAdjEntries lists) +
          x.n * (34 + 6 * k) := by ring
    rw [heq]
    omega
  · obtain ⟨H, H', hsep, hHV, hH'V, hinter, hL, hR⟩ := gm02GroupingState_separation x.G x.Q X hcomp
    refine ⟨H, H', hsep, ?_, ?_, ?_, hL, hR⟩
    · rw [hleft, gm02DecodedVertices_bits]
      exact hHV
    · rw [hright, gm02DecodedVertices_bits]
      exact hH'V
    · rw [hinter, Set.ncard_coe_finset]
      exact_mod_cast gm02SlotVertices_card_le (n := x.n) f

  · exact ⟨X ∪ Y, Finset.univ \ Y, hleft, hright⟩

/-- The output construction returns the valid separation required by (3.1). -/
theorem gm02BuildBalancedOutputProg_exec {k w code : ℕ} (x : GM02Alg31Input)
    (lists : Fin x.n → List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : 3 * x.n < 2 ^ w) (hb : x.n + 1 < 2 ^ w)
    (hp : (x.n + 1) ^ k < 2 ^ w) (hc : code < (x.n + 1) ^ k)
    (hadj : IsAdjList x.G 10 11 12 lists s) (hent : (s.arrs 12).length < 2 ^ w)
    (hrn : s.regs 40 = x.n) (hq : s.arrs 5 = gm02VertexBits x.Q) (hcode : s.regs 191 = code)
    (hgood : ∀ a : Fin x.n,
      a ∉ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit x.n code i.val) →
      3 * (GM02.deletedComponent (Graph.ofSimpleGraph x.G)
        (gm02SlotVertices (n := x.n) (fun i : Fin k => gm02SeparatorDigit x.n code i.val) : Set (Fin x.n)) a ∩
          (x.Q : Set (Fin x.n))).ncard ≤
        2 * (x.Q \ gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit x.n code i.val)).card) :
    ∃ s' t, Exec w (gm02BuildBalancedOutputProg k) s s' t ∧
      t ≤ 44 + k * (8 + 4 * k) + x.n *
        (185 + 18 * k + x.n * (k * 6 + 94) + 29 * totalAdjEntries lists) ∧ x.correct (k : ℤ) s' := by
  obtain ⟨s', t, he, ht, hout, _⟩ := gm02BuildBalancedOutputProg_exec_bits
    x lists s hw hn hb hp hc hadj hent hrn hq hcode hgood
  exact ⟨s', t, he, ht, hout⟩

end GraphMinor.Compute
