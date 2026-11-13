module

public import GraphMinor.Compute.GM06Alg34DualPrepare
public import GraphMinor.Compute.GM06Alg34DualPayloadAlloc
public import GraphMinor.Compute.GM06Alg34DualWriteTime
public import GraphMinor.Compute.GM06Alg34DualNextCuffProg
public import GraphMinor.Compute.GM06Alg34DualInstall

/-!
# A complete RAM constructor for the augmented disc dual

Starting from the supplied drawing array and its explicit gap-region
array, prepare the finite incidence and class tables, reserve output
space, serialize the dual drawing and compute its following gap labels.
Finally install both exact arrays. The construction has a quartic time
bound and preserves the pending component queue and both queue cursors.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Construct and install the complete finite augmented dual from the current arrays. -/
def gm06DualBuildProg : Cmd :=
  .seq gm06DualPrepareProg (.seq gm06DualPayloadAllocProg
    (.seq gm06DualPayloadWriteProg (.seq gm06DualNextCuffProg gm06DualInstallProg)))

private theorem build_budget (C K Y t₁ t₂ t₃ t₄ t₅ : ℕ)
    (hC : 1 ≤ C) (hK : K + 1 ≤ C) (hY : Y ≤ C)
    (h₁ : t₁ ≤ 1000 * C) (h₂ : t₂ ≤ C + 30) (h₃ : t₃ ≤ 1000 * C)
    (h₄ : t₄ ≤ 100 * (K + 1)) (h₅ : t₅ ≤ 100 * (Y + K + 1)) :
    t₁ + (t₂ + (t₃ + (t₄ + t₅))) ≤ 4000 * C := by omega

/-- The complete constructor reads only supplied finite data and installs
exactly the augmented dual, in quartic time and logarithmic word size. -/
theorem gm06DualBuildProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (hR : 0 < x.regions.length) (hLN : L.Nodup)
    (hDiv : GM06.IsDivision x.divisionSet) (g : Fin L.length → Fin x.regions.length)
    {c : ℕ} (hc : 4 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hgap : s.arrs 47 = List.ofFn (fun i => (g i).val)) :
    ∃ s' t, Exec (wordSize c x.size) gm06DualBuildProg s s' t ∧
      t ≤ 4000 * (x.size + 2) ^ 4 ∧
      s'.arrs 0 = (x.dualData L hR g).words ∧
      s'.arrs 47 = (x.dualGapInput L hR g).discGapWords ∧
      s'.arrs 42 = s.arrs 42 ∧ s'.regs 7000 = s.regs 7000 ∧ s'.regs 7001 = s.regs 7001 ∧
      (∀ A : ℕ, 58 ≤ A → s'.arrs A = s.arrs A) := by
  let C := (x.size + 2) ^ 4
  let y := x.dualData L hR g
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hsize := lt_two_pow_wordSize_of_le hc1 (n := x.size) (Nat.le_succ _)
  have hS := x.five_le_words_length.trans x.words_length_le_size
  have hw : 2 < 2 ^ wordSize c x.size := by omega
  have hw1 : 1 < 2 ^ wordSize c x.size := by omega
  have hcounts := x.counts_le_size
  have hn := hcounts.1.trans_lt hsize
  have hkS := gm06Dual_cuff_length_le_size x hL
  have hk := hkS.trans_lt hsize
  have hN := x.cellCount_le_size.trans_lt hsize
  have hsquare := (Nat.mul_le_mul x.cellCount_le_size x.cellCount_le_size).trans_lt
    (show x.size * x.size < 2 ^ wordSize c x.size from
      (Nat.mul_le_mul (by omega : x.size ≤ x.size + 2) (by omega : x.size ≤ x.size + 2)).trans_lt
        (sq_lt_two_pow_wordSize (n := x.size) hc2))
  have hRspan := gm06Dual_count_span_lt_wordSize x hc2 hcounts.2.2
  have hEspan := gm06Dual_count_span_lt_wordSize x hc2 hcounts.2.1
  have hKspan := gm06Dual_count_span_lt_wordSize x hc2 hkS
  have hdouble := gm06Dual_double_cuff_lt_wordSize x hc2 hkS
  have hd := (gm06Dual_division_length_le_size x).trans_lt hsize
  have hcapacity := gm06Dual_capacity_lt_wordSize x hc
  have hyC : y.size ≤ C := gm06Dual_size_le_capacity x L hR g hkS
  have hyw : y.size < 2 ^ wordSize c x.size := hyC.trans_lt hcapacity
  have hwordsC : y.words.length ≤ C := y.words_length_le_size.trans hyC
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hL₁, hD₁, hmat₁, hmask₁, _, h51, h52, h53,
    hn₁, hm₁, hr₁, hk₁, hstride₁, hcount₁, hgap₁, hqueue₁, ha₁, hg₁⟩ :=
    gm06DualPrepareProg_exec x hL hLN hDiv hc hinput
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ := gm06DualPayloadAllocProg_exec x hc hin₁ hn₁
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, ha₃, hg₃⟩ :=
    gm06DualPayloadWriteProg_exec x L hR hLN hDiv g hw hN hsquare hRspan hEspan hKspan hdouble hd
      ((ha₂ 12 (by decide)).trans hmat₁) ((hg₂ 170 (by decide) (by decide)).trans hstride₁)
      ((hg₂ 100 (by decide) (by decide)).trans hn₁) ((hg₂ 101 (by decide) (by decide)).trans hm₁)
      ((hg₂ 102 (by decide) (by decide)).trans hr₁) ((ha₂ 2 (by decide)).trans hL₁)
      ((ha₂ 3 (by decide)).trans hD₁) ((hg₂ 105 (by decide) (by decide)).trans hk₁)
      ((ha₂ 47 (by decide)).trans (hgap₁.trans hgap))
      ((ha₂ 52 (by decide)).trans h52) ((ha₂ 51 (by decide)).trans h51)
      ((ha₂ 53 (by decide)).trans h53) ((ha₂ 45 (by decide)).trans hmask₁)
      ((hg₂ 275 (by decide) (by decide)).trans hcount₁)
      (pre := []) (cap := C - y.words.length)
      (by have heq : C = y.words.length + (C - y.words.length) := by omega
          exact heq ▸ hb₂)
      hp₂ (by simp only [List.length_nil, Nat.zero_add]; exact y.words_length_le_size.trans_lt hyw)
  have hb₃' : IsPrefixBuffer 55 y.words (C - y.words.length) s₃ := by
    simpa only [List.nil_append] using hb₃
  have hp₃' : s₃.regs 7804 = y.words.length := by simpa only [List.nil_append] using hp₃
  obtain ⟨s₄, t₄, he₄, ht₄, hnext₄, hknext₄, ha₄, hg₄⟩ :=
    gm06DualNextCuffProg_exec_input x L hR g hw1 hn hk
      ((ha₃ 2 (by decide) (by decide) (by decide) (by decide)).trans ((ha₂ 2 (by decide)).trans hL₁))
  obtain ⟨s₅, t₅, he₅, ht₅, hout₅, hgap₅, ha₅, hg₅⟩ :=
    gm06DualInstallProg_exec x L hR g hw1 hn hk hyw (hb₃'.of_arr_eq (ha₄ 55 (by decide)))
      ((hg₄ 7804 (by decide) (by decide)).trans hp₃') hnext₄ hknext₄
  have hC : 1 ≤ C := pow_pos (by omega : 0 < x.size + 2) 4
  have hK : L.length + 1 ≤ C := by
    have hb := Nat.le_self_pow (by decide : 4 ≠ 0) (x.size + 2)
    omega
  have htime₃ := ht₃.trans (gm06DualWriteTime_le x L hkS)
  have hreg (q : ℕ) (hq : q = 7000 ∨ q = 7001) : s₅.regs q = s.regs q := by
    exact (hg₅ q (by omega)).trans ((hg₄ q (by omega) (by omega)).trans
      ((hg₃ q (by omega) (Or.inr (by omega)) (by omega)).trans
        ((hg₂ q (by omega) (by omega)).trans (hg₁ q (by omega) (by omega)))))
  refine ⟨s₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))),
    build_budget C L.length y.size t₁ t₂ t₃ t₄ t₅ hC hK hyC ht₁ ht₂ htime₃ ht₄ ht₅,
    hout₅, hgap₅, ?_, hreg 7000 (Or.inl rfl), hreg 7001 (Or.inr rfl), ?_⟩
  · exact (ha₅ 42 (by decide) (by decide)).trans ((ha₄ 42 (by decide)).trans
      ((ha₃ 42 (by decide) (by decide) (by decide) (by decide)).trans ((ha₂ 42 (by decide)).trans hqueue₁)))
  · intro A hA
    exact (ha₅ A (by omega) (by omega)).trans ((ha₄ A (by omega)).trans
      ((ha₃ A (by omega) (by omega) (by omega) (by omega)).trans
        ((ha₂ A (by omega)).trans (ha₁ A hA))))

end GraphMinor.Compute
