module

public import GraphMinor.Compute.GM06Reduction1Current
public import GraphMinor.Compute.GM06Reduction2Current
public import GraphMinor.Compute.GM06Reduction3Current
public import GraphMinor.Compute.GM06CurrentLinkageMasks
public import GraphMinor.GM06.Alg57CurrentBounds
public import GraphMinor.GM06.Alg57ReductionMeasure
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The three early branches of the reduction loop

The loop in VI (5.7), page 133, rebuilds linkage masks and tests
Reductions 2, 1 and 3 in that order. It stops at the first success,
records the branch tag and resets the single bit to one. If all
three scans fail, their exact negative conclusions justify moving
to the cut-cylinder stage. Every successful branch returns the
complete current drawing relation and its actual undo step.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Report an early reduction and reset the loop bit. -/
@[expose] def gm06MarkEarlyReductionProg (tag : ℕ) : Cmd :=
  .seq (.assign 901 (.const tag)) (.assign 329 (.const 1))

/-- Rebuild masks and test the three size-decreasing branches in
paper order. Zero in register 901 means all three tests failed. -/
@[expose] def gm06EarlyReductionsProg : Cmd :=
  .seq (.assign 100 (.read 2 (.const 0)))
    (.seq gm06InitLinkageMasksProg
      (.seq gm06Reduction2CurrentProg
        (.ite (.reg 294) (gm06MarkEarlyReductionProg 2)
          (.seq gm06Reduction1CurrentProg
            (.ite (.reg 60) (gm06MarkEarlyReductionProg 1)
              (.seq gm06Reduction3CurrentProg
                (.ite (.reg 327) (gm06MarkEarlyReductionProg 3) (.assign 901 (.const 0)))))))))

/-- Sum of the three concrete scan budgets, two possible pruning
budgets and the mask rebuild. This is a fixed polynomial. -/
@[expose] def gm06EarlyReductionsCost (n m k r p f : ℕ) : ℕ :=
  let B := 1 + n + 2 * m + 4 * k
  let prune := 28 + 16 * m + 30 * k + n * (260 + 34 * n + 300 * r)
  40 + n + 36 * m + 22 * k + 14 * f +
    gm06Reduction2ScanCost n m k + 2 * prune +
    (7 + k * (131 + 117 * B + m * (120 + 104 * B))) +
    (7 + k * (73 + 42 * m + 17 * k + 22 * p + 13 * k) +
      683 + 28 * m + 1000 * r + 17 * k + 54 * p)

private theorem mark_early_exec {w : ℕ} (tag : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (htag : tag < 2 ^ w) :
    ∃ sf, Exec w (gm06MarkEarlyReductionProg tag) s sf 4 ∧
      Keeps [901, 329] [] s sf ∧ sf.regs 901 = tag ∧ sf.regs 329 = 1 := by
  let sm := s.setReg 901 tag
  let sf := sm.setReg 329 1
  refine ⟨sf, .seq (.assign (Crossing.eval_const htag)) (.assign (Crossing.eval_const hw)),
    ((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _, ?_, ?_⟩
  · simp [sf, sm]
  · simp [sf]

/-- The three actual early scans either exclude all early reductions,
or produce one full proper current relation and its actual inverse
record. Each success is a size-decreasing reduction round with bit one. -/
theorem gm06EarlyReductionsProg_exec
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (b : Bool) (hist : List ℕ) (c : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hcap : 4 * (1 + x.vertexCount + 2 * rep.tagged.length + 4 * k) < 2 ^ w)
    (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1)
    (hhist : hist.length < 2 ^ w) (hslot : 2 * c + 1 < hist.length)
    (h2 : s.arrs 2 = [x.vertexCount]) (h3 : s.arrs 3 = x.endpoints)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h6 : s.arrs 6 = x.innerCuff)
    (h7 : s.arrs 7 = x.outerCuff) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (h9 : s.arrs 9 = hist) (h12 : s.arrs 12 = rep.tagged.map Prod.snd)
    (h14 : s.arrs 14 = gm02VertexBits rep.live) (h309 : s.regs 309 = c) :
    ∃ sf t, Exec w gm06EarlyReductionsProg s sf t ∧
      t ≤ gm06EarlyReductionsCost x.vertexCount rep.tagged.length k
        (gm06EncodeRows x.rotations).length (gm06EncodeRows x.linkage).length x.linkage.flatten.length ∧
      (∀ a ∈ [2, 6, 7], sf.arrs a = s.arrs a) ∧
      sf.regs 900 = s.regs 900 ∧
      ((sf.regs 901 = 0 ∧ sf.regs 329 = s.regs 329 ∧ sf.regs 309 = c ∧
          (∀ a ∈ [3, 4, 8, 9, 12, 14], sf.arrs a = s.arrs a) ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction1Step k G L H M ∧
            ¬ Section5Reduction2Step k G L H M ∧
            ¬ Section5Reduction3Step k G L H M) ∨
       ∃ (ends : List ℕ) (rots paths : List (List ℕ))
         (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
         (cur : GM06CurrentDrawingRep {x with endpoints := ends, rotations := rots, linkage := paths} H M)
         (record : Option (ℕ × ℕ)),
         sf.regs 901 ∈ [1, 2, 3] ∧ sf.regs 329 = 1 ∧
         sf.arrs 3 = ends ∧ sf.arrs 4 = gm06EncodeRows rots ∧ sf.arrs 8 = gm06EncodeRows paths ∧
         sf.arrs 12 = cur.tagged.map Prod.snd ∧ sf.arrs 14 = gm02VertexBits cur.live ∧
         Function.Injective cur.vertex ∧ cur.tagged.length = rep.tagged.length ∧
         (∀ p ∈ cur.tagged, p.2 ≤ 1) ∧
         IsCylinderSection5Drawing k H ∧
         Alg57ReductionRound ⟨G, L, b⟩ ⟨H, M, true⟩ false ∧
         GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
           ⟨H, cur.tagged, cur.vertex, cur.edge⟩ record ∧
         sf.regs 309 = c + record.isSome.toNat ∧
         sf.arrs 9 = match record with
           | none => hist
           | some (i, d) => (hist.set (2 * c) i).set (2 * c + 1) d) := by
  classical
  have hw2 : 2 < 2 ^ w := by omega
  have hn : x.vertexCount < 2 ^ w := by omega
  have hm : 2 * rep.tagged.length < 2 ^ w := by omega
  have hk : k < 2 ^ w := by omega
  have hsize : 2 * (rep.tagged.length + k) + 1 < 2 ^ w := by omega
  have hinner : x.innerCuff.length = k := by rw [rep.inner, List.length_ofFn]
  have houter : x.outerCuff.length = k := by rw [rep.outer, List.length_ofFn]
  have haug : rep.tagged.length + 2 * x.innerCuff.length < 2 ^ w := by rw [hinner]; omega
  obtain ⟨hrLen, hpLen, hrWords, hpWords⟩ := rep.scan_word_bounds hG hcap
  obtain ⟨hkB, hnB, hpathsB, hrotsB⟩ := rep.scan_row_bounds hG
  have hdarts : ∀ row ∈ x.rotations, ∀ d ∈ row,
      d < 2 * (rep.tagged.length + 2 * x.innerCuff.length) := by
    intro row hr d hd
    have hh := rep.rotation_word_lt hG (List.mem_flatten.mpr ⟨row, hr, hd⟩)
    rw [hinner]
    omega
  let s₀ := s.setReg 100 x.vertexCount
  have he₀ : Exec w (.assign 100 (.read 2 (.const 0))) s s₀ 3 := by
    apply Exec.assign
    simp [Expr.eval, checkWord, h2, hn]
  obtain ⟨s₁, t₁, Q, D, he₁, ht₁, hk₁, h17₁, _, _, hQ⟩ := gm06InitLinkageMasksProg_current rep s₀
    hw2 hn hm hk hpLen (by simp [s₀]) h3 h8
  have hf₁ (a : ℕ) (ha : a ≠ 17) (ha' : a ≠ 19) : s₁.arrs a = s.arrs a :=
    hk₁.2 a (by simp [ha, ha'])
  have hr₁ (r : ℕ) (hr : r ∈ [309, 329, 900]) : s₁.regs r = s.regs r := by
    have hnr : r ∉ [40, 280, 281, 282, 283, 285] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    have h100 : r ≠ 100 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    exact (hk₁.1 r hnr).trans (State.setReg_regs_ne _ _ h100)
  obtain ⟨s₂, t₂, he₂, ht₂, hf₂, hr₂, hout₂⟩ := gm06Reduction2CurrentProg_exec rep hvinj hG Q hQ
    hw2 hn hsquare hm hk hbits hrLen hrWords haug hdarts
    ((hf₁ 3 (by decide) (by decide)).trans h3) ((hf₁ 4 (by decide) (by decide)).trans h4)
    ((hf₁ 6 (by decide) (by decide)).trans h6) ((hf₁ 8 (by decide) (by decide)).trans h8)
    ((hf₁ 12 (by decide) (by decide)).trans h12) ((hf₁ 14 (by decide) (by decide)).trans h14)
    h17₁ ((hk₁.1 100 (by decide)).trans (by simp [s₀]))
  have hcore₂ (a : ℕ) (ha : a ∈ [2, 6, 7]) : s₂.arrs a = s.arrs a := by
    apply (hf₂ a ?_).trans (hf₁ a ?_ ?_)
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide
  have hreg₂ (r : ℕ) (hr : r ∈ [309, 329, 900]) : s₂.regs r = s.regs r :=
    (hr₂ r hr).trans (hr₁ r hr)
  rcases hout₂ with ⟨hflag₂, h4₂, h12₂, h14₂, hno₂⟩ |
      ⟨mask, H, M, cur, hflag₂, hflagBound, h3₂, h4₂, h8₂, h12₂, h14₂, hlen, hmaskBits, htag, hv, hH, hred, _, hundo⟩
  · obtain ⟨s₃, t₃, he₃, ht₃, hf₃, hr₃, hout₃⟩ := gm06Reduction1CurrentProg_exec rep hG hθ hw2 hsize
      hpLen hrLen hpWords hrWords hkB hnB hpathsB hrotsB hbits haug hdarts
      ((hf₂ 3 (by simp)).trans ((hf₁ 3 (by decide) (by decide)).trans h3)) h4₂
      ((hcore₂ 6 (by simp)).trans h6) ((hf₂ 8 (by simp)).trans ((hf₁ 8 (by decide) (by decide)).trans h8))
      h12₂ h14₂
    have hcore₃ (a : ℕ) (ha : a ∈ [2, 6, 7]) : s₃.arrs a = s.arrs a := by
      apply (hf₃ a ?_).trans (hcore₂ a ha)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> decide
    have hreg₃ (r : ℕ) (hr : r ∈ [309, 329, 900]) : s₃.regs r = s.regs r :=
      (hr₃ r hr).trans (hreg₂ r hr)
    rcases hout₃ with ⟨hflag₃, h4₃, h12₃, hno₁⟩ |
        ⟨j, M, cur, hflag₃, h3₃, h4₃, h8₃, h12₃, h14₃, hA, hv, htag, hH, hred, _, hundo⟩
    · obtain ⟨s₄, t₄, he₄, ht₄, hf₄, hr₄, hout₄⟩ := gm06Reduction3CurrentProg_exec rep hvinj hG hist c s₃
        hw2 hn hm hk hbits hrLen hrWords hpLen hpWords hhist hslot
        ((hf₃ 3 (by simp)).trans ((hf₂ 3 (by simp)).trans ((hf₁ 3 (by decide) (by decide)).trans h3))) h4₃
        ((hcore₃ 6 (by simp)).trans h6) ((hcore₃ 7 (by simp)).trans h7)
        ((hf₃ 8 (by simp)).trans ((hf₂ 8 (by simp)).trans ((hf₁ 8 (by decide) (by decide)).trans h8)))
        ((hf₃ 9 (by simp)).trans ((hf₂ 9 (by simp)).trans ((hf₁ 9 (by decide) (by decide)).trans h9)))
        h12₃ ((hf₃ 14 (by simp)).trans h14₂) ((hreg₃ 309 (by simp)).trans h309)
      have hcore₄ (a : ℕ) (ha : a ∈ [2, 6, 7]) : s₄.arrs a = s.arrs a := by
        apply (hf₄ a ?_).trans (hcore₃ a ha)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> decide
      have hreg₄ (r : ℕ) (hr : r ∈ [329, 900]) : s₄.regs r = s.regs r := by
        apply (hr₄ r hr).trans (hreg₃ r ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> simp
      rcases hout₄ with ⟨hflag₄, hc₄, hsame, hno₃⟩ |
          ⟨i, v, first, rest, H, M, cur, hflag₄, h3₄, h4₄, h8₄, h12₄, h14₄,
            hc₄, hh₄, _, _, hH, hred, hinj, hA, htag, hundo⟩
      · let sf := s₄.setReg 901 0
        have he₅ : Exec w (.assign 901 (.const 0)) s₄ sf 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
        refine ⟨sf, 3 + (t₁ + (t₂ + (1 + (t₃ + (1 + (t₄ + (1 + 2))))))),
          .seq he₀ (.seq he₁ (.seq he₂ (.ite_false (Crossing.eval_reg hflag₂ (Nat.two_pow_pos w))
            (.seq he₃ (.ite_false (Crossing.eval_reg hflag₃ (Nat.two_pow_pos w))
              (.seq he₄ (.ite_false (Crossing.eval_reg hflag₄ (Nat.two_pow_pos w)) he₅))))))),
          ?_, hcore₄, ?_, Or.inl ⟨by simp [sf], ?_, by simpa [sf] using hc₄, ?_, ?_⟩⟩
        · simp only [gm06EarlyReductionsCost, hinner, houter, rep.rows_length] at *
          omega
        · exact (State.setReg_regs_ne _ _ (by decide)).trans (hreg₄ 900 (by simp))
        · exact (State.setReg_regs_ne _ _ (by decide)).trans (hreg₄ 329 (by simp))
        · intro a ha
          have h12same : s₂.arrs 12 = s.arrs 12 := h12₂.trans h12.symm
          have h14same : s₂.arrs 14 = s.arrs 14 := h14₂.trans h14.symm
          have h4same : s₃.arrs 4 = s.arrs 4 := h4₃.trans h4.symm
          apply (hsame a ha).trans
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
          · exact (hf₃ 3 (by simp)).trans ((hf₂ 3 (by simp)).trans (hf₁ 3 (by decide) (by decide)))
          · exact h4same
          · exact (hf₃ 8 (by simp)).trans ((hf₂ 8 (by simp)).trans (hf₁ 8 (by decide) (by decide)))
          · exact (hf₃ 9 (by simp)).trans ((hf₂ 9 (by simp)).trans (hf₁ 9 (by decide) (by decide)))
          · exact h12₃.trans h12.symm
          · exact (hf₃ 14 (by simp)).trans h14same
        · intro H M
          exact ⟨hno₁ H M, hno₂ H M, hno₃ H M⟩
      · obtain ⟨sf, he₅, hk₅, h901, h329⟩ := mark_early_exec 3 s₄ (by omega) hw
        refine ⟨sf, 3 + (t₁ + (t₂ + (1 + (t₃ + (1 + (t₄ + (1 + 4))))))),
          .seq he₀ (.seq he₁ (.seq he₂ (.ite_false (Crossing.eval_reg hflag₂ (Nat.two_pow_pos w))
            (.seq he₃ (.ite_false (Crossing.eval_reg hflag₃ (Nat.two_pow_pos w))
              (.seq he₄ (.ite_true (Crossing.eval_reg hflag₄ (by omega)) (by decide) he₅))))))),
          ?_, (fun a ha => (hk₅.2 a (by simp)).trans (hcore₄ a ha)),
          (hk₅.1 900 (by decide)).trans (hreg₄ 900 (by simp)), Or.inr ?_⟩
        · simp only [gm06EarlyReductionsCost, hinner, houter, rep.rows_length] at *
          omega
        · let y := gm06ContractSuccessorInput x (rep.source i).val v.val i.val first rest
          refine ⟨y.endpoints, y.rotations, y.linkage, H, M, cur, some (i.val, first),
            by simp [h901], h329, (hk₅.2 3 (by simp)).trans h3₄, (hk₅.2 4 (by simp)).trans h4₄,
            (hk₅.2 8 (by simp)).trans h8₄, (hk₅.2 12 (by simp)).trans h12₄,
            (hk₅.2 14 (by simp)).trans h14₄, hinj, ?_, ?_, hH, .three hred hH rfl, hundo,
            (hk₅.1 309 (by decide)).trans hc₄, (hk₅.2 9 (by simp)).trans hh₄⟩
          · rw [htag, gm06ContractTaggedEdges_length]
          · rw [htag]
            exact gm06ContractTaggedEdges_flags_le_one _ _ _ _ hbits
    · obtain ⟨sf, he₄, hk₄, h901, h329⟩ := mark_early_exec (w := w) 1 s₃ (by omega) (by omega)
      refine ⟨sf, 3 + (t₁ + (t₂ + (1 + (t₃ + (1 + 4))))),
        .seq he₀ (.seq he₁ (.seq he₂ (.ite_false (Crossing.eval_reg hflag₂ (Nat.two_pow_pos w))
          (.seq he₃ (.ite_true (Crossing.eval_reg hflag₃ (by omega)) (by decide) he₄))))),
        ?_, (fun a ha => (hk₄.2 a (by simp)).trans (hcore₃ a ha)),
        (hk₄.1 900 (by decide)).trans (hreg₃ 900 (by simp)), Or.inr ?_⟩
      · simp only [gm06EarlyReductionsCost, hinner, houter, rep.rows_length] at *
        omega
      · let mask := (rep.tagged.map Prod.snd).set j.val 0
        let y := gm06RestrictSuccessorInput x mask
        have hlen : mask.length = rep.tagged.length := by simp only [mask, List.length_set, List.length_map]
        refine ⟨y.endpoints, y.rotations, y.linkage, _, M, cur, none,
          by simp [h901], h329, (hk₄.2 3 (by simp)).trans h3₃, (hk₄.2 4 (by simp)).trans h4₃,
          (hk₄.2 8 (by simp)).trans h8₃, (hk₄.2 12 (by simp)).trans h12₃,
          (hk₄.2 14 (by simp)).trans h14₃, hv.symm ▸ hvinj, ?_, ?_, hH, .one hred hH rfl, hundo,
          (hk₄.1 309 (by decide)).trans ((hreg₃ 309 (by simp)).trans h309), ?_⟩
        · rw [htag, gm06RetagEdges_length]
        · rw [htag]
          apply gm06RetagEdges_flags_le_one _ mask hlen
          intro z hz
          rcases List.mem_or_eq_of_mem_set hz with hz | hz
          · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
            exact hbits p hp
          · exact hz ▸ Nat.zero_le 1
        · exact (hk₄.2 9 (by simp)).trans ((hf₃ 9 (by simp)).trans
            ((hf₂ 9 (by simp)).trans ((hf₁ 9 (by decide) (by decide)).trans h9)))
  · have hflagLt : s₂.regs 294 < 2 ^ w := hflagBound.trans_le (by omega)
    obtain ⟨sf, he₃, hk₃, h901, h329⟩ := mark_early_exec (w := w) 2 s₂ (by omega) (by omega)
    refine ⟨sf, 3 + (t₁ + (t₂ + (1 + 4))),
      .seq he₀ (.seq he₁ (.seq he₂ (.ite_true (Crossing.eval_reg rfl hflagLt) hflag₂ he₃))),
      ?_, (fun a ha => (hk₃.2 a (by simp)).trans (hcore₂ a ha)),
      (hk₃.1 900 (by decide)).trans (hreg₂ 900 (by simp)), Or.inr ?_⟩
    · simp only [gm06EarlyReductionsCost, hinner, houter, rep.rows_length] at *
      omega
    · let y := gm06RestrictSuccessorInput x mask
      refine ⟨y.endpoints, y.rotations, y.linkage, H, M, cur, none,
        by simp [h901], h329, (hk₃.2 3 (by simp)).trans h3₂, (hk₃.2 4 (by simp)).trans h4₂,
        (hk₃.2 8 (by simp)).trans h8₂, (hk₃.2 12 (by simp)).trans h12₂,
        (hk₃.2 14 (by simp)).trans h14₂, hv.symm ▸ hvinj, ?_, ?_, hH, .two hred hH rfl, hundo,
        (hk₃.1 309 (by decide)).trans ((hreg₂ 309 (by simp)).trans h309), ?_⟩
      · rw [htag, gm06RetagEdges_length]
      · rw [htag]
        exact gm06RetagEdges_flags_le_one _ _ hlen hmaskBits
      · exact (hk₃.2 9 (by simp)).trans ((hf₂ 9 (by simp)).trans ((hf₁ 9 (by decide) (by decide)).trans h9))

private theorem early_cost_mono {n m k r p f S : ℕ}
    (hn : n ≤ S) (hm : m ≤ S) (hk : k ≤ S)
    (hr : r ≤ S) (hp : p ≤ S) (hf : f ≤ S) :
    gm06EarlyReductionsCost n m k r p f ≤ gm06EarlyReductionsCost S S S S S S := by
  unfold gm06EarlyReductionsCost gm06Reduction2ScanCost
  dsimp only
  gcongr

private theorem early_cost_uniform (S : ℕ) (hS : 1 ≤ S) :
    gm06EarlyReductionsCost S S S S S S ≤ 100000 * S ^ 4 := by
  have h0 : S ^ 0 ≤ S ^ 4 := pow_le_pow_right' hS (by decide)
  have h1 : S ^ 1 ≤ S ^ 4 := pow_le_pow_right' hS (by decide)
  have h2 : S ^ 2 ≤ S ^ 4 := pow_le_pow_right' hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 4 := pow_le_pow_right' hS (by decide)
  unfold gm06EarlyReductionsCost gm06Reduction2ScanCost
  ring_nf
  nlinarith

/-- The verified dense early scans have a uniform fourth-degree
bound in their finite input sizes. The paper requires a polynomial
bound, and the outer decreasing-measure loop contributes one more
factor in the original slot counts. -/
theorem gm06EarlyReductionsCost_le_quartic (n m k r p f : ℕ) :
    gm06EarlyReductionsCost n m k r p f ≤
      100000 * (1 + n + m + k + r + p + f) ^ 4 := by
  let S := 1 + n + m + k + r + p + f
  exact (early_cost_mono (S := S) (by dsimp [S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
    (by dsimp [S]; omega)).trans (early_cost_uniform S (by dsimp [S]; omega))

end GraphMinor.Compute
