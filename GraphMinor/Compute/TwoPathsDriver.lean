module

public import GraphMinor.Compute.TwoPathsDriverReturn
public import GraphMinor.Compute.TwoPathsDriverMath
public import GraphMinor.Compute.TwoPathsDriverCost
public import GraphMinor.Compute.WhileRounds

/-!
# The driver of Algorithm 5.1

Algorithm 5.1 of Humeau and Pous (page 18) is recursive: line 10 splits the instance into two
subinstances and line 11 returns `2DP(G_1, C_1) ∨ 2DP(G_2, C_2)`. The machine has no recursion,
so the driver runs the algorithm as one loop with an explicit stack of frames on the heap
`aHeap`. A frame holds the arrays of an instance that is waiting for the answer of a subinstance,
with the side `1` or `2` of that subinstance (`TwoPathsDriverProg.lean`). Register `rMode` says
what the next round does:
* mode `0`: solve the instance in memory (`solveRound`, `TwoPathsDriverSolve.lean`). The round
  answers at once (lines 2–7, and line 9 when the completion step finds a crossing) and goes to
  mode `1`, or it pushes a frame and writes subinstance `1` into memory (line 10), and stays in
  mode `0`;
* mode `1`: return the answer in `rRes` to the frame on top of the stack (`returnRound`,
  `TwoPathsDriverReturn.lean`): lift a crossing with the extraction step, or go on with
  subinstance `2`, or pop the frame with the answer `False`. When the stack is empty, go to
  mode `2`;
* mode `2`: stop.

**The proof.** The rounds that solve one instance, from the round that starts it in mode `0` to
the round that leaves its answer in mode `1` with the stack as it was, form a stretch of rounds
(`Rounds`, `WhileRounds.lean`). `drive` proves that this stretch exists, with the right answer
and a bound on its time, by strong induction on the potential `Φ = 2|S| - |T| - 3` of the
instance (`S` its vertex set): by `SplitData.counts`, both subinstances have a smaller potential.
This is the recursion of Algorithm 5.1, read as an induction on the calls. The invariant of an
instance in memory is `SolveAt`; the counts of time and heap are in `TwoPathsDriverCost.lean`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### The loop -/

/-- The loop runs while the mode is `0` or `1`. -/
def loopCond : Expr := .op .lt (.reg rMode) (.const 2)

/-- One round: solve in mode `0`, return in mode `1`. -/
def loopBody (comp ext : Cmd) : Cmd :=
  .ite (.op .eq (.reg rMode) (.const 0)) (solveRound comp) (returnRound ext)

/-- **The driver loop** of Algorithm 5.1. -/
def driverLoop (comp ext : Cmd) : Cmd := .while loopCond (loopBody comp ext)

theorem loopCond_cost : loopCond.cost = 3 := rfl

/-- A solve round is a round of the loop. -/
theorem round_solve {w : ℕ} (hw : 2 < 2 ^ w) {comp ext : Cmd} {s s' : State} {t : ℕ}
    (hm : s.regs rMode = 0) (h : Exec w (solveRound comp) s s' t) :
    Rounds w loopCond (loopBody comp ext) s s' (6 + t) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h1 : loopCond.eval w s = some 1 := by
    have := lt_eval (reg_eval hm (by omega)) (const_eval' (c := 2) (s := s) hw) hw1
    simpa [loopCond] using this
  have h2 : (Expr.op .eq (.reg rMode) (.const 0)).eval w s = some 1 := by
    have := eq_eval (reg_eval hm (by omega)) (const_eval' (c := 0) (s := s) (by omega)) hw1
    simpa using this
  have := Rounds.single (body := loopBody comp ext) h1 one_ne_zero (.ite_true h2 one_ne_zero h)
  convert this using 1
  simp only [loopCond, Expr.cost]; omega

/-- A return round is a round of the loop. -/
theorem round_return {w : ℕ} (hw : 2 < 2 ^ w) {comp ext : Cmd} {s s' : State} {t : ℕ}
    (hm : s.regs rMode = 1) (h : Exec w (returnRound ext) s s' t) :
    Rounds w loopCond (loopBody comp ext) s s' (6 + t) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h1 : loopCond.eval w s = some 1 := by
    have := lt_eval (reg_eval hm (by omega)) (const_eval' (c := 2) (s := s) hw) hw1
    simpa [loopCond] using this
  have h2 : (Expr.op .eq (.reg rMode) (.const 0)).eval w s = some 0 := by
    have := eq_eval (reg_eval hm (by omega)) (const_eval' (c := 0) (s := s) (by omega)) hw1
    simpa using this
  have := Rounds.single (body := loopBody comp ext) h1 one_ne_zero (.ite_false h2 h)
  convert this using 1
  simp only [loopCond, Expr.cost]; omega

/-! ### The invariant of an instance in memory -/

/-- The instance `(H, T)` with vertex set `S` is in memory at the start of its first round, the
stack holds `D` and the free part `R` of the heap is large enough for the instance. The arrays
`aEnt` hold at most `2E + N f` entries, where `f` is the length of the list of new edges of the
split that made the instance. -/
structure SolveAt (w N E c : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj]
    (lists : Fin N → List ℕ) (T : List (Fin N)) (S : Finset (Fin N)) (f : ℕ) (D R : List ℕ)
    (s : State) : Prop where
  n40 : s.regs 40 = N
  adj : IsAdjList H aStart aEnd aEnt lists s
  cyc : s.arrs aCyc = T.map Fin.val
  cycle : IsCycleList H T
  edges : EdgesIn H S
  budget : H.edgeFinset.card + (2 * S.card - T.length - 3) + (S.card - T.length) ≤ E
  mode : s.regs rMode = 0
  heap : s.arrs aHeap = D ++ R
  hp : s.regs rHp = D.length
  need : drvNeed N E c (2 * S.card - T.length - 3) (S.card - T.length) f ≤ R.length
  hDR : D.length + R.length < 2 ^ w
  ent : (s.arrs aEnt).length ≤ 2 * E + N * f
  hf : f ≤ 2 * N + 1
  words : ∀ x ∈ frameArrs, ∀ v ∈ s.arrs x, v < 2 ^ w
  hwords : ∀ v ∈ s.arrs aHeap, v < 2 ^ w

/-- What the stretch of rounds of an instance leaves: mode `1`, the stack as it was, the heap of
the same length, `Low` kept, and the answer in `rRes` (with a crossing in `aQ`, `aR` for the
answer `True`), within the time `drvTime`, plus `c N W` for the answer `True`. -/
def DoneAt (w N E c : ℕ) (H : SimpleGraph (Fin N)) (T : List (Fin N)) (Φ Ψ f : ℕ)
    (D R : List ℕ) (s s' : State) (t : ℕ) (comp ext : Cmd) : Prop :=
  ∃ R', Rounds w loopCond (loopBody comp ext) s s' t ∧ s'.regs rMode = 1 ∧
    s'.regs rHp = D.length ∧ s'.arrs aHeap = D ++ R' ∧ R'.length = R.length ∧ Low s s' ∧
    ((s'.regs rRes = 0 ∧ ¬ IsCrossed H T ∧ t ≤ drvTime N E c Φ Ψ f) ∨
      (s'.regs rRes = 1 ∧ CrossingAt H T aQ aR s' ∧
        t ≤ drvTime N E c Φ Ψ f + c * N * (N + E + 1)))

/-! ### The induction on the instances -/

section Drive

variable {comp ext : Cmd} {c c_w : ℕ} {N w E : ℕ}

/-- The heap fits the frame of a split of an instance in memory. -/
theorem frame_le {H : SimpleGraph (Fin N)} [DecidableRel H.Adj] {lists : Fin N → List ℕ}
    {T : List (Fin N)} {S : Finset (Fin N)} {f : ℕ} {D R : List ℕ} {s : State}
    (hX : SolveAt w N E c H lists T S f D R s) {s₁ : State} {a b : Fin N} {A B m : List (Fin N)}
    {P : H.Walk a b} {F : List ℕ} {P' : (H ⊔ pairGraph N F).Walk a b}
    (hd : SplitData w comp c H lists T s₁ a b A B m P F P')
    (hent : (s₁.arrs aEnt).length = (s.arrs aEnt).length) :
    (encAll frameArrs s₁).length ≤ 109 + 8 * N + 2 * E + N * f + 100 * (c * (N + E + 1)) := by
  have h1 := hd.length_frame_le
  have hM : H.edgeFinset.card ≤ E := by have := hX.budget; omega
  have h2 : c * (N + H.edgeFinset.card + 1) ≤ c * (N + E + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 := hX.ent
  omega

/-- **The driver solves an instance.** From the first round of an instance in memory
(`SolveAt`), a stretch of rounds leaves its answer (`DoneAt`). The proof is by strong induction
on the potential `k = 2|S| - |T| - 3`. -/
theorem drive (hcomp : CompSpec comp c c_w) (hext : ExtSpec comp ext c c_w)
    (hn : 4 * N + 4 < 2 ^ w) (hwE : wordSize c_w ((N + 1) * (E + N + 1)) ≤ w)
    (hcapE : 2 * E + N * (2 * N + 1) < 2 ^ w) :
    ∀ (k : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (lists : Fin N → List ℕ)
      (T : List (Fin N)) (S : Finset (Fin N)) (f : ℕ) (D R : List ℕ) (s : State),
      2 * S.card - T.length - 3 = k → SolveAt w N E c H lists T S f D R s →
      ∃ s' t, DoneAt w N E c H T k (S.card - T.length) f D R s s' t comp ext := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro H _ lists T S f D R s hk hX
  have hw2 : 2 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hM : H.edgeFinset.card ≤ E := by have := hX.budget; omega
  have hwH : wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w :=
    (wordSize_mono_right _ (Nat.mul_le_mul_left _ (by omega))).trans hwE
  have hlists : totalAdjEntries lists = 2 * H.edgeFinset.card :=
    totalAdjEntries_eq_two_mul_card_edgeFinset hX.adj.2
  have hneed0 := frame_le_need N E c k (S.card - T.length) f
  have hneed : drvNeed N E c k (S.card - T.length) f ≤ R.length := hk ▸ hX.need
  have hent := hX.ent
  have hNf : N * f ≤ N * (2 * N + 1) := Nat.mul_le_mul_left _ hX.hf
  have hcM : c * (N + H.edgeFinset.card + 1) ≤ c * (N + E + 1) := Nat.mul_le_mul_left _ (by omega)
  have hcap : totalAdjEntries lists + N * (2 * N + 1) < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, hout⟩ := solveRound_exec hcomp hn hwH hX.cycle D R s hX.n40 hX.adj hX.cyc
    hX.mode hX.heap hX.hp (by unfold drvFrame at hneed0; omega) hX.hDR hX.words (by omega) hcap
  have hr₁ := round_solve (ext := ext) hw2 hX.mode hex₁
  rcases hout with ⟨hdk, hm₁, hres⟩ | ⟨a, b, A, B, m, P, F, P', s₀, hd, hch, hm₁, hlow₁, hp₁, hh₁,
    hxw₀, hent₀, ht₁⟩
  · -- The round answers at once.
    have hl := time_leaf (N := N) (c := c) (Φ := k) (Ψ := S.card - T.length) (f := f) hM
    refine ⟨s₁, _, R, hr₁, hm₁, by rw [hdk.1]; exact hX.hp, by rw [hdk.2.1]; exact hX.heap, rfl,
      hdk.2.2, ?_⟩
    rw [hlists] at hres
    rcases hres with ⟨h0, hnc, ht⟩ | ⟨h1, hcr, ht⟩
    · exact Or.inl ⟨h0, hnc, by omega⟩
    · refine Or.inr ⟨h1, hcr, ?_⟩
      have : c * N * (N + H.edgeFinset.card + 1) ≤ c * N * (N + E + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
  · -- The round splits the instance: line 10.
    classical
    have henc := frame_le hX hd hent₀
    have hfl1 := length_frameOf s₀ A.length 1 D.length
    have hfl2 := length_frameOf s₀ A.length 2 D.length
    have hfr : (frameOf s₀ A.length 1 D.length).length ≤ drvFrame N E c + N * f := by
      unfold drvFrame; omega
    obtain ⟨hΦ, hΨ, hE₁, hE₂, hFm⟩ := hd.counts hX.edges hX.cycle
    have hF : F.length ≤ 2 * m.length + 3 := by omega
    have hp' : P'.support.length = m.length + 2 := by rw [hd.supp]; simp
    have hG₁ := card_edgeFinset_sub_le H F P'.support A 1
    have hG₂ := card_edgeFinset_sub_le H F P'.support A 2
    have hbud := hX.budget
    have hFN : F.length ≤ 2 * N + 1 := hd.lenF'
    have hNF : N * F.length ≤ N * (2 * N + 1) := Nat.mul_le_mul_left _ hFN
    have hent₀w : (s₀.arrs aEnt).length < 2 ^ w := by omega
    -- Subinstance `1`.
    have hn₁ := need_split (N := N) (E := E) (c := c) (f := f) (Φ := k) (Ψ := S.card - T.length)
      (Φ' := 2 * (childSet S (H ⊔ pairGraph N F) P'.support A 1).card - (subCycle a b A B m 1).length - 3)
      (Ψ' := (childSet S (H ⊔ pairGraph N F) P'.support A 1).card - (subCycle a b A B m 1).length)
      (m := m.length) (F := F.length) (by omega) (by omega) hF hfr
    have hc₁ : SolveAt w N E c (subGraph (H ⊔ pairGraph N F) P'.support A 1)
        (restrictListFamily (sideFin (H ⊔ pairGraph N F) P'.support A 1) (unionList lists F))
        (subCycle a b A B m 1) (childSet S (H ⊔ pairGraph N F) P'.support A 1) F.length
        (D ++ frameOf s₀ A.length 1 D.length) (R.drop (frameOf s₀ A.length 1 D.length).length)
        s₁ :=
      { n40 := hch.1
        adj := hch.2.1
        cyc := hch.2.2.2
        cycle := hd.childCycle 1 (.inl rfl)
        edges := hE₁
        budget := by omega
        mode := hm₁
        heap := hh₁
        hp := by rw [hp₁, List.length_append]
        need := by rw [List.length_drop]; omega
        hDR := by rw [List.length_append, List.length_drop]; have := hX.hDR; omega
        ent := by rw [hch.2.2.1, hlists]; omega
        hf := hFN
        words := fun x hx => hex₁.arrs_lt x (hX.words x hx)
        hwords := hex₁.arrs_lt aHeap hX.hwords }
    obtain ⟨s₂, t₂, R₂, hr₂, hm₂, hp₂, hh₂, hR₂, hlow₂, hout₂⟩ := ih _ (by omega) _ _ _ _ _ _ _ s₁
      rfl hc₁
    rw [List.length_drop] at hR₂
    have hp₂' : s₂.regs rHp = D.length + (frameOf s₀ A.length 1 D.length).length := by
      rw [hp₂, List.length_append]
    have hlt₂ : (D ++ frameOf s₀ A.length 1 D.length ++ R₂).length < 2 ^ w := by
      simp only [List.length_append]; have := hX.hDR; omega
    have hhw₂ : ∀ v ∈ s₂.arrs aHeap, v < 2 ^ w := hr₂.arrs_lt aHeap hc₁.hwords
    have h40₂ : s₂.regs 40 = N := by rw [hlow₂.1 40 le_rfl]; exact hch.1
    have hlow₁₂ : Low s s₂ := hlow₁.trans hlow₂
    rcases hout₂ with ⟨hres₂, hnc₁, ht₂⟩ | ⟨hres₂, hcr₂, ht₂⟩
    swap
    · -- Subinstance `1` is crossed: lift its crossing.
      obtain ⟨s₃, t₃, hex₃, ht₃, hcr₃, hp₃, hh₃, hres₃, hm₃, hlow₃⟩ := returnRound_lift hn hext hd
        hwH 1 (.inl rfl) D R₂ s₂ hh₂ hp₂' hlt₂ hhw₂ h40₂ hres₂ hent₀w hcr₂
      refine ⟨s₃, _, frameOf s₀ A.length 1 D.length ++ R₂,
        hr₁.trans (hr₂.trans (round_return hw2 hm₂ hex₃)), by rw [hm₃, hm₂], hp₃,
        by rw [hh₃, hh₂, List.append_assoc], by rw [List.length_append]; omega,
        hlow₁₂.trans hlow₃, Or.inr ⟨hres₃, hcr₃, ?_⟩⟩
      have := time_split (M := H.edgeFinset.card) (f := f) (Φ := k) (Ψ := S.card - T.length)
        (Φ₁ := 2 * (childSet S (H ⊔ pairGraph N F) P'.support A 1).card - (subCycle a b A B m 1).length - 3)
        (Φ₂ := 2 * (childSet S (H ⊔ pairGraph N F) P'.support A 2).card - (subCycle a b A B m 2).length - 3)
        (Ψ₁ := (childSet S (H ⊔ pairGraph N F) P'.support A 1).card - (subCycle a b A B m 1).length)
        (Ψ₂ := (childSet S (H ⊔ pairGraph N F) P'.support A 2).card - (subCycle a b A B m 2).length)
        (m := m.length) (F := F.length) (p := P'.support.length)
        (enc := (encAll frameArrs s₀).length) (c := c) hM (by omega) hF henc (by omega) (by omega)
      rw [hlists] at ht₁
      omega
    -- Subinstance `1` is not crossed: subinstance `2`.
    obtain ⟨s₃, t₃, hex₃, ht₃, hch₃, hm₃, hlow₃, hp₃, hh₃⟩ := returnRound_second hn ext hd D R₂ s₂
      hh₂ hp₂' hlt₂ hhw₂ h40₂ hres₂ hent₀w hcap
    have hn₂ := need_split (N := N) (E := E) (c := c) (f := f) (Φ := k) (Ψ := S.card - T.length)
      (Φ' := 2 * (childSet S (H ⊔ pairGraph N F) P'.support A 2).card - (subCycle a b A B m 2).length - 3)
      (Ψ' := (childSet S (H ⊔ pairGraph N F) P'.support A 2).card - (subCycle a b A B m 2).length)
      (m := m.length) (F := F.length) (by omega) (by omega) hF hfr
    have hc₂ : SolveAt w N E c (subGraph (H ⊔ pairGraph N F) P'.support A 2)
        (restrictListFamily (sideFin (H ⊔ pairGraph N F) P'.support A 2) (unionList lists F))
        (subCycle a b A B m 2) (childSet S (H ⊔ pairGraph N F) P'.support A 2) F.length
        (D ++ frameOf s₀ A.length 2 D.length) R₂ s₃ :=
      { n40 := hch₃.1
        adj := hch₃.2.1
        cyc := hch₃.2.2.2
        cycle := hd.childCycle 2 (.inr rfl)
        edges := hE₂
        budget := by omega
        mode := hm₃
        heap := hh₃
        hp := by rw [hp₃, List.length_append]
        need := by omega
        hDR := by rw [List.length_append]; have := hX.hDR; omega
        ent := by rw [hch₃.2.2.1, hlists]; omega
        hf := hFN
        words := fun x hx => hex₃.arrs_lt x (hr₂.arrs_lt x (hc₁.words x hx))
        hwords := hex₃.arrs_lt aHeap hhw₂ }
    obtain ⟨s₄, t₄, R₃, hr₄, hm₄, hp₄, hh₄, hR₃, hlow₄, hout₄⟩ := ih _ (by omega) _ _ _ _ _ _ _ s₃
      rfl hc₂
    have hp₄' : s₄.regs rHp = D.length + (frameOf s₀ A.length 2 D.length).length := by
      rw [hp₄, List.length_append]
    have hlt₄ : (D ++ frameOf s₀ A.length 2 D.length ++ R₃).length < 2 ^ w := by
      simp only [List.length_append]; have := hX.hDR; omega
    have hhw₄ : ∀ v ∈ s₄.arrs aHeap, v < 2 ^ w := hr₄.arrs_lt aHeap hc₂.hwords
    have h40₄ : s₄.regs 40 = N := by rw [hlow₄.1 40 le_rfl]; exact hch₃.1
    have hlow₁₄ : Low s s₄ := (hlow₁₂.trans hlow₃).trans hlow₄
    have hts := time_split (M := H.edgeFinset.card) (f := f) (Φ := k) (Ψ := S.card - T.length)
      (Φ₁ := 2 * (childSet S (H ⊔ pairGraph N F) P'.support A 1).card - (subCycle a b A B m 1).length - 3)
      (Φ₂ := 2 * (childSet S (H ⊔ pairGraph N F) P'.support A 2).card - (subCycle a b A B m 2).length - 3)
      (Ψ₁ := (childSet S (H ⊔ pairGraph N F) P'.support A 1).card - (subCycle a b A B m 1).length)
      (Ψ₂ := (childSet S (H ⊔ pairGraph N F) P'.support A 2).card - (subCycle a b A B m 2).length)
      (m := m.length) (F := F.length) (p := P'.support.length)
      (enc := (encAll frameArrs s₀).length) (c := c) hM (by omega) hF henc (by omega) (by omega)
    rw [hlists] at ht₁ ht₃
    rcases hout₄ with ⟨hres₄, hnc₂, ht₄⟩ | ⟨hres₄, hcr₄, ht₄⟩
    · -- Neither subinstance is crossed: pop the frame with the answer `False`.
      obtain ⟨s₅, t₅, hex₅, ht₅, hp₅, hh₅, hres₅, hm₅, hlow₅⟩ := returnRound_pop hw2 ext D R₃ s₀
        s₄ A.length hh₄ hp₄' hlt₄ hhw₄ hres₄
      refine ⟨s₅, _, frameOf s₀ A.length 2 D.length ++ R₃,
        hr₁.trans (hr₂.trans (round_return hw2 hm₂ hex₃ |>.trans (hr₄.trans
          (round_return hw2 hm₄ hex₅)))), by rw [hm₅, hm₄], hp₅,
        by rw [hh₅, hh₄, List.append_assoc], by rw [List.length_append]; omega,
        hlow₁₄.trans hlow₅, Or.inl ⟨hres₅, not_isCrossed_of_sub hd hnc₁ hnc₂, ?_⟩⟩
      omega
    · -- Subinstance `2` is crossed: lift its crossing.
      obtain ⟨s₅, t₅, hex₅, ht₅, hcr₅, hp₅, hh₅, hres₅, hm₅, hlow₅⟩ := returnRound_lift hn hext hd
        hwH 2 (.inr rfl) D R₃ s₄ hh₄ hp₄' hlt₄ hhw₄ h40₄ hres₄ hent₀w hcr₄
      refine ⟨s₅, _, frameOf s₀ A.length 2 D.length ++ R₃,
        hr₁.trans (hr₂.trans (round_return hw2 hm₂ hex₃ |>.trans (hr₄.trans
          (round_return hw2 hm₄ hex₅)))), by rw [hm₅, hm₄], hp₅,
        by rw [hh₅, hh₄, List.append_assoc], by rw [List.length_append]; omega,
        hlow₁₄.trans hlow₅, Or.inr ⟨hres₅, hcr₅, ?_⟩⟩
      omega

/-- **The driver loop.** Started on an instance in memory with an empty stack, the loop stops with
the answer for the instance in `rRes`, and a crossing in `aQ`, `aR` for the answer `True`. Its time
is the time of the instance and the last round, which finds the stack empty. -/
theorem driverLoop_exec (hcomp : CompSpec comp c c_w) (hext : ExtSpec comp ext c c_w)
    (hn : 4 * N + 4 < 2 ^ w) (hwE : wordSize c_w ((N + 1) * (E + N + 1)) ≤ w)
    (hcapE : 2 * E + N * (2 * N + 1) < 2 ^ w) {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
    {lists : Fin N → List ℕ} {T : List (Fin N)} {S : Finset (Fin N)} {f : ℕ} {R : List ℕ}
    {s : State} (hX : SolveAt w N E c H lists T S f [] R s) :
    ∃ s' t, Exec w (driverLoop comp ext) s s' t ∧ Low s s' ∧
      ((s'.regs rRes = 0 ∧ ¬ IsCrossed H T ∧
          t ≤ drvTime N E c (2 * S.card - T.length - 3) (S.card - T.length) f + 14) ∨
        (s'.regs rRes = 1 ∧ CrossingAt H T aQ aR s' ∧
          t ≤ drvTime N E c (2 * S.card - T.length - 3) (S.card - T.length) f +
            c * N * (N + E + 1) + 14)) := by
  have hw2 : 2 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, R', hr₁, hm₁, hp₁, -, -, hlow₁, hout⟩ :=
    drive hcomp hext hn hwE hcapE _ H lists T S f [] R s rfl hX
  obtain ⟨s₂, hex₂, hm₂, hdk₂, hreg₂, harr₂⟩ := returnRound_stop hw2 ext s₁ hp₁
  have hc : loopCond.eval w s₂ = some 0 := by
    have := lt_eval (reg_eval hm₂ (by omega)) (const_eval' (c := 2) (s := s₂) hw2) (by omega)
    simpa [loopCond] using this
  have hex := Exec.while_of_rounds (hr₁.trans (round_return hw2 hm₁ hex₂)) (.while_false hc)
  have hres : s₂.regs rRes = s₁.regs rRes := hreg₂ rRes (by decide)
  refine ⟨s₂, _, hex, hlow₁.trans hdk₂.2.2, ?_⟩
  rcases hout with ⟨h0, hnc, ht⟩ | ⟨h1, hcr, ht⟩
  · exact Or.inl ⟨by rw [hres, h0], hnc, by simp only [loopCond_cost]; omega⟩
  · refine Or.inr ⟨by rw [hres, h1], ?_, by simp only [loopCond_cost]; omega⟩
    unfold CrossingAt at hcr ⊢
    rw [harr₂]; exact hcr

end Drive

end GraphMinor.Compute.TwoPaths
