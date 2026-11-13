module

public import GraphMinor.Compute.CrossingFlowSetup

/-!
# Bit-Set Packing and Reverse Residual BFS for the Bounded-Flow Program

This file provides two components for the failure (cut-extraction) branch of `boundedFlowProg`:
1. `packBitSetProg`: packs any `0`/`1` bit-set array `IsBitSet Y a_Y s` into a duplicate-free list
   array `IsSetListAt a_out (Y : Set (Fin n)) s'` in `O(n)` time.
2. `VisQueueState` and `tryPushVis`: general visited-array + queue-history invariant and conditional
   push helper for BFS without a parent array.
3. `revResBfsProg`: runs the reverse residual BFS from `{outNode b | b ∈ sinkNeighbors S D z ow}`
   on `activeGraph G S z ow` and the path system `(used, pred, succ)`, establishing
   `IsRevResClosed G S D z k ow used pred succ rev_items` and
   `IsResVisArr N (a_base + 12) rev_items s'` in `O(N + totalAdjEntries lists_act)` time.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute

/-! ### Section 1: Packing a `Finset (Fin n)` Bit Array into `IsSetListAt` -/

/-- Ordered list of elements of `X : Finset (Fin n)` with index `< k`. -/
def prefixSetList {n : ℕ} (X : Finset (Fin n)) : (k : ℕ) → k ≤ n → List (Fin n)
  | 0, _ => []
  | k + 1, hk =>
      have hk' : k < n := Nat.lt_of_succ_le hk
      prefixSetList X k (Nat.le_of_lt hk') ++
        if (⟨k, hk'⟩ : Fin n) ∈ X then [⟨k, hk'⟩] else []

theorem mem_prefixSetList {n : ℕ} (X : Finset (Fin n)) (k : ℕ) (hk : k ≤ n) (u : Fin n) :
    u ∈ prefixSetList X k hk ↔ u ∈ X ∧ u.1 < k := by
  induction k with
  | zero =>
    simp [prefixSetList]
  | succ k ih =>
    have hk' : k < n := Nat.lt_of_succ_le hk
    simp only [prefixSetList, List.mem_append, ih (Nat.le_of_lt hk')]
    split_ifs with hmem
    · simp only [List.mem_singleton]
      constructor
      · rintro (⟨huX, hlt⟩ | rfl)
        · exact ⟨huX, by omega⟩
        · exact ⟨hmem, by simp⟩
      · rintro ⟨huX, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
        · exact Or.inl ⟨huX, hlt'⟩
        · exact Or.inr (Fin.ext heq)
    · simp only [List.not_mem_nil, or_false]
      constructor
      · rintro ⟨huX, hlt⟩
        exact ⟨huX, by omega⟩
      · rintro ⟨huX, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
        · exact ⟨huX, hlt'⟩
        · exfalso
          have : u = ⟨k, hk'⟩ := Fin.ext heq
          subst this
          exact hmem huX

theorem nodup_prefixSetList {n : ℕ} (X : Finset (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (prefixSetList X k hk).Nodup := by
  induction k with
  | zero =>
    simp [prefixSetList]
  | succ k ih =>
    have hk' : k < n := Nat.lt_of_succ_le hk
    simp only [prefixSetList]
    split_ifs with hmem
    · refine (ih (Nat.le_of_lt hk')).append (List.nodup_singleton _) ?_
      intro u hu hv
      rw [List.mem_singleton] at hv
      subst hv
      have hu_lt := ((mem_prefixSetList X k (Nat.le_of_lt hk') _).mp hu).2
      simp at hu_lt
    · simp [ih (Nat.le_of_lt hk')]

theorem length_prefixSetList {n : ℕ} (X : Finset (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (prefixSetList X k hk).length = ((bitSetList X).take k).sum := by
  induction k with
  | zero =>
    simp [prefixSetList]
  | succ k ih =>
    have hk' : k < n := Nat.lt_of_succ_le hk
    have hk_bl : k < (bitSetList X).length := by rw [length_bitSetList]; exact hk'
    rw [take_add_one_eq_append_getElem (bitSetList X) k hk_bl, List.sum_append,
      List.sum_singleton, ← ih (Nat.le_of_lt hk'), getElem_bitSetList X k hk']
    simp only [prefixSetList, List.length_append]
    split_ifs <;> simp

theorem length_prefixSetList_full {n : ℕ} (X : Finset (Fin n)) :
    (prefixSetList X n le_rfl).length = X.card := by
  rw [length_prefixSetList X n le_rfl]
  have htake : (bitSetList X).take n = bitSetList X := List.take_of_length_le (by simp)
  rw [htake, sum_bitSetList]

/-- Loop body for `packBitSetProg`: if `a_set[r_i] != 0`, write `r_i` to `a_out[r_pos]` and
increment `r_pos`. -/
def packBitSetBody (a_set a_out : Arr) (r_i r_pos r_val : Reg) : Cmd :=
  .seq (.assign r_val (.read a_set (.reg r_i)))
    (.ite (.reg r_val)
      (.seq (.write a_out (.reg r_pos) (.reg r_i))
        (.assign r_pos (.op .add (.reg r_pos) (.const 1))))
      .skip)

/-- Pack `IsBitSet X a_set s` into `a_out` as `IsSetListAt a_out (X : Set (Fin n)) s'`.
Uses `r_m` (`card`), `r_m + 1` (`r_i`), `r_m + 2` (`r_pos`), `r_m + 3` (`r_val`), and reads `n`
from `r_m + 12`. -/
def packBitSetProg (a_set a_out : Arr) (r_m : Reg) : Cmd :=
  .seq (cardBitSetProg a_set (.reg (r_m + 12)) r_m (r_m + 1))
    (.seq (.alloc a_out (.reg r_m))
      (.seq (.assign (r_m + 2) (.const 0))
        (.seq (.assign (r_m + 1) (.const 0))
          (forUp (r_m + 1) (.reg (r_m + 12))
            (packBitSetBody a_set a_out (r_m + 1) (r_m + 2) (r_m + 3))))))

theorem packBitSetLoop_exec {w n : ℕ} (X : Finset (Fin n)) (a_set a_out : ℕ) (r_m : ℕ)
    (hne_arr : a_set ≠ a_out)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hset : IsBitSet X a_set s)
    (hrn : s.regs (r_m + 12) = n)
    (hri : s.regs (r_m + 1) = k)
    (hrpos : s.regs (r_m + 2) = (prefixSetList X k (by omega)).length)
    (hout : s.arrs a_out =
      (prefixSetList X k (by omega)).map Fin.val ++
        List.replicate (X.card - (prefixSetList X k (by omega)).length) 0) :
    ∃ s' t,
      Exec w (forUp (r_m + 1) (.reg (r_m + 12))
        (packBitSetBody a_set a_out (r_m + 1) (r_m + 2) (r_m + 3))) s s' t ∧
      t ≤ 3 + 19 * rem ∧
      s'.arrs a_out = (prefixSetList X n le_rfl).map Fin.val ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg (r_m + 1)) (.reg (r_m + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    have hlen_full := length_prefixSetList_full X
    simp [hlen_full] at hout
    exact hout
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_le : k ≤ n := by omega
    have hk1_le : k + 1 ≤ n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_m + 1)) (.reg (r_m + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk_w, hn_w, hk_lt, hw]
    have hk_set : k < (s.arrs a_set).length := by rw [hset.1]; exact hk_lt
    let val := (s.arrs a_set)[k]'hk_set
    have hval_eq : val = if (⟨k, hk_lt⟩ : Fin n) ∈ X then 1 else 0 :=
      hset.getElem_eq_ite ⟨k, hk_lt⟩
    have hval_w : val < 2 ^ w := by split_ifs at hval_eq <;> omega
    let s₁ := s.setReg (r_m + 3) val
    have hex_rd : Exec w (.assign (r_m + 3) (.read a_set (.reg (r_m + 1)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hri, hk_w, hk_set, val, hval_w])
    let pos := (prefixSetList X k hk_le).length
    have hpos_step : (prefixSetList X (k + 1) hk1_le).length ≤ X.card := by
      rw [length_prefixSetList X (k + 1) hk1_le, sum_take_bitSetList X (k + 1) hk1_le]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hcard_le_n : X.card ≤ n := by
      have := Finset.card_le_univ X
      simpa using this
    have hbody : ∃ s₂ t_b,
        Exec w (packBitSetBody a_set a_out (r_m + 1) (r_m + 2) (r_m + 3)) s s₂ t_b ∧
        t_b ≤ 12 ∧
        s₂.regs (r_m + 1) = k ∧
        s₂.regs (r_m + 12) = n ∧
        s₂.regs (r_m + 2) = (prefixSetList X (k + 1) hk1_le).length ∧
        s₂.arrs a_out =
          (prefixSetList X (k + 1) hk1_le).map Fin.val ++
            List.replicate (X.card - (prefixSetList X (k + 1) hk1_le).length) 0 ∧
        (∀ a : ℕ, a ≠ a_out → s₂.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 → s₂.regs r = s.regs r) := by
      by_cases hmem : (⟨k, hk_lt⟩ : Fin n) ∈ X
      · have hval1 : val = 1 := by simp [hval_eq, hmem]
        have hcond_v : (Expr.reg (r_m + 3)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, checkWord, hval1, hw]
        have hlen_next : (prefixSetList X (k + 1) hk1_le).length = pos + 1 := by
          simp [prefixSetList, hmem, pos]
        have hpos_lt_card : pos < X.card := by omega
        have hpos_w : pos < 2 ^ w := by omega
        have hpos1_w : pos + 1 < 2 ^ w := by omega
        have hout_len : pos < (s₁.arrs a_out).length := by
          simp [s₁, hout, pos, hpos_lt_card]
        have hrpos₁ : s₁.regs (r_m + 2) = pos := by simp [s₁, State.setReg, hrpos, pos]
        have hri₁ : s₁.regs (r_m + 1) = k := by simp [s₁, State.setReg, hri]
        let s_w := s₁.writeArr a_out pos k
        have hex_wr : Exec w (.write a_out (.reg (r_m + 2)) (.reg (r_m + 1))) s₁ s_w 3 :=
          .write (by simp [Expr.eval, checkWord, hrpos₁, hpos_w])
            (by simp [Expr.eval, checkWord, hri₁, hk_w]) hout_len
        have hrpos_w : s_w.regs (r_m + 2) = pos := hrpos₁
        let s_p := s_w.setReg (r_m + 2) (pos + 1)
        have hex_inc_p : Exec w (.assign (r_m + 2) (.op .add (.reg (r_m + 2)) (.const 1)))
            s_w s_p 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos_w, hpos_w, hw, hpos1_w])
        have hex_ite : Exec w (.ite (.reg (r_m + 3))
            (.seq (.write a_out (.reg (r_m + 2)) (.reg (r_m + 1)))
              (.assign (r_m + 2) (.op .add (.reg (r_m + 2)) (.const 1))))
            .skip) s₁ s_p (1 + (3 + 4)) :=
          .ite_true hcond_v (by omega) (.seq hex_wr hex_inc_p)
        have hout_p : s_p.arrs a_out =
            (prefixSetList X (k + 1) hk1_le).map Fin.val ++
              List.replicate (X.card - (prefixSetList X (k + 1) hk1_le).length) 0 := by
          simp only [s_p, s_w, s₁, State.setReg_arrs, State.writeArr_arrs_self, hout]
          have hmap_len : ((prefixSetList X k hk_le).map Fin.val).length = pos := by
            simp [pos]
          rw [List.set_append_right _ _ (by omega)]
          have hsub0 : pos - ((prefixSetList X k hk_le).map Fin.val).length = 0 := by omega
          have hrep : X.card - pos = (X.card - (pos + 1)) + 1 := by omega
          rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
          simp [prefixSetList, hmem, List.append_assoc, pos]
        refine ⟨s_p, 3 + (1 + (3 + 4)), .seq hex_rd hex_ite, by omega,
          by simp [s_p, s_w, s₁, State.setReg, hri],
          by simp [s_p, s_w, s₁, State.setReg, hrn],
          by simp [s_p, hlen_next],
          hout_p,
          fun a ha => by simp [s_p, s_w, s₁, show (a : Arr) ≠ a_out from ha],
          fun r hr1 hr2 hr3 => by
            simp [s_p, s_w, s₁, State.setReg,
              show (r : Reg) ≠ r_m + 2 from hr2,
              show (r : Reg) ≠ r_m + 3 from hr3]⟩
      · have hval0 : val = 0 := by simp [hval_eq, hmem]
        have hcond_v : (Expr.reg (r_m + 3)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hval0, h0_w]
        have hex_ite : Exec w (.ite (.reg (r_m + 3))
            (.seq (.write a_out (.reg (r_m + 2)) (.reg (r_m + 1)))
              (.assign (r_m + 2) (.op .add (.reg (r_m + 2)) (.const 1))))
            .skip) s₁ s₁ 2 :=
          .ite_false hcond_v (.skip s₁)
        have hpref_eq : prefixSetList X (k + 1) hk1_le = prefixSetList X k hk_le := by
          simp [prefixSetList, hmem]
        refine ⟨s₁, 3 + 2, .seq hex_rd hex_ite, by omega,
          by simp [s₁, State.setReg, hri],
          by simp [s₁, State.setReg, hrn],
          by simp [s₁, State.setReg, hpref_eq, hrpos],
          by simp [s₁, hpref_eq, hout],
          fun _ _ => rfl,
          fun r _ _ hr3 => by simp [s₁, State.setReg, show (r : Reg) ≠ r_m + 3 from hr3]⟩
    rcases hbody with
      ⟨s₂, t_b, hex_b, ht_b, hri₂, hrn₂, hrpos₂, hout₂, harr₂, hreg₂⟩
    have hinc : (Expr.op .add (.reg (r_m + 1)) (.const 1)).eval w s₂ = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s₃ := s₂.setReg (r_m + 1) (k + 1)
    have hex_inc : Exec w (.assign (r_m + 1) (.op .add (.reg (r_m + 1)) (.const 1)))
        s₂ s₃ 4 := .assign hinc
    have hset₃ : IsBitSet X a_set s₃ :=
      hset.of_arr_eq (by simp [s₃, harr₂ a_set hne_arr])
    rcases ih (k + 1) (by omega) (s := s₃) hset₃
        (by simp [s₃, State.setReg, hrn₂])
        (by simp [s₃])
        (by simp [s₃, State.setReg, hrpos₂])
        (by simp [s₃, hout₂]) with
      ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + (t_b + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex₄,
      by omega, hout₄,
      fun a ha => by rw [harr₄ a ha]; exact harr₂ a ha,
      fun r hr1 hr2 hr3 => by
        rw [hreg₄ r hr1 hr2 hr3]
        simp [s₃, State.setReg, show (r : Reg) ≠ r_m + 1 from hr1, hreg₂ r hr1 hr2 hr3]⟩

theorem packBitSetProg_exec {w n : ℕ} (X : Finset (Fin n)) (a_set a_out : ℕ) (r_m : ℕ)
    (hne_arr : a_set ≠ a_out)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hset : IsBitSet X a_set s)
    (hrn : s.regs (r_m + 12) = n) :
    ∃ s' t,
      Exec w (packBitSetProg a_set a_out r_m) s s' t ∧
      t ≤ 15 + 32 * n ∧
      IsSetListAt a_out (X : Set (Fin n)) s' ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_m → r ≠ r_m + 1 → r ≠ r_m + 2 → r ≠ r_m + 3 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hcard_le_n : X.card ≤ n := by
    have := Finset.card_le_univ X
    simpa using this
  have hcard_w : X.card < 2 ^ w := by omega
  -- 1. cardBitSetProg
  rcases cardBitSetProg_exec X a_set (r_m + 12) r_m (r_m + 1)
      (by omega) (by omega) (by omega) hw hn_w hset hrn with
    ⟨s₁, t₁, hex₁, ht₁, hrcard₁, harr₁, hreg₁⟩
  -- 2. .alloc a_out (.reg r_m)
  let s₂ := s₁.setArr a_out (List.replicate X.card 0)
  have hex₂ : Exec w (.alloc a_out (.reg r_m)) s₁ s₂ (1 + X.card) :=
    .alloc (by simp [Expr.eval, checkWord, hrcard₁, hcard_w])
  -- 3. .assign (r_m + 2) 0, .assign (r_m + 1) 0
  let s₃ := s₂.setReg (r_m + 2) 0
  have hex₃ : Exec w (.assign (r_m + 2) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_m + 1) 0
  have hex₄ : Exec w (.assign (r_m + 1) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hset₄ : IsBitSet X a_set s₄ :=
    hset.of_arr_eq (by simp [s₄, s₃, s₂, show (a_set : Arr) ≠ a_out from hne_arr, harr₁ a_set])
  have hrn₄ : s₄.regs (r_m + 12) = n := by
    simp [s₄, s₃, s₂, State.setReg, hreg₁ (r_m + 12) (by omega) (by omega), hrn]
  rcases packBitSetLoop_exec X a_set a_out r_m hne_arr hw hn_w n 0 (by omega)
      (s := s₄) hset₄ hrn₄ (by simp [s₄])
      (by simp [s₄, s₃, prefixSetList])
      (by simp [s₄, s₃, s₂, prefixSetList]) with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, harr₅, hreg₅⟩
  refine ⟨s₅, t₁ + ((1 + X.card) + (2 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    ⟨prefixSetList X n le_rfl, nodup_prefixSetList X n le_rfl,
      fun u => by
        rw [mem_prefixSetList]
        exact ⟨fun h => h.1, fun h => ⟨h, u.2⟩⟩,
      hout₅⟩,
    fun a ha => by
      rw [harr₅ a ha]
      simp [s₄, s₃, s₂, show (a : Arr) ≠ a_out from ha, harr₁ a],
    fun r hr0 hr1 hr2 hr3 => by
      rw [hreg₅ r hr1 hr2 hr3]
      simp [s₄, s₃, s₂, State.setReg,
        show (r : Reg) ≠ r_m + 1 from hr1,
        show (r : Reg) ≠ r_m + 2 from hr2,
        hreg₁ r hr0 hr1]⟩

/-! ### Section 2: General Visited-Queue State and `tryPushVis` -/

/-- State invariant for a BFS queue `a_q` of capacity `cap` and visited bit array `a_vis` of
length `cap` (without a parent array). -/
def VisQueueState (cap : ℕ) (a_vis a_q : ℕ) (r_head r_tail : ℕ)
    (items : List ℕ) (headIdx : ℕ) (s : State) : Prop :=
  IsQueueHistory a_q r_head r_tail cap items headIdx s ∧
  items.Nodup ∧
  (∀ x ∈ items, x < cap) ∧
  ∃ (hvis : (s.arrs a_vis).length = cap),
    ∀ x : ℕ, (hx : x < cap) →
      (((s.arrs a_vis)[x]'(by rw [hvis]; exact hx) ≠ 0 ↔ x ∈ items) ∧
        (s.arrs a_vis)[x]'(by rw [hvis]; exact hx) ≤ 1)

theorem VisQueueState.of_eq {cap : ℕ} {a_vis a_q : ℕ} {r_head r_tail : ℕ}
    {items : List ℕ} {headIdx : ℕ} {s s' : State}
    (h : VisQueueState cap a_vis a_q r_head r_tail items headIdx s)
    (hvis_eq : s'.arrs a_vis = s.arrs a_vis)
    (hq_eq : s'.arrs a_q = s.arrs a_q)
    (hhead_eq : s'.regs r_head = s.regs r_head)
    (htail_eq : s'.regs r_tail = s.regs r_tail) :
    VisQueueState cap a_vis a_q r_head r_tail items headIdx s' := by
  rcases h with ⟨hq, hno, hlt, hvis_len, hvis_iff⟩
  exact ⟨hq.of_eq hq_eq hhead_eq htail_eq, hno, hlt,
    by rw [hvis_eq]; exact hvis_len,
    fun x hx => by simp only [hvis_eq]; exact hvis_iff x hx⟩

theorem VisQueueState.to_isResVisArr {N : ℕ} {a_vis a_q r_head r_tail : ℕ}
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (h : VisQueueState (2 * N) a_vis a_q r_head r_tail items headIdx s) :
    IsResVisArr N a_vis items s := by
  rcases h with ⟨_, _, _, hvis_len, hvis_iff⟩
  exact ⟨hvis_len, hvis_iff⟩

/-- If `a_vis[r_node] == 0`, mark `a_vis[r_node] := 1` and push `r_node` onto `a_q`. -/
def tryPushVis (a_vis a_q : Arr) (r_tail r_vis r_node : Reg) : Cmd :=
  .seq (.assign r_vis (.read a_vis (.reg r_node)))
    (.ite (.reg r_vis)
      .skip
      (.seq (.write a_vis (.reg r_node) (.const 1))
        (queuePush a_q r_tail (.reg r_node))))

theorem tryPushVis_exec {w cap : ℕ} (a_vis a_q : ℕ) (r_head r_tail r_vis r_node : ℕ)
    (hne_vq : a_vis ≠ a_q)
    (hne_ht : r_head ≠ r_tail) (hne_hv : r_head ≠ r_vis)
    (hne_tv : r_tail ≠ r_vis) (hne_vn : r_vis ≠ r_node)
    (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w)
    {items : List ℕ} {headIdx y : ℕ} {s : State}
    (hqstate : VisQueueState cap a_vis a_q r_head r_tail items headIdx s)
    (hr_node : s.regs r_node = y) (hy_lt : y < cap) :
    ∃ s' t extra,
      Exec w (tryPushVis a_vis a_q r_tail r_vis r_node) s s' t ∧
      t ≤ 14 ∧
      VisQueueState cap a_vis a_q r_head r_tail (items ++ extra) headIdx s' ∧
      (∀ z, z ∈ extra → z = y) ∧
      (∀ z, z ∈ items ++ extra ↔ z ∈ items ∨ z = y) ∧
      (∀ a : ℕ, a ≠ a_vis → a ≠ a_q → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_tail → r ≠ r_vis → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hy_w : y < 2 ^ w := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := hne_vq
  have hne_hv' : (r_head : Reg) ≠ r_vis := hne_hv
  have hne_tv' : (r_tail : Reg) ≠ r_vis := hne_tv
  have hne_vn' : (r_vis : Reg) ≠ r_node := hne_vn
  rcases hqstate with ⟨hq, hnodup, hlt_items, hvis_len, hvis_iff⟩
  have hy_vis : y < (s.arrs a_vis).length := by rw [hvis_len]; exact hy_lt
  let vis_y := (s.arrs a_vis)[y]'hy_vis
  have hvy_le1 : vis_y ≤ 1 := (hvis_iff y hy_lt).2
  have hvy_w : vis_y < 2 ^ w := by omega
  let s₁ := s.setReg r_vis vis_y
  have hex_rd : Exec w (.assign r_vis (.read a_vis (.reg r_node))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr_node, hy_w, hy_vis, vis_y, hvy_w])
  by_cases hy_mem : y ∈ items
  · have hvy_ne0 : vis_y ≠ 0 := (hvis_iff y hy_lt).1.mpr hy_mem
    have hcond : (Expr.reg r_vis).eval w s₁ = some vis_y := by
      simp [s₁, Expr.eval, checkWord, hvy_w]
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.write a_vis (.reg r_node) (.const 1))
          (queuePush a_q r_tail (.reg r_node)))) s₁ s₁ 2 :=
      .ite_true hcond hvy_ne0 (.skip s₁)
    refine ⟨s₁, 3 + 2, [], .seq hex_rd hex_ite, by omega, ?_,
      fun _ h => by simp at h, ?_, fun _ _ _ => rfl, ?_⟩
    · simp only [List.append_nil]
      exact ⟨hq.of_eq rfl (by simp [s₁, State.setReg, hne_hv']) (by simp [s₁, State.setReg, hne_tv']),
        hnodup, hlt_items, hvis_len, hvis_iff⟩
    · intro z
      simp only [List.append_nil, iff_self_or]
      rintro rfl
      exact hy_mem
    · intro r _ hr_vis
      simp [s₁, State.setReg, show (r : Reg) ≠ r_vis from hr_vis]
  · have hvy_eq0 : vis_y = 0 := by
      by_contra hne
      exact hy_mem ((hvis_iff y hy_lt).1.mp hne)
    have hcond : (Expr.reg r_vis).eval w s₁ = some 0 := by
      simp [s₁, Expr.eval, checkWord, hvy_eq0, h0_w]
    have hrn₁ : s₁.regs r_node = y := by simp [s₁, State.setReg, hne_vn'.symm, hr_node]
    let s₂ := s₁.writeArr a_vis y 1
    have hex_wvis : Exec w (.write a_vis (.reg r_node) (.const 1)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hrn₁, hy_w])
        (by simp [Expr.eval, checkWord, hw]) (by simp [s₁, hy_vis])
    have hq₂ : IsQueueHistory a_q r_head r_tail cap items headIdx s₂ :=
      hq.of_eq (by simp [s₂, s₁, hne_vq'.symm])
        (by simp [s₂, s₁, State.setReg, hne_hv'])
        (by simp [s₂, s₁, State.setReg, hne_tv'])
    have hitems_lt_cap : items.length < cap :=
      length_lt_of_nodup_lt_not_mem hnodup hlt_items hy_lt hy_mem
    rcases Triple.queuePush_spec a_q r_head r_tail (.reg r_node) cap items headIdx y
        hne_ht hw hcap_w hitems_lt_cap s₂
        ⟨hq₂, by simp [s₂, Expr.eval, checkWord, hrn₁, hy_w]⟩ with
      ⟨s₃, t_push, hex_push, ht_push, hq₃⟩
    dsimp [Expr.cost] at ht_push
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.write a_vis (.reg r_node) (.const 1))
          (queuePush a_q r_tail (.reg r_node)))) s₁ s₃ (1 + (3 + t_push)) :=
      .ite_false hcond (.seq hex_wvis hex_push)
    have hnot_push_vis : (a_vis : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_vq']
    have hvis₃ : s₃.arrs a_vis = (s.arrs a_vis).set y 1 := by
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_vis]
      simp [s₂, s₁]
    refine ⟨s₃, 3 + (1 + (3 + t_push)), [y], .seq hex_rd hex_ite, by omega,
      ?_, fun z hz => List.mem_singleton.mp hz,
      fun z => by simp [List.mem_append], ?_, ?_⟩
    · refine ⟨hq₃, hnodup.append (List.nodup_singleton y) ?_,
        fun z hz => by
          rw [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          · exact hlt_items z hz
          · exact hy_lt,
        by simp [hvis₃, hvis_len],
        fun z hz => ?_⟩
      · intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hy_mem ha
      · simp only [hvis₃, List.mem_append, List.mem_singleton]
        by_cases hzy : z = y
        · subst hzy
          rw [List.getElem_set_self (by simp [hvis_len, hz])]
          exact ⟨by simp, le_rfl⟩
        · rw [List.getElem_set_ne (Ne.symm hzy)]
          rcases hvis_iff z hz with ⟨hiff, hle⟩
          exact ⟨by simp [hiff, hzy], hle⟩
    · intro a ha_vis ha_q
      have ha_q' : (a : Arr) ≠ a_q := ha_q
      have hnot_a : (a : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
        simp [queuePush, Cmd.writtenArrs, ha_q']
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_a]
      simp [s₂, s₁, show (a : Arr) ≠ a_vis from ha_vis]
    · intro r hr_tail hr_vis
      have hr_tail' : (r : Reg) ≠ r_tail := hr_tail
      have hnot_r : (r : Reg) ∉ (queuePush a_q r_tail (.reg r_node)).writtenRegs := by
        simp [queuePush, Cmd.writtenRegs, hr_tail']
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_r]
      simp [s₂, s₁, State.setReg, show (r : Reg) ≠ r_vis from hr_vis]

/-! ### Section 3: Reverse Residual BFS (`revResBfsProg`) -/

/-- Soundness invariant on `rev_items` during the reverse residual BFS. -/
structure RevSoundInv {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (rev_items : List ℕ) : Prop where
  in_active : ∀ v : Fin N, v.val ∈ rev_items → v ∈ activeVerts S z ow
  out_active : ∀ w : Fin N, w.val + N ∈ rev_items → w ∈ activeVerts S z ow
  in_sound : ∀ v : Fin N, v.val ∈ rev_items →
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some v, false) (none, false)
  out_sound : ∀ w : Fin N, w.val + N ∈ rev_items →
    ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some w, true) (none, false)

theorem RevSoundInv.empty {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ) :
    RevSoundInv G S D z k ow used pred succ [] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h,
   fun _ h => by simp at h, fun _ h => by simp at h⟩

theorem RevSoundInv.append_in {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {rev_items extra : List ℕ} {v₀ : Fin N}
    (h : RevSoundInv G S D z k ow used pred succ rev_items)
    (hex : ∀ x ∈ extra, x = v₀.val)
    (hv_act : v₀ ∈ activeVerts S z ow)
    (hv_sound : ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some v₀, false) (none, false)) :
    RevSoundInv G S D z k ow used pred succ (rev_items ++ extra) := by
  refine ⟨fun v hv => ?_, fun w hw => ?_, fun v hv => ?_, fun w hw => ?_⟩
  · rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact h.in_active v hv
    · have hveq : v = v₀ := Fin.ext (hex v.val hv)
      rw [hveq]; exact hv_act
  · rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.out_active w hw
    · have := hex (w.val + N) hw
      have := v₀.2
      omega
  · rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact h.in_sound v hv
    · have hveq : v = v₀ := Fin.ext (hex v.val hv)
      rw [hveq]; exact hv_sound
  · rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.out_sound w hw
    · have := hex (w.val + N) hw
      have := v₀.2
      omega

theorem RevSoundInv.append_out {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {rev_items extra : List ℕ} {w₀ : Fin N}
    (h : RevSoundInv G S D z k ow used pred succ rev_items)
    (hex : ∀ x ∈ extra, x = w₀.val + N)
    (hw_act : w₀ ∈ activeVerts S z ow)
    (hw_sound : ResReach (splitCap (apex G D) (flowVerts S ow) (some z) none k)
      (pathSystemFlow z used pred succ) (some w₀, true) (none, false)) :
    RevSoundInv G S D z k ow used pred succ (rev_items ++ extra) := by
  refine ⟨fun v hv => ?_, fun w hw => ?_, fun v hv => ?_, fun w hw => ?_⟩
  · rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact h.in_active v hv
    · have := hex v.val hv
      have := v.2
      omega
  · rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.out_active w hw
    · have hweq : w = w₀ := Fin.ext (by have := hex (w.val + N) hw; omega)
      rw [hweq]; exact hw_act
  · rw [List.mem_append] at hv
    rcases hv with hv | hv
    · exact h.in_sound v hv
    · have := hex v.val hv
      have := v.2
      omega
  · rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact h.out_sound w hw
    · have hweq : w = w₀ := Fin.ext (by have := hex (w.val + N) hw; omega)
      rw [hweq]; exact hw_sound

/-- Pop-closure invariant for the first `headIdx` items of `rev_items` in the reverse residual BFS. -/
def IsRevPopClosed {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (z : Fin N) (ow : ℕ) (used succ : Fin N → ℕ)
    (rev_items : List ℕ) (headIdx : ℕ) : Prop :=
  ∀ i : ℕ, i < headIdx → (hi : i < rev_items.length) →
    (∀ v : Fin N, rev_items[i]'hi = v.val →
      (used v ≠ 0 → v.val + N ∈ rev_items) ∧
      (∀ u : Fin N, (activeGraph G S z ow).Adj v u → u.val + N ∈ rev_items)) ∧
    (∀ w : Fin N, rev_items[i]'hi = w.val + N →
      (used w = 0 → w.val ∈ rev_items) ∧
      (∀ u : Fin N, used w ≠ 0 → succ w = u.val → u.val ∈ rev_items))

theorem IsRevPopClosed.zero {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (z : Fin N) (ow : ℕ) (used succ : Fin N → ℕ) (rev_items : List ℕ) :
    IsRevPopClosed G S z ow used succ rev_items 0 :=
  fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem IsRevPopClosed.step {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {z : Fin N} {ow : ℕ} {used succ : Fin N → ℕ} {rev_items extra : List ℕ} {headIdx : ℕ}
    (hclosed : IsRevPopClosed G S z ow used succ rev_items headIdx)
    (hhead : headIdx < rev_items.length)
    (hin : ∀ v : Fin N, rev_items[headIdx]'hhead = v.val →
      (used v ≠ 0 → v.val + N ∈ rev_items ++ extra) ∧
      (∀ u : Fin N, (activeGraph G S z ow).Adj v u → u.val + N ∈ rev_items ++ extra))
    (hout : ∀ w : Fin N, rev_items[headIdx]'hhead = w.val + N →
      (used w = 0 → w.val ∈ rev_items ++ extra) ∧
      (∀ u : Fin N, used w ≠ 0 → succ w = u.val → u.val ∈ rev_items ++ extra)) :
    IsRevPopClosed G S z ow used succ (rev_items ++ extra) (headIdx + 1) := by
  intro i hi hi_len
  have hi_it : i < rev_items.length := by omega
  have hget : (rev_items ++ extra)[i]'hi_len = rev_items[i]'hi_it :=
    List.getElem_append_left hi_it
  rw [hget]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | rfl
  · rcases hclosed i hi_lt hi_it with ⟨h1, h2⟩
    refine ⟨fun v hv => ?_, fun w hw => ?_⟩
    · rcases h1 v hv with ⟨hu, hadj⟩
      exact ⟨fun h => List.mem_append_left _ (hu h),
        fun u h => List.mem_append_left _ (hadj u h)⟩
    · rcases h2 w hw with ⟨hu0, hsucc⟩
      exact ⟨fun h => List.mem_append_left _ (hu0 h),
        fun u h1' h2' => List.mem_append_left _ (hsucc u h1' h2')⟩
  · exact ⟨hin, hout⟩

theorem IsRevPopClosed.to_isRevResClosed {N : ℕ} {G : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} {z : Fin N} {k ow : ℕ} {used pred succ : Fin N → ℕ}
    {rev_items : List ℕ}
    (hsound : RevSoundInv G S D z k ow used pred succ rev_items)
    (hseed : ∀ b ∈ sinkNeighbors S D z ow, b.val + N ∈ rev_items)
    (hclosed : IsRevPopClosed G S z ow used succ rev_items rev_items.length) :
    IsRevResClosed G S D z k ow used pred succ rev_items := by
  refine ⟨hsound.in_active, hsound.out_active, hsound.in_sound, hsound.out_sound,
    hseed, ?_, ?_, ?_, ?_⟩
  · intro v hv hused
    have hidx : rev_items.idxOf v.val < rev_items.length := List.idxOf_lt_length_of_mem hv
    have hget : rev_items[rev_items.idxOf v.val]'hidx = v.val := List.getElem_idxOf hidx
    exact ((hclosed _ hidx hidx).1 v hget).1 hused
  · intro v u hv hadj
    have hidx : rev_items.idxOf v.val < rev_items.length := List.idxOf_lt_length_of_mem hv
    have hget : rev_items[rev_items.idxOf v.val]'hidx = v.val := List.getElem_idxOf hidx
    exact ((hclosed _ hidx hidx).1 v hget).2 u hadj
  · intro w hw hunused
    have hidx : rev_items.idxOf (w.val + N) < rev_items.length := List.idxOf_lt_length_of_mem hw
    have hget : rev_items[rev_items.idxOf (w.val + N)]'hidx = w.val + N := List.getElem_idxOf hidx
    exact ((hclosed _ hidx hidx).2 w hget).1 hunused
  · intro w u hw hused hsucc
    have hidx : rev_items.idxOf (w.val + N) < rev_items.length := List.idxOf_lt_length_of_mem hw
    have hget : rev_items[rev_items.idxOf (w.val + N)]'hidx = w.val + N := List.getElem_idxOf hidx
    exact ((hclosed _ hidx hidx).2 w hget).2 u hused hsucc

/-- Potential weight of a split node `z : Fin (2 * n)` in the reverse residual BFS. -/
def revNodeWeight {n : ℕ} (lists : Fin n → List ℕ) (z : Fin (2 * n)) : ℕ :=
  if h : z.1 < n then 45 + 29 * (lists ⟨z.1, h⟩).length else 45

theorem sum_revNodeWeight_univ {n : ℕ} (lists : Fin n → List ℕ) :
    (∑ z : Fin (2 * n), revNodeWeight lists z) = 90 * n + 29 * totalAdjEntries lists := by
  have hdisj : Disjoint (Finset.univ.map (inEmb n)) (Finset.univ.map (outEmb n)) := by
    rw [Finset.disjoint_left]
    intro z hzin hzout
    rcases Finset.mem_map.mp hzin with ⟨u, _, rfl⟩
    rcases Finset.mem_map.mp hzout with ⟨v, _, heq⟩
    have hval := congrArg Fin.val heq
    simp only [inEmb_val, outEmb_val] at hval
    have := u.2
    omega
  have hunion : (Finset.univ : Finset (Fin (2 * n))) =
      Finset.univ.map (inEmb n) ∪ Finset.univ.map (outEmb n) := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, true_and, true_iff]
    by_cases hz : z.1 < n
    · exact Or.inl ⟨⟨z.1, hz⟩, Fin.ext rfl⟩
    · exact Or.inr ⟨⟨z.1 - n, by omega⟩, Fin.ext (by simp [outEmb_val]; omega)⟩
  rw [hunion, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
  have hsum_in : (∑ u : Fin n, revNodeWeight lists (inEmb n u)) =
      45 * n + 29 * totalAdjEntries lists := by
    have hcongr : ∀ u : Fin n, revNodeWeight lists (inEmb n u) = 45 + 29 * (lists u).length := by
      intro u
      simp [revNodeWeight]
    simp only [hcongr]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_comm n 45, ← Finset.mul_sum, totalAdjEntries]
  have hsum_out : (∑ u : Fin n, revNodeWeight lists (outEmb n u)) = 45 * n := by
    have hcongr : ∀ u : Fin n, revNodeWeight lists (outEmb n u) = 45 := by
      intro u
      simp [revNodeWeight]
    simp [hcongr, mul_comm]
  omega

theorem sum_revNodeWeight_pop {n : ℕ} (lists : Fin n → List ℕ)
    {items extra : List ℕ} {headIdx : ℕ}
    (hno : items.Nodup) (hhead : headIdx < items.length) (hx : items[headIdx] < 2 * n) :
    revNodeWeight lists ⟨items[headIdx], hx⟩ +
      (∑ z ∈ Finset.univ \ listFinset (2 * n) ((items ++ extra).take (headIdx + 1)),
        revNodeWeight lists z) =
      ∑ z ∈ Finset.univ \ listFinset (2 * n) (items.take headIdx), revNodeWeight lists z := by
  rw [sdiff_listFinset_take_succ_append Finset.univ hhead hx]
  have hmem : (⟨items[headIdx], hx⟩ : Fin (2 * n)) ∈
      Finset.univ \ listFinset (2 * n) (items.take headIdx) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, not_mem_listFinset_take_of_nodup hno hhead hx⟩
  exact Finset.add_sum_erase _ _ hmem

theorem sum_revNodeWeight_le_univ {n : ℕ} (lists : Fin n → List ℕ) (S : Finset (Fin (2 * n))) :
    (∑ z ∈ S, revNodeWeight lists z) ≤ 90 * n + 29 * totalAdjEntries lists := by
  calc
    (∑ z ∈ S, revNodeWeight lists z) ≤ ∑ z : Fin (2 * n), revNodeWeight lists z :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = 90 * n + 29 * totalAdjEntries lists := sum_revNodeWeight_univ lists

/-- Seed the reverse residual BFS queue with `b + N` for all `b ∈ B` (`(a_base + 2)[b] != 0`). -/
def revInitSourcesBody (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.assign (r_m + 7) (.read (a_base + 2) (.reg (r_m + 3))))
    (.ite (.reg (r_m + 7))
      (.seq (.assign (r_m + 6) (.op .add (.reg (r_m + 3)) (.reg (r_m + 12))))
        (tryPushVis (a_base + 12) (a_base + 13) (r_m + 1) (r_m + 7) (r_m + 6)))
      .skip)

/-- Allocate `a_rvis = a_base + 12` and `a_rq = a_base + 13` of length `2 * N` (`r_m + 13`),
reset queue pointers `r_m, r_m + 1`, and seed `{b + N | b ∈ sinkNeighbors S D z ow}`. -/
def revInitSourcesProg (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (.alloc (a_base + 12) (.reg (r_m + 13)))
    (.seq (.alloc (a_base + 13) (.reg (r_m + 13)))
      (.seq (.assign r_m (.const 0))
        (.seq (.assign (r_m + 1) (.const 0))
          (.seq (.assign (r_m + 3) (.const 0))
            (forUp (r_m + 3) (.reg (r_m + 12)) (revInitSourcesBody a_base r_m))))))

theorem revInitSourcesLoop_exec {w N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (a_base r_m : ℕ)
    (hk : 1 ≤ k) (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w)
    (rem idx : ℕ) (hrem : idx + rem = N) {rev_items : List ℕ} {s : State}
    (hconst : ConstRegs N k r_m s)
    (hB_bit : IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s)
    (hsys : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s)
    (hqstate : VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) rev_items 0 s)
    (hsound : RevSoundInv G S D z k ow used pred succ rev_items)
    (hinit_prev : ∀ b ∈ sinkNeighbors S D z ow, b.val < idx → b.val + N ∈ rev_items)
    (hru : s.regs (r_m + 3) = idx) :
    ∃ s' t rev_items',
      Exec w (forUp (r_m + 3) (.reg (r_m + 12)) (revInitSourcesBody a_base r_m)) s s' t ∧
      t ≤ 3 + 30 * rem ∧
      ConstRegs N k r_m s' ∧
      PathSystemState (activeGraph G S z ow)
        (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s' ∧
      VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) rev_items' 0 s' ∧
      RevSoundInv G S D z k ow used pred succ rev_items' ∧
      (∀ b ∈ sinkNeighbors S D z ow, b.val + N ∈ rev_items') ∧
      (∀ a < a_base + 12, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hN_w : N < 2 ^ w := by omega
  induction rem generalizing idx rev_items s with
  | zero =>
    have hru_n : s.regs (r_m + 3) = N := by omega
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_n, hconst.1, hN_w, h0_w]
    exact ⟨s, 3, rev_items, .while_false hcond, by omega, hconst, hsys, hqstate, hsound,
      fun b hb => hinit_prev b hb (by have := b.2; omega), fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hidx_lt : idx < N := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_m + 3)) (.reg (r_m + 12))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hconst.1, hidx_w, hN_w, hidx_lt, hw]
    have hB_len : (s.arrs (a_base + 2)).length = N := hB_bit.1
    have hidx_B : idx < (s.arrs (a_base + 2)).length := by rw [hB_len]; exact hidx_lt
    let valB := (s.arrs (a_base + 2))[idx]'hidx_B
    have hvalB_eq : valB = if (⟨idx, hidx_lt⟩ : Fin N) ∈ sinkNeighbors S D z ow then 1 else 0 :=
      hB_bit.getElem_eq_ite ⟨idx, hidx_lt⟩
    have hvalB_w : valB < 2 ^ w := by split_ifs at hvalB_eq <;> omega
    let s₁ := s.setReg (r_m + 7) valB
    have hex_rdB : Exec w (.assign (r_m + 7) (.read (a_base + 2) (.reg (r_m + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hidx_w, hidx_B, valB, hvalB_w])
    have hbody_step : ∃ s_b t_b extra,
        Exec w (revInitSourcesBody a_base r_m) s s_b t_b ∧
        t_b ≤ 22 ∧
        ConstRegs N k r_m s_b ∧
        PathSystemState (activeGraph G S z ow)
          (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s_b ∧
        VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) (rev_items ++ extra) 0 s_b ∧
        RevSoundInv G S D z k ow used pred succ (rev_items ++ extra) ∧
        (∀ z_it, z_it ∈ rev_items ++ extra ↔
          z_it ∈ rev_items ∨ ((⟨idx, hidx_lt⟩ : Fin N) ∈ sinkNeighbors S D z ow ∧ z_it = idx + N)) ∧
        s_b.regs (r_m + 3) = idx ∧
        (∀ a < a_base + 12, s_b.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s_b.regs r = s.regs r) := by
      by_cases hmemB : (⟨idx, hidx_lt⟩ : Fin N) ∈ sinkNeighbors S D z ow
      · have hvalB_1 : valB = 1 := by simp [hvalB_eq, hmemB]
        have hcondB : (Expr.reg (r_m + 7)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, checkWord, hvalB_1, hw]
        have hidxN_w : idx + N < 2 ^ w := by omega
        have hru₁ : s₁.regs (r_m + 3) = idx := by simp [s₁, State.setReg, hru]
        have hrN₁ : s₁.regs (r_m + 12) = N := by simp [s₁, State.setReg, hconst.1]
        let s₂ := s₁.setReg (r_m + 6) (idx + N)
        have hex_add : Exec w (.assign (r_m + 6) (.op .add (.reg (r_m + 3)) (.reg (r_m + 12)))) s₁ s₂ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hrN₁, hidx_w, hN_w, hidxN_w])
        have hq₂ : VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) rev_items 0 s₂ :=
          hqstate.of_eq rfl rfl (by simp [s₂, s₁, State.setReg]) (by simp [s₂, s₁, State.setReg])
        rcases tryPushVis_exec (a_base + 12) (a_base + 13)
            r_m (r_m + 1) (r_m + 7) (r_m + 6)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw h2N_w (y := idx + N) hq₂ (by simp [s₂]) (by omega) with
          ⟨s₃, t_push, extra, hex_push, ht_push, hq₃, hex_eq, hmem_ex, harr₃, hreg₃⟩
        have hex_ite : Exec w (.ite (.reg (r_m + 7)) _ .skip) s₁ s₃ (1 + (4 + t_push)) :=
          .ite_true hcondB (by omega) (.seq hex_add hex_push)
        have harr_lt₃ : ∀ a < a_base + 12, s₃.arrs a = s.arrs a :=
          fun a ha => harr₃ a (by omega) (by omega)
        have hreg_out₃ : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₃.regs r = s.regs r := by
          intro r hr
          rw [hreg₃ r (by omega) (by omega)]
          simp [s₂, s₁, State.setReg,
            show (r : Reg) ≠ r_m + 6 by omega,
            show (r : Reg) ≠ r_m + 7 by omega]
        have hb_act : (⟨idx, hidx_lt⟩ : Fin N) ∈ activeVerts S z ow :=
          (mem_sinkNeighbors_iff ⟨idx, hidx_lt⟩).mp hmemB |>.1
        have hb_sound := resReach_out_of_mem_sinkNeighbors hk hsys.1 hmemB
        refine ⟨s₃, 3 + (1 + (4 + t_push)), extra, .seq hex_rdB hex_ite, by omega,
          hconst.of_regs_eq (hreg_out₃ _ (by omega)) (hreg_out₃ _ (by omega)) (hreg_out₃ _ (by omega)),
          hsys.of_arrs_eq (harr_lt₃ (a_base + 6) (by omega))
            (harr_lt₃ (a_base + 7) (by omega)) (harr_lt₃ (a_base + 8) (by omega)),
          hq₃,
          hsound.append_out hex_eq hb_act hb_sound,
          fun z_it => by simp [hmem_ex z_it, hmemB],
          by rw [hreg₃ (r_m + 3) (by omega) (by omega)]; simp [s₂, hru₁],
          harr_lt₃, hreg_out₃⟩
      · have hvalB_0 : valB = 0 := by simp [hvalB_eq, hmemB]
        have hcondB : (Expr.reg (r_m + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hvalB_0, h0_w]
        have hq₁ : VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) rev_items 0 s₁ :=
          hqstate.of_eq rfl rfl (by simp [s₁, State.setReg]) (by simp [s₁, State.setReg])
        have hreg_out₁ : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₁.regs r = s.regs r := by
          intro r hr
          simp [s₁, State.setReg, show (r : Reg) ≠ r_m + 7 by omega]
        refine ⟨s₁, 3 + 2, [], .seq hex_rdB (.ite_false hcondB (.skip s₁)), by omega,
          hconst.of_regs_eq (hreg_out₁ _ (by omega)) (hreg_out₁ _ (by omega)) (hreg_out₁ _ (by omega)),
          hsys, by simpa using hq₁, by simpa using hsound,
          fun z_it => by simp [hmemB],
          by simp [s₁, State.setReg, hru],
          fun _ _ => rfl, hreg_out₁⟩
    rcases hbody_step with
      ⟨s_b, t_b, extra, hex_b, ht_b, hconst_b, hsys_b, hq_b, hsound_b, hmem_b, hru_b, harr_b, hreg_b⟩
    have hinc : (Expr.op .add (.reg (r_m + 3)) (.const 1)).eval w s_b = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_b, hidx_w, hw,
        show idx + 1 < 2 ^ w by omega]
    let s_next := s_b.setReg (r_m + 3) (idx + 1)
    have hex_inc : Exec w (.assign (r_m + 3) (.op .add (.reg (r_m + 3)) (.const 1)))
        s_b s_next 4 := .assign hinc
    have hq_next : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
        r_m (r_m + 1) (rev_items ++ extra) 0 s_next :=
      hq_b.of_eq rfl rfl (by simp [s_next, State.setReg]) (by simp [s_next, State.setReg])
    have hreg_next : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s_next.regs r = s.regs r := by
      intro r hr
      simp [s_next, State.setReg, show (r : Reg) ≠ r_m + 3 by omega, hreg_b r hr]
    have hconst_next : ConstRegs N k r_m s_next :=
      hconst.of_regs_eq (hreg_next _ (by omega)) (hreg_next _ (by omega)) (hreg_next _ (by omega))
    have hB_next : IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s_next :=
      hB_bit.of_arr_eq (by simp [s_next, harr_b (a_base + 2) (by omega)])
    have hinit_next : ∀ b ∈ sinkNeighbors S D z ow, b.val < idx + 1 → b.val + N ∈ rev_items ++ extra := by
      intro b hb hb_lt
      rw [hmem_b (b.val + N)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb_lt with hlt | heq
      · exact Or.inl (hinit_prev b hb hlt)
      · have hb_eq : (⟨idx, hidx_lt⟩ : Fin N) = b := Fin.ext heq.symm
        rw [hb_eq]
        exact Or.inr ⟨hb, by omega⟩
    rcases ih (idx + 1) (by omega) hconst_next hB_next hsys_b hq_next hsound_b hinit_next
        (by simp [s_next]) with
      ⟨s_end, t_end, items_end, hex_end, ht_end, hconst_end, hsys_end, hq_end, hsound_end,
        hinit_end, harr_end, hreg_end⟩
    refine ⟨s_end, 3 + (t_b + 4) + t_end, items_end,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex_end,
      by omega, hconst_end, hsys_end, hq_end, hsound_end, hinit_end,
      fun a ha => by rw [harr_end a ha]; exact harr_b a ha,
      fun r hr => by rw [hreg_end r hr]; exact hreg_next r hr⟩

theorem revInitSourcesProg_exec {w N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (a_base r_m : ℕ)
    (hk : 1 ≤ k) (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w)
    {s : State}
    (hconst : ConstRegs N k r_m s)
    (hB_bit : IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s)
    (hsys : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s) :
    ∃ s' t rev_items,
      Exec w (revInitSourcesProg a_base r_m) s s' t ∧
      t ≤ 11 + 34 * N ∧
      ConstRegs N k r_m s' ∧
      PathSystemState (activeGraph G S z ow)
        (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s' ∧
      VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) rev_items 0 s' ∧
      RevSoundInv G S D z k ow used pred succ rev_items ∧
      (∀ b ∈ sinkNeighbors S D z ow, b.val + N ∈ rev_items) ∧
      (∀ a < a_base + 12, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr (a_base + 12) (List.replicate (2 * N) 0)
  have hex₁ : Exec w (.alloc (a_base + 12) (.reg (r_m + 13))) s s₁ (1 + 2 * N) :=
    .alloc (by simp [Expr.eval, checkWord, hconst.2.1, h2N_w])
  let s₂ := s₁.setArr (a_base + 13) (List.replicate (2 * N) 0)
  have hex₂ : Exec w (.alloc (a_base + 13) (.reg (r_m + 13))) s₁ s₂ (1 + 2 * N) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hconst.2.1, h2N_w])
  have harr_lt₂ : ∀ a < a_base + 12, s₂.arrs a = s.arrs a := by
    intro a ha
    simp [s₂, s₁, show (a : Arr) ≠ a_base + 13 by omega, show (a : Arr) ≠ a_base + 12 by omega]
  let s₃ := s₂.setReg r_m 0
  have hex₃ : Exec w (.assign r_m (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_m + 1) 0
  have hex₄ : Exec w (.assign (r_m + 1) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg (r_m + 3) 0
  have hex₅ : Exec w (.assign (r_m + 3) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hreg_out₅ : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₅.regs r = s.regs r := by
    intro r hr
    simp [s₅, s₄, s₃, s₂, s₁, State.setReg,
      show (r : Reg) ≠ r_m + 3 by omega,
      show (r : Reg) ≠ r_m + 1 by omega,
      show (r : Reg) ≠ r_m by omega]
  have hconst₅ : ConstRegs N k r_m s₅ :=
    hconst.of_regs_eq (hreg_out₅ _ (by omega)) (hreg_out₅ _ (by omega)) (hreg_out₅ _ (by omega))
  have hqstate₅ : VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) [] 0 s₅ := by
    refine ⟨⟨by simp [s₅, s₄, s₃, s₂], Nat.zero_le _,
      by simp [s₅, s₄, s₃, State.setReg],
      by simp [s₅, s₄, s₃, State.setReg],
      Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩,
      List.nodup_nil, fun _ h => by simp at h,
      by simp [s₅, s₄, s₃, s₂, s₁],
      fun x hx => by simp [s₅, s₄, s₃, s₂, s₁]⟩
  have hB₅ : IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s₅ :=
    hB_bit.of_arr_eq (by simp [s₅, s₄, s₃, harr_lt₂ (a_base + 2) (by omega)])
  have hsys₅ : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s₅ :=
    hsys.of_arrs_eq (harr_lt₂ (a_base + 6) (by omega))
      (harr_lt₂ (a_base + 7) (by omega)) (harr_lt₂ (a_base + 8) (by omega))
  rcases revInitSourcesLoop_exec G S D z k ow used pred succ a_base r_m hk hw h2N_w
      N 0 (by omega) hconst₅ hB₅ hsys₅ hqstate₅
      (RevSoundInv.empty G S D z k ow used pred succ)
      (fun _ _ h => absurd h (Nat.not_lt_zero _))
      (by simp [s₅]) with
    ⟨s₆, t₆, rev_items, hex₆, ht₆, hconst₆, hsys₆, hq₆, hsound₆, hinit₆, harr₆, hreg₆⟩
  refine ⟨s₆, (1 + 2 * N) + ((1 + 2 * N) + (2 + (2 + (2 + t₆)))), rev_items,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hconst₆, hsys₆, hq₆, hsound₆, hinit₆,
    fun a ha => by rw [harr₆ a ha]; exact harr_lt₂ a ha,
    fun r hr => by rw [hreg₆ r hr]; exact hreg_out₅ r hr⟩

/-- One step of the reverse residual BFS queue loop. -/
def revResBfsStepProg (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (queuePop (a_base + 13) r_m (r_m + 2))
    (.ite (.op .lt (.reg (r_m + 2)) (.reg (r_m + 12)))
      -- In-node x < N (v = x)
      (.seq (.assign (r_m + 7) (.read (a_base + 6) (.reg (r_m + 2))))
        (.seq (.ite (.reg (r_m + 7))
            (.seq (.assign (r_m + 6) (.op .add (.reg (r_m + 2)) (.reg (r_m + 12))))
              (tryPushVis (a_base + 12) (a_base + 13) (r_m + 1) (r_m + 7) (r_m + 6)))
            .skip)
          (forList (a_base + 3) (a_base + 4) (a_base + 5)
            (r_m + 2) (r_m + 4) (r_m + 5) (r_m + 3)
            (.seq (.assign (r_m + 6) (.op .add (.reg (r_m + 3)) (.reg (r_m + 12))))
              (tryPushVis (a_base + 12) (a_base + 13) (r_m + 1) (r_m + 7) (r_m + 6))))))
      -- Out-node x >= N (w = x - N)
      (.seq (.assign (r_m + 3) (.op .sub (.reg (r_m + 2)) (.reg (r_m + 12))))
        (.seq (.assign (r_m + 7) (.read (a_base + 6) (.reg (r_m + 3))))
          (.ite (.reg (r_m + 7))
            -- used[w] != 0: check succ[w] < N
            (.seq (.assign (r_m + 6) (.read (a_base + 8) (.reg (r_m + 3))))
              (.ite (.op .lt (.reg (r_m + 6)) (.reg (r_m + 12)))
                (tryPushVis (a_base + 12) (a_base + 13) (r_m + 1) (r_m + 7) (r_m + 6))
                .skip))
            -- used[w] == 0: push w
            (tryPushVis (a_base + 12) (a_base + 13) (r_m + 1) (r_m + 7) (r_m + 3))))))

/-- The reverse residual BFS queue `while` loop (`while r_m < r_m + 1`). -/
def revResBfsLoopProg (a_base : Arr) (r_m : Reg) : Cmd :=
  .while (.op .lt (.reg r_m) (.reg (r_m + 1)))
    (revResBfsStepProg a_base r_m)

/-- Full reverse residual BFS program (`revInitSourcesProg` followed by `revResBfsLoopProg`). -/
def revResBfsProg (a_base : Arr) (r_m : Reg) : Cmd :=
  .seq (revInitSourcesProg a_base r_m)
    (revResBfsLoopProg a_base r_m)

theorem revResBfsStepProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (lists_act : Fin N → List ℕ) (S : Finset (Fin N)) (D : List (Fin N))
    (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (a_base r_m : ℕ)
    (hk : 1 ≤ k) (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w)
    {rev_items : List ℕ} {headIdx : ℕ} {s : State}
    (hconst : ConstRegs N k r_m s)
    (hadj : IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s)
    (hent_w : (s.arrs (a_base + 5)).length < 2 ^ w)
    (hsys : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s)
    (hqstate : VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) rev_items headIdx s)
    (hsound : RevSoundInv G S D z k ow used pred succ rev_items)
    (hclosed : IsRevPopClosed G S z ow used succ rev_items headIdx)
    (hhead : headIdx < rev_items.length) :
    ∃ s' t extra,
      Exec w (revResBfsStepProg a_base r_m) s s' t ∧
      t + 3 ≤ revNodeWeight lists_act ⟨rev_items[headIdx], hqstate.2.2.1 rev_items[headIdx] (List.getElem_mem hhead)⟩ ∧
      ConstRegs N k r_m s' ∧
      IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s' ∧
      PathSystemState (activeGraph G S z ow)
        (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s' ∧
      VisQueueState (2 * N) (a_base + 12) (a_base + 13)
        r_m (r_m + 1) (rev_items ++ extra) (headIdx + 1) s' ∧
      RevSoundInv G S D z k ow used pred succ (rev_items ++ extra) ∧
      IsRevPopClosed G S z ow used succ (rev_items ++ extra) (headIdx + 1) ∧
      (∀ a < a_base + 12, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hN_w : N < 2 ^ w := by omega
  let x := rev_items[headIdx]
  have hx_mem : x ∈ rev_items := List.getElem_mem hhead
  have hx_lt : x < 2 * N := hqstate.2.2.1 x hx_mem
  have hx_w : x < 2 ^ w := by omega
  -- 1. queuePop (a_base + 13) r_m (r_m + 2)
  rcases Triple.queuePop_spec (a_base + 13) r_m (r_m + 1) (r_m + 2) (2 * N) rev_items headIdx
      (by omega) (by omega) (by omega) hw h2N_w hhead hx_w s hqstate.1 with
    ⟨s₁, t_pop, hex_pop, ht_pop, hq₁, hrx₁⟩
  change s₁.regs (r_m + 2) = x at hrx₁
  dsimp only at ht_pop
  have hnot_pop_arr : ∀ a : Arr, s₁.arrs a = s.arrs a :=
    fun a => Exec.arrs_eq_of_not_mem_writtenArrs hex_pop (by simp [queuePop, Cmd.writtenArrs])
  have hreg_pop : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₁.regs r = s.regs r := by
    intro r hr
    have hnot : (r : Reg) ∉ (queuePop (a_base + 13) r_m (r_m + 2)).writtenRegs := by
      simp [queuePop, Cmd.writtenRegs,
        show (r : Reg) ≠ r_m + 2 by omega, show (r : Reg) ≠ r_m by omega]
    exact Exec.regs_eq_of_not_mem_writtenRegs hex_pop hnot
  have hconst₁ : ConstRegs N k r_m s₁ :=
    hconst.of_regs_eq (hreg_pop _ (by omega)) (hreg_pop _ (by omega)) (hreg_pop _ (by omega))
  have hqstate₁ : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
      r_m (r_m + 1) rev_items (headIdx + 1) s₁ := by
    rcases hqstate with ⟨_, hno, hlt_it, hv_len, hv_iff⟩
    exact ⟨hq₁, hno, hlt_it,
      by rw [hnot_pop_arr]; exact hv_len,
      fun z_it hz => by simp only [hnot_pop_arr]; exact hv_iff z_it hz⟩
  by_cases hx_n : x < N
  · -- Branch x < N (in-node v = x)
    let vFin : Fin N := ⟨x, hx_n⟩
    have hv_act : vFin ∈ activeVerts S z ow := hsound.in_active vFin hx_mem
    have hv_sound := hsound.in_sound vFin hx_mem
    have hcond_x : (Expr.op .lt (.reg (r_m + 2)) (.reg (r_m + 12))).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hconst₁.1, hx_w, hN_w, hx_n, hw]
    have hu_len : (s₁.arrs (a_base + 6)).length = N := by rw [hnot_pop_arr]; exact hsys.2.1
    have hx_u : x < (s₁.arrs (a_base + 6)).length := by rw [hu_len]; exact hx_n
    have hvalU_eq : (s₁.arrs (a_base + 6))[x]'hx_u = used vFin := by
      simp only [hnot_pop_arr]; exact hsys.2.2.2.2.1 vFin
    have hvalU_le : used vFin ≤ 1 := hsys.1.used_le vFin
    have hvalU_w : used vFin < 2 ^ w := by omega
    let s₂ := s₁.setReg (r_m + 7) (used vFin)
    have hex_rdU : Exec w (.assign (r_m + 7) (.read (a_base + 6) (.reg (r_m + 2)))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrx₁, hx_w, hx_u, hvalU_eq, hvalU_w])
    have hrx₂ : s₂.regs (r_m + 2) = x := by simp [s₂, State.setReg, hrx₁]
    have hqstate₂ : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
        r_m (r_m + 1) rev_items (headIdx + 1) s₂ :=
      hqstate₁.of_eq rfl rfl (by simp [s₂, State.setReg]) (by simp [s₂, State.setReg])
    -- Step 2: if used[v] != 0 then push v + N
    have hused_step : ∃ s₃ t_used extra₁,
        Exec w (.ite (.reg (r_m + 7))
          (.seq (.assign (r_m + 6) (.op .add (.reg (r_m + 2)) (.reg (r_m + 12))))
            (tryPushVis (a_base + 12) (a_base + 13) (r_m + 1) (r_m + 7) (r_m + 6)))
          .skip) s₂ s₃ t_used ∧
        t_used ≤ 19 ∧
        VisQueueState (2 * N) (a_base + 12) (a_base + 13)
          r_m (r_m + 1) (rev_items ++ extra₁) (headIdx + 1) s₃ ∧
        RevSoundInv G S D z k ow used pred succ (rev_items ++ extra₁) ∧
        (used vFin ≠ 0 → x + N ∈ rev_items ++ extra₁) ∧
        s₃.regs (r_m + 2) = x ∧
        (∀ a < a_base + 12, s₃.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₃.regs r = s.regs r) := by
      by_cases hvalU_ne : used vFin ≠ 0
      · have hcondU : (Expr.reg (r_m + 7)).eval w s₂ = some (used vFin) := by
          simp [s₂, Expr.eval, checkWord, hvalU_w]
        have hxN_w : x + N < 2 ^ w := by omega
        have hrN₂ : s₂.regs (r_m + 12) = N := by simp [s₂, State.setReg, hconst₁.1]
        let s_a := s₂.setReg (r_m + 6) (x + N)
        have hex_add : Exec w (.assign (r_m + 6) (.op .add (.reg (r_m + 2)) (.reg (r_m + 12)))) s₂ s_a 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₂, hrN₂, hx_w, hN_w, hxN_w])
        have hq_a : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
            r_m (r_m + 1) rev_items (headIdx + 1) s_a :=
          hqstate₂.of_eq rfl rfl (by simp [s_a, State.setReg]) (by simp [s_a, State.setReg])
        rcases tryPushVis_exec (a_base + 12) (a_base + 13)
            r_m (r_m + 1) (r_m + 7) (r_m + 6)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw h2N_w (y := x + N) hq_a (by simp [s_a]) (by omega) with
          ⟨s₃, t_push, extra₁, hex_push, ht_push, hq₃, hex_eq, hmem_ex, harr₃, hreg₃⟩
        refine ⟨s₃, 1 + (4 + t_push), extra₁,
          .ite_true hcondU hvalU_ne (.seq hex_add hex_push), by omega,
          hq₃,
          hsound.append_out hex_eq hv_act (resReach_out_of_in_used hvalU_ne hv_sound),
          fun _ => (hmem_ex (x + N)).mpr (Or.inr rfl),
          by rw [hreg₃ (r_m + 2) (by omega) (by omega)]; simp [s_a, hrx₂],
          fun a ha => by rw [harr₃ a (by omega) (by omega)]; exact hnot_pop_arr a,
          fun r hr => by
            rw [hreg₃ r (by omega) (by omega)]
            simp [s_a, s₂, State.setReg,
              show (r : Reg) ≠ r_m + 6 by omega,
              show (r : Reg) ≠ r_m + 7 by omega, hreg_pop r hr]⟩
      · have hvalU_eq0 : used vFin = 0 := by omega
        have hcondU : (Expr.reg (r_m + 7)).eval w s₂ = some 0 := by
          simp [s₂, Expr.eval, checkWord, hvalU_eq0, h0_w]
        refine ⟨s₂, 2, [], .ite_false hcondU (.skip s₂), by omega,
          by simpa using hqstate₂, by simpa using hsound,
          fun hne => absurd hvalU_eq0 hne,
          hrx₂, fun a _ => hnot_pop_arr a,
          fun r hr => by
            simp [s₂, State.setReg, show (r : Reg) ≠ r_m + 7 by omega, hreg_pop r hr]⟩
    rcases hused_step with
      ⟨s₃, t_used, extra₁, hex_used, ht_used, hq₃, hsound₃, hused_mem, hrx₃, harr₃, hreg₃⟩
    -- Step 3: forList over neighbors u of vFin in activeGraph
    have hadj₃ : IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s₃ :=
      hadj.of_arrs_eq (harr₃ (a_base + 3) (by omega))
        (harr₃ (a_base + 4) (by omega)) (harr₃ (a_base + 5) (by omega))
    obtain ⟨st_v, en_v, hlist_v⟩ := hadj₃.1.2.2 vFin
    obtain ⟨hmem_lt_v, _, _, hadj_iff_v⟩ := hadj₃.2 vFin
    have hen_w : en_v < 2 ^ w := by
      rcases hlist_v with ⟨_, _, hen_ent, _, _, _, _, _⟩
      have hent₃ : s₃.arrs (a_base + 5) = s.arrs (a_base + 5) := harr₃ (a_base + 5) (by omega)
      rw [hent₃] at hen_ent
      omega
    let InnerInv (j : ℕ) (st : State) : Prop :=
      IsListAt (a_base + 3) (a_base + 4) (a_base + 5) x st_v en_v (lists_act vFin) st ∧
      st.regs (r_m + 2) = x ∧
      (∀ a < a_base + 12, st.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → st.regs r = s.regs r) ∧
      ∃ extra₂ : List ℕ,
        VisQueueState (2 * N) (a_base + 12) (a_base + 13)
          r_m (r_m + 1) (rev_items ++ extra₁ ++ extra₂) (headIdx + 1) st ∧
        RevSoundInv G S D z k ow used pred succ (rev_items ++ extra₁ ++ extra₂) ∧
        (∀ u ∈ (lists_act vFin).take j, u + N ∈ rev_items ++ extra₁ ++ extra₂)
    have hInner₀ : InnerInv 0 s₃ :=
      ⟨hlist_v, hrx₃, harr₃, hreg₃, [],
        by simpa using hq₃, by simpa using hsound₃, fun _ hu => by simp at hu⟩
    have hforList :
        ⦃InnerInv 0⦄[w]
          forList (a_base + 3) (a_base + 4) (a_base + 5)
            (r_m + 2) (r_m + 4) (r_m + 5) (r_m + 3)
            (.seq (.assign (r_m + 6) (.op .add (.reg (r_m + 3)) (.reg (r_m + 12))))
              (tryPushVis (a_base + 12) (a_base + 13) (r_m + 1) (r_m + 7) (r_m + 6)))
        ⦃InnerInv (lists_act vFin).length⦄ ≤
          fun _ => 9 + (lists_act vFin).length * (10 + 18) := by
      apply Triple.forList_const (a_base + 3) (a_base + 4) (a_base + 5)
        (r_m + 2) (r_m + 4) (r_m + 5) (r_m + 3)
        x st_v en_v (lists_act vFin) InnerInv 18 _
        (by omega) (by omega) hw hx_w hen_w
      · intro z_it hz
        have := hmem_lt_v z_it hz
        omega
      · intro st₀ ⟨hlist₀, hrx₀, harr₀, hreg₀, extra₂, hq₀, hsound₀, hprev₀⟩
        refine ⟨hlist₀, hrx₀, hlist₀,
          by simp [State.setReg, hrx₀],
          harr₀,
          fun r hr => by
            simp [State.setReg,
              show (r : Reg) ≠ r_m + 5 by omega,
              show (r : Reg) ≠ r_m + 4 by omega, hreg₀ r hr],
          extra₂,
          hq₀.of_eq rfl rfl (by simp [State.setReg]) (by simp [State.setReg]),
          hsound₀, hprev₀⟩
      · intro j _ st_j ⟨hlist_j, _, _, _, _⟩
        exact hlist_j
      · intro j hj sb_u ⟨sb, ⟨hlist_b, hrx_b, harr_b, hreg_b, extra₂, hq_b, hsound_b, hprev_b⟩,
          hsb_u, hrk_b, hrhi_b⟩
        subst hsb_u
        let u_val := (lists_act vFin)[j]
        have hu_mem : u_val ∈ lists_act vFin := List.getElem_mem hj
        have hu_lt_n : u_val < N := hmem_lt_v u_val hu_mem
        have hu_w : u_val < 2 ^ w := by omega
        have huN_w : u_val + N < 2 ^ w := by omega
        let uFin : Fin N := ⟨u_val, hu_lt_n⟩
        have hadj_vu : (activeGraph G S z ow).Adj vFin uFin :=
          (hadj_iff_v uFin).mp hu_mem
        have hu_act : uFin ∈ activeVerts S z ow := hadj_vu.2.1
        have hu_sound := resReach_out_of_in_adj hk hsys.1 hadj_vu hv_sound
        let sb₁ := sb.setReg (r_m + 3) u_val
        have hru₁ : sb₁.regs (r_m + 3) = u_val := by simp [sb₁]
        have hrN₁ : sb₁.regs (r_m + 12) = N := by
          simp [sb₁, State.setReg, hreg_b (r_m + 12) (by omega), hconst.1]
        let sb₂ := sb₁.setReg (r_m + 6) (u_val + N)
        have hex_add : Exec w (.assign (r_m + 6) (.op .add (.reg (r_m + 3)) (.reg (r_m + 12))))
            sb₁ sb₂ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hrN₁, hu_w, hN_w, huN_w])
        have hq_b₂ : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
            r_m (r_m + 1) (rev_items ++ extra₁ ++ extra₂) (headIdx + 1) sb₂ :=
          hq_b.of_eq rfl rfl (by simp [sb₂, sb₁, State.setReg]) (by simp [sb₂, sb₁, State.setReg])
        rcases tryPushVis_exec (a_base + 12) (a_base + 13)
            r_m (r_m + 1) (r_m + 7) (r_m + 6)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw h2N_w (y := u_val + N) hq_b₂ (by simp [sb₂]) (by omega) with
          ⟨sb₃, t_push, extra₃, hex_push, ht_push, hq_b₃, hex_eq₃, hmem_ex₃, harr_b₃, hreg_b₃⟩
        have harr_lt₃ : ∀ a < a_base + 12, sb₃.arrs a = s.arrs a := by
          intro a ha
          rw [harr_b₃ a (by omega) (by omega)]
          exact harr_b a ha
        have hlist_next : IsListAt (a_base + 3) (a_base + 4) (a_base + 5) x st_v en_v (lists_act vFin)
            (sb₃.setReg (r_m + 4) (st_v + (j + 1))) :=
          hlist_b.of_arrs_eq
            (harr_b₃ (a_base + 3) (by omega) (by omega))
            (harr_b₃ (a_base + 4) (by omega) (by omega))
            (harr_b₃ (a_base + 5) (by omega) (by omega))
        have hq_next : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
            r_m (r_m + 1) (rev_items ++ extra₁ ++ (extra₂ ++ extra₃)) (headIdx + 1)
            (sb₃.setReg (r_m + 4) (st_v + (j + 1))) := by
          rw [← List.append_assoc]
          exact hq_b₃.of_eq rfl rfl (by simp [State.setReg]) (by simp [State.setReg])
        have hsound_next : RevSoundInv G S D z k ow used pred succ
            (rev_items ++ extra₁ ++ (extra₂ ++ extra₃)) := by
          rw [← List.append_assoc]
          exact hsound_b.append_out hex_eq₃ hu_act hu_sound
        refine ⟨sb₃, 4 + t_push, .seq hex_add hex_push, show 4 + t_push ≤ 18 by omega,
          ⟨hlist_next,
            by simp [State.setReg, hreg_b₃ (r_m + 2) (by omega) (by omega), sb₂, sb₁, hrx_b],
            harr_lt₃,
            fun r hr => by
              simp [State.setReg,
                show (r : Reg) ≠ r_m + 4 by omega,
                hreg_b₃ r (by omega) (by omega), sb₂, sb₁,
                show (r : Reg) ≠ r_m + 6 by omega,
                show (r : Reg) ≠ r_m + 3 by omega, hreg_b r hr],
            extra₂ ++ extra₃, hq_next, hsound_next,
            fun u hu => by
              rw [← List.append_assoc, hmem_ex₃ (u + N)]
              rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
                List.mem_append, List.mem_singleton] at hu
              rcases hu with hu_prev | rfl
              · exact Or.inl (hprev_b u hu_prev)
              · exact Or.inr rfl⟩,
          by rw [hreg_b₃ (r_m + 4) (by omega) (by omega)]; simp [sb₂, sb₁, State.setReg, hrk_b],
          by rw [hreg_b₃ (r_m + 5) (by omega) (by omega)]; simp [sb₂, sb₁, State.setReg, hrhi_b]⟩
    rcases hforList s₃ hInner₀ with
      ⟨s₄, t_list, hex_list, ht_list, _, _, harr₄, hreg₄, extra₂, hq₄, hsound₄, hprev₄⟩
    dsimp only [vFin, x] at ht_list
    rw [List.take_length] at hprev₄
    rw [List.append_assoc] at hq₄ hsound₄ hprev₄
    have hclosed₄ : IsRevPopClosed G S z ow used succ (rev_items ++ (extra₁ ++ extra₂)) (headIdx + 1) := by
      apply hclosed.step hhead
      · intro v hv_eq
        have hveq : v = vFin := Fin.ext hv_eq.symm
        subst hveq
        refine ⟨fun hu_ne => ?_, fun u hadj_vu => ?_⟩
        · rw [← List.append_assoc]
          exact List.mem_append_left _ (hused_mem hu_ne)
        · exact hprev₄ u.val ((hadj_iff_v u).mpr hadj_vu)
      · intro w hw_eq
        change x = w.val + N at hw_eq
        omega
    refine ⟨s₄, t_pop + (3 + (3 + (t_used + t_list))), extra₁ ++ extra₂,
      .seq hex_pop (.ite_true hcond_x (by omega) (.seq hex_rdU (.seq hex_used hex_list))),
      by simp [revNodeWeight, show rev_items[headIdx] < N from hx_n]; omega,
      hconst.of_regs_eq (hreg₄ _ (by omega)) (hreg₄ _ (by omega)) (hreg₄ _ (by omega)),
      hadj.of_arrs_eq (harr₄ (a_base + 3) (by omega))
        (harr₄ (a_base + 4) (by omega)) (harr₄ (a_base + 5) (by omega)),
      hsys.of_arrs_eq (harr₄ (a_base + 6) (by omega))
        (harr₄ (a_base + 7) (by omega)) (harr₄ (a_base + 8) (by omega)),
      hq₄, hsound₄, hclosed₄, harr₄, hreg₄⟩
  · -- Branch x >= N (out-node w = x - N)
    have hcond_x : (Expr.op .lt (.reg (r_m + 2)) (.reg (r_m + 12))).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hconst₁.1, hx_w, hN_w, hx_n, h0_w]
    let u := x - N
    have hu_lt : u < N := by omega
    have hu_w : u < 2 ^ w := by omega
    let wFin : Fin N := ⟨u, hu_lt⟩
    have hw_mem : wFin.val + N ∈ rev_items := by
      have : wFin.val + N = x := by dsimp [wFin, u]; omega
      rw [this]; exact hx_mem
    have hw_act : wFin ∈ activeVerts S z ow := hsound.out_active wFin hw_mem
    have hw_sound := hsound.out_sound wFin hw_mem
    -- 1. r_m + 3 := (r_m + 2) - (r_m + 12)
    let s₂ := s₁.setReg (r_m + 3) u
    have hex_sub : Exec w (.assign (r_m + 3) (.op .sub (.reg (r_m + 2)) (.reg (r_m + 12)))) s₁ s₂ 4 :=
      .assign (by
        have hsub_w : x - N < 2 ^ w := hu_w
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hconst₁.1, hx_w, hN_w, hsub_w]
        rfl)
    -- 2. r_m + 7 := (a_base + 6)[r_m + 3] (used[w])
    have hu_len : (s₂.arrs (a_base + 6)).length = N := by
      simp only [s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.1
    have hu_idx : u < (s₂.arrs (a_base + 6)).length := by rw [hu_len]; exact hu_lt
    have hvalU_eq : (s₂.arrs (a_base + 6))[u]'hu_idx = used wFin := by
      simp only [s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.2.2.2.1 wFin
    have hvalU_le : used wFin ≤ 1 := hsys.1.used_le wFin
    have hvalU_w : used wFin < 2 ^ w := by omega
    have hru₂ : s₂.regs (r_m + 3) = u := by simp [s₂]
    let s₃ := s₂.setReg (r_m + 7) (used wFin)
    have hex_rdU : Exec w (.assign (r_m + 7) (.read (a_base + 6) (.reg (r_m + 3)))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru₂, hu_w, hu_idx, hvalU_eq, hvalU_w])
    have hru₃ : s₃.regs (r_m + 3) = u := by simp [s₃, s₂, State.setReg]
    have hqstate₃ : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
        r_m (r_m + 1) rev_items (headIdx + 1) s₃ :=
      hqstate₁.of_eq rfl rfl (by simp [s₃, s₂, State.setReg]) (by simp [s₃, s₂, State.setReg])
    by_cases hvalU_ne : used wFin ≠ 0
    · -- used[w] != 0: check succ[w] < N
      have hcondU : (Expr.reg (r_m + 7)).eval w s₃ = some (used wFin) := by
        simp [s₃, Expr.eval, checkWord, hvalU_w]
      have hs_len : (s₃.arrs (a_base + 8)).length = N := by
        simp only [s₃, s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.2.2.1
      have hu_s : u < (s₃.arrs (a_base + 8)).length := by rw [hs_len]; exact hu_lt
      have hvalS_eq : (s₃.arrs (a_base + 8))[u]'hu_s = succ wFin := by
        simp only [s₃, s₂, State.setReg_arrs, hnot_pop_arr]; exact hsys.2.2.2.2.2.2 wFin
      have hvalS_le : succ wFin ≤ N := hsys.1.succ_le wFin
      have hvalS_w : succ wFin < 2 ^ w := by omega
      let s₄ := s₃.setReg (r_m + 6) (succ wFin)
      have hex_rdS : Exec w (.assign (r_m + 6) (.read (a_base + 8) (.reg (r_m + 3)))) s₃ s₄ 3 :=
        .assign (by simp [Expr.eval, checkWord, hru₃, hu_w, hu_s, hvalS_eq, hvalS_w])
      have hrs₄ : s₄.regs (r_m + 6) = succ wFin := by simp [s₄]
      have hrN₄ : s₄.regs (r_m + 12) = N := by simp [s₄, s₃, s₂, State.setReg, hconst₁.1]
      have hqstate₄ : VisQueueState (2 * N) (a_base + 12) (a_base + 13)
          r_m (r_m + 1) rev_items (headIdx + 1) s₄ :=
        hqstate₃.of_eq rfl rfl (by simp [s₄, State.setReg]) (by simp [s₄, State.setReg])
      by_cases hvalS_lt : succ wFin < N
      · have hcondS : (Expr.op .lt (.reg (r_m + 6)) (.reg (r_m + 12))).eval w s₄ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs₄, hrN₄, hvalS_w, hN_w, hvalS_lt, hw]
        let uNext : Fin N := ⟨succ wFin, hvalS_lt⟩
        have huNext_act : uNext ∈ activeVerts S z ow :=
          (hsys.1.adj_of_succ wFin uNext rfl).2.2.2.1
        have huNext_sound := resReach_in_of_out_succ (pred := pred) (u := uNext) hw_act hvalU_ne rfl hw_sound
        rcases tryPushVis_exec (a_base + 12) (a_base + 13)
            r_m (r_m + 1) (r_m + 7) (r_m + 6)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw h2N_w (y := succ wFin) hqstate₄ hrs₄ (by omega) with
          ⟨s₅, t_push, extra, hex_push, ht_push, hq₅, hex_eq, hmem_ex, harr₅, hreg₅⟩
        have harr_lt₅ : ∀ a < a_base + 12, s₅.arrs a = s.arrs a := by
          intro a ha
          rw [harr₅ a (by omega) (by omega)]
          exact hnot_pop_arr a
        have hreg_out₅ : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₅.regs r = s.regs r := by
          intro r hr
          rw [hreg₅ r (by omega) (by omega)]
          simp [s₄, s₃, s₂, State.setReg,
            show (r : Reg) ≠ r_m + 6 by omega,
            show (r : Reg) ≠ r_m + 7 by omega,
            show (r : Reg) ≠ r_m + 3 by omega, hreg_pop r hr]
        have hclosed₅ : IsRevPopClosed G S z ow used succ (rev_items ++ extra) (headIdx + 1) := by
          apply hclosed.step hhead
          · intro v hv_eq
            change x = v.val at hv_eq
            have := v.2
            omega
          · intro w hw_eq
            have hweq : w = wFin := Fin.ext (by change x = w.val + N at hw_eq; dsimp [wFin, u]; omega)
            subst hweq
            refine ⟨fun hu0 => absurd hu0 hvalU_ne, fun u_t _ hsucc_u => ?_⟩
            rw [hmem_ex u_t.val]
            exact Or.inr hsucc_u.symm
        refine ⟨s₅, t_pop + (3 + (4 + (3 + (1 + (3 + (3 + t_push)))))), extra,
          .seq hex_pop (.ite_false hcond_x (.seq hex_sub (.seq hex_rdU
            (.ite_true hcondU hvalU_ne (.seq hex_rdS (.ite_true hcondS (by omega) hex_push)))))),
          by simp [revNodeWeight, show ¬ rev_items[headIdx] < N from hx_n]; omega,
          hconst.of_regs_eq (hreg_out₅ _ (by omega)) (hreg_out₅ _ (by omega)) (hreg_out₅ _ (by omega)),
          hadj.of_arrs_eq (harr_lt₅ (a_base + 3) (by omega))
            (harr_lt₅ (a_base + 4) (by omega)) (harr_lt₅ (a_base + 5) (by omega)),
          hsys.of_arrs_eq (harr_lt₅ (a_base + 6) (by omega))
            (harr_lt₅ (a_base + 7) (by omega)) (harr_lt₅ (a_base + 8) (by omega)),
          hq₅, hsound.append_in hex_eq huNext_act huNext_sound, hclosed₅, harr_lt₅, hreg_out₅⟩
      · have hcondS : (Expr.op .lt (.reg (r_m + 6)) (.reg (r_m + 12))).eval w s₄ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs₄, hrN₄, hvalS_w, hN_w, hvalS_lt, h0_w]
        have hreg_out₄ : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₄.regs r = s.regs r := by
          intro r hr
          simp [s₄, s₃, s₂, State.setReg,
            show (r : Reg) ≠ r_m + 6 by omega,
            show (r : Reg) ≠ r_m + 7 by omega,
            show (r : Reg) ≠ r_m + 3 by omega, hreg_pop r hr]
        have hclosed₄ : IsRevPopClosed G S z ow used succ (rev_items ++ []) (headIdx + 1) := by
          apply hclosed.step hhead
          · intro v hv_eq
            change x = v.val at hv_eq
            have := v.2
            omega
          · intro w hw_eq
            have hweq : w = wFin := Fin.ext (by change x = w.val + N at hw_eq; dsimp [wFin, u]; omega)
            subst hweq
            refine ⟨fun hu0 => absurd hu0 hvalU_ne, fun u_t _ hsucc_u => ?_⟩
            have := u_t.2
            omega
        refine ⟨s₄, t_pop + (3 + (4 + (3 + (1 + (3 + 4))))), [],
          .seq hex_pop (.ite_false hcond_x (.seq hex_sub (.seq hex_rdU
            (.ite_true hcondU hvalU_ne (.seq hex_rdS (.ite_false hcondS (.skip s₄))))))),
          by simp [revNodeWeight, show ¬ rev_items[headIdx] < N from hx_n]; omega,
          hconst.of_regs_eq (hreg_out₄ _ (by omega)) (hreg_out₄ _ (by omega)) (hreg_out₄ _ (by omega)),
          hadj.of_arrs_eq (hnot_pop_arr (a_base + 3)) (hnot_pop_arr (a_base + 4)) (hnot_pop_arr (a_base + 5)),
          hsys.of_arrs_eq (hnot_pop_arr (a_base + 6)) (hnot_pop_arr (a_base + 7)) (hnot_pop_arr (a_base + 8)),
          by simpa using hqstate₄, by simpa using hsound, hclosed₄,
          fun a _ => hnot_pop_arr a, hreg_out₄⟩
    · -- used[w] == 0: push w
      have hvalU_eq0 : used wFin = 0 := by omega
      have hcondU : (Expr.reg (r_m + 7)).eval w s₃ = some 0 := by
        simp [s₃, Expr.eval, checkWord, hvalU_eq0, h0_w]
      have hw_in_sound := resReach_in_of_out_unused hw_act hvalU_eq0 hw_sound
      rcases tryPushVis_exec (a_base + 12) (a_base + 13)
          r_m (r_m + 1) (r_m + 7) (r_m + 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          hw h2N_w hqstate₃ hru₃ (by omega) with
        ⟨s₄, t_push, extra, hex_push, ht_push, hq₄, hex_eq, hmem_ex, harr₄, hreg₄⟩
      have harr_lt₄ : ∀ a < a_base + 12, s₄.arrs a = s.arrs a := by
        intro a ha
        rw [harr₄ a (by omega) (by omega)]
        exact hnot_pop_arr a
      have hreg_out₄ : ∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s₄.regs r = s.regs r := by
        intro r hr
        rw [hreg₄ r (by omega) (by omega)]
        simp [s₃, s₂, State.setReg,
          show (r : Reg) ≠ r_m + 7 by omega,
          show (r : Reg) ≠ r_m + 3 by omega, hreg_pop r hr]
      have hclosed₄ : IsRevPopClosed G S z ow used succ (rev_items ++ extra) (headIdx + 1) := by
        apply hclosed.step hhead
        · intro v hv_eq
          change x = v.val at hv_eq
          have := v.2
          omega
        · intro w hw_eq
          have hweq : w = wFin := Fin.ext (by change x = w.val + N at hw_eq; dsimp [wFin, u]; omega)
          subst hweq
          refine ⟨fun _ => (hmem_ex wFin.val).mpr (Or.inr rfl),
            fun _ hne _ => absurd hvalU_eq0 hne⟩
      refine ⟨s₄, t_pop + (3 + (4 + (3 + (1 + t_push)))), extra,
        .seq hex_pop (.ite_false hcond_x (.seq hex_sub (.seq hex_rdU
          (.ite_false hcondU hex_push)))),
        by simp [revNodeWeight, show ¬ rev_items[headIdx] < N from hx_n]; omega,
        hconst.of_regs_eq (hreg_out₄ _ (by omega)) (hreg_out₄ _ (by omega)) (hreg_out₄ _ (by omega)),
        hadj.of_arrs_eq (harr_lt₄ (a_base + 3) (by omega))
          (harr_lt₄ (a_base + 4) (by omega)) (harr_lt₄ (a_base + 5) (by omega)),
        hsys.of_arrs_eq (harr_lt₄ (a_base + 6) (by omega))
          (harr_lt₄ (a_base + 7) (by omega)) (harr_lt₄ (a_base + 8) (by omega)),
        hq₄, hsound.append_in hex_eq hw_act hw_in_sound, hclosed₄, harr_lt₄, hreg_out₄⟩

theorem revResBfsLoopProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (lists_act : Fin N → List ℕ) (S : Finset (Fin N)) (D : List (Fin N))
    (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (a_base r_m : ℕ)
    (hk : 1 ≤ k) (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w)
    {rev_items : List ℕ} {headIdx : ℕ} {s : State}
    (hconst : ConstRegs N k r_m s)
    (hadj : IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s)
    (hent_w : (s.arrs (a_base + 5)).length < 2 ^ w)
    (hsys : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s)
    (hqstate : VisQueueState (2 * N) (a_base + 12) (a_base + 13) r_m (r_m + 1) rev_items headIdx s)
    (hsound : RevSoundInv G S D z k ow used pred succ rev_items)
    (hclosed : IsRevPopClosed G S z ow used succ rev_items headIdx)
    (hseed : ∀ b ∈ sinkNeighbors S D z ow, b.val + N ∈ rev_items) :
    ∃ s' t rev_items',
      Exec w (revResBfsLoopProg a_base r_m) s s' t ∧
      t ≤ 3 + (∑ z_it ∈ Finset.univ \ listFinset (2 * N) (rev_items.take headIdx), revNodeWeight lists_act z_it) ∧
      ConstRegs N k r_m s' ∧
      IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s' ∧
      PathSystemState (activeGraph G S z ow)
        (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s' ∧
      VisQueueState (2 * N) (a_base + 12) (a_base + 13)
        r_m (r_m + 1) rev_items' rev_items'.length s' ∧
      IsRevResClosed G S D z k ow used pred succ rev_items' ∧
      (∀ a < a_base + 12, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  generalize hB : (∑ z_it ∈ Finset.univ \ listFinset (2 * N) (rev_items.take headIdx), revNodeWeight lists_act z_it) = B_pot
  induction B_pot using Nat.strong_induction_on generalizing rev_items headIdx s with
  | _ B_pot ih =>
    rcases hqstate.1 with ⟨_, hle_2n, hrhead, hrtail, hhead_le, _⟩
    have htail_w : rev_items.length < 2 ^ w := by omega
    have hhead_w : headIdx < 2 ^ w := by omega
    by_cases hhead_lt : headIdx < rev_items.length
    · have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          hhead_w, htail_w, hhead_lt, hw]
      rcases revResBfsStepProg_exec G lists_act S D z k ow used pred succ a_base r_m
          hk hw h2N_w hconst hadj hent_w hsys hqstate hsound hclosed hhead_lt with
        ⟨s₁, t₁, extra, hex₁, ht₁, hconst₁, hadj₁, hsys₁, hq₁, hsound₁, hclosed₁, harr₁, hreg₁⟩
      have hx_lt : rev_items[headIdx] < 2 * N := hqstate.2.2.1 rev_items[headIdx] (List.getElem_mem hhead_lt)
      have hpop_sum := sum_revNodeWeight_pop (extra := extra) lists_act hqstate.2.1 hhead_lt hx_lt
      rw [hB] at hpop_sum
      set B' := ∑ z_it ∈ Finset.univ \ listFinset (2 * N) ((rev_items ++ extra).take (headIdx + 1)),
        revNodeWeight lists_act z_it
      have hB'_lt : B' < B_pot := by omega
      have hent_w₁ : (s₁.arrs (a_base + 5)).length < 2 ^ w := by
        rw [harr₁ (a_base + 5) (by omega)]; exact hent_w
      have hseed₁ : ∀ b ∈ sinkNeighbors S D z ow, b.val + N ∈ rev_items ++ extra :=
        fun b hb => List.mem_append_left _ (hseed b hb)
      rcases ih B' hB'_lt hconst₁ hadj₁ hent_w₁ hsys₁ hq₁ hsound₁ hclosed₁ hseed₁ rfl with
        ⟨s₂, t₂, rev_items', hex₂, ht₂, hconst₂, hadj₂, hsys₂, hq₂, hrev₂, harr₂, hreg₂⟩
      refine ⟨s₂, 3 + t₁ + t₂, rev_items', .while_true hcond (by omega) hex₁ hex₂,
        by omega, hconst₂, hadj₂, hsys₂, hq₂, hrev₂,
        fun a ha => by rw [harr₂ a ha, harr₁ a ha],
        fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]⟩
    · have hhead_eq : headIdx = rev_items.length := by omega
      subst hhead_eq
      have hcond : (Expr.op .lt (.reg r_m) (.reg (r_m + 1))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail, htail_w, h0_w]
      exact ⟨s, 3, rev_items, .while_false hcond, by omega, hconst, hadj, hsys, hqstate,
        hclosed.to_isRevResClosed hsound hseed, fun _ _ => rfl, fun _ _ => rfl⟩

theorem revResBfsProg_exec {w N : ℕ} (G : SimpleGraph (Fin N))
    (lists_act : Fin N → List ℕ) (S : Finset (Fin N)) (D : List (Fin N))
    (z : Fin N) (k ow : ℕ) (used pred succ : Fin N → ℕ)
    (a_base r_m : ℕ)
    (hk : 1 ≤ k) (hw : 1 < 2 ^ w) (h2N_w : 2 * N < 2 ^ w)
    {s : State}
    (hconst : ConstRegs N k r_m s)
    (hB_bit : IsBitSet (sinkNeighbors S D z ow) (a_base + 2) s)
    (hadj : IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s)
    (hent_w : (s.arrs (a_base + 5)).length < 2 ^ w)
    (hsys : PathSystemState (activeGraph G S z ow)
      (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s) :
    ∃ s' t rev_items,
      Exec w (revResBfsProg a_base r_m) s s' t ∧
      t ≤ 14 + 124 * N + 29 * totalAdjEntries lists_act ∧
      ConstRegs N k r_m s' ∧
      PathSystemState (activeGraph G S z ow)
        (sourceNeighbors G S z ow) (sinkNeighbors S D z ow) (a_base + 6) used pred succ s' ∧
      IsResVisArr N (a_base + 12) rev_items s' ∧
      IsRevResClosed G S D z k ow used pred succ rev_items ∧
      (∀ a < a_base + 12, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_m ∨ r ≥ r_m + 9 → s'.regs r = s.regs r) := by
  rcases revInitSourcesProg_exec G S D z k ow used pred succ a_base r_m hk hw h2N_w
      hconst hB_bit hsys with
    ⟨s₁, t₁, rev_items₀, hex₁, ht₁, hconst₁, hsys₁, hq₁, hsound₁, hseed₁, harr₁, hreg₁⟩
  have hadj₁ : IsAdjList (activeGraph G S z ow) (a_base + 3) (a_base + 4) (a_base + 5) lists_act s₁ :=
    hadj.of_arrs_eq (harr₁ (a_base + 3) (by omega))
      (harr₁ (a_base + 4) (by omega)) (harr₁ (a_base + 5) (by omega))
  have hent_w₁ : (s₁.arrs (a_base + 5)).length < 2 ^ w := by
    rw [harr₁ (a_base + 5) (by omega)]; exact hent_w
  rcases revResBfsLoopProg_exec G lists_act S D z k ow used pred succ a_base r_m hk hw h2N_w
      hconst₁ hadj₁ hent_w₁ hsys₁ hq₁ hsound₁
      (IsRevPopClosed.zero G S z ow used succ rev_items₀) hseed₁ with
    ⟨s₂, t₂, rev_items, hex₂, ht₂, hconst₂, _, hsys₂, hq₂, hrev₂, harr₂, hreg₂⟩
  have hsum_le := sum_revNodeWeight_le_univ lists_act
    (Finset.univ \ listFinset (2 * N) (rev_items₀.take 0))
  refine ⟨s₂, t₁ + t₂, rev_items, .seq hex₁ hex₂, by omega, hconst₂, hsys₂,
    hq₂.to_isResVisArr, hrev₂,
    fun a ha => by rw [harr₂ a ha, harr₁ a ha],
    fun r hr => by rw [hreg₂ r hr, hreg₁ r hr]⟩

end GraphMinor.Compute.Crossing
