module

public import GraphMinor.Compute.CrossingOpsBasic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Rebuilding adjacency lists, one vertex after another

The contraction, the replacement and the sparsification of the crossing extractor all rebuild
the adjacency lists of an instance. Each of them computes the new list `L x` of every vertex `x`
in turn, appends it to a buffer, and records where it starts and ends. This file proves this
pattern once:
* `flatUpTo L x`: the lists `L 0, …, L (x - 1)` one after another;
* `isListFamily_flatUpTo`: the start, end and entries arrays of this layout hold the family `L`;
* `length_flatUpTo_eq`: when the family `L` is an adjacency-list family of a graph `H`, the
  layout has `2 |E(H)|` entries, as `IsInstanceAt` asks;
* `vertexLoopProg_exec`: the loop over the vertices, for any body that appends `L x` to the
  buffer.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph

/-! ### The layout of a family of lists -/

/-- The lists `L 0, …, L (x - 1)`, one after another. -/
def flatUpTo (L : ℕ → List ℕ) (x : ℕ) : List ℕ :=
  ((List.range x).map L).flatten

@[simp] theorem flatUpTo_zero (L : ℕ → List ℕ) : flatUpTo L 0 = [] := rfl

theorem flatUpTo_succ (L : ℕ → List ℕ) (x : ℕ) :
    flatUpTo L (x + 1) = flatUpTo L x ++ L x := by
  simp [flatUpTo, List.range_succ]

theorem flatUpTo_add (L : ℕ → List ℕ) (x d : ℕ) :
    ∃ rest, flatUpTo L (x + d) = flatUpTo L x ++ rest := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨rest, h⟩ := ih
    exact ⟨rest ++ L (x + d), by rw [← Nat.add_assoc, flatUpTo_succ, h, List.append_assoc]⟩

theorem length_flatUpTo_mono (L : ℕ → List ℕ) {x y : ℕ} (h : x ≤ y) :
    (flatUpTo L x).length ≤ (flatUpTo L y).length := by
  obtain ⟨rest, hr⟩ := flatUpTo_add L x (y - x)
  rw [show x + (y - x) = y by omega] at hr
  rw [hr]; simp

theorem length_flatUpTo (L : ℕ → List ℕ) (x : ℕ) :
    (flatUpTo L x).length = ∑ y ∈ Finset.range x, (L y).length := by
  induction x with
  | zero => simp
  | succ x ih => rw [flatUpTo_succ, List.length_append, ih, Finset.sum_range_succ]

/-- **The layout holds the family.** If the start array holds `|flatUpTo L x|`, the end array
`|flatUpTo L (x + 1)|` and the entries array `flatUpTo L N`, then the arrays hold the lists
`L 0, …, L (N - 1)`. -/
theorem isListFamily_flatUpTo {N : ℕ} {a_st a_en a_ent : Arr} {L : ℕ → List ℕ} {s : State}
    (hst : s.arrs a_st = (List.range N).map (fun x => (flatUpTo L x).length))
    (hen : s.arrs a_en = (List.range N).map (fun x => (flatUpTo L (x + 1)).length))
    (hent : s.arrs a_ent = flatUpTo L N) :
    IsListFamily N a_st a_en a_ent (fun x => L x) s := by
  refine ⟨by simp [hst], by simp [hen], fun u => ?_⟩
  obtain ⟨rest, hrest⟩ := flatUpTo_add L (u.1 + 1) (N - (u.1 + 1))
  rw [show u.1 + 1 + (N - (u.1 + 1)) = N by omega, flatUpTo_succ] at hrest
  have hle := length_flatUpTo_mono L (show u.1 + 1 ≤ N by omega)
  refine ⟨(flatUpTo L u).length, (flatUpTo L (u + 1)).length, by simp [hst], by simp [hen],
    by rw [hent]; exact hle, by simp [flatUpTo_succ], by simp [hst], by simp [hen],
    length_flatUpTo_mono L (by omega), fun k hk => ?_⟩
  simp only [hent, hrest]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
  simp

/-! ### The number of entries -/

/-- A list of distinct numbers below `N` has at most `N` entries. -/
theorem length_le_of_nodup_lt {l : List ℕ} {N : ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < N) :
    l.length ≤ N := by
  rw [← List.toFinset_card_of_nodup hnd]
  calc l.toFinset.card ≤ (Finset.range N).card :=
        Finset.card_le_card (fun x hx => by simpa using hlt x (List.mem_toFinset.mp hx))
    _ = N := Finset.card_range N

/-- The list of a vertex in an adjacency-list family has the degree of the vertex as length. -/
theorem length_eq_degree {N : ℕ} {H : SimpleGraph (Fin N)} [DecidableRel H.Adj]
    {lists : Fin N → List ℕ} (h : IsAdjListFamily H lists) (x : Fin N) :
    (lists x).length = H.degree x := by
  obtain ⟨hlt, hnd, -, hmem⟩ := h x
  rw [← List.toFinset_card_of_nodup hnd, ← card_neighborFinset_eq_degree]
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext y
  simp only [List.mem_toFinset, Finset.mem_map, mem_neighborFinset, Fin.valEmbedding_apply]
  constructor
  · intro hy
    exact ⟨⟨y, hlt y hy⟩, (hmem ⟨y, hlt y hy⟩).mp hy, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact (hmem z).mpr hz

/-- **The number of entries.** When `L` is an adjacency-list family of `H`, the layout of `L`
has `2 |E(H)|` entries. -/
theorem length_flatUpTo_eq {N : ℕ} {H : SimpleGraph (Fin N)} {L : ℕ → List ℕ}
    (h : IsAdjListFamily H (fun x => L x)) :
    (flatUpTo L N).length = 2 * H.edgeSet.ncard := by
  classical
  rw [length_flatUpTo, ← Fin.sum_univ_eq_sum_range (fun y => (L y).length)]
  have : ∀ x : Fin N, (L x).length = H.degree x := fun x => length_eq_degree h x
  simp only [this]
  rw [sum_degrees_eq_twice_card_edges, ← Set.ncard_coe_finset, coe_edgeFinset]

/-! ### The loop over the vertices -/

/-- For each vertex `x < N` (`N` in register `r_N`, `x` in register `r_x`): record the start of
its list, run `body`, which appends the list of `x` to the buffer at the cursor `r_cnt`, and
record the end. -/
def vertexLoopProg (r_x r_N r_cnt : Reg) (a_st a_en : Arr) (body : Cmd) : Cmd :=
  forUp r_x (.reg r_N)
    (.seq (.write a_st (.reg r_x) (.reg r_cnt))
      (.seq body (.write a_en (.reg r_x) (.reg r_cnt))))

/-- The arrays of starts and ends after `x` rounds of the loop over the vertices. -/
def startsUpTo (L : ℕ → List ℕ) (N x : ℕ) : List ℕ :=
  (List.range x).map (fun y => (flatUpTo L y).length) ++ List.replicate (N - x) 0

/-- See `startsUpTo`. -/
def endsUpTo (L : ℕ → List ℕ) (N x : ℕ) : List ℕ :=
  (List.range x).map (fun y => (flatUpTo L (y + 1)).length) ++ List.replicate (N - x) 0

theorem set_upTo {f : ℕ → ℕ} {N x : ℕ} (hx : x < N) :
    ((List.range x).map f ++ List.replicate (N - x) 0).set x (f x) =
      (List.range (x + 1)).map f ++ List.replicate (N - (x + 1)) 0 := by
  rw [show N - x = (N - (x + 1)) + 1 by omega, List.replicate_succ,
    List.set_append_right _ _ (by simp)]
  simp [List.range_succ]

/-- **The loop over the vertices.** If, for every vertex `x`, the body appends `L x` to the
buffer in at most `cost x` steps and keeps the property `P`, the loop leaves the layout of `L`
in the start, end and buffer arrays. The property `P` must not depend on the start and end
arrays or on the register `r_x`. -/
theorem vertexLoopProg_exec {w N cap : ℕ} (r_x r_N r_cnt a_st a_en a_buf : ℕ) (body : Cmd)
    (L : ℕ → List ℕ) (cost : ℕ → ℕ) (P : State → Prop)
    (h_se : a_st ≠ a_en) (h_sb : a_st ≠ a_buf) (h_eb : a_en ≠ a_buf)
    (h_xN : r_x ≠ r_N) (h_xc : r_x ≠ r_cnt)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hcap : cap < 2 ^ w)
    (htot : (flatUpTo L N).length ≤ cap)
    (hP : ∀ s s', P s → (∀ a, a ≠ a_st → a ≠ a_en → s'.arrs a = s.arrs a) →
      (∀ r, r ≠ r_x → s'.regs r = s.regs r) → P s')
    (hbody : ∀ x < N, ∀ s k, P s → s.regs r_x = x → s.regs r_N = N →
      IsBuf a_buf r_cnt (flatUpTo L x) k s → (L x).length ≤ k →
      ∃ s' t, Exec w body s s' t ∧ t ≤ cost x ∧ P s' ∧ s'.regs r_x = x ∧ s'.regs r_N = N ∧
        IsBuf a_buf r_cnt (flatUpTo L (x + 1)) (k - (L x).length) s' ∧
        s'.arrs a_st = s.arrs a_st ∧ s'.arrs a_en = s.arrs a_en)
    {s : State} (hP0 : P s) (hx0 : s.regs r_x = 0) (hN0 : s.regs r_N = N)
    (hst0 : s.arrs a_st = List.replicate N 0) (hen0 : s.arrs a_en = List.replicate N 0)
    (hbuf0 : IsBuf a_buf r_cnt [] cap s) :
    ∃ s' t, Exec w (vertexLoopProg r_x r_N r_cnt a_st a_en body) s s' t ∧
      t ≤ 3 + 13 * N + ∑ x ∈ Finset.range N, cost x ∧ P s' ∧ s'.regs r_N = N ∧
      IsBuf a_buf r_cnt (flatUpTo L N) (cap - (flatUpTo L N).length) s' ∧
      s'.arrs a_st = (List.range N).map (fun x => (flatUpTo L x).length) ∧
      s'.arrs a_en = (List.range N).map (fun x => (flatUpTo L (x + 1)).length) := by
  let I : ℕ → State → Prop := fun x st =>
    P st ∧ st.regs r_x = x ∧ st.regs r_N = N ∧
    IsBuf a_buf r_cnt (flatUpTo L x) (cap - (flatUpTo L x).length) st ∧
    st.arrs a_st = startsUpTo L N x ∧ st.arrs a_en = endsUpTo L N x
  have hI0 : I 0 s := ⟨hP0, hx0, hN0, by simpa using hbuf0, by simp [startsUpTo, hst0],
    by simp [endsUpTo, hen0]⟩
  let Φ : State → ℕ := fun st => ∑ y ∈ Finset.range (st.regs r_x), cost y
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec I Φ N 6 (r_i := r_x) (hi := .reg r_N)
    (body := .seq (.write a_st (.reg r_x) (.reg r_cnt))
      (.seq body (.write a_en (.reg r_x) (.reg r_cnt)))) hw hN
    (fun x _ st h => ⟨h.2.1, eval_reg h.2.2.1 hN⟩)
    (fun x hx st h => by
      obtain ⟨hPs, hrx, hrN, hbuf, hst, hen⟩ := h
      have hxw : x < 2 ^ w := by omega
      have hfl : (flatUpTo L x).length ≤ (flatUpTo L N).length := length_flatUpTo_mono L hx.le
      have hfl1 : (flatUpTo L (x + 1)).length ≤ (flatUpTo L N).length :=
        length_flatUpTo_mono L hx
      have hcw : (flatUpTo L x).length < 2 ^ w := by omega
      -- record the start
      have hlt₁ : x < (st.arrs a_st).length := by rw [hst]; simp [startsUpTo]; omega
      have hex₁ := Exec.write (a := a_st) (eval_reg hrx hxw) (eval_reg hbuf.2 hcw) hlt₁
      set st₁ := st.writeArr a_st x (flatUpTo L x).length
      have hP₁ : P st₁ := hP st st₁ hPs (fun a h1 _ => by simp [st₁, State.writeArr_arrs_ne _ _ _ h1])
        (fun r _ => rfl)
      have hbuf₁ : IsBuf a_buf r_cnt (flatUpTo L x) (cap - (flatUpTo L x).length) st₁ :=
        ⟨by simp [st₁, State.writeArr_arrs_ne _ _ _ h_sb.symm, hbuf.1], by simp [st₁, hbuf.2]⟩
      have hlen : (L x).length ≤ cap - (flatUpTo L x).length := by
        rw [flatUpTo_succ, List.length_append] at hfl1; omega
      obtain ⟨st₂, t₂, hex₂, ht₂, hP₂, hrx₂, hrN₂, hbuf₂, hst₂, hen₂⟩ :=
        hbody x hx st₁ _ hP₁ (by simp [st₁, hrx]) (by simp [st₁, hrN]) hbuf₁ hlen
      -- record the end
      have hcw' : (flatUpTo L (x + 1)).length < 2 ^ w := by omega
      have hlt₃ : x < (st₂.arrs a_en).length := by
        rw [hen₂]; simp [st₁, State.writeArr_arrs_ne _ _ _ h_se.symm, hen, endsUpTo]; omega
      have hex₃ := Exec.write (a := a_en) (eval_reg hrx₂ hxw) (eval_reg hbuf₂.2 hcw') hlt₃
      set st₃ := st₂.writeArr a_en x (flatUpTo L (x + 1)).length
      refine ⟨st₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, ⟨?_, by simp, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Φ, Expr.cost, State.setReg_regs_self, Finset.sum_range_succ]
        rw [show st.regs r_x = x from hrx]; omega
      · refine hP st₂ _ hP₂ (fun a _ h2 => ?_) (fun r h => ?_)
        · simp [st₃, State.writeArr_arrs_ne _ _ _ h2]
        · simp [st₃, h]
      · simp [st₃, State.setReg_regs_ne _ _ h_xN.symm, hrN₂]
      · have e : cap - (flatUpTo L x).length - (L x).length =
            cap - (flatUpTo L (x + 1)).length := by
          rw [flatUpTo_succ, List.length_append]; omega
        refine ⟨by simp [st₃, State.writeArr_arrs_ne _ _ _ h_eb.symm, hbuf₂.1, e], ?_⟩
        simp [st₃, State.setReg_regs_ne _ _ h_xc.symm, hbuf₂.2]
      · simp only [st₃, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h_se, hst₂, st₁,
          State.writeArr_arrs_self, hst, startsUpTo]
        exact set_upTo hx
      · simp only [st₃, State.setReg_arrs, State.writeArr_arrs_self, hen₂, st₁,
          State.writeArr_arrs_ne _ _ _ h_se.symm, hen, endsUpTo]
        exact set_upTo (f := fun y => (flatUpTo L (y + 1)).length) hx
      · simp [st₃, hrx₂])
    0 (Nat.zero_le _) s hI0
  obtain ⟨hPs, hrx, hrN, hbuf, hst, hen⟩ := hI
  refine ⟨s', t, hex, ?_, hPs, hrN, hbuf, by simpa [startsUpTo] using hst,
    by simpa [endsUpTo] using hen⟩
  simp only [Φ, hx0, Finset.range_zero, Finset.sum_empty, Expr.cost, hrx] at ht
  omega

end GraphMinor.Compute.Crossing
