module

public import GraphMinor.GM02.DisjointPathsInput
public import GraphMinor.Compute.MultiDigraph
public import GraphMinor.Compute.GM02ConcatArrays
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.GM02CapEdgeList
import GraphMinor.Compute.Algorithm44

/-!
# From a disjoint-paths instance to a terminated graph

Graph Minors II proves (1.3) by running the program of (3.2) on the terminated
graph whose pairs are the terminal pairs. The disjoint-paths encoding lists the
graph and then the pairs `s_0, t_0, ..., s_{k-1}, t_{k-1}`. The encoding of
(3.2) lists the graph, then the number of pairs, then the pairs as increasing
vertex pairs in row-major order. This file gives a program that rewrites the
first encoding into the second (`dpTerminatedProg_exec`).

The program caps every multiplicity at one, so that every word of the graph
part fits in a word of the machine. It then scans all vertex pairs `(u, v)` in
row-major order. For `u < v` it checks all `k` pairs and writes `(u, v)` when
`{u, v}` is one of them. Last it joins the capped graph and the list of pairs.
The time is `O((k + 1)(n + 1)²)`.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.GM02 _root_.GraphMinor.Compute.Crossing

variable {k : ℕ}

/-- One round of the scan over the `k` pairs: read the pair with number in
register `529` and add one to register `528` for each order in which it equals
`(u, v)`, held in registers `526` and `527`. Register `522` holds the position
of the first pair in the input. -/
def dpCountBody : Cmd :=
  .seq (.assign 530 (.read inArr (.op .add (.reg 522) (.op .mul (.const 2) (.reg 529)))))
    (.seq (.assign 531 (.read inArr
        (.op .add (.op .add (.reg 522) (.op .mul (.const 2) (.reg 529))) (.const 1))))
      (.assign 528 (.op .add (.reg 528)
        (.op .add (.op .mul (.op .eq (.reg 530) (.reg 526)) (.op .eq (.reg 531) (.reg 527)))
          (.op .mul (.op .eq (.reg 530) (.reg 527)) (.op .eq (.reg 531) (.reg 526)))))))

/-- One round of the scan over vertex pairs: register `525` holds the number
`j` of the pair `(j / n, j % n)`. When `j / n < j % n` and the pair is a
terminal pair, append it to array `503` at position `523`. -/
def dpOuterBody (k : ℕ) : Cmd :=
  .seq (.assign 526 (.op .div (.reg 525) (.reg 520)))
    (.seq (.assign 527 (.op .mod (.reg 525) (.reg 520)))
      (.ite (.op .lt (.reg 526) (.reg 527))
        (.seq (.assign 528 (.const 0))
          (.seq (.assign 529 (.const 0))
            (.seq (forUp 529 (.const k) dpCountBody)
              (.ite (.reg 528) (bufPush2 503 523 526 527) .skip))))
        .skip))

/-- Read `n` and the number of active pairs, find the first terminal pair, and
start array `503` with the number `k`. -/
def dpHeaderProg (k : ℕ) : Cmd :=
  .seq (.assign 520 (.read inArr (.const 0)))
    (.seq (.assign 521 (.read inArr (.const 1)))
      (.seq (.assign 522 (.op .add (.const 2) (.op .mul (.const 3) (.reg 521))))
        (.seq (.alloc 503 (.const (1 + 2 * k)))
          (.seq (.write 503 (.const 0) (.const k))
            (.seq (.assign 523 (.const 1))
              (.seq (.assign 524 (.op .mul (.reg 520) (.reg 520)))
                (.assign 525 (.const 0))))))))

/-- Rewrite a disjoint-paths instance with `k` pairs into the input of II (3.2). -/
def dpTerminatedProg (k : ℕ) : Cmd :=
  .seq (capMultiDigraphProg 0 inArr 500 501 500)
    (.seq (dpHeaderProg k)
      (.seq (forUp 525 (.reg 524) (dpOuterBody k)) (gm02ConcatArraysProg 501 503 inArr)))

/-! ### Small facts -/

theorem eval_div {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hb : b ≠ 0) :
    (Expr.op .div A B).eval w s = some (a / b) := by
  have ha : a < 2 ^ w := Expr.eval_lt hA
  have h : a / b < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self a b) ha
  simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hb]

theorem eval_mod {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hb : b ≠ 0) :
    (Expr.op .mod A B).eval w s = some (a % b) := by
  have hb' : b < 2 ^ w := Expr.eval_lt hB
  have h : a % b < 2 ^ w := lt_trans (Nat.mod_lt a (Nat.pos_of_ne_zero hb)) hb'
  simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hb]

/-- Every word of a multigraph encoding fits when `n`, the number of active
pairs and every multiplicity fit. -/
theorem MultiDigraph.enc_lt {w n : ℕ} (G : MultiDigraph n) (hn : n < 2 ^ w)
    (hm : G.numActivePairs < 2 ^ w) (hmult : ∀ u v, G.edgeMult u v < 2 ^ w) :
    ∀ y ∈ G.enc, y < 2 ^ w := by
  have htri : ∀ (L : List (Fin n × Fin n)), ∀ y ∈ MultiDigraph.flatTriples G L, y < 2 ^ w := by
    intro L
    induction L with
    | nil => simp [MultiDigraph.flatTriples]
    | cons p ps ih =>
      intro y hy
      simp only [MultiDigraph.flatTriples, List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · exact lt_trans p.1.2 hn
      · exact lt_trans p.2.2 hn
      · exact hmult _ _
      · exact ih y hy
  intro y hy
  simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hy
  rcases hy with rfl | rfl | hy
  · exact hn
  · exact hm
  · exact htri _ y hy

/-- The pair words of the disjoint-paths encoding. -/
theorem encDPIn_getElem?_fst (x : DPInput k) (i : Fin k) :
    (encDPIn x)[x.G.enc.length + 2 * i.1]? = some (x.pairs i).1.1 := by
  rw [encDPIn, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by simp), getElem_encDPPairs_even]

theorem encDPIn_getElem?_snd (x : DPInput k) (i : Fin k) :
    (encDPIn x)[x.G.enc.length + 2 * i.1 + 1]? = some (x.pairs i).2.1 := by
  rw [encDPIn, List.getElem?_append_right (by omega), Nat.add_assoc, Nat.add_sub_cancel_left,
    List.getElem?_eq_getElem (by simp; omega), getElem_encDPPairs_odd]

theorem eval_read_of_getElem? {w : ℕ} {s : State} {a : Arr} {E : Expr} {i v : ℕ}
    (hE : E.eval w s = some i) (h : (s.arrs a)[i]? = some v) (hv : v < 2 ^ w) :
    (Expr.read a E).eval w s = some v := by
  obtain ⟨hi, hval⟩ := List.getElem?_eq_some_iff.1 h
  rw [eval_read hE hi (hval ▸ hv), hval]

/-- Pair `i` equals `(u, v)` in one of its two orders. -/
def dpMatch (x : DPInput k) (i : Fin k) (u v : ℕ) : Prop :=
  ((x.pairs i).1.1 = u ∧ (x.pairs i).2.1 = v) ∨ ((x.pairs i).1.1 = v ∧ (x.pairs i).2.1 = u)

theorem dpMatchCount_ne_zero_iff (a b u v : ℕ) :
    (if a = u then 1 else 0) * (if b = v then 1 else 0) +
      (if a = v then 1 else 0) * (if b = u then 1 else 0) ≠ 0 ↔
      (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  by_cases h1 : a = u <;> by_cases h2 : b = v <;> by_cases h3 : a = v <;>
    by_cases h4 : b = u <;> simp [h1, h2, h3, h4]

/-! ### The scan over the `k` pairs -/

theorem dpCount_exec (x : DPInput k) {W : ℕ} (hW : x.G.enc.length + 2 * k + 2 < 2 ^ W)
    (hn : x.n < 2 ^ W) {u v : ℕ} (hu : u < 2 ^ W) (hv : v < 2 ^ W) {s : State}
    (hin : s.arrs inArr = encDPIn x) (h522 : s.regs 522 = x.G.enc.length)
    (h526 : s.regs 526 = u) (h527 : s.regs 527 = v) (h528 : s.regs 528 = 0)
    (h529 : s.regs 529 = 0) :
    ∃ s' t, Exec W (forUp 529 (.const k) dpCountBody) s s' t ∧ t ≤ 3 + k * 41 ∧
      s'.arrs = s.arrs ∧ (∀ r < 528, s'.regs r = s.regs r) ∧ s'.regs 528 ≤ 2 * k ∧
      (s'.regs 528 ≠ 0 ↔ ∃ i : Fin k, dpMatch x i u v) := by
  have hw : 1 < 2 ^ W := by omega
  let I : ℕ → State → Prop := fun i s' => s'.regs 529 = i ∧ s'.arrs = s.arrs ∧
    (∀ r < 528, s'.regs r = s.regs r) ∧ s'.regs 528 ≤ 2 * i ∧
    (s'.regs 528 ≠ 0 ↔ ∃ i' : Fin k, i'.1 < i ∧ dpMatch x i' u v)
  have hI0 : I 0 s := ⟨h529, rfl, fun _ _ => rfl, by omega, by simp [h528]⟩
  have hbody : ∀ i < k, ∀ s₁, I i s₁ → ∃ s₂ t, Exec W dpCountBody s₁ s₂ t ∧
      t ≤ 34 ∧ I (i + 1) (s₂.setReg 529 (i + 1)) ∧ s₂.regs 529 = i := by
    intro i hi s₁ hs₁
    obtain ⟨hr529, harr, hregs, hle, hiff⟩ := hs₁
    let ii : Fin k := ⟨i, hi⟩
    let a := (x.pairs ii).1.1
    let b := (x.pairs ii).2.1
    have ha : a < 2 ^ W := lt_trans (x.pairs ii).1.2 hn
    have hb : b < 2 ^ W := lt_trans (x.pairs ii).2.2 hn
    have hin₁ : s₁.arrs inArr = encDPIn x := by rw [harr, hin]
    have h522₁ : s₁.regs 522 = x.G.enc.length := by rw [hregs 522 (by decide), h522]
    have h526₁ : s₁.regs 526 = u := by rw [hregs 526 (by decide), h526]
    have h527₁ : s₁.regs 527 = v := by rw [hregs 527 (by decide), h527]
    have hidx : (Expr.op .add (.reg 522) (.op .mul (.const 2) (.reg 529))).eval W s₁ =
        some (x.G.enc.length + 2 * i) :=
      eval_add (eval_reg h522₁ (by omega))
        (eval_mul (eval_const (by omega)) (eval_reg hr529 (by omega)) (by omega)) (by omega)
    let s₂ := s₁.setReg 530 a
    have he₂ : Exec W (.assign 530 (.read inArr
        (.op .add (.reg 522) (.op .mul (.const 2) (.reg 529))))) s₁ s₂ 7 :=
      .assign (eval_read_of_getElem? hidx (by rw [hin₁]; exact encDPIn_getElem?_fst x ii) ha)
    have hidx' : (Expr.op .add (.op .add (.reg 522) (.op .mul (.const 2) (.reg 529)))
        (.const 1)).eval W s₂ = some (x.G.enc.length + 2 * i + 1) :=
      eval_add (eval_add (eval_reg (by simp [s₂, h522₁]) (by omega))
        (eval_mul (eval_const (by omega)) (eval_reg (by simp [s₂, hr529]) (by omega)) (by omega))
        (by omega)) (eval_const hw) (by omega)
    let s₃ := s₂.setReg 531 b
    have he₃ : Exec W (.assign 531 (.read inArr (.op .add (.op .add (.reg 522)
        (.op .mul (.const 2) (.reg 529))) (.const 1)))) s₂ s₃ 9 :=
      .assign (eval_read_of_getElem? hidx' (by
        simp only [s₂, State.setReg_arrs]
        rw [hin₁]
        exact encDPIn_getElem?_snd x ii) hb)
    let e := (if a = u then 1 else 0) * (if b = v then 1 else 0) +
      (if a = v then 1 else 0) * (if b = u then 1 else 0)
    have he2 : e ≤ 2 := by simp only [e]; split_ifs <;> omega
    have heiff : e ≠ 0 ↔ dpMatch x ii u v := dpMatchCount_ne_zero_iff a b u v
    let c := s₁.regs 528
    let s₄ := s₃.setReg 528 (c + e)
    have hr3 : ∀ r, r ≠ 530 → r ≠ 531 → s₃.regs r = s₁.regs r := fun r h1 h2 => by
      simp [s₃, s₂, State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2]
    have hev : ∀ (r₁ r₂ : Reg) (y₁ y₂ : ℕ), s₃.regs r₁ = y₁ → s₃.regs r₂ = y₂ → y₁ < 2 ^ W →
        y₂ < 2 ^ W → (Expr.op .eq (.reg r₁) (.reg r₂)).eval W s₃ = some (if y₁ = y₂ then 1 else 0) :=
      fun r₁ r₂ y₁ y₂ h₁ h₂ hy₁ hy₂ => eval_eq (eval_reg h₁ hy₁) (eval_reg h₂ hy₂) hw
    have h530 : s₃.regs 530 = a := by simp [s₃, s₂]
    have h531 : s₃.regs 531 = b := by simp [s₃]
    have h526₃ : s₃.regs 526 = u := by rw [hr3 526 (by decide) (by decide), h526₁]
    have h527₃ : s₃.regs 527 = v := by rw [hr3 527 (by decide) (by decide), h527₁]
    have he₄ : Exec W (.assign 528 (.op .add (.reg 528)
        (.op .add (.op .mul (.op .eq (.reg 530) (.reg 526)) (.op .eq (.reg 531) (.reg 527)))
          (.op .mul (.op .eq (.reg 530) (.reg 527)) (.op .eq (.reg 531) (.reg 526)))))) s₃ s₄ 18 := by
      refine .assign (eval_add (eval_reg (hr3 528 (by decide) (by decide)) (by omega))
        (eval_add (eval_mul (hev _ _ _ _ h530 h526₃ ha hu) (hev _ _ _ _ h531 h527₃ hb hv) ?_)
          (eval_mul (hev _ _ _ _ h530 h527₃ ha hv) (hev _ _ _ _ h531 h526₃ hb hu) ?_) ?_) ?_)
      · split_ifs <;> omega
      · split_ifs <;> omega
      · exact lt_of_le_of_lt he2 (by omega)
      · exact lt_of_le_of_lt (Nat.add_le_add hle he2) (by omega)
    refine ⟨s₄, 34, .seq he₂ (.seq he₃ he₄), by omega, ⟨by simp, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [s₄, s₃, s₂, State.setReg_arrs]
      exact harr
    · intro r hr
      have h1 : r ≠ 529 := Nat.ne_of_lt (lt_trans hr (by decide))
      have h2 : r ≠ 528 := Nat.ne_of_lt hr
      rw [State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2,
        hr3 r (Nat.ne_of_lt (lt_trans hr (by decide))) (Nat.ne_of_lt (lt_trans hr (by decide)))]
      exact hregs r hr
    · rw [State.setReg_regs_ne _ _ (by decide : (528 : Reg) ≠ 529)]
      simp only [s₄, State.setReg_regs_self]
      omega
    · rw [State.setReg_regs_ne _ _ (by decide : (528 : Reg) ≠ 529)]
      simp only [s₄, State.setReg_regs_self]
      constructor
      · intro h
        by_cases hc : c = 0
        · have hne : e ≠ 0 := by omega
          exact ⟨ii, by simp [ii], heiff.1 hne⟩
        · obtain ⟨i', hi', hm⟩ := hiff.1 hc
          exact ⟨i', by omega, hm⟩
      · rintro ⟨i', hi', hm⟩
        by_cases hlt : i'.1 < i
        · have := hiff.2 ⟨i', hlt, hm⟩
          omega
        · have hii : i' = ii := Fin.ext (by simp [ii]; omega)
          subst hii
          have := heiff.2 hm
          omega
    · simp [s₄, s₃, s₂, hr529]
  obtain ⟨s', t, he, ht, hI⟩ := forUp_exec' I k 34 hw (by omega)
    (fun i _ s' hs' => ⟨hs'.1, eval_const (by omega)⟩) hbody s hI0
  refine ⟨s', t, he, by simpa using ht, hI.2.1, hI.2.2.1, hI.2.2.2.1, ?_⟩
  rw [hI.2.2.2.2]
  exact ⟨fun ⟨i, _, h⟩ => ⟨i, h⟩, fun ⟨i, h⟩ => ⟨i, i.2, h⟩⟩

/-! ### The scan over all vertex pairs -/

/-- All vertex pairs in row-major order. -/
def dpRowPairs (n : ℕ) : List (Fin n × Fin n) :=
  List.ofFn fun j : Fin (n * n) => finProdFinEquiv.symm j

/-- The terminal pairs among the first `j` vertex pairs. -/
def dpPairPrefix (x : DPInput k) (j : ℕ) : List (Fin x.n × Fin x.n) :=
  ((dpRowPairs x.n).take j).filter fun p => decide (dpPairTest x p)

theorem dpPairPrefix_length_le (x : DPInput k) (hx : IsTermination x) (j : ℕ) :
    (dpPairPrefix x j).length ≤ k :=
  (((List.take_sublist j _).filter _).length_le).trans (dpPairList_length x hx).le

theorem dpPairPrefix_full (x : DPInput k) :
    dpPairPrefix x (x.n * x.n) = (dpRowPairs x.n).filter fun p => decide (dpPairTest x p) := by
  rw [dpPairPrefix, List.take_of_length_le (by simp [dpRowPairs])]

theorem dpPairPrefix_succ (x : DPInput k) {j : ℕ} (hj : j < x.n * x.n) :
    dpPairPrefix x (j + 1) = dpPairPrefix x j ++
      (if dpPairTest x (finProdFinEquiv.symm ⟨j, hj⟩) then [finProdFinEquiv.symm ⟨j, hj⟩]
        else []) := by
  rw [dpPairPrefix, dpPairPrefix, List.take_add_one, List.filter_append]
  congr 1
  rw [dpRowPairs, List.getElem?_ofFn]
  split_ifs with h
  · have h' : dpPairTest x ((⟨j, hj⟩ : Fin (x.n * x.n)).divNat, (⟨j, hj⟩ : Fin (x.n * x.n)).modNat) := h
    simp [h']
  · have h' : ¬ dpPairTest x ((⟨j, hj⟩ : Fin (x.n * x.n)).divNat,
        (⟨j, hj⟩ : Fin (x.n * x.n)).modNat) := h
    simp [h']

theorem dpPairTest_row_iff (x : DPInput k) {j : ℕ} (hj : j < x.n * x.n) :
    dpPairTest x (finProdFinEquiv.symm ⟨j, hj⟩) ↔
      j / x.n < j % x.n ∧ ∃ i, dpMatch x i (j / x.n) (j % x.n) := by
  have h1 : (finProdFinEquiv.symm (⟨j, hj⟩ : Fin (x.n * x.n))).1.1 = j / x.n := rfl
  have h2 : (finProdFinEquiv.symm (⟨j, hj⟩ : Fin (x.n * x.n))).2.1 = j % x.n := rfl
  simp only [dpPairTest, dpMatch, Fin.ext_iff, h1, h2]

/-- The state during the scan over vertex pairs, before pair `j`. -/
def DPScanInv (x : DPInput k) (E : List ℕ) (j : ℕ) (s : State) : Prop :=
  s.regs 525 = j ∧ s.regs 520 = x.n ∧ s.regs 522 = x.G.enc.length ∧
    s.regs 524 = x.n * x.n ∧ s.arrs inArr = encDPIn x ∧ s.arrs 501 = E ∧
    s.arrs 503 = (k :: flatEdges (dpPairPrefix x j)) ++
      List.replicate (2 * k - 2 * (dpPairPrefix x j).length) 0 ∧
    s.regs 523 = 1 + 2 * (dpPairPrefix x j).length

theorem DPScanInv.keep {x : DPInput k} {E : List ℕ} {j : ℕ} {s s' : State}
    (h : DPScanInv x E j s) (h520 : s'.regs 520 = s.regs 520) (h522 : s'.regs 522 = s.regs 522)
    (h524 : s'.regs 524 = s.regs 524) (h523 : s'.regs 523 = s.regs 523) (harr : s'.arrs = s.arrs)
    (hpre : dpPairPrefix x (j + 1) = dpPairPrefix x j) :
    DPScanInv x E (j + 1) (s'.setReg 525 (j + 1)) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [State.setReg_regs_ne _ _ (by decide), h520, h1]
  · rw [State.setReg_regs_ne _ _ (by decide), h522, h2]
  · rw [State.setReg_regs_ne _ _ (by decide), h524, h3]
  · rw [State.setReg_arrs, harr, h4]
  · rw [State.setReg_arrs, harr, h5]
  · rw [State.setReg_arrs, harr, h6, hpre]
  · rw [State.setReg_regs_ne _ _ (by decide), h523, h7, hpre]

theorem flatEdges_append_single {n : ℕ} (L : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    flatEdges (L ++ [p]) = flatEdges L ++ [p.1.1, p.2.1] := by
  simp [flatEdges]

theorem dpScan_exec (x : DPInput k) (hx : IsTermination x) (E : List ℕ) {W : ℕ}
    (hW1 : x.G.enc.length + 2 * k + 3 < 2 ^ W) (hW2 : x.n * x.n + x.n + 2 < 2 ^ W)
    {s : State} (hs : DPScanInv x E 0 s) :
    ∃ s' t, Exec W (forUp 525 (.reg 524) (dpOuterBody k)) s s' t ∧
      t ≤ 3 + x.n * x.n * (47 + 41 * k) ∧ DPScanInv x E (x.n * x.n) s' := by
  have hw : 1 < 2 ^ W := by omega
  have hn : x.n < 2 ^ W := by omega
  have hbody : ∀ j < x.n * x.n, ∀ s₁, DPScanInv x E j s₁ → ∃ s₂ t,
      Exec W (dpOuterBody k) s₁ s₂ t ∧ t ≤ 40 + 41 * k ∧
      DPScanInv x E (j + 1) (s₂.setReg 525 (j + 1)) ∧ s₂.regs 525 = j := by
    intro j hj s₁ hs₁
    have hinv := hs₁
    obtain ⟨h525, h520, h522, h524, hin, h501, h503, h523⟩ := hs₁
    have hn0 : x.n ≠ 0 := by
      rintro h
      rw [h] at hj
      omega
    have hu : j / x.n < x.n := Nat.div_lt_of_lt_mul hj
    have hv : j % x.n < x.n := Nat.mod_lt _ (Nat.pos_of_ne_zero hn0)
    let u := j / x.n
    let v := j % x.n
    let s₂ := s₁.setReg 526 u
    have he₂ : Exec W (.assign 526 (.op .div (.reg 525) (.reg 520))) s₁ s₂ 4 :=
      .assign (eval_div (eval_reg h525 (by omega)) (eval_reg h520 hn) hn0)
    let s₃ := s₂.setReg 527 v
    have he₃ : Exec W (.assign 527 (.op .mod (.reg 525) (.reg 520))) s₂ s₃ 4 :=
      .assign (eval_mod (eval_reg (by simp [s₂, h525]) (by omega))
        (eval_reg (by simp [s₂, h520]) hn) hn0)
    have h526₃ : s₃.regs 526 = u := by simp [s₃, s₂]
    have h527₃ : s₃.regs 527 = v := by simp [s₃]
    have hr₃ : ∀ r, r ≠ 526 → r ≠ 527 → s₃.regs r = s₁.regs r := fun r h1 h2 => by
      simp [s₃, s₂, State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2]
    have hcond := eval_lt (w := W) (A := .reg 526) (B := .reg 527)
      (eval_reg h526₃ (by omega)) (eval_reg h527₃ (by omega)) hw
    have htest := dpPairTest_row_iff x hj
    have hsucc := dpPairPrefix_succ x hj
    by_cases huv : u < v
    · rw [ite_eq_left huv] at hcond
      let s₄ := (s₃.setReg 528 0).setReg 529 0
      have he₄ : Exec W (.seq (.assign 528 (.const 0)) (.assign 529 (.const 0))) s₃ s₄ 4 :=
        .seq (.assign (eval_const (by omega))) (.assign (eval_const (by omega)))
      have hr₄ : ∀ r, r ≠ 528 → r ≠ 529 → s₄.regs r = s₃.regs r := fun r h1 h2 => by
        simp [s₄, State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2]
      obtain ⟨s₅, t₅, he₅, ht₅, harr₅, hreg₅, hle₅, hiff₅⟩ := dpCount_exec x (by omega) hn
        (u := u) (v := v) (by omega) (by omega) (s := s₄) (by simp [s₄, s₃, s₂, hin])
        (by rw [hr₄ 522 (by decide) (by decide), hr₃ 522 (by decide) (by decide), h522])
        (by rw [hr₄ 526 (by decide) (by decide), h526₃])
        (by rw [hr₄ 527 (by decide) (by decide), h527₃])
        (by simp [s₄]) (by simp [s₄])
      have hr₅ : ∀ r, r < 526 → s₅.regs r = s₁.regs r := fun r hr => by
        rw [hreg₅ r (lt_trans hr (by decide)), hr₄ r (Nat.ne_of_lt (lt_trans hr (by decide)))
          (Nat.ne_of_lt (lt_trans hr (by decide))), hr₃ r (Nat.ne_of_lt hr)
          (Nat.ne_of_lt (lt_trans hr (by decide)))]
      have harr₅' : s₅.arrs = s₁.arrs := by rw [harr₅]; rfl
      have he₄a : Exec W (.assign 528 (.const 0)) s₃ (s₃.setReg 528 0) 2 :=
        .assign (eval_const (by omega))
      have he₄b : Exec W (.assign 529 (.const 0)) (s₃.setReg 528 0) s₄ 2 :=
        .assign (eval_const (by omega))
      by_cases hc : s₅.regs 528 = 0
      · have hnt : ¬ dpPairTest x (finProdFinEquiv.symm ⟨j, hj⟩) := by
          rw [htest]
          rintro ⟨-, hm⟩
          exact (hiff₅.2 hm) hc
        have he₆ : Exec W (.ite (.reg 528) (bufPush2 503 523 526 527) .skip) s₅ s₅ 2 :=
          .ite_false (eval_reg hc (by omega)) (.skip _)
        refine ⟨s₅, _, .seq he₂ (.seq he₃ (.ite_true hcond one_ne_zero
          (.seq he₄a (.seq he₄b (.seq he₅ he₆))))), by simp only [Expr.cost]; omega,
          hinv.keep (hr₅ 520 (by decide)) (hr₅ 522 (by decide)) (hr₅ 524 (by decide))
            (hr₅ 523 (by decide)) harr₅' (by rw [hsucc, ite_eq_right hnt, List.append_nil]), ?_⟩
        rw [hr₅ 525 (by decide), h525]
      · have ht' : dpPairTest x (finProdFinEquiv.symm ⟨j, hj⟩) := htest.2 ⟨huv, hiff₅.1 hc⟩
        have hpre : dpPairPrefix x (j + 1) = dpPairPrefix x j ++ [finProdFinEquiv.symm ⟨j, hj⟩] := by
          rw [hsucc, ite_eq_left ht']
        have hlen := dpPairPrefix_length_le x hx (j + 1)
        rw [hpre, List.length_append, List.length_singleton] at hlen
        let len := (dpPairPrefix x j).length
        let pfx := k :: flatEdges (dpPairPrefix x j)
        have hpfx : pfx.length = 1 + 2 * len := by simp [pfx, len]; omega
        have hbuf : s₅.arrs 503 = pfx ++ List.replicate ((2 * k - 2 * len - 2) + 2) 0 := by
          rw [harr₅', h503, show (2 * k - 2 * len - 2) + 2 = 2 * k - 2 * len by omega]
        obtain ⟨s₆, t₆, he₆', ht₆, hbuf₆, hpos₆, harr₆, hreg₆⟩ :=
          bufPush2_exec (w := W) 503 523 526 527 pfx (2 * k - 2 * len - 2) u v (by omega)
            (by omega) (by omega) (by omega) hbuf
            (by rw [hr₅ 523 (by decide), h523, hpfx])
            (by rw [hreg₅ 526 (by decide), hr₄ 526 (by decide) (by decide), h526₃])
            (by rw [hreg₅ 527 (by decide), hr₄ 527 (by decide) (by decide), h527₃])
        have he₆ : Exec W (.ite (.reg 528) (bufPush2 503 523 526 527) .skip) s₅ s₆ (1 + t₆) :=
          .ite_true (eval_reg rfl (by omega)) hc he₆'
        have hr₆ : ∀ r, r < 526 → r ≠ 523 → s₆.regs r = s₁.regs r := fun r hr hr' => by
          rw [hreg₆ r hr', hr₅ r hr]
        have hfa : ∀ a, a ≠ 503 → s₆.arrs a = s₁.arrs a := fun a ha => by
          rw [harr₆ a ha, harr₅']
        refine ⟨s₆, _, .seq he₂ (.seq he₃ (.ite_true hcond one_ne_zero
          (.seq he₄a (.seq he₄b (.seq he₅ he₆))))), by simp only [Expr.cost]; omega,
          ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [State.setReg_regs_ne _ _ (by decide), hr₆ 520 (by decide) (by decide), h520]
        · rw [State.setReg_regs_ne _ _ (by decide), hr₆ 522 (by decide) (by decide), h522]
        · rw [State.setReg_regs_ne _ _ (by decide), hr₆ 524 (by decide) (by decide), h524]
        · rw [State.setReg_arrs, hfa inArr (by decide), hin]
        · rw [State.setReg_arrs, hfa 501 (by decide), h501]
        · rw [State.setReg_arrs, hbuf₆, hpre, flatEdges_append_single, List.length_append,
            List.length_singleton, show 2 * k - 2 * (len + 1) = 2 * k - 2 * len - 2 by omega]
          rfl
        · rw [State.setReg_regs_ne _ _ (by decide), hpos₆, hpre, List.length_append, hpfx]
          simp [len]
          omega
        · rw [hr₆ 525 (by decide) (by decide), h525]
    · rw [ite_eq_right huv] at hcond
      have hnt : ¬ dpPairTest x (finProdFinEquiv.symm ⟨j, hj⟩) := by
        rw [htest]
        exact fun h => huv h.1
      refine ⟨s₃, _, .seq he₂ (.seq he₃ (.ite_false hcond (.skip _))),
        by simp only [Expr.cost]; omega,
        hinv.keep (hr₃ 520 (by decide) (by decide)) (hr₃ 522 (by decide) (by decide))
          (hr₃ 524 (by decide) (by decide)) (hr₃ 523 (by decide) (by decide)) rfl
          (by rw [hsucc, ite_eq_right hnt, List.append_nil]), ?_⟩
      rw [hr₃ 525 (by decide) (by decide), h525]
  obtain ⟨s', t, he, ht, hI⟩ := forUp_exec' (DPScanInv x E) (x.n * x.n) (40 + 41 * k) hw
    (by omega) (fun i _ s' hs' => ⟨hs'.1, eval_reg hs'.2.2.2.1 (by omega)⟩) hbody s hs
  refine ⟨s', t, he, ?_, hI⟩
  have h : 7 + (40 + 41 * k) = 47 + 41 * k := by omega
  simpa [h] using ht

/-! ### The whole rewriting program -/

theorem flatEdges_lt {n : ℕ} (L : List (Fin n × Fin n)) : ∀ y ∈ flatEdges L, y < n := by
  intro y hy
  simp only [flatEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hy
  obtain ⟨e, -, rfl | rfl⟩ := hy
  · exact e.1.2
  · exact e.2.2

/-- The program `dpTerminatedProg k` replaces a disjoint-paths instance with
distinct terminals by the input of II (3.2) for its terminated graph. -/
theorem dpTerminatedProg_exec (x : DPInput k) (hx : IsTermination x) {W : ℕ}
    (hW : (4 * k + 20) * (x.n + 1) ^ 2 < 2 ^ W) {s : State} (hs : s.arrs inArr = encDPIn x) :
    ∃ s' t, Exec W (dpTerminatedProg k) s s' t ∧ t ≤ (400 + 100 * k) * (x.n + 1) ^ 2 ∧
      s'.arrs inArr = (dpMultiInput x hx).enc := by
  have hm := x.G.numActivePairs_le_sq
  have hm' := (x.G.cap 0).numActivePairs_le_sq
  have hE := lemma_4_4_cap_numEdges_le 0 x.G
  have hlenG := x.G.length_enc
  have hlenE := (x.G.cap 0).length_enc
  have hS : x.n * x.n + 1 ≤ (x.n + 1) ^ 2 := by nlinarith
  have hkS : k * (x.n * x.n) + k ≤ k * (x.n + 1) ^ 2 := by
    rw [← Nat.mul_add_one]
    exact Nat.mul_le_mul_left _ hS
  have e1 : (4 * k + 20) * (x.n + 1) ^ 2 = 4 * (k * (x.n + 1) ^ 2) + 20 * (x.n + 1) ^ 2 := by
    ring
  have hnn : x.n ≤ x.n * x.n := Nat.le_mul_self x.n
  rw [e1] at hW
  generalize (x.n + 1) ^ 2 = S at hS hkS hW ⊢
  generalize hKS : k * S = KS at hkS hW
  generalize hNN : x.n * x.n = NN at hS hkS hm hm' hE hnn
  have hE' : (x.G.cap 0).numEdges ≤ NN := by simpa using hE
  have hw : 1 < 2 ^ W := by omega
  have t1 : 3 < 2 ^ W := by omega
  have t2 : x.n < 2 ^ W := by omega
  have t3 : 2 + 3 * x.G.numActivePairs < 2 ^ W := by omega
  have t4 : (x.G.cap 0).numEdges < 2 ^ W := by omega
  have t5 : x.G.enc.length + 2 * k + 3 < 2 ^ W := by omega
  have t6 : x.n * x.n + x.n + 2 < 2 ^ W := by rw [hNN]; omega
  -- 1. cap the multiplicities at one
  obtain ⟨s₁, t₁, he₁, ht₁, hdst₁, -, -, -, harr₁, -⟩ :=
    capMultiDigraphProg_exec x.G 0 (encDPPairs x.pairs) inArr 500 501 500 (by decide)
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) hs
  have hin₁ : s₁.arrs inArr = x.G.enc ++ encDPPairs x.pairs := by
    rw [harr₁ inArr (by decide) (by decide), hs]
    rfl
  -- 2. the header
  obtain ⟨h0, hv0⟩ := enc_getElem_zero x.G (encDPPairs x.pairs) hin₁
  obtain ⟨h1, hv1⟩ := enc_getElem_one x.G (encDPPairs x.pairs) hin₁
  let s₂ := s₁.setReg 520 x.n
  have he₂ : Exec W (.assign 520 (.read inArr (.const 0))) s₁ s₂ 3 :=
    .assign (eval_read_of_getElem? (eval_const (by omega))
      (List.getElem?_eq_some_iff.2 ⟨h0, hv0⟩) (by omega))
  let s₃ := s₂.setReg 521 x.G.numActivePairs
  have he₃ : Exec W (.assign 521 (.read inArr (.const 1))) s₂ s₃ 3 :=
    .assign (eval_read_of_getElem? (eval_const (by omega))
      (List.getElem?_eq_some_iff.2 ⟨h1, hv1⟩) (by omega))
  let s₄ := s₃.setReg 522 (2 + 3 * x.G.numActivePairs)
  have he₄ : Exec W (.assign 522 (.op .add (.const 2) (.op .mul (.const 3) (.reg 521)))) s₃ s₄ 6 :=
    .assign (eval_add (eval_const (by omega))
      (eval_mul (eval_const (by omega)) (eval_reg (by simp [s₃]) (by omega)) (by omega))
      (by omega))
  let s₅ := s₄.setArr 503 (List.replicate (1 + 2 * k) 0)
  have he₅ : Exec W (.alloc 503 (.const (1 + 2 * k))) s₄ s₅ (1 + (1 + 2 * k)) :=
    .alloc (eval_const (by omega))
  let s₆ := s₅.writeArr 503 0 k
  have he₆ : Exec W (.write 503 (.const 0) (.const k)) s₅ s₆ 3 :=
    .write (eval_const (by omega)) (eval_const (by omega)) (by simp [s₅])
  let s₇ := s₆.setReg 523 1
  have he₇ : Exec W (.assign 523 (.const 1)) s₆ s₇ 2 := .assign (eval_const hw)
  let s₈ := s₇.setReg 524 (x.n * x.n)
  have he₈ : Exec W (.assign 524 (.op .mul (.reg 520) (.reg 520))) s₇ s₈ 4 :=
    .assign (eval_mul (eval_reg (by simp [s₇, s₆, s₅, s₄, s₃, s₂]) (by omega))
      (eval_reg (by simp [s₇, s₆, s₅, s₄, s₃, s₂]) (by omega)) (by omega))
  let s₉ := s₈.setReg 525 0
  have he₉ : Exec W (.assign 525 (.const 0)) s₈ s₉ 2 := .assign (eval_const (by omega))
  have hheader : Exec W (dpHeaderProg k) s₁ s₉ _ :=
    Exec.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ (.seq he₈ he₉))))))
  have hinv : DPScanInv x (x.G.cap 0).enc 0 s₉ := by
    refine ⟨by simp [s₉], by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂],
      by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, hlenG], by simp [s₉, s₈, hNN], ?_, ?_, ?_,
      by simp [s₉, s₈, s₇, dpPairPrefix]⟩
    · simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, State.setReg_arrs, State.writeArr_arrs_ne _ _ _
        (by decide : inArr ≠ 503), State.setArr_arrs_ne _ _ (by decide : inArr ≠ 503)]
      rw [harr₁ inArr (by decide) (by decide), hs]
    · simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, State.setReg_arrs, State.writeArr_arrs_ne _ _ _
        (by decide : (501 : Arr) ≠ 503), State.setArr_arrs_ne _ _ (by decide : (501 : Arr) ≠ 503)]
      exact hdst₁
    · simp only [s₉, s₈, s₇, s₆, s₅, State.setReg_arrs, State.writeArr_arrs_self,
        State.setArr_arrs_self]
      simp [dpPairPrefix, flatEdges, Nat.add_comm 1, List.replicate_succ]
  -- 3. the scan
  obtain ⟨s₁₀, t₁₀, he₁₀, ht₁₀, hinv₁₀⟩ := dpScan_exec x hx (x.G.cap 0).enc t5 t6 hinv
  obtain ⟨-, -, -, -, -, h501, h503, -⟩ := hinv₁₀
  have hfull := dpPairList_length x hx
  rw [dpPairPrefix_full x] at h503
  change ((List.ofFn fun j : Fin (x.n * x.n) => finProdFinEquiv.symm j).filter
    fun p => decide (dpPairTest x p)).length = k at hfull
  rw [show ((dpRowPairs x.n).filter fun p => decide (dpPairTest x p)) =
    (List.ofFn fun j : Fin (x.n * x.n) => finProdFinEquiv.symm j).filter
      fun p => decide (dpPairTest x p) from rfl, hfull, Nat.sub_self, List.replicate_zero,
    List.append_nil] at h503
  -- 4. join the two arrays
  obtain ⟨s₁₁, t₁₁, he₁₁, ht₁₁, hdst₁₁, -, -⟩ :=
    gm02ConcatArraysProg_exec (w := W) 501 503 inArr (by decide) (by decide) _ _ s₁₀ h501 h503 hw
      (by rw [List.length_cons, length_flatEdges, hfull, hlenE]; omega)
      (MultiDigraph.enc_lt _ (by omega) (by omega) fun u v =>
        lt_of_le_of_lt (x.G.cap_edgeMult_le_succ 0 u v) (by omega))
      (by
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · exact lt_of_lt_of_le (flatEdges_lt _ y hy) (by omega))
  refine ⟨s₁₁, _, .seq he₁ (.seq hheader (.seq he₁₀ he₁₁)), ?_, ?_⟩
  · simp only [length_flatEdges, hfull, List.length_cons] at ht₁₁
    have e2 : NN * (47 + 41 * k) = 47 * NN + 41 * (k * NN) := by ring
    rw [hNN, e2] at ht₁₀
    have e3 : (400 + 100 * k) * S = 400 * S + 100 * (k * S) := by ring
    rw [e3, hKS]
    rw [hlenE] at ht₁₁
    omega
  · rw [hdst₁₁, dpMultiInput_enc]
    simp

end GraphMinor.Compute
