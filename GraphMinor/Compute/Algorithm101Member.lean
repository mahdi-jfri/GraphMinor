module

public import GraphMinor.Compute.Algorithm101MemberInd

/-!
# Member Boundary, Interior Check, and Walk Tracing Gadgets for Algorithm (10.1)

This file implements and verifies the member boundary builder (`buildMemberBoundaryProg`),
interior member check (`checkMemberInteriorProg`), and Menger path-system walk tracer
(`traceWalkStopBProg`) used by Algorithm (10.1).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-- Prefix of `memberBoundaryList corners K_eList r` over `(r.vList).take k`. -/
def memberBoundaryPrefix (corners : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) (k : ℕ) : List ℕ :=
  (r.vList.take k).filter (isMemberBoundaryVert corners K_eList r)

theorem memberBoundaryPrefix_zero (corners : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) :
    memberBoundaryPrefix corners K_eList r 0 = [] := rfl

theorem memberBoundaryPrefix_full (corners : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) :
    memberBoundaryPrefix corners K_eList r r.vList.length =
      memberBoundaryList corners K_eList r := by
  simp [memberBoundaryPrefix, memberBoundaryList]

theorem memberBoundaryPrefix_succ (corners : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) {k : ℕ} (hk : k < r.vList.length) :
    memberBoundaryPrefix corners K_eList r (k + 1) =
      if isMemberBoundaryVert corners K_eList r (r.vList[k]'hk) then
        memberBoundaryPrefix corners K_eList r k ++ [r.vList[k]'hk]
      else
        memberBoundaryPrefix corners K_eList r k := by
  unfold memberBoundaryPrefix
  rw [take_add_one_eq_append_getElem r.vList k hk, List.filter_append]
  by_cases h : isMemberBoundaryVert corners K_eList r (r.vList[k]'hk) <;> simp [h]

theorem length_memberBoundaryPrefix_le (corners : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) (k : ℕ) :
    (memberBoundaryPrefix corners K_eList r k).length ≤ r.vList.length := by
  unfold memberBoundaryPrefix
  exact Nat.le_trans (List.length_filter_le _ _) (List.length_take_le' _ _)

/-- Loop body for `buildMemberBoundaryProg`: reads `v = a_rVList[r_base]`, tests
`0 < (a_degR[v] < a_degK[v]) + a_isCorner[v]`, and appends `v` to `a_buf` if true.
Uses scratch registers `r_base + 1 .. r_base + 4`. -/
def buildMemberBoundaryBody (a_degK a_degR a_isCorner a_rVList a_buf : Arr)
    (r_bdLen r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_rVList (.reg r_base)))
    (.seq (.assign (r_base + 2) (.read a_degR (.reg (r_base + 1))))
      (.seq (.assign (r_base + 3) (.read a_degK (.reg (r_base + 1))))
        (.seq (.assign (r_base + 4) (.read a_isCorner (.reg (r_base + 1))))
          (.seq (.assign (r_base + 2)
              (.op .lt (.const 0)
                (.op .add (.op .lt (.reg (r_base + 2)) (.reg (r_base + 3))) (.reg (r_base + 4)))))
            (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
              (appendWordProg a_buf r_bdLen (.reg (r_base + 1)))
              .skip)))))

/-- Build `memberBoundaryList p.corners p.K_eList r` in `a_bdOut` and its length in `r_bdLen`.
Uses scratch array `a_buf` and scratch registers `r_base .. r_base + 4`. -/
def buildMemberBoundaryProg (a_degK a_degR a_isCorner a_rVList a_buf a_bdOut : Arr)
    (r_vlen r_bdLen r_base : Reg) : Cmd :=
  .seq (initPrefixBufferProg a_buf (.reg r_vlen) r_bdLen)
    (.seq (.assign r_base (.const 0))
      (.seq (forUp r_base (.reg r_vlen)
          (buildMemberBoundaryBody a_degK a_degR a_isCorner a_rVList a_buf r_bdLen r_base))
        (copyBufPrefixProg a_buf a_bdOut r_bdLen r_base)))

theorem buildMemberBoundaryLoop_exec {w n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (hv_lt : ∀ v ∈ r.vList, v < n)
    (a_degK a_degR a_isCorner a_rVList a_buf r_vlen r_bdLen r_base : ℕ)
    (hne_kb : a_degK ≠ a_buf) (hne_rb : a_degR ≠ a_buf)
    (hne_cb : a_isCorner ≠ a_buf) (hne_vb : a_rVList ≠ a_buf)
    (hr_vlen : r_vlen < r_base) (hr_bd : r_bdLen < r_base) (hne_vb_reg : r_vlen ≠ r_bdLen)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hKlen_w : p.K_eList.length < 2 ^ w) (hrlen_w : r.eList.length < 2 ^ w)
    (hvlen_w : r.vList.length + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = r.vList.length) :
    ∀ (cap : ℕ),
      rem ≤ cap →
      ∀ {s : State},
        s.arrs a_degK = List.ofFn (fun v : Fin n => incEdgeCount p.K_eList v.1) →
        s.arrs a_degR = List.ofFn (fun v : Fin n => incEdgeCount r.eList v.1) →
        s.arrs a_isCorner = bitSetList (Finset.univ.filter (fun v : Fin n => v.1 ∈ p.corners)) →
        s.arrs a_rVList = r.vList →
        IsPrefixBuffer a_buf (memberBoundaryPrefix p.corners p.K_eList r k) cap s →
        s.regs r_vlen = r.vList.length →
        s.regs r_bdLen = (memberBoundaryPrefix p.corners p.K_eList r k).length →
        s.regs r_base = k →
        ∃ s' t,
          Exec w (forUp r_base (.reg r_vlen)
            (buildMemberBoundaryBody a_degK a_degR a_isCorner a_rVList a_buf r_bdLen r_base))
            s s' t ∧
          t ≤ 3 + 38 * rem ∧
          ∃ cap' : ℕ,
            IsPrefixBuffer a_buf (memberBoundaryList p.corners p.K_eList r) cap' s' ∧
            s'.regs r_bdLen = (memberBoundaryList p.corners p.K_eList r).length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r_reg < r_base, r_reg ≠ r_bdLen → s'.regs r_reg = s.regs r_reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  induction rem generalizing k with
  | zero =>
    intro cap _ s hdegK hdegR hisC hrV hbuf hrvlen hrbd hrbase
    have hk_eq : k = r.vList.length := by omega
    rw [hk_eq] at hrbase hbuf hrbd
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_vlen)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrvlen,
        show r.vList.length < 2 ^ w by omega, h0_w]
    rw [memberBoundaryPrefix_full] at hbuf hrbd
    exact ⟨s, 3, .while_false hcond, by omega, cap, hbuf, hrbd,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    intro cap hcap s hdegK hdegR hisC hrV hbuf hrvlen hrbd hrbase
    have hk_lt : k < r.vList.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_vlen)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrvlen,
        hk_w, show r.vList.length < 2 ^ w by omega, hk_lt, hw]
    let v := r.vList[k]'hk_lt
    have hv_mem : v ∈ r.vList := List.getElem_mem hk_lt
    have hv_n : v < n := hv_lt v hv_mem
    have hv_w : v < 2 ^ w := Nat.lt_trans hv_n hn_w
    let dR := incEdgeCount r.eList v
    let dK := incEdgeCount p.K_eList v
    let c := if v ∈ p.corners then 1 else 0
    have hdR_w : dR < 2 ^ w := Nat.lt_of_le_of_lt (incEdgeCount_le_length _ _) hrlen_w
    have hdK_w : dK < 2 ^ w := Nat.lt_of_le_of_lt (incEdgeCount_le_length _ _) hKlen_w
    have hc_w : c < 2 ^ w := by dsimp [c]; split_ifs <;> omega
    let s₁ := s.setReg (r_base + 1) v
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_rVList (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrbase, hk_w, hrV, hk_lt, v, hv_w])
    let s₂ := s₁.setReg (r_base + 2) dR
    have hex₂ : Exec w (.assign (r_base + 2) (.read a_degR (.reg (r_base + 1)))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hv_w, hdegR, hv_n, dR, hdR_w])
    let s₃ := s₂.setReg (r_base + 3) dK
    have hex₃ : Exec w (.assign (r_base + 3) (.read a_degK (.reg (r_base + 1)))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, Expr.eval, checkWord, hv_w, hdegK, hv_n, dK, hdK_w])
    let s₄ := s₃.setReg (r_base + 4) c
    have hex₄ : Exec w (.assign (r_base + 4) (.read a_isCorner (.reg (r_base + 1)))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hv_w, hisC, hv_n, bitSetList, c, hc_w])
    let isBd := if isMemberBoundaryVert p.corners p.K_eList r v then 1 else 0
    have hisBd_eq : (if 0 < (if dR < dK then 1 else 0) + c then 1 else 0) = isBd := by
      have hdR_eq : r.eList.countP (fun e => decide (e.1 = v ∨ e.2.1 = v)) = dR := rfl
      have hdK_eq : p.K_eList.countP (fun e => decide (e.1 = v ∨ e.2.1 = v)) = dK := rfl
      dsimp only [isBd, c]
      rw [isMemberBoundaryVert_eq_decide_countP_lt p hr v, hdR_eq, hdK_eq]
      by_cases hlt_d : dR < dK <;>
        by_cases hmem_c : v ∈ p.corners <;>
        simp [hv_mem, hlt_d, hmem_c]
    have heval_bd :
        (Expr.op .lt (.const 0)
          (.op .add (.op .lt (.reg (r_base + 2)) (.reg (r_base + 3))) (.reg (r_base + 4)))).eval
          w s₄ = some isBd := by
      have hlt_w : (if dR < dK then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      have hsum_w : (if dR < dK then 1 else 0) + c < 2 ^ w := by dsimp [c]; split_ifs <;> omega
      rw [← hisBd_eq]
      simp [s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hdR_w, hdK_w, hlt_w, hc_w, hsum_w, h0_w]
      split_ifs <;> omega
    let s₅ := s₄.setReg (r_base + 2) isBd
    have hex₅ :
        Exec w (.assign (r_base + 2)
          (.op .lt (.const 0)
            (.op .add (.op .lt (.reg (r_base + 2)) (.reg (r_base + 3))) (.reg (r_base + 4)))))
          s₄ s₅ 8 :=
      .assign heval_bd
    have hstep_if :
        ∃ s₆ t₆,
          Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
            (appendWordProg a_buf r_bdLen (.reg (r_base + 1))) .skip) s₅ s₆ t₆ ∧
          t₆ ≤ 11 ∧
          ∃ cap₁ : ℕ,
            rem ≤ cap₁ ∧
            IsPrefixBuffer a_buf (memberBoundaryPrefix p.corners p.K_eList r (k + 1)) cap₁ s₆ ∧
            s₆.regs r_bdLen = (memberBoundaryPrefix p.corners p.K_eList r (k + 1)).length ∧
            s₆.regs r_base = k ∧
            (∀ a : ℕ, a ≠ a_buf → s₆.arrs a = s.arrs a) ∧
            (∀ r_reg < r_base, r_reg ≠ r_bdLen → s₆.regs r_reg = s.regs r_reg) := by
      by_cases hbd : isMemberBoundaryVert p.corners p.K_eList r v
      · have hisBd1 : isBd = 1 := by simp [isBd, hbd]
        have heq_cond : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₅ = some 1 := by
          simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hisBd1, hw]
        have hbuf₅ :
            IsPrefixBuffer a_buf (memberBoundaryPrefix p.corners p.K_eList r k) ((cap - 1) + 1) s₅ := by
          unfold IsPrefixBuffer at hbuf ⊢
          have hrep : cap = (cap - 1) + 1 := by omega
          rw [← hrep]
          exact hbuf
        have hrbd₅ : s₅.regs r_bdLen = (memberBoundaryPrefix p.corners p.K_eList r k).length := by
          simp [s₅, s₄, s₃, s₂, s₁,
            show r_bdLen ≠ r_base + 1 by omega, show r_bdLen ≠ r_base + 2 by omega,
            show r_bdLen ≠ r_base + 3 by omega, show r_bdLen ≠ r_base + 4 by omega, hrbd]
        have hlen_pfx_w : (memberBoundaryPrefix p.corners p.K_eList r k).length + 1 < 2 ^ w := by
          have := length_memberBoundaryPrefix_le p.corners p.K_eList r k
          omega
        rcases appendWordProg_exec (val := v) a_buf r_bdLen (.reg (r_base + 1))
            hw hlen_pfx_w hbuf₅ hrbd₅
            (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hv_w]) with
          ⟨s₆, t₆, hex₆, ht₆, hbuf₆, hrbd₆, harr₆, hreg₆⟩
        have hsucc :
            memberBoundaryPrefix p.corners p.K_eList r (k + 1) =
              memberBoundaryPrefix p.corners p.K_eList r k ++ [v] := by
          rw [memberBoundaryPrefix_succ p.corners p.K_eList r hk_lt]
          simp [v, hbd]
        rw [← hsucc] at hbuf₆ hrbd₆
        refine ⟨s₆, 3 + t₆, .ite_true heq_cond (by omega) hex₆,
          by simp [Expr.cost] at ht₆; omega,
          cap - 1, by omega, hbuf₆, hrbd₆,
          by
            rw [hreg₆ r_base (by omega)]
            simp [s₅, s₄, s₃, s₂, s₁, hrbase],
          fun a ha => by rw [harr₆ a ha]; rfl,
          fun r_reg hr_reg hne_r => by
            rw [hreg₆ r_reg hne_r]
            simp [s₅, s₄, s₃, s₂, s₁,
              show r_reg ≠ r_base + 1 by omega, show r_reg ≠ r_base + 2 by omega,
              show r_reg ≠ r_base + 3 by omega, show r_reg ≠ r_base + 4 by omega]⟩
      · have hisBd0 : isBd = 0 := by simp [isBd, hbd]
        have heq_cond : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₅ = some 0 := by
          simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hisBd0, hw, h0_w]
        have hsucc :
            memberBoundaryPrefix p.corners p.K_eList r (k + 1) =
              memberBoundaryPrefix p.corners p.K_eList r k := by
          rw [memberBoundaryPrefix_succ p.corners p.K_eList r hk_lt]
          simp [v, hbd]
        refine ⟨s₅, 3 + 1, .ite_false heq_cond (.skip s₅), by omega,
          cap, by omega,
          by rw [hsucc]; exact hbuf,
          by
            rw [hsucc]
            simp [s₅, s₄, s₃, s₂, s₁,
              show r_bdLen ≠ r_base + 1 by omega, show r_bdLen ≠ r_base + 2 by omega,
              show r_bdLen ≠ r_base + 3 by omega, show r_bdLen ≠ r_base + 4 by omega, hrbd],
          by simp [s₅, s₄, s₃, s₂, s₁, hrbase],
          fun _ _ => rfl,
          fun r_reg hr_reg _ => by
            simp [s₅, s₄, s₃, s₂, s₁,
              show r_reg ≠ r_base + 1 by omega, show r_reg ≠ r_base + 2 by omega,
              show r_reg ≠ r_base + 3 by omega, show r_reg ≠ r_base + 4 by omega]⟩
    rcases hstep_if with
      ⟨s₆, t₆, hex₆, ht₆, cap₁, hcap₁, hbuf₆, hrbd₆, hrbase₆, harr₆, hreg₆⟩
    let s₇ := s₆.setReg r_base (k + 1)
    have hex₇ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₆ s₇ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase₆, hk_w, hw, hk1_w])
    rcases ih (k + 1) (by omega) cap₁ hcap₁ (s := s₇)
        (by simp [s₇, harr₆ a_degK hne_kb, hdegK])
        (by simp [s₇, harr₆ a_degR hne_rb, hdegR])
        (by simp [s₇, harr₆ a_isCorner hne_cb, hisC])
        (by simp [s₇, harr₆ a_rVList hne_vb, hrV])
        hbuf₆
        (by simp [s₇, show r_vlen ≠ r_base by omega,
          hreg₆ r_vlen hr_vlen hne_vb_reg, hrvlen])
        (by simp [s₇, show r_bdLen ≠ r_base by omega, hrbd₆])
        (by simp [s₇]) with
      ⟨s₈, t₈, hex₈, ht₈, cap', hbuf₈, hrbd₈, harr₈, hreg₈⟩
    refine ⟨s₈, 3 + ((3 + (3 + (3 + (3 + (8 + t₆))))) + 4) + t₈,
      .while_true hcond (by omega)
        (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))) hex₇) hex₈,
      by omega, cap', hbuf₈, hrbd₈,
      fun a ha => (harr₈ a ha).trans (harr₆ a ha),
      fun r_reg hr_reg hne_r => by
        rw [hreg₈ r_reg hr_reg hne_r]
        simp [s₇, show r_reg ≠ r_base by omega, hreg₆ r_reg hr_reg hne_r]⟩

theorem buildMemberBoundaryProg_exec {w n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    (hv_lt : ∀ v ∈ r.vList, v < n)
    (a_degK a_degR a_isCorner a_rVList a_buf a_bdOut r_vlen r_bdLen r_base : ℕ)
    (hne_kb : a_degK ≠ a_buf) (hne_rb : a_degR ≠ a_buf)
    (hne_cb : a_isCorner ≠ a_buf) (hne_vb : a_rVList ≠ a_buf) (hne_bo : a_buf ≠ a_bdOut)
    (hr_vlen : r_vlen < r_base) (hr_bd : r_bdLen < r_base) (hne_vb_reg : r_vlen ≠ r_bdLen)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hKlen_w : p.K_eList.length < 2 ^ w) (hrlen_w : r.eList.length < 2 ^ w)
    (hvlen_w : r.vList.length + 1 < 2 ^ w)
    {s : State}
    (hdegK : s.arrs a_degK = List.ofFn (fun v : Fin n => incEdgeCount p.K_eList v.1))
    (hdegR : s.arrs a_degR = List.ofFn (fun v : Fin n => incEdgeCount r.eList v.1))
    (hisC : s.arrs a_isCorner = bitSetList (Finset.univ.filter (fun v : Fin n => v.1 ∈ p.corners)))
    (hrV : s.arrs a_rVList = r.vList)
    (hrvlen : s.regs r_vlen = r.vList.length) :
    ∃ s' t,
      Exec w (buildMemberBoundaryProg a_degK a_degR a_isCorner a_rVList a_buf a_bdOut
        r_vlen r_bdLen r_base) s s' t ∧
      t ≤ 55 * r.vList.length + 20 ∧
      s'.arrs a_bdOut = memberBoundaryList p.corners p.K_eList r ∧
      s'.regs r_bdLen = (memberBoundaryList p.corners p.K_eList r).length ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_bdOut → s'.arrs a = s.arrs a) ∧
      (∀ r_reg < r_base, r_reg ≠ r_bdLen → s'.regs r_reg = s.regs r_reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  rcases initPrefixBufferProg_exec (cap := r.vList.length) a_buf (.reg r_vlen) r_bdLen hw
      (s := s) (by simp [Expr.eval, checkWord, hrvlen, show r.vList.length < 2 ^ w by omega]) with
    ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrbd₁, harr₁, hreg₁⟩
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases buildMemberBoundaryLoop_exec p hr hv_lt
      a_degK a_degR a_isCorner a_rVList a_buf r_vlen r_bdLen r_base
      hne_kb hne_rb hne_cb hne_vb hr_vlen hr_bd hne_vb_reg
      hw2 hn_w hKlen_w hrlen_w hvlen_w r.vList.length 0 (by omega) r.vList.length (le_rfl)
      (s := s₂)
      (by simp [s₂, harr₁ a_degK hne_kb, hdegK])
      (by simp [s₂, harr₁ a_degR hne_rb, hdegR])
      (by simp [s₂, harr₁ a_isCorner hne_cb, hisC])
      (by simp [s₂, harr₁ a_rVList hne_vb, hrV])
      (by simpa [IsPrefixBuffer, memberBoundaryPrefix, s₂] using hbuf₁)
      (by simp [s₂, show r_vlen ≠ r_base by omega, hreg₁ r_vlen hne_vb_reg, hrvlen])
      (by simp [s₂, show r_bdLen ≠ r_base by omega, hrbd₁, memberBoundaryPrefix])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, cap', hbuf₃, hrbd₃, harr₃, hreg₃⟩
  have hbd_w : ∀ x ∈ memberBoundaryList p.corners p.K_eList r, x < 2 ^ w := fun x hx =>
    Nat.lt_trans (hv_lt x (List.mem_of_mem_filter hx)) hn_w
  have hbd_len_le : (memberBoundaryList p.corners p.K_eList r).length ≤ r.vList.length :=
    List.length_filter_le _ _
  rcases copyBufPrefixProg_exec a_buf a_bdOut r_bdLen r_base hne_bo hr_bd
      hbd_w hw (by omega) hbuf₃ hrbd₃ with
    ⟨s₄, t₄, hex₄, ht₄, hbdOut₄, harr₄, hreg₄⟩
  refine ⟨s₄, t₁ + (2 + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp [Expr.cost] at ht₁; omega, hbdOut₄,
    by rw [hreg₄ r_bdLen hr_bd, hrbd₃],
    fun a ha₁ ha₂ => by rw [harr₄ a ha₂, harr₃ a ha₁]; simp [s₂, harr₁ a ha₁],
    fun r_reg hr_reg hne_r => by
      rw [hreg₄ r_reg hr_reg, hreg₃ r_reg hr_reg hne_r]
      simp [s₂, show r_reg ≠ r_base by omega, hreg₁ r_reg hne_r]⟩

/-! ### Section 4: Member Interior Check (`checkMemberInteriorProg`) -/

/-- Prefix of `isMemberInterior W r` over `(r.vList).take k`. -/
def isMemberInteriorPrefix {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (r : Case3MemberRecord) (k : ℕ) : Bool :=
  (r.vList.take k).all (fun v => decide (v ∉ W.perimFinset.image Fin.val))

theorem isMemberInteriorPrefix_zero {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (r : Case3MemberRecord) :
    isMemberInteriorPrefix W r 0 = true := rfl

theorem isMemberInteriorPrefix_full {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (r : Case3MemberRecord) :
    isMemberInteriorPrefix W r r.vList.length = isMemberInterior W r := by
  simp [isMemberInteriorPrefix, isMemberInterior]

theorem isMemberInteriorPrefix_succ {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (r : Case3MemberRecord) {k : ℕ} (hk : k < r.vList.length)
    (hv : r.vList[k]'hk < n) :
    isMemberInteriorPrefix W r (k + 1) =
      (isMemberInteriorPrefix W r k && decide ((⟨r.vList[k]'hk, hv⟩ : Fin n) ∉ W.perimFinset)) := by
  have hmem_iff :
      r.vList[k]'hk ∈ W.perimFinset.image Fin.val ↔
        (⟨r.vList[k]'hk, hv⟩ : Fin n) ∈ W.perimFinset := by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨u, hu, heq⟩
      have : u = ⟨r.vList[k]'hk, hv⟩ := Fin.ext heq
      rwa [← this]
    · intro hmem
      exact ⟨⟨r.vList[k]'hk, hv⟩, hmem, rfl⟩
  unfold isMemberInteriorPrefix
  rw [take_add_one_eq_append_getElem r.vList k hk, List.all_append, List.all_cons, List.all_nil]
  simp only [Bool.and_true, hmem_iff]

/-- Loop body for `checkMemberInteriorProg`: reads `v = a_rVList[r_base]`, reads
`pbit = a_perim[v]`, and updates `r_out := r_out * (1 - pbit)`. -/
def checkMemberInteriorBody (a_perim a_rVList : Arr) (r_out r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_rVList (.reg r_base)))
    (.seq (.assign (r_base + 2) (.read a_perim (.reg (r_base + 1))))
      (.assign r_out
        (.op .mul (.reg r_out) (.op .sub (.const 1) (.reg (r_base + 2))))))

/-- Compute `if isMemberInterior W r then 1 else 0` in `r_out` from `a_perim = bitSetList W.perimFinset`
and `a_rVList = r.vList`. Uses scratch registers `r_base .. r_base + 2`. -/
def checkMemberInteriorProg (a_perim a_rVList : Arr) (r_vlen r_out r_base : Reg) : Cmd :=
  .seq (.assign r_out (.const 1))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_vlen) (checkMemberInteriorBody a_perim a_rVList r_out r_base)))

theorem checkMemberInteriorLoop_exec {w h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (r : Case3MemberRecord)
    (hv_lt : ∀ v ∈ r.vList, v < n)
    (a_perim a_rVList r_vlen r_out r_base : ℕ)
    (hr_vlen : r_vlen < r_base) (hr_out : r_out < r_base) (hne_vo : r_vlen ≠ r_out)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hvlen_w : r.vList.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = r.vList.length)
    {s : State}
    (hperim : s.arrs a_perim = bitSetList W.perimFinset)
    (hrV : s.arrs a_rVList = r.vList)
    (hrvlen : s.regs r_vlen = r.vList.length)
    (hrout : s.regs r_out = if isMemberInteriorPrefix W r k then 1 else 0)
    (hrbase : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_vlen)
        (checkMemberInteriorBody a_perim a_rVList r_out r_base)) s s' t ∧
      t ≤ 3 + 22 * rem ∧
      s'.regs r_out = (if isMemberInterior W r then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r_reg < r_base, r_reg ≠ r_out → s'.regs r_reg = s.regs r_reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = r.vList.length := by omega
    rw [hk_eq] at hrbase hrout
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_vlen)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrvlen, hvlen_w, h0_w]
    rw [isMemberInteriorPrefix_full] at hrout
    exact ⟨s, 3, .while_false hcond, by omega, hrout, fun _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < r.vList.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_vlen)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrvlen, hk_w, hvlen_w, hk_lt, hw]
    let v := r.vList[k]'hk_lt
    have hv_n : v < n := hv_lt v (List.getElem_mem hk_lt)
    have hv_w : v < 2 ^ w := Nat.lt_trans hv_n hn_w
    let u : Fin n := ⟨v, hv_n⟩
    let pbit := if u ∈ W.perimFinset then 1 else 0
    have hpbit_w : pbit < 2 ^ w := by dsimp [pbit]; split_ifs <;> omega
    let s₁ := s.setReg (r_base + 1) v
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_rVList (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrbase, hk_w, hrV, hk_lt, v, hv_w])
    let s₂ := s₁.setReg (r_base + 2) pbit
    have hex₂ : Exec w (.assign (r_base + 2) (.read a_perim (.reg (r_base + 1)))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hv_w, hperim, hv_n, bitSetList, u, pbit, hpbit_w])
    let out_next := if isMemberInteriorPrefix W r (k + 1) then 1 else 0
    have heval_out :
        (Expr.op .mul (.reg r_out) (.op .sub (.const 1) (.reg (r_base + 2)))).eval w s₂ =
          some out_next := by
      have hrout₂ : s₂.regs r_out = if isMemberInteriorPrefix W r k then 1 else 0 := by
        simp [s₂, s₁,
          show r_out ≠ r_base + 1 by omega, show r_out ≠ r_base + 2 by omega, hrout]
      have hout_prev_w : (if isMemberInteriorPrefix W r k then 1 else 0) < 2 ^ w := by
        split_ifs <;> omega
      have hsub_w : 1 - pbit < 2 ^ w := by dsimp [pbit]; split_ifs <;> omega
      have hnext_eq :
          (if isMemberInteriorPrefix W r k then 1 else 0) * (1 - pbit) = out_next := by
        dsimp [out_next, pbit]
        rw [isMemberInteriorPrefix_succ W r hk_lt hv_n]
        change (if isMemberInteriorPrefix W r k = true then 1 else 0) *
            (1 - if u ∈ W.perimFinset then 1 else 0) =
          if (isMemberInteriorPrefix W r k && decide (u ∉ W.perimFinset)) = true then 1 else 0
        cases isMemberInteriorPrefix W r k <;>
          by_cases hm : u ∈ W.perimFinset <;> simp [hm]
      rw [← hnext_eq]
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrout₂, hout_prev_w, hw, hpbit_w, hsub_w]
      split_ifs <;> omega
    let s₃ := s₂.setReg r_out out_next
    have hex₃ :
        Exec w (.assign r_out
          (.op .mul (.reg r_out) (.op .sub (.const 1) (.reg (r_base + 2))))) s₂ s₃ 6 :=
      .assign heval_out
    let s₄ := s₃.setReg r_base (k + 1)
    have hex₄ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [s₃, s₂, s₁, show r_base ≠ r_out by omega,
          Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hk_w, hw, hk1_w])
    rcases ih (k + 1) (by omega) (s := s₄)
        (by simp [s₄, s₃, s₂, s₁, hperim])
        (by simp [s₄, s₃, s₂, s₁, hrV])
        (by simp [s₄, s₃, s₂, s₁,
          show r_vlen ≠ r_base by omega, show r_vlen ≠ r_out by omega,
          show r_vlen ≠ r_base + 1 by omega, show r_vlen ≠ r_base + 2 by omega, hrvlen])
        (by simp [s₄, s₃, show r_out ≠ r_base by omega, out_next])
        (by simp [s₄]) with
      ⟨s₅, t₅, hex₅, ht₅, hrout₅, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + 6)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex₃)) hex₄) hex₅,
      by omega, hrout₅,
      fun a => by rw [harr₅ a]; rfl,
      fun r_reg hr_reg hne_r => by
        rw [hreg₅ r_reg hr_reg hne_r]
        simp [s₄, s₃, s₂, s₁,
          show r_reg ≠ r_base by omega, hne_r,
          show r_reg ≠ r_base + 1 by omega, show r_reg ≠ r_base + 2 by omega]⟩

theorem checkMemberInteriorProg_exec {w h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (r : Case3MemberRecord)
    (hv_lt : ∀ v ∈ r.vList, v < n)
    (a_perim a_rVList r_vlen r_out r_base : ℕ)
    (hr_vlen : r_vlen < r_base) (hr_out : r_out < r_base) (hne_vo : r_vlen ≠ r_out)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hvlen_w : r.vList.length < 2 ^ w)
    {s : State}
    (hperim : s.arrs a_perim = bitSetList W.perimFinset)
    (hrV : s.arrs a_rVList = r.vList)
    (hrvlen : s.regs r_vlen = r.vList.length) :
    ∃ s' t,
      Exec w (checkMemberInteriorProg a_perim a_rVList r_vlen r_out r_base) s s' t ∧
      t ≤ 22 * r.vList.length + 10 ∧
      s'.regs r_out = (if isMemberInterior W r then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r_reg < r_base, r_reg ≠ r_out → s'.regs r_reg = s.regs r_reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  let s₁ := s.setReg r_out 1
  have hex₁ : Exec w (.assign r_out (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases checkMemberInteriorLoop_exec W r hv_lt a_perim a_rVList r_vlen r_out r_base
      hr_vlen hr_out hne_vo hw2 hn_w hvlen_w r.vList.length 0 (by omega) (s := s₂)
      (by simp [s₂, s₁, hperim])
      (by simp [s₂, s₁, hrV])
      (by simp [s₂, s₁, show r_vlen ≠ r_base by omega, hne_vo, hrvlen])
      (by simp [s₂, s₁, show r_out ≠ r_base by omega, isMemberInteriorPrefix_zero])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hrout₃, harr₃, hreg₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hrout₃, harr₃,
    fun r_reg hr_reg hne_r => by
      rw [hreg₃ r_reg hr_reg hne_r]
      simp [s₂, s₁, show r_reg ≠ r_base by omega, hne_r]⟩

/-! ### Section 5: Path Tracing in Menger Path Systems (`traceWalkStopBProg`) -/

/-- Tail of a path traced from `u` in `succList` stopping when `bList[u] = 1` or `¬ (succList[u] < n)`. -/
def traceWalkTail (succList bList : List ℕ) (n : ℕ) : ℕ → ℕ → List ℕ × ℕ
  | 0, u => ([], u)
  | k + 1, u =>
    if bList.getD u 0 = 1 then
      ([], u)
    else
      let nxt := succList.getD u n
      if nxt < n then
        let res := traceWalkTail succList bList n k nxt
        (nxt :: res.1, res.2)
      else
        ([], u)

/-- Full vertex list and endpoint of a path traced from `u` for up to `steps` steps. -/
def traceWalkList (succList bList : List ℕ) (n steps u : ℕ) : List ℕ × ℕ :=
  let res := traceWalkTail succList bList n steps u
  (u :: res.1, res.2)

theorem length_traceWalkTail_le (succList bList : List ℕ) (n : ℕ) :
    ∀ (steps u : ℕ), (traceWalkTail succList bList n steps u).1.length ≤ steps
  | 0, _ => le_rfl
  | k + 1, u => by
    unfold traceWalkTail
    dsimp only
    split_ifs
    · exact Nat.zero_le _
    · dsimp only [List.length_cons]
      exact Nat.succ_le_succ (length_traceWalkTail_le succList bList n k _)
    · exact Nat.zero_le _

theorem traceWalkTail_lt (succList bList : List ℕ) (n : ℕ) :
    ∀ (steps : ℕ) {u : ℕ}, u < n →
      (∀ x ∈ (traceWalkTail succList bList n steps u).1, x < n) ∧
        (traceWalkTail succList bList n steps u).2 < n
  | 0, u, hu => ⟨by simp [traceWalkTail], hu⟩
  | k + 1, u, hu => by
    unfold traceWalkTail
    dsimp only
    split_ifs with hb hnxt
    · exact ⟨by simp, hu⟩
    · rcases traceWalkTail_lt succList bList n k hnxt with ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hnxt
      · exact h1 x hx'
    · exact ⟨by simp, hu⟩

theorem traceWalkList_eq_traceWalkStopB {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ) :
    ∀ (steps : ℕ) (u₀ : Fin n),
      traceWalkList (List.ofFn succ) (bitSetList B) n steps u₀.1 =
        ((traceWalkStopB hsys steps u₀).2.support.map Fin.val,
         (traceWalkStopB hsys steps u₀).1.1)
  | 0, u₀ => by
    simp [traceWalkList, traceWalkTail, traceWalkStopB]
  | k + 1, u₀ => by
    unfold traceWalkList
    conv_lhs => unfold traceWalkTail
    have hb_getD : (bitSetList B).getD u₀.1 0 = if u₀ ∈ B then 1 else 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [u₀.2])]
      simp [bitSetList]
    have hsucc_getD : (List.ofFn succ).getD u₀.1 n = succ u₀ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [u₀.2])]
      simp
    rw [hb_getD, hsucc_getD]
    by_cases huB : u₀ ∈ B
    · rw [traceWalkStopB_succ_of_mem_B hsys k u₀ huB]
      simp [huB]
    · simp only [huB, ite_false]
      by_cases hn : succ u₀ < n
      · simp only [hn, ite_true]
        let next_u : Fin n := ⟨succ u₀, hn⟩
        have ih := traceWalkList_eq_traceWalkStopB hsys k next_u
        dsimp only [traceWalkList, next_u] at ih
        rw [traceWalkStopB_succ_of_lt hsys k u₀ huB hn]
        simp [ih]
      · rw [traceWalkStopB_succ_of_not_lt hsys k u₀ huB hn]
        simp [hn]

/-- Loop body for `traceWalkStopBProg`:
Checks if `a_B[r_endOut] == 0` and `a_succ[r_endOut] < r_n`:
- If true: appends `a_succ[r_endOut]` to `a_buf` at `r_lenOut`, sets `r_endOut := a_succ[r_endOut]`,
  and decrements `r_base` (`r_rem`) by `1`.
- If false: sets `r_base := 0` to terminate the loop.
Uses scratch registers `r_base + 1 .. r_base + 3`. -/
def traceWalkStopBBody (a_succ a_B a_buf : Arr) (r_n r_endOut r_lenOut r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_B (.reg r_endOut)))
    (.seq (.assign (r_base + 2) (.read a_succ (.reg r_endOut)))
      (.seq (.assign (r_base + 3)
          (.op .mul (.op .sub (.const 1) (.reg (r_base + 1)))
            (.op .lt (.reg (r_base + 2)) (.reg r_n))))
        (.ite (.op .eq (.reg (r_base + 3)) (.const 1))
          (.seq (appendWordProg a_buf r_lenOut (.reg (r_base + 2)))
            (.seq (.assign r_endOut (.reg (r_base + 2)))
               (.assign r_base (.op .sub (.reg r_base) (.const 1)))))
          (.assign r_base (.const 0)))))

/-- Trace a path in `a_succ` starting at `r_u0` until hitting `a_B` (or `r_n` steps), storing the
vertex list in `a_pathOut`, its endpoint in `r_endOut`, and its length in `r_lenOut`.
Uses scratch array `a_buf` and scratch registers `r_base .. r_base + 3`. -/
def traceWalkStopBProg (a_succ a_B a_buf a_pathOut : Arr)
    (r_u0 r_n r_endOut r_lenOut r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.op .add (.reg r_n) (.const 1)))
    (.seq (initPrefixBufferProg a_buf (.reg (r_base + 1)) r_lenOut)
      (.seq (appendWordProg a_buf r_lenOut (.reg r_u0))
        (.seq (.assign r_endOut (.reg r_u0))
          (.seq (.assign r_base (.reg r_n))
            (.seq (.while (.op .lt (.const 0) (.reg r_base))
                (traceWalkStopBBody a_succ a_B a_buf r_n r_endOut r_lenOut r_base))
              (copyBufPrefixProg a_buf a_pathOut r_lenOut r_base))))))

theorem traceWalkStopBLoop_exec {w n : ℕ} (succList bList : List ℕ)
    (hsucc_len : succList.length = n) (hb_len : bList.length = n)
    (hsucc_w : ∀ x ∈ succList, x < 2 ^ w) (hb_le : ∀ x ∈ bList, x ≤ 1)
    (a_succ a_B a_buf r_n r_endOut r_lenOut r_base : ℕ)
    (hne_sb : a_succ ≠ a_buf) (hne_bb : a_B ≠ a_buf)
    (hr_n : r_n < r_base) (hr_end : r_endOut < r_base) (hr_len : r_lenOut < r_base)
    (hne_ne : r_n ≠ r_endOut) (hne_nl : r_n ≠ r_lenOut) (hne_el : r_endOut ≠ r_lenOut)
    (hw : 1 < 2 ^ w) (hn_w : n + 2 < 2 ^ w)
    (rem : ℕ) :
    ∀ (u cap : ℕ) (pfx : List ℕ),
      u < n →
      rem ≤ cap →
      pfx.length + rem < 2 ^ w →
      ∀ {s : State},
        s.arrs a_succ = succList →
        s.arrs a_B = bList →
        IsPrefixBuffer a_buf pfx cap s →
        s.regs r_n = n →
        s.regs r_endOut = u →
        s.regs r_lenOut = pfx.length →
        s.regs r_base = rem →
        ∃ s' t,
          Exec w (.while (.op .lt (.const 0) (.reg r_base))
            (traceWalkStopBBody a_succ a_B a_buf r_n r_endOut r_lenOut r_base)) s s' t ∧
          t ≤ 3 + 36 * rem ∧
          ∃ cap' : ℕ,
            IsPrefixBuffer a_buf (pfx ++ (traceWalkTail succList bList n rem u).1) cap' s' ∧
            s'.regs r_endOut = (traceWalkTail succList bList n rem u).2 ∧
            s'.regs r_lenOut = (pfx ++ (traceWalkTail succList bList n rem u).1).length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, r ≠ r_endOut → r ≠ r_lenOut → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem with
  | zero =>
    intro u cap pfx _ _ _ s _ _ hbuf _ hrend hrlen hrbase
    have hcond : (Expr.op .lt (.const 0) (.reg r_base)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, h0_w]
    simp only [traceWalkTail, List.append_nil]
    exact ⟨s, 3, .while_false hcond, by omega, cap, hbuf, hrend, hrlen,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ k ih =>
    intro u cap pfx hu hcap hpfx_w s hsucc hB hbuf hrn hrend hrlen hrbase
    have hrem_w : k + 1 < 2 ^ w := by omega
    have hk_w : k < 2 ^ w := by omega
    have hu_w : u < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg r_base)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrem_w, h0_w, hw]
    have hu_b : u < bList.length := by omega
    have hu_s : u < succList.length := by omega
    let b := bList[u]'hu_b
    let nxt := succList[u]'hu_s
    have hb_getD : bList.getD u 0 = b := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu_b]; rfl
    have hnxt_getD : succList.getD u n = nxt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu_s]; rfl
    have hb_1 : b ≤ 1 := hb_le b (List.getElem_mem hu_b)
    have hb_w : b < 2 ^ w := by omega
    have hnxt_w : nxt < 2 ^ w := hsucc_w nxt (List.getElem_mem hu_s)
    let s₁ := s.setReg (r_base + 1) b
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_B (.reg r_endOut))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrend, hu_w, hB, hu_b, b, hb_w])
    let s₂ := s₁.setReg (r_base + 2) nxt
    have hex₂ : Exec w (.assign (r_base + 2) (.read a_succ (.reg r_endOut))) s₁ s₂ 3 :=
      .assign (by
        simp [s₁, show r_endOut ≠ r_base + 1 by omega,
          Expr.eval, checkWord, hrend, hu_w, hsucc, hu_s, nxt, hnxt_w])
    let cont := (1 - b) * (if nxt < n then 1 else 0)
    have heval_cont :
        (Expr.op .mul (.op .sub (.const 1) (.reg (r_base + 1)))
          (.op .lt (.reg (r_base + 2)) (.reg r_n))).eval w s₂ = some cont := by
      have hsub_w : 1 - b < 2 ^ w := by omega
      have hlt_w : (if nxt < n then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      simp [s₂, s₁,
        show r_n ≠ r_base + 1 by omega, show r_n ≠ r_base + 2 by omega, hrn,
        Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw, hb_w, hsub_w, hnxt_w, show n < 2 ^ w by omega, hlt_w, cont]
      split_ifs <;> omega
    let s₃ := s₂.setReg (r_base + 3) cont
    have hex₃ :
        Exec w (.assign (r_base + 3)
          (.op .mul (.op .sub (.const 1) (.reg (r_base + 1)))
            (.op .lt (.reg (r_base + 2)) (.reg r_n)))) s₂ s₃ 8 :=
      .assign heval_cont
    by_cases hgo : b ≠ 1 ∧ nxt < n
    · have hb0 : b = 0 := by omega
      have hnxt_lt : nxt < n := hgo.2
      have hcont1 : cont = 1 := by simp [cont, hb0, hnxt_lt]
      have heq_cond : (Expr.op .eq (.reg (r_base + 3)) (.const 1)).eval w s₃ = some 1 := by
        simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcont1, hw]
      have hbuf₃ : IsPrefixBuffer a_buf pfx ((cap - 1) + 1) s₃ := by
        unfold IsPrefixBuffer at hbuf ⊢
        have hrep : cap = (cap - 1) + 1 := by omega
        rw [← hrep]
        exact hbuf
      have hrlen₃ : s₃.regs r_lenOut = pfx.length := by
        simp [s₃, s₂, s₁,
          show r_lenOut ≠ r_base + 1 by omega, show r_lenOut ≠ r_base + 2 by omega,
          show r_lenOut ≠ r_base + 3 by omega, hrlen]
      rcases appendWordProg_exec (val := nxt) a_buf r_lenOut (.reg (r_base + 2))
          hw (by omega) hbuf₃ hrlen₃
          (by simp [s₃, s₂, Expr.eval, checkWord, hnxt_w]) with
        ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrlen₄, harr₄, hreg₄⟩
      let s₅ := s₄.setReg r_endOut nxt
      have hex₅ : Exec w (.assign r_endOut (.reg (r_base + 2))) s₄ s₅ 2 :=
        .assign (by
          rw [Expr.eval, hreg₄ (r_base + 2) (by omega)]
          simp [s₃, s₂, checkWord, hnxt_w])
      let s₆ := s₅.setReg r_base k
      have hex₆ : Exec w (.assign r_base (.op .sub (.reg r_base) (.const 1))) s₅ s₆ 4 :=
        .assign (by
          have hrbase₅ : s₅.regs r_base = k + 1 := by
            simp [s₅, show r_base ≠ r_endOut by omega, hreg₄ r_base (by omega),
              s₃, s₂, s₁, hrbase]
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase₅, hrem_w, hw, hk_w])
      rcases ih nxt (cap - 1) (pfx ++ [nxt]) hnxt_lt (by omega)
          (by rw [List.length_append]; simp; omega) (s := s₆)
          (by simp [s₆, s₅, harr₄ a_succ hne_sb, s₃, s₂, s₁, hsucc])
          (by simp [s₆, s₅, harr₄ a_B hne_bb, s₃, s₂, s₁, hB])
          hbuf₄
          (by
            simp [s₆, s₅, show r_n ≠ r_base by omega, hne_ne, hreg₄ r_n hne_nl,
              s₃, s₂, s₁,
              show r_n ≠ r_base + 1 by omega, show r_n ≠ r_base + 2 by omega,
              show r_n ≠ r_base + 3 by omega, hrn])
          (by simp [s₆, s₅, show r_endOut ≠ r_base by omega])
          (by simp [s₆, s₅, show r_lenOut ≠ r_base by omega, hne_el.symm, hrlen₄])
          (by simp [s₆]) with
        ⟨s₇, t₇, hex₇, ht₇, cap', hbuf₇, hrend₇, hrlen₇, harr₇, hreg₇⟩
      have htail_eq :
          traceWalkTail succList bList n (k + 1) u =
            (nxt :: (traceWalkTail succList bList n k nxt).1,
             (traceWalkTail succList bList n k nxt).2) := by
        conv_lhs => unfold traceWalkTail
        rw [hb_getD, hnxt_getD]
        simp [hb0, hnxt_lt]
      have happ_eq :
          (pfx ++ [nxt]) ++ (traceWalkTail succList bList n k nxt).1 =
            pfx ++ (traceWalkTail succList bList n (k + 1) u).1 := by
        rw [htail_eq, List.append_assoc, List.singleton_append]
      have hrend_eq :
          (traceWalkTail succList bList n k nxt).2 =
            (traceWalkTail succList bList n (k + 1) u).2 := by
        rw [htail_eq]
      rw [happ_eq] at hbuf₇ hrlen₇
      rw [hrend_eq] at hrend₇
      refine ⟨s₇, 3 + (3 + (3 + (8 + (3 + (t₄ + (2 + 4)))))) + t₇,
        .while_true hcond (by omega)
          (.seq hex₁ (.seq hex₂ (.seq hex₃
            (.ite_true heq_cond (by omega) (.seq hex₄ (.seq hex₅ hex₆)))))) hex₇,
        by simp [Expr.cost] at ht₄; omega,
        cap', hbuf₇, hrend₇, hrlen₇,
        fun a ha => (harr₇ a ha).trans (harr₄ a ha),
        fun r hr hne₁ hne₂ => by
          rw [hreg₇ r hr hne₁ hne₂]
          simp [s₆, s₅, show r ≠ r_base by omega, hne₁, hreg₄ r hne₂,
            s₃, s₂, s₁,
            show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega,
            show r ≠ r_base + 3 by omega]⟩
    · have hcont0 : cont = 0 := by
        dsimp [cont]
        by_cases hb1 : b = 1
        · simp [hb1]
        · have hnot_lt : ¬ nxt < n := fun h => hgo ⟨hb1, h⟩
          simp [hnot_lt]
      have heq_cond : (Expr.op .eq (.reg (r_base + 3)) (.const 1)).eval w s₃ = some 0 := by
        simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcont0, hw, h0_w]
      let s₄ := s₃.setReg r_base 0
      have hex₄ : Exec w (.assign r_base (.const 0)) s₃ s₄ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      have hcond_end : (Expr.op .lt (.const 0) (.reg r_base)).eval w s₄ = some 0 := by
        simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w]
      have htail_stop : traceWalkTail succList bList n (k + 1) u = ([], u) := by
        unfold traceWalkTail
        rw [hb_getD, hnxt_getD]
        by_cases hb1 : b = 1
        · simp [hb1]
        · have hnot_lt : ¬ nxt < n := fun h => hgo ⟨hb1, h⟩
          simp [hb1, hnot_lt]
      rw [htail_stop]
      simp only [List.append_nil]
      refine ⟨s₄, 3 + (3 + (3 + (8 + (3 + 2)))) + 3,
        .while_true hcond (by omega)
          (.seq hex₁ (.seq hex₂ (.seq hex₃ (.ite_false heq_cond hex₄))))
          (.while_false hcond_end),
        by omega, cap, hbuf,
        by simp [s₄, s₃, s₂, s₁,
          show r_endOut ≠ r_base by omega, show r_endOut ≠ r_base + 1 by omega,
          show r_endOut ≠ r_base + 2 by omega, show r_endOut ≠ r_base + 3 by omega, hrend],
        by simp [s₄, s₃, s₂, s₁,
          show r_lenOut ≠ r_base by omega, show r_lenOut ≠ r_base + 1 by omega,
          show r_lenOut ≠ r_base + 2 by omega, show r_lenOut ≠ r_base + 3 by omega, hrlen],
        fun _ _ => rfl,
        fun r hr _ _ => by
          simp [s₄, s₃, s₂, s₁,
            show r ≠ r_base by omega, show r ≠ r_base + 1 by omega,
            show r ≠ r_base + 2 by omega, show r ≠ r_base + 3 by omega]⟩

theorem traceWalkStopBProg_exec {w n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    (u₀ : Fin n)
    (a_succ a_B a_buf a_pathOut r_u0 r_n r_endOut r_lenOut r_base : ℕ)
    (hne_sb : a_succ ≠ a_buf) (_hne_sp : a_succ ≠ a_pathOut)
    (hne_bb : a_B ≠ a_buf) (_hne_bp : a_B ≠ a_pathOut) (hne_bufp : a_buf ≠ a_pathOut)
    (hr_u0 : r_u0 < r_base) (hr_n : r_n < r_base)
    (hr_end : r_endOut < r_base) (hr_len : r_lenOut < r_base)
    (_hne_un : r_u0 ≠ r_n) (_hne_ue : r_u0 ≠ r_endOut) (hne_ul : r_u0 ≠ r_lenOut)
    (hne_ne : r_n ≠ r_endOut) (hne_nl : r_n ≠ r_lenOut) (hne_el : r_endOut ≠ r_lenOut)
    (hw : 1 < 2 ^ w) (hn_w : n + 2 < 2 ^ w)
    {s : State}
    (hsucc : s.arrs a_succ = List.ofFn succ)
    (hB : s.arrs a_B = bitSetList B)
    (hru0 : s.regs r_u0 = u₀.1)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (traceWalkStopBProg a_succ a_B a_buf a_pathOut
        r_u0 r_n r_endOut r_lenOut r_base) s s' t ∧
      t ≤ 54 * n + 50 ∧
      s'.arrs a_pathOut = (traceWalkStopB hsys n u₀).2.support.map Fin.val ∧
      s'.regs r_endOut = (traceWalkStopB hsys n u₀).1.1 ∧
      s'.regs r_lenOut = ((traceWalkStopB hsys n u₀).2.support.map Fin.val).length ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_pathOut → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_endOut → r ≠ r_lenOut → s'.regs r = s.regs r) := by
  have hn1_w : n + 1 < 2 ^ w := by omega
  have hu0_w : u₀.1 < 2 ^ w := Nat.lt_trans u₀.2 (by omega)
  let s₁ := s.setReg (r_base + 1) (n + 1)
  have hex₁ : Exec w (.assign (r_base + 1) (.op .add (.reg r_n) (.const 1))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn,
      show n < 2 ^ w by omega, hw, hn1_w])
  rcases initPrefixBufferProg_exec (cap := n + 1) a_buf (.reg (r_base + 1)) r_lenOut hw
      (s := s₁) (by simp [s₁, Expr.eval, checkWord, hn1_w]) with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrlen₂, harr₂, hreg₂⟩
  have hru0₂ : s₂.regs r_u0 = u₀.1 := by
    rw [hreg₂ r_u0 hne_ul]
    simp [s₁, show r_u0 ≠ r_base + 1 by omega, hru0]
  rcases appendWordProg_exec (val := u₀.1) a_buf r_lenOut (.reg r_u0)
      hw (by simp [hw]) hbuf₂ hrlen₂
      (by simp [Expr.eval, checkWord, hru0₂, hu0_w]) with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hrlen₃, harr₃, hreg₃⟩
  have hru0₃ : s₃.regs r_u0 = u₀.1 := by rw [hreg₃ r_u0 hne_ul, hru0₂]
  let s₄ := s₃.setReg r_endOut u₀.1
  have hex₄ : Exec w (.assign r_endOut (.reg r_u0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hru0₃, hu0_w])
  have hrn₄ : s₄.regs r_n = n := by
    simp [s₄, hne_ne, hreg₃ r_n hne_nl, hreg₂ r_n hne_nl,
      s₁, show r_n ≠ r_base + 1 by omega, hrn]
  let s₅ := s₄.setReg r_base n
  have hex₅ : Exec w (.assign r_base (.reg r_n)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn₄, show n < 2 ^ w by omega])
  have hsucc_w : ∀ x ∈ List.ofFn succ, x < 2 ^ w := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    have hle := hsys.succ_le i
    omega
  have hb_le : ∀ x ∈ bitSetList B, x ≤ 1 := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    simp only [bitSetList, List.getElem_ofFn]
    split_ifs <;> omega
  rcases traceWalkStopBLoop_exec (List.ofFn succ) (bitSetList B)
      (by simp) (by simp) hsucc_w hb_le
      a_succ a_B a_buf r_n r_endOut r_lenOut r_base
      hne_sb hne_bb hr_n hr_end hr_len hne_ne hne_nl hne_el
      hw hn_w n u₀.1 n [u₀.1] u₀.2 (le_rfl) (by simp; omega) (s := s₅)
      (by simp [s₅, s₄, harr₃ a_succ hne_sb, harr₂ a_succ hne_sb, s₁, hsucc])
      (by simp [s₅, s₄, harr₃ a_B hne_bb, harr₂ a_B hne_bb, s₁, hB])
      (by simpa [IsPrefixBuffer, s₅, s₄] using hbuf₃)
      (by simp [s₅, show r_n ≠ r_base by omega, hrn₄])
      (by simp [s₅, s₄, show r_endOut ≠ r_base by omega])
      (by simp [s₅, s₄, show r_lenOut ≠ r_base by omega, hne_el.symm, hrlen₃])
      (by simp [s₅]) with
    ⟨s₆, t₆, hex₆, ht₆, cap', hbuf₆, hrend₆, hrlen₆, harr₆, hreg₆⟩
  have hwalk_eq := traceWalkList_eq_traceWalkStopB hsys n u₀
  unfold traceWalkList at hwalk_eq
  have hwalk1 :
      [u₀.1] ++ (traceWalkTail (List.ofFn succ) (bitSetList B) n n u₀.1).1 =
        (traceWalkStopB hsys n u₀).2.support.map Fin.val := by
    simpa using congrArg Prod.fst hwalk_eq
  have hwalk2 :
      (traceWalkTail (List.ofFn succ) (bitSetList B) n n u₀.1).2 =
        (traceWalkStopB hsys n u₀).1.1 :=
    congrArg Prod.snd hwalk_eq
  rw [hwalk1] at hbuf₆ hrlen₆
  rw [hwalk2] at hrend₆
  have hpath_w : ∀ x ∈ (traceWalkStopB hsys n u₀).2.support.map Fin.val, x < 2 ^ w := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨v, _, rfl⟩
    exact Nat.lt_trans v.2 (by omega)
  have hpath_le :
      ((traceWalkStopB hsys n u₀).2.support.map Fin.val).length ≤ n + 1 := by
    rw [← hwalk1, List.length_append]
    have := length_traceWalkTail_le (List.ofFn succ) (bitSetList B) n n u₀.1
    simp; omega
  have hpath_len :
      ((traceWalkStopB hsys n u₀).2.support.map Fin.val).length < 2 ^ w := by
    omega
  rcases copyBufPrefixProg_exec a_buf a_pathOut r_lenOut r_base hne_bufp hr_len
      hpath_w hw hpath_len hbuf₆ hrlen₆ with
    ⟨s₇, t₇, hex₇, ht₇, hpath₇, harr₇, hreg₇⟩
  refine ⟨s₇, 4 + (t₂ + (t₃ + (2 + (2 + (t₆ + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by simp [Expr.cost] at ht₂ ht₃; omega,
    hpath₇,
    by rw [hreg₇ r_endOut hr_end, hrend₆],
    by rw [hreg₇ r_lenOut hr_len, hrlen₆],
    fun a ha₁ ha₂ => by
      rw [harr₇ a ha₂, harr₆ a ha₁]
      simp [s₅, s₄, harr₃ a ha₁, harr₂ a ha₁, s₁],
    fun r hr hne₁ hne₂ => by
      rw [hreg₇ r hr, hreg₆ r hr hne₁ hne₂]
      simp [s₅, s₄, show r ≠ r_base by omega, hne₁, hreg₃ r hne₂, hreg₂ r hne₂,
        s₁, show r ≠ r_base + 1 by omega]⟩

end GraphMinor.Compute
