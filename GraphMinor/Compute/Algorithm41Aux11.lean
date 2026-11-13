module

public import GraphMinor.Compute.Algorithm41Aux10

/-!
# Output Array Appends for GM XIII (4.1)

This file verifies the output copying loop used to serialize models in step (4)
of GM XIII (4.1), page 76. The loop appends an array prefix to a preallocated
output buffer and preserves the arena registers and arrays.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Loop body of `append41SliceToOutProg`: reads `a_src[r_16]` into `r_17`, writes it to
`outArr[r_9]`, and increments `r_9`. -/
def append41SliceToOutBody (a_src : Arr) : Cmd :=
  .seq (.assign 17 (.read a_src (.reg 16)))
    (.seq (.write outArr (.reg 9) (.reg 17))
      (.assign 9 (.op .add (.reg 9) (.const 1))))

/-- Copies the first `r_len` words of `a_src` into `outArr` starting at `r_9`, advancing
`r_9` by `r_len`. -/
def append41SliceToOutProg (a_src : Arr) (r_len : Reg) : Cmd :=
  .seq (.assign 16 (.const 0))
    (forUp 16 (.reg r_len) (append41SliceToOutBody a_src))

theorem append41SliceToOutLoop_exec {w len cap : ℕ} (a_src : Arr) (r_len : Reg)
    (hne_src : a_src ≠ outArr)
    (hne_len16 : r_len ≠ 16) (hne_len17 : r_len ≠ 17) (hne_len165 : r_len ≠ 9)
    (pref mid extra : List ℕ)
    (hmid_len : mid.length = len)
    (hmid_w : ∀ v ∈ mid, v < 2 ^ w)
    (hcap_le : pref.length + len ≤ cap)
    (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = len) {s : State}
    (hsrc : s.arrs a_src = mid ++ extra)
    (hout : s.arrs outArr =
      (pref ++ mid.take k) ++ List.replicate (cap - (pref.length + k)) 0)
    (hrlen : s.regs r_len = len)
    (hr16 : s.regs 16 = k)
    (hr9 : s.regs 9 = pref.length + k) :
    ∃ s' t,
      Exec w (forUp 16 (.reg r_len) (append41SliceToOutBody a_src)) s s' t ∧
      t ≤ 3 + 17 * rem ∧
      s'.arrs outArr = (pref ++ mid) ++ List.replicate (cap - (pref.length + len)) 0 ∧
      s'.regs 9 = pref.length + len ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 16 → r ≠ 17 → r ≠ 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : len < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = len := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 16) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr16, hrlen, hlen_w]
    have htake : mid.take mid.length = mid := List.take_length
    rw [← hmid_len] at hout hr9 ⊢
    rw [htake] at hout
    exact ⟨s, 3, .while_false hcond, by omega, hout, hr9,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < len := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk_mid : k < mid.length := by omega
    let val := mid[k]'hk_mid
    have hval_w : val < 2 ^ w := hmid_w val (List.getElem_mem hk_mid)
    have hcond : (Expr.op .lt (.reg 16) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr16, hrlen, hk_w, hlen_w, hk_lt, hw]
    have hk_src : k < (s.arrs a_src).length := by rw [hsrc, List.length_append]; omega
    have hget_src : (s.arrs a_src)[k]'hk_src = val := by
      simp only [hsrc, List.getElem_append_left hk_mid, val]
    let s₁ := s.setReg 17 val
    have hex₁ : Exec w (.assign 17 (.read a_src (.reg 16))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr16, hk_w, hk_src, hget_src, hval_w])
    have hr9_w : pref.length + k < 2 ^ w := by omega
    have hout_idx : pref.length + k < (s₁.arrs outArr).length := by
      simp only [s₁, State.setReg_arrs, hout, List.length_append, List.length_take,
        List.length_replicate]
      omega
    let s₂ := s₁.writeArr outArr (pref.length + k) val
    have hex₂ : Exec w (.write outArr (.reg 9) (.reg 17)) s₁ s₂ 3 :=
      .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hr9, hr9_w])
        (by simp [s₁, State.setReg, Expr.eval, checkWord, hval_w])
        hout_idx
    have hr9_s₂ : s₂.regs 9 = pref.length + k := hr9
    let s₃ := s₂.setReg 9 (pref.length + k + 1)
    have hex₃ : Exec w (.assign 9 (.op .add (.reg 9) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_s₂, hr9_w, hw,
          show pref.length + k + 1 < 2 ^ w by omega])
    have hr16_s₃ : s₃.regs 16 = k := hr16
    let s₄ := s₃.setReg 16 (k + 1)
    have hex_inc : Exec w (.assign 16 (.op .add (.reg 16) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr16_s₃, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hout₄ : s₄.arrs outArr =
        (pref ++ mid.take (k + 1)) ++ List.replicate (cap - (pref.length + (k + 1))) 0 := by
      change (s.arrs outArr).set (pref.length + k) val = _
      rw [hout]
      have hlen_pt : (pref ++ mid.take k).length = pref.length + k := by
        rw [List.length_append, List.length_take]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : pref.length + k - (pref ++ mid.take k).length = 0 := by omega
      have hrep : cap - (pref.length + k) = (cap - (pref.length + (k + 1))) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      dsimp [val]
      rw [take_add_one_eq_append_getElem mid k hk_mid]
      simp only [List.append_assoc, List.singleton_append]
    rcases ih (k + 1) (by omega)
        (by simp [s₄, s₃, s₂, s₁, hne_src, hsrc])
        hout₄
        (by simp [s₄, s₃, s₂, s₁, State.setReg, hne_len16, hne_len17, hne_len165, hrlen])
        (by simp [s₄])
        (by simp [s₄, s₃, State.setReg, Nat.add_assoc]) with
      ⟨s₅, t₅, hex₅, ht₅, hout₅, hr9₅, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + 4)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex₃)) hex_inc) hex₅,
      by omega, hout₅, hr9₅,
      fun a ha => by rw [harr₅ a ha]; simp [s₄, s₃, s₂, s₁, ha],
      fun r h2 h3 h25 => by
        rw [hreg₅ r h2 h3 h25]
        simp [s₄, s₃, s₂, s₁, State.setReg, h2, h3, h25]⟩

theorem append41SliceToOutProg_exec {w len cap : ℕ} (a_src : Arr) (r_len : Reg)
    (hne_src : a_src ≠ outArr)
    (hne_len16 : r_len ≠ 16) (hne_len17 : r_len ≠ 17) (hne_len165 : r_len ≠ 9)
    (pref mid extra : List ℕ)
    (hmid_len : mid.length = len)
    (hmid_w : ∀ v ∈ mid, v < 2 ^ w)
    (hcap_le : pref.length + len ≤ cap)
    (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w) {s : State}
    (hsrc : s.arrs a_src = mid ++ extra)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hrlen : s.regs r_len = len)
    (hr9 : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (append41SliceToOutProg a_src r_len) s s' t ∧
      t ≤ 17 * len + 5 ∧
      s'.arrs outArr = (pref ++ mid) ++ List.replicate (cap - (pref.length + len)) 0 ∧
      s'.regs 9 = pref.length + len ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 16 → r ≠ 17 → r ≠ 9 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 16 0
  have hex₁ : Exec w (.assign 16 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases append41SliceToOutLoop_exec a_src r_len hne_src hne_len16 hne_len17 hne_len165
      pref mid extra hmid_len hmid_w hcap_le hw hcap_w len 0 (by omega) (s := s₁)
      hsrc
      (by simpa [s₁] using hout)
      (by simp [s₁, State.setReg, hne_len16, hrlen])
      (by simp [s₁])
      (by simp [s₁, State.setReg, hr9]) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hr9₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hout₂, hr9₂,
    fun a ha => by rw [harr₂ a ha]; rfl,
    fun r h2 h3 h25 => by
      rw [hreg₂ r h2 h3 h25]
      simp [s₁, State.setReg, h2]⟩


/-- Backtrack from one arena pointer and append its represented set as a bit list.
The arena is traversed by the backward sweep of `materializeArenaProg`. -/
def emit41ArenaSetProg (a_kd a_v1 a_v2 : Arr) (r_N r_K : Reg)
    (root : Expr) : Cmd :=
  .seq (.assign 7 root)
    (.seq (materializeArenaProg a_kd a_v1 a_v2 r_N r_K 7)
      (append41SliceToOutProg a_bits r_N))

/-- The set emitted by `emit41ArenaSetProg` is exactly the set named by its arena pointer.
The bound counts both the arena traversal and the copying of the bit list. -/
theorem emit41ArenaSetProg_exec {w N K p cap : ℕ}
    (a_kd a_v1 a_v2 r_N r_K : ℕ) (root : Expr)
    (hkd_act : a_kd ≠ a_act) (hkd_bits : a_kd ≠ a_bits)
    (hv1_act : a_v1 ≠ a_act) (hv1_bits : a_v1 ≠ a_bits)
    (hv2_act : a_v2 ≠ a_act) (hv2_bits : a_v2 ≠ a_bits)
    (hrN : r_N < 7) (hrK : r_K < 7)
    (hw : 2 < 2 ^ w) (hN_w : N < 2 ^ w) (hK_w : K < 2 ^ w)
    (hp : p < K) (pref : List ℕ) (hcap : pref.length + N ≤ cap) (hcap_w : cap < 2 ^ w)
    {s : State}
    (hwf : ArenaWF N K (s.arrs a_kd) (s.arrs a_v1) (s.arrs a_v2))
    (hregN : s.regs r_N = N) (hregK : s.regs r_K = K)
    (hroot : root.eval w s = some p)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (emit41ArenaSetProg a_kd a_v1 a_v2 r_N r_K root) s s' t ∧
      t ≤ root.cost + 42 * K + 18 * N + 21 ∧
      s'.arrs outArr =
        (pref ++ bitSetList (evalArena N (s.arrs a_kd) (s.arrs a_v1) (s.arrs a_v2) p)) ++
          List.replicate (cap - (pref.length + N)) 0 ∧
      s'.regs 9 = pref.length + N ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  let s₁ := s.setReg 7 p
  have hex₁ : Exec w (.assign 7 root) s s₁ (root.cost + 1) := .assign hroot
  rcases materializeArenaProg_exec (s := s₁) hwf hw hN_w hK_w
      hkd_act hkd_bits hv1_act hv1_bits hv2_act hv2_bits
      (show r_N < 10 by omega) (show r_K < 10 by omega) (by decide) hp
      (by simpa [s₁, State.setReg, show r_N ≠ 7 by omega] using hregN)
      (by simpa [s₁, State.setReg, show r_K ≠ 7 by omega] using hregK)
      (State.setReg_regs_self s 7 p) rfl rfl rfl with
    ⟨s₂, t₂, hex₂, ht₂, hbits₂, harr₂, hreg₂⟩
  let U := evalArena N (s.arrs a_kd) (s.arrs a_v1) (s.arrs a_v2) p
  have hbits_w : ∀ v ∈ bitSetList U, v < 2 ^ w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    have := getElem_bitSetList_le_one U i hi
    omega
  rcases append41SliceToOutProg_exec (w := w) (len := N) (cap := cap)
      a_bits r_N (by decide) (by change r_N ≠ (16 : ℕ); omega)
      (by change r_N ≠ (17 : ℕ); omega) (by change r_N ≠ (9 : ℕ); omega)
      pref (bitSetList U) [] (length_bitSetList U) hbits_w hcap (by omega) hcap_w
      (s := s₂)
      (by simpa [U] using hbits₂)
      (by rw [harr₂ outArr (by decide) (by decide)]; exact hout)
      (by rw [hreg₂ r_N (by change r_N < (10 : ℕ); omega)]; simpa [s₁, State.setReg, show r_N ≠ 7 by omega] using hregN)
      (by rw [hreg₂ 9 (by decide)]; exact hpos) with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, hpos₃, harr₃, hreg₃⟩
  refine ⟨s₃, (root.cost + 1) + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃),
    by omega, hout₃, hpos₃, ?_, ?_⟩
  · intro a ha_act ha_bits ha_out
    rw [harr₃ a ha_out, harr₂ a ha_act ha_bits]
    rfl
  · intro r hr h7 h9
    rw [hreg₃ r (by change r ≠ (16 : ℕ); omega) (by change r ≠ (17 : ℕ); omega) h9, hreg₂ r hr]
    exact State.setReg_regs_ne s p h7


/-- Array slot for a vertex or edge of a represented folio member. -/
theorem entrySlot_lt_S_tab {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)} {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s)
    (idx : Fin es.length) {u : ℕ} (hu : u < V_max δ ξ ω) :
    idx.1 * V_max δ ξ ω + u < S_tab δ ξ ω := by
  have hcount := length_allDetailLeCodes_lt_C_max δ ξ ω hbuf.hq_le
  have hidx : idx.1 + 1 ≤ C_max δ ξ ω := by have := idx.2; have := hbuf.hlen_le; omega
  calc
    idx.1 * V_max δ ξ ω + u < idx.1 * V_max δ ξ ω + V_max δ ξ ω :=
      Nat.add_lt_add_left hu _
    _ = (idx.1 + 1) * V_max δ ξ ω := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ C_max δ ξ ω * V_max δ ξ ω := Nat.mul_le_mul_right _ hidx

/-- Write the vertex and edge bit lists of one branch subgraph in a final model.
Both lists are recovered by backtracking through the stored union nodes. -/
def emit41ModelVertexProg (δ ξ ω idx u : ℕ) : Cmd :=
  .seq
    (emit41ArenaSetProg a_vkd a_vv1 a_vv2 0 r_kv
      (.read a_acc_vv (.const (idx * V_max δ ξ ω + u))))
    (emit41ArenaSetProg a_ekd a_ev1 a_ev2 1 r_ke
      (.read a_acc_ve (.const (idx * V_max δ ξ ω + u))))

/-- Execution of the model branch-subgraph output step of GM XIII (4.1), step (4), page 76. -/
theorem emit41ModelVertexProg_exec {w δ ξ ω kv ke cap : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)} {s : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z E es bufA s)
    (har : ArenaStateInv G kv ke s)
    (idx : Fin es.length) (u : Fin es[idx.1].H.digraph.numVerts)
    (hw : 2 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hkv_w : kv < 2 ^ w) (hke_w : ke < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (pref : List ℕ) (hcap : pref.length + G.numVerts + G.numEdges ≤ cap)
    (hcap_w : cap < 2 ^ w)
    (hr0 : s.regs 0 = G.numVerts) (hr1 : s.regs 1 = G.numEdges)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t,
      Exec w (emit41ModelVertexProg δ ξ ω idx.1 u.1) s s' t ∧
      t ≤ 42 * kv + 42 * ke + 18 * (G.numVerts + G.numEdges) + 46 ∧
      s'.arrs outArr =
        (pref ++ (bitSetList (es[idx.1].vertVerts u) ++ bitSetList (es[idx.1].vertEdges u))) ++
          List.replicate (cap - (pref.length + G.numVerts + G.numEdges)) 0 ∧
      s'.regs 9 = pref.length + G.numVerts + G.numEdges ∧
      (∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) := by
  let slot := idx.1 * V_max δ ξ ω + u.1
  have hdet := hbuf.hdet es[idx.1] (List.getElem_mem idx.2)
  have hslot := entrySlot_lt_S_tab hbuf idx
    (Nat.lt_trans u.2 (numVerts_lt_V_max hbuf.hq_le hdet))
  have hslot_w : slot < 2 ^ w := Nat.lt_trans hslot hS_w
  obtain ⟨hpV, heV, hpE, heE⟩ := (hbuf.hentries idx).1 u
  dsimp only [bufA] at hpV heV hpE heE
  let pV := (s.arrs a_acc_vv).getD slot 0
  let pE := (s.arrs a_acc_ve).getD slot 0
  have hpV' : pV < kv := by simpa [pV, slot, har.hr_kv] using hpV
  have hpE' : pE < ke := by simpa [pE, slot, har.hr_ke] using hpE
  have hlenV : slot < (s.arrs a_acc_vv).length := by change slot < (s.arrs bufA.a_vv).length; rw [hbuf.hvv_len]; exact hslot
  have hgetV : (s.arrs a_acc_vv)[slot] = pV := by
    simp only [pV, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlenV, Option.getD_some]
  have hrootV : (Expr.read a_acc_vv (.const slot)).eval w s = some pV := by
    simp [Expr.eval, checkWord, hslot_w, hlenV, hgetV, show pV < 2 ^ w by omega]
  rcases emit41ArenaSetProg_exec a_vkd a_vv1 a_vv2 0 r_kv
      (.read a_acc_vv (.const slot))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hw hn_w hkv_w hpV' pref (by omega) hcap_w
      har.hwfV hr0 har.hr_kv hrootV hout hpos with
    ⟨s₁, t₁, hex₁, ht₁, hout₁, hpos₁, harr₁, hreg₁⟩
  have hout₁' : s₁.arrs outArr = (pref ++ bitSetList (es[idx.1].vertVerts u)) ++
      List.replicate (cap - (pref.length + G.numVerts)) 0 := by
    simpa only [pV, slot, heV] using hout₁
  have hlenE : slot < (s.arrs a_acc_ve).length := by change slot < (s.arrs bufA.a_ve).length; rw [hbuf.hve_len]; exact hslot
  have hgetE : (s.arrs a_acc_ve)[slot] = pE := by
    simp only [pE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlenE, Option.getD_some]
  have hrootE : (Expr.read a_acc_ve (.const slot)).eval w s₁ = some pE := by
    have hread := harr₁ a_acc_ve (by decide) (by decide) (by decide)
    simp [Expr.eval, checkWord, hread, hslot_w, hlenE, hgetE, show pE < 2 ^ w by omega]
  have hwfE₁ : ArenaWF G.numEdges ke (s₁.arrs a_ekd) (s₁.arrs a_ev1) (s₁.arrs a_ev2) := by
    rw [harr₁ a_ekd (by decide) (by decide) (by decide),
      harr₁ a_ev1 (by decide) (by decide) (by decide),
      harr₁ a_ev2 (by decide) (by decide) (by decide)]
    exact har.hwfE
  rcases emit41ArenaSetProg_exec a_ekd a_ev1 a_ev2 1 r_ke
      (.read a_acc_ve (.const slot))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hw hm_w hke_w hpE'
      (pref ++ bitSetList (es[idx.1].vertVerts u)) (by simpa using hcap) hcap_w
      hwfE₁ (by rw [hreg₁ 1 (by decide) (by decide) (by decide)]; exact hr1)
      (by rw [hreg₁ r_ke (by decide) (by decide) (by decide)]; exact har.hr_ke)
      hrootE (by simpa using hout₁') (by simpa using hpos₁) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hpos₂, harr₂, hreg₂⟩
  have heE₁ : evalArena G.numEdges (s₁.arrs a_ekd) (s₁.arrs a_ev1) (s₁.arrs a_ev2) pE =
      es[idx.1].vertEdges u := by
    rw [harr₁ a_ekd (by decide) (by decide) (by decide),
      harr₁ a_ev1 (by decide) (by decide) (by decide),
      harr₁ a_ev2 (by decide) (by decide) (by decide)]
    exact heE
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₁ ht₂
    omega
  · simpa [heE₁, List.append_assoc] using hout₂
  · simpa using hpos₂
  · intro a ha hb hc
    exact (harr₂ a ha hb hc).trans (harr₁ a ha hb hc)
  · intro r hr h7 h9
    exact (hreg₂ r hr h7 h9).trans (hreg₁ r hr h7 h9)


/-- Append one computed word and advance the output cursor `r_9`. -/
def emit41WordProg (val : Expr) : Cmd :=
  .seq (.write outArr (.reg 9) val)
    (.assign 9 (.op .add (.reg 9) (.const 1)))

/-- Execution and frame properties of the single-word output operation. -/
theorem emit41WordProg_exec {w cap v : ℕ} (val : Expr) (pref : List ℕ)
    (hw : 1 < 2 ^ w) (hcap : pref.length < cap) (hcap_w : cap < 2 ^ w)
    {s : State} (heval : val.eval w s = some v)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hpos : s.regs 9 = pref.length) :
    ∃ s' t, Exec w (emit41WordProg val) s s' t ∧ t ≤ val.cost + 6 ∧
      s'.arrs outArr = (pref ++ [v]) ++ List.replicate (cap - (pref.length + 1)) 0 ∧
      s'.regs 9 = pref.length + 1 ∧
      (∀ a : ℕ, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 9 → s'.regs r = s.regs r) := by
  have hpos_w : pref.length < 2 ^ w := Nat.lt_trans hcap hcap_w
  have hnext_w : pref.length + 1 < 2 ^ w := Nat.lt_of_le_of_lt hcap hcap_w
  have hlen : pref.length < (s.arrs outArr).length := by rw [hout]; simp; omega
  let s₁ := s.writeArr outArr pref.length v
  have hex₁ : Exec w (.write outArr (.reg 9) val) s s₁ (1 + val.cost + 1) :=
    .write (by simp [Expr.eval, checkWord, hpos, hpos_w]) heval hlen
  let s₂ := s₁.setReg 9 (pref.length + 1)
  have hex₂ : Exec w (.assign 9 (.op .add (.reg 9) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hpos, hpos_w, hw, hnext_w])
  refine ⟨s₂, (1 + val.cost + 1) + 4, .seq hex₁ hex₂, by omega, ?_,
    State.setReg_regs_self s₁ 9 _, ?_, ?_⟩
  · change (s.arrs outArr).set pref.length v = _
    rw [hout, List.set_append_right _ _ le_rfl, Nat.sub_self]
    have hrem : cap - pref.length = (cap - (pref.length + 1)) + 1 := by omega
    rw [hrem, List.replicate_succ, List.set_cons_zero]
    simp only [List.append_assoc, List.singleton_append]
  · intro a ha
    exact State.writeArr_arrs_ne s pref.length v ha
  · intro r hr
    exact State.setReg_regs_ne s₁ _ hr

/-- Serialization preserves the working folio buffer when it changes only the output,
materialization scratch arrays, and scratch registers. -/
theorem ValidPieceBuffer.output_frame {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} {E : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z.card)} {s s' : State}
    (h : ValidPieceBuffer δ ξ ω G Z E es bufA s)
    (ha : ∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a)
    (hr : ∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) :
    ValidPieceBuffer δ ξ ω G Z E es bufA s' := by
  have hV := ha a_vkd (by decide) (by decide) (by decide)
  have hV1 := ha a_vv1 (by decide) (by decide) (by decide)
  have hV2 := ha a_vv2 (by decide) (by decide) (by decide)
  have hE := ha a_ekd (by decide) (by decide) (by decide)
  have hE1 := ha a_ev1 (by decide) (by decide) (by decide)
  have hE2 := ha a_ev2 (by decide) (by decide) (by decide)
  refine h.mono_arena
    (hr 5 (by decide) (by decide) (by decide))
    (hr 6 (by decide) (by decide) (by decide))
    (ha a_acc_zV (by decide) (by decide) (by decide))
    (ha a_acc_zI (by decide) (by decide) (by decide))
    (ha a_acc_vv (by decide) (by decide) (by decide))
    (ha a_acc_ve (by decide) (by decide) (by decide))
    (ha a_acc_em (by decide) (by decide) (by decide))
    (by rw [hr 3 (by decide) (by decide) (by decide)])
    (by rw [hr 4 (by decide) (by decide) (by decide)])
    (fun p _ => by rw [hV, hV1, hV2])
    (fun p _ => by rw [hE, hE1, hE2])

/-- The model-output steps preserve the two set-union arenas. -/
theorem ArenaStateInv.output_frame {G : ComputeDigraph} {kv ke : ℕ} {s s' : State}
    (h : ArenaStateInv G kv ke s)
    (ha : ∀ a : ℕ, a ≠ a_act → a ≠ a_bits → a ≠ outArr → s'.arrs a = s.arrs a)
    (hr : ∀ r : ℕ, r < 10 → r ≠ 7 → r ≠ 9 → s'.regs r = s.regs r) :
    ArenaStateInv G kv ke s' := by
  refine ⟨(hr 3 (by decide) (by decide) (by decide)).trans h.hr_kv,
    (hr 4 (by decide) (by decide) (by decide)).trans h.hr_ke, ?_, ?_⟩
  · rw [ha a_vkd (by decide) (by decide) (by decide),
      ha a_vv1 (by decide) (by decide) (by decide), ha a_vv2 (by decide) (by decide) (by decide)]
    exact h.hwfV
  · rw [ha a_ekd (by decide) (by decide) (by decide),
      ha a_ev1 (by decide) (by decide) (by decide), ha a_ev2 (by decide) (by decide) (by decide)]
    exact h.hwfE

end GraphMinor.Compute
