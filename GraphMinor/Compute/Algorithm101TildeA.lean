module

public import GraphMinor.Compute.Algorithm101Member

/-!
# Member Stream Reader, `vertOwner` Pre-Pass, and $\tilde{A}$ List Builders for Algorithm (10.1)

This file implements the first half of Step 2 of **Graph Minors XIII, Algorithm (10.1)**
(Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, pages 106–107):

1. **Stream Reader for `Case3MemberRecord` (`Section 1`):**
   `readOneMemberRecordProg` reads a single serialized member record `r.enc` from Section 3 of
   `block` into arrays `(a_vList, a_eList, a_par, a_tau)` and registers `(r_vLen, r_eLen, r_t)`
   in `O(|r.enc|)` steps.
2. **Pre-Pass Computing `vertOwner` (`Section 2`):**
   `buildVertOwnerProg` streams through all `M = p.members.length` member records of `block` and
   constructs `List.ofFn (fun v : Fin n => vertOwner p v.1)` in `O(n + |block|)` steps.
3. **Building `memberTildeAVList` and Root/Deletion Bitsets (`Section 3`):**
   `buildTildeAVListProg` constructs `vList = memberTildeAVList xSeq r sSeq` along with the root
   subset indicator `bitSetList (prefixRootFinset vList.length (sSeq.length + xSeq.length))` and
   the `X'`-deletion indicator `bitSetList (tildeAXFinset vList xSeq)` in `O(|vList| + 1)` steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Stream Reader for One `Case3MemberRecord` (`readOneMemberRecordProg`) -/

/-- Read one serialized `Case3MemberRecord` `r.enc` from stream `(a_src, r_off)` into:
- `a_vList := r.vList`, `r_vLen := r.vList.length`
- `a_eList := encEdgeTriples r.eList`, `r_eLen := r.eList.length`
- `a_par := r.parList`, `r_t := r.t_len`
- `a_tau := r.tauList`
using scratch registers starting at `r_base`. -/
def readOneMemberRecordProg (a_src : Arr) (r_off : Reg)
    (a_vList a_eList a_par a_tau : Arr)
    (r_vLen r_eLen r_t r_base : Reg) : Cmd :=
  .seq (readLengthPrefixedProg a_src a_vList r_off r_vLen r_base)
    (.seq (readEdgeTriplesStreamProg a_src a_eList r_off r_eLen r_base (r_base + 1))
      (.seq (readLengthPrefixedProg a_src a_par r_off r_t r_base)
        (readStreamSliceProg a_src a_tau r_off r_eLen r_base)))

theorem Case3MemberRecord.enc_eq_append (r : Case3MemberRecord) :
    r.enc =
      (r.vList.length :: r.vList) ++
      (r.eList.length :: encEdgeTriples r.eList) ++
      (r.t_len :: r.parList) ++
      r.tauList := by
  unfold Case3MemberRecord.enc
  simp [List.append_assoc]

theorem Case3MemberRecord.length_enc (r : Case3MemberRecord)
    (hpar : r.parList.length = r.t_len) (htau : r.tauList.length = r.eList.length) :
    r.enc.length = 3 + r.vList.length + 4 * r.eList.length + r.t_len := by
  rw [r.enc_eq_append]
  simp only [List.length_append, List.length_cons, length_encEdgeTriples, hpar, htau]
  omega

theorem readOneMemberRecordProg_exec {w : ℕ}
    (a_src r_off a_vList a_eList a_par a_tau r_vLen r_eLen r_t r_base : ℕ)
    (hne_sv : a_src ≠ a_vList) (hne_se : a_src ≠ a_eList)
    (hne_sp : a_src ≠ a_par) (hne_st : a_src ≠ a_tau)
    (hne_ve : a_vList ≠ a_eList) (hne_vp : a_vList ≠ a_par) (hne_vt : a_vList ≠ a_tau)
    (hne_ep : a_eList ≠ a_par) (hne_et : a_eList ≠ a_tau) (hne_pt : a_par ≠ a_tau)
    (hr_off : r_off < r_base) (hr_v : r_vLen < r_base)
    (hr_e : r_eLen < r_base) (hr_t : r_t < r_base)
    (hne_ov : r_off ≠ r_vLen) (hne_oe : r_off ≠ r_eLen) (hne_ot : r_off ≠ r_t)
    (hne_ve_r : r_vLen ≠ r_eLen) (hne_vt_r : r_vLen ≠ r_t) (hne_et_r : r_eLen ≠ r_t)
    (r : Case3MemberRecord) (rest : List ℕ) (off : ℕ)
    (hpar_len : r.parList.length = r.t_len)
    (htau_len : r.tauList.length = r.eList.length)
    (hwords : ∀ x ∈ r.enc, x < 2 ^ w)
    (hw3 : 3 < 2 ^ w)
    (hoff_w : off + r.enc.length < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (r.enc ++ rest) s)
    (hroff : s.regs r_off = off) :
    ∃ s' t,
      Exec w (readOneMemberRecordProg a_src r_off a_vList a_eList a_par a_tau
        r_vLen r_eLen r_t r_base) s s' t ∧
      t ≤ 18 * r.vList.length + 67 * r.eList.length + 18 * r.t_len + 88 ∧
      AtStream a_src (off + r.enc.length) rest s' ∧
      s'.regs r_off = off + r.enc.length ∧
      s'.arrs a_vList = r.vList ∧
      s'.regs r_vLen = r.vList.length ∧
      s'.arrs a_eList = encEdgeTriples r.eList ∧
      s'.regs r_eLen = r.eList.length ∧
      s'.arrs a_par = r.parList ∧
      s'.regs r_t = r.t_len ∧
      s'.arrs a_tau = r.tauList ∧
      (∀ a : ℕ, a ≠ a_vList → a ≠ a_eList → a ≠ a_par → a ≠ a_tau → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, reg ≠ r_off → reg ≠ r_vLen → reg ≠ r_eLen → reg ≠ r_t →
        s'.regs reg = s.regs reg) := by
  have hw : 1 < 2 ^ w := by omega
  have henc_len := r.length_enc hpar_len htau_len
  have hv_w : ∀ x ∈ r.vList, x < 2 ^ w := fun x hx =>
    hwords x (by rw [r.enc_eq_append]; simp [hx])
  have he_w : ∀ x ∈ encEdgeTriples r.eList, x < 2 ^ w := fun x hx =>
    hwords x (by rw [r.enc_eq_append]; simp [hx])
  have hpar_w : ∀ x ∈ r.parList, x < 2 ^ w := fun x hx =>
    hwords x (by rw [r.enc_eq_append]; simp [hx])
  have htau_w : ∀ x ∈ r.tauList, x < 2 ^ w := fun x hx =>
    hwords x (by rw [r.enc_eq_append]; simp [hx])
  let rest₁ := (r.eList.length :: encEdgeTriples r.eList) ++ (r.t_len :: r.parList) ++ r.tauList ++ rest
  have hstream₀ : AtStream a_src off (r.vList.length :: r.vList ++ rest₁) s := by
    have heq : r.enc ++ rest = r.vList.length :: r.vList ++ rest₁ := by
      rw [r.enc_eq_append]
      simp [rest₁, List.append_assoc]
    rwa [← heq]
  rcases readLengthPrefixedProg_exec r_off r_vLen r_base
      hne_sv hr_off hr_v hne_ov hv_w hw (by omega) hstream₀ hroff with
    ⟨s₁, t₁, hex₁, ht₁, hvList₁, hrvLen₁, hroff₁, hstream₁, harr₁, hreg₁⟩
  let off₁ := off + 1 + r.vList.length
  let rest₂ := (r.t_len :: r.parList) ++ r.tauList ++ rest
  have hstream₁' : AtStream a_src off₁ (r.eList.length :: encEdgeTriples r.eList ++ rest₂) s₁ := by
    simpa [off₁, rest₁, rest₂, List.append_assoc] using hstream₁
  rcases readEdgeTriplesStreamProg_exec r_off r_eLen r_base (r_base + 1)
      hne_se (by omega) (by omega) (by omega) hne_oe hr_off.ne hr_e.ne
      he_w hw3 (by omega) hstream₁' hroff₁ with
    ⟨s₂, t₂, hex₂, ht₂, heList₂, hreLen₂, _, hroff₂, hstream₂, harr₂, hreg₂⟩
  let off₂ := off₁ + 1 + 3 * r.eList.length
  let rest₃ := r.tauList ++ rest
  have hstream₂' : AtStream a_src off₂ (r.parList.length :: r.parList ++ rest₃) s₂ := by
    rw [hpar_len]
    simpa [off₂, rest₂, rest₃, List.append_assoc] using hstream₂
  rcases readLengthPrefixedProg_exec r_off r_t r_base
      hne_sp hr_off hr_t hne_ot hpar_w hw
      (by rw [hpar_len]; omega) hstream₂' hroff₂ with
    ⟨s₃, t₃, hex₃, ht₃, hpar₃, hrt₃, hroff₃, hstream₃, harr₃, hreg₃⟩
  rw [hpar_len] at hstream₃ hroff₃ hrt₃ ht₃
  let off₃ := off₂ + 1 + r.t_len
  have hreLen₃ : s₃.regs r_eLen = r.tauList.length := by
    rw [hreg₃ r_eLen hr_e hne_oe.symm hne_et_r, hreLen₂, htau_len]
  rcases readStreamSliceProg_exec r_off r_eLen r_base
      hne_st hr_off hr_e hne_oe htau_w hw
      (by rw [htau_len]; omega) hstream₃ hroff₃ hreLen₃ with
    ⟨s₄, t₄, hex₄, ht₄, htau₄, hroff₄, _, hstream₄, harr₄, hreg₄⟩
  rw [htau_len] at hstream₄ hroff₄ ht₄
  have hoff_final : off₃ + r.eList.length = off + r.enc.length := by
    dsimp [off₃, off₂, off₁]
    omega
  rw [hoff_final] at hstream₄ hroff₄
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    hstream₄, hroff₄,
    by rw [harr₄ a_vList hne_vt, harr₃ a_vList hne_vp, harr₂ a_vList hne_ve, hvList₁],
    by rw [hreg₄ r_vLen hr_v hne_ov.symm,
         hreg₃ r_vLen hr_v hne_ov.symm hne_vt_r,
         hreg₂ r_vLen (by omega) hne_ov.symm hne_ve_r hr_v.ne, hrvLen₁],
    by rw [harr₄ a_eList hne_et, harr₃ a_eList hne_ep, heList₂],
    by rw [hreg₄ r_eLen hr_e hne_oe.symm,
         hreg₃ r_eLen hr_e hne_oe.symm hne_et_r, hreLen₂],
    by rw [harr₄ a_par hne_pt, hpar₃],
    by rw [hreg₄ r_t hr_t hne_ot.symm, hrt₃],
    htau₄,
    fun a ha₁ ha₂ ha₃ ha₄ => by
      rw [harr₄ a ha₄, harr₃ a ha₃, harr₂ a ha₂, harr₁ a ha₁],
    fun reg hlt h1 h2 h3 h4 => by
      rw [hreg₄ reg hlt h1, hreg₃ reg hlt h1 h4, hreg₂ reg (by omega) h1 h3 hlt.ne, hreg₁ reg hlt h1 h2]⟩

/-! ### Section 2: Pre-Pass Computing `vertOwner` (`buildVertOwnerProg`) -/

/-- Whether vertex `v` belongs to `r.vList` for some `r ∈ rs`. -/
def seenMembers (rs : List Case3MemberRecord) (v : ℕ) : Bool :=
  rs.any (fun r => decide (v ∈ r.vList))

/-- Index of the first member record in `rs` whose `vList` contains `v` (defaulting to `0`). -/
def ownerMembers (rs : List Case3MemberRecord) (v : ℕ) : ℕ :=
  match (List.finRange rs.length).find? (fun j => decide (v ∈ (rs[j.1]'j.2).vList)) with
  | some j => j.1
  | none => 0

@[simp]
theorem seenMembers_nil (v : ℕ) : seenMembers [] v = false := rfl

@[simp]
theorem ownerMembers_nil (v : ℕ) : ownerMembers [] v = 0 := rfl

theorem ownerMembers_eq_zero_of_seenMembers_false (rs : List Case3MemberRecord) {v : ℕ}
    (h : seenMembers rs v = false) :
    ownerMembers rs v = 0 := by
  unfold ownerMembers
  cases hfind : (List.finRange rs.length).find? (fun j => decide (v ∈ (rs[j.1]'j.2).vList)) with
  | none => rfl
  | some j =>
    have hmem := List.find?_some hfind
    simp only [decide_eq_true_eq] at hmem
    have hany : seenMembers rs v = true := by
      unfold seenMembers
      rw [List.any_eq_true]
      exact ⟨rs[j.1]'j.2, List.getElem_mem j.2, decide_eq_true hmem⟩
    rw [h] at hany
    nomatch hany

theorem seenMembers_append_singleton (rs : List Case3MemberRecord) (r : Case3MemberRecord) (v : ℕ) :
    seenMembers (rs ++ [r]) v = (seenMembers rs v || decide (v ∈ r.vList)) := by
  simp [seenMembers]

theorem finRange_length_append_singleton {α : Type*} (l : List α) (x : α) :
    List.finRange (l ++ [x]).length =
      (List.finRange l.length).map (fun j : Fin l.length => ⟨j.1, by simp⟩) ++
        [⟨l.length, by simp⟩] := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  rw [List.getElem_finRange]
  by_cases hlt : i < l.length
  · rw [List.getElem_append_left (by simp [hlt])]
    simp
  · have heq : i = l.length := by simp at hi₁; omega
    subst heq
    rw [List.getElem_append_right (by simp)]
    simp

theorem ownerMembers_append_singleton (rs : List Case3MemberRecord) (r : Case3MemberRecord) (v : ℕ) :
    ownerMembers (rs ++ [r]) v =
      if seenMembers rs v then ownerMembers rs v
      else if v ∈ r.vList then rs.length
      else 0 := by
  unfold ownerMembers
  rw [finRange_length_append_singleton rs r, List.find?_append, List.find?_map]
  have hfun_eq :
      ((fun j : Fin (rs ++ [r]).length =>
          decide (v ∈ ((rs ++ [r])[j.1]'j.2).vList)) ∘
        fun j : Fin rs.length => (⟨j.1, by simp⟩ : Fin (rs ++ [r]).length)) =
      (fun j : Fin rs.length => decide (v ∈ (rs[j.1]'j.2).vList)) := by
    funext j
    simp [List.getElem_append_left j.2]
  rw [hfun_eq]
  cases hfind : (List.finRange rs.length).find? (fun j => decide (v ∈ (rs[j.1]'j.2).vList)) with
  | some j =>
    have hpred := List.find?_some hfind
    simp only [decide_eq_true_eq] at hpred
    have hseen : seenMembers rs v = true := by
      unfold seenMembers
      rw [List.any_eq_true]
      exact ⟨rs[j.1]'j.2, List.getElem_mem j.2, decide_eq_true hpred⟩
    simp [hseen]
  | none =>
    have hseen : seenMembers rs v = false := by
      unfold seenMembers
      rw [List.any_eq_false]
      intro r' hr'
      rcases List.mem_iff_getElem.mp hr' with ⟨idx, hidx, rfl⟩
      have hnone := List.find?_eq_none.mp hfind ⟨idx, hidx⟩ (List.mem_finRange _)
      exact hnone
    by_cases hv : v ∈ r.vList <;> simp [hseen, hv]

theorem ownerMembers_eq_vertOwner {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (v : ℕ) :
    ownerMembers p.members v = vertOwner p v := by
  unfold ownerMembers vertOwner
  have hfun :
      (fun j : Fin p.members.length => decide (v ∈ (p.members[j.1]'j.2).vList)) =
      (fun j : Fin p.members.length =>
        @decide (v ∈ (p.members[j.1]'j.2).vList) (Classical.propDecidable _)) := by
    funext j
    simp
  rw [hfun]
  cases (List.finRange p.members.length).find?
    (fun j : Fin p.members.length =>
      @decide (v ∈ (p.members[j.1]'j.2).vList) (Classical.propDecidable _)) <;> rfl

/-- Intermediate `seen` value after processing prefix `rs` of members and prefix `vs` of `r.vList`. -/
def seenStep (rs : List Case3MemberRecord) (vs : List ℕ) (v : ℕ) : ℕ :=
  if (seenMembers rs v || decide (v ∈ vs)) = true then 1 else 0

/-- Intermediate `owner` value after processing prefix `rs` of members and prefix `vs` of `r.vList`. -/
def ownerStep (rs : List Case3MemberRecord) (vs : List ℕ) (v : ℕ) : ℕ :=
  if seenMembers rs v = true then ownerMembers rs v
  else if v ∈ vs then rs.length
  else 0

theorem seenStep_nil (rs : List Case3MemberRecord) (v : ℕ) :
    seenStep rs [] v = if seenMembers rs v = true then 1 else 0 := by
  simp [seenStep]

theorem ownerStep_nil (rs : List Case3MemberRecord) (v : ℕ) :
    ownerStep rs [] v = ownerMembers rs v := by
  unfold ownerStep
  by_cases h : seenMembers rs v = true
  · simp [h]
  · simp only [Bool.not_eq_true] at h
    simp [h, ownerMembers_eq_zero_of_seenMembers_false rs h]

theorem seenStep_full (rs : List Case3MemberRecord) (r : Case3MemberRecord) (v : ℕ) :
    seenStep rs r.vList v = if seenMembers (rs ++ [r]) v = true then 1 else 0 := by
  simp [seenStep, seenMembers_append_singleton]

theorem ownerStep_full (rs : List Case3MemberRecord) (r : Case3MemberRecord) (v : ℕ) :
    ownerStep rs r.vList v = ownerMembers (rs ++ [r]) v := by
  simp [ownerStep, ownerMembers_append_singleton]

/-- Inner loop body updating `a_seen` and `a_owner` for `v = a_vList[r_base]`. -/
def updateOwnerVertBody (a_vList a_seen a_owner : Arr) (r_j r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_vList (.reg r_base)))
    (.ite (.op .eq (.read a_seen (.reg (r_base + 1))) (.const 0))
      (.seq (.write a_seen (.reg (r_base + 1)) (.const 1))
        (.write a_owner (.reg (r_base + 1)) (.reg r_j)))
      .skip)

/-- Update `a_seen` and `a_owner` for all vertices in `a_vList` (of length `r_vLen`) with member
index `r_j`. -/
def updateOwnerMemberProg (a_vList a_seen a_owner : Arr) (r_vLen r_j r_base : Reg) : Cmd :=
  .seq (.assign r_base (.const 0))
    (forUp r_base (.reg r_vLen) (updateOwnerVertBody a_vList a_seen a_owner r_j r_base))

theorem updateOwnerMemberProg_exec {w n : ℕ}
    (rs : List Case3MemberRecord) (vList : List ℕ)
    (hv_lt : ∀ v ∈ vList, v < n)
    (a_vList a_seen a_owner r_vLen r_j r_base : ℕ)
    (hne_vs : a_vList ≠ a_seen) (hne_vo : a_vList ≠ a_owner) (hne_so : a_seen ≠ a_owner)
    (hr_vLen : r_vLen < r_base) (hr_j : r_j < r_base) (_hne_vj : r_vLen ≠ r_j)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hvLen_w : vList.length < 2 ^ w)
    (hj_w : rs.length < 2 ^ w)
    {s : State}
    (hvList : s.arrs a_vList = vList)
    (hseen : s.arrs a_seen = List.ofFn (fun u : Fin n => seenStep rs [] u.1))
    (howner : s.arrs a_owner = List.ofFn (fun u : Fin n => ownerStep rs [] u.1))
    (hrvLen : s.regs r_vLen = vList.length)
    (hrj : s.regs r_j = rs.length) :
    ∃ s' t,
      Exec w (updateOwnerMemberProg a_vList a_seen a_owner r_vLen r_j r_base) s s' t ∧
      t ≤ 22 * vList.length + 10 ∧
      s'.arrs a_seen = List.ofFn (fun u : Fin n => seenStep rs vList u.1) ∧
      s'.arrs a_owner = List.ofFn (fun u : Fin n => ownerStep rs vList u.1) ∧
      (∀ a : ℕ, a ≠ a_seen → a ≠ a_owner → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_base 0
  have hex₁ : Exec w (.assign r_base (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (k : ℕ) (st : State) : Prop :=
    st.arrs a_vList = vList ∧
    st.arrs a_seen = List.ofFn (fun u : Fin n => seenStep rs (vList.take k) u.1) ∧
    st.arrs a_owner = List.ofFn (fun u : Fin n => ownerStep rs (vList.take k) u.1) ∧
    st.regs r_vLen = vList.length ∧
    st.regs r_j = rs.length ∧
    st.regs r_base = k ∧
    (∀ a : ℕ, a ≠ a_seen → a ≠ a_owner → st.arrs a = s.arrs a) ∧
    (∀ r < r_base, st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₁ := by
    refine ⟨hvList, by simpa [s₁] using hseen, by simpa [s₁] using howner,
      by simp [s₁, show r_vLen ≠ r_base by omega, hrvLen],
      by simp [s₁, show r_j ≠ r_base by omega, hrj],
      by simp [s₁],
      fun _ _ _ => rfl,
      fun r hr => by simp [s₁, show r ≠ r_base by omega]⟩
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_base (.reg r_vLen) (updateOwnerVertBody a_vList a_seen a_owner r_j r_base)
      ⦃Inv vList.length⦄ ≤ fun _ => 3 + vList.length * (7 + 15) := by
    apply Triple.forUp_const Inv vList.length 15 hw hvLen_w
    · intro k _ st ⟨_, _, _, hrv_st, _, hrb_st, _, _⟩
      exact ⟨hrb_st, by simp [Expr.eval, checkWord, hrv_st, hvLen_w]⟩
    · intro k hk st ⟨hv_st, hs_st, ho_st, hrv_st, hrj_st, hrb_st, harr_st, hreg_st⟩
      have hk_w : k < 2 ^ w := by omega
      let v := vList[k]'hk
      have hv_n : v < n := hv_lt v (List.getElem_mem hk)
      have hv_w : v < 2 ^ w := by omega
      have hk_len : k < (st.arrs a_vList).length := by rw [hv_st]; exact hk
      have hget_v : (st.arrs a_vList)[k]'hk_len = v := by simp [hv_st, v]
      let st₁ := st.setReg (r_base + 1) v
      have hex_v : Exec w (.assign (r_base + 1) (.read a_vList (.reg r_base))) st st₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hrb_st, hk_w, hk_len, hget_v, hv_w])
      have hs_len' : v < (st.arrs a_seen).length := by simp [hs_st, hv_n]
      have hs_len : v < (st₁.arrs a_seen).length := by simpa [st₁] using hs_len'
      let sv := seenStep rs (vList.take k) v
      have hget_s' : (st.arrs a_seen)[v]'hs_len' = sv := by simp [hs_st, sv]
      have hsv_w : sv < 2 ^ w := by dsimp [sv, seenStep]; split_ifs <;> omega
      have htake_succ : vList.take (k + 1) = vList.take k ++ [v] := by simp [v]
      by_cases hsv0 : sv = 0
      · have hnot_seen : seenMembers rs v = false ∧ v ∉ vList.take k := by
          change (if (seenMembers rs v || decide (v ∈ vList.take k)) = true then 1 else 0) = 0 at hsv0
          split_ifs at hsv0 with hcond
          simpa [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] using hcond
        have hcond : (Expr.op .eq (.read a_seen (.reg (r_base + 1))) (.const 0)).eval w st₁ = some 1 := by
          simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hv_w, hs_len', hget_s', hsv0, h0_w, hw]
        let st₂ := st₁.writeArr a_seen v 1
        have hex_ws : Exec w (.write a_seen (.reg (r_base + 1)) (.const 1)) st₁ st₂ 3 :=
          .write (by simp [st₁, Expr.eval, checkWord, hv_w])
            (by simp [Expr.eval, checkWord, hw]) hs_len
        have ho_len : v < (st₂.arrs a_owner).length := by
          simp [st₂, st₁, State.writeArr_arrs_ne _ _ _ hne_so.symm, ho_st, hv_n]
        let st₃ := st₂.writeArr a_owner v rs.length
        have hex_wo : Exec w (.write a_owner (.reg (r_base + 1)) (.reg r_j)) st₂ st₃ 3 :=
          .write (by simp [st₂, st₁, Expr.eval, checkWord, hv_w])
            (by simp [st₂, st₁, show r_j ≠ r_base + 1 by omega, Expr.eval, checkWord, hrj_st, hj_w])
            ho_len
        have hs_eq :
            st₃.arrs a_seen = List.ofFn (fun u : Fin n => seenStep rs (vList.take (k + 1)) u.1) := by
          simp only [st₃, st₂, st₁, State.writeArr_arrs_ne _ _ _ hne_so,
            State.writeArr_arrs_self, State.setReg_arrs, hs_st, htake_succ]
          apply List.ext_getElem (by simp)
          intro i hi₁ hi₂
          rw [List.getElem_ofFn]
          by_cases hiv : i = v
          · subst hiv
            rw [List.getElem_set_self]
            simp [seenStep]
          · rw [List.getElem_set_ne (Ne.symm hiv), List.getElem_ofFn]
            simp [seenStep, hiv]
        have ho_eq :
            st₃.arrs a_owner = List.ofFn (fun u : Fin n => ownerStep rs (vList.take (k + 1)) u.1) := by
          simp only [st₃, st₂, st₁, State.writeArr_arrs_self,
            State.writeArr_arrs_ne _ _ _ hne_so.symm, State.setReg_arrs, ho_st, htake_succ]
          apply List.ext_getElem (by simp)
          intro i hi₁ hi₂
          rw [List.getElem_ofFn]
          by_cases hiv : i = v
          · subst hiv
            rw [List.getElem_set_self]
            simp [ownerStep, hnot_seen.1]
          · rw [List.getElem_set_ne (Ne.symm hiv), List.getElem_ofFn]
            simp [ownerStep, hiv]
        refine ⟨st₃, _,
          .seq hex_v (.ite_true hcond (by omega) (.seq hex_ws hex_wo)),
          by dsimp [Expr.cost]; omega,
          ⟨by simp [st₃, st₂, st₁, hne_vo, hne_vs, hv_st],
           hs_eq, ho_eq,
           by simp [st₃, st₂, st₁, show r_vLen ≠ r_base by omega, show r_vLen ≠ r_base + 1 by omega, hrv_st],
           by simp [st₃, st₂, st₁, show r_j ≠ r_base by omega, show r_j ≠ r_base + 1 by omega, hrj_st],
           by simp [st₃, st₂, st₁],
           fun a ha₁ ha₂ => by simp [st₃, st₂, st₁, ha₁, ha₂, harr_st a ha₁ ha₂],
           fun r hr => by simp [st₃, st₂, st₁, show r ≠ r_base by omega, show r ≠ r_base + 1 by omega, hreg_st r hr]⟩,
          by simp [st₃, st₂, st₁, hrb_st]⟩
      · have hseen_or : seenMembers rs v = true ∨ v ∈ vList.take k := by
          change ¬ (if (seenMembers rs v || decide (v ∈ vList.take k)) = true then 1 else 0) = 0 at hsv0
          split_ifs at hsv0 with hcond
          · simpa [Bool.or_eq_true, decide_eq_true_eq] using hcond
          · contradiction
        have hsv1 : sv = 1 := by
          dsimp [sv, seenStep]
          rcases hseen_or with h1 | h2
          · simp [h1]
          · simp [h2]
        have hcond : (Expr.op .eq (.read a_seen (.reg (r_base + 1))) (.const 0)).eval w st₁ = some 0 := by
          simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hv_w, hs_len', hget_s', hsv1, h0_w, hw]
        have hs_eq :
            st₁.arrs a_seen = List.ofFn (fun u : Fin n => seenStep rs (vList.take (k + 1)) u.1) := by
          simp only [st₁, State.setReg_arrs, hs_st, htake_succ]
          apply List.ext_getElem (by simp)
          intro i hi₁ hi₂
          simp only [List.getElem_ofFn, seenStep, List.mem_append, List.mem_singleton]
          by_cases hiv : i = v
          · subst hiv
            rcases hseen_or with h1 | h2
            · simp [h1]
            · simp [h2]
          · simp [hiv]
        have ho_eq :
            st₁.arrs a_owner = List.ofFn (fun u : Fin n => ownerStep rs (vList.take (k + 1)) u.1) := by
          simp only [st₁, State.setReg_arrs, ho_st, htake_succ]
          apply List.ext_getElem (by simp)
          intro i hi₁ hi₂
          simp only [List.getElem_ofFn, ownerStep, List.mem_append, List.mem_singleton]
          by_cases hiv : i = v
          · subst hiv
            rcases hseen_or with h1 | h2
            · simp [h1]
            · simp [h2]
          · simp [hiv]
        refine ⟨st₁, _,
          .seq hex_v (.ite_false hcond (.skip st₁)),
          by dsimp [Expr.cost]; omega,
          ⟨by simp [st₁, hv_st],
           hs_eq, ho_eq,
           by simp [st₁, show r_vLen ≠ r_base by omega, show r_vLen ≠ r_base + 1 by omega, hrv_st],
           by simp [st₁, show r_j ≠ r_base by omega, show r_j ≠ r_base + 1 by omega, hrj_st],
           by simp,
           fun a ha₁ ha₂ => by simp [st₁, harr_st a ha₁ ha₂],
           fun r hr => by simp [st₁, show r ≠ r_base by omega, show r ≠ r_base + 1 by omega, hreg_st r hr]⟩,
          by simp [st₁, hrb_st]⟩
  rcases hLoop s₁ hInv₀ with
    ⟨s₂, t₂, hex₂, ht₂, ⟨_, hs₂, ho₂, _, _, _, harr₂, hreg₂⟩⟩
  dsimp only at ht₂
  rw [List.take_length] at hs₂ ho₂
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hs₂, ho₂, harr₂, hreg₂⟩

/-- Pre-pass loop body for one member `j` in `buildVertOwnerProg`. -/
def buildVertOwnerBody (a_src : Arr) (r_off : Reg)
    (a_vList a_eList a_par a_tau a_seen a_owner : Arr)
    (r_vLen r_eLen r_t r_j r_base : Reg) : Cmd :=
  .seq (readOneMemberRecordProg a_src r_off a_vList a_eList a_par a_tau r_vLen r_eLen r_t r_base)
    (updateOwnerMemberProg a_vList a_seen a_owner r_vLen r_j r_base)

/-- Pre-pass over all `r_M = p.members.length` member records starting at stream offset `r_off` in
`a_src`, computing `a_owner = List.ofFn (fun v : Fin n => vertOwner p v.1)`. -/
def buildVertOwnerProg (a_src : Arr) (r_off r_M r_n : Reg)
    (a_vList a_eList a_par a_tau a_seen a_owner : Arr)
    (r_vLen r_eLen r_t r_j r_base : Reg) : Cmd :=
  .seq (.alloc a_seen (.reg r_n))
    (.seq (.alloc a_owner (.reg r_n))
      (.seq (.assign r_j (.const 0))
        (forUp r_j (.reg r_M)
          (buildVertOwnerBody a_src r_off a_vList a_eList a_par a_tau a_seen a_owner
            r_vLen r_eLen r_t r_j r_base))))

theorem buildVertOwnerLoop_exec {w n : ℕ}
    (a_src r_off r_M a_vList a_eList a_par a_tau a_seen a_owner
      r_vLen r_eLen r_t r_j r_base : ℕ)
    (hne_sv : a_src ≠ a_vList) (hne_se : a_src ≠ a_eList)
    (hne_sp : a_src ≠ a_par) (hne_st : a_src ≠ a_tau)
    (hne_ss : a_src ≠ a_seen) (hne_so : a_src ≠ a_owner)
    (hne_ve : a_vList ≠ a_eList) (hne_vp : a_vList ≠ a_par) (hne_vt : a_vList ≠ a_tau)
    (hne_vs : a_vList ≠ a_seen) (hne_vo : a_vList ≠ a_owner)
    (hne_ep : a_eList ≠ a_par) (hne_et : a_eList ≠ a_tau)
    (hne_es : a_eList ≠ a_seen) (hne_eo : a_eList ≠ a_owner)
    (hne_pt : a_par ≠ a_tau) (hne_ps : a_par ≠ a_seen) (hne_po : a_par ≠ a_owner)
    (hne_ts : a_tau ≠ a_seen) (hne_to : a_tau ≠ a_owner)
    (hne_seen_own : a_seen ≠ a_owner)
    (hr_off : r_off < r_base) (hr_M : r_M < r_base)
    (hr_v : r_vLen < r_base) (hr_e : r_eLen < r_base)
    (hr_t : r_t < r_base) (hr_j : r_j < r_base)
    (hne_om : r_off ≠ r_M) (hne_ov : r_off ≠ r_vLen) (hne_oe : r_off ≠ r_eLen)
    (hne_ot : r_off ≠ r_t) (hne_oj : r_off ≠ r_j)
    (hne_mv : r_M ≠ r_vLen) (hne_me : r_M ≠ r_eLen) (hne_mt : r_M ≠ r_t) (hne_mj : r_M ≠ r_j)
    (hne_ve_r : r_vLen ≠ r_eLen) (hne_vt_r : r_vLen ≠ r_t) (hne_vj : r_vLen ≠ r_j)
    (hne_et_r : r_eLen ≠ r_t) (hne_ej : r_eLen ≠ r_j) (hne_tj : r_t ≠ r_j)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (suff : List Case3MemberRecord) :
    ∀ (pref : List Case3MemberRecord) (rest : List ℕ) (off : ℕ),
      (∀ r ∈ suff,
        (∀ v ∈ r.vList, v < n) ∧
        r.vList.length < 2 ^ w ∧
        r.parList.length = r.t_len ∧
        r.tauList.length = r.eList.length ∧
        (∀ x ∈ r.enc, x < 2 ^ w)) →
      pref.length + suff.length < 2 ^ w →
      off + (suff.flatMap Case3MemberRecord.enc).length < 2 ^ w →
      ∀ {s : State},
        AtStream a_src off ((suff.flatMap Case3MemberRecord.enc) ++ rest) s →
        s.arrs a_seen = List.ofFn (fun u : Fin n => if seenMembers pref u.1 = true then 1 else 0) →
        s.arrs a_owner = List.ofFn (fun u : Fin n => ownerMembers pref u.1) →
        s.regs r_off = off →
        s.regs r_j = pref.length →
        s.regs r_M = pref.length + suff.length →
        ∃ s' t,
          Exec w
            (forUp r_j (.reg r_M)
              (buildVertOwnerBody a_src r_off a_vList a_eList a_par a_tau a_seen a_owner
                r_vLen r_eLen r_t r_j r_base)) s s' t ∧
          t ≤ 3 + (suff.map (fun r => 40 * r.vList.length + 67 * r.eList.length + 18 * r.t_len + 105)).sum ∧
          AtStream a_src (off + (suff.flatMap Case3MemberRecord.enc).length) rest s' ∧
          s'.regs r_off = off + (suff.flatMap Case3MemberRecord.enc).length ∧
          s'.arrs a_seen = List.ofFn
            (fun u : Fin n => if seenMembers (pref ++ suff) u.1 = true then 1 else 0) ∧
          s'.arrs a_owner = List.ofFn (fun u : Fin n => ownerMembers (pref ++ suff) u.1) ∧
          (∀ a : ℕ, a ≠ a_vList → a ≠ a_eList → a ≠ a_par → a ≠ a_tau →
            a ≠ a_seen → a ≠ a_owner → s'.arrs a = s.arrs a) ∧
          (∀ reg < r_base, reg ≠ r_off → reg ≠ r_vLen → reg ≠ r_eLen →
            reg ≠ r_t → reg ≠ r_j → s'.regs reg = s.regs reg) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  induction suff with
  | nil =>
    intro pref rest off _ hM_w _ s hstream hseen howner hroff hrj hrM
    have hrM' : s.regs r_M = pref.length := by simpa using hrM
    have hcond : (Expr.op .lt (.reg r_j) (.reg r_M)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrM',
        show pref.length < 2 ^ w by omega, h0_w]
    refine ⟨s, 3, .while_false hcond, by simp,
      by simpa using hstream, by simpa using hroff,
      by simpa using hseen, by simpa using howner,
      fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | cons r rs ih =>
    intro pref rest off hall hM_w hoff_w s hstream hseen howner hroff hrj hrM
    rcases hall r List.mem_cons_self with ⟨hv_lt, hvLen_w, hpar_len, htau_len, hwords⟩
    have hall_rs : ∀ r' ∈ rs,
        (∀ v ∈ r'.vList, v < n) ∧
        r'.vList.length < 2 ^ w ∧
        r'.parList.length = r'.t_len ∧
        r'.tauList.length = r'.eList.length ∧
        (∀ x ∈ r'.enc, x < 2 ^ w) :=
      fun r' hr' => hall r' (List.mem_cons_of_mem r hr')
    have hM_w' : pref.length + (rs.length + 1) < 2 ^ w := by simpa using hM_w
    have hj_w : pref.length < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_j) (.reg r_M)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrM, hj_w, hM_w', hw]
    have hstream_r : AtStream a_src off (r.enc ++ ((rs.flatMap Case3MemberRecord.enc) ++ rest)) s := by
      simpa [List.flatMap_cons, List.append_assoc] using hstream
    have hoff_r_w : off + r.enc.length < 2 ^ w := by
      simp only [List.flatMap_cons, List.length_append] at hoff_w
      omega
    rcases readOneMemberRecordProg_exec a_src r_off a_vList a_eList a_par a_tau
        r_vLen r_eLen r_t r_base
        hne_sv hne_se hne_sp hne_st hne_ve hne_vp hne_vt hne_ep hne_et hne_pt
        hr_off hr_v hr_e hr_t hne_ov hne_oe hne_ot hne_ve_r hne_vt_r hne_et_r
        r ((rs.flatMap Case3MemberRecord.enc) ++ rest) off hpar_len htau_len hwords hw3 hoff_r_w
        hstream_r hroff with
      ⟨s₁, t₁, hex₁, ht₁, hstream₁, hroff₁, hvList₁, hrvLen₁, _, _, _, _, _, harr₁, hreg₁⟩
    have hseen₁ : s₁.arrs a_seen = List.ofFn (fun u : Fin n => seenStep pref [] u.1) := by
      rw [harr₁ a_seen hne_vs.symm hne_es.symm hne_ps.symm hne_ts.symm, hseen]
      apply List.ext_getElem (by simp)
      intro i _ _
      simp [seenStep_nil]
    have howner₁ : s₁.arrs a_owner = List.ofFn (fun u : Fin n => ownerStep pref [] u.1) := by
      rw [harr₁ a_owner hne_vo.symm hne_eo.symm hne_po.symm hne_to.symm, howner]
      apply List.ext_getElem (by simp)
      intro i _ _
      simp [ownerStep_nil]
    have hrj₁ : s₁.regs r_j = pref.length := by
      rw [hreg₁ r_j hr_j hne_oj.symm hne_vj.symm hne_ej.symm hne_tj.symm, hrj]
    rcases updateOwnerMemberProg_exec pref r.vList hv_lt
        a_vList a_seen a_owner r_vLen r_j r_base
        hne_vs hne_vo hne_seen_own hr_v hr_j hne_vj hw hn_w hvLen_w hj_w
        hvList₁ hseen₁ howner₁ hrvLen₁ hrj₁ with
      ⟨s₂, t₂, hex₂, ht₂, hseen₂, howner₂, harr₂, hreg₂⟩
    have hrj₂ : s₂.regs r_j = pref.length := by
      rw [hreg₂ r_j hr_j, hrj₁]
    let s₃ := s₂.setReg r_j (pref.length + 1)
    have hex_inc : Exec w (.assign r_j (.op .add (.reg r_j) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj₂, hj_w, hw,
        show pref.length + 1 < 2 ^ w by simp at hM_w; omega])
    have hstream₃ : AtStream a_src (off + r.enc.length) ((rs.flatMap Case3MemberRecord.enc) ++ rest) s₃ := by
      apply hstream₁.of_arr_eq
      simp [s₃, harr₂ a_src hne_ss hne_so]
    have hseen₃ : s₃.arrs a_seen =
        List.ofFn (fun u : Fin n => if seenMembers (pref ++ [r]) u.1 = true then 1 else 0) := by
      simp only [s₃, State.setReg_arrs, hseen₂]
      apply List.ext_getElem (by simp)
      intro i _ _
      simp [seenStep_full]
    have howner₃ : s₃.arrs a_owner =
        List.ofFn (fun u : Fin n => ownerMembers (pref ++ [r]) u.1) := by
      simp only [s₃, State.setReg_arrs, howner₂]
      apply List.ext_getElem (by simp)
      intro i _ _
      simp [ownerStep_full]
    have hroff₃ : s₃.regs r_off = off + r.enc.length := by
      simp [s₃, hne_oj, hreg₂ r_off hr_off, hroff₁]
    have hrM₃ : s₃.regs r_M = (pref ++ [r]).length + rs.length := by
      have hlen_eq : pref.length + (r :: rs).length = (pref ++ [r]).length + rs.length := by
        simp; omega
      rw [← hlen_eq]
      simp [s₃, hne_mj, hreg₂ r_M hr_M,
        hreg₁ r_M hr_M hne_om.symm hne_mv hne_me hne_mt, hrM]
    rcases ih (pref ++ [r]) rest (off + r.enc.length) hall_rs
        (by simp at hM_w ⊢; omega)
        (by simpa [List.flatMap_cons, List.length_append, Nat.add_assoc] using hoff_w)
        hstream₃ hseen₃ howner₃ hroff₃ (by simp [s₃]) hrM₃ with
      ⟨s₄, t₄, hex₄, ht₄, hstream₄, hroff₄, hseen₄, howner₄, harr₄, hreg₄⟩
    have hoff_eq :
        off + r.enc.length + (rs.flatMap Case3MemberRecord.enc).length =
          off + ((r :: rs).flatMap Case3MemberRecord.enc).length := by
      simp [List.flatMap_cons, List.length_append, Nat.add_assoc]
    rw [hoff_eq] at hstream₄ hroff₄
    have hpref_eq : pref ++ [r] ++ rs = pref ++ (r :: rs) := by simp
    rw [hpref_eq] at hseen₄ howner₄
    refine ⟨s₄, 3 + ((t₁ + t₂) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex_inc) hex₄,
      by simp only [List.map_cons, List.sum_cons]; omega,
      hstream₄, hroff₄, hseen₄, howner₄,
      fun a ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ => by
        rw [harr₄ a ha₁ ha₂ ha₃ ha₄ ha₅ ha₆]
        simp [s₃, harr₂ a ha₅ ha₆, harr₁ a ha₁ ha₂ ha₃ ha₄],
      fun reg hlt h1 h2 h3 h4 h5 => by
        rw [hreg₄ reg hlt h1 h2 h3 h4 h5]
        simp [s₃, h5, hreg₂ reg hlt, hreg₁ reg hlt h1 h2 h3 h4]⟩

theorem buildVertOwnerProg_exec {w n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (rest : List ℕ) (off : ℕ)
    (a_src r_off r_M r_n a_vList a_eList a_par a_tau a_seen a_owner
      r_vLen r_eLen r_t r_j r_base : ℕ)
    (hne_sv : a_src ≠ a_vList) (hne_se : a_src ≠ a_eList)
    (hne_sp : a_src ≠ a_par) (hne_st : a_src ≠ a_tau)
    (hne_ss : a_src ≠ a_seen) (hne_so : a_src ≠ a_owner)
    (hne_ve : a_vList ≠ a_eList) (hne_vp : a_vList ≠ a_par) (hne_vt : a_vList ≠ a_tau)
    (hne_vs : a_vList ≠ a_seen) (hne_vo : a_vList ≠ a_owner)
    (hne_ep : a_eList ≠ a_par) (hne_et : a_eList ≠ a_tau)
    (hne_es : a_eList ≠ a_seen) (hne_eo : a_eList ≠ a_owner)
    (hne_pt : a_par ≠ a_tau) (hne_ps : a_par ≠ a_seen) (hne_po : a_par ≠ a_owner)
    (hne_ts : a_tau ≠ a_seen) (hne_to : a_tau ≠ a_owner)
    (hne_seen_own : a_seen ≠ a_owner)
    (hr_off : r_off < r_base) (hr_M : r_M < r_base) (_hr_n : r_n < r_base)
    (hr_v : r_vLen < r_base) (hr_e : r_eLen < r_base)
    (hr_t : r_t < r_base) (hr_j : r_j < r_base)
    (hne_om : r_off ≠ r_M) (hne_ov : r_off ≠ r_vLen) (hne_oe : r_off ≠ r_eLen)
    (hne_ot : r_off ≠ r_t) (hne_oj : r_off ≠ r_j)
    (hne_mv : r_M ≠ r_vLen) (hne_me : r_M ≠ r_eLen) (hne_mt : r_M ≠ r_t) (hne_mj : r_M ≠ r_j)
    (hne_ve_r : r_vLen ≠ r_eLen) (hne_vt_r : r_vLen ≠ r_t) (hne_vj : r_vLen ≠ r_j)
    (hne_et_r : r_eLen ≠ r_t) (hne_ej : r_eLen ≠ r_j) (hne_tj : r_t ≠ r_j)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hwords : ∀ r ∈ p.members, ∀ x ∈ r.enc, x < 2 ^ w)
    (hM_w : p.members.length < 2 ^ w)
    (hoff_w : off + (p.members.flatMap Case3MemberRecord.enc).length < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off ((p.members.flatMap Case3MemberRecord.enc) ++ rest) s)
    (hroff : s.regs r_off = off)
    (hrM : s.regs r_M = p.members.length)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w
        (buildVertOwnerProg a_src r_off r_M r_n a_vList a_eList a_par a_tau a_seen a_owner
          r_vLen r_eLen r_t r_j r_base) s s' t ∧
      t ≤ 2 * n + 10 +
        (p.members.map (fun r => 40 * r.vList.length + 67 * r.eList.length + 18 * r.t_len + 105)).sum ∧
      AtStream a_src (off + (p.members.flatMap Case3MemberRecord.enc).length) rest s' ∧
      s'.regs r_off = off + (p.members.flatMap Case3MemberRecord.enc).length ∧
      s'.arrs a_owner = List.ofFn (fun u : Fin n => vertOwner p u.1) ∧
      (∀ a : ℕ, a ≠ a_vList → a ≠ a_eList → a ≠ a_par → a ≠ a_tau →
        a ≠ a_seen → a ≠ a_owner → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, reg ≠ r_off → reg ≠ r_vLen → reg ≠ r_eLen →
        reg ≠ r_t → reg ≠ r_j → s'.regs reg = s.regs reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_seen (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_seen (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setArr a_owner (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_owner (.reg r_n)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hrn, hn_w])
  let s₃ := s₂.setReg r_j 0
  have hex₃ : Exec w (.assign r_j (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hall : ∀ r ∈ p.members,
      (∀ v ∈ r.vList, v < n) ∧
      r.vList.length < 2 ^ w ∧
      r.parList.length = r.t_len ∧
      r.tauList.length = r.eList.length ∧
      (∀ x ∈ r.enc, x < 2 ^ w) := by
    intro r hr
    have hval := p.member_valid_iff hr
    refine ⟨?_, ?_, hval.2.2.2.2.2.2.2.2.1, hval.2.2.2.2.2.2.2.2.2.2.1, hwords r hr⟩
    · intro v hv
      have hv_del := p.K_vList_mem_delGraph (hval.2.2.1 v hv)
      exact ((mem_vertexSet_delGraph_iff G X' v).mp hv_del).1
    · exact Nat.lt_of_le_of_lt hval.1 hn_w
  have hstream₃ : AtStream a_src off ((p.members.flatMap Case3MemberRecord.enc) ++ rest) s₃ := by
    apply hstream.of_arr_eq
    simp [s₃, s₂, s₁, hne_ss, hne_so]
  have hseen₃ : s₃.arrs a_seen =
      List.ofFn (fun u : Fin n => if seenMembers [] u.1 = true then 1 else 0) := by
    have hrep : s₃.arrs a_seen = List.replicate n 0 := by simp [s₃, s₂, s₁, hne_seen_own]
    rw [hrep]
    apply List.ext_getElem (by simp)
    intro i _ _
    simp
  have howner₃ : s₃.arrs a_owner = List.ofFn (fun u : Fin n => ownerMembers [] u.1) := by
    simp only [s₃, s₂, s₁, State.setReg_arrs, State.setArr_arrs_self]
    apply List.ext_getElem (by simp)
    intro i _ _
    simp
  rcases buildVertOwnerLoop_exec
      a_src r_off r_M a_vList a_eList a_par a_tau a_seen a_owner
      r_vLen r_eLen r_t r_j r_base
      hne_sv hne_se hne_sp hne_st hne_ss hne_so
      hne_ve hne_vp hne_vt hne_vs hne_vo hne_ep hne_et hne_es hne_eo
      hne_pt hne_ps hne_po hne_ts hne_to hne_seen_own
      hr_off hr_M hr_v hr_e hr_t hr_j
      hne_om hne_ov hne_oe hne_ot hne_oj hne_mv hne_me hne_mt hne_mj
      hne_ve_r hne_vt_r hne_vj hne_et_r hne_ej hne_tj
      hw3 hn_w p.members [] rest off hall (by simpa using hM_w) hoff_w
      hstream₃ hseen₃ howner₃
      (by simp [s₃, s₂, s₁, hne_oj, hroff])
      (by simp [s₃])
      (by simp [s₃, s₂, s₁, hne_mj, hrM]) with
    ⟨s₄, t₄, hex₄, ht₄, hstream₄, hroff₄, _, howner₄, harr₄, hreg₄⟩
  simp only [List.nil_append, ownerMembers_eq_vertOwner] at howner₄
  refine ⟨s₄, (1 + n) + ((1 + n) + (2 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    hstream₄, hroff₄, howner₄,
    fun a ha₁ ha₂ ha₃ ha₄ ha₅ ha₆ => by
      rw [harr₄ a ha₁ ha₂ ha₃ ha₄ ha₅ ha₆]
      simp [s₃, s₂, s₁, ha₅, ha₆],
    fun reg hlt h1 h2 h3 h4 h5 => by
      rw [hreg₄ reg hlt h1 h2 h3 h4 h5]
      simp [s₃, s₂, s₁, h5]⟩

/-! ### Section 3: Building `memberTildeAVList` and Root/Deletion Bitsets (`buildTildeAVListProg`) -/

/-- Inner loop body appending `v = a_rVList[r_base]` to `a_buf` when `a_sInd[v] == 0`. -/
def appendRemVertBody (a_rVList a_sInd a_buf : Arr) (r_nA r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1) (.read a_rVList (.reg r_base)))
    (.ite (.op .eq (.read a_sInd (.reg (r_base + 1))) (.const 0))
      (appendWordProg a_buf r_nA (.reg (r_base + 1)))
      .skip)

/-- Build `a_tildeV = memberTildeAVList xSeq r sSeq` and `r_nA = (memberTildeAVList xSeq r sSeq).length`
from `a_sSeq = sSeq`, `a_xSeq = xSeq`, `a_rVList = r.vList`, and `a_sInd = bitSetList {u | u.1 ∈ sSeq}`. -/
def buildTildeAVListProg (a_sSeq a_xSeq a_rVList a_sInd a_buf a_tildeV : Arr)
    (r_sLen r_xLen r_vLen r_nA r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 1)
      (.op .add (.op .add (.reg r_sLen) (.reg r_xLen)) (.reg r_vLen)))
    (.seq (initPrefixBufferProg a_buf (.reg (r_base + 1)) r_nA)
      (.seq (appendBufSliceProg a_sSeq a_buf r_sLen r_nA r_base)
        (.seq (appendBufSliceProg a_xSeq a_buf r_xLen r_nA r_base)
          (.seq (.assign r_base (.const 0))
            (.seq (forUp r_base (.reg r_vLen)
                (appendRemVertBody a_rVList a_sInd a_buf r_nA r_base))
              (copyBufPrefixProg a_buf a_tildeV r_nA r_base))))))

theorem appendRemVertLoop_exec {w n : ℕ}
    (rVList sSeq : List ℕ) (hv_lt : ∀ v ∈ rVList, v < n)
    (a_rVList a_sInd a_buf r_vLen r_nA r_base : ℕ)
    (hne_vb : a_rVList ≠ a_buf) (hne_sb : a_sInd ≠ a_buf)
    (hr_vLen : r_vLen < r_base) (hr_nA : r_nA < r_base) (hne_vn : r_vLen ≠ r_nA)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hvLen_w : rVList.length < 2 ^ w)
    (pfx : List ℕ) (extra : ℕ)
    (hpfx_w : pfx.length + rVList.length < 2 ^ w)
    {s : State}
    (hrV : s.arrs a_rVList = rVList)
    (hsInd : s.arrs a_sInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ sSeq)))
    (hbuf : IsPrefixBuffer a_buf pfx (rVList.length + extra) s)
    (hrvLen : s.regs r_vLen = rVList.length)
    (hrnA : s.regs r_nA = pfx.length)
    (hrb : s.regs r_base = 0) :
    ∃ s' t rem_extra,
      Exec w
        (forUp r_base (.reg r_vLen) (appendRemVertBody a_rVList a_sInd a_buf r_nA r_base))
        s s' t ∧
      t ≤ 26 * rVList.length + 5 ∧
      IsPrefixBuffer a_buf (pfx ++ rVList.filter (fun v => decide (v ∉ sSeq))) rem_extra s' ∧
      s'.regs r_nA = (pfx ++ rVList.filter (fun v => decide (v ∉ sSeq))).length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, reg ≠ r_nA → s'.regs reg = s.regs reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  let Inv (k : ℕ) (st : State) : Prop :=
    let cur := pfx ++ (rVList.take k).filter (fun v => decide (v ∉ sSeq))
    ∃ rem_extra,
      st.arrs a_rVList = rVList ∧
      st.arrs a_sInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ sSeq)) ∧
      IsPrefixBuffer a_buf cur ((rVList.length - k) + rem_extra) st ∧
      st.regs r_vLen = rVList.length ∧
      st.regs r_nA = cur.length ∧
      st.regs r_base = k ∧
      (∀ a : ℕ, a ≠ a_buf → st.arrs a = s.arrs a) ∧
      (∀ reg < r_base, reg ≠ r_nA → st.regs reg = s.regs reg)
  have hInv₀ : Inv 0 s := by
    refine ⟨extra, hrV, hsInd, by simpa using hbuf, hrvLen, by simpa using hrnA, hrb,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_base (.reg r_vLen) (appendRemVertBody a_rVList a_sInd a_buf r_nA r_base)
      ⦃Inv rVList.length⦄ ≤ fun _ => 3 + rVList.length * (7 + 19) := by
    apply Triple.forUp_const Inv rVList.length 19 hw hvLen_w
    · intro k _ st ⟨_, _, _, _, hrv_st, _, hrb_st, _, _⟩
      exact ⟨hrb_st, by simp [Expr.eval, checkWord, hrv_st, hvLen_w]⟩
    · intro k hk st ⟨rem_ex, hrV_st, hsInd_st, hbuf_st, hrv_st, hrnA_st, hrb_st, harr_st, hreg_st⟩
      let cur := pfx ++ (rVList.take k).filter (fun v => decide (v ∉ sSeq))
      have hk_w : k < 2 ^ w := by omega
      let v := rVList[k]'hk
      have hv_n : v < n := hv_lt v (List.getElem_mem hk)
      have hv_w : v < 2 ^ w := by omega
      have hk_len : k < (st.arrs a_rVList).length := by rw [hrV_st]; exact hk
      have hget_v : (st.arrs a_rVList)[k]'hk_len = v := by simp only [hrV_st, v]
      let st₁ := st.setReg (r_base + 1) v
      have hex₁ : Exec w (.assign (r_base + 1) (.read a_rVList (.reg r_base))) st st₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hrb_st, hk_w, hk_len, hget_v, hv_w])
      have hs_len : v < (st₁.arrs a_sInd).length := by simp [st₁, hsInd_st, length_bitSetList, hv_n]
      let b := if v ∈ sSeq then 1 else 0
      have hget_s : (st₁.arrs a_sInd)[v]'hs_len = b := by
        simp [st₁, hsInd_st, bitSetList, b]
      have hb_w : b < 2 ^ w := by dsimp [b]; split_ifs <;> omega
      have htake_succ : rVList.take (k + 1) = rVList.take k ++ [v] := by simp [v]
      have hcur_le : cur.length ≤ pfx.length + k := by
        dsimp [cur]
        rw [List.length_append]
        have := List.length_filter_le (fun v => decide (v ∉ sSeq)) (rVList.take k)
        rw [List.length_take_of_le (Nat.le_of_lt hk)] at this
        omega
      by_cases hvs : v ∉ sSeq
      · have hb0 : b = 0 := by simp [b, hvs]
        have hcond : (Expr.op .eq (.read a_sInd (.reg (r_base + 1))) (.const 0)).eval w st₁ = some 1 := by
          simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hv_w, hsInd_st, bitSetList, hv_n, hvs, h0_w, hw]
        have hbuf₁ : IsPrefixBuffer a_buf cur (((rVList.length - (k + 1)) + rem_ex) + 1) st₁ := by
          unfold IsPrefixBuffer at hbuf_st ⊢
          have hrep : (rVList.length - k) + rem_ex = ((rVList.length - (k + 1)) + rem_ex) + 1 := by omega
          rw [← hrep]
          exact hbuf_st
        have hrnA₁ : st₁.regs r_nA = cur.length := by
          simp [st₁, show r_nA ≠ r_base + 1 by omega, hrnA_st, cur]
        rcases appendWordProg_exec (val := v) a_buf r_nA (.reg (r_base + 1))
            hw (by omega) hbuf₁ hrnA₁
            (by simp [st₁, Expr.eval, checkWord, hv_w]) with
          ⟨st₂, t₂, hex₂, ht₂, hbuf₂, hrnA₂, harr₂, hreg₂⟩
        have hcur_succ :
            pfx ++ (rVList.take (k + 1)).filter (fun w => decide (w ∉ sSeq)) = cur ++ [v] := by
          rw [htake_succ, List.filter_append]
          simp [cur, hvs, List.append_assoc]
        rw [← hcur_succ] at hbuf₂ hrnA₂
        refine ⟨st₂, _,
          .seq hex₁ (.ite_true hcond (by omega) hex₂),
          by dsimp [Expr.cost] at ht₂ ⊢; omega,
          ⟨rem_ex,
           by simp only [State.setReg_arrs]; rw [harr₂ a_rVList hne_vb]; simp [st₁, hrV_st],
           by simp only [State.setReg_arrs]; rw [harr₂ a_sInd hne_sb]; simp [st₁, hsInd_st],
           by simpa [IsPrefixBuffer] using hbuf₂,
           by simp [show r_vLen ≠ r_base by omega, hreg₂ r_vLen hne_vn,
             st₁, show r_vLen ≠ r_base + 1 by omega, hrv_st],
           by simp [show r_nA ≠ r_base by omega, hrnA₂],
           by simp,
           fun a ha => by simp only [State.setReg_arrs]; rw [harr₂ a ha]; simp [st₁, harr_st a ha],
           fun reg hlt hne => by
             simp [show reg ≠ r_base by omega, hreg₂ reg hne,
               st₁, show reg ≠ r_base + 1 by omega, hreg_st reg hlt hne]⟩,
          by rw [hreg₂ r_base (by omega)]; simp [st₁, hrb_st]⟩
      · push Not at hvs
        have hb1 : b = 1 := by simp [b, hvs]
        have hcond : (Expr.op .eq (.read a_sInd (.reg (r_base + 1))) (.const 0)).eval w st₁ = some 0 := by
          simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hv_w, hsInd_st, bitSetList, hv_n, hvs, h0_w, hw]
        have hcur_succ :
            pfx ++ (rVList.take (k + 1)).filter (fun w => decide (w ∉ sSeq)) = cur := by
          rw [htake_succ, List.filter_append]
          simp [cur, hvs]
        have hbuf₁ : IsPrefixBuffer a_buf cur ((rVList.length - (k + 1)) + (rem_ex + 1)) st₁ := by
          unfold IsPrefixBuffer at hbuf_st ⊢
          have hrep : (rVList.length - k) + rem_ex = (rVList.length - (k + 1)) + (rem_ex + 1) := by omega
          rw [← hrep]
          exact hbuf_st
        refine ⟨st₁, _,
          .seq hex₁ (.ite_false hcond (.skip st₁)),
          by dsimp [Expr.cost]; omega,
          ⟨rem_ex + 1,
           by simp [st₁, hrV_st],
           by simp [st₁, hsInd_st],
           by rw [hcur_succ]; simpa [IsPrefixBuffer] using hbuf₁,
           by simp [st₁, show r_vLen ≠ r_base by omega, show r_vLen ≠ r_base + 1 by omega, hrv_st],
           by rw [hcur_succ]; simp [st₁, show r_nA ≠ r_base by omega, show r_nA ≠ r_base + 1 by omega, hrnA_st, cur],
           by simp,
           fun a ha => by simp [st₁, harr_st a ha],
           fun reg hlt hne => by
             simp [st₁, show reg ≠ r_base by omega, show reg ≠ r_base + 1 by omega, hreg_st reg hlt hne]⟩,
          by simp [st₁, hrb_st]⟩
  rcases hLoop s hInv₀ with
    ⟨s₁, t₁, hex₁, ht₁, ⟨rem_ex, _, _, hbuf₁, _, hrnA₁, _, harr₁, hreg₁⟩⟩
  dsimp only at ht₁ hbuf₁ hrnA₁
  rw [List.take_length] at hbuf₁ hrnA₁
  rw [Nat.sub_self, Nat.zero_add] at hbuf₁
  exact ⟨s₁, t₁, rem_ex, hex₁, by omega, hbuf₁, hrnA₁, harr₁, hreg₁⟩

theorem buildTildeAVListProg_exec {w n : ℕ}
    (xSeq : List ℕ) (r : Case3MemberRecord) (sSeq : List ℕ)
    (hs_lt : ∀ v ∈ sSeq, v < n) (hx_lt : ∀ v ∈ xSeq, v < n) (hr_lt : ∀ v ∈ r.vList, v < n)
    (a_sSeq a_xSeq a_rVList a_sInd a_buf a_tildeV
      r_sLen r_xLen r_vLen r_nA r_base : ℕ)
    (hne_sb : a_sSeq ≠ a_buf) (hne_xb : a_xSeq ≠ a_buf)
    (hne_vb : a_rVList ≠ a_buf) (hne_sib : a_sInd ≠ a_buf) (hne_bt : a_buf ≠ a_tildeV)
    (hr_s : r_sLen < r_base) (hr_x : r_xLen < r_base)
    (hr_v : r_vLen < r_base) (hr_nA : r_nA < r_base)
    (hne_sn : r_sLen ≠ r_nA) (hne_xn : r_xLen ≠ r_nA) (hne_vn : r_vLen ≠ r_nA)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hcap_w : sSeq.length + xSeq.length + r.vList.length < 2 ^ w)
    {s : State}
    (hsSeq : s.arrs a_sSeq = sSeq)
    (hxSeq : s.arrs a_xSeq = xSeq)
    (hrV : s.arrs a_rVList = r.vList)
    (hsInd : s.arrs a_sInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ sSeq)))
    (hrsLen : s.regs r_sLen = sSeq.length)
    (hrxLen : s.regs r_xLen = xSeq.length)
    (hrvLen : s.regs r_vLen = r.vList.length) :
    ∃ s' t,
      Exec w
        (buildTildeAVListProg a_sSeq a_xSeq a_rVList a_sInd a_buf a_tildeV
          r_sLen r_xLen r_vLen r_nA r_base) s s' t ∧
      t ≤ 65 * (sSeq.length + xSeq.length + r.vList.length + 1) ∧
      s'.arrs a_tildeV = memberTildeAVList xSeq r sSeq ∧
      s'.regs r_nA = (memberTildeAVList xSeq r sSeq).length ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_tildeV → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, reg ≠ r_nA → s'.regs reg = s.regs reg) := by
  let cap := sSeq.length + xSeq.length + r.vList.length
  have hs_w : sSeq.length < 2 ^ w := by omega
  have hx_w : xSeq.length < 2 ^ w := by omega
  have hv_w : r.vList.length < 2 ^ w := by omega
  have hsx_w : sSeq.length + xSeq.length < 2 ^ w := by omega
  let s₁ := s.setReg (r_base + 1) cap
  have hex₁ : Exec w (.assign (r_base + 1)
      (.op .add (.op .add (.reg r_sLen) (.reg r_xLen)) (.reg r_vLen))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hrsLen, hrxLen, hrvLen, hs_w, hx_w, hv_w, hsx_w, hcap_w, cap])
  rcases initPrefixBufferProg_exec (cap := cap) a_buf (.reg (r_base + 1)) r_nA hw
      (s := s₁) (by simp [s₁, Expr.eval, checkWord, hcap_w, cap]) with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrnA₂, harr₂, hreg₂⟩
  have hs_words : ∀ x ∈ sSeq, x < 2 ^ w := fun x hx => Nat.lt_trans (hs_lt x hx) hn_w
  have hx_words : ∀ x ∈ xSeq, x < 2 ^ w := fun x hx => Nat.lt_trans (hx_lt x hx) hn_w
  have hbuf₂' : IsPrefixBuffer a_buf [] (sSeq.length + (xSeq.length + r.vList.length)) s₂ := by
    unfold IsPrefixBuffer at hbuf₂ ⊢
    have hrep : cap = sSeq.length + (xSeq.length + r.vList.length) := by dsimp [cap]; omega
    rwa [← hrep]
  rcases appendBufSliceProg_exec a_sSeq a_buf r_sLen r_nA r_base
      hne_sb hr_s hr_nA hne_sn hs_words hw (by simp [hs_w])
      (by rw [harr₂ a_sSeq hne_sb]; simp [s₁, hsSeq])
      hbuf₂'
      (by rw [hreg₂ r_sLen hne_sn]; simp [s₁, show r_sLen ≠ r_base + 1 by omega, hrsLen])
      hrnA₂ with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hrnA₃, _, harr₃, hreg₃⟩
  simp only [List.nil_append] at hbuf₃ hrnA₃
  rcases appendBufSliceProg_exec a_xSeq a_buf r_xLen r_nA r_base
      hne_xb hr_x hr_nA hne_xn hx_words hw (by omega)
      (by rw [harr₃ a_xSeq hne_xb, harr₂ a_xSeq hne_xb]; simp [s₁, hxSeq])
      (by simpa [IsPrefixBuffer] using hbuf₃)
      (by rw [hreg₃ r_xLen hr_x hne_xn, hreg₂ r_xLen hne_xn];
          simp [s₁, show r_xLen ≠ r_base + 1 by omega, hrxLen])
      hrnA₃ with
    ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrnA₄, _, harr₄, hreg₄⟩
  let s₅ := s₄.setReg r_base 0
  have hex₅ : Exec w (.assign r_base (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
  have hbuf₅ : IsPrefixBuffer a_buf (sSeq ++ xSeq) (r.vList.length + 0) s₅ := by
    simpa [IsPrefixBuffer, s₅] using hbuf₄
  rcases appendRemVertLoop_exec r.vList sSeq hr_lt
      a_rVList a_sInd a_buf r_vLen r_nA r_base
      hne_vb hne_sib hr_v hr_nA hne_vn hw hn_w hv_w (sSeq ++ xSeq) 0
      (by rw [List.length_append]; omega)
      (by simp [s₅, harr₄ a_rVList hne_vb, harr₃ a_rVList hne_vb, harr₂ a_rVList hne_vb, s₁, hrV])
      (by simp [s₅, harr₄ a_sInd hne_sib, harr₃ a_sInd hne_sib, harr₂ a_sInd hne_sib, s₁, hsInd])
      hbuf₅
      (by simp [s₅, show r_vLen ≠ r_base by omega, hreg₄ r_vLen hr_v hne_vn,
        hreg₃ r_vLen hr_v hne_vn, hreg₂ r_vLen hne_vn, s₁, show r_vLen ≠ r_base + 1 by omega, hrvLen])
      (by simp [s₅, show r_nA ≠ r_base by omega, hrnA₄])
      (by simp [s₅]) with
    ⟨s₆, t₆, rem_ex, hex₆, ht₆, hbuf₆, hrnA₆, harr₆, hreg₆⟩
  change IsPrefixBuffer a_buf (memberTildeAVList xSeq r sSeq) rem_ex s₆ at hbuf₆
  change s₆.regs r_nA = (memberTildeAVList xSeq r sSeq).length at hrnA₆
  have htilde_w : ∀ x ∈ memberTildeAVList xSeq r sSeq, x < 2 ^ w := by
    intro x hx
    unfold memberTildeAVList at hx
    simp only [List.mem_append, List.mem_filter] at hx
    rcases hx with (h1 | h2) | ⟨h3, _⟩
    · exact hs_words x h1
    · exact hx_words x h2
    · exact Nat.lt_trans (hr_lt x h3) hn_w
  have htilde_len_le : (memberTildeAVList xSeq r sSeq).length ≤ cap := by
    unfold memberTildeAVList
    simp only [List.length_append, cap]
    have := List.length_filter_le (fun v => decide (v ∉ sSeq)) r.vList
    omega
  rcases copyBufPrefixProg_exec a_buf a_tildeV r_nA r_base
      hne_bt hr_nA htilde_w hw (by omega) hbuf₆ hrnA₆ with
    ⟨s₇, t₇, hex₇, ht₇, htilde₇, harr₇, hreg₇⟩
  refine ⟨s₇, 6 + (t₂ + (t₃ + (t₄ + (2 + (t₆ + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by simp [Expr.cost] at ht₂; omega,
    htilde₇,
    by rw [hreg₇ r_nA hr_nA, hrnA₆],
    fun a ha₁ ha₂ => by
      rw [harr₇ a ha₂, harr₆ a ha₁]
      simp [s₅, harr₄ a ha₁, harr₃ a ha₁, harr₂ a ha₁, s₁],
    fun reg hlt hne => by
      rw [hreg₇ reg hlt, hreg₆ reg hlt hne]
      simp [s₅, show reg ≠ r_base by omega, hreg₄ reg hlt hne, hreg₃ reg hlt hne,
        hreg₂ reg hne, s₁, show reg ≠ r_base + 1 by omega]⟩

/-- Build `a_zA = bitSetList (prefixRootFinset n_A k_A)` and
`a_xIndA = bitSetList (tildeAXFinset vList xSeq)` on `Fin n_A` (`n_A = vList.length`). -/
def buildTildeABitSetsProg (a_tildeV a_xInd a_zA a_xIndA : Arr)
    (r_nA r_kA r_base : Reg) : Cmd :=
  .seq (.alloc a_zA (.reg r_nA))
    (.seq (.assign r_base (.const 0))
      (.seq (forUp r_base (.reg r_kA) (.write a_zA (.reg r_base) (.const 1)))
        (.seq (.alloc a_xIndA (.reg r_nA))
          (.seq (.assign r_base (.const 0))
            (forUp r_base (.reg r_nA)
              (.write a_xIndA (.reg r_base)
                (.read a_xInd (.read a_tildeV (.reg r_base)))))))))

theorem buildTildeABitSetsProg_exec {w n : ℕ}
    (vList xSeq : List ℕ) (k_A : ℕ)
    (hv_lt : ∀ v ∈ vList, v < n) (hk_le : k_A ≤ vList.length)
    (a_tildeV a_xInd a_zA a_xIndA r_nA r_kA r_base : ℕ)
    (hne_vz : a_tildeV ≠ a_zA) (hne_vx : a_tildeV ≠ a_xIndA)
    (hne_xz : a_xInd ≠ a_zA) (hne_xx : a_xInd ≠ a_xIndA) (hne_zx : a_zA ≠ a_xIndA)
    (hr_nA : r_nA < r_base) (hr_kA : r_kA < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hnA_w : vList.length < 2 ^ w)
    {s : State}
    (hvList : s.arrs a_tildeV = vList)
    (hxInd : s.arrs a_xInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)))
    (hrnA : s.regs r_nA = vList.length)
    (hrkA : s.regs r_kA = k_A) :
    ∃ s' t,
      Exec w (buildTildeABitSetsProg a_tildeV a_xInd a_zA a_xIndA r_nA r_kA r_base) s s' t ∧
      t ≤ 28 * vList.length + 20 ∧
      s'.arrs a_zA = bitSetList (prefixRootFinset vList.length k_A) ∧
      s'.arrs a_xIndA = bitSetList (tildeAXFinset vList xSeq) ∧
      (∀ a : ℕ, a ≠ a_zA → a ≠ a_xIndA → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, s'.regs reg = s.regs reg) := by
  let n_A := vList.length
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : k_A < 2 ^ w := by omega
  let s₁ := s.setArr a_zA (List.replicate n_A 0)
  have hex₁ : Exec w (.alloc a_zA (.reg r_nA)) s s₁ (1 + n_A) :=
    .alloc (by simp [Expr.eval, checkWord, hrnA, hnA_w, n_A])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let InvZ (j : ℕ) (st : State) : Prop :=
    st.arrs a_zA = List.ofFn (fun i : Fin n_A => if i.1 < j then 1 else 0) ∧
    st.regs r_kA = k_A ∧
    st.regs r_base = j ∧
    (∀ a : ℕ, a ≠ a_zA → st.arrs a = s.arrs a) ∧
    (∀ reg < r_base, st.regs reg = s.regs reg)
  have hInvZ₀ : InvZ 0 s₂ := by
    refine ⟨?_, by simp [s₂, s₁, show r_kA ≠ r_base by omega, hrkA],
      by simp [s₂], fun a ha => by simp [s₂, s₁, ha],
      fun reg hlt => by simp [s₂, s₁, show reg ≠ r_base by omega]⟩
    simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self]
    apply List.ext_getElem (by simp)
    intro i _ _
    simp
  have hLoopZ :
      ⦃InvZ 0⦄[w]
        forUp r_base (.reg r_kA) (.write a_zA (.reg r_base) (.const 1))
      ⦃InvZ k_A⦄ ≤ fun _ => 3 + k_A * (7 + 3) := by
    apply Triple.forUp_const InvZ k_A 3 hw hk_w
    · intro j _ st ⟨_, hrk_st, hrb_st, _, _⟩
      exact ⟨hrb_st, by simp [Expr.eval, checkWord, hrk_st, hk_w]⟩
    · intro j hj st ⟨hz_st, hrk_st, hrb_st, harr_st, hreg_st⟩
      have hj_nA : j < n_A := Nat.lt_of_lt_of_le hj hk_le
      have hj_w : j < 2 ^ w := by omega
      have hj_len : j < (st.arrs a_zA).length := by rw [hz_st, List.length_ofFn]; exact hj_nA
      let st₁ := st.writeArr a_zA j 1
      have hex_w : Exec w (.write a_zA (.reg r_base) (.const 1)) st st₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hrb_st, hj_w])
          (by simp [Expr.eval, checkWord, hw]) hj_len
      have hz_eq :
          st₁.arrs a_zA = List.ofFn (fun i : Fin n_A => if i.1 < j + 1 then 1 else 0) := by
        simp only [st₁, State.writeArr_arrs_self, hz_st]
        apply List.ext_getElem (by simp)
        intro i hi₁ hi₂
        rw [List.getElem_ofFn]
        by_cases hij : i = j
        · subst hij; simp
        · rw [List.getElem_set_ne (Ne.symm hij), List.getElem_ofFn]
          have : (i < j + 1) ↔ (i < j) := by omega
          simp [this]
      exact ⟨st₁, 3, hex_w, le_rfl,
        ⟨hz_eq,
         by simp [st₁, show r_kA ≠ r_base by omega, hrk_st],
         by simp,
         fun a ha => by simp [st₁, ha, harr_st a ha],
         fun reg hlt => by simp [st₁, show reg ≠ r_base by omega, hreg_st reg hlt]⟩,
        by simp [st₁, hrb_st]⟩
  rcases hLoopZ s₂ hInvZ₀ with ⟨s₃, t₃, hex₃, ht₃, ⟨hz₃, _, _, harr₃, hreg₃⟩⟩
  dsimp only at ht₃
  have hz₃_eq : s₃.arrs a_zA = bitSetList (prefixRootFinset n_A k_A) := by
    rw [hz₃]
    apply List.ext_getElem (by simp [length_bitSetList])
    intro i _ _
    simp [bitSetList]
  have hrnA₃ : s₃.regs r_nA = n_A := by rw [hreg₃ r_nA hr_nA, hrnA]
  let s₄ := s₃.setArr a_xIndA (List.replicate n_A 0)
  have hex₄ : Exec w (.alloc a_xIndA (.reg r_nA)) s₃ s₄ (1 + n_A) :=
    .alloc (by simp [Expr.eval, checkWord, hrnA₃, hnA_w, n_A])
  let s₅ := s₄.setReg r_base 0
  have hex₅ : Exec w (.assign r_base (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let InvX (j : ℕ) (st : State) : Prop :=
    st.arrs a_xIndA =
      List.ofFn (fun i : Fin n_A => if i.1 < j ∧ (vList[i.1]'i.2) ∈ xSeq then 1 else 0) ∧
    st.regs r_nA = n_A ∧
    st.regs r_base = j ∧
    (∀ a : ℕ, a ≠ a_zA → a ≠ a_xIndA → st.arrs a = s.arrs a) ∧
    st.arrs a_zA = bitSetList (prefixRootFinset n_A k_A) ∧
    (∀ reg < r_base, st.regs reg = s.regs reg)
  have hInvX₀ : InvX 0 s₅ := by
    refine ⟨?_, by simp [s₅, s₄, show r_nA ≠ r_base by omega, hrnA₃],
      by simp [s₅],
      fun a ha₁ ha₂ => by simp [s₅, s₄, ha₂, harr₃ a ha₁],
      by simp [s₅, s₄, hne_zx, hz₃_eq],
      fun reg hlt => by simp [s₅, s₄, show reg ≠ r_base by omega, hreg₃ reg hlt]⟩
    simp only [s₅, s₄, State.setReg_arrs, State.setArr_arrs_self]
    apply List.ext_getElem (by simp)
    intro i _ _
    simp
  have hLoopX :
      ⦃InvX 0⦄[w]
        forUp r_base (.reg r_nA)
          (.write a_xIndA (.reg r_base) (.read a_xInd (.read a_tildeV (.reg r_base))))
      ⦃InvX n_A⦄ ≤ fun _ => 3 + n_A * (7 + 5) := by
    apply Triple.forUp_const InvX n_A 5 hw hnA_w
    · intro j _ st ⟨_, hrn_st, hrb_st, _, _, _⟩
      exact ⟨hrb_st, by simp [Expr.eval, checkWord, hrn_st, hnA_w, n_A]⟩
    · intro j hj st ⟨hx_st, hrn_st, hrb_st, harr_st, hz_st, hreg_st⟩
      have hj_w : j < 2 ^ w := by omega
      let v := vList[j]'hj
      have hv_n : v < n := hv_lt v (List.getElem_mem hj)
      have hv_w : v < 2 ^ w := by omega
      have hv_st : st.arrs a_tildeV = vList := (harr_st a_tildeV hne_vz hne_vx).trans hvList
      have hxI_st : st.arrs a_xInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)) :=
        (harr_st a_xInd hne_xz hne_xx).trans hxInd
      have hj_vlen : j < (st.arrs a_tildeV).length := by rw [hv_st]; exact hj
      have hget_v : (st.arrs a_tildeV)[j]'hj_vlen = v := by simp only [hv_st, v]
      have hv_xlen : v < (st.arrs a_xInd).length := by rw [hxI_st, length_bitSetList]; exact hv_n
      let b := if v ∈ xSeq then 1 else 0
      have hget_b : (st.arrs a_xInd)[v]'hv_xlen = b := by simp [hxI_st, bitSetList, b]
      have hb_w : b < 2 ^ w := by dsimp [b]; split_ifs <;> omega
      have hj_xAlen : j < (st.arrs a_xIndA).length := by rw [hx_st, List.length_ofFn]; exact hj
      let st₁ := st.writeArr a_xIndA j b
      have hex_w :
          Exec w (.write a_xIndA (.reg r_base) (.read a_xInd (.read a_tildeV (.reg r_base))))
            st st₁ 5 :=
        .write (by simp [Expr.eval, checkWord, hrb_st, hj_w])
          (by simp [Expr.eval, checkWord, hrb_st, hj_w, hj_vlen, hget_v, hv_w, hv_xlen, hget_b, hb_w])
          hj_xAlen
      have hx_eq :
          st₁.arrs a_xIndA =
            List.ofFn (fun i : Fin n_A =>
              if i.1 < j + 1 ∧ (vList[i.1]'i.2) ∈ xSeq then 1 else 0) := by
        simp only [st₁, State.writeArr_arrs_self, hx_st]
        apply List.ext_getElem (by simp)
        intro i hi₁ hi₂
        rw [List.getElem_ofFn]
        by_cases hij : i = j
        · subst hij
          rw [List.getElem_set_self]
          simp [b, v]
        · rw [List.getElem_set_ne (Ne.symm hij), List.getElem_ofFn]
          have : (i < j + 1) ↔ (i < j) := by omega
          simp [this]
      exact ⟨st₁, 5, hex_w, le_rfl,
        ⟨hx_eq,
         by simp [st₁, show r_nA ≠ r_base by omega, hrn_st],
         by simp,
         fun a ha₁ ha₂ => by simp [st₁, ha₂, harr_st a ha₁ ha₂],
         by simp [st₁, hne_zx, hz_st],
         fun reg hlt => by simp [st₁, show reg ≠ r_base by omega, hreg_st reg hlt]⟩,
        by simp [st₁, hrb_st]⟩
  rcases hLoopX s₅ hInvX₀ with ⟨s₆, t₆, hex₆, ht₆, ⟨hx₆, _, _, harr₆, hz₆, hreg₆⟩⟩
  dsimp only at ht₆
  have hx₆_eq : s₆.arrs a_xIndA = bitSetList (tildeAXFinset vList xSeq) := by
    rw [hx₆]
    apply List.ext_getElem (by simp [length_bitSetList, n_A])
    intro i _ _
    simp [bitSetList, n_A]
  refine ⟨s₆, (1 + n_A) + (2 + (t₃ + ((1 + n_A) + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega,
    hz₆, hx₆_eq, harr₆, hreg₆⟩

end GraphMinor.Compute
