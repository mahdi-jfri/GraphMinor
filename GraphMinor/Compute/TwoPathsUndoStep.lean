module

public import GraphMinor.Compute.TwoPathsUndoRec
import GraphMinor.Compute.TwoPathsSweep
import GraphMinor.Compute.TwoPathsChild
import GraphMinor.Compute.TwoPathsChord
import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.HP25.Lemma43Fan

/-!
# One collapse record on the successor array: the proof

`recProg_exec`: under `SpliceOK`, `recProg` (`TwoPathsUndoRec.lean`) turns the successor array of
the two paths `Q, R` into that of `spliceT2Lists y z N Q R`. The proof follows the five branches of
the program: empty window; `z` right after `y` on `Q` or on `R` (splice forwards); `y` right after
`z` on `Q` or on `R` (splice backwards); and neither, where no path uses `y z`
(`linkArr_succ_iff`).
-/

namespace GraphMinor.Compute.TwoPaths

public section

variable {w V : ℕ}

/-- The entries of a list after a `drop`. -/
theorem getElem?_of_drop {rec l : List ℕ} {o : ℕ} (h : rec.drop o = l) (i : ℕ) :
    rec[o + i]? = l[i]? := by
  rw [← h, List.getElem?_drop]

/-- The splice of a list that has `z` right after `y`. -/
theorem spliceT2Lists_fwdQ {y z : ℕ} {N Q R l₀ l₁ : List ℕ} (hN : N ≠ []) (hQ : Q.Nodup)
    (hQs : Q = l₀ ++ y :: z :: l₁) :
    spliceT2Lists y z N Q R = (l₀ ++ y :: N ++ z :: l₁, R) := by
  have hu : t2Uses y z N Q = true := (t2Uses_iff _ _ _ _).mpr ⟨hN, hQs ▸ isListEdge_mid _ _ _ _⟩
  subst hQs
  simp only [spliceT2Lists, hu, ↓reduceIte, rule2PocketChain_fwd hQ]

theorem spliceT2Lists_bwdQ {y z : ℕ} {N Q R l₀ l₁ : List ℕ} (hN : N ≠ []) (hQ : Q.Nodup)
    (hQs : Q = l₀ ++ z :: y :: l₁) :
    spliceT2Lists y z N Q R = (l₀ ++ z :: N.reverse ++ y :: l₁, R) := by
  have hu : t2Uses y z N Q = true :=
    (t2Uses_iff _ _ _ _).mpr ⟨hN, hQs ▸ (isListEdge_mid _ _ _ _).symm⟩
  subst hQs
  simp only [spliceT2Lists, hu, ↓reduceIte, rule2PocketChain_bwd hQ]

theorem spliceT2Lists_R {y z : ℕ} {N Q R : List ℕ} (hyQ : y ∉ Q) :
    spliceT2Lists y z N Q R =
      if t2Uses y z N R then (Q, HP25.rule2PocketChain y z N R) else (Q, R) := by
  have hu : t2Uses y z N Q = false :=
    Bool.eq_false_iff.mpr fun h => hyQ ((t2Uses_iff _ _ _ _).mp h).2.mem_left
  simp only [spliceT2Lists, hu, Bool.false_eq_true, ↓reduceIte]

/-- **Reading a record.** -/
theorem recRead_exec (hw : 1 < 2 ^ w) {st : State} {j o y z : ℕ} {OFF rec N rest : List ℕ}
    (hcnt : st.regs rUdcnt = j) (hOFF : st.arrs aUdOff = OFF) (hj : j < OFF.length)
    (hoj : OFF[j] = o) (hjw : j < 2 ^ w) (hrec : st.arrs aT2Rec = rec)
    (hdrop : rec.drop o = y :: z :: N.length :: (N ++ rest))
    (hyw : y < 2 ^ w) (hzw : z < 2 ^ w) (hrw : rec.length + 3 < 2 ^ w) :
    ∃ s₅, Exec w recRead st s₅ 20 ∧ Keeps recRegs [] st s₅ ∧ s₅.regs rUdy = y ∧
      s₅.regs rUdz = z ∧ s₅.regs rUdk = N.length ∧ s₅.regs rUdo = o + 3 := by
  have hg := getElem?_of_drop hdrop
  have hlen : o + 3 + N.length ≤ rec.length := by
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons, List.length_append] at this
    omega
  have hread : ∀ (s : State) (E : Expr) (i v : ℕ), s.arrs aT2Rec = rec →
      E.eval w s = some (o + i) → rec[o + i]? = some v → v < 2 ^ w →
      (Expr.read aT2Rec E).eval w s = some v := by
    intro s E i v hs hE hv hvw
    obtain ⟨h, e⟩ := List.getElem?_eq_some_iff.mp hv
    have := read_eval (w := w) (s := s) (a := aT2Rec) hE (by rw [hs]; exact h)
      (by simp only [hs, e]; exact hvw)
    simpa only [hs, e] using this
  have hoff : (Expr.read aUdOff (.reg rUdcnt)).eval w st = some o := by
    have := read_eval (w := w) (s := st) (a := aUdOff) (E := .reg rUdcnt)
      (reg_eval hcnt hjw) (by rw [hOFF]; exact hj) (by simp only [hOFF, hoj]; omega)
    simpa only [hOFF, hoj] using this
  set s₁ := st.setReg rUdo o
  have hry : (Expr.read aT2Rec (.reg rUdo)).eval w s₁ = some y :=
    hread s₁ _ 0 y (by simp [s₁, hrec]) (reg_eval (v := o + 0) (by simp [s₁]) (by omega))
      (by rw [hg]; rfl) hyw
  set s₂ := s₁.setReg rUdy y
  have hrz : (Expr.read aT2Rec (.op .add (.reg rUdo) (.const 1))).eval w s₂ = some z :=
    hread s₂ _ 1 z (by simp [s₂, s₁, hrec])
      (add_eval (reg_eval (v := o) (by simp [s₂, s₁]) (by omega)) (const_eval' (w := w) hw)
        (by omega)) (by rw [hg]; rfl) hzw
  set s₃ := s₂.setReg rUdz z
  have hrk : (Expr.read aT2Rec (.op .add (.reg rUdo) (.const 2))).eval w s₃ = some N.length :=
    hread s₃ _ 2 N.length (by simp [s₃, s₂, s₁, hrec])
      (add_eval (reg_eval (v := o) (by simp [s₃, s₂, s₁]) (by omega))
        (const_eval' (w := w) (by omega)) (by omega)) (by rw [hg]; rfl) (by omega)
  set s₄ := s₃.setReg rUdk N.length
  have hr3 : (Expr.op .add (.reg rUdo) (.const 3)).eval w s₄ = some (o + 3) :=
    add_eval (reg_eval (v := o) (by simp [s₄, s₃, s₂, s₁]) (by omega))
      (const_eval' (w := w) (by omega)) (by omega)
  refine ⟨s₄.setReg rUdo (o + 3), .seq (.assign hoff) (.seq (.assign hry) (.seq (.assign hrz)
    (.seq (.assign hrk) (.assign hr3)))), ?_, by simp [s₄, s₃, s₂], by simp [s₄, s₃],
    by simp [s₄], by simp⟩
  exact (((((Keeps.refl _ _ _).setReg (by simp [recRegs]) _).setReg (by simp [recRegs]) _).setReg
    (by simp [recRegs]) _).setReg (by simp [recRegs]) _).setReg (by simp [recRegs]) _

/-- The common part of a branch of `recCase`: set `p` and the direction, then run the loop. -/
theorem recBranch_exec {s : State} {rp p f : ℕ} {Lnew : List ℕ} {B : ℕ}
    (hp : s.regs rp = p) (hpw : p < 2 ^ w) (hfw : f < 2 ^ w)
    (hloop : ∃ s' c, Exec w (insLoop aT2Rec) ((s.setReg rUdp p).setReg rUdfwd f) s' c ∧ c ≤ B ∧
      Keeps [rUdi, rUdx, rUdp] [aUdNxt] ((s.setReg rUdp p).setReg rUdfwd f) s' ∧
      s'.arrs aUdNxt = Lnew) :
    ∃ s' c, Exec w (.seq (.assign rUdp (.reg rp)) (.seq (.assign rUdfwd (.const f))
      (insLoop aT2Rec))) s s' c ∧ c ≤ B + 4 ∧ Keeps recRegs [aUdNxt] s s' ∧
      s'.arrs aUdNxt = Lnew := by
  obtain ⟨s', c, hex, hc, hks, hn⟩ := hloop
  refine ⟨s', _, .seq (.assign (reg_eval hp hpw)) (.seq (.assign (const_eval' hfw)) hex),
    by simp only [Expr.cost]; omega, ?_, hn⟩
  exact (((Keeps.refl _ _ _).setReg (by simp [recRegs]) _).setReg (by simp [recRegs]) _).trans
    (hks.mono (by simp [recRegs]) (by simp)) (fun r h => h) (fun a h => h)

/-- The facts of the state after `recRead` that `recCase` needs. -/
structure RecState (V : ℕ) (rec : List ℕ) (o y z : ℕ) (N : List ℕ) (s : State) : Prop where
  hy : s.regs rUdy = y
  hz : s.regs rUdz = z
  hk : s.regs rUdk = N.length
  ho : s.regs rUdo = o + 3
  hrec : s.arrs aT2Rec = rec
  hwin : ∀ i < N.length, rec.getD (o + 3 + i) 0 = N.getD i 0
  hlen : o + 3 + N.length ≤ rec.length

/-- **Splicing on the first list, forwards.** -/
theorem recFwd_exec (hw : 1 < 2 ^ w) {s : State} {rec N l₀ l₁ L' : List ℕ} {o y z : ℕ}
    (hs : RecState V rec o y z N s) (hnxt : s.arrs aUdNxt = linkArr V (l₀ ++ y :: z :: l₁) L')
    (hnew : (l₀ ++ y :: N ++ z :: l₁).Nodup)
    (hL' : ∀ v ∈ l₀ ++ y :: N ++ z :: l₁, v ∉ L' ∧ v < V) (hyV : y < V) (hVw : V < 2 ^ w)
    (hrw : rec.length < 2 ^ w) :
    ∃ s' c, Exec w (.seq (.assign rUdp (.reg rUdy)) (.seq (.assign rUdfwd (.const 1))
      (insLoop aT2Rec))) s s' c ∧ c ≤ 5 + 24 * N.length + 4 ∧ Keeps recRegs [aUdNxt] s s' ∧
      s'.arrs aUdNxt = linkArr V (l₀ ++ y :: N ++ z :: l₁) L' :=
  recBranch_exec hs.hy (by omega) hw (spliceFwd_exec (S := rec) (N := N) (l₀ := l₀) (l₁ := l₁) (L' := L') (o := o + 3)
    (by decide) hw (by simp [hs.ho])
    (by simp [hs.hk]) (by simp) (by simp) (by simp [hs.hrec]) hs.hwin (by have := hs.hlen; omega)
    (by simp [hnxt]) hnew hL' hVw (by have := hs.hlen; omega))

/-- **Splicing on the first list, backwards.** -/
theorem recBwd_exec (hw : 1 < 2 ^ w) {s : State} {rec N l₀ l₁ L' : List ℕ} {o y z : ℕ}
    (hs : RecState V rec o y z N s) (hnxt : s.arrs aUdNxt = linkArr V (l₀ ++ z :: y :: l₁) L')
    (hnew : (l₀ ++ z :: N.reverse ++ y :: l₁).Nodup)
    (hL' : ∀ v ∈ l₀ ++ z :: N.reverse ++ y :: l₁, v ∉ L' ∧ v < V) (hzV : z < V)
    (hVw : V < 2 ^ w) (hrw : rec.length < 2 ^ w) :
    ∃ s' c, Exec w (.seq (.assign rUdp (.reg rUdz)) (.seq (.assign rUdfwd (.const 0))
      (insLoop aT2Rec))) s s' c ∧ c ≤ 5 + 24 * N.length + 4 ∧ Keeps recRegs [aUdNxt] s s' ∧
      s'.arrs aUdNxt = linkArr V (l₀ ++ z :: N.reverse ++ y :: l₁) L' :=
  recBranch_exec hs.hz (by omega) (by omega) (spliceBwd_exec (S := rec) (N := N) (l₀ := l₀) (l₁ := l₁) (L' := L') (o := o + 3)
    (by decide) hw (by simp [hs.ho])
    (by simp [hs.hk]) (by simp) (by simp) (by simp [hs.hrec]) hs.hwin (by have := hs.hlen; omega)
    (by simp [hnxt]) hnew hL' hVw (by have := hs.hlen; omega))

/-- The membership of a spliced list. -/
theorem mem_splice_iff {v p q : ℕ} {M l₀ l₁ : List ℕ} :
    v ∈ l₀ ++ p :: M ++ q :: l₁ ↔ v ∈ l₀ ++ p :: q :: l₁ ∨ v ∈ M := by
  simp only [List.mem_append, List.mem_cons]; tauto

/-- **The test and the splice of one record.** -/
theorem recCase_exec (hw : 1 < 2 ^ w) {s : State} {rec N Q R : List ℕ} {o y z : ℕ}
    (hs : RecState V rec o y z N s) (hnxt : s.arrs aUdNxt = linkArr V Q R)
    (hok : SpliceOK y z N Q R) (hyV : y < V) (hzV : z < V) (hNV : ∀ x ∈ N, x < V)
    (hQV : ∀ v ∈ Q, v < V) (hRV : ∀ v ∈ R, v < V) (hVw : 2 * V + 1 < 2 ^ w)
    (hrw : rec.length < 2 ^ w) :
    ∃ s' c, Exec w recCase s s' c ∧ c ≤ 24 + 24 * N.length ∧ Keeps recRegs [aUdNxt] s s' ∧
      s'.arrs aUdNxt = linkArr V (spliceT2Lists y z N Q R).1 (spliceT2Lists y z N Q R).2 := by
  obtain ⟨hQnd, hRnd, hdisj, hwin⟩ := hok
  have hlk : (linkArr V Q R).length = V := length_linkArr _ _ _
  have hsum : ∀ v, nextOf Q v + nextOf R v ≤ 2 * V := fun v => by
    have := nextOf_le hQV v; have := nextOf_le hRV v; omega
  have htest : ∀ (ra rb : ℕ) (a b : ℕ), s.regs ra = a → s.regs rb = b → a < V → b < V →
      (Expr.op .eq (.read aUdNxt (.reg ra)) (.op .add (.reg rb) (.const 1))).eval w s =
        some (if nextOf Q a + nextOf R a = b + 1 then 1 else 0) := by
    intro ra rb a b ha hb haV hbV
    have hra : (Expr.read aUdNxt (.reg ra)).eval w s = some (nextOf Q a + nextOf R a) := by
      have := read_eval (w := w) (s := s) (a := aUdNxt) (E := .reg ra) (reg_eval ha (by omega))
        (by rw [hnxt, hlk]; exact haV) (by simp only [hnxt, linkArr_getElem]; have := hsum a; omega)
      simpa only [hnxt, linkArr_getElem] using this
    exact eq_eval hra (add_eval (reg_eval hb (by omega)) (const_eval' (w := w) hw) (by omega)) hw
  have hkr : (Expr.reg rUdk).eval w s = some N.length :=
    reg_eval hs.hk (by have := hs.hlen; omega)
  by_cases hN0 : N = []
  · subst hN0
    have hsp : spliceT2Lists y z [] Q R = (Q, R) := by simp [spliceT2Lists, t2Uses]
    refine ⟨s, _, .ite_false (by simpa using hkr) (.skip _), by simp, Keeps.refl _ _ _, ?_⟩
    rw [hsp, hnxt]
  have hNne : N.length ≠ 0 := fun h => hN0 (List.eq_nil_of_length_eq_zero h)
  have hc1 := htest rUdy rUdz y z hs.hy hs.hz hyV hzV
  by_cases ht1 : nextOf Q y + nextOf R y = z + 1
  · rw [if_pos ht1] at hc1
    rcases (linkArr_succ_iff hQnd hRnd hdisj y z).mp ht1 with ⟨l₀, l₁, hQs⟩ | ⟨l₀, l₁, hRs⟩
    · have hsp := spliceT2Lists_fwdQ (R := R) hN0 hQnd hQs
      obtain ⟨hNnd, -, -, hNout⟩ := hwin (Or.inl ((t2Uses_iff _ _ _ _).mpr
        ⟨hN0, hQs ▸ isListEdge_mid _ _ _ _⟩))
      subst hQs
      obtain ⟨s', c, hex, hc, hks, hn⟩ := recFwd_exec hw hs hnxt
        (nodup_insert_middle hQnd hNnd (fun x hx => (hNout x hx).1))
        (fun v hv => by
          rcases mem_splice_iff.mp hv with h | h
          · exact ⟨fun h' => hdisj h h', hQV v h⟩
          · exact ⟨(hNout v h).2, hNV v h⟩) hyV (by omega) hrw
      refine ⟨s', _, .ite_true hkr hNne (.ite_true hc1 one_ne_zero hex), ?_, hks,
        by rw [hsp]; exact hn⟩
      simp only [Expr.cost] at hc ⊢; omega
    · have hyQ : y ∉ Q := fun h => hdisj h (by rw [hRs]; simp)
      have hu : t2Uses y z N R = true :=
        (t2Uses_iff _ _ _ _).mpr ⟨hN0, hRs ▸ isListEdge_mid _ _ _ _⟩
      obtain ⟨hNnd, -, -, hNout⟩ := hwin (Or.inr hu)
      have hsp : spliceT2Lists y z N Q R = (Q, l₀ ++ y :: N ++ z :: l₁) := by
        rw [spliceT2Lists_R hyQ, if_pos hu, hRs, rule2PocketChain_fwd (hRs ▸ hRnd)]
      subst hRs
      obtain ⟨s', c, hex, hc, hks, hn⟩ := recFwd_exec hw hs (by rw [hnxt, linkArr_comm])
        (nodup_insert_middle hRnd hNnd (fun x hx => (hNout x hx).2))
        (fun v hv => by
          rcases mem_splice_iff.mp hv with h | h
          · exact ⟨fun h' => hdisj h' h, hRV v h⟩
          · exact ⟨(hNout v h).1, hNV v h⟩) hyV (by omega) hrw
      refine ⟨s', _, .ite_true hkr hNne (.ite_true hc1 one_ne_zero hex), ?_, hks,
        by rw [hsp, linkArr_comm]; exact hn⟩
      simp only [Expr.cost] at hc ⊢; omega
  · rw [if_neg ht1] at hc1
    have hc2 := htest rUdz rUdy z y hs.hz hs.hy hzV hyV
    by_cases ht2 : nextOf Q z + nextOf R z = y + 1
    · rw [if_pos ht2] at hc2
      rcases (linkArr_succ_iff hQnd hRnd hdisj z y).mp ht2 with ⟨l₀, l₁, hQs⟩ | ⟨l₀, l₁, hRs⟩
      · have hsp := spliceT2Lists_bwdQ (R := R) hN0 hQnd hQs
        obtain ⟨hNnd, -, -, hNout⟩ := hwin (Or.inl ((t2Uses_iff _ _ _ _).mpr
          ⟨hN0, hQs ▸ (isListEdge_mid _ _ _ _).symm⟩))
        subst hQs
        obtain ⟨s', c, hex, hc, hks, hn⟩ := recBwd_exec hw hs hnxt
          (nodup_insert_middle hQnd (List.nodup_reverse.mpr hNnd)
            (fun x hx => (hNout x (List.mem_reverse.mp hx)).1))
          (fun v hv => by
            rcases mem_splice_iff.mp hv with h | h
            · exact ⟨fun h' => hdisj h h', hQV v h⟩
            · have h := List.mem_reverse.mp h
              exact ⟨(hNout v h).2, hNV v h⟩) hzV (by omega) hrw
        refine ⟨s', _, .ite_true hkr hNne (.ite_false hc1 (.ite_true hc2 one_ne_zero hex)), ?_,
          hks, by rw [hsp]; exact hn⟩
        simp only [Expr.cost] at hc ⊢; omega
      · have hyQ : y ∉ Q := fun h => hdisj h (by rw [hRs]; simp)
        have hu : t2Uses y z N R = true :=
          (t2Uses_iff _ _ _ _).mpr ⟨hN0, hRs ▸ (isListEdge_mid _ _ _ _).symm⟩
        obtain ⟨hNnd, -, -, hNout⟩ := hwin (Or.inr hu)
        have hsp : spliceT2Lists y z N Q R = (Q, l₀ ++ z :: N.reverse ++ y :: l₁) := by
          rw [spliceT2Lists_R hyQ, if_pos hu, hRs, rule2PocketChain_bwd (hRs ▸ hRnd)]
        subst hRs
        obtain ⟨s', c, hex, hc, hks, hn⟩ := recBwd_exec hw hs (by rw [hnxt, linkArr_comm])
          (nodup_insert_middle hRnd (List.nodup_reverse.mpr hNnd)
            (fun x hx => (hNout x (List.mem_reverse.mp hx)).2))
          (fun v hv => by
            rcases mem_splice_iff.mp hv with h | h
            · exact ⟨fun h' => hdisj h' h, hRV v h⟩
            · have h := List.mem_reverse.mp h
              exact ⟨(hNout v h).1, hNV v h⟩) hzV (by omega) hrw
        refine ⟨s', _, .ite_true hkr hNne (.ite_false hc1 (.ite_true hc2 one_ne_zero hex)), ?_,
          hks, by rw [hsp, linkArr_comm]; exact hn⟩
        simp only [Expr.cost] at hc ⊢; omega
    · rw [if_neg ht2] at hc2
      have hno : ∀ L, L.Nodup → (L = Q ∨ L = R) → ¬ HP25.IsListEdge L y z := by
        intro L hL hLQR he
        obtain ⟨l₀, l₁, h | h⟩ := he.exists_split
        · exact ht1 ((linkArr_succ_iff hQnd hRnd hdisj y z).mpr (by
            rcases hLQR with rfl | rfl
            · exact Or.inl ⟨l₀, l₁, h⟩
            · exact Or.inr ⟨l₀, l₁, h⟩))
        · exact ht2 ((linkArr_succ_iff hQnd hRnd hdisj z y).mpr (by
            rcases hLQR with rfl | rfl
            · exact Or.inl ⟨l₀, l₁, h⟩
            · exact Or.inr ⟨l₀, l₁, h⟩))
      have hsp : spliceT2Lists y z N Q R = (Q, R) := by
        have hq : t2Uses y z N Q = false := Bool.eq_false_iff.mpr fun h =>
          hno Q hQnd (Or.inl rfl) ((t2Uses_iff _ _ _ _).mp h).2
        have hr : t2Uses y z N R = false := Bool.eq_false_iff.mpr fun h =>
          hno R hRnd (Or.inr rfl) ((t2Uses_iff _ _ _ _).mp h).2
        simp only [spliceT2Lists, hq, hr, Bool.false_eq_true, ↓reduceIte]
      refine ⟨s, _, .ite_true hkr hNne (.ite_false hc1 (.ite_false hc2 (.skip _))),
        by simp only [Expr.cost]; omega, Keeps.refl _ _ _, by rw [hsp, hnxt]⟩

/-- **One collapse record.** Under `SpliceOK`, `recProg` turns the successor array of `Q, R` into
that of `spliceT2Lists y z N Q R`, where the record `y, z, |N|, N` starts at offset
`aUdOff[rUdcnt]` of `aT2Rec`. -/
theorem recProg_exec (hw : 1 < 2 ^ w) {st : State} {j o y z : ℕ} {OFF rec N rest Q R : List ℕ}
    (hcnt : st.regs rUdcnt = j) (hOFF : st.arrs aUdOff = OFF) (hj : j < OFF.length)
    (hoj : OFF[j] = o) (hjw : j < 2 ^ w) (hrec : st.arrs aT2Rec = rec)
    (hdrop : rec.drop o = y :: z :: N.length :: (N ++ rest))
    (hnxt : st.arrs aUdNxt = linkArr V Q R) (hok : SpliceOK y z N Q R)
    (hyV : y < V) (hzV : z < V) (hNV : ∀ x ∈ N, x < V) (hQV : ∀ v ∈ Q, v < V)
    (hRV : ∀ v ∈ R, v < V) (hVw : 2 * V + 1 < 2 ^ w) (hrw : rec.length + 3 < 2 ^ w) :
    ∃ st' c, Exec w recProg st st' c ∧ c ≤ 44 + 24 * N.length ∧
      Keeps recRegs [aUdNxt] st st' ∧
      st'.arrs aUdNxt = linkArr V (spliceT2Lists y z N Q R).1 (spliceT2Lists y z N Q R).2 := by
  obtain ⟨s₅, hex₅, hk₅, hy, hz, hk, ho⟩ := recRead_exec hw hcnt hOFF hj hoj hjw hrec hdrop
    (by omega) (by omega) hrw
  have hg := getElem?_of_drop hdrop
  have hlen : o + 3 + N.length ≤ rec.length := by
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons, List.length_append] at this
    omega
  have hrs : RecState V rec o y z N s₅ := ⟨hy, hz, hk, ho,
    by rw [hk₅.2 aT2Rec (by simp)]; exact hrec, fun i hi => by
      rw [List.getD_eq_getElem?_getD, show o + 3 + i = o + (3 + i) by omega, hg,
        List.getD_eq_getElem?_getD]
      simp [Nat.add_comm 3 i, List.getElem?_append_left hi], hlen⟩
  obtain ⟨s', c, hex, hc, hks, hn⟩ := recCase_exec hw hrs
    (by rw [hk₅.2 aUdNxt (by simp)]; exact hnxt) hok hyV hzV hNV hQV hRV hVw (by omega)
  exact ⟨s', _, .seq hex₅ hex, by omega, (hk₅.mono (fun r h => h) (by simp)).trans hks
    (fun r h => h) (fun a h => h), hn⟩

end

end GraphMinor.Compute.TwoPaths
