module

public import GraphMinor.Compute.CrossingLoopTrial
public import GraphMinor.Crossing.Sparse101
public import GraphMinor.Crossing.Sparse102
public import GraphMinor.Crossing.Sparse72
public import GraphMinor.Crossing.LinkList

/-!
# Candidate Selection and Five-Vertex Trial Search (`docs/crossing/crossing_extractor.tex`, Section
10)

This file formalizes steps 2–5 of one iteration of the contraction loop in Section 10 of
`docs/crossing/crossing_extractor.tex`:
* `isCrossed_of_clean_of_not_planar`: any clean, nonplanar instance `(K, S, D)` is crossed (by
  Fact T).
* `emitLowDegProg`: scans `0, …, N - 1` and emits into `a_low` all active vertices of degree at
  most `64`. By `sec101_proved`, when `|E(K)| ≤ 16 |S|`, at least five such vertices are emitted,
  and the first five form a `5`-element subset `U ⊆ S` of vertices of degree at most `64`.
* `buildCandProg`: for a chosen vertex `u ∈ S` of degree at most `64`, tests whether `u ∈ D` by
  scanning `a.cyc`, and emits into `a_cv` (of capacity `64`) the candidate neighbours `v` such that
  `IsTrialEdge K D u v` and `u ∈ D → 4 < D.length`.
* `tryCandLoopProg` and `tryFiveProg`: runs the trial program `P_tr` over all candidates for the
  first five low-degree vertices while the outcome register `r_state` is `0` (`NO`). By
  `sec102_proved` and Lemma 4 (`not_isCrossed_of_planar_of_no_distinctBridges`), at least one trial
  cannot return `0`, so `tryFiveProg` finishes with `r_state ∈ {1, 2}` (`YES` or `WITNESS`).
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### Part 1: Mathematical helper lemmas for Section 10 -/

/-- If `D` is crossed in `K` and `D.length ≠ 4`, then `4 < D.length` (since any crossing has four
distinct endpoints at strictly increasing indices `i < r < j < s < D.length`). -/
theorem four_lt_length_of_isCrossed_of_ne_four {V : Type*} {K : SimpleGraph V} {D : List V}
    (hcross : HP25.IsCrossed K D) (hne : D.length ≠ 4) : 4 < D.length := by
  obtain ⟨_, _, _, _, _, _, ⟨i, r, j, s, hir, hrj, hjs, _, _, _, hs⟩, _⟩ := hcross
  have hs_lt : s < D.length := (List.getElem?_eq_some_iff.mp hs).1
  omega

/-- Every vertex of a cycle `D` of `K` belongs to `S` when `K` is supported on `S`. -/
theorem mem_S_of_mem_cycle {V : Type*} {K : SimpleGraph V} {S : Set V} {D : List V}
    (hK : HP25.IsSupportedOn K S) (hD : HP25.IsCycleList K D) :
    ∀ v ∈ D, v ∈ S :=
  fun _ hv => mem_of_isCycleList_of_isSupportedOn hK hD hv

private lemma not_walk_to_outside_of_mem_U {V : Type*} {K : SimpleGraph V} {S U : Set V}
    {D : List V} {X : Finset (Option V)} (hK : HP25.IsSupportedOn K S)
    (hUD : U ⊆ S \ {v | v ∈ D})
    (hX : ∀ z ∈ S \ U, (∃ y ∈ U, K.Adj y z) → some z ∈ X)
    {a b : Option V} (p : (apex K D).Walk a b)
    (hp : ∀ w ∈ p.support, w ∈ apexVerts S \ (X : Set (Option V)))
    (ha : a ∈ some '' U) (hb : b ∉ some '' U) : False := by
  induction p with
  | nil => exact hb ha
  | @cons a w b haw p' ih =>
    obtain ⟨y, hyU, hy_eq⟩ := ha
    have ha_eq : a = some y := hy_eq.symm
    subst ha_eq
    by_cases hwU : w ∈ some '' U
    · exact ih (fun z hz => hp z (List.mem_cons_of_mem _ hz)) hwU hb
    · have hw_mem : w ∈ apexVerts S \ (X : Set (Option V)) :=
        hp w (List.mem_cons_of_mem _ (Walk.start_mem_support p'))
      cases w with
      | none => exact (hUD hyU).2 haw
      | some z =>
        have hzU : z ∉ U := fun hz => hwU ⟨z, hz, rfl⟩
        have hzS : z ∈ S := hK haw.symm
        exact hw_mem.2 (hX z ⟨hzS, hzU⟩ ⟨y, hyU, haw⟩)

/-- **Fact T for clean instances** (Fact T of Section 1, used as in Section 6; cleanliness is
defined in Section 2): if `(K, D)` is clean on a finite set
`S` and `K` is not planar on `S`, then `D` is crossed in `K`. -/
theorem isCrossed_of_clean_of_not_planar {V : Type*} [DecidableEq V] {K : SimpleGraph V}
    {S : Set V} {D : List V} (hSfin : S.Finite) (hK : HP25.IsSupportedOn K S)
    (hD : HP25.IsCycleList K D) (hclean : IsClean K S D)
    (hnp : ¬ Nonempty (HP25.PlaneEmbedding K S)) :
    HP25.IsCrossed K D := by
  by_contra hnc
  have hDS : ∀ v ∈ D, v ∈ S := mem_S_of_mem_cycle hK hD
  obtain ⟨U, hUD, ⟨u₀, hu₀U⟩, _, hNcard⟩ := fact_T_on hSfin hK hD hDS hnc hnp
  let NU : Set V := {z ∈ S \ U | ∃ y ∈ U, K.Adj y z}
  have hNU_fin : NU.Finite := hSfin.subset (fun _ hz => hz.1.1)
  let X : Finset (Option V) := hNU_fin.toFinset.image some
  have hXsub : (X : Set (Option V)) ⊆ apexVerts S \ {none} := by
    intro w hw
    simp only [X, Finset.coe_image, Set.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hzNU : z ∈ NU := hNU_fin.mem_toFinset.mp hz
    exact ⟨Or.inr ⟨z, hzNU.1.1, rfl⟩, by simp⟩
  have hXcard : X.card < 4 := by
    have h1 : X.card ≤ hNU_fin.toFinset.card := Finset.card_image_le
    have h2 : hNU_fin.toFinset.card = NU.ncard := (Set.ncard_eq_toFinset_card NU hNU_fin).symm
    dsimp only [NU] at h2
    omega
  have hu₀_mem : some u₀ ∈ apexVerts S \ (X : Set (Option V)) := by
    refine ⟨Or.inr ⟨u₀, (hUD hu₀U).1, rfl⟩, ?_⟩
    simp only [X, Finset.coe_image, Set.mem_image, Option.some.injEq, exists_eq_right]
    exact fun hu₀NU => (hNU_fin.mem_toFinset.mp hu₀NU).1.2 hu₀U
  have hnone_mem : (none : Option V) ∈ apexVerts S \ (X : Set (Option V)) :=
    ⟨Or.inl rfl, by simp [X]⟩
  obtain ⟨p, hp⟩ := (hclean X hXsub hXcard).2 (some u₀) hu₀_mem none hnone_mem
  refine not_walk_to_outside_of_mem_U hK hUD (fun z hzS hex => ?_) p hp
    ⟨u₀, hu₀U, rfl⟩ (by simp)
  exact Finset.mem_image_of_mem some (hNU_fin.mem_toFinset.mpr ⟨hzS, hex⟩)

/-- `ContractionsLong` is preserved under list append. -/
theorem ContractionsLong.append {N : ℕ} {recs₁ recs₂ : List (CrossRecord (Fin N))}
    (h₁ : ContractionsLong recs₁) (h₂ : ContractionsLong recs₂) :
    ContractionsLong (recs₁ ++ recs₂) := by
  intro r hr
  rcases List.mem_append.mp hr with hr₁ | hr₂
  · exact h₁ r hr₁
  · exact h₂ r hr₂

/-! ### Part 2: Finding five low-degree vertices (`emitLowDegProg`) -/

theorem eval_le {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .le A B).eval w s = some (if a ≤ b then 1 else 0) := by
  by_cases h : a ≤ b <;>
    simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hw, show 0 < 2 ^ w by omega]

/-- Initialize `r_i := 0` and run `forUp r_i hi body`. -/
def forRangeProg (r_i : Reg) (hi : Expr) (body : Cmd) : Cmd :=
  .seq (.assign r_i (.const 0)) (forUp r_i hi body)

theorem forRangeProg_exec {w : ℕ} (r_i : Reg) (hi : Expr) (body : Cmd) (N B : ℕ)
    (I : ℕ → State → Prop) (hN : N < 2 ^ w)
    (hstep : ∀ j ≤ N, ∀ st v, I j st → I j (st.setReg r_i v))
    (hhi : ∀ j < N, ∀ st, I j st → st.regs r_i = j → hi.eval w st = some N)
    (hhiN : ∀ st, I N st → st.regs r_i = N → hi.eval w st = some N)
    (hbody : ∀ j < N, ∀ st, I j st → st.regs r_i = j →
      ∃ st' t, Exec w body st st' t ∧ t ≤ B ∧ I (j + 1) st' ∧ st'.regs r_i = j)
    {s : State} (hI0 : I 0 s) :
    ∃ s' t, Exec w (forRangeProg r_i hi body) s s' t ∧
      t ≤ (N + 1) * (hi.cost + B + 6) ∧ I N s' ∧ s'.regs r_i = N := by
  have hw0 : 0 < 2 ^ w := Nat.two_pow_pos w
  have hI0' : I 0 (s.setReg r_i 0) := hstep 0 (Nat.zero_le N) s 0 hI0
  have hhi_all : ∀ j ≤ N, ∀ st, I j st → st.regs r_i = j → hi.eval w st = some N := by
    intro j hj st hI hri
    rcases Nat.lt_or_eq_of_le hj with hlt | rfl
    · exact hhi j hlt st hI hri
    · exact hhiN st hI hri
  by_cases hw1 : 1 < 2 ^ w
  · let J : ℕ → State → Prop := fun j st => st.regs r_i = j ∧ I j st
    have hex0 : Exec w (.assign r_i (.const 0)) s (s.setReg r_i 0) 2 :=
      .assign (eval_const hw0)
    obtain ⟨s', t, hex, ht, hJN⟩ := forUp_exec' J N B hw1 hN
      (fun j hj st ⟨hri, hI⟩ => ⟨hri, hhi_all j hj st hI hri⟩)
      (fun j hj st ⟨hri, hI⟩ => by
        obtain ⟨st', t', hex', ht', hI', hri'⟩ := hbody j hj st hI hri
        exact ⟨st', t', hex', ht', ⟨by simp, hstep (j + 1) hj st' (j + 1) hI'⟩, hri'⟩)
      (s.setReg r_i 0) ⟨by simp, hI0'⟩
    refine ⟨s', 2 + t, .seq hex0 hex, ?_, hJN.2, hJN.1⟩
    have hcost_pos : 1 ≤ hi.cost := Expr.cost_pos hi
    nlinarith
  · have hN0 : N = 0 := by
      have : 2 ^ w ≤ 1 := by omega
      omega
    subst hN0
    set s₀ := s.setReg r_i 0
    have hex0 : Exec w (.assign r_i (.const 0)) s s₀ 2 := .assign (eval_const hw0)
    have hhi0 : hi.eval w s₀ = some 0 := hhi_all 0 le_rfl s₀ hI0' (by simp [s₀])
    have hcond : (Expr.op .lt (.reg r_i) hi).eval w s₀ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₀, hhi0, hw0]
    refine ⟨s₀, _, .seq hex0 (.while_false hcond), ?_, hI0', by simp [s₀]⟩
    simp only [Expr.cost]; omega

theorem ncard_neighborSet_eq_degree {N : ℕ} (K : SimpleGraph (Fin N)) [DecidableRel K.Adj]
    (u : Fin N) : (K.neighborSet u).ncard = K.degree u := by
  simp

/-- Whether vertex index `x` is active in `(K, S)` and has degree at most `64`. -/
noncomputable def isLowDeg {N : ℕ} (K : SimpleGraph (Fin N)) [DecidableRel K.Adj]
    (S : Finset (Fin N)) (x : ℕ) : Bool :=
  if hx : x < N then decide (⟨x, hx⟩ ∈ S ∧ (K.neighborSet ⟨x, hx⟩).ncard ≤ 64) else false

/-- The list of low-degree active vertices below `m`. -/
noncomputable def lowDegUpTo {N : ℕ} (K : SimpleGraph (Fin N)) [DecidableRel K.Adj]
    (S : Finset (Fin N)) (m : ℕ) : List ℕ :=
  (List.range m).filter (isLowDeg K S)

theorem lowDegUpTo_zero {N : ℕ} (K : SimpleGraph (Fin N)) [DecidableRel K.Adj]
    (S : Finset (Fin N)) : lowDegUpTo K S 0 = [] := rfl

theorem lowDegUpTo_succ {N : ℕ} (K : SimpleGraph (Fin N)) [DecidableRel K.Adj]
    (S : Finset (Fin N)) (m : ℕ) :
    lowDegUpTo K S (m + 1) =
      lowDegUpTo K S m ++ (if isLowDeg K S m then [m] else []) := by
  simp [lowDegUpTo, List.range_succ, List.filter_append, List.filter_cons]

theorem length_lowDegUpTo_le {N : ℕ} (K : SimpleGraph (Fin N)) [DecidableRel K.Adj]
    (S : Finset (Fin N)) (m : ℕ) : (lowDegUpTo K S m).length ≤ m := by
  unfold lowDegUpTo
  exact (List.length_filter_le _ _).trans (by simp)

/-- Scan `x = 0, …, N - 1` and emit `x` into `(a_low, r_cnt)` whenever `a.alive[x] = 1` and
`a.en[x] - a.st[x] ≤ 64`. Uses registers `r_cnt`, `r_N`, `r_x`, `r_deg`. -/
def emitLowDegProg (a : InstArrs) (a_low : Arr) (r_cnt r_N r_x r_deg : Reg) : Cmd :=
  .seq (.assign r_N (.len a.alive))
    (.seq (.alloc a_low (.reg r_N))
      (.seq (.assign r_cnt (.const 0))
        (forRangeProg r_x (.reg r_N)
          (.ite (.read a.alive (.reg r_x))
            (.seq (.assign r_deg (.op .sub (.read a.en (.reg r_x)) (.read a.st (.reg r_x))))
              (.ite (.op .le (.reg r_deg) (.const 64))
                (emitProg a_low r_cnt (.reg r_x))
                .skip))
            .skip))))

/-- Execution of `emitLowDegProg`: builds `lowDegUpTo K S N` in `a_low`. -/
theorem emitLowDegProg_exec {w N : ℕ} (a : InstArrs) (a_low : Arr)
    (r_cnt r_N r_x r_deg : Reg)
    {K : SimpleGraph (Fin N)} [DecidableRel K.Adj] {S : Finset (Fin N)} {D : List (Fin N)}
    {s : State} (hinst : IsInstanceAt a K S D s)
    (ha_low : ∀ x ∈ a.list, x ≠ a_low)
    (hregs : [r_cnt, r_N, r_x, r_deg].Nodup)
    (hw : 4 * instSize N K + 65 < 2 ^ w) :
    ∃ s' t, Exec w (emitLowDegProg a a_low r_cnt r_N r_x r_deg) s s' t ∧
      t ≤ 30 * (N + 1) ∧
      IsBuf a_low r_cnt (lowDegUpTo K S N) (N - (lowDegUpTo K S N).length) s' ∧
      (∀ x, x ≠ a_low → s'.arrs x = s.arrs x) ∧
      (∀ r, r ∉ [r_cnt, r_N, r_x, r_deg] → s'.regs r = s.regs r) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true, ← ne_eq] at hregs
  obtain ⟨⟨hcnt_N, hcnt_x, hcnt_deg⟩, ⟨hN_x, hN_deg⟩, hx_deg⟩ := hregs
  obtain ⟨hsupp, halive, ⟨lists, hadj⟩, hent_len, hcyc⟩ := hinst
  have hN_le : N ≤ instSize N K := by unfold instSize; omega
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  have halive_len : (s.arrs a.alive).length = N := by simp [halive]
  have halive_ne : a.alive ≠ a_low := ha_low a.alive (by simp [InstArrs.list])
  have hst_ne : a.st ≠ a_low := ha_low a.st (by simp [InstArrs.list])
  have hen_ne : a.en ≠ a_low := ha_low a.en (by simp [InstArrs.list])
  have hent_ne : a.ent ≠ a_low := ha_low a.ent (by simp [InstArrs.list])
  set s₁ := s.setReg r_N N
  have hex₁ : Exec w (.assign r_N (.len a.alive)) s s₁ 2 :=
    .assign (by rw [eval_len rfl (by omega), halive_len])
  set s₂ := s₁.setArr a_low (List.replicate N 0)
  have hex₂ : Exec w (.alloc a_low (.reg r_N)) s₁ s₂ (1 + N) :=
    .alloc (eval_reg (by simp [s₁]) hNw)
  set s₃ := s₂.setReg r_cnt 0
  have hex₃ : Exec w (.assign r_cnt (.const 0)) s₂ s₃ 2 :=
    .assign (eval_const hw0)
  let I : ℕ → State → Prop := fun j st =>
    IsBuf a_low r_cnt (lowDegUpTo K S j) (N - (lowDegUpTo K S j).length) st ∧
    st.regs r_N = N ∧
    (∀ x, x ≠ a_low → st.arrs x = s.arrs x) ∧
    (∀ r, r ∉ [r_cnt, r_N, r_x, r_deg] → st.regs r = s.regs r)
  have hI0 : I 0 s₃ := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [s₃, s₂, lowDegUpTo_zero]
    · simp [s₃, lowDegUpTo_zero]
    · simp [s₃, s₂, s₁, hcnt_N.symm]
    · intro x hx
      simp [s₃, s₂, s₁, State.setArr_arrs_ne _ _ hx]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [s₃, s₂, s₁, hr.1, hr.2.1]
  obtain ⟨s₄, t₄, hex₄, ht₄, hIN, _⟩ := forRangeProg_exec r_x (.reg r_N)
    (.ite (.read a.alive (.reg r_x))
      (.seq (.assign r_deg (.op .sub (.read a.en (.reg r_x)) (.read a.st (.reg r_x))))
        (.ite (.op .le (.reg r_deg) (.const 64))
          (emitProg a_low r_cnt (.reg r_x))
          .skip))
      .skip)
    N 18 I hNw
    (fun j hj st v ⟨hbuf, hrN, harr, hreg⟩ => by
      refine ⟨⟨hbuf.1, by simp [State.setReg_regs_ne _ _ hcnt_x, hbuf.2]⟩,
        by simp [State.setReg_regs_ne _ _ hN_x, hrN], harr, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [State.setReg_regs_ne _ _ hr.2.2.1]
      exact hreg r (by simp [hr]))
    (fun j hj st ⟨_, hrN, _, _⟩ _ => eval_reg hrN hNw)
    (fun st ⟨_, hrN, _, _⟩ _ => eval_reg hrN hNw)
    (fun j hj st ⟨hbuf, hrN, harr, hreg⟩ hrx => by
      let u : Fin N := ⟨j, hj⟩
      have halive_st : st.arrs a.alive = s.arrs a.alive := harr a.alive halive_ne
      have hst_st : st.arrs a.st = s.arrs a.st := harr a.st hst_ne
      have hen_st : st.arrs a.en = s.arrs a.en := harr a.en hen_ne
      have hent_st : st.arrs a.ent = s.arrs a.ent := harr a.ent hent_ne
      have halive_j : (st.arrs a.alive)[j]'(by rw [halive_st, halive]; simp [hj]) =
          if u ∈ S then 1 else 0 := by
        simp [halive_st, halive, u]
      have hread_alive : (Expr.read a.alive (.reg r_x)).eval w st =
          some (if u ∈ S then 1 else 0) := by
        rw [← halive_j]
        exact eval_read (w := w) (eval_reg (w := w) hrx (by omega))
          (by rw [halive_st, halive]; simp [hj]) (by rw [halive_j]; split_ifs <;> omega)
      by_cases huS : u ∈ S
      · simp only [huS, ↓reduceIte] at hread_alive
        obtain ⟨st_u, en_u, hlist_u⟩ := hadj.1.2.2 u
        obtain ⟨hu_st, hu_en, hen_le, hlen_u, hst_u, hen_u, hle_u, _⟩ := hlist_u
        have hlen_eq_deg : (lists u).length = (K.neighborSet u).ncard :=
          (ncard_neighborSet_eq_length hadj.2 u).symm
        have h2m_w : 2 * K.edgeSet.ncard < 2 ^ w := by unfold instSize at hw; omega
        have hen_w : en_u < 2 ^ w := by rw [hent_len] at hen_le; omega
        have hst_w : st_u < 2 ^ w := Nat.lt_of_le_of_lt hle_u hen_w
        have hen_j : (st.arrs a.en)[j]'(by rw [hen_st, hadj.1.2.1]; exact hj) = en_u := by
          simp only [hen_st]
          exact hen_u
        have hread_en : (Expr.read a.en (.reg r_x)).eval w st = some en_u := by
          rw [← hen_j]
          exact eval_read (w := w) (eval_reg (w := w) hrx (by omega))
            (by rw [hen_st, hadj.1.2.1]; exact hj) (by rw [hen_j]; exact hen_w)
        have hst_j : (st.arrs a.st)[j]'(by rw [hst_st, hadj.1.1]; exact hj) = st_u := by
          simp only [hst_st]
          exact hst_u
        have hread_st : (Expr.read a.st (.reg r_x)).eval w st = some st_u := by
          rw [← hst_j]
          exact eval_read (w := w) (eval_reg (w := w) hrx (by omega))
            (by rw [hst_st, hadj.1.1]; exact hj) (by rw [hst_j]; exact hst_w)
        have hsub_eval : (Expr.op .sub (.read a.en (.reg r_x)) (.read a.st (.reg r_x))).eval w st =
            some (en_u - st_u) :=
          eval_sub hread_en hread_st
        set st₁ := st.setReg r_deg (en_u - st_u)
        have hex_deg : Exec w (.assign r_deg (.op .sub (.read a.en (.reg r_x)) (.read a.st (.reg r_x))))
            st st₁ 6 := .assign hsub_eval
        have hdeg_eq : en_u - st_u = (K.neighborSet u).ncard := by omega
        have hle_eval : (Expr.op .le (.reg r_deg) (.const 64)).eval w st₁ =
            some (if (K.neighborSet u).ncard ≤ 64 then 1 else 0) := by
          rw [← hdeg_eq]
          exact eval_le (eval_reg (w := w) (by simp [st₁]) (by omega))
            (eval_const (w := w) (by omega)) hw1
        have hlen_low_j : (lowDegUpTo K S j).length < N :=
          Nat.lt_of_le_of_lt (length_lowDegUpTo_le K S j) hj
        by_cases hdeg64 : (K.neighborSet u).ncard ≤ 64
        · simp only [hdeg64, ↓reduceIte] at hle_eval
          have hisLow : isLowDeg K S j = true := by
            simp only [isLowDeg, hj, ↓reduceDIte, decide_eq_true_eq]
            exact ⟨huS, hdeg64⟩
          have hbuf₁ : IsBuf a_low r_cnt (lowDegUpTo K S j)
              ((N - (lowDegUpTo K S (j + 1)).length) + 1) st₁ := by
            rw [lowDegUpTo_succ, hisLow]
            simp only [↓reduceIte, List.length_append, List.length_singleton]
            refine ⟨?_, by simp [st₁, State.setReg_regs_ne _ _ hcnt_deg, hbuf.2]⟩
            rw [State.setReg_arrs, show N - ((lowDegUpTo K S j).length + 1) + 1 =
              N - (lowDegUpTo K S j).length by omega]
            exact hbuf.1
          have hrx₁ : st₁.regs r_x = j := (State.setReg_regs_ne _ _ hx_deg).trans hrx
          obtain ⟨st₂, hex_em, hbuf₂, harr₂, hreg₂⟩ :=
            emitReg_exec (w := w) a_low r_cnt r_x hbuf₁ hrx₁ (by omega) (by omega)
          have hbuf₂' : IsBuf a_low r_cnt (lowDegUpTo K S (j + 1))
              (N - (lowDegUpTo K S (j + 1)).length) st₂ := by
            simpa [lowDegUpTo_succ, hisLow] using hbuf₂
          refine ⟨st₂, 2 + (6 + (3 + 7)),
            .ite_true hread_alive (by decide) (.seq hex_deg (.ite_true hle_eval (by decide) hex_em)),
            by omega, ⟨hbuf₂', ?_, ?_, ?_⟩, ?_⟩
          · rw [hreg₂ r_N hcnt_N.symm]
            simp [st₁, State.setReg_regs_ne _ _ hN_deg, hrN]
          · intro x hx
            rw [harr₂ x hx]
            exact harr x hx
          · intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            rw [hreg₂ r hr.1]
            simp [st₁, State.setReg_regs_ne _ _ hr.2.2.2, hreg r (by simp [hr])]
          · rw [hreg₂ r_x hcnt_x.symm]
            exact hrx₁
        · simp only [hdeg64, ↓reduceIte] at hle_eval
          have hisLow : isLowDeg K S j = false := by
            simp only [isLowDeg, hj, ↓reduceDIte, decide_eq_false_iff_not, not_and]
            intro _; exact hdeg64
          refine ⟨st₁, 2 + (6 + (3 + 1)),
            .ite_true hread_alive (by decide) (.seq hex_deg (.ite_false hle_eval (.skip _))),
            by omega, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
          · simp only [lowDegUpTo_succ, hisLow, Bool.false_eq_true, ↓reduceIte, List.append_nil]
            exact ⟨hbuf.1, by simp [st₁, State.setReg_regs_ne _ _ hcnt_deg, hbuf.2]⟩
          · simp [st₁, State.setReg_regs_ne _ _ hN_deg, hrN]
          · exact harr
          · intro r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            simp [st₁, State.setReg_regs_ne _ _ hr.2.2.2, hreg r (by simp [hr])]
          · exact (State.setReg_regs_ne _ _ hx_deg).trans hrx
      · simp only [huS, ↓reduceIte] at hread_alive
        have hisLow : isLowDeg K S j = false := by
          simp only [isLowDeg, hj, ↓reduceDIte, decide_eq_false_iff_not, not_and]
          intro h; exact absurd h huS
        refine ⟨st, 2 + 1, .ite_false hread_alive (.skip _), by omega,
          ⟨?_, hrN, harr, hreg⟩, hrx⟩
        simp only [lowDegUpTo_succ, hisLow, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        exact hbuf)
    hI0
  obtain ⟨hbufN, _, harrN, hregN⟩ := hIN
  refine ⟨s₄, 2 + ((1 + N) + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp only [Expr.cost] at ht₄; omega, hbufN, harrN, hregN⟩

/-- Every element of `lowDegUpTo K S N` is `< N`, belongs to `S`, and has degree `≤ 64`. -/
theorem mem_lowDegUpTo_iff {N : ℕ} {K : SimpleGraph (Fin N)} [DecidableRel K.Adj]
    {S : Finset (Fin N)} {x : ℕ} :
    x ∈ lowDegUpTo K S N ↔ ∃ hx : x < N, ⟨x, hx⟩ ∈ S ∧ (K.neighborSet ⟨x, hx⟩).ncard ≤ 64 := by
  simp only [lowDegUpTo, List.mem_filter, List.mem_range, isLowDeg]
  constructor
  · rintro ⟨hx, h⟩
    simp only [hx, ↓reduceDIte, decide_eq_true_eq] at h
    exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    simp only [hx, ↓reduceDIte, decide_eq_true_eq]
    exact h

theorem nodup_lowDegUpTo {N : ℕ} (K : SimpleGraph (Fin N)) [DecidableRel K.Adj]
    (S : Finset (Fin N)) (m : ℕ) : (lowDegUpTo K S m).Nodup :=
  List.nodup_range.filter _

/-- When `(K, S)` is nonplanar, supported on `S`, and has `|E(K)| ≤ 16 |S|`, `lowDegUpTo K S N` has
length at least `5`, and its first `5` entries give a `5`-element subset `U ⊆ S` of vertices of
degree at most `64`. -/
theorem five_le_length_lowDegUpTo {N : ℕ} {K : SimpleGraph (Fin N)} [DecidableRel K.Adj]
    {S : Finset (Fin N)} (hsupp : HP25.IsSupportedOn K (S : Set (Fin N)))
    (hnp : IsEmpty (HP25.PlaneEmbedding K (S : Set (Fin N))))
    (hedge : K.edgeSet.ncard ≤ 16 * S.card) :
    5 ≤ (lowDegUpTo K S N).length ∧
    ∃ U : Finset (Fin N), U.card = 5 ∧ (U : Set (Fin N)) ⊆ (S : Set (Fin N)) ∧
      (∀ u ∈ U, (K.neighborSet u).ncard ≤ 64) ∧
      ∀ u ∈ U, ∃ j < 5, (lowDegUpTo K S N)[j]? = some u.val := by
  have hSfin : (S : Set (Fin N)).Finite := Finset.finite_toSet S
  have hnp' : ¬ Nonempty (HP25.PlaneEmbedding K (S : Set (Fin N))) :=
    fun ⟨φ⟩ => hnp.false φ
  have hedge' : K.edgeSet.ncard ≤ 16 * (S : Set (Fin N)).ncard := by
    rwa [Set.ncard_coe_finset]
  obtain ⟨U₀, hU₀_card, hU₀_sub, hU₀_deg⟩ :=
    sec101_proved K (S : Set (Fin N)) hSfin hsupp hnp' hedge'
  have hU₀_sub_low : U₀.map Fin.valEmbedding ⊆ (lowDegUpTo K S N).toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨u, huU₀, rfl⟩ := hx
    rw [List.mem_toFinset, mem_lowDegUpTo_iff]
    exact ⟨u.2, hU₀_sub huU₀, hU₀_deg u huU₀⟩
  have hlen5 : 5 ≤ (lowDegUpTo K S N).length := by
    rw [← List.toFinset_card_of_nodup (nodup_lowDegUpTo K S N)]
    have h1 := Finset.card_le_card hU₀_sub_low
    rw [Finset.card_map, hU₀_card] at h1
    exact h1
  set L5 := (lowDegUpTo K S N).take 5
  have hL5_len : L5.length = 5 := List.length_take_of_le hlen5
  have hL5_nd : L5.Nodup := (nodup_lowDegUpTo K S N).take
  have hL5_mem : ∀ x ∈ L5, x ∈ lowDegUpTo K S N := fun x hx => List.mem_of_mem_take hx
  let L5_fin : List (Fin N) := L5.pmap (fun x (hx : x < N) => (⟨x, hx⟩ : Fin N))
    (fun x hx => (mem_lowDegUpTo_iff.mp (hL5_mem x hx)).1)
  have hmap_val : L5_fin.map Fin.val = L5 := by
    dsimp [L5_fin]
    rw [List.map_pmap]
    exact List.pmap_eq_self.mpr (fun _ _ => rfl)
  have hL5_fin_nd : L5_fin.Nodup := List.Nodup.of_map Fin.val (hmap_val ▸ hL5_nd)
  have hL5_fin_len : L5_fin.length = 5 := by simp [L5_fin, hL5_len]
  refine ⟨hlen5, L5_fin.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hL5_fin_nd, hL5_fin_len]
  · intro u hu
    rw [Finset.mem_coe, List.mem_toFinset] at hu
    have hu_val : u.val ∈ L5 := hmap_val ▸ List.mem_map_of_mem (f := Fin.val) hu
    obtain ⟨_, huS, _⟩ := mem_lowDegUpTo_iff.mp (hL5_mem u.val hu_val)
    exact huS
  · intro u hu
    rw [List.mem_toFinset] at hu
    have hu_val : u.val ∈ L5 := hmap_val ▸ List.mem_map_of_mem (f := Fin.val) hu
    obtain ⟨_, _, hudeg⟩ := mem_lowDegUpTo_iff.mp (hL5_mem u.val hu_val)
    exact hudeg
  · intro u hu
    rw [List.mem_toFinset] at hu
    have hu_val : u.val ∈ L5 := hmap_val ▸ List.mem_map_of_mem (f := Fin.val) hu
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem hu_val
    rw [hL5_len] at hj
    refine ⟨j, hj, ?_⟩
    have hj_low : j < (lowDegUpTo K S N).length := by omega
    rw [List.getElem?_eq_getElem hj_low]
    congr 1
    simpa [L5, List.getElem_take] using hget

/-! ### Part 3: Candidate edge generation for one vertex (`buildCandProg`) -/

/-- Next index on a cycle of length `len` after `pos`. -/
def nextCycIdx (len pos : ℕ) : ℕ :=
  if pos + 1 = len then 0 else pos + 1

/-- Previous index on a cycle of length `len` before `pos`. -/
def prevCycIdx (len pos : ℕ) : ℕ :=
  if pos = 0 then len - 1 else pos - 1

theorem nextCycIdx_lt {len pos : ℕ} (hlen : 3 ≤ len) (hpos : pos < len) :
    nextCycIdx len pos < len := by
  unfold nextCycIdx
  split_ifs <;> omega

theorem prevCycIdx_lt {len pos : ℕ} (_hlen : 3 ≤ len) (hpos : pos < len) :
    prevCycIdx len pos < len := by
  unfold prevCycIdx
  split_ifs <;> omega

theorem nextCycIdx_eq_mod {len pos : ℕ} (_hlen : 3 ≤ len) (hpos : pos < len) :
    nextCycIdx len pos = (pos + 1) % len := by
  unfold nextCycIdx
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact (Nat.mod_eq_of_lt (by omega)).symm

theorem prevCycIdx_succ_mod {len pos : ℕ} (hlen : 3 ≤ len) (hpos : pos < len) :
    (prevCycIdx len pos + 1) % len = pos := by
  unfold prevCycIdx
  split_ifs with h
  · subst h
    rw [show len - 1 + 1 = len by omega, Nat.mod_self]
  · rw [show pos - 1 + 1 = pos by omega]
    exact Nat.mod_eq_of_lt hpos

/-- For `u ∈ D` on a cycle `D` of `K`, the vertices at `nextCycIdx D.length (D.idxOf u)` and
`prevCycIdx D.length (D.idxOf u)` are precisely the `v` such that `IsTrialEdge K D u v`. -/
theorem isTrialEdge_on_cycle_iff {V : Type*} [DecidableEq V] {K : SimpleGraph V} {D : List V}
    {u v : V} (hD : HP25.IsCycleList K D) (huD : u ∈ D) :
    have hpos : D.idxOf u < D.length := List.idxOf_lt_length_of_mem huD
    IsTrialEdge K D u v ↔
      v = D[nextCycIdx D.length (D.idxOf u)]'(nextCycIdx_lt hD.1 hpos) ∨
      v = D[prevCycIdx D.length (D.idxOf u)]'(prevCycIdx_lt hD.1 hpos) := by
  intro hpos
  have hlen3 : 3 ≤ D.length := hD.1
  have hnd : D.Nodup := hD.2.1
  have hpos_eq : D[D.idxOf u]'hpos = u := List.getElem_idxOf hpos
  have hlen_rot : (D.rotate 1).length = D.length := List.length_rotate D 1
  have hlen_zip : (D.zip (D.rotate 1)).length = D.length := by simp
  constructor
  · rintro ⟨_, hu_not_D | ⟨p, hp, hp_eq⟩⟩
    · exact absurd huD hu_not_D
    · obtain ⟨k, hk_zip, hk_eq⟩ := List.getElem_of_mem hp
      have hk : k < D.length := by simpa [hlen_zip] using hk_zip
      simp only [List.getElem_zip] at hk_eq
      have hrot_k : (D.rotate 1)[k]'(by omega) = D[(k + 1) % D.length]'(Nat.mod_lt _ (by omega)) := by
        simp
      rcases hp_eq with rfl | rfl
      · injection hk_eq with hk1 hk2
        have hk_pos : k = D.idxOf u :=
          (List.Nodup.getElem_inj_iff hnd).mp (hk1.trans hpos_eq.symm)
        subst hk_pos
        left
        rw [← hk2, hrot_k]
        congr 1
        exact (nextCycIdx_eq_mod hlen3 hpos).symm
      · injection hk_eq with hk1 hk2
        rw [hrot_k] at hk2
        have hmod_pos : (k + 1) % D.length = D.idxOf u :=
          (List.Nodup.getElem_inj_iff hnd).mp (hk2.trans hpos_eq.symm)
        have hk_prev : k = prevCycIdx D.length (D.idxOf u) := by
          unfold prevCycIdx
          split_ifs with h0
          · rw [h0] at hmod_pos
            by_cases hk1_len : k + 1 = D.length
            · omega
            · have : (k + 1) % D.length = k + 1 := Nat.mod_eq_of_lt (by omega)
              omega
          · have hk1_lt : k + 1 < D.length := by
              by_contra hge
              have hk1_eq : k + 1 = D.length := by omega
              rw [hk1_eq, Nat.mod_self] at hmod_pos
              exact h0 hmod_pos.symm
            rw [Nat.mod_eq_of_lt hk1_lt] at hmod_pos
            omega
        right
        subst hk_prev
        exact hk1.symm
  · rintro (rfl | rfl)
    · have hrot_pos : (D.rotate 1)[D.idxOf u]'(by omega) =
          D[nextCycIdx D.length (D.idxOf u)]'(nextCycIdx_lt hlen3 hpos) := by
        have h1 := List.getElem_rotate D 1 (D.idxOf u) (by omega)
        simp only [← nextCycIdx_eq_mod hlen3 hpos] at h1
        exact h1
      have hp_mem : (u, D[nextCycIdx D.length (D.idxOf u)]'(nextCycIdx_lt hlen3 hpos)) ∈
          D.zip (D.rotate 1) := by
        rw [List.mem_iff_getElem]
        refine ⟨D.idxOf u, by simp [hpos], ?_⟩
        simp [hpos_eq, hrot_pos]
      exact ⟨hD.2.2 _ hp_mem, Or.inr ⟨_, hp_mem, Or.inl rfl⟩⟩
    · set k := prevCycIdx D.length (D.idxOf u)
      have hk : k < D.length := prevCycIdx_lt hlen3 hpos
      have hrot_k : (D.rotate 1)[k]'(by omega) = u := by
        have h1 := List.getElem_rotate D 1 k (by omega)
        simp only [k, prevCycIdx_succ_mod hlen3 hpos, hpos_eq] at h1
        exact h1
      have hp_mem : (D[k]'hk, u) ∈ D.zip (D.rotate 1) := by
        rw [List.mem_iff_getElem]
        refine ⟨k, by simp [hk], ?_⟩
        simp [hrot_k]
      exact ⟨(hD.2.2 _ hp_mem).symm, Or.inr ⟨_, hp_mem, Or.inr rfl⟩⟩

/-- The list of candidate neighbour values emitted for vertex `u`. -/
def candVals {N : ℕ} (D : List (Fin N)) (lists : Fin N → List ℕ) (u : Fin N) : List ℕ :=
  if hu : u ∈ D then
    if hlen : 4 < D.length then
      have hpos : D.idxOf u < D.length := List.idxOf_lt_length_of_mem hu
      have h3 : 3 ≤ D.length := by omega
      [(D[nextCycIdx D.length (D.idxOf u)]'(nextCycIdx_lt h3 hpos)).val,
       (D[prevCycIdx D.length (D.idxOf u)]'(prevCycIdx_lt h3 hpos)).val]
    else []
  else listOf lists u.val

theorem length_candVals_le {N : ℕ} {K : SimpleGraph (Fin N)} {D : List (Fin N)}
    {lists : Fin N → List ℕ} {u : Fin N} (hadj : IsAdjListFamily K lists)
    (hdeg : (K.neighborSet u).ncard ≤ 64) :
    (candVals D lists u).length ≤ 64 := by
  unfold candVals
  split_ifs with hu hlen
  · simp
  · simp
  · rw [listOf_fin, ← ncard_neighborSet_eq_length hadj u]
    exact hdeg

theorem mem_candVals_iff {N : ℕ} {K : SimpleGraph (Fin N)} {D : List (Fin N)}
    {lists : Fin N → List ℕ} {u : Fin N} (hD : HP25.IsCycleList K D)
    (hadj : IsAdjListFamily K lists) (x : ℕ) :
    x ∈ candVals D lists u ↔
      ∃ hx : x < N, IsTrialEdge K D u ⟨x, hx⟩ ∧ (u ∈ D → 4 < D.length) := by
  unfold candVals
  by_cases hu : u ∈ D
  · simp only [hu, ↓reduceDIte, forall_true_left]
    by_cases hlen : 4 < D.length
    · simp only [hlen, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false, and_true]
      have hpos : D.idxOf u < D.length := List.idxOf_lt_length_of_mem hu
      have h3 : 3 ≤ D.length := hD.1
      set v₁ := D[nextCycIdx D.length (D.idxOf u)]'(nextCycIdx_lt h3 hpos)
      set v₂ := D[prevCycIdx D.length (D.idxOf u)]'(prevCycIdx_lt h3 hpos)
      constructor
      · rintro (rfl | rfl)
        · exact ⟨v₁.2, (isTrialEdge_on_cycle_iff hD hu).mpr (Or.inl rfl)⟩
        · exact ⟨v₂.2, (isTrialEdge_on_cycle_iff hD hu).mpr (Or.inr rfl)⟩
      · rintro ⟨hx, htrial⟩
        rcases (isTrialEdge_on_cycle_iff hD hu).mp htrial with h1 | h2
        · left; exact congrArg Fin.val h1
        · right; exact congrArg Fin.val h2
    · simp [hlen]
  · simp only [hu, ↓reduceDIte, IsEmpty.forall_iff, and_true, listOf_fin]
    constructor
    · intro hx_mem
      have hx : x < N := (hadj u).1 x hx_mem
      exact ⟨hx, ⟨((hadj u).2.2.2 ⟨x, hx⟩).mp hx_mem, Or.inl hu⟩⟩
    · rintro ⟨hx, huv, _⟩
      exact ((hadj u).2.2.2 ⟨x, hx⟩).mpr huv

/-- Body of the cycle scan in `buildCandProg`: if `r_y = r_u`, set `r_onD := 1` and `r_pos := r_k`. -/
def findCyclePosBody (r_u r_onD r_pos r_k r_y : Reg) : Cmd :=
  .ite (.op .eq (.reg r_y) (.reg r_u))
    (.seq (.assign r_onD (.const 1)) (.assign r_pos (.reg r_k)))
    .skip

/-- Emit the two cycle neighbours of `u` when `4 < r_clen`. -/
def emitCycleCandsProg (a : InstArrs) (a_cv : Arr)
    (r_ncand r_pos r_clen r_k r_y : Reg) : Cmd :=
  .ite (.op .lt (.const 4) (.reg r_clen))
    (.seq (.assign r_k (.op .add (.reg r_pos) (.const 1)))
      (.seq (.ite (.op .eq (.reg r_k) (.reg r_clen)) (.assign r_k (.const 0)) .skip)
        (.seq (.assign r_y (.read a.cyc (.reg r_k)))
          (.seq (emitProg a_cv r_ncand (.reg r_y))
            (.seq (.ite (.op .eq (.reg r_pos) (.const 0))
                (.assign r_k (.op .sub (.reg r_clen) (.const 1)))
                (.assign r_k (.op .sub (.reg r_pos) (.const 1))))
              (.seq (.assign r_y (.read a.cyc (.reg r_k)))
                (emitProg a_cv r_ncand (.reg r_y))))))))
    .skip

/-- Build `candVals D lists u` in `(a_cv, r_ncand)` for the vertex `u` in `r_u`. -/
def buildCandProg (a : InstArrs) (a_cv : Arr)
    (r_u r_ncand r_onD r_pos r_clen r_k r_hi r_y : Reg) : Cmd :=
  .seq (.alloc a_cv (.const 64))
    (.seq (.assign r_ncand (.const 0))
      (.seq (.assign r_onD (.const 0))
        (.seq (.assign r_pos (.const 0))
          (.seq (forArrProg a.cyc r_k r_hi r_y (findCyclePosBody r_u r_onD r_pos r_k r_y))
            (.ite (.reg r_onD)
              (.seq (.assign r_clen (.len a.cyc))
                (emitCycleCandsProg a a_cv r_ncand r_pos r_clen r_k r_y))
              (forList a.st a.en a.ent r_u r_k r_hi r_y
                (emitProg a_cv r_ncand (.reg r_y))))))))

theorem idxOf_map_val {N : ℕ} (D : List (Fin N)) (u : Fin N) :
    (D.map Fin.val).idxOf u.val = D.idxOf u := by
  induction D with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxu : x = u
    · subst hxu
      simp
    · have hval : x.val ≠ u.val := fun h => hxu (Fin.ext h)
      simp [List.idxOf_cons_ne _ hxu, List.idxOf_cons_ne _ hval, ih]

/-- Execution of `buildCandProg`: populates `(a_cv, r_ncand)` with `candVals D lists u`. -/
theorem buildCandProg_exec {w N : ℕ} (a : InstArrs) (a_cv : Arr)
    (r_u r_ncand r_onD r_pos r_clen r_k r_hi r_y : Reg)
    {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {lists : Fin N → List ℕ} {u : Fin N} {s : State}
    (hinst : IsInstanceAt a K S D s)
    (hadj : IsAdjList K a.st a.en a.ent lists s)
    (hD : HP25.IsCycleList K D)
    (hu : s.regs r_u = u.val)
    (hdeg : (K.neighborSet u).ncard ≤ 64)
    (ha_cv : ∀ x ∈ a.list, x ≠ a_cv)
    (hregs : [r_u, r_ncand, r_onD, r_pos, r_clen, r_k, r_hi, r_y].Nodup)
    (hw : 4 * instSize N K + 70 < 2 ^ w) :
    ∃ s' t, Exec w (buildCandProg a a_cv r_u r_ncand r_onD r_pos r_clen r_k r_hi r_y) s s' t ∧
      t ≤ 25 * (N + 1) + 1200 ∧
      IsBuf a_cv r_ncand (candVals D lists u) (64 - (candVals D lists u).length) s' ∧
      (∀ x, x ≠ a_cv → s'.arrs x = s.arrs x) ∧
      (∀ r, r ∉ [r_ncand, r_onD, r_pos, r_clen, r_k, r_hi, r_y] → s'.regs r = s.regs r) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    ← ne_eq, not_false_eq_true, List.nodup_nil, and_true] at hregs
  obtain ⟨⟨hu_nc, hu_on, hu_pos, hu_cl, hu_k, hu_hi, hu_y⟩,
    ⟨hnc_on, hnc_pos, hnc_cl, hnc_k, hnc_hi, hnc_y⟩,
    ⟨hon_pos, hon_cl, hon_k, hon_hi, hon_y⟩,
    ⟨hpos_cl, hpos_k, hpos_hi, hpos_y⟩,
    ⟨hcl_k, hcl_hi, hcl_y⟩,
    ⟨hk_hi, hk_y⟩, hhi_y⟩ := hregs
  obtain ⟨hsupp, halive, _, hent_len, hcyc⟩ := hinst
  have hN_le : N ≤ instSize N K := by unfold instSize; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  have huw : u.val < 2 ^ w := by omega
  have hDN : D.length ≤ N := by
    have hsub : D.toFinset ⊆ Finset.univ := Finset.subset_univ _
    have hcard := Finset.card_le_card hsub
    rwa [List.toFinset_card_of_nodup hD.2.1, Finset.card_fin] at hcard
  have hst_ne : a.st ≠ a_cv := ha_cv a.st (by simp [InstArrs.list])
  have hen_ne : a.en ≠ a_cv := ha_cv a.en (by simp [InstArrs.list])
  have hent_ne : a.ent ≠ a_cv := ha_cv a.ent (by simp [InstArrs.list])
  have hcyc_ne : a.cyc ≠ a_cv := ha_cv a.cyc (by simp [InstArrs.list])
  -- Phase 1: alloc a_cv 64, r_ncand := 0, r_onD := 0, r_pos := 0
  set s₁ := (((s.setArr a_cv (List.replicate 64 0)).setReg r_ncand 0).setReg r_onD 0).setReg r_pos 0
  have hex₁ : ∀ {s' : State} {t : ℕ},
      Exec w (.seq (forArrProg a.cyc r_k r_hi r_y (findCyclePosBody r_u r_onD r_pos r_k r_y))
        (.ite (.reg r_onD)
          (.seq (.assign r_clen (.len a.cyc))
            (emitCycleCandsProg a a_cv r_ncand r_pos r_clen r_k r_y))
          (forList a.st a.en a.ent r_u r_k r_hi r_y
            (emitProg a_cv r_ncand (.reg r_y))))) s₁ s' t →
      Exec w (buildCandProg a a_cv r_u r_ncand r_onD r_pos r_clen r_k r_hi r_y) s s'
        (65 + (2 + (2 + (2 + t)))) := fun h =>
    .seq (.alloc (eval_const (by omega)))
      (.seq (.assign (eval_const (by omega)))
        (.seq (.assign (eval_const (by omega)))
          (.seq (.assign (eval_const (by omega))) h)))
  -- Phase 2: scan a.cyc
  set l := D.map Fin.val
  have hl_s₁ : s₁.arrs a.cyc = l := by
    simp only [s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hcyc_ne, hcyc]
  have hl_nd : l.Nodup := hD.2.1.map Fin.val_injective
  have hl_w : ∀ y ∈ l, y < 2 ^ w := by
    intro y hy
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
    omega
  let Q₁ : ℕ → State → Prop := fun j st =>
    st.arrs = s₁.arrs ∧
    st.regs r_onD = (if u.val ∈ l.take j then 1 else 0) ∧
    (u.val ∈ l.take j → st.regs r_pos = l.idxOf u.val) ∧
    (∀ r, r ∉ [r_onD, r_pos, r_k, r_hi, r_y] → st.regs r = s₁.regs r)
  have hQ₁0 : Q₁ 0 s₁ := by
    refine ⟨rfl, ?_, by simp, fun _ _ => rfl⟩
    simp [s₁, hon_pos]
  obtain ⟨s₂, t₂, hex₂, ht₂, hQ₁_end, hbuf₂⟩ :=
    forArrEmit_exec a.cyc r_k r_hi r_y a_cv r_ncand
      (findCyclePosBody r_u r_onD r_pos r_k r_y) (fun _ => []) Q₁ 8
      (pre := []) (k := 64)
      hk_hi hnc_k.symm hnc_hi.symm hnc_y.symm hk_y.symm hhi_y.symm
      hw1 (by rw [hl_s₁]; simp [l]; omega) (by rw [hl_s₁]; exact hl_w) hQ₁0
      ⟨by simp [s₁], by simp [s₁, hnc_on, hnc_pos]⟩ (by simp)
      (fun j st st' ⟨harr, hon, hpos, hreg⟩ ha hr => by
        refine ⟨ha.trans harr, ?_, ?_, fun r hr' => ?_⟩
        · rw [hr r_onD hon_k hon_hi hon_y, hon]
        · intro hmem
          rw [hr r_pos hpos_k hpos_hi hpos_y, hpos hmem]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
          rw [hr r hr'.2.2.1 hr'.2.2.2.1 hr'.2.2.2.2]
          exact hreg r (by simp [hr']))
      (fun j st ⟨harr, _, _, _⟩ => by rw [harr])
      (fun j hj st pre' k' ⟨harr, hon, hpos, hreg⟩ hrk hrh hry hb' _ _ => by
        have hj' : j < l.length := by rwa [hl_s₁] at hj
        have hry' : st.regs r_y = l[j]'hj' := by
          simp only [hl_s₁] at hry
          exact hry
        have hru : st.regs r_u = u.val := by
          rw [hreg r_u (by simp [hu_on, hu_pos, hu_k, hu_hi, hu_y])]
          simp [s₁, hu_nc, hu_on, hu_pos, hu]
        have hy_w : l[j]'hj' < 2 ^ w := hl_w (l[j]'hj') (List.getElem_mem hj')
        by_cases hyu : l[j]'hj' = u.val
        · set st' := (st.setReg r_onD 1).setReg r_pos j
          have hex_body : Exec w (findCyclePosBody r_u r_onD r_pos r_k r_y) st st' (3 + (2 + 2)) :=
            exec_ite_eq_true hry' (hru.trans hyu.symm) hy_w hw1
              (.seq (.assign (eval_const hw1))
                (.assign (eval_reg (w := w) (by simp [hon_k.symm, hrk]) (by simp [l] at hj'; omega))))
          have hmem_succ : u.val ∈ l.take (j + 1) := by
            rw [List.take_succ_eq_append_getElem hj']
            simp [hyu]
          have hidx_eq : l.idxOf u.val = j := by
            rw [← hyu]
            exact List.Nodup.idxOf_getElem hl_nd j hj'
          refine ⟨st', 7, hex_body, by omega, ⟨harr, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
          · simp [st', hon_pos, hmem_succ]
          · intro _
            simp [st', hidx_eq]
          · intro r hr'
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
            simp [st', hr'.1, hr'.2.1, hreg r (by simp [hr'])]
          · simp [st', hon_k.symm, hpos_k.symm, hrk]
          · simp [st', hon_hi.symm, hpos_hi.symm, hrh]
          · simp only [List.append_nil, List.length_nil, Nat.sub_zero]
            exact ⟨hb'.1, by simp [st', hnc_on, hnc_pos, hb'.2]⟩
        · have hex_body : Exec w (findCyclePosBody r_u r_onD r_pos r_k r_y) st st (3 + 1) :=
            exec_ite_eq_false hry' hru hyu hy_w huw hw1 (.skip _)
          have hmem_iff : u.val ∈ l.take (j + 1) ↔ u.val ∈ l.take j := by
            rw [List.take_succ_eq_append_getElem hj']
            simp only [List.mem_append, List.mem_singleton]
            exact ⟨fun h => h.resolve_right (fun e => hyu e.symm), Or.inl⟩
          refine ⟨st, 4, hex_body, by omega, ⟨harr, ?_, ?_, hreg⟩, hrk, hrh, by simpa using hb'⟩
          · simp only [hmem_iff, hon]
          · intro hmem
            exact hpos (hmem_iff.mp hmem))
  rw [hl_s₁] at ht₂ hQ₁_end hbuf₂
  obtain ⟨harr₂, hon₂, hpos₂, hreg₂⟩ := hQ₁_end
  rw [List.take_length] at hon₂ hpos₂
  simp only [flatMap_nil_fun, List.append_nil, List.length_nil, Nat.sub_zero] at hbuf₂
  have hu_mem_l : u.val ∈ l ↔ u ∈ D := List.mem_map_of_injective Fin.val_injective
  have hru₂ : s₂.regs r_u = u.val := by
    rw [hreg₂ r_u (by simp [hu_on, hu_pos, hu_k, hu_hi, hu_y])]
    simp [s₁, hu_nc, hu_on, hu_pos, hu]
  -- Phase 3: branch on r_onD
  by_cases huD : u ∈ D
  · -- Branch 1: u ∈ D
    have hu_in_l : u.val ∈ l := hu_mem_l.mpr huD
    simp only [hu_in_l, ↓reduceIte] at hon₂
    have hpos_val : s₂.regs r_pos = D.idxOf u := by
      rw [hpos₂ hu_in_l, idxOf_map_val]
    have hcond_on : (Expr.reg r_onD).eval w s₂ = some 1 := eval_reg hon₂ hw1
    have hcyc₂ : s₂.arrs a.cyc = l := by rw [harr₂, hl_s₁]
    set s₃ := s₂.setReg r_clen D.length
    have hex_clen : Exec w (.assign r_clen (.len a.cyc)) s₂ s₃ 2 := by
      refine .assign ?_
      rw [eval_len rfl (by rw [hcyc₂]; simp [l]; omega), hcyc₂]
      simp [l]
    have hclen_s₃ : s₃.regs r_clen = D.length := by simp [s₃]
    by_cases hlen4 : 4 < D.length
    · -- Subbranch 1a: 4 < D.length (emit two cycle neighbours)
      have hlt_eval : (Expr.op .lt (.const 4) (.reg r_clen)).eval w s₃ = some 1 := by
        have := eval_lt (w := w) (s := s₃) (eval_const (c := 4) (by omega))
          (eval_reg (w := w) hclen_s₃ (by omega)) hw1
        simpa only [hlen4, ↓reduceIte] using this
      have hpos_lt : D.idxOf u < D.length := List.idxOf_lt_length_of_mem huD
      have h3 : 3 ≤ D.length := hD.1
      set idx1 := nextCycIdx D.length (D.idxOf u)
      set idx2 := prevCycIdx D.length (D.idxOf u)
      have hidx1_lt : idx1 < D.length := nextCycIdx_lt h3 hpos_lt
      have hidx2_lt : idx2 < D.length := prevCycIdx_lt h3 hpos_lt
      set v₁ := (D[idx1]'hidx1_lt).val
      set v₂ := (D[idx2]'hidx2_lt).val
      have hv₁_w : v₁ < 2 ^ w := by have := (D[idx1]'hidx1_lt).2; omega
      have hv₂_w : v₂ < 2 ^ w := by have := (D[idx2]'hidx2_lt).2; omega
      -- Step 1: r_k := r_pos + 1
      set s₄ := s₃.setReg r_k (D.idxOf u + 1)
      have hex₄ : Exec w (.assign r_k (.op .add (.reg r_pos) (.const 1))) s₃ s₄ 4 :=
        .assign (eval_add (eval_reg (w := w) (by simp [s₃, hpos_cl, hpos_val]) (by omega))
          (eval_const hw1) (by omega))
      -- Step 2: if r_k = r_clen then r_k := 0 else skip
      have hex₅ : ∃ s₅ t₅,
          Exec w (.ite (.op .eq (.reg r_k) (.reg r_clen)) (.assign r_k (.const 0)) .skip) s₄ s₅ t₅ ∧
          t₅ ≤ 5 ∧ s₅.arrs = s₄.arrs ∧ s₅.regs r_k = idx1 ∧
          (∀ r, r ≠ r_k → s₅.regs r = s₄.regs r) := by
        by_cases heq1 : D.idxOf u + 1 = D.length
        · refine ⟨s₄.setReg r_k 0, 5, exec_ite_eq_true (a := D.length) (by simp [s₄, heq1])
            (by simp [s₄, s₃, hcl_k]) (by omega) hw1 (.assign (eval_const (by omega))),
            by omega, rfl, by simp [idx1, nextCycIdx, heq1],
            fun r hr => State.setReg_regs_ne _ _ hr⟩
        · refine ⟨s₄, 4, exec_ite_eq_false (by simp [s₄]) (by simp [s₄, s₃, hcl_k])
            heq1 (by omega) (by omega) hw1 (.skip _),
            by omega, rfl, by simp [s₄, idx1, nextCycIdx, heq1], fun _ _ => rfl⟩
      obtain ⟨s₅, t₅, hex₅, ht₅, harr₅, hrk₅, hreg₅⟩ := hex₅
      -- Step 3: r_y := a.cyc[r_k]
      have hcyc₅ : s₅.arrs a.cyc = l := by rw [harr₅]; exact hcyc₂
      have hv₁_get : (s₅.arrs a.cyc)[idx1]'(by rw [hcyc₅]; simp [l, hidx1_lt]) = v₁ := by
        simp [hcyc₅, l, v₁]
      have hread_v₁ : (Expr.read a.cyc (.reg r_k)).eval w s₅ = some v₁ := by
        rw [← hv₁_get]
        exact eval_read (w := w) (eval_reg (w := w) hrk₅ (by omega))
          (by rw [hcyc₅]; simp [l, hidx1_lt]) (by rw [hv₁_get]; exact hv₁_w)
      set s₆ := s₅.setReg r_y v₁
      have hex₆ : Exec w (.assign r_y (.read a.cyc (.reg r_k))) s₅ s₆ 3 := .assign hread_v₁
      -- Step 4: emitProg a_cv r_ncand (.reg r_y)
      have hbuf₆ : IsBuf a_cv r_ncand [] (63 + 1) s₆ := by
        refine ⟨by rw [State.setReg_arrs, harr₅]; exact hbuf₂.1, ?_⟩
        rw [State.setReg_regs_ne _ _ hnc_y, hreg₅ r_ncand hnc_k]
        simp [s₄, s₃, hnc_k, hnc_cl, hbuf₂.2]
      obtain ⟨s₇, hex₇, hbuf₇, harr₇, hreg₇⟩ :=
        emitReg_exec (w := w) a_cv r_ncand r_y hbuf₆ (by simp [s₆]) hv₁_w hw1
      -- Step 5: compute idx2 in r_k
      have hrpos₇ : s₇.regs r_pos = D.idxOf u := by
        rw [hreg₇ r_pos hnc_pos.symm, State.setReg_regs_ne _ _ hpos_y, hreg₅ r_pos hpos_k]
        simp [s₄, s₃, hpos_k, hpos_cl, hpos_val]
      have hrclen₇ : s₇.regs r_clen = D.length := by
        rw [hreg₇ r_clen hnc_cl.symm, State.setReg_regs_ne _ _ hcl_y, hreg₅ r_clen hcl_k]
        simp [s₄, s₃, hcl_k]
      have hex₈ : ∃ s₈ t₈,
          Exec w (.ite (.op .eq (.reg r_pos) (.const 0))
            (.assign r_k (.op .sub (.reg r_clen) (.const 1)))
            (.assign r_k (.op .sub (.reg r_pos) (.const 1)))) s₇ s₈ t₈ ∧
          t₈ ≤ 7 ∧ s₈.arrs = s₇.arrs ∧ s₈.regs r_k = idx2 ∧
          (∀ r, r ≠ r_k → s₈.regs r = s₇.regs r) := by
        have heq_eval : (Expr.op .eq (.reg r_pos) (.const 0)).eval w s₇ =
            some (if D.idxOf u = 0 then 1 else 0) :=
          eval_eq (eval_reg (w := w) hrpos₇ (by omega)) (eval_const (c := 0) (by omega)) hw1
        by_cases hp0 : D.idxOf u = 0
        · simp only [hp0, ↓reduceIte] at heq_eval
          refine ⟨s₇.setReg r_k (D.length - 1), 7,
            .ite_true heq_eval (show 1 ≠ 0 by decide)
              (.assign (eval_sub (eval_reg (w := w) hrclen₇ (by omega)) (eval_const hw1))),
            by omega, rfl, by simp [idx2, prevCycIdx, hp0],
            fun r hr => State.setReg_regs_ne _ _ hr⟩
        · simp only [hp0, ↓reduceIte] at heq_eval
          refine ⟨s₇.setReg r_k (D.idxOf u - 1), 7,
            .ite_false heq_eval
              (.assign (eval_sub (eval_reg (w := w) hrpos₇ (by omega)) (eval_const hw1))),
            by omega, rfl, by simp [idx2, prevCycIdx, hp0],
            fun r hr => State.setReg_regs_ne _ _ hr⟩
      obtain ⟨s₈, t₈, hex₈, ht₈, harr₈, hrk₈, hreg₈⟩ := hex₈
      -- Step 6: r_y := a.cyc[r_k]
      have hcyc₈ : s₈.arrs a.cyc = l := by
        rw [harr₈, harr₇ a.cyc hcyc_ne, State.setReg_arrs, harr₅]
        exact hcyc₂
      have hv₂_get : (s₈.arrs a.cyc)[idx2]'(by rw [hcyc₈]; simp [l, hidx2_lt]) = v₂ := by
        simp [hcyc₈, l, v₂]
      have hread_v₂ : (Expr.read a.cyc (.reg r_k)).eval w s₈ = some v₂ := by
        rw [← hv₂_get]
        exact eval_read (w := w) (eval_reg (w := w) hrk₈ (by omega))
          (by rw [hcyc₈]; simp [l, hidx2_lt]) (by rw [hv₂_get]; exact hv₂_w)
      set s₉ := s₈.setReg r_y v₂
      have hex₉ : Exec w (.assign r_y (.read a.cyc (.reg r_k))) s₈ s₉ 3 := .assign hread_v₂
      -- Step 7: emitProg a_cv r_ncand (.reg r_y)
      have hbuf₉ : IsBuf a_cv r_ncand [v₁] (62 + 1) s₉ := by
        refine ⟨by rw [State.setReg_arrs, harr₈]; exact hbuf₇.1, ?_⟩
        rw [State.setReg_regs_ne _ _ hnc_y, hreg₈ r_ncand hnc_k]
        exact hbuf₇.2
      obtain ⟨s₁₀, hex₁₀, hbuf₁₀, harr₁₀, hreg₁₀⟩ :=
        emitReg_exec (w := w) a_cv r_ncand r_y hbuf₉ (by simp [s₉]) hv₂_w (show 2 < 2 ^ w by omega)
      have hcand_eq : candVals D lists u = [v₁, v₂] := by
        simp [candVals, huD, hlen4, idx1, idx2, v₁, v₂]
      refine ⟨s₁₀, _, hex₁ (.seq hex₂ (.ite_true hcond_on (show 1 ≠ 0 by decide)
        (.seq hex_clen (.ite_true hlt_eval (show 1 ≠ 0 by decide)
          (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))))),
        by simp only [Expr.cost, l, List.length_map] at ht₂ ⊢; omega,
        by simpa [hcand_eq] using hbuf₁₀, ?_, ?_⟩
      · intro x hx
        rw [harr₁₀ x hx, State.setReg_arrs, harr₈, harr₇ x hx, State.setReg_arrs, harr₅]
        simp only [s₄, s₃, State.setReg_arrs, harr₂, s₁, State.setArr_arrs_ne _ _ hx]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
        rw [hreg₁₀ r h1, State.setReg_regs_ne _ _ h7, hreg₈ r h5, hreg₇ r h1,
          State.setReg_regs_ne _ _ h7, hreg₅ r h5]
        simp only [s₄, s₃, State.setReg_regs_ne _ _ h5, State.setReg_regs_ne _ _ h4]
        rw [hreg₂ r (by simp [h2, h3, h5, h6, h7])]
        simp [s₁, h1, h2, h3]
    · -- Subbranch 1b: ¬ (4 < D.length) (emit nothing)
      have hlt_eval : (Expr.op .lt (.const 4) (.reg r_clen)).eval w s₃ = some 0 := by
        have := eval_lt (w := w) (s := s₃) (eval_const (c := 4) (by omega))
          (eval_reg (w := w) hclen_s₃ (by omega)) hw1
        simpa only [hlen4, ↓reduceIte] using this
      have hcand_eq : candVals D lists u = [] := by simp [candVals, huD, hlen4]
      refine ⟨s₃, _, hex₁ (.seq hex₂ (.ite_true hcond_on (show 1 ≠ 0 by decide)
        (.seq hex_clen (.ite_false hlt_eval (.skip _))))),
        by simp only [Expr.cost, l, List.length_map] at ht₂ ⊢; omega,
        ?_, ?_, ?_⟩
      · rw [hcand_eq]
        exact ⟨hbuf₂.1, by simp [s₃, hnc_cl, hbuf₂.2]⟩
      · intro x hx
        simp only [s₃, State.setReg_arrs, harr₂, s₁, State.setArr_arrs_ne _ _ hx]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
        simp only [s₃, State.setReg_regs_ne _ _ h4]
        rw [hreg₂ r (by simp [h2, h3, h5, h6, h7])]
        simp [s₁, h1, h2, h3]
  · -- Branch 2: u ∉ D (emit listOf lists u via forList)
    have hu_not_l : u.val ∉ l := fun h => huD (hu_mem_l.mp h)
    simp only [hu_not_l, ↓reduceIte] at hon₂
    have hcond_off : (Expr.reg r_onD).eval w s₂ = some 0 := eval_reg hon₂ (by omega)
    have hcand_eq : candVals D lists u = listOf lists u.val := by simp [candVals, huD]
    obtain ⟨st_u, en_u, hlist_u, hen_u⟩ := exists_isListAt hadj u.2
    have hlist_s₂ : IsListAt a.st a.en a.ent u.val st_u en_u (listOf lists u.val) s₂ := by
      refine hlist_u.of_arrs_eq ?_ ?_ ?_
      · simp only [harr₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hst_ne]
      · simp only [harr₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hen_ne]
      · simp only [harr₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hent_ne]
    have h2m_w : (s.arrs a.ent).length < 2 ^ w := by
      rw [hent_len]; unfold instSize at hw; omega
    have hen_w : en_u < 2 ^ w := Nat.lt_of_le_of_lt hen_u h2m_w
    have hlu_lt := listOf_lt hadj.2 u.val
    have hlu_w : ∀ y ∈ listOf lists u.val, y < 2 ^ w := fun y hy => by
      have := hlu_lt y hy; omega
    have hlu_len : (listOf lists u.val).length ≤ 64 := by
      rw [ ← hcand_eq]
      exact length_candVals_le hadj.2 hdeg
    let Q₂ : ℕ → State → Prop := fun _ st =>
      (∀ x, x ≠ a_cv → st.arrs x = s₂.arrs x) ∧
      (∀ r, r ∉ [r_ncand, r_k, r_hi, r_y] → st.regs r = s₂.regs r)
    have hflat_id : ∀ L : List ℕ, L.flatMap (fun y => [y]) = L := by
      intro L; induction L <;> simp [*]
    obtain ⟨s₃, t₃, hex₃, ht₃, hQ₂_end, hbuf₃⟩ :=
      forListEmit_exec a.st a.en a.ent r_u r_k r_hi r_y a_cv r_ncand
        (emitProg a_cv r_ncand (.reg r_y)) u.val st_u en_u (listOf lists u.val)
        (fun y => [y]) Q₂ 7
        (pre := []) (k := 64)
        hu_k hk_hi hnc_k.symm hnc_hi.symm hnc_y.symm hk_y.symm hhi_y.symm
        hw1 hen_w (by omega) hlist_s₂ hru₂ hlu_w
        ⟨fun _ _ => rfl, fun _ _ => rfl⟩ hbuf₂
        (by rw [hflat_id]; exact hlu_len)
        (fun j st st' ⟨ha, hr⟩ ha' hr' =>
          ⟨fun x hx => (congrFun ha' x).trans (ha x hx),
           fun r hr'' => by
             simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
             exact (hr' r hr''.2.1 hr''.2.2.1 hr''.2.2.2).trans (hr r (by simp [hr'']))⟩)
        (fun j st ⟨ha, _⟩ => ha a.ent hent_ne)
        (fun j hj st pre' k' ⟨ha, hr⟩ hrk hrh hry hb' hk' hpk => by
          have hy_w : (listOf lists u.val)[j] < 2 ^ w := hlu_w _ (List.getElem_mem hj)
          simp only [List.length_singleton, List.length_nil, zero_add] at hk' hpk
          have hb'' : IsBuf a_cv r_ncand pre' ((k' - 1) + 1) st := by
            rw [show (k' - 1) + 1 = k' by omega]
            exact hb'
          obtain ⟨st', hex_em, hb_em, ha_em, hr_em⟩ :=
            emitReg_exec (w := w) a_cv r_ncand r_y hb'' hry hy_w (by omega)
          refine ⟨st', 7, hex_em, le_refl _,
            ⟨fun x hx => (ha_em x hx).trans (ha x hx),
             fun r hr'' => by
               simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
               exact (hr_em r hr''.1).trans (hr r (by simp [hr'']))⟩,
            (hr_em r_k hnc_k.symm).trans hrk,
            (hr_em r_hi hnc_hi.symm).trans hrh,
            by simpa using hb_em⟩)
    rw [hflat_id, List.nil_append, ← hcand_eq] at hbuf₃
    obtain ⟨ha₃, hr₃⟩ := hQ₂_end
    refine ⟨s₃, _, hex₁ (.seq hex₂ (.ite_false hcond_off hex₃)),
      by simp only [Expr.cost, l, List.length_map] at ht₂ ht₃ ⊢; omega,
      hbuf₃, ?_, ?_⟩
    · intro x hx
      rw [ha₃ x hx, harr₂]
      simp only [s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hx]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hr
      rw [hr₃ r (by simp [h1, h5, h6, h7]), hreg₂ r (by simp [h2, h3, h5, h6, h7])]
      simp [s₁, h1, h2, h3]

end GraphMinor.Compute.Crossing
