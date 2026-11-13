module

public import GraphMinor.Compute.CrossingCleanAux
public import GraphMinor.Compute.CrossingOpsEmit
public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Breadth-first reachability and boundary filtering for the crossing extractor

Section 4 of `docs/crossing/crossing_extractor.tex`: "First we discard the components of $G$ that
do not contain $C$", and, at steps 4 and 5, "Find the component $A$ of $K-S$ that contains $v$.
Replace $A$ by the clique on its actual neighborhood $N_K(A)$, using Lemma 1." Section 9.2, step 8:
"Record one component of $B-\{p,q\}$ inside $U$, for example the component containing $z$, as the
connected representative for the later lifting."

This file implements and verifies the Word RAM reachability search and boundary-filtering
subprograms used by `CrossingCleanInit.lean` and `CrossingCleanRestore.lean`:
* `ReachSet G W srcs`: the set `{y ∈ W | ∃ u ∈ srcs, ReachIn G W u y}` of vertices in `W`
  reachable in `G[W]` from a list of sources `srcs`.
* `reachSearchProg`: breadth-first search on an instance `(G, S, D)` inside an allowed vertex set
  `W` (given by its indicator array `a_allow`) from a source list `a_src`, producing both the
  indicator array `a_rch` of `ReachSet G W srcs` and a duplicate-free vertex list `a_out`
  (`IsSetListAt a_out (ReachSet G W srcs) s'`).
* `allowMinusSepProg` and `allowFromListProg`: indicator-array constructors for `S \ X₀` and for
  a vertex list `U`.
* `filterSepToBdProg`: filters a separator array `a_sep` to those vertices adjacent in `G` to a
  reached component `A`, producing `IsSetListAt a_bd (nbhd G A) s'`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open Classical SimpleGraph GraphMinor.Crossing

/-! ### Reachable vertex set from a list of sources -/

/-- The set of vertices in `W` reachable in `G` through `W` from some source in `srcs`. -/
def ReachSet {V : Type*} (G : SimpleGraph V) (W : Set V) (srcs : List V) : Set V :=
  {y | y ∈ W ∧ ∃ u ∈ srcs, ReachIn G W u y}

theorem mem_reachSet_iff {V : Type*} {G : SimpleGraph V} {W : Set V} {srcs : List V} {y : V} :
    y ∈ ReachSet G W srcs ↔ y ∈ W ∧ ∃ u ∈ srcs, ReachIn G W u y := Iff.rfl

theorem reachSet_subset {V : Type*} (G : SimpleGraph V) (W : Set V) (srcs : List V) :
    ReachSet G W srcs ⊆ W := fun _ h => h.1

theorem mem_reachSet_of_mem_srcs {V : Type*} {G : SimpleGraph V} {W : Set V} {srcs : List V}
    {u : V} (hu : u ∈ srcs) (huW : u ∈ W) : u ∈ ReachSet G W srcs :=
  ⟨huW, u, hu, ReachIn.refl huW⟩

theorem mem_reachSet_of_adj {V : Type*} {G : SimpleGraph V} {W : Set V} {srcs : List V}
    {u v : V} (hu : u ∈ ReachSet G W srcs) (hadj : G.Adj u v) (hvW : v ∈ W) :
    v ∈ ReachSet G W srcs := by
  obtain ⟨_, s₀, hs₀, hreach⟩ := hu
  exact ⟨hvW, s₀, hs₀, ReachIn.step_right hreach hadj hvW⟩

theorem reachSet_singleton {V : Type*} (G : SimpleGraph V) (W : Set V) {v : V} :
    ReachSet G W [v] = {y | ReachIn G W v y} := by
  ext y
  simp only [ReachSet, Set.mem_ofPred_eq, List.mem_singleton, exists_eq_left]
  exact ⟨fun h => h.2, fun ⟨p, hp⟩ => ⟨hp y p.end_mem_support, p, hp⟩⟩

theorem reachSet_eq_of_closed {N : ℕ} {G : SimpleGraph (Fin N)} {W : Set (Fin N)}
    {srcs : List (Fin N)} {items : List ℕ}
    (hreach : ∀ x : Fin N, x.1 ∈ items → x ∈ ReachSet G W srcs)
    (hsrcs : ∀ u ∈ srcs, u ∈ W → u.1 ∈ items)
    (hcl : ∀ u : Fin N, u.1 ∈ items → ∀ v : Fin N, G.Adj u v → v ∈ W → v.1 ∈ items) :
    ∀ x : Fin N, x.1 ∈ items ↔ x ∈ ReachSet G W srcs := by
  intro x
  refine ⟨hreach x, ?_⟩
  rintro ⟨_, u, hu_src, ⟨p, hp⟩⟩
  have hwalk : ∀ {a b : Fin N} (q : G.Walk a b),
      a.1 ∈ items → (∀ z ∈ q.support, z ∈ W) → b.1 ∈ items := by
    intro a b q
    induction q with
    | nil => intro ha _; exact ha
    | @cons a w b hadj rest ih =>
      intro ha hsupp
      have hwW : w ∈ W := hsupp w (List.mem_cons_of_mem _ rest.start_mem_support)
      have hw_it : w.1 ∈ items := hcl a ha w hadj hwW
      exact ih hw_it (fun z hz => hsupp z (List.mem_cons_of_mem _ hz))
  exact hwalk p (hsrcs u hu_src (hp u p.start_mem_support)) hp

/-! ### Visiting one candidate vertex in BFS -/

/-- If `r_v` is allowed (`a_allow[r_v] = 1`) and not yet reached (`a_rch[r_v] = 0`), mark it in
`a_rch` and append it to the queue buffer `(a_que, r_tail)`. -/
def visitVertexProg (a_allow a_rch a_que : Arr) (r_v r_tail r_tmp : Reg) : Cmd :=
  .seq (.assign r_tmp (.read a_allow (.reg r_v)))
    (.ite (.op .eq (.reg r_tmp) (.const 1))
      (.seq (.assign r_tmp (.read a_rch (.reg r_v)))
        (.ite (.op .eq (.reg r_tmp) (.const 0))
          (.seq (.write a_rch (.reg r_v) (.const 1))
            (emitProg a_que r_tail (.reg r_v)))
          .skip))
      .skip)

/-- State invariant for the reached list `items` during BFS. -/
structure RState {N : ℕ} (G : SimpleGraph (Fin N)) (W : Set (Fin N)) (srcs : List (Fin N))
    (a_rch a_que : Arr) (r_tail : Reg) (items : List ℕ) (s : State) : Prop where
  nodup : items.Nodup
  lt : ∀ x ∈ items, x < N
  reach : ∀ x : Fin N, x.1 ∈ items → x ∈ ReachSet G W srcs
  rch_arr : s.arrs a_rch = List.ofFn (fun x : Fin N => if x.1 ∈ items then 1 else 0)
  que_buf : IsBuf a_que r_tail items (N - items.length) s

theorem RState.length_le {N : ℕ} {G : SimpleGraph (Fin N)} {W : Set (Fin N)}
    {srcs : List (Fin N)} {a_rch a_que : Arr} {r_tail : Reg} {items : List ℕ} {s : State}
    (h : RState G W srcs a_rch a_que r_tail items s) : items.length ≤ N :=
  length_le_of_nodup_lt h.nodup h.lt

theorem RState.of_arrs_regs_eq {N : ℕ} {G : SimpleGraph (Fin N)} {W : Set (Fin N)}
    {srcs : List (Fin N)} {a_rch a_que : Arr} {r_tail : Reg} {items : List ℕ} {s s' : State}
    (h : RState G W srcs a_rch a_que r_tail items s)
    (hrch : s'.arrs a_rch = s.arrs a_rch) (hque : s'.arrs a_que = s.arrs a_que)
    (htail : s'.regs r_tail = s.regs r_tail) :
    RState G W srcs a_rch a_que r_tail items s' :=
  ⟨h.nodup, h.lt, h.reach, hrch.trans h.rch_arr, ⟨hque.trans h.que_buf.1, htail.trans h.que_buf.2⟩⟩

theorem ofFn_set_mem_append {N : ℕ} (items : List ℕ) (v : Fin N) :
    (List.ofFn (fun x : Fin N => if x.1 ∈ items then 1 else 0)).set v.1 1 =
      List.ofFn (fun x : Fin N => if x.1 ∈ items ++ [v.1] then 1 else 0) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_set, List.getElem_ofFn, List.mem_append, List.mem_singleton]
  by_cases hiv : v.1 = i
  · subst hiv; simp
  · have hne : i ≠ v.1 := Ne.symm hiv
    simp [hiv, hne]

/-- Executing `visitVertexProg` on a vertex `v : Fin N` in register `r_v` when `v ∈ W → v ∈ ReachSet`. -/
theorem visitVertexProg_exec {w N : ℕ} {G : SimpleGraph (Fin N)} {W : Set (Fin N)}
    {srcs : List (Fin N)} (a_allow a_rch a_que r_v r_tail r_tmp : ℕ)
    (_haar : a_allow ≠ a_rch) (_haaq : a_allow ≠ a_que) (hrq : a_rch ≠ a_que)
    (_hvt : r_v ≠ r_tail) (hvtmp : r_v ≠ r_tmp) (httmp : r_tail ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    {items : List ℕ} {s : State} (v : Fin N)
    (hst : RState G W srcs a_rch a_que r_tail items s)
    (hallow : s.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0))
    (hrv : s.regs r_v = v.1)
    (hv_reach : v ∈ W → v ∈ ReachSet G W srcs) :
    ∃ (s' : State) (t : ℕ) (extra : List ℕ),
      Exec w (visitVertexProg a_allow a_rch a_que r_v r_tail r_tmp) s s' t ∧
      t ≤ 23 ∧
      RState G W srcs a_rch a_que r_tail (items ++ extra) s' ∧
      (v ∈ W → v.1 ∈ items ++ extra) ∧
      (∀ a, a ≠ a_rch → a ≠ a_que → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_tail → r ≠ r_tmp → s'.regs r = s.regs r) := by
  classical
  have hvw : v.1 < 2 ^ w := lt_trans v.2 hN
  have h0w : 0 < 2 ^ w := by omega
  set av : ℕ := if v ∈ W then 1 else 0
  have hav_w : av < 2 ^ w := by simp only [av]; split_ifs <;> omega
  have hal_len : v.1 < (s.arrs a_allow).length := by rw [hallow]; simp
  have hal_val : (s.arrs a_allow)[v.1]'hal_len = av := by simp [hallow, av]
  have hrd_allow : (Expr.read a_allow (.reg r_v)).eval w s = some av := by
    have := eval_read (a := a_allow) (eval_reg hrv hvw) hal_len (by rw [hal_val]; exact hav_w)
    rwa [hal_val] at this
  set s₁ := s.setReg r_tmp av
  have hex₁ : Exec w (.assign r_tmp (.read a_allow (.reg r_v))) s s₁ 3 := .assign hrd_allow
  by_cases hvW : v ∈ W
  · have hav1 : av = 1 := by simp [av, hvW]
    have hcond1 : (Expr.op .eq (.reg r_tmp) (.const 1)).eval w s₁ = some 1 := by
      have := eval_eq (s := s₁) (eval_reg (r := r_tmp) (by simp [s₁, hav1]) hw) (eval_const hw) hw
      simpa using this
    set rv0 : ℕ := if v.1 ∈ items then 1 else 0
    have hrv0_w : rv0 < 2 ^ w := by simp only [rv0]; split_ifs <;> omega
    have hrch_len : v.1 < (s₁.arrs a_rch).length := by simp [s₁, hst.rch_arr]
    have hrch_val : (s₁.arrs a_rch)[v.1]'hrch_len = rv0 := by simp [s₁, hst.rch_arr, rv0]
    have hrd_rch : (Expr.read a_rch (.reg r_v)).eval w s₁ = some rv0 := by
      have hrv₁ : s₁.regs r_v = v.1 := by simp [s₁, hvtmp, hrv]
      have := eval_read (a := a_rch) (eval_reg hrv₁ hvw) hrch_len (by rw [hrch_val]; exact hrv0_w)
      rwa [hrch_val] at this
    set s₂ := s₁.setReg r_tmp rv0
    have hex₂ : Exec w (.assign r_tmp (.read a_rch (.reg r_v))) s₁ s₂ 3 := .assign hrd_rch
    by_cases hmem : v.1 ∈ items
    · have hrv0_1 : rv0 = 1 := by simp [rv0, hmem]
      have hcond2 : (Expr.op .eq (.reg r_tmp) (.const 0)).eval w s₂ = some 0 := by
        have := eval_eq (s := s₂) (eval_reg (r := r_tmp) (by simp [s₂, hrv0_1]) hw)
          (eval_const h0w) hw
        simpa using this
      have hex_ite2 : Exec w (.ite (.op .eq (.reg r_tmp) (.const 0))
          (.seq (.write a_rch (.reg r_v) (.const 1)) (emitProg a_que r_tail (.reg r_v))) .skip)
          s₂ s₂ 4 := .ite_false hcond2 (.skip s₂)
      have hex_ite1 : Exec w (.ite (.op .eq (.reg r_tmp) (.const 1))
          (.seq (.assign r_tmp (.read a_rch (.reg r_v)))
            (.ite (.op .eq (.reg r_tmp) (.const 0))
              (.seq (.write a_rch (.reg r_v) (.const 1)) (emitProg a_que r_tail (.reg r_v))) .skip))
          .skip) s₁ s₂ 10 := .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
      refine ⟨s₂, 13, [], .seq hex₁ hex_ite1, by omega, ?_, by simpa using fun _ => hmem,
        fun a _ _ => rfl, fun r _ h2 => by simp [s₂, s₁, h2]⟩
      simp only [List.append_nil]
      exact hst.of_arrs_regs_eq (s' := s₂) rfl rfl (by simp [s₂, s₁, httmp])
    · have hrv0_0 : rv0 = 0 := by simp [rv0, hmem]
      have hcond2 : (Expr.op .eq (.reg r_tmp) (.const 0)).eval w s₂ = some 1 := by
        have := eval_eq (s := s₂) (eval_reg (r := r_tmp) (by simp [s₂, hrv0_0]) h0w)
          (eval_const h0w) hw
        simpa using this
      have hrv₂ : s₂.regs r_v = v.1 := by simp [s₂, s₁, hvtmp, hrv]
      have hrch_len₂ : v.1 < (s₂.arrs a_rch).length := by simp [s₂, s₁, hst.rch_arr]
      have hex_wr : Exec w (.write a_rch (.reg r_v) (.const 1)) s₂ (s₂.writeArr a_rch v.1 1) 3 :=
        .write (eval_reg hrv₂ hvw) (eval_const hw) hrch_len₂
      set s₃ := s₂.writeArr a_rch v.1 1
      have hnd' : (items ++ [v.1]).Nodup :=
        hst.nodup.append (List.nodup_singleton v.1)
          (fun x hx hx' => hmem (by simp only [List.mem_singleton] at hx'; rwa [← hx']))
      have hlt' : ∀ x ∈ items ++ [v.1], x < N := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hst.lt x hx
        · simp only [List.mem_singleton] at hx; subst hx; exact v.2
      have hlen' : (items ++ [v.1]).length ≤ N := length_le_of_nodup_lt hnd' hlt'
      have hlen_lt : items.length < N := by simp at hlen'; omega
      have hbuf₃ : IsBuf a_que r_tail items ((N - (items ++ [v.1]).length) + 1) s₃ := by
        refine ⟨?_, ?_⟩
        · simp only [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hrq.symm, State.setReg_arrs]
          rw [hst.que_buf.1]
          congr 2; simp; omega
        · simp [s₃, s₂, s₁, httmp, hst.que_buf.2]
      obtain ⟨s₄, hex_em, hbuf₄, harr₄, hreg₄⟩ :=
        emitReg_exec a_que r_tail r_v hbuf₃ (by simp [s₃, hrv₂]) hvw (by omega)
      have hex_ite2 : Exec w (.ite (.op .eq (.reg r_tmp) (.const 0))
          (.seq (.write a_rch (.reg r_v) (.const 1)) (emitProg a_que r_tail (.reg r_v))) .skip)
          s₂ s₄ 13 := .ite_true hcond2 one_ne_zero (.seq hex_wr hex_em)
      have hex_ite1 : Exec w (.ite (.op .eq (.reg r_tmp) (.const 1))
          (.seq (.assign r_tmp (.read a_rch (.reg r_v)))
            (.ite (.op .eq (.reg r_tmp) (.const 0))
              (.seq (.write a_rch (.reg r_v) (.const 1)) (emitProg a_que r_tail (.reg r_v))) .skip))
          .skip) s₁ s₄ 19 := .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
      refine ⟨s₄, 22, [v.1], .seq hex₁ hex_ite1, by omega, ?_, by simp, ?_, ?_⟩
      · refine ⟨hnd', hlt', ?_, ?_, hbuf₄⟩
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hst.reach x hx
          · simp only [List.mem_singleton] at hx
            have hxv : x = v := Fin.ext hx
            subst hxv
            exact hv_reach hvW
        · rw [harr₄ a_rch hrq]
          simp only [s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hst.rch_arr]
          exact ofFn_set_mem_append items v
      · intro a ha1 ha2
        rw [harr₄ a ha2]
        simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha1]
      · intro r hr1 hr2
        rw [hreg₄ r hr1]
        simp [s₃, s₂, s₁, hr2]
  · have hav0 : av = 0 := by simp [av, hvW]
    have hcond1 : (Expr.op .eq (.reg r_tmp) (.const 1)).eval w s₁ = some 0 := by
      have := eval_eq (s := s₁) (eval_reg (r := r_tmp) (by simp [s₁, hav0]) h0w) (eval_const hw) hw
      simpa using this
    have hex_ite1 : Exec w (.ite (.op .eq (.reg r_tmp) (.const 1))
        (.seq (.assign r_tmp (.read a_rch (.reg r_v)))
          (.ite (.op .eq (.reg r_tmp) (.const 0))
            (.seq (.write a_rch (.reg r_v) (.const 1)) (emitProg a_que r_tail (.reg r_v))) .skip))
        .skip) s₁ s₁ 4 := .ite_false hcond1 (.skip s₁)
    refine ⟨s₁, 7, [], .seq hex₁ hex_ite1, by omega, ?_, fun h => (hvW h).elim,
      fun a _ _ => rfl, fun r _ h2 => by simp [s₁, h2]⟩
    simp only [List.append_nil]
    exact hst.of_arrs_regs_eq (s' := s₁) rfl rfl (by simp [s₁, httmp])

/-! ### Pushing the initial sources and scanning one adjacency list -/

/-- Loop over the source array `a_src` to visit every initial source. -/
def reachInitSrcProg (a_src a_allow a_rch a_que : Arr)
    (r_i r_n r_v r_tail r_tmp : Reg) : Cmd :=
  forArrProg a_src r_i r_n r_v (visitVertexProg a_allow a_rch a_que r_v r_tail r_tmp)

theorem reachInitSrcProg_exec {w N : ℕ} {G : SimpleGraph (Fin N)} {W : Set (Fin N)}
    {srcs : List (Fin N)} (a_src a_allow a_rch a_que r_i r_n r_v r_tail r_tmp : ℕ)
    (hsr : a_src ≠ a_rch) (hsq : a_src ≠ a_que)
    (haar : a_allow ≠ a_rch) (haaq : a_allow ≠ a_que) (hrq : a_rch ≠ a_que)
    (hin : r_i ≠ r_n) (hvi : r_v ≠ r_i) (hvn : r_v ≠ r_n)
    (hit : r_i ≠ r_tail) (hitmp : r_i ≠ r_tmp)
    (hnt : r_n ≠ r_tail) (hntmp : r_n ≠ r_tmp)
    (hvt : r_v ≠ r_tail) (hvtmp : r_v ≠ r_tmp) (httmp : r_tail ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) {s : State}
    (hsrc_arr : s.arrs a_src = srcs.map Fin.val)
    (hsrc_len : srcs.length < 2 ^ w)
    (hallow : s.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0))
    (hst0 : RState G W srcs a_rch a_que r_tail [] s) :
    ∃ (s' : State) (t : ℕ) (items : List ℕ),
      Exec w (reachInitSrcProg a_src a_allow a_rch a_que r_i r_n r_v r_tail r_tmp) s s' t ∧
      t ≤ 7 + srcs.length * 33 ∧
      RState G W srcs a_rch a_que r_tail items s' ∧
      (∀ u ∈ srcs, u ∈ W → u.1 ∈ items) ∧
      (∀ a, a ≠ a_rch → a ≠ a_que → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → r ≠ r_n → r ≠ r_v → r ≠ r_tail → r ≠ r_tmp → s'.regs r = s.regs r) := by
  let Q : ℕ → State → Prop := fun j st =>
    (∀ a, a ≠ a_rch → a ≠ a_que → st.arrs a = s.arrs a) ∧
    (∀ r, r ≠ r_i → r ≠ r_n → r ≠ r_v → r ≠ r_tail → r ≠ r_tmp → st.regs r = s.regs r) ∧
    ∃ items : List ℕ,
      RState G W srcs a_rch a_que r_tail items st ∧
      (∀ u ∈ srcs.take j, u ∈ W → u.1 ∈ items)
  have hlen : (s.arrs a_src).length < 2 ^ w := by rw [hsrc_arr, List.length_map]; exact hsrc_len
  have hl_w : ∀ x ∈ s.arrs a_src, x < 2 ^ w := by
    intro x hx
    rw [hsrc_arr, List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    exact lt_trans u.2 hN
  have hQ0 : Q 0 s := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, [], hst0, by simp⟩
  obtain ⟨s', t, hex, ht, hQ⟩ := forArr_exec a_src r_i r_n r_v
    (visitVertexProg a_allow a_rch a_que r_v r_tail r_tmp) Q 23 hin hvi hvn hw hlen hl_w hQ0
    (fun j s₁ s₂ hQ harr hreg => by
      obtain ⟨ha₁, hr₁, items, hst₁, hsrc₁⟩ := hQ
      refine ⟨fun a h1 h2 => by rw [harr]; exact ha₁ a h1 h2,
        fun r h1 h2 h3 h4 h5 => by rw [hreg r h1 h2 h3]; exact hr₁ r h1 h2 h3 h4 h5,
        items, hst₁.of_arrs_regs_eq (by rw [harr]) (by rw [harr])
          (hreg r_tail hit.symm hnt.symm hvt.symm), hsrc₁⟩)
    (fun j s₁ hQ => hQ.1 a_src hsr hsq)
    (fun j hj s₁ hQ hri hrn hrv => by
      obtain ⟨ha₁, hr₁, items, hst₁, hsrc₁⟩ := hQ
      have hj' : j < srcs.length := by rwa [hsrc_arr, List.length_map] at hj
      set u : Fin N := srcs[j]'hj'
      have hsrc_j : (s.arrs a_src)[j]'hj = u.1 := by simp [hsrc_arr, u]
      have hallow₁ : s₁.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0) := by
        rw [ha₁ a_allow haar haaq, hallow]
      obtain ⟨s₂, t₂, extra, hex₂, ht₂, hst₂, hu_mem, ha₂, hr₂⟩ :=
        visitVertexProg_exec a_allow a_rch a_que r_v r_tail r_tmp haar haaq hrq hvt hvtmp httmp
          hw hN u hst₁ hallow₁ (by rw [hrv, hsrc_j])
          (fun huW => mem_reachSet_of_mem_srcs (List.getElem_mem hj') huW)
      refine ⟨s₂, t₂, hex₂, ht₂, ⟨?_, ?_, items ++ extra, hst₂, ?_⟩,
        by rw [hr₂ r_i hit hitmp, hri], by rw [hr₂ r_n hnt hntmp, hrn]⟩
      · intro a h1 h2; rw [ha₂ a h1 h2, ha₁ a h1 h2]
      · intro r h1 h2 h3 h4 h5; rw [hr₂ r h4 h5, hr₁ r h1 h2 h3 h4 h5]
      · intro y hy hyW
        rw [List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
          List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact List.mem_append_left _ (hsrc₁ y hy hyW)
        · exact hu_mem hyW)
  obtain ⟨ha', hr', items, hst', hsrc'⟩ := hQ
  have htake : srcs.take (s.arrs a_src).length = srcs := by
    rw [hsrc_arr, List.length_map, List.take_length]
  rw [htake] at hsrc'
  rw [hsrc_arr, List.length_map] at ht
  exact ⟨s', t, items, hex, ht, hst', hsrc', ha', hr'⟩

/-- Scan the adjacency list of a reached vertex `u` and visit all its neighbours. -/
theorem reachVisitAdj_exec {w N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (hlists : IsAdjListFamily G lists) {W : Set (Fin N)} {srcs : List (Fin N)}
    (a_st a_en a_ent a_allow a_rch a_que r_u r_k r_hi r_v r_tail r_tmp : ℕ)
    (hent_rch : a_ent ≠ a_rch) (hent_que : a_ent ≠ a_que)
    (haar : a_allow ≠ a_rch) (haaq : a_allow ≠ a_que) (hrq : a_rch ≠ a_que)
    (hku : r_u ≠ r_k) (hkh : r_k ≠ r_hi) (huh : r_u ≠ r_hi)
    (hvu : r_v ≠ r_u) (hvk : r_v ≠ r_k) (hvh : r_v ≠ r_hi)
    (hut : r_u ≠ r_tail) (hutmp : r_u ≠ r_tmp)
    (hkt : r_k ≠ r_tail) (hktmp : r_k ≠ r_tmp)
    (hht : r_hi ≠ r_tail) (hhtmp : r_hi ≠ r_tmp)
    (hvt : r_v ≠ r_tail) (hvtmp : r_v ≠ r_tmp) (httmp : r_tail ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    (u : Fin N) (st en : ℕ) (hen : en < 2 ^ w)
    {items : List ℕ} {s : State}
    (hlist : IsListAt a_st a_en a_ent u.1 st en (lists u) s)
    (hru : s.regs r_u = u.1)
    (hu_reach : u ∈ ReachSet G W srcs)
    (hallow : s.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0))
    (hst0 : RState G W srcs a_rch a_que r_tail items s) :
    ∃ (s' : State) (t : ℕ) (extra : List ℕ),
      Exec w (forList a_st a_en a_ent r_u r_k r_hi r_v
        (visitVertexProg a_allow a_rch a_que r_v r_tail r_tmp)) s s' t ∧
      t ≤ 9 + (lists u).length * 33 ∧
      RState G W srcs a_rch a_que r_tail (items ++ extra) s' ∧
      (∀ v : Fin N, G.Adj u v → v ∈ W → v.1 ∈ items ++ extra) ∧
      (∀ a, a ≠ a_rch → a ≠ a_que → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_tail → r ≠ r_tmp → s'.regs r = s.regs r) := by
  let I : ℕ → State → Prop := fun j st' =>
    st'.regs r_u = u.1 ∧
    (∀ a, a ≠ a_rch → a ≠ a_que → st'.arrs a = s.arrs a) ∧
    (∀ r, r ≠ r_k → r ≠ r_hi → r ≠ r_v → r ≠ r_tail → r ≠ r_tmp → st'.regs r = s.regs r) ∧
    ∃ extra : List ℕ,
      RState G W srcs a_rch a_que r_tail (items ++ extra) st' ∧
      (∀ v : Fin N, v.1 ∈ (lists u).take j → v ∈ W → v.1 ∈ items ++ extra)
  have hI0 : I 0 ((s.setReg r_k st).setReg r_hi en) := by
    refine ⟨?_, fun _ _ _ => rfl, fun r h1 h2 _ _ _ => by simp [h1, h2],
      [], ?_, by simp⟩
    · simp [huh, hku, hru]
    · simp only [List.append_nil]
      exact hst0.of_arrs_regs_eq (s' := (s.setReg r_k st).setReg r_hi en) rfl rfl
        (by simp [hkt.symm, hht.symm])
  have hl_w : ∀ x ∈ lists u, x < 2 ^ w :=
    fun x hx => lt_trans ((hlists u).1 x hx) hN
  obtain ⟨s', t, hex, ht, hI⟩ := forList_exec a_st a_en a_ent r_u r_k r_hi r_v
    (visitVertexProg a_allow a_rch a_que r_v r_tail r_tmp) u.1 st en (lists u) I 23
    hku hkh hw hen (lt_trans u.2 hN) hlist hru hI0
    (fun j hj st' h => by
      have hent_eq := h.2.1 a_ent hent_rch hent_que
      obtain ⟨_, _, hen_ent, hdiff, _, _, _, helem⟩ := hlist
      rw [hent_eq]
      exact ⟨by omega, helem j hj⟩)
    hl_w
    (fun j hj st' h hrk hrh => by
      obtain ⟨hru₁, ha₁, hr₁, extra, hst₁, hcl₁⟩ := h
      have hvn : (lists u)[j] < N := (hlists u).1 _ (List.getElem_mem hj)
      set v : Fin N := ⟨(lists u)[j], hvn⟩
      have hadj : G.Adj u v := ((hlists u).2.2.2 v).mp (List.getElem_mem hj)
      have hallow₁ : (st'.setReg r_v (lists u)[j]).arrs a_allow =
          List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0) := by
        simp [ha₁ a_allow haar haaq, hallow]
      have hst₁' : RState G W srcs a_rch a_que r_tail (items ++ extra)
          (st'.setReg r_v (lists u)[j]) :=
        hst₁.of_arrs_regs_eq rfl rfl (by simp [hvt.symm])
      obtain ⟨s₂, t₂, extra₂, hex₂, ht₂, hst₂, hv_mem, ha₂, hr₂⟩ :=
        visitVertexProg_exec a_allow a_rch a_que r_v r_tail r_tmp haar haaq hrq hvt hvtmp httmp
          hw hN v hst₁' hallow₁ (by simp [v])
          (fun hvW => mem_reachSet_of_adj hu_reach hadj hvW)
      have hrk₂ : s₂.regs r_k = st + j := by
        rw [hr₂ r_k hkt hktmp]; simp [hvk.symm, hrk]
      have hrh₂ : s₂.regs r_hi = en := by
        rw [hr₂ r_hi hht hhtmp]; simp [hvh.symm, hrh]
      refine ⟨s₂, t₂, hex₂, ht₂, hrk₂, hrh₂, ?_⟩
      refine ⟨?_, ?_, ?_, extra ++ extra₂, ?_, ?_⟩
      · simp only [State.setReg_regs, hku, ite_false]
        rw [hr₂ r_u hut hutmp]
        simp [hvu.symm, hru₁]
      · intro a h1 h2
        simp only [State.setReg_arrs]
        rw [ha₂ a h1 h2]; exact ha₁ a h1 h2
      · intro r h1 h2 h3 h4 h5
        simp only [State.setReg_regs, h1, ite_false]
        rw [hr₂ r h4 h5]
        simp [h3, hr₁ r h1 h2 h3 h4 h5]
      · rw [← List.append_assoc]
        exact hst₂.of_arrs_regs_eq rfl rfl (by simp [hkt.symm])
      · intro y hy hyW
        rw [← List.append_assoc]
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
          List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | hy_eq
        · exact List.mem_append_left _ (hcl₁ y hy hyW)
        · have hyv : y = v := Fin.ext hy_eq
          subst hyv
          exact hv_mem hyW)
  obtain ⟨_, ha', hr', extra, hst', hcl'⟩ := hI
  rw [List.take_length] at hcl'
  refine ⟨s', t, extra, hex, ht, hst', ?_, ha', hr'⟩
  intro v hadj hvW
  exact hcl' v (((hlists u).2.2.2 v).mpr hadj) hvW

/-! ### Full BFS search program (`reachSearchProg`) -/

/-- One round of the BFS queue loop: pop `u = a_que[r_head]` and scan its adjacency list. -/
def reachStepProg (a : InstArrs) (a_allow a_rch a_que : Arr)
    (r_head r_tail r_u r_k r_hi r_v r_tmp : Reg) : Cmd :=
  .seq (.assign r_u (.read a_que (.reg r_head)))
    (.seq (.assign r_head (.op .add (.reg r_head) (.const 1)))
      (forList a.st a.en a.ent r_u r_k r_hi r_v
        (visitVertexProg a_allow a_rch a_que r_v r_tail r_tmp)))

/-- The BFS queue loop. -/
def reachLoopProg (a : InstArrs) (a_allow a_rch a_que : Arr)
    (r_head r_tail r_u r_k r_hi r_v r_tmp : Reg) : Cmd :=
  .while (.op .lt (.reg r_head) (.reg r_tail))
    (reachStepProg a a_allow a_rch a_que r_head r_tail r_u r_k r_hi r_v r_tmp)

/-- Full BFS reachability search on `(G, S, D)` at `a`:
reads `a_allow` (`1` on `W`, `0` elsewhere) and `a_src` (`srcs`), allocates `a_rch`, `a_que`, and
`a_out`, and writes the indicator of `ReachSet G W srcs` into `a_rch` and a duplicate-free list of
`ReachSet G W srcs` into `a_out`. Uses registers `r_base .. r_base + 7`. -/
def reachSearchProg (a : InstArrs) (a_allow a_src a_rch a_out a_que : Arr) (r_base : Reg) : Cmd :=
  let r_N := r_base
  let r_head := r_base + 1
  let r_tail := r_base + 2
  let r_u := r_base + 3
  let r_k := r_base + 4
  let r_hi := r_base + 5
  let r_v := r_base + 6
  let r_tmp := r_base + 7
  .seq (.assign r_N (.len a_allow))
    (.seq (.alloc a_rch (.reg r_N))
      (.seq (.alloc a_que (.reg r_N))
        (.seq (.assign r_head (.const 0))
          (.seq (.assign r_tail (.const 0))
            (.seq (reachInitSrcProg a_src a_allow a_rch a_que r_u r_hi r_v r_tail r_tmp)
              (.seq (reachLoopProg a a_allow a_rch a_que r_head r_tail r_u r_k r_hi r_v r_tmp)
                (copyMinNProg a_que a_out r_N r_u r_tail)))))))

theorem take_append_replicate_of_le {α : Type*} (l : List α) (k h : ℕ) (x : α) (hh : h ≤ l.length) :
    (l ++ List.replicate k x).take h = l.take h := by
  rw [List.take_append_of_le_length hh]

/-- Execution of `reachSearchProg`. -/
theorem reachSearchProg_exec {w N : ℕ} (a : InstArrs)
    (a_allow a_src a_rch a_out a_que r_base : ℕ)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {W : Set (Fin N)} {srcs : List (Fin N)} {s : State}
    (hinst : IsInstanceAt a G S D s)
    (hallow : s.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0))
    (hsrc_arr : s.arrs a_src = srcs.map Fin.val)
    (hsrc_len : srcs.length ≤ N + 1)
    (hd_rch : a_rch ∉ a.list ∧ a_rch ≠ a_allow ∧ a_rch ≠ a_src ∧ a_rch ≠ a_out ∧ a_rch ≠ a_que)
    (hd_que : a_que ∉ a.list ∧ a_que ≠ a_allow ∧ a_que ≠ a_src ∧ a_que ≠ a_out)
    (hd_out : a_out ∉ a.list ∧ a_out ≠ a_allow ∧ a_out ≠ a_src ∧ a_out ≠ a_rch)
    (hw : 4 * instSize N G + 4 < 2 ^ w) :
    ∃ s' t, Exec w (reachSearchProg a a_allow a_src a_rch a_out a_que r_base) s s' t ∧
      t ≤ 180 * instSize N G ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ x, x ≠ a_rch → x ≠ a_out → x ≠ a_que → s'.arrs x = s.arrs x) ∧
      s'.arrs a_rch = List.ofFn (fun x : Fin N => if x ∈ ReachSet G W srcs then 1 else 0) ∧
      IsSetListAt a_out (ReachSet G W srcs) s' := by
  classical
  obtain ⟨hsupp, halive, ⟨lists, hadj⟩, hentlen, hcyc⟩ := hinst
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  have hsrc_w : srcs.length < 2 ^ w := by omega
  let r_N : ℕ := r_base
  let r_head : ℕ := r_base + 1
  let r_tail : ℕ := r_base + 2
  let r_u : ℕ := r_base + 3
  let r_k : ℕ := r_base + 4
  let r_hi : ℕ := r_base + 5
  let r_v : ℕ := r_base + 6
  let r_tmp : ℕ := r_base + 7
  have hal_len : (s.arrs a_allow).length = N := by rw [hallow, List.length_ofFn]
  -- Step 1: r_N := len a_allow
  set s₁ := s.setReg r_N N
  have hex₁ : Exec w (.assign r_N (.len a_allow)) s s₁ 2 :=
    .assign (by rw [ ← hal_len]; exact eval_len rfl (by rw [hal_len]; exact hNw))
  -- Step 2: alloc a_rch r_N
  set s₂ := s₁.setArr a_rch (List.replicate N 0)
  have hex₂ : Exec w (.alloc a_rch (.reg r_N)) s₁ s₂ (1 + N) :=
    .alloc (eval_reg (by simp [s₁]) hNw)
  -- Step 3: alloc a_que r_N
  set s₃ := s₂.setArr a_que (List.replicate N 0)
  have hex₃ : Exec w (.alloc a_que (.reg r_N)) s₂ s₃ (1 + N) :=
    .alloc (eval_reg (by simp [s₂, s₁]) hNw)
  -- Step 4: r_head := 0
  set s₄ := s₃.setReg r_head 0
  have hex₄ : Exec w (.assign r_head (.const 0)) s₃ s₄ 2 := .assign (eval_const h0w)
  -- Step 5: r_tail := 0
  set s₅ := s₄.setReg r_tail 0
  have hex₅ : Exec w (.assign r_tail (.const 0)) s₄ s₅ 2 := .assign (eval_const h0w)
  -- Initial RState at s₅
  have hst₅ : RState G W srcs a_rch a_que r_tail [] s₅ := by
    refine ⟨List.nodup_nil, by simp, by simp, ?_, ?_⟩
    · simp [s₅, s₄, s₃, s₂, State.setArr_arrs_ne _ _ hd_rch.2.2.2.2]
    · refine ⟨by simp [s₅, s₄, s₃], by simp [s₅]⟩
  have hsrc₅ : s₅.arrs a_src = srcs.map Fin.val := by
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ hd_que.2.2.1.symm,
      State.setArr_arrs_ne _ _ hd_rch.2.2.1.symm, hsrc_arr]
  have hallow₅ : s₅.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0) := by
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ hd_que.2.1.symm,
      State.setArr_arrs_ne _ _ hd_rch.2.1.symm, hallow]
  -- Step 6: reachInitSrcProg
  obtain ⟨s₆, t₆, items₀, hex₆, ht₆, hst₆, hsrcs₆, ha₆, hr₆⟩ :=
    reachInitSrcProg_exec a_src a_allow a_rch a_que r_u r_hi r_v r_tail r_tmp
      hd_rch.2.2.1.symm hd_que.2.2.1.symm hd_rch.2.1.symm hd_que.2.1.symm hd_rch.2.2.2.2
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hw1 hNw hsrc₅ hsrc_w hallow₅ hst₅
  -- Step 7: reachLoopProg via while_exec
  let LInv : State → Prop := fun st =>
    st.regs r_N = N ∧
    (∀ r < r_base, st.regs r = s.regs r) ∧
    (∀ x, x ≠ a_rch → x ≠ a_que → st.arrs x = s.arrs x) ∧
    ∃ items : List ℕ, ∃ h : ℕ,
      h ≤ items.length ∧
      st.regs r_head = h ∧
      RState G W srcs a_rch a_que r_tail items st ∧
      (∀ u ∈ srcs, u ∈ W → u.1 ∈ items) ∧
      (∀ u : Fin N, u.1 ∈ items.take h → ∀ v : Fin N, G.Adj u v → v ∈ W → v.1 ∈ items)
  have hLInv₆ : LInv s₆ := by
    refine ⟨?_, ?_, ?_, items₀, 0, Nat.zero_le _, ?_, hst₆, hsrcs₆, by simp⟩
    · rw [hr₆ r_N (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₅, s₄, s₃, s₂, s₁, r_N, r_head, r_tail]
    · intro r hr
      rw [hr₆ r (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₅, s₄, s₃, s₂, s₁, r_N, r_head, r_tail,
        show r ≠ r_base by omega, show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]
    · intro x hx1 hx2
      rw [ha₆ x hx1 hx2]
      simp [s₅, s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ hx1, State.setArr_arrs_ne _ _ hx2]
    · rw [hr₆ r_head (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₅, s₄, r_head, r_tail]
  let μ : State → ℕ := fun st => N - st.regs r_head
  let Φ : State → ℕ := fun st =>
    33 * (((st.arrs a_que).take (st.regs r_head)).map (fun x => (listOf lists x).length)).sum
  have hcond_eval : ∀ st, LInv st →
      (Expr.op .lt (.reg r_head) (.reg r_tail)).eval w st =
        some (if st.regs r_head < st.regs r_tail then 1 else 0) := by
    intro st ⟨_, _, _, items, h, hle, hrh, hst, _, _⟩
    have hlen_le : items.length ≤ N := hst.length_le
    have hhw : st.regs r_head < 2 ^ w := by omega
    have htw : st.regs r_tail < 2 ^ w := by rw [hst.que_buf.2]; omega
    exact eval_lt (eval_reg rfl hhw) (eval_reg rfl htw) hw1
  obtain ⟨s₇, t₇, hex₇, ht₇, hLInv₇, hcond₇⟩ :=
    while_exec LInv μ Φ 16 (cond := .op .lt (.reg r_head) (.reg r_tail))
      (body := reachStepProg a a_allow a_rch a_que r_head r_tail r_u r_k r_hi r_v r_tmp)
      (fun st hst => ⟨_, hcond_eval st hst⟩)
      (fun st hst hne0 => by
        rw [hcond_eval st hst] at hne0
        obtain ⟨hrN, hregs, harrs, items, h, hle, hrh, hR, hsrcs, hcl⟩ := hst
        have hlt_tail : h < items.length := by
          rw [hrh, hR.que_buf.2] at hne0
          by_contra hge
          have : ¬ (h < items.length) := hge
          simp [this] at hne0
        have hlen_le : items.length ≤ N := hR.length_le
        have hhw : h < 2 ^ w := by omega
        have hhw1 : h + 1 < 2 ^ w := by omega
        have hun : items[h] < N := hR.lt _ (List.getElem_mem hlt_tail)
        set u : Fin N := ⟨items[h], hun⟩
        have hu_mem : u.1 ∈ items := List.getElem_mem hlt_tail
        have hu_reach : u ∈ ReachSet G W srcs := hR.reach u hu_mem
        have hque_len : h < (st.arrs a_que).length := by
          rw [hR.que_buf.1, List.length_append]; omega
        have hque_val : (st.arrs a_que)[h]'hque_len = u.1 := by
          simp only [hR.que_buf.1, u]
          exact List.getElem_append_left hlt_tail
        have hrd_u : (Expr.read a_que (.reg r_head)).eval w st = some u.1 := by
          have := eval_read (a := a_que) (eval_reg hrh hhw) hque_len
            (by rw [hque_val]; exact lt_trans u.2 hNw)
          rwa [hque_val] at this
        set st₁ := st.setReg r_u u.1
        have hex_u : Exec w (.assign r_u (.read a_que (.reg r_head))) st st₁ 3 := .assign hrd_u
        have hinc_h : (Expr.op .add (.reg r_head) (.const 1)).eval w st₁ = some (h + 1) :=
          eval_add (eval_reg (by simp [st₁, r_head, r_u, hrh]) hhw) (eval_const hw1) hhw1
        set st₂ := st₁.setReg r_head (h + 1)
        have hex_h : Exec w (.assign r_head (.op .add (.reg r_head) (.const 1))) st₁ st₂ 4 :=
          .assign hinc_h
        -- adjacency list of u in st₂
        have hadj_st₂ : IsAdjList G a.st a.en a.ent lists st₂ := by
          apply hadj.of_arrs_eq
          · exact harrs a.st (fun e => hd_rch.1 (by simp [InstArrs.list, e]))
              (fun e => hd_que.1 (by simp [InstArrs.list, e]))
          · exact harrs a.en (fun e => hd_rch.1 (by simp [InstArrs.list, e]))
              (fun e => hd_que.1 (by simp [InstArrs.list, e]))
          · exact harrs a.ent (fun e => hd_rch.1 (by simp [InstArrs.list, e]))
              (fun e => hd_que.1 (by simp [InstArrs.list, e]))
        obtain ⟨st_u, en_u, hlist_u⟩ := hadj_st₂.1.2.2 u
        have hen_ent : en_u ≤ (st₂.arrs a.ent).length := hlist_u.2.2.1
        have hent_len₂ : (st₂.arrs a.ent).length = 2 * G.edgeSet.ncard := by
          simp [st₂, st₁, harrs a.ent (fun e => hd_rch.1 (by simp [InstArrs.list, e]))
            (fun e => hd_que.1 (by simp [InstArrs.list, e])), hentlen]
        have hen_w : en_u < 2 ^ w := by omega
        have hallow₂ : st₂.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ W then 1 else 0) := by
          simp [st₂, st₁, harrs a_allow hd_rch.2.1.symm hd_que.2.1.symm, hallow]
        have hR₂ : RState G W srcs a_rch a_que r_tail items st₂ :=
          hR.of_arrs_regs_eq rfl rfl (by simp [st₂, st₁, r_tail, r_head, r_u])
        have hent_rch : a.ent ≠ a_rch := fun e => hd_rch.1 (by simp [InstArrs.list, e])
        have hent_que : a.ent ≠ a_que := fun e => hd_que.1 (by simp [InstArrs.list, e])
        obtain ⟨st₃, t₃, extra, hex₃, ht₃, hR₃, hcl_u, ha₃, hr₃⟩ :=
          reachVisitAdj_exec hadj.2 a.st a.en a.ent a_allow a_rch a_que
            r_u r_k r_hi r_v r_tail r_tmp hent_rch hent_que hd_rch.2.1.symm hd_que.2.1.symm
            hd_rch.2.2.2.2 (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) hw1 hNw u st_u en_u hen_w hlist_u
            (by simp [st₂, st₁, r_u, r_head]) hu_reach hallow₂ hR₂
        have hrh₃ : st₃.regs r_head = h + 1 := by
          rw [hr₃ r_head (by omega) (by omega) (by omega) (by omega) (by omega)]
          simp [st₂]
        have htake_old : (st.arrs a_que).take (st.regs r_head) = items.take h := by
          rw [hrh, hR.que_buf.1, take_append_replicate_of_le items _ h 0 hle]
        have htake_new : (st₃.arrs a_que).take (st₃.regs r_head) = items.take h ++ [u.1] := by
          rw [hrh₃, hR₃.que_buf.1,
            take_append_replicate_of_le (items ++ extra) _ (h + 1) 0
              (by rw [List.length_append]; omega),
            List.take_append_of_le_length (by omega),
            List.take_add_one, List.getElem?_eq_getElem hlt_tail, Option.toList_some]
        have hΦ_eq : Φ st₃ = Φ st + 33 * (lists u).length := by
          simp only [Φ, htake_old, htake_new, List.map_append, List.map_singleton,
            List.sum_append, List.sum_singleton]
          rw [listOf_fin]
          omega
        refine ⟨st₃, 3 + (4 + t₃), .seq hex_u (.seq hex_h hex₃), by omega, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_, items ++ extra, h + 1, by rw [List.length_append]; omega,
            hrh₃, hR₃, fun y hy hyW => List.mem_append_left _ (hsrcs y hy hyW), ?_⟩
          · rw [hr₃ r_N (by omega) (by omega) (by omega) (by omega) (by omega)]
            simp [st₂, st₁, r_N, r_head, r_u, hrN]
          · intro r hr
            rw [hr₃ r (by omega) (by omega) (by omega) (by omega) (by omega)]
            simp [st₂, st₁, r_head, r_u, show r ≠ r_base + 1 by omega,
              show r ≠ r_base + 3 by omega, hregs r hr]
          · intro x hx1 hx2
            rw [ha₃ x hx1 hx2]
            exact harrs x hx1 hx2
          · intro y hy v hadj_yv hvW
            rw [List.take_append_of_le_length (by omega), List.take_add_one,
              List.getElem?_eq_getElem hlt_tail, Option.toList_some,
              List.mem_append, List.mem_singleton] at hy
            rcases hy with hy | hy_eq
            · exact List.mem_append_left _ (hcl y hy v hadj_yv hvW)
            · have hyv : y = u := Fin.ext hy_eq
              subst hyv
              exact hcl_u v hadj_yv hvW
        · simp only [μ, hrh, hrh₃]
          omega)
      s₆ hLInv₆
  rw [hcond_eval s₇ hLInv₇] at hcond₇
  obtain ⟨hrN₇, hregs₇, harrs₇, items, h, hle, hrh₇, hR₇, hsrcs₇, hcl₇⟩ := hLInv₇
  have hh_eq : h = items.length := by
    rw [hrh₇, hR₇.que_buf.2] at hcond₇
    by_contra hne
    have hlt : h < items.length := by omega
    simp [hlt] at hcond₇
  subst hh_eq
  rw [List.take_length] at hcl₇
  have hitems_iff : ∀ x : Fin N, x.1 ∈ items ↔ x ∈ ReachSet G W srcs :=
    reachSet_eq_of_closed hR₇.reach hsrcs₇ hcl₇
  -- Bound Φ s₇
  have hΦ₆ : Φ s₆ = 0 := by
    have hrh₆ : s₆.regs r_head = 0 := by
      rw [hr₆ r_head (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₅, s₄, r_head, r_tail]
    simp [Φ, hrh₆]
  have hΦ₇ : Φ s₇ ≤ 66 * G.edgeSet.ncard := by
    have htake₇ : (s₇.arrs a_que).take (s₇.regs r_head) = items := by
      rw [hrh₇, hR₇.que_buf.1, take_append_replicate_of_le items _ items.length 0 le_rfl,
        List.take_length]
    simp only [Φ, htake₇]
    have hsum1 := sum_map_le_of_nodup (fun x => (listOf lists x).length) hR₇.nodup hR₇.lt
    have hsum2 : ∑ x ∈ Finset.range N, (listOf lists x).length = 2 * G.edgeSet.ncard := by
      have := length_flatUpTo_eq (H := G) (L := listOf lists) (by
        intro x; simpa [listOf_fin] using hadj.2 x)
      rw [← this, length_flatUpTo]
    omega
  have hμ₆ : μ s₆ = N := by
    have hrh₆ : s₆.regs r_head = 0 := by
      rw [hr₆ r_head (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [s₅, s₄, r_head, r_tail]
    simp [μ, hrh₆]
  -- Step 8: copyMinNProg a_que a_out r_N r_u r_tail
  have hlen_items : items.length ≤ N := hR₇.length_le
  have hque_len₇ : items.length ≤ (s₇.arrs a_que).length := by
    rw [hR₇.que_buf.1, List.length_append]; omega
  obtain ⟨s₈, t₈, hex₈, ht₈, hout₈, ha₈, hr₈⟩ :=
    copyMinNProg_exec a_que a_out r_N r_u r_tail hd_que.2.2.2
      (by omega) (by omega) (by omega) hrN₇ hNw hw1 hR₇.que_buf.2
      (by omega) hque_len₇
  refine ⟨s₈, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₇
    rw [hΦ₆, hμ₆] at ht₇
    rw [hsz]
    omega
  · intro r hr
    rw [hr₈ r (by omega)]
    exact hregs₇ r hr
  · intro x hx1 hx2 hx3
    rw [ha₈ x hx2]
    exact harrs₇ x hx1 hx3
  · rw [ha₈ a_rch hd_out.2.2.2.symm, hR₇.rch_arr]
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_ofFn, hitems_iff ⟨i, by simpa using h₁⟩]
  · refine ⟨toFin N items, nodup_toFin hR₇.nodup hR₇.lt, ?_, ?_⟩
    · intro y
      rw [mem_toFin]
      exact hitems_iff y
    · rw [hout₈, hR₇.que_buf.1, take_append_replicate_of_le items _ items.length 0 le_rfl,
        List.take_length, map_val_toFin hR₇.lt]
      exact map_min_of_le (fun x hx => le_of_lt (hR₇.lt x hx))

/-! ### Indicator-array and source-list constructors -/

/-- Allocate a 1-element array `a_v` holding `[s.regs r_v]`. -/
def singleSrcProg (a_v : Arr) (r_v : Reg) : Cmd :=
  .seq (.alloc a_v (.const 1)) (.write a_v (.const 0) (.reg r_v))

theorem singleSrcProg_exec {w N : ℕ} (a_v : Arr) (r_v : Reg) (v : Fin N) {s : State}
    (hrv : s.regs r_v = v.1) (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) :
    ∃ s' t, Exec w (singleSrcProg a_v r_v) s s' t ∧
      t ≤ 5 ∧
      s'.arrs a_v = [v].map Fin.val ∧
      (∀ a, a ≠ a_v → s'.arrs a = s.arrs a) ∧
      s'.regs = s.regs := by
  have h0w : 0 < 2 ^ w := by omega
  have hvw : v.1 < 2 ^ w := lt_trans v.2 hN
  set s₁ := s.setArr a_v [0]
  have hex₁ : Exec w (.alloc a_v (.const 1)) s s₁ 2 := .alloc (eval_const hw)
  have hex₂ : Exec w (.write a_v (.const 0) (.reg r_v)) s₁ (s₁.writeArr a_v 0 v.1) 3 :=
    .write (eval_const h0w) (eval_reg (by simp [s₁, hrv]) hvw) (by simp [s₁])
  refine ⟨s₁.writeArr a_v 0 v.1, 5, .seq hex₁ hex₂, le_rfl, by simp [s₁], ?_, rfl⟩
  intro a ha
  simp [s₁, State.writeArr_arrs_ne _ _ _ ha, State.setArr_arrs_ne _ _ ha]

/-- Build the indicator array `a_allow` for `(S : Set (Fin N)) \ X₀` by copying `a.alive` and
writing `0` at every entry of `a_sep`. Uses registers `r_base .. r_base + 2`. -/
def allowMinusSepProg (a : InstArrs) (a_sep a_allow : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.len a.alive))
    (.seq (copyMinProg a.alive a_allow r_base (r_base + 1) (r_base + 2))
      (writeAllProg a_allow a_sep 0 r_base (r_base + 1) (r_base + 2)))

theorem allowMinusSepProg_exec {w N : ℕ} (a : InstArrs) (a_sep a_allow r_base : ℕ)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {X₀ : Set (Fin N)} {s : State}
    (hinst : IsInstanceAt a G S D s)
    (hsep : IsSetListAt a_sep X₀ s)
    (hd_al : a_allow ≠ a.alive ∧ a_allow ≠ a_sep)
    (hw : 4 * instSize N G + 4 < 2 ^ w) :
    ∃ s' t, Exec w (allowMinusSepProg a a_sep a_allow r_base) s s' t ∧
      t ≤ 35 * instSize N G ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ x, x ≠ a_allow → s'.arrs x = s.arrs x) ∧
      s'.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ (S : Set (Fin N)) \ X₀ then 1 else 0) := by
  classical
  obtain ⟨_, halive, _, _, _⟩ := hinst
  obtain ⟨sep_l, hsep_nd, hsep_mem, hsep_arr⟩ := hsep
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  have hal_len : (s.arrs a.alive).length = N := by rw [halive, List.length_ofFn]
  set s₁ := s.setReg r_base N
  have hex₁ : Exec w (.assign r_base (.len a.alive)) s s₁ 2 :=
    .assign (by rw [← hal_len]; exact eval_len rfl (by rw [hal_len]; exact hNw))
  obtain ⟨s₂, t₂, hex₂, ht₂, hcp₂, ha₂, hr₂⟩ :=
    copyMinProg_exec (s := s₁) a.alive a_allow r_base (r_base + 1) (r_base + 2) hd_al.1.symm
      (by omega) (by omega) (by omega) (by simp [s₁]) hNw hw1
      (by simp [s₁, hal_len, hNw])
  have hal₂ : s₂.arrs a_allow = s.arrs a.alive := by
    rw [hcp₂]; simp only [s₁, State.setReg_arrs]
    apply map_min_of_le
    intro x hx
    rw [halive] at hx
    obtain ⟨v, _, rfl⟩ := List.mem_ofFn.mp hx
    have : 0 < N := v.pos
    split_ifs <;> omega
  have hsep₂ : s₂.arrs a_sep = sep_l.map Fin.val := by
    rw [ha₂ a_sep hd_al.2.symm]; exact hsep_arr
  have hsep_len : sep_l.length ≤ N := by
    rw [← List.toFinset_card_of_nodup hsep_nd]
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hsep_len_w : (s₂.arrs a_sep).length < 2 ^ w := by
    rw [hsep₂, List.length_map]; omega
  have hsep_lt : ∀ y ∈ s₂.arrs a_sep, y < (s₂.arrs a_allow).length := by
    intro y hy
    rw [hsep₂, List.mem_map] at hy
    obtain ⟨v, _, rfl⟩ := hy
    rw [hal₂, hal_len]; exact v.2
  obtain ⟨s₃, t₃, hex₃, ht₃, hwr₃, ha₃, hr₃⟩ :=
    writeAll_exec a_allow a_sep 0 r_base (r_base + 1) (r_base + 2) hd_al.2
      (by omega) (by omega) (by omega) hw1 h0w hsep_len_w hsep_lt
      (by rw [hal₂, hal_len]; exact hNw)
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, ?_, ?_⟩
  · simp only [s₁, State.setReg_arrs, hal_len] at ht₂
    rw [hsep₂, List.length_map] at ht₃
    rw [hsz]; omega
  · intro r hr
    rw [hr₃ r (by omega) (by omega) (by omega), hr₂ r (by omega) (by omega)]
    simp [s₁, show r ≠ r_base by omega]
  · intro x hx
    rw [ha₃ x hx, ha₂ x hx]; rfl
  · rw [hwr₃, hal₂, hsep₂, halive]
    apply List.ext_getElem (by simp [setAt])
    intro i h₁ h₂
    simp only [setAt, List.getElem_map, List.getElem_range, List.mem_map, List.getElem_ofFn]
    have hiN : i < N := by simpa using h₂
    set v : Fin N := ⟨i, hiN⟩
    have hmem_map : (∃ a ∈ sep_l, a.val = i) ↔ v ∈ X₀ := by
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact (hsep_mem a).mp ha
      · intro hv
        exact ⟨v, (hsep_mem v).mpr hv, rfl⟩
    have hgetD : (List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0)).getD i 0 =
        if v ∈ S then 1 else 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hiN])]
      simp [v]
    rw [hgetD]
    by_cases hvX : v ∈ X₀
    · have hex : ∃ a ∈ sep_l, a.val = i := hmem_map.mpr hvX
      simp [hex, hvX]
    · have hnex : ¬ ∃ a ∈ sep_l, a.val = i := fun h => hvX (hmem_map.mp h)
      simp [hnex, hvX]

/-- Build the indicator array `a_allow` for a vertex list `U_l` stored in `a_list` by allocating
`N = len a.alive` zeros and writing `1` at every entry of `a_list`. Uses registers
`r_base .. r_base + 2`. -/
def allowFromListProg (a : InstArrs) (a_list a_allow : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.len a.alive))
    (.seq (.alloc a_allow (.reg r_base))
      (writeAllProg a_allow a_list 1 r_base (r_base + 1) (r_base + 2)))

theorem allowFromListProg_exec {w N : ℕ} (a : InstArrs) (a_list a_allow r_base : ℕ)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {U_l : List (Fin N)} {s : State}
    (hinst : IsInstanceAt a G S D s)
    (hlist_arr : s.arrs a_list = U_l.map Fin.val)
    (hlist_len : U_l.length ≤ N)
    (hd_al : a_allow ≠ a_list)
    (hw : 4 * instSize N G + 4 < 2 ^ w) :
    ∃ s' t, Exec w (allowFromListProg a a_list a_allow r_base) s s' t ∧
      t ≤ 20 * instSize N G ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ x, x ≠ a_allow → s'.arrs x = s.arrs x) ∧
      s'.arrs a_allow = List.ofFn (fun x : Fin N => if x ∈ U_l then 1 else 0) := by
  classical
  obtain ⟨_, halive, _, _, _⟩ := hinst
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  have hal_len : (s.arrs a.alive).length = N := by rw [halive, List.length_ofFn]
  set s₁ := s.setReg r_base N
  have hex₁ : Exec w (.assign r_base (.len a.alive)) s s₁ 2 :=
    .assign (by rw [← hal_len]; exact eval_len rfl (by rw [hal_len]; exact hNw))
  set s₂ := s₁.setArr a_allow (List.replicate N 0)
  have hex₂ : Exec w (.alloc a_allow (.reg r_base)) s₁ s₂ (1 + N) :=
    .alloc (eval_reg (by simp [s₁]) hNw)
  have hlist₂ : s₂.arrs a_list = U_l.map Fin.val := by
    simp [s₂, s₁, State.setArr_arrs_ne _ _ hd_al.symm, hlist_arr]
  have hlen_w : (s₂.arrs a_list).length < 2 ^ w := by
    rw [hlist₂, List.length_map]; omega
  have hlt₂ : ∀ y ∈ s₂.arrs a_list, y < (s₂.arrs a_allow).length := by
    intro y hy
    rw [hlist₂, List.mem_map] at hy
    obtain ⟨v, _, rfl⟩ := hy
    simp [s₂, v.2]
  obtain ⟨s₃, t₃, hex₃, ht₃, hwr₃, ha₃, hr₃⟩ :=
    writeAll_exec a_allow a_list 1 r_base (r_base + 1) (r_base + 2) hd_al
      (by omega) (by omega) (by omega) hw1 hw1 hlen_w hlt₂ (by simp [s₂, hNw])
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, ?_, ?_⟩
  · rw [hlist₂, List.length_map] at ht₃
    rw [hsz]; omega
  · intro r hr
    rw [hr₃ r (by omega) (by omega) (by omega)]
    simp [s₂, s₁, show r ≠ r_base by omega]
  · intro x hx
    rw [ha₃ x hx]
    simp [s₂, s₁, State.setArr_arrs_ne _ _ hx]
  · rw [hwr₃, hlist₂]
    simp only [s₂, State.setArr_arrs_self]
    apply List.ext_getElem (by simp [setAt])
    intro i h₁ h₂
    simp only [setAt, List.getElem_map, List.getElem_range, List.mem_map, List.getElem_ofFn,
      List.length_replicate]
    have hiN : i < N := by simpa using h₂
    set v : Fin N := ⟨i, hiN⟩
    have hmem_map : (∃ a ∈ U_l, a.val = i) ↔ v ∈ U_l := by
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro hv; exact ⟨v, hv, rfl⟩
    have hgetD : (List.replicate N 0).getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp [hiN]
    rw [hgetD]
    by_cases hvU : v ∈ U_l
    · have hex : ∃ a ∈ U_l, a.val = i := hmem_map.mpr hvU
      simp [hex, hvU]
    · have hnex : ¬ ∃ a ∈ U_l, a.val = i := fun h => hvU (hmem_map.mp h)
      simp [hnex, hvU]

/-! ### Filtering a separator `a_sep` to the boundary `nbhd G A` -/

/-- Check if a single neighbour `r_u` of `r_y` is in `a_rch`, setting `r_hit := 1` if so. -/
def checkNbrInRchProg (a_rch : Arr) (r_u r_tmp r_hit : Reg) : Cmd :=
  .seq (.assign r_tmp (.read a_rch (.reg r_u)))
    (.ite (.op .eq (.reg r_tmp) (.const 1))
      (.assign r_hit (.const 1))
      .skip)

/-- For a separator vertex `r_y`, scan its adjacency list in `G`; if any neighbour is in `a_rch`,
emit `r_y` into `(a_buf, r_cnt)`. -/
def filterSepBodyProg (a : InstArrs) (a_rch a_buf : Arr)
    (r_y r_k r_hi r_u r_tmp r_hit r_cnt : Reg) : Cmd :=
  .seq (.assign r_hit (.const 0))
    (.seq (forList a.st a.en a.ent r_y r_k r_hi r_u
        (checkNbrInRchProg a_rch r_u r_tmp r_hit))
      (.ite (.op .eq (.reg r_hit) (.const 1))
        (emitProg a_buf r_cnt (.reg r_y))
        .skip))

/-- Filter `a_sep` (`X₀`) to those vertices with a `G`-neighbour in `A` (`a_rch`), writing the
resulting duplicate-free boundary list into `a_bd`. Uses scratch array `a_buf` and registers
`r_base .. r_base + 8`. -/
def filterSepToBdProg (a : InstArrs) (a_sep a_rch a_bd a_buf : Arr) (r_base : Reg) : Cmd :=
  let r_N := r_base
  let r_cnt := r_base + 1
  let r_i := r_base + 2
  let r_n := r_base + 3
  let r_y := r_base + 4
  let r_k := r_base + 5
  let r_hi := r_base + 6
  let r_u := r_base + 7
  let r_tmp := r_base + 8
  let r_hit := r_base + 9
  .seq (.assign r_N (.len a.alive))
    (.seq (.alloc a_buf (.reg r_N))
      (.seq (.assign r_cnt (.const 0))
        (.seq (forArrProg a_sep r_i r_n r_y
            (filterSepBodyProg a a_rch a_buf r_y r_k r_hi r_u r_tmp r_hit r_cnt))
          (copyMinNProg a_buf a_bd r_N r_i r_cnt))))

theorem filterSepBodyProg_exec {w N : ℕ} (a : InstArrs)
    (a_rch a_buf r_y r_k r_hi r_u r_tmp r_hit r_cnt : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} (hlists : IsAdjListFamily G lists)
    {A : Set (Fin N)} (y : Fin N) (st en : ℕ) (hen : en < 2 ^ w)
    (hky : r_y ≠ r_k) (hkh : r_k ≠ r_hi)
    (huk : r_u ≠ r_k) (huh : r_u ≠ r_hi)
    (htmp_k : r_tmp ≠ r_k) (htmp_h : r_tmp ≠ r_hi)
    (hhit_k : r_hit ≠ r_k) (hhit_h : r_hit ≠ r_hi)
    (hhit_u : r_hit ≠ r_u) (hhit_tmp : r_hit ≠ r_tmp)
    (hy_tmp : r_y ≠ r_tmp) (hy_hit : r_y ≠ r_hit) (hy_u : r_y ≠ r_u)
    (hy_h : r_y ≠ r_hi) (_hy_c : r_y ≠ r_cnt)
    (hc_k : r_cnt ≠ r_k) (hc_h : r_cnt ≠ r_hi) (hc_u : r_cnt ≠ r_u)
    (hc_tmp : r_cnt ≠ r_tmp) (hc_hit : r_cnt ≠ r_hit)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    {pre : List ℕ} {k : ℕ} {s : State}
    (hlist : IsListAt a.st a.en a.ent y.1 st en (lists y) s)
    (hry : s.regs r_y = y.1)
    (hrch : s.arrs a_rch = List.ofFn (fun x : Fin N => if x ∈ A then 1 else 0))
    (hbuf : IsBuf a_buf r_cnt pre (k + 1) s)
    (hpre_w : pre.length + 1 < 2 ^ w) :
    let g_y : List ℕ := if ∃ u ∈ A, G.Adj y u then [y.1] else []
    ∃ s' t, Exec w (filterSepBodyProg a a_rch a_buf r_y r_k r_hi r_u r_tmp r_hit r_cnt) s s' t ∧
      t ≤ 21 + (lists y).length * 19 ∧
      IsBuf a_buf r_cnt (pre ++ g_y) (k + 1 - g_y.length) s' ∧
      (∀ x, x ≠ a_buf → s'.arrs x = s.arrs x) ∧
      (∀ r, r ≠ r_k → r ≠ r_hi → r ≠ r_u → r ≠ r_tmp → r ≠ r_hit → r ≠ r_cnt →
        s'.regs r = s.regs r) := by
  classical
  intro g_y
  have h0w : 0 < 2 ^ w := by omega
  have hyw : y.1 < 2 ^ w := lt_trans y.2 hN
  set s₁ := s.setReg r_hit 0
  have hex₁ : Exec w (.assign r_hit (.const 0)) s s₁ 2 := .assign (eval_const h0w)
  let I : ℕ → State → Prop := fun j st' =>
    st'.arrs = s.arrs ∧
    (∀ r, r ≠ r_k → r ≠ r_hi → r ≠ r_u → r ≠ r_tmp → r ≠ r_hit → st'.regs r = s.regs r) ∧
    st'.regs r_hit = (if ∃ u : Fin N, u.1 ∈ (lists y).take j ∧ u ∈ A then 1 else 0)
  have hI0 : I 0 ((s₁.setReg r_k st).setReg r_hi en) := by
    refine ⟨rfl, fun r h1 h2 _ _ h5 => by simp [s₁, h1, h2, h5], ?_⟩
    simp [s₁, hhit_k, hhit_h]
  have hl_w : ∀ x ∈ lists y, x < 2 ^ w := fun x hx => lt_trans ((hlists y).1 x hx) hN
  have hlist₁ : IsListAt a.st a.en a.ent y.1 st en (lists y) s₁ :=
    hlist.of_arrs_eq rfl rfl rfl
  obtain ⟨s₂, t₂, hex₂, ht₂, hI₂⟩ := forList_exec a.st a.en a.ent r_y r_k r_hi r_u
    (checkNbrInRchProg a_rch r_u r_tmp r_hit) y.1 st en (lists y) I 9
    hky hkh hw hen hyw hlist₁ (by simp [s₁, hy_hit, hry]) hI0
    (fun j hj st' h => by
      obtain ⟨_, _, _, _, _, _, _, helem⟩ := hlist
      rw [h.1]
      exact ⟨by omega, helem j hj⟩)
    hl_w
    (fun j hj st' h hrk hrh => by
      obtain ⟨harr, hreg, hhit_val⟩ := h
      have hun : (lists y)[j] < N := (hlists y).1 _ (List.getElem_mem hj)
      set u : Fin N := ⟨(lists y)[j], hun⟩
      have huw : u.1 < 2 ^ w := lt_trans u.2 hN
      set st_u := st'.setReg r_u u.1
      set rv_u : ℕ := if u ∈ A then 1 else 0
      have hrv_w : rv_u < 2 ^ w := by simp only [rv_u]; split_ifs <;> omega
      have hrch_len : u.1 < (st_u.arrs a_rch).length := by simp [st_u, harr, hrch]
      have hrch_val : (st_u.arrs a_rch)[u.1]'hrch_len = rv_u := by simp [st_u, harr, hrch, rv_u]
      have hrd_u : (Expr.read a_rch (.reg r_u)).eval w st_u = some rv_u := by
        have := eval_read (a := a_rch) (eval_reg (r := r_u) (by simp [st_u]) huw) hrch_len
          (by rw [hrch_val]; exact hrv_w)
        rwa [hrch_val] at this
      set st_t := st_u.setReg r_tmp rv_u
      have hex_rd : Exec w (.assign r_tmp (.read a_rch (.reg r_u))) st_u st_t 3 := .assign hrd_u
      have htake_j1 : (∃ u' : Fin N, u'.1 ∈ (lists y).take (j + 1) ∧ u' ∈ A) ↔
          (∃ u' : Fin N, u'.1 ∈ (lists y).take j ∧ u' ∈ A) ∨ u ∈ A := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
        constructor
        · rintro ⟨u', hu', hu'A⟩
          rcases List.mem_append.mp hu' with hu' | hu'_eq
          · exact Or.inl ⟨u', hu', hu'A⟩
          · simp only [List.mem_singleton] at hu'_eq
            have : u' = u := Fin.ext hu'_eq
            subst this; exact Or.inr hu'A
        · rintro (⟨u', hu', hu'A⟩ | huA)
          · exact ⟨u', List.mem_append_left _ hu', hu'A⟩
          · exact ⟨u, List.mem_append_right _ (List.mem_singleton.mpr rfl), huA⟩
      by_cases huA : u ∈ A
      · have hrv1 : rv_u = 1 := by simp [rv_u, huA]
        have hcond : (Expr.op .eq (.reg r_tmp) (.const 1)).eval w st_t = some 1 := by
          have := eval_eq (s := st_t) (eval_reg (r := r_tmp) (by simp [st_t, hrv1]) hw)
            (eval_const hw) hw
          simpa using this
        set st_h := st_t.setReg r_hit 1
        have hex_ite : Exec w (.ite (.op .eq (.reg r_tmp) (.const 1))
            (.assign r_hit (.const 1)) .skip) st_t st_h 5 :=
          .ite_true hcond one_ne_zero (.assign (eval_const hw))
        refine ⟨st_h, 8, .seq hex_rd hex_ite, by omega,
          by simp [st_h, st_t, st_u, hhit_k.symm, htmp_k.symm, huk.symm, hrk],
          by simp [st_h, st_t, st_u, hhit_h.symm, htmp_h.symm, huh.symm, hrh],
          harr, ?_, ?_⟩
        · intro r h1 h2 h3 h4 h5
          simp [st_h, st_t, st_u, h1, h3, h4, h5, hreg r h1 h2 h3 h4 h5]
        · simp [st_h, hhit_k, htake_j1, huA]
      · have hrv0 : rv_u = 0 := by simp [rv_u, huA]
        have hcond : (Expr.op .eq (.reg r_tmp) (.const 1)).eval w st_t = some 0 := by
          have := eval_eq (s := st_t) (eval_reg (r := r_tmp) (by simp [st_t, hrv0]) h0w)
            (eval_const hw) hw
          simpa using this
        have hex_ite : Exec w (.ite (.op .eq (.reg r_tmp) (.const 1))
            (.assign r_hit (.const 1)) .skip) st_t st_t 4 := .ite_false hcond (.skip st_t)
        refine ⟨st_t, 7, .seq hex_rd hex_ite, by omega,
          by simp [st_t, st_u, htmp_k.symm, huk.symm, hrk],
          by simp [st_t, st_u, htmp_h.symm, huh.symm, hrh],
          harr, ?_, ?_⟩
        · intro r h1 h2 h3 h4 h5
          simp [st_t, st_u, h1, h3, h4, hreg r h1 h2 h3 h4 h5]
        · have hhit_t : (st_t.setReg r_k (st + j + 1)).regs r_hit = st'.regs r_hit := by
            simp [st_t, st_u, hhit_k, hhit_tmp, hhit_u]
          rw [hhit_t, hhit_val]
          simp [htake_j1, huA])
  obtain ⟨harr₂, hreg₂, hhit₂⟩ := hI₂
  rw [List.take_length] at hhit₂
  have hiff_adj : (∃ u : Fin N, u.1 ∈ lists y ∧ u ∈ A) ↔ (∃ u ∈ A, G.Adj y u) := by
    constructor
    · rintro ⟨u, hu_mem, huA⟩
      exact ⟨u, huA, ((hlists y).2.2.2 u).mp hu_mem⟩
    · rintro ⟨u, huA, hadj⟩
      exact ⟨u, ((hlists y).2.2.2 u).mpr hadj, huA⟩
  have hbuf₂ : IsBuf a_buf r_cnt pre (k + 1) s₂ :=
    ⟨by rw [harr₂]; exact hbuf.1,
      by rw [hreg₂ r_cnt hc_k hc_h hc_u hc_tmp hc_hit]; exact hbuf.2⟩
  have hry₂ : s₂.regs r_y = y.1 := by
    rw [hreg₂ r_y hky hy_h hy_u hy_tmp hy_hit]; exact hry
  by_cases hhit_prop : ∃ u ∈ A, G.Adj y u
  · have hhit_1 : s₂.regs r_hit = 1 := by
      have := hiff_adj.mpr hhit_prop
      simp [hhit₂, this]
    have hcond : (Expr.op .eq (.reg r_hit) (.const 1)).eval w s₂ = some 1 := by
      have := eval_eq (s := s₂) (eval_reg hhit_1 hw) (eval_const hw) hw
      simpa using this
    obtain ⟨s₃, hex_em, hbuf₃, harr₃, hreg₃⟩ :=
      emitReg_exec a_buf r_cnt r_y hbuf₂ hry₂ hyw hpre_w
    have hex_ite : Exec w (.ite (.op .eq (.reg r_hit) (.const 1))
        (emitProg a_buf r_cnt (.reg r_y)) .skip) s₂ s₃ 10 :=
      .ite_true hcond one_ne_zero hex_em
    have hg_eq : g_y = [y.1] := by simp [g_y, hhit_prop]
    refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex_ite), by omega, ?_, ?_, ?_⟩
    · rw [hg_eq]; simpa using hbuf₃
    · intro x hx; rw [harr₃ x hx, harr₂]
    · intro r h1 h2 h3 h4 h5 h6
      rw [hreg₃ r h6, hreg₂ r h1 h2 h3 h4 h5]
  · have hhit_0 : s₂.regs r_hit = 0 := by
      have : ¬ ∃ u : Fin N, u.1 ∈ lists y ∧ u ∈ A := fun h => hhit_prop (hiff_adj.mp h)
      simp [hhit₂, this]
    have hcond : (Expr.op .eq (.reg r_hit) (.const 1)).eval w s₂ = some 0 := by
      have := eval_eq (s := s₂) (eval_reg hhit_0 h0w) (eval_const hw) hw
      simpa using this
    have hex_ite : Exec w (.ite (.op .eq (.reg r_hit) (.const 1))
        (emitProg a_buf r_cnt (.reg r_y)) .skip) s₂ s₂ 4 := .ite_false hcond (.skip s₂)
    have hg_eq : g_y = [] := by simp [g_y, hhit_prop]
    refine ⟨s₂, _, .seq hex₁ (.seq hex₂ hex_ite), by omega, ?_, ?_, ?_⟩
    · rw [hg_eq]; simpa using hbuf₂
    · intro x _; rw [harr₂]
    · intro r h1 h2 h3 h4 h5 _
      exact hreg₂ r h1 h2 h3 h4 h5

/-- Execution of `filterSepToBdProg` producing `IsSetListAt a_bd (nbhd G A) s'`. -/
theorem filterSepToBdProg_exec {w N : ℕ} (a : InstArrs)
    (a_sep a_rch a_bd a_buf r_base : ℕ)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {X₀ : Set (Fin N)} {v : Fin N} {s : State}
    (hinst : IsInstanceAt a G S D s)
    (hsep : IsSetListAt a_sep X₀ s)
    (hrch : s.arrs a_rch = List.ofFn (fun x : Fin N =>
      if x ∈ {y | ReachIn G ((S : Set (Fin N)) \ X₀) v y} then 1 else 0))
    (hd_buf : a_buf ∉ a.list ∧ a_buf ≠ a_sep ∧ a_buf ≠ a_rch ∧ a_buf ≠ a_bd)
    (_hd_bd : a_bd ∉ a.list ∧ a_bd ≠ a_sep ∧ a_bd ≠ a_rch)
    (hw : 4 * instSize N G + 4 < 2 ^ w) :
    let A : Set (Fin N) := {y | ReachIn G ((S : Set (Fin N)) \ X₀) v y}
    ∃ s' t, Exec w (filterSepToBdProg a a_sep a_rch a_bd a_buf r_base) s s' t ∧
      t ≤ 60 * instSize N G ∧
      (∀ r < r_base, s'.regs r = s.regs r) ∧
      (∀ x, x ≠ a_bd → x ≠ a_buf → s'.arrs x = s.arrs x) ∧
      IsSetListAt a_bd (nbhd G A) s' := by
  classical
  intro A
  obtain ⟨hsupp, halive, ⟨lists, hadj⟩, hentlen, _⟩ := hinst
  obtain ⟨sep_l, hsep_nd, hsep_mem, hsep_arr⟩ := hsep
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  have hal_len : (s.arrs a.alive).length = N := by rw [halive, List.length_ofFn]
  let r_N : ℕ := r_base
  let r_cnt : ℕ := r_base + 1
  let r_i : ℕ := r_base + 2
  let r_n : ℕ := r_base + 3
  let r_y : ℕ := r_base + 4
  let r_k : ℕ := r_base + 5
  let r_hi : ℕ := r_base + 6
  let r_u : ℕ := r_base + 7
  let r_tmp : ℕ := r_base + 8
  let r_hit : ℕ := r_base + 9
  -- Step 1: r_N := len a.alive
  set s₁ := s.setReg r_N N
  have hex₁ : Exec w (.assign r_N (.len a.alive)) s s₁ 2 :=
    .assign (by rw [← hal_len]; exact eval_len rfl (by rw [hal_len]; exact hNw))
  -- Step 2: alloc a_buf r_N
  set s₂ := s₁.setArr a_buf (List.replicate N 0)
  have hex₂ : Exec w (.alloc a_buf (.reg r_N)) s₁ s₂ (1 + N) :=
    .alloc (eval_reg (by simp [s₁]) hNw)
  -- Step 3: r_cnt := 0
  set s₃ := s₂.setReg r_cnt 0
  have hex₃ : Exec w (.assign r_cnt (.const 0)) s₂ s₃ 2 := .assign (eval_const h0w)
  -- Step 4: forArrProg over a_sep with potential on scanned degrees
  let g : ℕ → List ℕ := fun x =>
    if hx : x < N then
      if ∃ u ∈ A, G.Adj ⟨x, hx⟩ u then [x] else []
    else []
  let bd_l : List (Fin N) := sep_l.filter (fun y => decide (∃ u ∈ A, G.Adj y u))
  have hflat_take : ∀ j ≤ sep_l.length,
      ((sep_l.map Fin.val).take j).flatMap g =
        ((sep_l.take j).filter (fun y => decide (∃ u ∈ A, G.Adj y u))).map Fin.val := by
    intro j _
    rw [← List.map_take]
    induction sep_l.take j with
    | nil => rfl
    | cons y ys ih =>
      have hgy : g y.1 = if ∃ u ∈ A, G.Adj y u then [y.1] else [] := by simp [g, y.2]
      simp only [List.map_cons, List.flatMap_cons, hgy, List.filter_cons, decide_eq_true_eq]
      split_ifs <;> simp [ih]
  have hsep_len_le : sep_l.length ≤ N := by
    rw [← List.toFinset_card_of_nodup hsep_nd]
    exact le_trans (Finset.card_le_univ _) (by simp)
  have hsep₃ : s₃.arrs a_sep = sep_l.map Fin.val := by
    simp [s₃, s₂, s₁, State.setArr_arrs_ne _ _ hd_buf.2.1.symm, hsep_arr]
  let I : ℕ → State → Prop := fun j st' =>
    st'.regs r_i = j ∧
    st'.regs r_n = sep_l.length ∧
    st'.regs r_N = N ∧
    (∀ r < r_base, st'.regs r = s.regs r) ∧
    (∀ x, x ≠ a_buf → st'.arrs x = s.arrs x) ∧
    IsBuf a_buf r_cnt (((sep_l.map Fin.val).take j).flatMap g)
      (N - (((sep_l.map Fin.val).take j).flatMap g).length) st'
  let Φ : State → ℕ := fun st' =>
    19 * (((sep_l.map Fin.val).take (st'.regs r_i)).map (fun x => (listOf lists x).length)).sum
  have hsep_len_w : sep_l.length < 2 ^ w := by omega
  have hex_n : Exec w (.assign r_n (.len a_sep)) s₃ (s₃.setReg r_n sep_l.length) 2 :=
    .assign (by
      have := eval_len hsep₃ (by rw [List.length_map]; exact hsep_len_w)
      rwa [List.length_map] at this)
  set s₄ := (s₃.setReg r_n sep_l.length).setReg r_i 0
  have hex_i : Exec w (.assign r_i (.const 0)) (s₃.setReg r_n sep_l.length) s₄ 2 :=
    .assign (eval_const h0w)
  have hI0 : I 0 s₄ := by
    refine ⟨by simp [s₄], by simp [s₄, r_i, r_n], by simp [s₄, s₃, s₂, s₁, r_N, r_cnt, r_n, r_i],
      fun r hr => by
        simp [s₄, s₃, s₂, s₁, r_N, r_cnt, r_n, r_i,
          show r ≠ r_base by omega, show r ≠ r_base + 1 by omega,
          show r ≠ r_base + 2 by omega, show r ≠ r_base + 3 by omega],
      fun x hx => by simp [s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ hx],
      by simp [s₄, s₃, s₂], by simp [s₄, s₃, r_cnt, r_n, r_i]⟩
  obtain ⟨s₅, t₅, hex₅, ht₅, hI₅⟩ := forUp_exec I Φ sep_l.length 24 (r_i := r_i) (hi := .reg r_n)
    (body := .seq (.assign r_y (.read a_sep (.reg r_i)))
      (filterSepBodyProg a a_rch a_buf r_y r_k r_hi r_u r_tmp r_hit r_cnt))
    hw1 hsep_len_w
    (fun j _ st' h => ⟨h.1, eval_reg h.2.1 hsep_len_w⟩)
    (fun j hj st' h => by
      obtain ⟨hri, hrn, hrN, hregs, harrs, hbuf⟩ := h
      set y : Fin N := sep_l[j]'hj
      have hsep_st : st'.arrs a_sep = sep_l.map Fin.val := by
        rw [harrs a_sep hd_buf.2.1.symm, hsep_arr]
      have hj_len : j < (st'.arrs a_sep).length := by rw [hsep_st, List.length_map]; exact hj
      have hsep_j : (st'.arrs a_sep)[j]'hj_len = y.1 := by simp [hsep_st, y]
      have hrd_y : (Expr.read a_sep (.reg r_i)).eval w st' = some y.1 := by
        have := eval_read (a := a_sep) (eval_reg (w := w) hri (by omega)) hj_len
          (by rw [hsep_j]; exact lt_trans y.2 hNw)
        rwa [hsep_j] at this
      set st₁ := st'.setReg r_y y.1
      have hex_y : Exec w (.assign r_y (.read a_sep (.reg r_i))) st' st₁ 3 := .assign hrd_y
      have hadj_st₁ : IsAdjList G a.st a.en a.ent lists st₁ := by
        apply hadj.of_arrs_eq
        · exact harrs a.st (fun e => hd_buf.1 (by simp [InstArrs.list, e]))
        · exact harrs a.en (fun e => hd_buf.1 (by simp [InstArrs.list, e]))
        · exact harrs a.ent (fun e => hd_buf.1 (by simp [InstArrs.list, e]))
      obtain ⟨st_y, en_y, hlist_y⟩ := hadj_st₁.1.2.2 y
      have hen_ent : en_y ≤ (st₁.arrs a.ent).length := hlist_y.2.2.1
      have hent_len₁ : (st₁.arrs a.ent).length = 2 * G.edgeSet.ncard := by
        simp [st₁, harrs a.ent (fun e => hd_buf.1 (by simp [InstArrs.list, e])), hentlen]
      have hen_w : en_y < 2 ^ w := by omega
      -- Length of flatMap up to j + 1 is at most j + 1 ≤ N
      have hlen_j1 : (((sep_l.map Fin.val).take (j + 1)).flatMap g).length ≤ j + 1 := by
        rw [hflat_take (j + 1) (by omega), List.length_map]
        exact le_trans (List.length_filter_le _ _) (by simp)
      have hlen_j : (((sep_l.map Fin.val).take j).flatMap g).length ≤ j := by
        rw [hflat_take j (by omega), List.length_map]
        exact le_trans (List.length_filter_le _ _) (by simp)
      have hbuf₁ : IsBuf a_buf r_cnt (((sep_l.map Fin.val).take j).flatMap g)
          ((N - (((sep_l.map Fin.val).take j).flatMap g).length - 1) + 1) st₁ := by
        refine ⟨?_, by simp [st₁, r_cnt, r_y, hbuf.2]⟩
        simp only [st₁, State.setReg_arrs]
        rw [hbuf.1]; congr 2; omega
      have hrch₁ : st₁.arrs a_rch = List.ofFn (fun x : Fin N => if x ∈ A then 1 else 0) := by
        rw [State.setReg_arrs, harrs a_rch hd_buf.2.2.1.symm, hrch]
      obtain ⟨st₂, t₂, hex_body, ht_body, hbuf₂, ha₂, hr₂⟩ :=
        filterSepBodyProg_exec a a_rch a_buf r_y r_k r_hi r_u r_tmp r_hit r_cnt
          hadj.2 y st_y en_y hen_w
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          hw1 hNw hlist_y (by simp [st₁]) hrch₁ hbuf₁ (by omega)
      have hri₂ : st₂.regs r_i = j := by
        rw [hr₂ r_i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        simp [st₁, r_i, r_y, hri]
      have htake_j1 : ((sep_l.map Fin.val).take (j + 1)) =
          (sep_l.map Fin.val).take j ++ [y.1] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by simp [hj]), Option.toList_some]
        simp [y]
      have hgy_eq : (if ∃ u ∈ A, G.Adj y u then [y.1] else []) = g y.1 := by
        simp [g, y.2]
      have hΦ_eq : Φ (st₂.setReg r_i (j + 1)) = Φ st' + 19 * (lists y).length := by
        simp only [Φ, State.setReg_regs_self, hri, htake_j1, List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton]
        rw [listOf_fin]
        omega
      refine ⟨st₂, 3 + t₂, .seq hex_y hex_body, by omega, ?_, hri₂⟩
      refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [State.setReg_regs, show r_n ≠ r_i by omega, ite_false]
        rw [hr₂ r_n (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        simp [st₁, r_n, r_y, hrn]
      · simp only [State.setReg_regs, show r_N ≠ r_i by omega, ite_false]
        rw [hr₂ r_N (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        simp [st₁, r_N, r_y, hrN]
      · intro r hr
        simp only [State.setReg_regs, show r ≠ r_i by omega, ite_false]
        rw [hr₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        simp [st₁, show r ≠ r_y by omega, hregs r hr]
      · intro x hx
        simp only [State.setReg_arrs]
        rw [ha₂ x hx]
        exact harrs x hx
      · rw [htake_j1, List.flatMap_append, List.flatMap_singleton, ← hgy_eq]
        refine ⟨?_, ?_⟩
        · simp only [State.setReg_arrs]
          rw [hbuf₂.1]; congr 2; rw [List.length_append]; omega
        · simp only [State.setReg_regs, show r_cnt ≠ r_i by omega, ite_false]
          rw [hbuf₂.2, List.length_append])
    0 (Nat.zero_le _) s₄ hI0
  obtain ⟨hri₅, _, hrN₅, hregs₅, harrs₅, hbuf₅⟩ := hI₅
  have htake_all : (sep_l.map Fin.val).take sep_l.length = sep_l.map Fin.val := by
    rw [← List.map_take, List.take_length]
  have hflat_all : ((sep_l.map Fin.val).take sep_l.length).flatMap g = bd_l.map Fin.val := by
    rw [hflat_take sep_l.length le_rfl, List.take_length]
  rw [hflat_all] at hbuf₅
  have hΦ₄ : Φ s₄ = 0 := by simp [Φ, s₄]
  have hΦ₅ : Φ s₅ ≤ 38 * G.edgeSet.ncard := by
    simp only [Φ, hri₅, htake_all]
    have hnd_val : (sep_l.map Fin.val).Nodup := hsep_nd.map Fin.val_injective
    have hlt_val : ∀ x ∈ sep_l.map Fin.val, x < N := by
      intro x hx
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      exact u.2
    have hsum1 := sum_map_le_of_nodup (fun x => (listOf lists x).length) hnd_val hlt_val
    have hsum2 : ∑ x ∈ Finset.range N, (listOf lists x).length = 2 * G.edgeSet.ncard := by
      have := length_flatUpTo_eq (H := G) (L := listOf lists) (by
        intro x; simpa [listOf_fin] using hadj.2 x)
      rw [← this, length_flatUpTo]
    omega
  -- Step 5: copyMinNProg a_buf a_bd r_N r_i r_cnt
  have hbd_len : (bd_l.map Fin.val).length ≤ N := by
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hsep_len_le
  have hbuf_len₅ : (bd_l.map Fin.val).length ≤ (s₅.arrs a_buf).length := by
    rw [hbuf₅.1, List.length_append]; omega
  obtain ⟨s₆, t₆, hex₆, ht₆, hbd₆, ha₆, hr₆⟩ :=
    copyMinNProg_exec a_buf a_bd r_N r_i r_cnt hd_buf.2.2.2
      (by omega) (by omega) (by omega) hrN₅ hNw hw1 hbuf₅.2
      (by omega) hbuf_len₅
  refine ⟨s₆, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq (.seq hex_n (.seq hex_i hex₅)) hex₆))),
    ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₅
    rw [hΦ₄] at ht₅
    rw [hsz]; omega
  · intro r hr
    rw [hr₆ r (by omega)]
    exact hregs₅ r hr
  · intro x hx1 hx2
    rw [ha₆ x hx1]
    exact harrs₅ x hx2
  · refine ⟨bd_l, hsep_nd.filter _, ?_, ?_⟩
    · intro y
      rw [nbhd_eq_sep_filter hsupp]
      simp only [bd_l, List.mem_filter, decide_eq_true_eq, hsep_mem, A, Set.mem_ofPred_eq]
    · rw [hbd₆, hbuf₅.1, take_append_replicate_of_le (bd_l.map Fin.val) _ _ 0 le_rfl,
        List.take_length]
      exact map_min_of_le (fun x hx => by
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
        exact le_of_lt u.2)

end GraphMinor.Compute.Crossing
