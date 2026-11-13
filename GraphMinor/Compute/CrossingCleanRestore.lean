module

import GraphMinor.Compute.CrossingOpsReplace

public import GraphMinor.Compute.CrossingCleanInit
import GraphMinor.Crossing.CutSec3
import GraphMinor.Crossing.CutSec91

/-!
# The Restoration Program of the Crossing Extractor (Section 9.2)

Section 9.2 of `docs/crossing/crossing_extractor.tex`:
"We process the fixed list $M$, once for each marker. For a marker $z$:
1. If $z$ has been deleted, skip it.
2. If $z$ is on the current cycle, skip it. Its edge to $x$ keeps it out of every component that
   does not contain $x$.
3. Form $B=J-w$.
4. Run the bounded-flow computation for three internally disjoint paths from $z$ to $x$ in $B$.
5. If it succeeds, continue with the next marker.
6. Otherwise, obtain the minimum two-cut $\{p,q\}$ with maximum open source side $U$, as in
   Section 2.2.
7. Delete all vertices of $U$ from $H$, and complete the triangle $\{w,p,q\}$.
8. Record one component of $B-\{p,q\}$ inside $U$, for example the component containing $z$, as
   the connected representative for the later lifting."

In Section 9 of `docs/crossing/crossing_extractor.tex`, the marker list is
$M = N_K(u) \setminus \{v\}$, which excludes the merged vertex $w = v$. When $v \in M$ and
$v \in S \setminus D$, `IsRestoreStep D v v H S H' S' rec` is mathematically false (since
`some v ∉ restoreVerts S v`). Accordingly, this file:
* defines `RestoreRecNeProgClaim` (adding `v ∉ M` to `RestoreRecProgClaim`) and proves
  `restoreRecNeProgClaim_of (hR : ReplaceRecProgClaim) : RestoreRecNeProgClaim` using
  `boundedFlowProgLeClaim_proved`;
* proves `not_exists_isRestoreStep_self`, `not_restoreRecProgClaim : ¬ RestoreRecProgClaim`, and
  `not_restoreProgClaim : ¬ RestoreProgClaim`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open Classical SimpleGraph GraphMinor.Crossing

/-! ### Combinatorial helpers for restoration runs and separators -/

/-- Appending one `IsRestoreStep` to the end of an `IsRestoreRun`. -/
theorem IsRestoreRun.snoc {V : Type*} [DecidableEq V] {D : List V} {w z : V} :
    ∀ {M : List V} {H₁ H₂ H₃ : SimpleGraph V} {S₁ S₂ S₃ : Set V}
      {rs : List (ReplRecord V)} {rec : Option (ReplRecord V)},
      IsRestoreRun D w M H₁ S₁ H₂ S₂ rs →
      IsRestoreStep D w z H₂ S₂ H₃ S₃ rec →
      IsRestoreRun D w (M ++ [z]) H₁ S₁ H₃ S₃ (rs ++ rec.toList)
  | [], _, _, _, _, _, _, _, rec, ⟨rfl, rfl, rfl⟩, hstep =>
    ⟨_, _, rec, [], hstep, ⟨rfl, rfl, rfl⟩, by simp⟩
  | _ :: _, _, _, _, _, _, _, _, rec, ⟨H_m, S_m, rec₀, rs', h₀, hrun, hrs⟩, hstep => by
    subst hrs
    exact ⟨H_m, S_m, rec₀, rs' ++ rec.toList, h₀, IsRestoreRun.snoc hrun hstep,
      List.append_assoc _ _ _⟩

/-- Valid replacements preserve `RootedConn (apex H D) (apexVerts S) none k`. -/
theorem rootedConn_apexVerts_newGraph {V : Type*} {r : ReplRecord V} {D : List V} {k : ℕ}
    (hsupp : HP25.IsSupportedOn r.graph r.verts) (hD : HP25.IsCycleList r.graph D)
    (hval : r.IsValid D)
    (hrc : RootedConn (apex r.graph D) (apexVerts r.verts) none k) :
    RootedConn (apex r.newGraph D) (apexVerts r.newVerts) none k := by
  have h := rootedConn_newGraph_of_lemma2 (F := ∅) hsupp hD hval
    (Set.empty_subset _) (by simpa using hrc)
  simpa using h

/-- Valid replacements keeping `w ∈ r.newVerts` preserve
`RootedConn (apex H D) (restoreVerts S w) none k`. -/
theorem rootedConn_restoreVerts_newGraph {V : Type*} [DecidableEq V]
    {r : ReplRecord V} {D : List V} {w : V} {k : ℕ}
    (hsupp : HP25.IsSupportedOn r.graph r.verts) (hD : HP25.IsCycleList r.graph D)
    (hval : r.IsValid D) (hw : w ∈ r.newVerts)
    (hrc : RootedConn (apex r.graph D) (restoreVerts r.verts w) none k) :
    RootedConn (apex r.newGraph D) (restoreVerts r.newVerts w) none k := by
  have h := rootedConn_newGraph_of_lemma2 (F := {w}) hsupp hD hval
    (Set.singleton_subset_iff.mpr hw) (by simpa [restoreVerts] using hrc)
  simpa [restoreVerts] using h

/-- When the 3-path bounded-flow query in `restoreVerts S v` fails on `z ∈ S \ D` (`z ≠ v`),
the returned maximum-source-side separator `X` has size `2` and is stored in `a_sep` as
`[p.val, q.val]` for two distinct vertices `p, q ≠ v` with `X = {some p, some q}`. -/
theorem sep_pair_of_maxSourceSeparator {N : ℕ} {H : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {v z : Fin N}
    {X : Finset (Option (Fin N))} {a_sep : ℕ} {s : State}
    (hzS : z ∈ S) (hzD : z ∉ D) (hzv : z ≠ v)
    (hR2 : RootedConn (apex H D) (restoreVerts (S : Set (Fin N)) v) none 2)
    (hmax : IsMaxSourceSeparator (apex H D) (restoreVerts (S : Set (Fin N)) v) (some z) none X)
    (hX_lt : X.card < 3)
    (hsep : IsSetListAt a_sep {y | some y ∈ X} s) :
    ¬ IsUnseparable (apex H D) (restoreVerts (S : Set (Fin N)) v) (some z) none 2 ∧
      ∃ p q : Fin N, p ≠ q ∧ p ≠ v ∧ q ≠ v ∧
        X = {some p, some q} ∧
        s.arrs a_sep = [p.val, q.val] := by
  have hunsep : ¬ IsUnseparable (apex H D) (restoreVerts (S : Set (Fin N)) v) (some z) none 2 :=
    fun h => hmax.1.1.2 (h X hmax.1.1.1 (by omega))
  have hnone_B : (none : Option (Fin N)) ∈ restoreVerts (S : Set (Fin N)) v :=
    ⟨Or.inl rfl, by simp⟩
  have hz_B : some z ∈ restoreVerts (S : Set (Fin N)) v :=
    ⟨Or.inr ⟨z, hzS, rfl⟩, by simp [hzv]⟩
  obtain ⟨X₀, hX₀_min, hX₀_card⟩ :=
    sec92Value_proved (apex H D) (restoreVerts (S : Set (Fin N)) v) none (some z)
      (Set.toFinite _) hnone_B hz_B (by simp) hzD hR2 hunsep
  have hle1 : X.card ≤ X₀.card := hmax.1.2 X₀ hX₀_min.1
  have hle2 : X₀.card ≤ X.card := hX₀_min.2 X hmax.1.1
  have hX_card : X.card = 2 := by omega
  obtain ⟨sep_l, hnd, hmem, harr⟩ := hsep
  have hX_eq_map : X = sep_l.toFinset.map ⟨Option.some, Option.some_injective _⟩ := by
    ext x
    simp only [Finset.mem_map, List.mem_toFinset, Function.Embedding.coeFn_mk]
    constructor
    · intro hx
      have hxB := hmax.1.1.1 hx
      rcases x with _ | y
      · exact (hxB.2 (Or.inr rfl)).elim
      · exact ⟨y, (hmem y).mpr hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mp hy
  have hlen : sep_l.length = 2 := by
    have h1 : (sep_l.toFinset.map ⟨Option.some, Option.some_injective _⟩).card = 2 := by
      rw [← hX_eq_map, hX_card]
    rw [Finset.card_map, List.toFinset_card_of_nodup hnd] at h1
    exact h1
  rcases sep_l with _ | ⟨p, _ | ⟨q, _ | _⟩⟩
  · simp at hlen
  · simp at hlen
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, and_true] at hnd
    have hX_pq : X = {some p, some q} := by
      ext x
      rw [hX_eq_map]
      simp [Finset.mem_insert, Finset.mem_singleton]
    have hp_B : some p ∈ restoreVerts (S : Set (Fin N)) v \ {some z, none} := by
      apply hmax.1.1.1
      rw [hX_pq]; simp
    have hq_B : some q ∈ restoreVerts (S : Set (Fin N)) v \ {some z, none} := by
      apply hmax.1.1.1
      rw [hX_pq]; simp
    have hpv : p ≠ v := fun h => hp_B.1.2 (congrArg some h)
    have hqv : q ≠ v := fun h => hq_B.1.2 (congrArg some h)
    exact ⟨hunsep, p, q, hnd, hpv, hqv, hX_pq, harr⟩
  · simp only [List.length_cons] at hlen; omega

/-! ### Array-frame helpers for restoration -/

/-- `ArrsOk` for `a.list ++ [a_base, a_base + 1]` below `a_base + 9`. -/
theorem arrsOk_flow_of_arrsOk_restore {a : InstArrs} {rest : List ℕ} {a_base : ℕ}
    (h : ArrsOk (a.list ++ rest) a_base) :
    ArrsOk (a.list ++ [a_base, a_base + 1]) (a_base + 9) := by
  have hnd_a : a.list.Nodup := (List.nodup_append.mp h.1).1
  refine ⟨List.nodup_append.mpr ⟨hnd_a, by simp, fun x hx y hy hxy => ?_⟩, fun x hx => ?_⟩
  · have hx_lt := mem_instArrs_lt_of_arrsOk h hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> omega
  · rcases List.mem_append.mp hx with hx | hx
    · have := mem_instArrs_lt_of_arrsOk h hx; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega

/-- `ArrsOk` for `a.list ++ [a_base + 1, a_base + 2, a_base + 3, a_rec]` below `a_base + 9`. -/
theorem arrsOk_repl_of_arrsOk_restore {a : InstArrs} {a_mk a_rec a_base : ℕ}
    (h : ArrsOk (a.list ++ [a_mk, a_rec]) a_base) :
    ArrsOk (a.list ++ [a_base + 1, a_base + 2, a_base + 3, a_rec]) (a_base + 9) := by
  obtain ⟨hnd_a, _, hdisj⟩ := List.nodup_append.mp h.1
  have hrec_lt : a_rec < a_base := h.2 a_rec (by simp)
  have hrec_not_a : a_rec ∉ a.list := fun hm => hdisj a_rec hm a_rec (by simp) rfl
  have hnd_right : ([a_base + 1, a_base + 2, a_base + 3, a_rec] : List ℕ).Nodup := by
    simp; omega
  refine ⟨List.nodup_append.mpr ⟨hnd_a, hnd_right, fun x hx y hy hxy => ?_⟩, fun x hx => ?_⟩
  · have hx_lt := mem_instArrs_lt_of_arrsOk h hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · omega
    · omega
    · omega
    · exact hrec_not_a (hxy ▸ hx)
  · rcases List.mem_append.mp hx with hx | hx
    · have := mem_instArrs_lt_of_arrsOk h hx; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> omega

/-! ### Building the 3-vertex restoration boundary `[v, p, q]` -/

/-- Allocate `a_bd` of length `3` and write `[r_v, a_sep[0], a_sep[1]]`. -/
def buildRestoreBdProg (a_sep a_bd : Arr) (r_v r_tmp : Reg) : Cmd :=
  .seq (.alloc a_bd (.const 3))
    (.seq (.write a_bd (.const 0) (.reg r_v))
      (.seq (.assign r_tmp (.read a_sep (.const 0)))
        (.seq (.write a_bd (.const 1) (.reg r_tmp))
          (.seq (.assign r_tmp (.read a_sep (.const 1)))
            (.write a_bd (.const 2) (.reg r_tmp))))))

/-- Execution of `buildRestoreBdProg`: produces `IsSetListAt a_bd {v, p, q}` in `17` steps. -/
theorem buildRestoreBdProg_exec {w N : ℕ} (a_sep a_bd r_v r_tmp : ℕ)
    (v p q : Fin N) {s : State}
    (hab : a_bd ≠ a_sep) (hr : r_tmp ≠ r_v)
    (hpq : p ≠ q) (hpv : p ≠ v) (hqv : q ≠ v)
    (hrv : s.regs r_v = v.val)
    (hsep : s.arrs a_sep = [p.val, q.val])
    (hw3 : 3 < 2 ^ w) (hN : N < 2 ^ w) :
    ∃ s' t, Exec w (buildRestoreBdProg a_sep a_bd r_v r_tmp) s s' t ∧
      t ≤ 19 ∧
      IsSetListAt a_bd (({v, p, q} : Finset (Fin N)) : Set (Fin N)) s' ∧
      (∀ x : ℕ, x ≠ a_bd → s'.arrs x = s.arrs x) ∧
      (∀ r : ℕ, r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hvw : v.val < 2 ^ w := lt_trans v.isLt hN
  have hpw : p.val < 2 ^ w := lt_trans p.isLt hN
  have hqw : q.val < 2 ^ w := lt_trans q.isLt hN
  set s₁ := s.setArr a_bd [0, 0, 0]
  have hex₁ : Exec w (.alloc a_bd (.const 3)) s s₁ 4 := .alloc (eval_const hw3)
  set s₂ := s₁.writeArr a_bd 0 v.val
  have hex₂ : Exec w (.write a_bd (.const 0) (.reg r_v)) s₁ s₂ 3 :=
    .write (eval_const h0w) (eval_reg (by simp [s₁, hrv]) hvw) (by simp [s₁])
  have hsep₂ : s₂.arrs a_sep = [p.val, q.val] := by
    simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ hab.symm, State.setArr_arrs_ne _ _ hab.symm, hsep]
  have hrd₀ : (Expr.read a_sep (.const 0)).eval w s₂ = some p.val := by
    have hlen : 0 < (s₂.arrs a_sep).length := by simp [hsep₂]
    have := eval_read (a := a_sep) (eval_const h0w) hlen (by simp [hsep₂, hpw])
    simpa [hsep₂] using this
  set s₃ := s₂.setReg r_tmp p.val
  have hex₃ : Exec w (.assign r_tmp (.read a_sep (.const 0))) s₂ s₃ 3 := .assign hrd₀
  set s₄ := s₃.writeArr a_bd 1 p.val
  have hex₄ : Exec w (.write a_bd (.const 1) (.reg r_tmp)) s₃ s₄ 3 :=
    .write (eval_const h1w) (eval_reg (by simp [s₃]) hpw) (by simp [s₃, s₂, s₁])
  have hsep₄ : s₄.arrs a_sep = [p.val, q.val] := by
    simp [s₄, s₃, State.writeArr_arrs_ne _ _ _ hab.symm, hsep₂]
  have hrd₁ : (Expr.read a_sep (.const 1)).eval w s₄ = some q.val := by
    have hlen : 1 < (s₄.arrs a_sep).length := by simp [hsep₄]
    have := eval_read (a := a_sep) (eval_const h1w) hlen (by simp [hsep₄, hqw])
    simpa [hsep₄] using this
  set s₅ := s₄.setReg r_tmp q.val
  have hex₅ : Exec w (.assign r_tmp (.read a_sep (.const 1))) s₄ s₅ 3 := .assign hrd₁
  set s₆ := s₅.writeArr a_bd 2 q.val
  have hex₆ : Exec w (.write a_bd (.const 2) (.reg r_tmp)) s₅ s₆ 3 :=
    .write (eval_const h2w) (eval_reg (by simp [s₅]) hqw) (by simp [s₅, s₄, s₃, s₂, s₁])
  refine ⟨s₆, 19,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    le_rfl, ?_, ?_, ?_⟩
  · refine ⟨[v, p, q], ?_, ?_, ?_⟩
    · simp [hpv.symm, hqv.symm, hpq]
    · intro y
      simp
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr]
  · intro x hx
    simp [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hx, State.setArr_arrs_ne _ _ hx]
  · intro r hne
    let _ := hr
    simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hne]

/-! ### The restoration step and loop programs (Section 9.2) -/

/-- When the 3-path flow query fails (`r_sub = 0`), build `a_bd = [v, p, q]`, find the component of
`z` inside `U` (which is already in `a_del = a_src`), and call `P_repl`. -/
def restoreReplaceProg (a : InstArrs)
    (a_sep a_del a_bd a_rep a_allow a_z a_rch a_que : Arr)
    (P_repl : Cmd) (r_v r_z r_sub : Reg) : Cmd :=
  .seq (buildRestoreBdProg a_sep a_bd r_v r_sub)
    (.seq (allowFromListProg a a_del a_allow r_sub)
      (.seq (singleSrcProg a_z r_z)
        (.seq (reachSearchProg a a_allow a_z a_rch a_rep a_que r_sub)
          P_repl)))

/-- Run the 3-path bounded-flow query from `r_z` to `x` in `B = J - v` (`ow = r_v`), and on failure
run `restoreReplaceProg`. -/
def restoreFlowAndReplaceProg (a : InstArrs)
    (a_sep a_del a_bd a_rep a_allow a_z a_rch a_que : Arr)
    (P_flow P_repl : Cmd) (r_v r_z r_sub : Reg) : Cmd :=
  .seq (.assign r_sub (.reg r_z))
    (.seq (.assign (r_sub + 1) (.const 3))
      (.seq (.assign (r_sub + 2) (.reg r_v))
        (.seq P_flow
          (.ite (.op .eq (.reg r_sub) (.const 0))
            (restoreReplaceProg a a_sep a_del a_bd a_rep a_allow a_z a_rch a_que
              P_repl r_v r_z r_sub)
            .skip))))

/-- One iteration of the restoration loop for index `r_j` into `a_mk`. -/
def restoreBodyProg (a : InstArrs)
    (a_mk a_sep a_del a_bd a_rep a_cyc_ind a_allow a_z a_rch a_que : Arr)
    (P_flow P_repl : Cmd) (r_v r_j r_z r_tmp r_sub : Reg) : Cmd :=
  .seq (.assign r_z (.read a_mk (.reg r_j)))
    (.seq (.assign r_tmp (.read a.alive (.reg r_z)))
      (.ite (.op .eq (.reg r_tmp) (.const 1))
        (.seq (.assign r_tmp (.read a_cyc_ind (.reg r_z)))
          (.ite (.op .eq (.reg r_tmp) (.const 0))
            (restoreFlowAndReplaceProg a a_sep a_del a_bd a_rep a_allow a_z a_rch a_que
              P_flow P_repl r_v r_z r_sub)
            .skip))
        .skip))

/-- Complete restoration program (Section 9.2): build the cycle indicator array `a_base + 4` and
process `M` in `a_mk` once each. -/
def restoreProg (a : InstArrs) (a_mk a_base : Arr) (P_flow P_repl : Cmd) (r_base : Reg) : Cmd :=
  .seq (allowFromListProg a a.cyc (a_base + 4) (r_base + 5))
    (.seq (.assign (r_base + 1) (.len a_mk))
      (.seq (.assign (r_base + 2) (.const 0))
        (forUp (r_base + 2) (.reg (r_base + 1))
          (restoreBodyProg a a_mk a_base (a_base + 1) (a_base + 2) (a_base + 3)
            (a_base + 4) (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
            P_flow P_repl r_base (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)))))

/-- Execution of one iteration `restoreBodyProg` at marker `z = M[j]`. -/
theorem restoreBodyProg_exec {w N : ℕ} (a : InstArrs) (a_mk a_rec r_rec a_base r_base : ℕ)
    (harrs : ArrsOk (a.list ++ [a_mk, a_rec]) a_base) (hr_rec : r_rec < r_base)
    {P_flow P_repl : Cmd} {C_F c_F C_R c_R : ℕ}
    (hP_flow : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (s : State),
      wordSize c_F (instSize N G) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → z ∈ S → z ∉ D → 1 ≤ k → k ≤ 4 → ow ≠ z.val → ow ≤ N →
      s.regs (r_base + 5) = z.val → s.regs (r_base + 5 + 1) = k → s.regs (r_base + 5 + 2) = ow →
      ∃ s' t, Exec w P_flow s s' t ∧ t ≤ C_F * instSize N G ∧
        KeepsBelow (r_base + 5) (a_base + 9) [] [a_base, a_base + 1] s s' ∧
        ((s'.regs (r_base + 5) = 1 ∧
            IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1)) ∨
          (s'.regs (r_base + 5) = 0 ∧
            ∃ X : Finset (Option (Fin N)),
              IsMaxSourceSeparator (apex G D) (flowVerts S ow) (some z) none X ∧ X.card < k ∧
              IsSetListAt a_base {y | some y ∈ X} s' ∧
              IsSetListAt (a_base + 1)
                {y | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s')))
    (hP_repl : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (r : ReplRecord (Fin N)) (recs : List (CrossRecord (Fin N)))
      (S' : Finset (Fin N)) (k : ℕ) (s : State),
      wordSize c_R (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → r.graph = G → r.verts = S → r.IsValid D →
      (S' : Set (Fin N)) = r.newVerts →
      IsSetListAt (a_base + 1) r.deleted s → IsSetListAt (a_base + 2) (r.boundary : Set (Fin N)) s →
      IsSetListAt (a_base + 3) r.rep s →
      IsRecBufAt a_rec r_rec recs k s → C_R * instSize N G ≤ k →
      ∃ s' t, Exec w P_repl s s' t ∧ t ≤ C_R * instSize N G ∧
        KeepsBelow (r_base + 5) (a_base + 9) [r_rec] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a r.newGraph S' D s' ∧
        ∃ k', IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.repl r]) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C_R * instSize N G)
    {H H_cur : SimpleGraph (Fin N)} {S S_cur : Finset (Fin N)} {D : List (Fin N)}
    {v : Fin N} {M : List (Fin N)} {recs₀ : List (CrossRecord (Fin N))}
    {rs : List (ReplRecord (Fin N))} {k j : ℕ} (hj : j < M.length)
    (hvM : v ∉ M)
    {s₀ s : State}
    (hinst : IsInstanceAt a H_cur S_cur D s) (hD : HP25.IsCycleList H_cur D)
    (hvS : v ∈ S_cur)
    (hR3 : RootedConn (apex H_cur D) (apexVerts (S_cur : Set (Fin N))) none 3)
    (hR2 : RootedConn (apex H_cur D) (restoreVerts (S_cur : Set (Fin N)) v) none 2)
    (hrun : IsRestoreRun D v (M.take j) H (S : Set (Fin N)) H_cur (S_cur : Set (Fin N)) rs)
    (hbuf : IsRecBufAt a_rec r_rec (recs₀ ++ rs.map CrossRecord.repl) k s)
    (hpot : H_cur.edgeSet.ncard + 3 * S_cur.card ≤ H.edgeSet.ncard + 3 * S.card)
    (hlen_rec : (s.arrs a_rec).length = (s₀.arrs a_rec).length)
    (hk_cap : 4 * C_R * instSize N H ≤ k)
    (hkeep : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s)
    (hrv : s.regs r_base = v.val) (hrm : s.regs (r_base + 1) = M.length)
    (hrj : s.regs (r_base + 2) = j)
    (hmk : s.arrs a_mk = M.map Fin.val)
    (hcyc_ind : s.arrs (a_base + 4) = List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0))
    (hw_F : wordSize c_F (instSize N H_cur) ≤ w)
    (hw_R : wordSize c_R (instSize N H_cur + (s₀.arrs a_rec).length) ≤ w)
    (hw_4K : 4 * instSize N H_cur + 4 < 2 ^ w)
    (hw_M : M.length + 1 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (H' : SimpleGraph (Fin N)) (S' : Finset (Fin N))
      (rs' : List (ReplRecord (Fin N))) (k' : ℕ),
      Exec w (restoreBodyProg a a_mk a_base (a_base + 1) (a_base + 2) (a_base + 3)
        (a_base + 4) (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
        P_flow P_repl r_base (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)) s s' t ∧
      t ≤ (4 * C_F + 4 * C_R + 1000) * instSize N H ∧
      IsInstanceAt a H' S' D s' ∧ HP25.IsCycleList H' D ∧
      v ∈ S' ∧
      RootedConn (apex H' D) (apexVerts (S' : Set (Fin N))) none 3 ∧
      RootedConn (apex H' D) (restoreVerts (S' : Set (Fin N)) v) none 2 ∧
      IsRestoreRun D v (M.take (j + 1)) H (S : Set (Fin N)) H' (S' : Set (Fin N)) rs' ∧
      IsRecBufAt a_rec r_rec (recs₀ ++ rs'.map CrossRecord.repl) k' s' ∧
      H'.edgeSet.ncard + 3 * S'.card ≤ H.edgeSet.ncard + 3 * S.card ∧
      (s'.arrs a_rec).length = (s₀.arrs a_rec).length ∧
      k ≤ k' + 4 * C_R * instSize N H ∧
      KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s' ∧
      s'.regs r_base = v.val ∧ s'.regs (r_base + 1) = M.length ∧
      s'.regs (r_base + 2) = j ∧ s'.arrs a_mk = M.map Fin.val ∧
      s'.arrs (a_base + 4) = List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) := by
  have hK_sz : instSize N H_cur ≤ 4 * instSize N H :=
    (instSize_le_four_mul_of_edge_pot hpot).2
  have hw1 : 1 < 2 ^ w := by have := instSize_pos N H_cur; omega
  have h0w : 0 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by have := instSize_pos N H_cur; omega
  have hNw : N < 2 ^ w := by have := le_instSize_self N H_cur; omega
  have hjw : j < 2 ^ w := by omega
  set z : Fin N := M[j]'hj
  have hz_mem_M : z ∈ M := List.getElem_mem hj
  have hzv : z ≠ v := fun e => hvM (e ▸ hz_mem_M)
  have htake_j1 : M.take (j + 1) = M.take j ++ [z] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
  have hzw : z.val < 2 ^ w := lt_trans z.isLt hNw
  -- Step 1: r_z := a_mk[r_j]
  have hmk_len : j < (s.arrs a_mk).length := by rw [hmk, List.length_map]; exact hj
  have hmk_val : (s.arrs a_mk)[j]'hmk_len = z.val := by simp [hmk, z]
  have hrd_mk : (Expr.read a_mk (.reg (r_base + 2))).eval w s = some z.val := by
    have := eval_read (a := a_mk) (eval_reg hrj hjw) hmk_len (by rw [hmk_val]; exact hzw)
    rwa [hmk_val] at this
  set s₁ := s.setReg (r_base + 3) z.val
  have hex₀ : Exec w (.assign (r_base + 3) (.read a_mk (.reg (r_base + 2)))) s s₁ 3 :=
    .assign hrd_mk
  -- Step 2: r_tmp := a.alive[r_z]
  set az : ℕ := if z ∈ S_cur then 1 else 0
  have haz_w : az < 2 ^ w := by simp only [az]; split_ifs <;> omega
  have hal_len : z.val < (s₁.arrs a.alive).length := by
    simp [s₁, hinst.length_alive, z.isLt]
  have hal_val : (s₁.arrs a.alive)[z.val]'hal_len = az := by
    simp [s₁, hinst.2.1, az]
  have hrd_al : (Expr.read a.alive (.reg (r_base + 3))).eval w s₁ = some az := by
    have := eval_read (a := a.alive) (eval_reg (r := r_base + 3) (by simp [s₁]) hzw) hal_len
      (by rw [hal_val]; exact haz_w)
    rwa [hal_val] at this
  set s₂ := s₁.setReg (r_base + 4) az
  have hex₁ : Exec w (.assign (r_base + 4) (.read a.alive (.reg (r_base + 3)))) s₁ s₂ 3 :=
    .assign hrd_al
  by_cases hzS : z ∈ S_cur
  · -- z ∈ S_cur: branch 1 taken
    have haz1 : az = 1 := by simp [az, hzS]
    have hcond1 : (Expr.op .eq (.reg (r_base + 4)) (.const 1)).eval w s₂ = some 1 := by
      have := eval_eq (s := s₂) (eval_reg (r := r_base + 4) (by simp [s₂, haz1]) hw1)
        (eval_const hw1) hw1
      simpa using this
    -- Step 3: r_tmp := (a_base + 4)[r_z]
    set dz : ℕ := if z ∈ D then 1 else 0
    have hdz_w : dz < 2 ^ w := by simp only [dz]; split_ifs <;> omega
    have hrc_len : z.val < (s₂.arrs (a_base + 4)).length := by
      simp [s₂, s₁, hcyc_ind, z.isLt]
    have hrc_val : (s₂.arrs (a_base + 4))[z.val]'hrc_len = dz := by
      simp [s₂, s₁, hcyc_ind, dz]
    have hrd_rc : (Expr.read (a_base + 4) (.reg (r_base + 3))).eval w s₂ = some dz := by
      have := eval_read (a := a_base + 4) (eval_reg (r := r_base + 3) (by simp [s₂, s₁]) hzw)
        hrc_len (by rw [hrc_val]; exact hdz_w)
      rwa [hrc_val] at this
    set s₃ := s₂.setReg (r_base + 4) dz
    have hex₂ : Exec w (.assign (r_base + 4) (.read (a_base + 4) (.reg (r_base + 3)))) s₂ s₃ 3 :=
      .assign hrd_rc
    by_cases hzD : z ∈ D
    · -- z ∈ D: skip
      have hdz1 : dz = 1 := by simp [dz, hzD]
      have hcond2 : (Expr.op .eq (.reg (r_base + 4)) (.const 0)).eval w s₃ = some 0 := by
        have := eval_eq (s := s₃) (eval_reg (r := r_base + 4) (by simp [s₃, hdz1]) hw1)
          (eval_const h0w) hw1
        simpa using this
      have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 4)) (.const 0))
          (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
            (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
            P_flow P_repl r_base (r_base + 3) (r_base + 5)) .skip) s₃ s₃ 4 :=
        .ite_false hcond2 (.skip s₃)
      have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 4)) (.const 1))
          (.seq (.assign (r_base + 4) (.read (a_base + 4) (.reg (r_base + 3))))
            (.ite (.op .eq (.reg (r_base + 4)) (.const 0))
              (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
                (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
                P_flow P_repl r_base (r_base + 3) (r_base + 5)) .skip)) .skip)
          s₂ s₃ 10 := .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
      have hstep : IsRestoreStep D v z H_cur (S_cur : Set (Fin N))
          H_cur (S_cur : Set (Fin N)) none :=
        Or.inl ⟨Or.inr (Or.inl hzD), rfl, rfl, rfl⟩
      have hrun' : IsRestoreRun D v (M.take (j + 1)) H (S : Set (Fin N))
          H_cur (S_cur : Set (Fin N)) rs := by
        rw [htake_j1]
        simpa using IsRestoreRun.snoc hrun hstep
      have hsz_pos : 1 ≤ instSize N H := instSize_pos N H
      have h_mul : (4 * C_F + 4 * C_R + 1000) * instSize N H =
          4 * C_F * instSize N H + 4 * C_R * instSize N H + 1000 * instSize N H := by ring
      refine ⟨s₃, 16, H_cur, S_cur, rs, k, .seq hex₀ (.seq hex₁ hex_ite1), by omega,
        hinst.of_keeps_disjoint (fun _ _ => rfl), hD, hvS, hR3, hR2, hrun',
        hbuf.of_arrs_regs_eq rfl (by
          simp [s₃, s₂, s₁, show r_rec ≠ r_base + 4 by omega, show r_rec ≠ r_base + 3 by omega]),
        hpot, hlen_rec, by omega,
        ((hkeep.setReg_ge (by omega) _).setReg_ge (by omega) _).setReg_ge (by omega) _,
        by simp [s₃, s₂, s₁, hrv], by simp [s₃, s₂, s₁, hrm],
        by simp [s₃, s₂, s₁, hrj], hmk, hcyc_ind⟩
    · -- z ∈ S_cur ∧ z ∉ D: run 3-path flow query in B = J - v
      have hdz0 : dz = 0 := by simp [dz, hzD]
      have hcond2 : (Expr.op .eq (.reg (r_base + 4)) (.const 0)).eval w s₃ = some 1 := by
        have := eval_eq (s := s₃) (eval_reg (r := r_base + 4) (by simp [s₃, hdz0]) h0w)
          (eval_const h0w) hw1
        simpa using this
      have hvw : v.val < 2 ^ w := lt_trans v.isLt hNw
      -- Step 4a: set r_sub := z.val, r_sub + 1 := 3, r_sub + 2 := v.val
      set s₄ := s₃.setReg (r_base + 5) z.val
      have hex_a1 : Exec w (.assign (r_base + 5) (.reg (r_base + 3))) s₃ s₄ 2 :=
        .assign (eval_reg (by simp [s₃, s₂, s₁]) hzw)
      set s₅ := s₄.setReg (r_base + 5 + 1) 3
      have hex_a2 : Exec w (.assign (r_base + 5 + 1) (.const 3)) s₄ s₅ 2 :=
        .assign (eval_const h3w)
      set s₆ := s₅.setReg (r_base + 5 + 2) v.val
      have hex_a3 : Exec w (.assign (r_base + 5 + 2) (.reg r_base)) s₅ s₆ 2 :=
        .assign (eval_reg (by
          simp [s₅, s₄, s₃, s₂, s₁, show r_base ≠ r_base + 5 + 1 by omega, hrv]) hvw)
      have hinst₆ : IsInstanceAt a H_cur S_cur D s₆ := hinst.of_keeps_disjoint (fun _ _ => rfl)
      -- Step 4b: P_flow
      have hzv_val : v.val ≠ z.val := fun e => hzv (Fin.ext e.symm)
      obtain ⟨s₇, t_fl, hex_fl, ht_fl, hkeep_fl, hres_fl⟩ :=
        hP_flow w N H_cur S_cur D z 3 v.val s₆ hw_F hinst₆ hD hzS hzD (by omega) (by omega)
          hzv_val (le_of_lt v.isLt)
          (by simp [s₆, s₅, s₄]) (by simp [s₆, s₅]) (by simp [s₆])
      have hno_a : ∀ d, a_base + d ∉ a.list := fun d => add_not_mem_instArrs_of_arrsOk harrs
      have hinst₇ : IsInstanceAt a H_cur S_cur D s₇ :=
        hinst₆.of_keeps_disjoint (fun x hx =>
          hkeep_fl.2 x (lt_trans (mem_instArrs_lt_of_arrsOk harrs hx) (by omega))
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or];
                exact ⟨fun e => hno_a 0 (by simpa [← e] using hx), fun e => hno_a 1 (e ▸ hx)⟩))
      have hmk_lt : a_mk < a_base := harrs.2 a_mk (by simp)
      have hrec_lt : a_rec < a_base := harrs.2 a_rec (by simp)
      have ha₇_mk : s₇.arrs a_mk = M.map Fin.val := by
        rw [hkeep_fl.2 a_mk (by omega) (by simp; omega)]; exact hmk
      have ha₇_rec : s₇.arrs a_rec = s.arrs a_rec :=
        hkeep_fl.2 a_rec (by omega) (by simp; omega)
      have ha₇_cyc_ind : s₇.arrs (a_base + 4) =
          List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) := by
        rw [hkeep_fl.2 (a_base + 4) (by omega) (by simp)]; exact hcyc_ind
      have hr₇_below : ∀ r₀ < r_base + 3, s₇.regs r₀ = s.regs r₀ := by
        intro r₀ hr₀
        rw [hkeep_fl.1 r₀ (by omega) (by simp)]
        simp [s₆, s₅, s₄, s₃, s₂, s₁,
          show r₀ ≠ r_base + 5 + 2 by omega, show r₀ ≠ r_base + 5 + 1 by omega,
          show r₀ ≠ r_base + 5 by omega, show r₀ ≠ r_base + 4 by omega,
          show r₀ ≠ r_base + 3 by omega]
      have hrz₇ : s₇.regs (r_base + 3) = z.val := by
        rw [hkeep_fl.1 (r_base + 3) (by omega) (by simp)]
        simp [s₆, s₅, s₄, s₃, s₂, s₁]
      have hkeep_s₇ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₇ := by
        refine ⟨fun r₀ hr₀ hnr₀ => by rw [hr₇_below r₀ (by omega)]; exact hkeep.1 r₀ hr₀ hnr₀,
                fun x hx hnx => by
                  rw [hkeep_fl.2 x (by omega) (by simp; omega)]
                  exact hkeep.2 x hx hnx⟩
      rcases hres_fl with ⟨hr_fl1, hunsep_z⟩ | ⟨hr_fl0, X, hmax_X, hX_lt, hsep_X, hsrc_X⟩
      · -- Flow succeeded: s₇.regs (r_base + 5) = 1
        rw [flowVerts_val] at hunsep_z
        have hcond3 : (Expr.op .eq (.reg (r_base + 5)) (.const 0)).eval w s₇ = some 0 := by
          have := eval_eq (s := s₇) (eval_reg hr_fl1 hw1) (eval_const h0w) hw1
          simpa using this
        have hex_ite3 : Exec w (.ite (.op .eq (.reg (r_base + 5)) (.const 0))
            (restoreReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_repl r_base (r_base + 3) (r_base + 5)) .skip) s₇ s₇ 4 :=
          .ite_false hcond3 (.skip s₇)
        have hex_fl_all : Exec w
            (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_flow P_repl r_base (r_base + 3) (r_base + 5))
            s₃ s₇ (2 + (2 + (2 + (t_fl + 4)))) :=
          .seq hex_a1 (.seq hex_a2 (.seq hex_a3 (.seq hex_fl hex_ite3)))
        have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 4)) (.const 0))
            (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_flow P_repl r_base (r_base + 3) (r_base + 5)) .skip)
            s₃ s₇ (3 + (2 + (2 + (2 + (t_fl + 4))))) :=
          .ite_true hcond2 one_ne_zero hex_fl_all
        have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 4)) (.const 1))
            (.seq (.assign (r_base + 4) (.read (a_base + 4) (.reg (r_base + 3))))
              (.ite (.op .eq (.reg (r_base + 4)) (.const 0))
                (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
                  (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
                  P_flow P_repl r_base (r_base + 3) (r_base + 5)) .skip)) .skip)
            s₂ s₇ (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + 4))))))) :=
          .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
        have hstep : IsRestoreStep D v z H_cur (S_cur : Set (Fin N))
            H_cur (S_cur : Set (Fin N)) none :=
          Or.inl ⟨Or.inr (Or.inr hunsep_z), rfl, rfl, rfl⟩
        have hrun' : IsRestoreRun D v (M.take (j + 1)) H (S : Set (Fin N))
            H_cur (S_cur : Set (Fin N)) rs := by
          rw [htake_j1]
          simpa using IsRestoreRun.snoc hrun hstep
        have ht_bound : 3 + (3 + (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + 4)))))))) ≤
            (4 * C_F + 4 * C_R + 1000) * instSize N H := by
          have h1 : C_F * instSize N H_cur ≤ 4 * C_F * instSize N H := by
            calc C_F * instSize N H_cur ≤ C_F * (4 * instSize N H) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_F * instSize N H := by ring
          have h2 : (4 * C_F + 4 * C_R + 1000) * instSize N H =
              4 * C_F * instSize N H + 4 * C_R * instSize N H + 1000 * instSize N H := by ring
          have hsz_pos : 1 ≤ instSize N H := instSize_pos N H
          omega
        refine ⟨s₇, _, H_cur, S_cur, rs, k, .seq hex₀ (.seq hex₁ hex_ite1), ht_bound,
          hinst₇, hD, hvS, hR3, hR2, hrun',
          hbuf.of_arrs_regs_eq ha₇_rec (hr₇_below r_rec (by omega)),
          hpot, by rw [ha₇_rec, hlen_rec], by omega, hkeep_s₇,
          by rw [hr₇_below r_base (by omega), hrv],
          by rw [hr₇_below (r_base + 1) (by omega), hrm],
          by rw [hr₇_below (r_base + 2) (by omega), hrj],
          ha₇_mk, ha₇_cyc_ind⟩
      · -- Flow failed: s₇.regs (r_base + 5) = 0, run restoreReplaceProg
        rw [flowVerts_val] at hmax_X hsrc_X
        have hcond3 : (Expr.op .eq (.reg (r_base + 5)) (.const 0)).eval w s₇ = some 1 := by
          have := eval_eq (s := s₇) (eval_reg hr_fl0 h0w) (eval_const h0w) hw1
          simpa using this
        obtain ⟨hunsep_z, p, q, hpq, hpv, hqv, hX_pq, hsep_pq⟩ :=
          sep_pair_of_maxSourceSeparator hzS hzD hzv hR2 hmax_X hX_lt hsep_X
        rw [hX_pq] at hmax_X hsrc_X
        let r := restoreRecord H_cur (S_cur : Set (Fin N)) D v z p q
        obtain ⟨hval, _⟩ := restoreRecord_isValid hinst.1 hvS hR3 hR2 hmax_X
        -- Step 5a: buildRestoreBdProg a_base (a_base + 2) r_base (r_base + 5)
        have hrv₇ : s₇.regs r_base = v.val := by
          rw [hr₇_below r_base (by omega), hrv]
        obtain ⟨s₈, t₈, hex₈, ht₈, hbd₈, ha₈, hr₈⟩ :=
          buildRestoreBdProg_exec a_base (a_base + 2) r_base (r_base + 5) v p q
            (by omega) (by omega) hpq hpv hqv hrv₇ hsep_pq h3w hNw
        have hinst₈ : IsInstanceAt a H_cur S_cur D s₈ :=
          hinst₇.of_keeps_disjoint (fun x hx => ha₈ x (fun e => hno_a 2 (e ▸ hx)))
        -- Step 5b: allowFromListProg a (a_base + 1) (a_base + 5) (r_base + 5)
        have hsrc₈ : IsSetListAt (a_base + 1) r.deleted s₈ :=
          hsrc_X.of_arrs_eq (ha₈ (a_base + 1) (by omega))
        obtain ⟨U_l, hU_nd, hU_mem, hU_arr⟩ := hsrc₈
        have hU_len : U_l.length ≤ N := by
          have := hU_nd.length_le_card
          simpa using this
        obtain ⟨s₉, t₉, hex₉, ht₉, hr₉, ha₉, hallow₉⟩ :=
          allowFromListProg_exec a (a_base + 1) (a_base + 5) (r_base + 5)
            hinst₈ hU_arr hU_len (by omega) hw_4K
        have hinst₉ : IsInstanceAt a H_cur S_cur D s₉ :=
          hinst₈.of_keeps_disjoint (fun x hx => ha₉ x (fun e => hno_a 5 (e ▸ hx)))
        -- Step 5c: singleSrcProg (a_base + 6) (r_base + 3)
        have hrz₉ : s₉.regs (r_base + 3) = z.val := by
          rw [hr₉ (r_base + 3) (by omega), hr₈ (r_base + 3) (by omega), hrz₇]
        obtain ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hsrc_z₁₀, ha₁₀, hr₁₀⟩ :=
          singleSrcProg_exec_nat (w := w) (a_base + 6) (r_base + 3) z (s := s₉) hrz₉ hw1 hNw
        have hinst₁₀ : IsInstanceAt a H_cur S_cur D s₁₀ :=
          hinst₉.of_keeps_disjoint (fun x hx => ha₁₀ x (fun e => hno_a 6 (e ▸ hx)))
        have hallow₁₀ : s₁₀.arrs (a_base + 5) =
            List.ofFn (fun x : Fin N =>
              @ite ℕ (x ∈ r.deleted) (propDecidable _) 1 0) := by
          rw [ha₁₀ (a_base + 5) (by omega), hallow₉]
          congr 1; funext x
          by_cases hxU : x ∈ r.deleted
          · have hxL : x ∈ U_l := (hU_mem x).mpr hxU
            simp [hxU, hxL]
          · have hxL : x ∉ U_l := fun hm => hxU ((hU_mem x).mp hm)
            simp [hxU, hxL]
        -- Step 5d: reachSearchProg a (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 3) (a_base + 8)
        obtain ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hr₁₁, ha₁₁, _, hrep₁₁⟩ :=
          reachSearchProg_exec a (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 3) (a_base + 8)
            (r_base + 5) hinst₁₀ hallow₁₀ hsrc_z₁₀ (by simp)
            ⟨hno_a 7, by omega, by omega, by omega, by omega⟩
            ⟨hno_a 8, by omega, by omega, by omega⟩
            ⟨hno_a 3, by omega, by omega, by omega⟩ hw_4K
        have ha₁₁_below : ∀ x < a_base, s₁₁.arrs x = s.arrs x := by
          intro x hx
          rw [ha₁₁ x (by omega) (by omega) (by omega),
              ha₁₀ x (by omega), ha₉ x (by omega), ha₈ x (by omega),
              hkeep_fl.2 x (by omega) (by simp; omega)]
          rfl
        have hr₁₁_below : ∀ r₀ < r_base + 3, s₁₁.regs r₀ = s.regs r₀ := by
          intro r₀ hr₀
          rw [hr₁₁ r₀ (by omega), hr₁₀, hr₉ r₀ (by omega),
              hr₈ r₀ (by omega), hr₇_below r₀ hr₀]
        have hinst₁₁ : IsInstanceAt a H_cur S_cur D s₁₁ :=
          hinst.of_keeps_disjoint (fun x hx => ha₁₁_below x (mem_instArrs_lt_of_arrsOk harrs hx))
        have hdel₁₁ : IsSetListAt (a_base + 1) r.deleted s₁₁ :=
          ⟨U_l, hU_nd, hU_mem, by
            rw [ha₁₁ (a_base + 1) (by omega) (by omega) (by omega),
                ha₁₀ (a_base + 1) (by omega), ha₉ (a_base + 1) (by omega), hU_arr]⟩
        have hbd₁₁ : IsSetListAt (a_base + 2) (r.boundary : Set (Fin N)) s₁₁ := by
          apply hbd₈.of_arrs_eq
          rw [ha₁₁ (a_base + 2) (by omega) (by omega) (by omega),
              ha₁₀ (a_base + 2) (by omega), ha₉ (a_base + 2) (by omega)]
        have hrep₁₁' : IsSetListAt (a_base + 3) r.rep s₁₁ := by
          change IsSetListAt (a_base + 3) {y | ReachIn H_cur r.deleted z y} s₁₁
          rw [← reachSet_singleton H_cur r.deleted]
          exact hrep₁₁
        let S' : Finset (Fin N) := r.newVerts.toFinset
        have hS'_coe : (S' : Set (Fin N)) = r.newVerts := Set.coe_toFinset r.newVerts
        have hbuf₁₁ : IsRecBufAt a_rec r_rec (recs₀ ++ rs.map CrossRecord.repl) k s₁₁ :=
          hbuf.of_arrs_regs_eq (ha₁₁_below a_rec hrec_lt) (hr₁₁_below r_rec (by omega))
        have hlen_rec₁₁ : (s₁₁.arrs a_rec).length = (s₀.arrs a_rec).length := by
          rw [ha₁₁_below a_rec hrec_lt, hlen_rec]
        have hk_R : C_R * instSize N H_cur ≤ k := by
          calc C_R * instSize N H_cur ≤ C_R * (4 * instSize N H) := Nat.mul_le_mul_left _ hK_sz
            _ = 4 * C_R * instSize N H := by ring
            _ ≤ k := hk_cap
        -- Step 5e: P_repl
        obtain ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hkeep₁₂, hinst₁₂, k', hbuf₁₂, hlen₁₂, hk₁₂⟩ :=
          hP_repl w N H_cur S_cur D r (recs₀ ++ rs.map CrossRecord.repl) S' k s₁₁
            (by rwa [hlen_rec₁₁]) hinst₁₁ hD rfl rfl hval hS'_coe
            hdel₁₁ hbd₁₁ hrep₁₁' hbuf₁₁ hk_R
        have hex_repl_all : Exec w
            (restoreReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_repl r_base (r_base + 3) (r_base + 5))
            s₇ s₁₂ (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂)))) :=
          .seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))
        have hex_ite3 : Exec w (.ite (.op .eq (.reg (r_base + 5)) (.const 0))
            (restoreReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_repl r_base (r_base + 3) (r_base + 5)) .skip)
            s₇ s₁₂ (3 + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))) :=
          .ite_true hcond3 one_ne_zero hex_repl_all
        have hex_fl_all : Exec w
            (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_flow P_repl r_base (r_base + 3) (r_base + 5))
            s₃ s₁₂ (2 + (2 + (2 + (t_fl + (3 + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))))))) :=
          .seq hex_a1 (.seq hex_a2 (.seq hex_a3 (.seq hex_fl hex_ite3)))
        have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 4)) (.const 0))
            (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_flow P_repl r_base (r_base + 3) (r_base + 5)) .skip)
            s₃ s₁₂ (3 + (2 + (2 + (2 + (t_fl + (3 + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂)))))))))) :=
          .ite_true hcond2 one_ne_zero hex_fl_all
        have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 4)) (.const 1))
            (.seq (.assign (r_base + 4) (.read (a_base + 4) (.reg (r_base + 3))))
              (.ite (.op .eq (.reg (r_base + 4)) (.const 0))
                (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
                  (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
                  P_flow P_repl r_base (r_base + 3) (r_base + 5)) .skip)) .skip)
            s₂ s₁₂
            (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + (3 + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂)))))))))))) :=
          .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
        have hv_new : v ∈ r.newVerts :=
          hval.2.2.2.1 (Finset.mem_insert_self v {p, q})
        have hvS' : v ∈ S' := by rwa [← Finset.mem_coe, hS'_coe]
        have hR3' : RootedConn (apex r.newGraph D) (apexVerts (S' : Set (Fin N))) none 3 := by
          rw [hS'_coe]
          exact rootedConn_apexVerts_newGraph hinst.1 hD hval hR3
        have hR2' : RootedConn (apex r.newGraph D) (restoreVerts (S' : Set (Fin N)) v) none 2 := by
          rw [hS'_coe]
          exact rootedConn_restoreVerts_newGraph hinst.1 hD hval hv_new hR2
        have hstep : IsRestoreStep D v z H_cur (S_cur : Set (Fin N))
            r.newGraph (S' : Set (Fin N)) (some r) :=
          Or.inr ⟨hzS, hzD, hunsep_z, p, q, hpq, hmax_X, rfl, rfl, hS'_coe⟩
        have hrun' : IsRestoreRun D v (M.take (j + 1)) H (S : Set (Fin N))
            r.newGraph (S' : Set (Fin N)) (rs ++ [r]) := by
          rw [htake_j1]
          exact IsRestoreRun.snoc hrun hstep
        have hbuf₁₂' : IsRecBufAt a_rec r_rec
            (recs₀ ++ (rs ++ [r]).map CrossRecord.repl) k' s₁₂ := by
          simpa [List.map_append, List.append_assoc] using hbuf₁₂
        have hkeep_s₁₁ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₁₁ :=
          ⟨fun r₀ hr₀ hnr₀ => by rw [hr₁₁_below r₀ (by omega)]; exact hkeep.1 r₀ hr₀ hnr₀,
           fun x hx hnx => by rw [ha₁₁_below x hx]; exact hkeep.2 x hx hnx⟩
        have hkeep_s₁₂ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₁₂ :=
          hkeep_s₁₁.trans (hkeep₁₂.le (by omega) (by omega))
            (fun _ hm _ => hm) (fun _ hm _ => hm)
        have hrv₁₂ : s₁₂.regs r_base = v.val := by
          rw [hkeep₁₂.1 r_base (by omega) (by simp; omega), hr₁₁_below r_base (by omega), hrv]
        have hrm₁₂ : s₁₂.regs (r_base + 1) = M.length := by
          rw [hkeep₁₂.1 (r_base + 1) (by omega) (by simp; omega),
              hr₁₁_below (r_base + 1) (by omega), hrm]
        have hrj₁₂ : s₁₂.regs (r_base + 2) = j := by
          rw [hkeep₁₂.1 (r_base + 2) (by omega) (by simp; omega),
              hr₁₁_below (r_base + 2) (by omega), hrj]
        have hmk_not_ar : a_mk ∉ a.list ++ [a_rec] := by
          obtain ⟨_, hnd_mr, hdisj⟩ := List.nodup_append.mp harrs.1
          simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨fun hm => hdisj a_mk hm a_mk (by simp) rfl,
                 fun e => (List.nodup_cons.mp hnd_mr).1 (by simp [e])⟩
        have hmk₁₂ : s₁₂.arrs a_mk = M.map Fin.val := by
          rw [hkeep₁₂.2 a_mk (by omega) hmk_not_ar, ha₁₁_below a_mk hmk_lt, hmk]
        have hcyc_ind₁₂ : s₁₂.arrs (a_base + 4) =
            List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) := by
          rw [hkeep₁₂.2 (a_base + 4) (by omega) (by
            simp only [List.mem_append, List.mem_singleton, not_or]
            exact ⟨hno_a 4, by omega⟩)]
          rw [ha₁₁ (a_base + 4) (by omega) (by omega) (by omega),
              ha₁₀ (a_base + 4) (by omega), ha₉ (a_base + 4) (by omega),
              ha₈ (a_base + 4) (by omega)]
          exact ha₇_cyc_ind
        have ht_bound :
            3 + (3 + (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + (3 + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))))))))))) ≤
            (4 * C_F + 4 * C_R + 1000) * instSize N H := by
          have h1 : C_F * instSize N H_cur ≤ 4 * C_F * instSize N H := by
            calc C_F * instSize N H_cur ≤ C_F * (4 * instSize N H) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_F * instSize N H := by ring
          have h2 : C_R * instSize N H_cur ≤ 4 * C_R * instSize N H := by
            calc C_R * instSize N H_cur ≤ C_R * (4 * instSize N H) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_R * instSize N H := by ring
          have h3 : (4 * C_F + 4 * C_R + 1000) * instSize N H =
              4 * C_F * instSize N H + 4 * C_R * instSize N H + 1000 * instSize N H := by ring
          have hsz_pos : 1 ≤ instSize N H := instSize_pos N H
          omega
        have hk_bound : k ≤ k' + 4 * C_R * instSize N H := by
          have h1 : C_R * instSize N H_cur ≤ 4 * C_R * instSize N H := by
            calc C_R * instSize N H_cur ≤ C_R * (4 * instSize N H) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_R * instSize N H := by ring
          omega
        exact ⟨s₁₂, _, r.newGraph, S', rs ++ [r], k',
          .seq hex₀ (.seq hex₁ hex_ite1), ht_bound, hinst₁₂,
          ReplRecord.isCycleList_newGraph hD hval, hvS', hR3', hR2', hrun', hbuf₁₂',
          le_trans (edge_pot_step rfl rfl hval hS'_coe).2.2 hpot,
          hlen₁₂.trans hlen_rec₁₁, hk_bound, hkeep_s₁₂, hrv₁₂, hrm₁₂, hrj₁₂, hmk₁₂, hcyc_ind₁₂⟩
  · -- z ∉ S_cur: skip
    have haz0 : az = 0 := by simp [az, hzS]
    have hcond1 : (Expr.op .eq (.reg (r_base + 4)) (.const 1)).eval w s₂ = some 0 := by
      have := eval_eq (s := s₂) (eval_reg (r := r_base + 4) (by simp [s₂, haz0]) h0w)
        (eval_const hw1) hw1
      simpa using this
    have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 4)) (.const 1))
        (.seq (.assign (r_base + 4) (.read (a_base + 4) (.reg (r_base + 3))))
          (.ite (.op .eq (.reg (r_base + 4)) (.const 0))
            (restoreFlowAndReplaceProg a a_base (a_base + 1) (a_base + 2) (a_base + 3)
              (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
              P_flow P_repl r_base (r_base + 3) (r_base + 5)) .skip)) .skip)
        s₂ s₂ 4 := .ite_false hcond1 (.skip s₂)
    have hstep : IsRestoreStep D v z H_cur (S_cur : Set (Fin N))
        H_cur (S_cur : Set (Fin N)) none :=
      Or.inl ⟨Or.inl hzS, rfl, rfl, rfl⟩
    have hrun' : IsRestoreRun D v (M.take (j + 1)) H (S : Set (Fin N))
        H_cur (S_cur : Set (Fin N)) rs := by
      rw [htake_j1]
      simpa using IsRestoreRun.snoc hrun hstep
    have hsz_pos : 1 ≤ instSize N H := instSize_pos N H
    have h_mul : (4 * C_F + 4 * C_R + 1000) * instSize N H =
        4 * C_F * instSize N H + 4 * C_R * instSize N H + 1000 * instSize N H := by ring
    refine ⟨s₂, 10, H_cur, S_cur, rs, k, .seq hex₀ (.seq hex₁ hex_ite1), by omega,
      hinst.of_keeps_disjoint (fun _ _ => rfl), hD, hvS, hR3, hR2, hrun',
      hbuf.of_arrs_regs_eq rfl (by
        simp [s₂, s₁, show r_rec ≠ r_base + 4 by omega, show r_rec ≠ r_base + 3 by omega]),
      hpot, hlen_rec, by omega,
      (hkeep.setReg_ge (by omega) _).setReg_ge (by omega) _,
      by simp [s₂, s₁, hrv], by simp [s₂, s₁, hrm],
      by simp [s₂, s₁, hrj], hmk, hcyc_ind⟩

/-! ### Corrected `RestoreRecNeProgClaim` and its proof -/

/-- **Restoration** (Section 9.2), with the records in a buffer and the condition `v ∉ M`
(since in Section 9, $M = N_K(u) \setminus \{v\}$ excludes the merged vertex $v$). -/
def RestoreRecNeProgClaim : Prop :=
  ∀ (a : InstArrs) (a_mk a_rec r_rec a_base r_base : ℕ),
    ArrsOk (a.list ++ [a_mk, a_rec]) a_base → r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (H : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (v : Fin N) (M : List (Fin N))
      (recs : List (CrossRecord (Fin N))) (k : ℕ) (s : State),
      wordSize c ((M.length + 1) * instSize N H + (s.arrs a_rec).length) ≤ w →
      IsInstanceAt a H S D s → HP25.IsCycleList H D → v ∈ S → v ∉ M →
      RootedConn (apex H D) (apexVerts (S : Set (Fin N))) none 3 →
      RootedConn (apex H D) (restoreVerts (S : Set (Fin N)) v) none 2 →
      s.regs r_base = v.val → s.arrs a_mk = M.map Fin.val → IsRecBufAt a_rec r_rec recs k s →
      C * (M.length + 1) * instSize N H ≤ k →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (M.length + 1) * instSize N H ∧
        KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' ∧
        ∃ (H' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (rs : List (ReplRecord (Fin N)))
          (k' : ℕ),
          IsRestoreRun D v M H (S : Set (Fin N)) H' (S' : Set (Fin N)) rs ∧
          IsInstanceAt a H' S' D s' ∧
          IsRecBufAt a_rec r_rec (recs ++ rs.map CrossRecord.repl) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
          k ≤ k' + C * (M.length + 1) * instSize N H

/-- **Restoration** (`RestoreRecNeProgClaim`) proved from `ReplaceRecProgClaim` and
`boundedFlowProgLeClaim_proved`. -/
theorem restoreRecNeProgClaim_of : RestoreRecNeProgClaim := by
  intro a a_mk a_rec r_rec a_base r_base harrs hr_rec
  obtain ⟨P_flow, C_F, c_F, hP_flow⟩ :=
    boundedFlowProgLeClaim_proved a a_base (a_base + 1) (a_base + 9) (r_base + 5)
      (arrsOk_flow_of_arrsOk_restore harrs)
  obtain ⟨P_repl, C_R, c_R, hP_repl⟩ :=
    replaceRecProgClaim_proved a (a_base + 1) (a_base + 2) (a_base + 3) a_rec r_rec (a_base + 9) (r_base + 5)
      (arrsOk_repl_of_arrsOk_restore harrs) (by omega)
  let C_total := 4 * C_F + 4 * C_R + 1200
  let c_total := 3 * c_F + 3 * c_R + 5
  refine ⟨restoreProg a a_mk a_base P_flow P_repl r_base, C_total, c_total, ?_⟩
  intro w N inst_dec H S D v M recs₀ k s hw hinst hD hvS hvM hR3 hR2 hrv hmk hbuf hk
  have : inst_dec = instDecidableEqFin N := Subsingleton.elim _ _
  subst this
  have hb0 := wordSize_subprog_bounds (K := H) (L_mult := M.length)
    (by have := instSize_pos N H; omega) hw
  have hw1 : 1 < 2 ^ w := hb0.2.2.2.2.1
  have h0w : 0 < 2 ^ w := by omega
  have hMw : M.length < 2 ^ w := by have := hb0.2.2.2.1; omega
  have hno_a : ∀ d, a_base + d ∉ a.list := fun d => add_not_mem_instArrs_of_arrsOk harrs
  have hcyc_ne : ∀ d, a_base + d ≠ a.cyc :=
    fun d e => hno_a d (e ▸ by simp [InstArrs.list])
  have hmk_lt : a_mk < a_base := harrs.2 a_mk (by simp)
  have hrec_lt : a_rec < a_base := harrs.2 a_rec (by simp)
  have hD_len : D.length ≤ N := isCycleList_length_le_fin hD
  -- Step 1: allowFromListProg on a.cyc into a_base + 4
  obtain ⟨s₁, t₁, hex₁, ht₁, hr₁, ha₁, hcyc_ind₁⟩ :=
    allowFromListProg_exec a a.cyc (a_base + 4) (r_base + 5)
      hinst hinst.2.2.2.2 hD_len (hcyc_ne 4) hb0.2.2.1
  have hinst₁ : IsInstanceAt a H S D s₁ :=
    hinst.of_keeps_disjoint (fun x hx => ha₁ x (fun e => hno_a 4 (e ▸ hx)))
  -- Step 2: r_m := len a_mk; r_j := 0
  have hmk_len₁ : (s₁.arrs a_mk).length = M.length := by
    rw [ha₁ a_mk (by omega), hmk, List.length_map]
  set s₂ := s₁.setReg (r_base + 1) M.length
  have hex₂ : Exec w (.assign (r_base + 1) (.len a_mk)) s₁ s₂ 2 :=
    .assign (by rw [← hmk_len₁]; exact eval_len rfl (by rw [hmk_len₁]; exact hMw))
  set s₃ := s₂.setReg (r_base + 2) 0
  have hex₃ : Exec w (.assign (r_base + 2) (.const 0)) s₂ s₃ 2 := .assign (eval_const h0w)
  -- Step 3: forUp loop over j = 0 .. M.length - 1
  let I : ℕ → State → Prop := fun j st =>
    st.regs r_base = v.val ∧ st.regs (r_base + 1) = M.length ∧ st.regs (r_base + 2) = j ∧
    st.arrs a_mk = M.map Fin.val ∧
    st.arrs (a_base + 4) = List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) ∧
    (st.arrs a_rec).length = (s.arrs a_rec).length ∧
    KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s st ∧
    ∃ (H_cur : SimpleGraph (Fin N)) (S_cur : Finset (Fin N)) (rs : List (ReplRecord (Fin N)))
      (k_cur : ℕ),
      IsInstanceAt a H_cur S_cur D st ∧ HP25.IsCycleList H_cur D ∧
      v ∈ S_cur ∧
      RootedConn (apex H_cur D) (apexVerts (S_cur : Set (Fin N))) none 3 ∧
      RootedConn (apex H_cur D) (restoreVerts (S_cur : Set (Fin N)) v) none 2 ∧
      IsRestoreRun D v (M.take j) H (S : Set (Fin N)) H_cur (S_cur : Set (Fin N)) rs ∧
      IsRecBufAt a_rec r_rec (recs₀ ++ rs.map CrossRecord.repl) k_cur st ∧
      H_cur.edgeSet.ncard + 3 * S_cur.card ≤ H.edgeSet.ncard + 3 * S.card ∧
      k ≤ k_cur + j * (4 * C_R * instSize N H)
  have hkeep₃ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s₃ := by
    refine ⟨fun r₀ hr₀ _ => ?_, fun x hx _ => ?_⟩
    · simp only [s₃, s₂, State.setReg_regs_ne _ _ (show r₀ ≠ r_base + 2 by omega),
        State.setReg_regs_ne _ _ (show r₀ ≠ r_base + 1 by omega)]
      exact hr₁ r₀ (by omega)
    · simp only [s₃, s₂, State.setReg_arrs]
      exact ha₁ x (by omega)
  have hI0 : I 0 s₃ := by
    refine ⟨by simp [s₃, s₂, hr₁ r_base (by omega), hrv],
      by simp [s₃, s₂], by simp [s₃],
      by simp [s₃, s₂, ha₁ a_mk (by omega), hmk],
      hcyc_ind₁,
      by simp [s₃, s₂, ha₁ a_rec (by omega)],
      hkeep₃,
      H, S, [], k, hinst₁, hD, hvS, hR3, hR2, ⟨rfl, rfl, rfl⟩, ?_, le_rfl, by omega⟩
    simp only [List.map_nil, List.append_nil]
    exact hbuf.of_arrs_regs_eq (ha₁ a_rec (by omega))
      (by simp [s₃, s₂, show r_rec ≠ r_base + 2 by omega, show r_rec ≠ r_base + 1 by omega,
        hr₁ r_rec (by omega)])
  let B := (4 * C_F + 4 * C_R + 1000) * instSize N H
  have hM_cap : M.length * (4 * C_R * instSize N H) ≤ k := by
    have : M.length * (4 * C_R * instSize N H) ≤ C_total * (M.length + 1) * instSize N H := by
      dsimp only [C_total]
      have : (4 * C_F + 4 * C_R + 1200) * (M.length + 1) * instSize N H =
          M.length * (4 * C_R * instSize N H) +
          (4 * C_F + 1200) * (M.length + 1) * instSize N H + 4 * C_R * instSize N H := by ring
      omega
    omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hIM⟩ := forUp_exec' I M.length B
    (r_i := r_base + 2) (hi := .reg (r_base + 1))
    (body := restoreBodyProg a a_mk a_base (a_base + 1) (a_base + 2) (a_base + 3)
      (a_base + 4) (a_base + 5) (a_base + 6) (a_base + 7) (a_base + 8)
      P_flow P_repl r_base (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5))
    hw1 hMw
    (fun j _ st hI => ⟨hI.2.2.1, eval_reg hI.2.1 hMw⟩)
    (fun j hj st hI => by
      obtain ⟨hrv_j, hrm_j, hrj_j, hmk_j, hcyc_j, hlen_j, hkeep_j,
        H_cur, S_cur, rs_j, k_cur, hinst_j, hD_j, hvS_j, hR3_j, hR2_j,
        hrun_j, hbuf_j, hpot_j, hk_j⟩ := hI
      have hK_sz := (instSize_le_four_mul_of_edge_pot hpot_j).2
      have hwb := wordSize_subprog_bounds hK_sz hw
      have hk_rem : 4 * C_R * instSize N H ≤ k_cur := by
        have : (j + 1) * (4 * C_R * instSize N H) ≤ M.length * (4 * C_R * instSize N H) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      obtain ⟨st', t', H', S', rs', k', hex_b, ht_b, hinst', hD', hvS', hR3', hR2',
        hrun', hbuf', hpot', hlen', hk', hkeep', hrv', hrm', hrj', hmk', hcyc'⟩ :=
        restoreBodyProg_exec a a_mk a_rec r_rec a_base r_base harrs hr_rec hP_flow hP_repl
          hj hvM hinst_j hD_j hvS_j hR3_j hR2_j hrun_j hbuf_j hpot_j hlen_j hk_rem
          hkeep_j hrv_j hrm_j hrj_j hmk_j hcyc_j hwb.1 hwb.2.1 hwb.2.2.1 hwb.2.2.2.1
      refine ⟨st', t', hex_b, ht_b, ?_, hrj'⟩
      refine ⟨by simp [hrv'], by simp [hrm'], by simp, hmk', hcyc', hlen',
        hkeep'.setReg_ge (by omega) _, H', S', rs', k',
        hinst'.of_keeps_disjoint (fun _ _ => rfl), hD', hvS', hR3', hR2', hrun',
        hbuf'.of_arrs_regs_eq rfl (by simp [show r_rec ≠ r_base + 2 by omega]),
        hpot', ?_⟩
      rw [Nat.add_mul, Nat.one_mul]
      omega)
    s₃ hI0
  obtain ⟨_, _, _, _, _, hlen₄, hkeep₄, H', S', rs, k',
    hinst₄, _, _, _, _, hrun₄, hbuf₄, _, hk₄⟩ := hIM
  rw [List.take_length] at hrun₄
  have ht_total : t₁ + (2 + (2 + t₄)) ≤ C_total * (M.length + 1) * instSize N H := by
    simp only [Expr.cost, B] at ht₄
    have hsz_pos : 1 ≤ instSize N H := instSize_pos N H
    have hM_le : M.length ≤ M.length * instSize N H := by
      simpa using Nat.mul_le_mul_left M.length hsz_pos
    have hring : C_total * (M.length + 1) * instSize N H + 7 * M.length =
        M.length * (1 + 6 + (4 * C_F + 4 * C_R + 1000) * instSize N H) +
        200 * (M.length * instSize N H) +
        (4 * C_F + 4 * C_R) * instSize N H + 1200 * instSize N H := by
      dsimp only [C_total]; ring
    omega
  have hk_total : k ≤ k' + C_total * (M.length + 1) * instSize N H := by
    have : M.length * (4 * C_R * instSize N H) ≤ C_total * (M.length + 1) * instSize N H := by
      dsimp only [C_total]
      have : (4 * C_F + 4 * C_R + 1200) * (M.length + 1) * instSize N H =
          M.length * (4 * C_R * instSize N H) +
          (4 * C_F + 1200) * (M.length + 1) * instSize N H + 4 * C_R * instSize N H := by ring
      omega
    omega
  exact ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ht_total, hkeep₄,
    H', S', rs, k', hrun₄, hinst₄, hbuf₄, hlen₄, hk_total⟩

/-! ### Disproof of `RestoreRecProgClaim` and `RestoreProgClaim` without `v ∉ M` -/

/-- When `v ∈ S` and `v ∉ D`, no restoration step can exist for the marker `z = v` because
`some v ∉ restoreVerts S v`. -/
theorem not_exists_isRestoreStep_self {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {S : Set V} {D : List V} {v : V}
    (hvS : v ∈ S) (hvD : v ∉ D) :
    ¬ ∃ (H' : SimpleGraph V) (S' : Set V) (rec : Option (ReplRecord V)),
        IsRestoreStep D v v H S H' S' rec := by
  rintro ⟨H', S', rec, hstep⟩
  have hnot_mem : (some v : Option V) ∉ restoreVerts S v := by
    simp [restoreVerts]
  rcases hstep with ⟨hskip, _, _, _⟩ | ⟨_, _, _, p, q, _, hmax, _, _, _⟩
  · rcases hskip with hvS' | hvD' | hunsep
    · exact hvS' hvS
    · exact hvD hvD'
    · obtain ⟨w, hw⟩ := hunsep ∅ (by simp) (by simp)
      have hstart := hw (some v) w.start_mem_support
      exact hnot_mem hstart.1
  · exact hnot_mem (mem_of_isMaxSourceSeparator_pair hmax)

/-- When `v ∈ S` and `v ∉ D`, no restoration run can exist for `M = [v]`. -/
theorem not_exists_isRestoreRun_singleton_self {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {S : Set V} {D : List V} {v : V}
    (hvS : v ∈ S) (hvD : v ∉ D) :
    ¬ ∃ (H' : SimpleGraph V) (S' : Set V) (rs : List (ReplRecord V)),
        IsRestoreRun D v [v] H S H' S' rs := by
  rintro ⟨H', S', rs, H₁, S₁, rec, _, hstep, _, _⟩
  exact not_exists_isRestoreStep_self hvS hvD ⟨H₁, S₁, rec, hstep⟩

/-- Canonical adjacency list family for any graph `H : SimpleGraph (Fin N)`. -/
noncomputable def canonicalAdjLists {N : ℕ} (H : SimpleGraph (Fin N)) (x : ℕ) : List ℕ :=
  if hx : x < N then
    ((List.finRange N).filter (fun y => decide (H.Adj ⟨x, hx⟩ y))).map Fin.val
  else []

theorem isAdjListFamily_canonicalAdjLists {N : ℕ} (H : SimpleGraph (Fin N)) :
    IsAdjListFamily H (fun x : Fin N => canonicalAdjLists H x.val) := by
  intro x
  dsimp only
  have h_eq : canonicalAdjLists H x.val =
      ((List.finRange N).filter (fun y => decide (H.Adj x y))).map Fin.val := by
    simp [canonicalAdjLists, x.isLt]
  rw [h_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hy
    exact u.isLt
  · exact ((List.nodup_finRange N).filter _).map Fin.val_injective
  · rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (by simp)
  · intro y
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact ⟨fun ⟨u, hadj, heq⟩ => Fin.ext heq ▸ hadj, fun hadj => ⟨y, hadj, rfl⟩⟩

/-- Existence of a memory state storing any valid instance `(H, Finset.univ, D)` along with
`a_mk`, `a_rec`, `r_base`, and `r_rec`. -/
theorem exists_state_isInstanceAt_univ {N : ℕ} (H : SimpleGraph (Fin N))
    (D M : List (Fin N)) (v : Fin N) (k : ℕ) :
    let a : InstArrs := ⟨0, 1, 2, 3, 4⟩
    ∃ s : State,
      IsInstanceAt a H Finset.univ D s ∧
      s.regs 1 = v.val ∧
      s.arrs 5 = M.map Fin.val ∧
      IsRecBufAt 6 0 ([] : List (CrossRecord (Fin N))) k s ∧
      (k = 0 → IsRecordsAt 6 ([] : List (CrossRecord (Fin N))) s) := by
  intro a
  let L := canonicalAdjLists H
  let s : State :=
    { regs := fun r => if r = 0 then 0 else v.val
      arrs := fun x =>
        if x = 0 then List.ofFn (fun _ : Fin N => 1)
        else if x = 1 then (List.range N).map (fun i => (flatUpTo L i).length)
        else if x = 2 then (List.range N).map (fun i => (flatUpTo L (i + 1)).length)
        else if x = 3 then flatUpTo L N
        else if x = 4 then D.map Fin.val
        else if x = 5 then M.map Fin.val
        else if x = 6 then List.replicate k 0
        else [] }
  have hfam : IsAdjListFamily H (fun x : Fin N => L x.val) :=
    isAdjListFamily_canonicalAdjLists H
  have hlist : IsListFamily N a.st a.en a.ent (fun x : Fin N => L x.val) s :=
    isListFamily_flatUpTo (by simp [s, a]) (by simp [s, a]) (by simp [s, a])
  have hadj : IsAdjList H a.st a.en a.ent (fun x : Fin N => L x.val) s :=
    ⟨hlist, hfam⟩
  have hent_len : (s.arrs a.ent).length = 2 * H.edgeSet.ncard := by
    simp only [s, a]
    exact length_flatUpTo_eq hfam
  refine ⟨s, ⟨fun _ _ _ => Finset.mem_univ _, by simp [s, a], ⟨_, hadj⟩, hent_len, by simp [s, a]⟩,
    by simp [s], by simp [s], ?_, ?_⟩
  · refine ⟨[], List.Forall₂.nil, by simp [s], by simp [s]⟩
  · intro hk0
    exact ⟨[], List.Forall₂.nil, by simp [s, hk0]⟩

/-- `RootedConn (apex H D) (apexVerts S) none 3` implies
`RootedConn (apex H D) (restoreVerts S w) none 2` whenever `w ∈ S`. -/
theorem rootedConn_restoreVerts_of_rootedConn {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {S : Set V} {D : List V} {w : V}
    (hwS : w ∈ S) (hR3 : RootedConn (apex H D) (apexVerts S) none 3) :
    RootedConn (apex H D) (restoreVerts S w) none 2 := by
  intro X hX_sub hX_lt
  let X' : Finset (Option V) := insert (some w) X
  have hX'_sub : (X' : Set (Option V)) ⊆ apexVerts S \ {none} := by
    intro z hz
    rw [Finset.mem_coe, Finset.mem_insert] at hz
    rcases hz with rfl | hzX
    · exact ⟨Or.inr ⟨w, hwS, rfl⟩, by simp⟩
    · exact ⟨(hX_sub hzX).1.1, (hX_sub hzX).2⟩
  have hX'_lt : X'.card < 3 := by
    dsimp only [X']
    have := Finset.card_insert_le (some w) X
    omega
  have hconn := hR3 X' hX'_sub hX'_lt
  have hset_eq : restoreVerts S w \ (X : Set (Option V)) = apexVerts S \ (X' : Set (Option V)) := by
    ext z
    simp only [restoreVerts, X', Finset.coe_insert, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_insert_iff, Finset.mem_coe, not_or]
    tauto
  rwa [hset_eq]

/-- Counterexample instance on `Fin 4`: `H = ⊤`, `S = Finset.univ`, `D = [0, 1, 2]` satisfies
`RootedConn (apex H D) (apexVerts S) none 3`. -/
theorem rootedConn_counterexample_fin4 :
    RootedConn (apex (⊤ : SimpleGraph (Fin 4)) ([0, 1, 2] : List (Fin 4)))
      (apexVerts ((Finset.univ : Finset (Fin 4)) : Set (Fin 4))) none 3 := by
  intro X hX_sub hX_lt
  let T' : Set (Option (Fin 4)) :=
    apexVerts ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)) \ (X : Set (Option (Fin 4)))
  have hnone_not_X : (none : Option (Fin 4)) ∉ X := fun h => (hX_sub h).2 rfl
  have hnone_mem : (none : Option (Fin 4)) ∈ T' := ⟨Or.inl rfl, hnone_not_X⟩
  have hd_ex : ∃ d : Fin 4, d ∈ ([0, 1, 2] : List (Fin 4)) ∧ (some d : Option (Fin 4)) ∉ X := by
    by_contra! hall
    have hsub : ({some (0 : Fin 4), some 1, some 2} : Finset (Option (Fin 4))) ⊆ X := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hall 0 (by decide)
      · exact hall 1 (by decide)
      · exact hall 2 (by decide)
    have hcard := Finset.card_le_card hsub
    have h3 : ({some (0 : Fin 4), some 1, some 2} : Finset (Option (Fin 4))).card = 3 := by decide
    omega
  obtain ⟨d, hdD, hdX⟩ := hd_ex
  have hd_mem : (some d : Option (Fin 4)) ∈ T' :=
    ⟨Or.inr ⟨d, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩, hdX⟩
  have hd_none : (apex (⊤ : SimpleGraph (Fin 4)) [0, 1, 2]).Adj (some d) none := hdD
  have hreach_d : ReachIn (apex (⊤ : SimpleGraph (Fin 4)) [0, 1, 2]) T' (some d) none :=
    ⟨.cons hd_none .nil, fun y hy => by
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hy
      rcases hy with rfl | rfl
      · exact hd_mem
      · exact hnone_mem⟩
  have hreach_none : ∀ z ∈ T', ReachIn (apex (⊤ : SimpleGraph (Fin 4)) [0, 1, 2]) T' z none := by
    intro z hz
    rcases z with _ | u
    · exact ReachIn.refl hnone_mem
    · by_cases hud : u = d
      · subst hud; exact hreach_d
      · have hu_d : (apex (⊤ : SimpleGraph (Fin 4)) [0, 1, 2]).Adj (some u) (some d) := hud
        have hreach_ud : ReachIn (apex (⊤ : SimpleGraph (Fin 4)) [0, 1, 2]) T' (some u) (some d) :=
          ⟨.cons hu_d .nil, fun y hy => by
            simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
              or_false] at hy
            rcases hy with rfl | rfl
            · exact hz
            · exact hd_mem⟩
        exact ReachIn.trans hreach_ud hreach_d
  exact ⟨⟨none, hnone_mem⟩, fun a ha b hb =>
    ReachIn.trans (hreach_none a ha) (ReachIn.symm (hreach_none b hb))⟩

/-- `RestoreRecProgClaim` is false as stated in `SpecsCrossingRec.lean` because it omits `v ∉ M`
(when `v = 3 ∈ S \ D` and `M = [3]`, no `IsRestoreRun` exists). -/
theorem not_restoreRecProgClaim : ¬ RestoreRecProgClaim := by
  intro hclaim
  let a : InstArrs := ⟨0, 1, 2, 3, 4⟩
  have harrs : ArrsOk (a.list ++ [5, 6]) 7 :=
    ⟨by simp [a, InstArrs.list], fun x hx => by simp [a, InstArrs.list] at hx; omega⟩
  obtain ⟨P, C, c, hP⟩ := hclaim a 5 6 0 7 1 harrs (by omega)
  let H4 : SimpleGraph (Fin 4) := ⊤
  let S4 : Finset (Fin 4) := Finset.univ
  let D4 : List (Fin 4) := [0, 1, 2]
  let v4 : Fin 4 := 3
  let M4 : List (Fin 4) := [3]
  let k := C * (M4.length + 1) * instSize 4 H4
  obtain ⟨s, hinst, hrv, hmk, hbuf, _⟩ := exists_state_isInstanceAt_univ H4 D4 M4 v4 k
  let w := wordSize c ((M4.length + 1) * instSize 4 H4 + (s.arrs 6).length)
  have hD4 : HP25.IsCycleList H4 D4 :=
    ⟨by simp [D4], by simp [D4], fun p hp => by
      change p ∈ ([(0, 1), (1, 2), (2, 0)] : List (Fin 4 × Fin 4)) at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · decide
      · rcases List.mem_cons.mp hp with rfl | hp
        · decide
        · rcases List.mem_singleton.mp hp with rfl
          decide⟩
  have hv4S : v4 ∈ S4 := Finset.mem_univ _
  have hR3 : RootedConn (apex H4 D4) (apexVerts (S4 : Set (Fin 4))) none 3 :=
    rootedConn_counterexample_fin4
  have hR2 : RootedConn (apex H4 D4) (restoreVerts (S4 : Set (Fin 4)) v4) none 2 :=
    rootedConn_restoreVerts_of_rootedConn (Finset.mem_coe.mpr hv4S) hR3
  obtain ⟨s', t, _, _, _, H', S', rs, _, hrun, _, _, _, _⟩ :=
    hP w 4 H4 S4 D4 v4 M4 [] k s le_rfl hinst hD4 hv4S hR3 hR2 hrv hmk hbuf le_rfl
  exact not_exists_isRestoreRun_singleton_self (Finset.mem_coe.mpr hv4S) (by decide)
    ⟨H', S', rs, hrun⟩

/-- `RestoreProgClaim` is false as stated in `SpecsCrossing.lean` because it omits `v ∉ M`. -/
theorem not_restoreProgClaim : ¬ RestoreProgClaim := by
  intro hclaim
  let a : InstArrs := ⟨0, 1, 2, 3, 4⟩
  have harrs : ArrsOk (a.list ++ [5, 6]) 7 :=
    ⟨by simp [a, InstArrs.list], fun x hx => by simp [a, InstArrs.list] at hx; omega⟩
  obtain ⟨P, C, c, hP⟩ := hclaim a 5 6 7 1 harrs
  let H4 : SimpleGraph (Fin 4) := ⊤
  let S4 : Finset (Fin 4) := Finset.univ
  let D4 : List (Fin 4) := [0, 1, 2]
  let v4 : Fin 4 := 3
  let M4 : List (Fin 4) := [3]
  obtain ⟨s, hinst, hrv, hmk, _, hrec0⟩ := exists_state_isInstanceAt_univ H4 D4 M4 v4 0
  let w := wordSize c ((M4.length + 1) * instSize 4 H4 + (s.arrs 6).length)
  have hD4 : HP25.IsCycleList H4 D4 :=
    ⟨by simp [D4], by simp [D4], fun p hp => by
      change p ∈ ([(0, 1), (1, 2), (2, 0)] : List (Fin 4 × Fin 4)) at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · decide
      · rcases List.mem_cons.mp hp with rfl | hp
        · decide
        · rcases List.mem_singleton.mp hp with rfl
          decide⟩
  have hv4S : v4 ∈ S4 := Finset.mem_univ _
  have hR3 : RootedConn (apex H4 D4) (apexVerts (S4 : Set (Fin 4))) none 3 :=
    rootedConn_counterexample_fin4
  have hR2 : RootedConn (apex H4 D4) (restoreVerts (S4 : Set (Fin 4)) v4) none 2 :=
    rootedConn_restoreVerts_of_rootedConn (Finset.mem_coe.mpr hv4S) hR3
  obtain ⟨s', t, _, _, _, H', S', rs, hrun, _, _, _⟩ :=
    hP w 4 H4 S4 D4 v4 M4 [] s le_rfl hinst hD4 hv4S hR3 hR2 hrv hmk (hrec0 rfl)
  exact not_exists_isRestoreRun_singleton_self (Finset.mem_coe.mpr hv4S) (by decide)
    ⟨H', S', rs, hrun⟩

end GraphMinor.Compute.Crossing
