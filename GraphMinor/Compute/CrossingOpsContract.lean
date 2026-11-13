module

public import GraphMinor.Compute.CrossingOpsCopy
public import GraphMinor.Compute.SpecsCrossingRec
public import GraphMinor.Compute.CrossingOpsRecord
public import GraphMinor.Compute.CrossingOpsContractBody

/-!
# The contraction program

Section 9 of `docs/crossing/crossing_extractor.tex`: "Contract $uv$ to a new vertex $w$, suppressing
loops and duplicate edges. If $u\notin V(D)$, the cycle is unchanged. If both ends are on $D$,
remove $u$ from the cyclic list and keep the name $v$ for $w$." Section 11: "The record stores the
graph and the cycle before the contraction, and the edge $uv$."

The program `contractProg` works in five phases:
1. `contrPre`: copy the instance into scratch arrays, and look whether `u` and `v` are on `D`;
2. `contrEnc`: write the encoding of the record (`IsRecordEnc`);
3. `contrApp`: append it to the array of records (`appendRecProg`);
4. `contrRebuild`: rebuild the adjacency lists, vertex by vertex (`vertexLoopProg` with
   `contrBody`), into the arrays of the instance;
5. `contrFinish`: delete `u` from the vertex set and from the cycle.

The scratch arrays are `A = a_base, …, A + 8`: the copied lists in `A`, `A + 1`, `A + 2`, the
marks in `A + 3`, the buffer in `A + 4`, the copied vertex set and cycle in `A + 5`, `A + 6`, the
encoding in `A + 7` and a scratch copy of the records in `A + 8`. The registers are
`R = r_base` (`u`), `R + 1` (`v`) and the scratch registers `R + 2, …, R + 17`.

`ContractProgClaim` cannot be met as stated: appending a record makes a new array of records,
which costs its length (`Exec.length_eq_or_le`), and that length is not bounded by the size of the
instance. The corrected claim `ContractLenProgClaim` adds the length of the array of records to
the time bound, and it is proved (`contractLenProgClaim_proved`).
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### The corrected claim -/

/-- **The contraction** (Section 9), with the time bound corrected to
`C (N + |E(G)| + 1 + |a_rec|)`: "Contract $uv$ to a new vertex $w$, suppressing loops and duplicate
edges." This is `ContractProgClaim` with the length of the array of records added to the time bound.
-/
def ContractLenProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_rec]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (G : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (u v : Fin N) (recs : List (CrossRecord (Fin N)))
      (s : State),
      wordSize c (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → IsTrialEdge G D u v →
      s.regs r_base = u.val → s.regs (r_base + 1) = v.val → IsRecordsAt a_rec recs s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (instSize N G + (s.arrs a_rec).length) ∧
        KeepsBelow r_base a_base [] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a (contractGraph G u v) (S.erase u) (contractCycle D u) s' ∧
        IsRecordsAt a_rec (recs ++ [CrossRecord.contr
          { graph := G, verts := (S : Set (Fin N)), cycle := D, u := u, v := v }]) s'


/-! ### Facts about lists -/

theorem length_filter_ne_add {l : List ℕ} (hl : l.Nodup) (u : ℕ) :
    (l.filter (fun y => y ≠ u)).length + (if u ∈ l then 1 else 0) = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    by_cases hau : a = u
    · subst hau
      simp [List.filter_cons]
      exact fun y hy e => hl.1 (e ▸ hy)
    · have := ih hl.2
      have e1 : (a :: l).filter (fun y => y ≠ u) = a :: l.filter (fun y => y ≠ u) := by
        simp [List.filter_cons, hau]
      have e2 : (if u ∈ a :: l then 1 else 0) = (if u ∈ l then 1 else 0) := by
        simp [Ne.symm hau]
      rw [e1, e2, List.length_cons, List.length_cons]
      omega

theorem length_contrList_le {N : ℕ} (lists : Fin N → List ℕ) (u v x : ℕ) :
    (contrList lists u v x).length ≤
      (listOf lists x).length + (if x = v then (listOf lists u).length else 0) := by
  unfold contrList
  by_cases h1 : x = u
  · simp [h1]
  · by_cases h2 : x = v
    · subst h2
      simp only [h1, if_false, if_true, contrListV, List.length_append]
      have := List.length_filter_le (fun y => decide (y ≠ u)) (listOf lists x)
      have := List.length_filter_le (fun y => decide (y ≠ x ∧ y ∉ listOf lists x))
        (listOf lists u)
      omega
    · simp only [h1, h2, if_false, Nat.add_zero]
      unfold contrListO
      split_ifs
      · exact List.length_filter_le _ _
      · simp

theorem length_flatUpTo_contrList {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (u v : ℕ) (hu : u < N) (hv : v < N) :
    (flatUpTo (contrList lists u v) N).length ≤ 2 * G.edgeSet.ncard + N := by
  have h1 : ∑ x ∈ Finset.range N, (listOf lists x).length = 2 * G.edgeSet.ncard := by
    have := length_flatUpTo_eq (H := G) (L := listOf lists) (by
      intro x; simpa [listOf_fin] using h x)
    rw [← this, length_flatUpTo]
  have h2 : ∑ x ∈ Finset.range N, (if x = v then (listOf lists u).length else 0) =
      (listOf lists u).length := by
    rw [Finset.sum_ite_eq']; simp [hv]
  have h3 : (listOf lists u).length ≤ N := by
    rw [show u = (⟨u, hu⟩ : Fin N).val from rfl, listOf_fin]; exact (h _).2.2.1
  rw [length_flatUpTo]
  calc ∑ x ∈ Finset.range N, (contrList lists u v x).length
      ≤ ∑ x ∈ Finset.range N, ((listOf lists x).length +
          (if x = v then (listOf lists u).length else 0)) :=
        Finset.sum_le_sum fun x _ => length_contrList_le lists u v x
    _ ≤ 2 * G.edgeSet.ncard + N := by rw [Finset.sum_add_distrib, h1, h2]; omega

theorem ofFn_set_erase {N : ℕ} (S : Finset (Fin N)) (u : Fin N) :
    (List.ofFn (fun x : Fin N => if x ∈ S then 1 else 0)).set u.val 0 =
      List.ofFn (fun x : Fin N => if x ∈ S.erase u then 1 else 0) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_set, List.getElem_ofFn, Finset.mem_erase]
  split_ifs with h3 h4 h5 <;> first | rfl | (exfalso; simp_all [Fin.ext_iff])

/-! ### The phases -/

/-- The scratch copy of the instance. -/
def bArrs (A : ℕ) : InstArrs := ⟨A + 5, A, A + 1, A + 2, A + 6⟩

/-- Set the flag `R + 9` when the entry in `R + 5` is `u`, and `R + 10` when it is `v`. -/
def flagBody (R : ℕ) : Cmd :=
  .seq (.ite (.op .eq (.reg (R + 5)) (.reg R)) (.assign (R + 9) (.const 1)) .skip)
    (.ite (.op .eq (.reg (R + 5)) (.reg (R + 1))) (.assign (R + 10) (.const 1)) .skip)

/-- Phase 1: copy the instance, and look whether `u` and `v` are on the cycle. -/
def contrPre (a : InstArrs) (A R : ℕ) : Cmd :=
  .seq (copyInstanceProg a (bArrs A) (R + 15))
    (.seq (.assign (R + 8) (.len (A + 5)))
      (.seq (.assign (R + 9) (.const 0))
        (.seq (.assign (R + 10) (.const 0))
          (.seq (.alloc (A + 4) (.const 0))
            (.seq (.assign (R + 7) (.const 0))
              (forArrProg (A + 6) (R + 12) (R + 14) (R + 5) (flagBody R)))))))

/-- The degree of `v` in the copied lists. -/
def degE (A R : ℕ) : Expr :=
  .op .sub (.read (A + 1) (.reg (R + 1))) (.read A (.reg (R + 1)))

/-- Phase 2: the encoding of the record in `A + 7`. -/
def contrEnc (A R : ℕ) : Cmd :=
  .seq (.alloc (A + 7) (.op .add (degE A R) (.const 7)))
    (.seq (.assign (R + 7) (.const 0))
      (.seq (emitProg (A + 7) (R + 7) (.const 1))
        (.seq (emitProg (A + 7) (R + 7) (.reg R))
          (.seq (emitProg (A + 7) (R + 7) (.reg (R + 1)))
            (.seq (emitProg (A + 7) (R + 7) (.reg (R + 9)))
              (.seq (emitProg (A + 7) (R + 7) (.reg (R + 10)))
                (.seq (emitProg (A + 7) (R + 7) (degE A R))
                  (.seq (forList A (A + 1) (A + 2) (R + 1) (R + 3) (R + 4) (R + 5)
                      (emitProg (A + 7) (R + 7) (.reg (R + 5))))
                    (emitProg (A + 7) (R + 7) (.op .add (degE A R) (.const 6)))))))))))

/-- Phase 3: append the encoding to the records. -/
def contrApp (a_rec A R : ℕ) : Cmd :=
  .seq (.assign (R + 11) (.op .add (.op .add (.len a_rec) (.len (A + 7)))
      (.op .add (.reg (R + 8)) (.const 2))))
    (appendRecProg a_rec (A + 7) (A + 8) (R + 11) (R + 12) (R + 13) (R + 14))

/-- Phase 4: rebuild the adjacency lists into the arrays of the instance. -/
def contrRebuild (a : InstArrs) (A R : ℕ) : Cmd :=
  .seq (.alloc a.st (.reg (R + 8)))
    (.seq (.alloc a.en (.reg (R + 8)))
      (.seq (.alloc (A + 4) (.op .add (.len (A + 2)) (.reg (R + 8))))
        (.seq (.alloc (A + 3) (.reg (R + 8)))
          (.seq (.assign (R + 7) (.const 0))
            (.seq (.assign (R + 2) (.const 0))
              (.seq (vertexLoopProg (R + 2) (R + 8) (R + 7) a.st a.en (contrBody A R))
                (.seq (.assign (R + 14) (.reg (R + 7)))
                  (.seq (.assign (R + 11) (.reg (R + 8)))
                    (copyMinNProg (A + 4) a.ent (R + 11) (R + 12) (R + 14))))))))))

/-- Phase 5: delete `u` from the vertex set and from the cycle. -/
def contrFinish (a : InstArrs) (A R : ℕ) : Cmd :=
  .seq (.write a.alive (.reg R) (.const 0))
    (.seq (.alloc a.cyc (.op .sub (.len (A + 6)) (.reg (R + 9))))
      (.seq (.assign (R + 7) (.const 0))
        (forArrProg (A + 6) (R + 12) (R + 14) (R + 5)
          (.ite (.op .eq (.reg (R + 5)) (.reg R)) .skip (emitProg a.cyc (R + 7) (.reg (R + 5)))))))

/-- **The contraction program.** -/
def contractProg (a : InstArrs) (a_rec A R : ℕ) : Cmd :=
  .seq (contrPre a A R)
    (.seq (contrEnc A R)
      (.seq (contrApp a_rec A R)
        (.seq (contrRebuild a A R) (contrFinish a A R))))

/-- Phase 3 with the records in a buffer: copy the encoding into the free entries of the buffer,
and move the register `r_rec` that holds the length of the records. -/
def contrAppBuf (a_rec r_rec A R : ℕ) : Cmd :=
  .seq (.assign (R + 11) (.op .add (.reg (R + 8)) (.op .add (.len (A + 7)) (.const 2))))
    (.seq (.assign (R + 13) (.reg r_rec))
      (.seq (.assign (R + 14) (.len (A + 7)))
        (.seq (copyAtProg (A + 7) a_rec (R + 11) (R + 12) (R + 13) (R + 14))
          (.assign r_rec (.op .add (.reg r_rec) (.len (A + 7)))))))

/-- **The contraction program, with the records in a buffer.** -/
def contractBufProg (a : InstArrs) (a_rec r_rec A R : ℕ) : Cmd :=
  .seq (contrPre a A R)
    (.seq (contrEnc A R)
      (.seq (contrAppBuf a_rec r_rec A R)
        (.seq (contrRebuild a A R) (contrFinish a A R))))

/-! ### Tools for the proofs -/

/-- Unfold the programs, to compute the registers and arrays that they write. -/
local macro "wsimp" : tactic => `(tactic| simp [contractProg, contractBufProg, contrAppBuf, contrPre, contrEnc, contrApp,
  contrRebuild, contrFinish, Cmd.writtenRegs, Cmd.writtenArrs, copyInstanceProg, copyMinProg,
  forArrProg, flagBody, emitProg, forList, appendRecProg, concatProg, copyAtProg, vertexLoopProg,
  contrBody, contrBodyO, contrBodyV, copyMinNProg, forUp, bArrs, degE])

/-- `omega`, after unfolding the types of registers and arrays. -/
local macro "aomega" : tactic => `(tactic| ((try dsimp only [Arr, Reg] at *) <;> omega))

/-- `omega`, after computing the lengths of lists. -/
local macro "lomega" : tactic => `(tactic| ((try simp only [List.length_append, List.length_nil,
  List.length_cons, List.length_singleton, List.nil_append, List.cons_append]) <;> omega))

/-- Compute a register or an array of a state made by `setReg` and `setArr`. -/
local macro "stsimp" : tactic => `(tactic| ((try simp only [State.setReg_regs, State.setArr_regs,
  State.setReg_arrs, State.setArr_arrs, State.writeArr_regs, State.writeArr]) <;>
  (try split_ifs) <;> first | rfl | aomega | skip))

/-- Show that a register or an array is not written by a program. -/
local macro "wfr" : tactic => `(tactic| (wsimp <;> (try constructorm* _ ∧ _) <;> (try intro h) <;>
  (try dsimp only [Arr, Reg] at h ⊢) <;> omega))

theorem IsInstanceAt.of_arrs_eq {N : ℕ} {a : InstArrs} {G : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)} {s s' : State} (h : IsInstanceAt a G S D s)
    (heq : ∀ x ∈ a.list, s'.arrs x = s.arrs x) : IsInstanceAt a G S D s' := by
  obtain ⟨h1, h2, ⟨lists, h3⟩, h4, h5⟩ := h
  have e1 := heq a.alive (by simp [InstArrs.list])
  have e2 := heq a.st (by simp [InstArrs.list])
  have e3 := heq a.en (by simp [InstArrs.list])
  have e4 := heq a.ent (by simp [InstArrs.list])
  have e5 := heq a.cyc (by simp [InstArrs.list])
  exact ⟨h1, by rw [e1]; exact h2, ⟨lists, h3.of_arrs_eq e2 e3 e4⟩, by rw [e4]; exact h4,
    by rw [e5]; exact h5⟩

theorem val_mem_map {N : ℕ} {D : List (Fin N)} {x : Fin N} : x.val ∈ D.map Fin.val ↔ x ∈ D :=
  List.mem_map_of_injective Fin.val_injective

theorem ite_mem_take_succ {l : List ℕ} {j : ℕ} (hj : j < l.length) (x : ℕ) :
    (if x ∈ l.take (j + 1) then 1 else 0) =
      if l[j] = x then 1 else (if x ∈ l.take j then 1 else 0) := by
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.mem_append, List.mem_singleton]
  by_cases h : l[j] = x
  · simp [h]
  · have : x ≠ l[j] := fun e => h e.symm
    simp [h, this]

/-- A test that sets a flag. -/
theorem flag_exec {w : ℕ} {r₁ r₂ rf : Reg} {s : State} {a b : ℕ} (h₁ : s.regs r₁ = a)
    (h₂ : s.regs r₂ = b) (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (.ite (.op .eq (.reg r₁) (.reg r₂)) (.assign rf (.const 1)) .skip) s s' t ∧
      t ≤ 5 ∧ s'.arrs = s.arrs ∧ s'.regs rf = (if a = b then 1 else s.regs rf) ∧
      ∀ r, r ≠ rf → s'.regs r = s.regs r := by
  by_cases hab : a = b
  · subst hab
    exact ⟨s.setReg rf 1, _, exec_ite_eq_true h₁ h₂ ha hw (.assign (eval_const hw)), by simp,
      rfl, by simp, fun r hr => State.setReg_regs_ne _ _ hr⟩
  · exact ⟨s, _, exec_ite_eq_false h₁ h₂ hab ha hb hw (.skip _), by simp, rfl, by simp [hab],
      fun _ _ => rfl⟩

/-! ### Phase 1 -/

theorem contrPre_exec {w N : ℕ} (a : InstArrs) (A R : ℕ) (hok : ArrsOk a.list A)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)} {s : State} {u v : Fin N}
    (hinst : IsInstanceAt a G S D s) (hDN : D.length ≤ N) (hw : 4 * instSize N G + 4 < 2 ^ w)
    (hu : s.regs R = u.val) (hv : s.regs (R + 1) = v.val) :
    ∃ s' t, Exec w (contrPre a A R) s s' t ∧ t ≤ 60 * instSize N G + 22 * N + 20 ∧
      IsInstanceAt (bArrs A) G S D s' ∧ (∀ x < A, s'.arrs x = s.arrs x) ∧
      (∀ r < R + 2, s'.regs r = s.regs r) ∧ s'.regs (R + 8) = N ∧
      s'.regs (R + 9) = (if u ∈ D then 1 else 0) ∧ s'.regs (R + 10) = (if v ∈ D then 1 else 0) := by
  have hok' : ArrsOk (a.list ++ (bArrs A).list) (A + 7) := by
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hok.1, by simp [bArrs, InstArrs.list] <;> omega, ?_⟩
      intro x hx y hy
      have := hok.2 x hx
      simp [bArrs, InstArrs.list] at hy
      omega
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · have := hok.2 x h; omega
      · simp [bArrs, InstArrs.list] at h; omega
  have hsz : N ≤ instSize N G := by unfold instSize; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, -, hb₁⟩ :=
    copyInstanceProg_exec a (bArrs A) (A + 7) (R + 15) hok' hinst hDN hw
  have hfa₁ : ∀ x < A, s₁.arrs x = s.arrs x := fun x hx =>
    hex₁.arrs_eq_of_not_mem_writtenArrs (by wfr)
  have hfr₁ : ∀ r < R + 15, s₁.regs r = s.regs r := fun r hr =>
    hex₁.regs_eq_of_not_mem_writtenRegs (by wfr)
  have hal₁ : s₁.arrs (A + 5) = List.ofFn (fun x : Fin N => if x ∈ S then 1 else 0) := hb₁.2.1
  have hcy₁ : s₁.arrs (A + 6) = D.map Fin.val := hb₁.2.2.2.2
  -- the assignments
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = ((((s₁.setReg (R + 8) N).setReg (R + 9) 0).setReg (R + 10) 0).setArr
      (A + 4) (List.replicate 0 0)).setReg (R + 7) 0 := ⟨_, rfl⟩
  have hlen : (Expr.len (A + 5)).eval w s₁ = some N := by
    rw [eval_len rfl (by rw [hal₁]; simpa using hNw), hal₁, List.length_ofFn]
  have hex₂ : ∀ {s' : State} {t : ℕ},
      Exec w (forArrProg (A + 6) (R + 12) (R + 14) (R + 5) (flagBody R)) s₂ s' t →
      Exec w (.seq (.assign (R + 8) (.len (A + 5))) (.seq (.assign (R + 9) (.const 0))
        (.seq (.assign (R + 10) (.const 0)) (.seq (.alloc (A + 4) (.const 0))
          (.seq (.assign (R + 7) (.const 0))
            (forArrProg (A + 6) (R + 12) (R + 14) (R + 5) (flagBody R))))))) s₁ s'
        (2 + (2 + (2 + (1 + (2 + t))))) := fun h => by
    rw [hs₂] at h
    exact .seq (.assign hlen) (.seq (.assign (eval_const (by omega))) (.seq
      (.assign (eval_const (by omega))) (.seq (.alloc (eval_const (by omega)))
        (.seq (.assign (eval_const (by omega))) h))))
  have hcy₂ : s₂.arrs (A + 6) = D.map Fin.val := by
    rw [hs₂]; simp [State.setArr_arrs, hcy₁]
  -- the loop over the cycle
  obtain ⟨l, hl⟩ : ∃ l, s₂.arrs (A + 6) = l := ⟨_, rfl⟩
  have hlD : l = D.map Fin.val := hl ▸ hcy₂
  have hll : l.length ≤ N := by rw [hlD, List.length_map]; exact hDN
  have hlt : ∀ x ∈ l, x < N := by rw [hlD]; exact vals_lt D
  let Q : ℕ → State → Prop := fun j s' => s'.arrs = s₂.arrs ∧ s'.regs R = u.val ∧
    s'.regs (R + 1) = v.val ∧ s'.regs (R + 9) = (if u.val ∈ l.take j then 1 else 0) ∧
    s'.regs (R + 10) = (if v.val ∈ l.take j then 1 else 0)
  have hQ0 : Q 0 s₂ := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> rw [hs₂] <;> simp [State.setReg_regs]
    · rw [hfr₁ R (by omega)]; exact hu
    · rw [hfr₁ (R + 1) (by omega)]; exact hv
  obtain ⟨s₃, t₃, hex₃, ht₃, hQ₃, -⟩ := forArrEmit_exec (A + 6) (R + 12) (R + 14) (R + 5)
    (A + 4) (R + 7) (flagBody R) (fun _ => []) Q 10 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hw1 (s := s₂) (pre := []) (k := 0)
    (by rw [hl]; omega) (by rw [hl]; intro x hx; have := hlt x hx; omega) hQ0
    (by rw [hs₂]; simp [IsBuf, State.setArr_arrs])
    (by simp)
    (fun j s s' hQ harr hreg => ⟨harr.trans hQ.1,
      (hreg R (by omega) (by omega) (by omega)).trans hQ.2.1,
      (hreg (R + 1) (by omega) (by omega) (by omega)).trans hQ.2.2.1,
      (hreg (R + 9) (by omega) (by omega) (by omega)).trans hQ.2.2.2.1,
      (hreg (R + 10) (by omega) (by omega) (by omega)).trans hQ.2.2.2.2⟩)
    (fun j s' hQ => by rw [hQ.1])
    (by
      intro j hj s' pre' k' hQ _ _ hy hbuf _ _
      have hj' : j < l.length := hl ▸ hj
      have hy' : s'.regs (R + 5) = l[j] := by rw [hy]; simp only [hl]
      have hyw : l[j] < 2 ^ w := by have := hlt _ (List.getElem_mem hj'); omega
      obtain ⟨sa, ta, hexa, hta, harra, hfa, hoa⟩ := flag_exec (rf := R + 9) hy' hQ.2.1 hyw
        (by omega) hw1
      obtain ⟨sb, tb, hexb, htb, harrb, hfb, hob⟩ := flag_exec (rf := R + 10) (s := sa)
        (b := v.val)
        (by rw [hoa (R + 5) (by simp)]; exact hy') (by rw [hoa (R + 1) (by simp)]; exact hQ.2.2.1) hyw
        (by omega) hw1
      refine ⟨sb, ta + tb, .seq hexa hexb, by omega, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [harrb, harra]; exact hQ.1
      · rw [hob R (by simp), hoa R (by simp)]; exact hQ.2.1
      · rw [hob (R + 1) (by simp), hoa (R + 1) (by simp)]; exact hQ.2.2.1
      · rw [hob (R + 9) (by simp), hfa, ite_mem_take_succ hj', hQ.2.2.2.1]
      · rw [hfb, hoa (R + 10) (by simp), ite_mem_take_succ hj', hQ.2.2.2.2]
      · rw [hob (R + 12) (by simp), hoa (R + 12) (by simp)]; assumption
      · rw [hob (R + 14) (by simp), hoa (R + 14) (by simp)]; assumption
      · simp only [List.append_nil, List.length_nil, Nat.sub_zero]
        exact ⟨by rw [harrb, harra]; exact hbuf.1,
          by rw [hob (R + 7) (by simp), hoa (R + 7) (by simp)]; exact hbuf.2⟩)
  simp only [Q, hl, List.take_of_length_le (le_refl _)] at hQ₃
  refine ⟨s₃, _, .seq hex₁ (hex₂ hex₃), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl] at ht₃; omega
  · refine hb₁.of_arrs_eq (fun x hx => ?_)
    rw [hQ₃.1, hs₂]
    simp only [bArrs, InstArrs.list, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> stsimp
  · intro x hx
    rw [hQ₃.1, hs₂, ← hfa₁ x hx]
    stsimp
  · intro r hr
    rw [hex₃.regs_eq_of_not_mem_writtenRegs (by wfr), hs₂, ← hfr₁ r (by omega)]
    stsimp
  · rw [hex₃.regs_eq_of_not_mem_writtenRegs (by wfr), hs₂]
    stsimp
  · rw [hQ₃.2.2.2.1, hlD]; simp only [val_mem_map]
  · rw [hQ₃.2.2.2.2, hlD]; simp only [val_mem_map]

/-! ### Phase 2 -/

/-- Emitting the value of any expression, with the frame. -/
theorem emitE_exec {w : ℕ} (a_buf r_cnt : ℕ) (val : Expr) {pre : List ℕ} {k v : ℕ} {s : State}
    (hb : IsBuf a_buf r_cnt pre (k + 1) s) (hv : val.eval w s = some v)
    (hw : pre.length + 1 < 2 ^ w) :
    ∃ s', Exec w (emitProg a_buf r_cnt val) s s' (val.cost + 6) ∧
      IsBuf a_buf r_cnt (pre ++ [v]) k s' ∧
      (∀ a, a ≠ a_buf → s'.arrs a = s.arrs a) ∧ (∀ r', r' ≠ r_cnt → s'.regs r' = s.regs r') := by
  obtain ⟨hex, hb'⟩ := emitProg_exec a_buf r_cnt val hb hv hw
  exact ⟨_, hex, hb', fun a ha => by simp [State.writeArr_arrs_ne _ _ _ ha],
    fun r' hr => by simp [State.setReg_regs, hr]⟩

theorem contrEnc_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : State} {u v : Fin N} {fu fv : ℕ}
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hent : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hu : s.regs R = u.val) (hv : s.regs (R + 1) = v.val) (hfu : fu ≤ 1) (hfv : fv ≤ 1)
    (h9 : s.regs (R + 9) = fu) (h10 : s.regs (R + 10) = fv)
    (hw : 4 * instSize N G + 4 < 2 ^ w) :
    ∃ s' t, Exec w (contrEnc A R) s s' t ∧ t ≤ 18 * N + 90 ∧
      s'.arrs (A + 7) = withLength ([1, u.val, v.val, fu, fv, (listOf lists v).length] ++
        listOf lists v) := by
  have hsz : N + 2 * G.edgeSet.ncard + 2 ≤ 2 * instSize N G := by unfold instSize; omega
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨lv, hlv⟩ : ∃ lv, listOf lists v = lv := ⟨_, rfl⟩
  have hlvN : lv.length ≤ N := by rw [← hlv, listOf_fin]; exact (hadj.2 v).2.2.1
  have hlvlt : ∀ y ∈ lv, y < N := by rw [← hlv]; exact listOf_lt hadj.2 v
  obtain ⟨st, en, hlist, hen⟩ := exists_isListAt hadj v.2
  rw [hlv] at hlist
  have hlist' := hlist
  obtain ⟨hu_st, hu_en, hen_ent, hdiff, hst, hen', hle, -⟩ := hlist'
  have hen_w : en < 2 ^ w := by rw [hent] at hen; omega
  have hst_w : st < 2 ^ w := by omega
  have hvw : v.val < 2 ^ w := by have := v.2; omega
  -- the degree of `v`
  have hdeg : ∀ s' : State, s'.regs (R + 1) = v.val → s'.arrs A = s.arrs A →
      s'.arrs (A + 1) = s.arrs (A + 1) → (degE A R).eval w s' = some lv.length := by
    intro s' h1 h2 h3
    have e1 : (Expr.read (A + 1) (.reg (R + 1))).eval w s' = some en := by
      rw [eval_read (eval_reg (w := w) h1 hvw) (by rw [h3]; exact hu_en) (by
        simp only [h3, hen']; exact hen_w)]
      simp only [h3, hen']
    have e2 : (Expr.read A (.reg (R + 1))).eval w s' = some st := by
      rw [eval_read (eval_reg (w := w) h1 hvw) (by rw [h2]; exact hu_st) (by
        simp only [h2, hst]; exact hst_w)]
      simp only [h2, hst]
    rw [degE, eval_sub e1 e2, hdiff]
  -- the allocation
  obtain ⟨sa, hsa⟩ : ∃ sa, sa = s.setArr (A + 7) (List.replicate (lv.length + 7) 0) := ⟨_, rfl⟩
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = sa.setReg (R + 7) 0 := ⟨_, rfl⟩
  have hexa : Exec w (.alloc (A + 7) (.op .add (degE A R) (.const 7))) s sa
      ((degE A R).cost + 1 + 1 + (lv.length + 7)) := by
    rw [hsa]
    exact .alloc (eval_add (hdeg s hv rfl rfl) (eval_const (by omega)) (by omega))
  have hexb : Exec w (.assign (R + 7) (.const 0)) sa s₀ 2 := by
    rw [hs₀]; exact .assign (eval_const (by omega))
  have hb₀ : IsBuf (A + 7) (R + 7) [] (lv.length + 7) s₀ := by
    rw [hs₀, hsa]; simp [IsBuf, State.setReg_regs]
  have hA₀ : ∀ a, a ≠ A + 7 → s₀.arrs a = s.arrs a := fun a ha => by
    rw [hs₀, hsa]; simp [State.setReg_arrs, State.setArr_arrs_ne _ _ ha]
  have hR₀ : ∀ r, r ≠ R + 7 → s₀.regs r = s.regs r := fun r hr => by
    rw [hs₀, hsa]; simp [State.setReg_regs, hr, State.setArr_regs]
  -- the six emits
  obtain ⟨s₁, hex₁, hb₁, hA₁, hR₁⟩ := emitE_exec (w := w) (A + 7) (R + 7) (.const 1)
    (k := lv.length + 6) hb₀ (eval_const (by omega)) (by lomega)
  obtain ⟨s₂, hex₂, hb₂, hA₂, hR₂⟩ := emitE_exec (w := w) (A + 7) (R + 7) (.reg R)
    (k := lv.length + 5) hb₁
    (eval_reg (by rw [hR₁ R (by simp), hR₀ R (by simp), hu]) (by have := u.2; omega))
    (by lomega)
  obtain ⟨s₃, hex₃, hb₃, hA₃, hR₃⟩ := emitE_exec (w := w) (A + 7) (R + 7) (.reg (R + 1))
    (k := lv.length + 4) hb₂
    (eval_reg (by rw [hR₂ (R + 1) (by simp), hR₁ (R + 1) (by simp), hR₀ (R + 1) (by simp), hv])
      (by have := v.2; omega))
    (by lomega)
  obtain ⟨s₄, hex₄, hb₄, hA₄, hR₄⟩ := emitE_exec (w := w) (A + 7) (R + 7) (.reg (R + 9))
    (k := lv.length + 3) hb₃
    (eval_reg (by rw [hR₃ (R + 9) (by simp), hR₂ (R + 9) (by simp), hR₁ (R + 9) (by simp),
      hR₀ (R + 9) (by simp), h9]) (by omega))
    (by lomega)
  obtain ⟨s₅, hex₅, hb₅, hA₅, hR₅⟩ := emitE_exec (w := w) (A + 7) (R + 7) (.reg (R + 10))
    (k := lv.length + 2) hb₄
    (eval_reg (by rw [hR₄ (R + 10) (by simp), hR₃ (R + 10) (by simp), hR₂ (R + 10) (by simp),
      hR₁ (R + 10) (by simp), hR₀ (R + 10) (by simp), h10]) (by omega))
    (by lomega)
  have hA₅' : ∀ a, a ≠ A + 7 → s₅.arrs a = s.arrs a := fun a ha => by
    rw [hA₅ a ha, hA₄ a ha, hA₃ a ha, hA₂ a ha, hA₁ a ha, hA₀ a ha]
  have hR₅' : ∀ r, r ≠ R + 7 → s₅.regs r = s.regs r := fun r hr => by
    rw [hR₅ r hr, hR₄ r hr, hR₃ r hr, hR₂ r hr, hR₁ r hr, hR₀ r hr]
  obtain ⟨s₆, hex₆, hb₆, hA₆, hR₆⟩ := emitE_exec (w := w) (A + 7) (R + 7) (degE A R)
    (k := lv.length + 1) hb₅
    (hdeg s₅ (by rw [hR₅' _ (by simp), hv]) (hA₅' _ (by simp)) (hA₅' _ (by simp)))
    (by lomega)
  have hA₆' : ∀ a, a ≠ A + 7 → s₆.arrs a = s.arrs a := fun a ha => by rw [hA₆ a ha, hA₅' a ha]
  have hR₆' : ∀ r, r ≠ R + 7 → s₆.regs r = s.regs r := fun r hr => by rw [hR₆ r hr, hR₅' r hr]
  simp only [List.nil_append, List.cons_append, List.singleton_append] at hb₆
  -- the loop over the list of `v`
  have hlist₆ : IsListAt A (A + 1) (A + 2) v.val st en lv s₆ :=
    hlist.of_arrs_eq (hA₆' _ (by simp)) (hA₆' _ (by simp)) (hA₆' _ (by simp))
  let Q : ℕ → State → Prop := fun _ s' => (∀ a, a ≠ A + 7 → s'.arrs a = s.arrs a) ∧
    (∀ r, r ≠ R + 7 → r ≠ R + 3 → r ≠ R + 4 → r ≠ R + 5 → s'.regs r = s.regs r)
  obtain ⟨s₇, t₇, hex₇, ht₇, hQ₇, hb₇⟩ := forListEmit_exec (w := w) A (A + 1) (A + 2) (R + 1)
    (R + 3) (R + 4) (R + 5) (A + 7) (R + 7) (emitProg (A + 7) (R + 7) (.reg (R + 5))) v.val st en
    lv (fun y => [y]) Q 7 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    hw1 hen_w hvw hlist₆ (by rw [hR₆' _ (by simp), hv]) (fun x hx => by have := hlvlt x hx; omega)
    ⟨hA₆', fun r h _ _ _ => hR₆' r h⟩ hb₆ (by simp)
    (fun j s s' hQ harr hreg => ⟨fun a ha => by rw [harr]; exact hQ.1 a ha,
      fun r h1 h2 h3 h4 => by rw [hreg r h2 h3 h4]; exact hQ.2 r h1 h2 h3 h4⟩)
    (fun j s' hQ => by rw [hQ.1 _ (by simp), hA₆' _ (by simp)])
    (by
      intro j hj s' pre' k' hQ hk hh hy hbuf hk1 hlen
      simp only [List.length_singleton] at hk1
      simp only [List.length_cons, List.length_nil] at hlen
      have hyw : lv[j] < 2 ^ w := by have := hlvlt _ (List.getElem_mem hj); omega
      obtain ⟨s'', hex, hb'', hA'', hR''⟩ := emitReg_exec (w := w) (A + 7) (R + 7) (R + 5)
        (k := k' - 1) (by rw [show k' - 1 + 1 = k' by omega]; exact hbuf) hy hyw (by omega)
      refine ⟨s'', 7, hex, le_refl _, ⟨fun a ha => by rw [hA'' a ha]; exact hQ.1 a ha,
        fun r h1 h2 h3 h4 => by rw [hR'' r h1]; exact hQ.2 r h1 h2 h3 h4⟩,
        by rw [hR'' _ (by simp)]; exact hk, by rw [hR'' _ (by simp)]; exact hh,
        by simpa using hb''⟩)
  have hfl : lv.flatMap (fun y => [y]) = lv := by
    induction lv with
    | nil => rfl
    | cons a l ih => simp
  rw [hfl, show lv.length + 1 - lv.length = 1 by omega] at hb₇
  obtain ⟨s₈, hex₈, hb₈, -, -⟩ := emitE_exec (w := w) (A + 7) (R + 7)
    (.op .add (degE A R) (.const 6)) (k := 0) (by rw [Nat.zero_add]; exact hb₇)
    (eval_add (hdeg s₇ (by rw [hQ₇.2 (R + 1) (by simp) (by simp) (by simp) (by simp), hv])
      (hQ₇.1 _ (by simp)) (hQ₇.1 _ (by simp))) (eval_const (by omega)) (by omega)) (by lomega)
  refine ⟨s₈, _, .seq hexa (.seq hexb (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
    (.seq hex₆ (.seq hex₇ hex₈)))))))), ?_, ?_⟩
  · simp only [degE, Expr.cost_op, Expr.cost_read, Expr.cost_reg, Expr.cost_const]
    have : lv.length * (10 + 7) ≤ 17 * N := by nlinarith
    omega
  · rw [hb₈.1, ← hlv]
    simp [withLength]

/-! ### Phase 3 -/

theorem contrApp_exec {w N : ℕ} (a_rec A R : ℕ) (hA : a_rec < A) {recs : List (CrossRecord (Fin N))}
    {s : State} (hrec : IsRecordsAt a_rec recs s)
    (henc : ∀ x ∈ s.arrs (A + 7), x ≤ N + 2 + (s.arrs (A + 7)).length)
    (h8 : s.regs (R + 8) = N)
    (hw : (s.arrs a_rec).length + (s.arrs (A + 7)).length + N + 2 < 2 ^ w) :
    ∃ s' t, Exec w (contrApp a_rec A R) s s' t ∧
      t ≤ 32 * ((s.arrs a_rec).length + (s.arrs (A + 7)).length) + 46 ∧
      s'.arrs a_rec = s.arrs a_rec ++ s.arrs (A + 7) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨B, hB⟩ : ∃ B, B = (s.arrs a_rec).length + (s.arrs (A + 7)).length + (N + 2) :=
    ⟨_, rfl⟩
  have hev : (Expr.op .add (.op .add (.len a_rec) (.len (A + 7))) (.op .add (.reg (R + 8))
      (.const 2))).eval w s = some B := by
    rw [eval_add (eval_add (eval_len rfl (by omega)) (eval_len rfl (by omega)) (by omega))
      (eval_add (eval_reg h8 (by omega)) (eval_const (by omega)) (by omega)) (by omega), hB]
  obtain ⟨s', t, hex, ht, hrec', -, -⟩ := appendRecProg_exec (w := w) a_rec (A + 7) (A + 8)
    (R + 11) (R + 12) (R + 13) (R + 14) (by omega) (by omega) (by omega) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (s := s.setReg (R + 11) B) (B := B) (by simp)
    (by omega) hw1 (by simp only [State.setReg_arrs]; omega)
    (by
      intro x hx
      simp only [State.setReg_arrs, List.mem_append] at hx
      rcases hx with hx | hx
      · have := le_of_isRecordsAt hrec x hx; omega
      · have := henc x hx; omega)
  exact ⟨s', _, .seq (.assign hev) hex, by simp only [State.setReg_arrs] at ht; simp; omega,
    by simpa using hrec'⟩

/-! ### Phase 4 -/

theorem lt_of_mem_flatUpTo {N : ℕ} {H : SimpleGraph (Fin N)} {L : ℕ → List ℕ}
    (h : IsAdjListFamily H (fun x => L x)) : ∀ y ∈ flatUpTo L N, y < N := by
  intro y hy
  simp only [flatUpTo, List.mem_flatten, List.mem_map, List.mem_range] at hy
  obtain ⟨l, ⟨x, hx, rfl⟩, hy⟩ := hy
  exact (h ⟨x, hx⟩).1 y hy

theorem contrRebuild_exec {w N : ℕ} (a : InstArrs) (A R : ℕ) (hok : ArrsOk a.list A)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {s : State} {u v : Fin N}
    (huv : G.Adj u v) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hent : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hu : s.regs R = u.val) (hv : s.regs (R + 1) = v.val) (h8 : s.regs (R + 8) = N)
    (hw : 4 * instSize N G + 4 < 2 ^ w) :
    ∃ s' t, Exec w (contrRebuild a A R) s s' t ∧ t ≤ 200 * instSize N G ∧
      s'.arrs a.st = (List.range N).map
        (fun x => (flatUpTo (contrList lists u.val v.val) x).length) ∧
      s'.arrs a.en = (List.range N).map
        (fun x => (flatUpTo (contrList lists u.val v.val) (x + 1)).length) ∧
      s'.arrs a.ent = flatUpTo (contrList lists u.val v.val) N := by
  have hnd := hok.1
  simp only [InstArrs.list, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨-, -, -, -⟩, ⟨h23, h24, -⟩, ⟨h34, -⟩, -⟩ := hnd
  have hst : a.st < A := hok.2 _ (by simp [InstArrs.list])
  have hen : a.en < A := hok.2 _ (by simp [InstArrs.list])
  have hentA : a.ent < A := hok.2 _ (by simp [InstArrs.list])
  set E := G.edgeSet.ncard with hE
  have hsz : instSize N G = N + E + 1 := rfl
  have hw1 : 1 < 2 ^ w := by omega
  set L := contrList lists u.val v.val with hL
  have hfam : IsAdjListFamily (contractGraph G u v) (fun x => L x) :=
    isAdjListFamily_contrList hadj.2 huv
  have htot : (flatUpTo L N).length ≤ 2 * E + N :=
    length_flatUpTo_contrList hadj.2 u.val v.val u.2 v.2
  obtain ⟨cap, hcap⟩ : ∃ cap, cap = (s.arrs (A + 2)).length + N := ⟨_, rfl⟩
  -- the allocations
  have hN : N < 2 ^ w := by omega
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = s.setArr a.st (List.replicate N 0) := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = s₁.setArr a.en (List.replicate N 0) := ⟨_, rfl⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s₃, s₃ = s₂.setArr (A + 4) (List.replicate cap 0) := ⟨_, rfl⟩
  obtain ⟨s₄, hs₄⟩ : ∃ s₄, s₄ = s₃.setArr (A + 3) (List.replicate N 0) := ⟨_, rfl⟩
  obtain ⟨s₅, hs₅⟩ : ∃ s₅, s₅ = s₄.setReg (R + 7) 0 := ⟨_, rfl⟩
  obtain ⟨s₆, hs₆⟩ : ∃ s₆, s₆ = s₅.setReg (R + 2) 0 := ⟨_, rfl⟩
  have hR₄ : ∀ r, s₄.regs r = s.regs r := fun r => by rw [hs₄, hs₃, hs₂, hs₁]; rfl
  have hex₁ : Exec w (.alloc a.st (.reg (R + 8))) s s₁ (1 + N) := by
    rw [hs₁]; exact .alloc (eval_reg h8 hN)
  have hex₂ : Exec w (.alloc a.en (.reg (R + 8))) s₁ s₂ (1 + N) := by
    rw [hs₂]; exact .alloc (eval_reg (by rw [hs₁]; exact h8) hN)
  have hA₂ : s₁.arrs (A + 2) = s.arrs (A + 2) := by
    rw [hs₁, State.setArr_arrs_ne _ _ (by aomega)]
  have hex₃ : Exec w (.alloc (A + 4) (.op .add (.len (A + 2)) (.reg (R + 8)))) s₂ s₃
      ((1 + 1 + 1) + cap) := by
    have e : s₂.arrs (A + 2) = s.arrs (A + 2) := by
      rw [hs₂, State.setArr_arrs_ne _ _ (by aomega), hA₂]
    rw [hs₃]
    refine .alloc ?_
    rw [eval_add (eval_len rfl (by rw [e]; omega)) (eval_reg (by rw [hs₂, hs₁]; exact h8) hN)
      (by rw [e]; omega), e, hcap]
  have hex₄ : Exec w (.alloc (A + 3) (.reg (R + 8))) s₃ s₄ (1 + N) := by
    rw [hs₄]; exact .alloc (eval_reg (by rw [hs₃, hs₂, hs₁]; exact h8) hN)
  have hex₅ : Exec w (.assign (R + 7) (.const 0)) s₄ s₅ 2 := by
    rw [hs₅]; exact .assign (eval_const (by omega))
  have hex₅' : Exec w (.assign (R + 2) (.const 0)) s₅ s₆ 2 := by
    rw [hs₆]; exact .assign (eval_const (by omega))
  have hA₆ : ∀ x, x ≠ a.st → x ≠ a.en → x ≠ A + 4 → x ≠ A + 3 → s₆.arrs x = s.arrs x := by
    intro x h1 h2 h3 h4
    rw [hs₆, hs₅, hs₄, hs₃, hs₂, hs₁]
    simp only [State.setReg_arrs]
    rw [State.setArr_arrs_ne _ _ h4, State.setArr_arrs_ne _ _ h3, State.setArr_arrs_ne _ _ h2,
      State.setArr_arrs_ne _ _ h1]
  have hR₆ : ∀ r, r ≠ R + 7 → r ≠ R + 2 → s₆.regs r = s.regs r := by
    intro r h1 h2
    rw [hs₆, State.setReg_regs_ne _ _ h2, hs₅, State.setReg_regs_ne _ _ h1, hR₄]
  have hadj₆ : IsAdjList G A (A + 1) (A + 2) lists s₆ :=
    hadj.of_arrs_eq (hA₆ _ (by aomega) (by aomega) (by simp) (by simp))
      (hA₆ _ (by aomega) (by aomega) (by simp) (by simp))
      (hA₆ _ (by aomega) (by aomega) (by simp) (by simp))
  -- the loop over the vertices
  let P : State → Prop := fun s' => IsAdjList G A (A + 1) (A + 2) lists s' ∧
    s'.regs R = u.val ∧ s'.regs (R + 1) = v.val ∧ s'.arrs (A + 3) = List.replicate N 0 ∧
    (s'.arrs (A + 2)).length = 2 * E ∧ (s'.arrs (A + 4)).length = cap
  have hP₆ : P s₆ := by
    refine ⟨hadj₆, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hR₆ _ (by simp) (by simp)]; exact hu
    · rw [hR₆ _ (by simp) (by simp)]; exact hv
    · rw [hs₆, hs₅, hs₄]; simp
    · rw [hA₆ _ (by aomega) (by aomega) (by simp) (by simp)]; exact hent
    · rw [hs₆, hs₅, hs₄, hs₃, State.setReg_arrs, State.setReg_arrs,
        State.setArr_arrs_ne _ _ (by simp)]; simp
  obtain ⟨s₇, t₇, hex₇, ht₇, -, hN₇, hb₇, hst₇, hen₇⟩ := vertexLoopProg_exec (w := w) (cap := cap)
    (R + 2) (R + 8) (R + 7) a.st a.en (A + 4) (contrBody A R) L (contrCost lists u.val v.val) P
    (by aomega) (by aomega) (by aomega) (by simp) (by simp) hw1 hN (by omega) (by omega)
    (fun s s' hP harr hreg => ⟨hP.1.of_arrs_eq (harr _ (by aomega) (by aomega))
      (harr _ (by aomega) (by aomega)) (harr _ (by aomega) (by aomega)),
      by rw [hreg _ (by simp)]; exact hP.2.1, by rw [hreg _ (by simp)]; exact hP.2.2.1,
      by rw [harr _ (by aomega) (by aomega)]; exact hP.2.2.2.1,
      by rw [harr _ (by aomega) (by aomega)]; exact hP.2.2.2.2.1,
      by rw [harr _ (by aomega) (by aomega)]; exact hP.2.2.2.2.2⟩)
    (by
      intro x hx s' k hP hx' hN' hb hk
      have hlen := hP.2.2.2.2.2
      rw [hb.1] at hlen
      simp only [List.length_append, List.length_replicate] at hlen
      obtain ⟨s'', t, hex, ht, hb'', ha'', hr''⟩ := contrBody_exec (w := w) A R hP.1 hP.2.1
        hP.2.2.1 hx' hx u.2 v.2 hP.2.2.2.1 hb hk (by rw [hP.2.2.2.2.1]; omega)
      rw [← hL] at hb''
      have hr5 : ∀ r, r < R + 3 → s''.regs r = s'.regs r := fun r hr =>
        hr'' r (by aomega) (by aomega) (by aomega) (by aomega) (by aomega)
      have hr8 : s''.regs (R + 8) = s'.regs (R + 8) :=
        hr'' _ (by simp) (by simp) (by simp) (by simp) (by simp)
      refine ⟨s'', t, hex, ht, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · exact hP.1.of_arrs_eq (ha'' _ (by simp)) (ha'' _ (by simp)) (ha'' _ (by simp))
      · rw [hr5 R (by omega)]; exact hP.2.1
      · rw [hr5 (R + 1) (by omega)]; exact hP.2.2.1
      · rw [ha'' _ (by simp)]; exact hP.2.2.2.1
      · rw [ha'' _ (by simp)]; exact hP.2.2.2.2.1
      · rw [hb''.1]
        simp only [List.length_append, List.length_replicate]
        omega
      · rw [hr5 _ (by omega)]; exact hx'
      · rw [hr8]; exact hN'
      · rw [flatUpTo_succ]; exact hb''
      · exact ha'' _ (by aomega)
      · exact ha'' _ (by aomega))
    hP₆ (by rw [hs₆]; simp) (by rw [hR₆ _ (by simp) (by simp)]; exact h8)
    (by rw [hs₆, hs₅, State.setReg_arrs, State.setReg_arrs, hs₄,
          State.setArr_arrs_ne _ _ (by aomega), hs₃, State.setArr_arrs_ne _ _ (by aomega), hs₂,
          State.setArr_arrs_ne _ _ h23, hs₁, State.setArr_arrs_self])
    (by rw [hs₆, hs₅, State.setReg_arrs, State.setReg_arrs, hs₄,
          State.setArr_arrs_ne _ _ (by aomega), hs₃, State.setArr_arrs_ne _ _ (by aomega), hs₂,
          State.setArr_arrs_self])
    ⟨by rw [hs₆, hs₅, State.setReg_arrs, State.setReg_arrs, hs₄,
          State.setArr_arrs_ne _ _ (by simp), hs₃, State.setArr_arrs_self]; simp,
      by rw [hs₆, State.setReg_regs_ne _ _ (by simp), hs₅, State.setReg_regs_self]; rfl⟩
  -- the copy of the buffer into the entries
  obtain ⟨cnt, hcnt⟩ : ∃ cnt, cnt = (flatUpTo L N).length := ⟨_, rfl⟩
  obtain ⟨s₈, hs₈⟩ : ∃ s₈, s₈ = s₇.setReg (R + 14) cnt := ⟨_, rfl⟩
  obtain ⟨s₉, hs₉⟩ : ∃ s₉, s₉ = s₈.setReg (R + 11) N := ⟨_, rfl⟩
  have hex₈ : Exec w (.assign (R + 14) (.reg (R + 7))) s₇ s₈ 2 := by
    rw [hs₈]; exact .assign (eval_reg (by rw [hb₇.2, hcnt]) (by omega))
  have hex₉ : Exec w (.assign (R + 11) (.reg (R + 8))) s₈ s₉ 2 := by
    rw [hs₉]; exact .assign (eval_reg (by rw [hs₈, State.setReg_regs_ne _ _ (by simp)]; exact hN₇) hN)
  have hA₉ : s₉.arrs = s₇.arrs := by rw [hs₉, hs₈]; rfl
  have hbuf₉ : s₉.arrs (A + 4) = flatUpTo L N ++ List.replicate (cap - cnt) 0 := by
    rw [hA₉, hb₇.1, hcnt]
  obtain ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hd₁₀, ha₁₀, -⟩ := copyMinNProg_exec (w := w) (A + 4) a.ent
    (R + 11) (R + 12) (R + 14) (by aomega) (by simp) (by simp) (by simp) (s := s₉) (B := N)
    (n := cnt) (by rw [hs₉]; simp) hN hw1
    (by rw [hs₉, State.setReg_regs_ne _ _ (by simp), hs₈]; simp) (by omega)
    (by rw [hbuf₉]; simp [hcnt])
  have hlu : (listOf lists u.val).length ≤ N := by rw [listOf_fin]; exact (hadj.2 u).2.2.1
  have hsum := sum_contrCost hadj.2 (u := u.val) v.2
  refine ⟨s₁₀, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₅'
    (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))), ?_, ?_, ?_, ?_⟩
  · rw [hcap, hent] at *
    omega
  · rw [ha₁₀ _ h24, hA₉, hst₇]
  · rw [ha₁₀ _ h34, hA₉, hen₇]
  · rw [hd₁₀, hbuf₉, List.take_left' hcnt.symm]
    exact map_min_of_le fun x hx => le_of_lt (lt_of_mem_flatUpTo hfam x hx)

/-! ### Phase 5 -/

theorem contrFinish_exec {w N : ℕ} (a : InstArrs) (A R : ℕ) (hok : ArrsOk a.list A)
    {S : Finset (Fin N)} {D : List (Fin N)} {s : State} {u : Fin N} (hD : D.Nodup)
    (hDN : D.length ≤ N)
    (halive : s.arrs a.alive = List.ofFn (fun x : Fin N => if x ∈ S then 1 else 0))
    (hcyc : s.arrs (A + 6) = D.map Fin.val) (hu : s.regs R = u.val)
    (h9 : s.regs (R + 9) = if u ∈ D then 1 else 0) (hw : N + 2 < 2 ^ w) :
    ∃ s' t, Exec w (contrFinish a A R) s s' t ∧ t ≤ 21 * N + 15 ∧
      s'.arrs a.alive = List.ofFn (fun x : Fin N => if x ∈ S.erase u then 1 else 0) ∧
      s'.arrs a.cyc = (contractCycle D u).map Fin.val := by
  have hnd := hok.1
  simp only [InstArrs.list, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨-, -, -, h15⟩, -, -, -⟩ := hnd
  have hal : a.alive < A := hok.2 _ (by simp [InstArrs.list])
  have hcy : a.cyc < A := hok.2 _ (by simp [InstArrs.list])
  have hw1 : 1 < 2 ^ w := by omega
  have huw : u.val < 2 ^ w := by have := u.2; omega
  obtain ⟨l, hl⟩ : ∃ l, D.map Fin.val = l := ⟨_, rfl⟩
  have hlnd : l.Nodup := hl ▸ hD.map Fin.val_injective
  have hll : l.length ≤ N := by rw [← hl, List.length_map]; exact hDN
  have hlt : ∀ y ∈ l, y < N := hl ▸ vals_lt D
  have hf : (if u ∈ D then 1 else 0) = (if u.val ∈ l then 1 else 0) := by
    rw [← hl]; simp only [val_mem_map]
  have hfl := length_filter_ne_add hlnd u.val
  rw [← hf] at hfl
  -- the write and the allocation
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = s.writeArr a.alive u.val 0 := ⟨_, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ = s₁.setArr a.cyc
    (List.replicate (l.length - (if u ∈ D then 1 else 0)) 0) := ⟨_, rfl⟩
  obtain ⟨s₃, hs₃⟩ : ∃ s₃, s₃ = s₂.setReg (R + 7) 0 := ⟨_, rfl⟩
  have hex₁ : Exec w (.write a.alive (.reg R) (.const 0)) s s₁ (1 + 1 + 1) := by
    rw [hs₁]
    exact .write (eval_reg hu huw) (eval_const (by omega)) (by rw [halive]; simp)
  have h6₁ : s₁.arrs (A + 6) = l := by
    rw [hs₁, State.writeArr_arrs_ne _ _ _ (by aomega), hcyc, hl]
  have hex₂ : Exec w (.alloc a.cyc (.op .sub (.len (A + 6)) (.reg (R + 9)))) s₁ s₂
      ((1 + 1 + 1) + (l.length - (if u ∈ D then 1 else 0))) := by
    rw [hs₂]
    refine .alloc ?_
    rw [eval_sub (eval_len rfl (by rw [h6₁]; omega))
      (eval_reg (v := if u ∈ D then 1 else 0) (by rw [hs₁, State.writeArr_regs]; exact h9)
        (by split_ifs <;> omega)), h6₁]
  have hex₃ : Exec w (.assign (R + 7) (.const 0)) s₂ s₃ 2 := by
    rw [hs₃]; exact .assign (eval_const (by omega))
  have h6₃ : s₃.arrs (A + 6) = l := by
    rw [hs₃, State.setReg_arrs, hs₂, State.setArr_arrs_ne _ _ (by aomega), h6₁]
  have hR₃ : s₃.regs R = u.val := by
    rw [hs₃, State.setReg_regs_ne _ _ (by simp), hs₂, State.setArr_regs, hs₁,
      State.writeArr_regs, hu]
  -- the loop over the cycle
  let Q : ℕ → State → Prop := fun _ s' => s'.arrs (A + 6) = l ∧ s'.regs R = u.val
  have hg : l.flatMap (fun y => if y = u.val then [] else [y]) =
      l.filter (fun y => y ≠ u.val) := flatMap_filter_ite l (fun y => y = u.val)
  obtain ⟨s₄, t₄, hex₄, ht₄, -, hb₄⟩ := forArrEmit_exec (A + 6) (R + 12) (R + 14) (R + 5) a.cyc
    (R + 7) (.ite (.op .eq (.reg (R + 5)) (.reg R)) .skip (emitProg a.cyc (R + 7) (.reg (R + 5))))
    (fun y => if y = u.val then [] else [y]) Q 10 (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) hw1 (s := s₃) (pre := []) (k := l.length - (if u ∈ D then 1 else 0))
    (by rw [h6₃]; omega) (by rw [h6₃]; intro x hx; have := hlt x hx; omega) ⟨h6₃, hR₃⟩
    ⟨by rw [hs₃, State.setReg_arrs, hs₂, State.setArr_arrs_self]; simp,
      by rw [hs₃, State.setReg_regs_self]; rfl⟩
    (by rw [h6₃, hg]; omega)
    (fun j s s' hQ harr hreg => ⟨by rw [harr]; exact hQ.1,
      by rw [hreg R (by simp) (by simp) (by simp)]; exact hQ.2⟩)
    (fun j s' hQ => by rw [hQ.1, h6₃])
    (by
      intro j hj s' pre' k' hQ hi hn hy hbuf hk hlen
      have hj' : j < l.length := h6₃ ▸ hj
      have hy' : s'.regs (R + 5) = l[j] := by rw [hy]; simp only [h6₃]
      have hyl : (s₃.arrs (A + 6))[j] = l[j] := by simp only [h6₃]
      rw [hyl] at hk ⊢
      have hyw : l[j] < 2 ^ w := by have := hlt _ (List.getElem_mem hj'); omega
      by_cases hyu : l[j] = u.val
      · refine ⟨s', _, exec_ite_eq_true (w := w) hy' (hQ.2.trans hyu.symm) hyw hw1 (.skip _),
          by simp, hQ, hi, hn, by simpa [hyu] using hbuf⟩
      · simp only [hyu, if_false, List.length_singleton] at hk ⊢
        simp only [List.length_nil, Nat.zero_add] at hlen
        obtain ⟨s'', hex, hb'', hA'', hR''⟩ := emitReg_exec (w := w) a.cyc (R + 7) (R + 5)
          (k := k' - 1) (by rw [show k' - 1 + 1 = k' by omega]; exact hbuf) hy' hyw (by omega)
        refine ⟨s'', _, exec_ite_eq_false (w := w) hy' hQ.2 hyu hyw huw hw1 hex, by simp,
          ⟨by rw [hA'' _ (by aomega)]; exact hQ.1, by rw [hR'' _ (by simp)]; exact hQ.2⟩,
          by rw [hR'' _ (by simp)]; exact hi, by rw [hR'' _ (by simp)]; exact hn, hb''⟩)
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, ?_, ?_⟩
  · rw [h6₃] at ht₄
    have : l.length * (10 + 10) ≤ 20 * N := by nlinarith
    omega
  · rw [hex₄.arrs_eq_of_not_mem_writtenArrs (by wfr), hs₃, State.setReg_arrs, hs₂,
      State.setArr_arrs_ne _ _ h15, hs₁, State.writeArr_arrs_self, halive]
    exact ofFn_set_erase S u
  · rw [hb₄.1, h6₃, hg, contractCycle_map hD, hl]
    simp only [List.nil_append]
    rw [show l.length - (if u ∈ D then 1 else 0) - (l.filter (fun y => y ≠ u.val)).length = 0
      by omega]
    simp

/-! ### The whole program -/

theorem exists_fin_list {N : ℕ} (l : List ℕ) (h : ∀ y ∈ l, y < N) :
    ∃ L : List (Fin N), L.map Fin.val = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    obtain ⟨L, hL⟩ := ih (fun y hy => h y (List.mem_cons_of_mem a hy))
    exact ⟨⟨a, h a (by simp)⟩ :: L, by simp [hL]⟩

theorem sixteen_le_pow (n : ℕ) : 16 * n + 16 ≤ (n + 2) ^ 4 := by
  have h1 : 4 * n + 4 ≤ (n + 2) ^ 2 := by nlinarith
  have h2 : (n + 2) ^ 4 = ((n + 2) ^ 2) ^ 2 := by ring
  rw [h2]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The corrected contraction claim holds.** -/
theorem contractLenProgClaim_proved : ContractLenProgClaim := by
  intro a a_rec A R hok
  refine ⟨contractProg a a_rec A R, 700, 4, fun w N inst G S D u v recs s hw hinst hcyc htrial hu
    hv hrec => ?_⟩
  obtain rfl : inst = instDecidableEqFin N := Subsingleton.elim _ _
  -- the setting
  obtain ⟨n, hn⟩ : ∃ n, n = instSize N G + (s.arrs a_rec).length := ⟨_, rfl⟩
  have hw' : 16 * n + 16 < 2 ^ w := by
    have h1 := pow_lt_two_pow_wordSize (c := 4) (by omega) (instSize N G + (s.arrs a_rec).length)
    have h2 : 2 ^ wordSize 4 (instSize N G + (s.arrs a_rec).length) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by omega) hw
    have h3 := sixteen_le_pow n
    rw [← hn] at h1 h2
    omega
  have hsz : N + 1 ≤ instSize N G := by unfold instSize; omega
  have hw4 : 4 * instSize N G + 4 < 2 ^ w := by omega
  have hokA : ArrsOk a.list A := ⟨hok.1.sublist (List.sublist_append_left _ _),
    fun x hx => hok.2 x (List.mem_append_left _ hx)⟩
  have hrecA : a_rec < A := hok.2 a_rec (by simp)
  have hnd := hok.1
  simp only [InstArrs.list, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h12, h13, h14, h15, h1r⟩, ⟨h23, h24, h25, h2r⟩, ⟨h34, h35, h3r⟩, ⟨h45, h4r⟩, h5r⟩ := hnd
  have hal : a.alive < A := hokA.2 _ (by simp [InstArrs.list])
  have hst : a.st < A := hokA.2 _ (by simp [InstArrs.list])
  have hen : a.en < A := hokA.2 _ (by simp [InstArrs.list])
  have hent : a.ent < A := hokA.2 _ (by simp [InstArrs.list])
  have hcy : a.cyc < A := hokA.2 _ (by simp [InstArrs.list])
  have hD : D.Nodup := hcyc.2.1
  have hDN : D.length ≤ N := by simpa using hD.length_le_card
  have huv : G.Adj u v := htrial.1
  -- phase 1
  obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, hfa₁, hfr₁, h8₁, h9₁, h10₁⟩ :=
    contrPre_exec (w := w) a A R hokA hinst hDN hw4 hu hv
  obtain ⟨-, halive₁, ⟨lists, hadj₁⟩, hent₁, hcyc₁⟩ := hb₁
  have hadj₁' : IsAdjList G A (A + 1) (A + 2) lists s₁ := hadj₁
  have hu₁ : s₁.regs R = u.val := by rw [hfr₁ R (by omega)]; exact hu
  have hv₁ : s₁.regs (R + 1) = v.val := by rw [hfr₁ (R + 1) (by omega)]; exact hv
  -- phase 2
  obtain ⟨s₂, t₂, hex₂, ht₂, henc₂⟩ := contrEnc_exec (w := w) A R hadj₁' hent₁ hu₁ hv₁
    (by split_ifs <;> omega) (by split_ifs <;> omega) h9₁ h10₁ hw4
  have hA₂ : ∀ x, x ≠ A + 7 → s₂.arrs x = s₁.arrs x := fun x hx =>
    hex₂.arrs_eq_of_not_mem_writtenArrs (by wfr)
  have hR₂ : ∀ r, r ∈ [R, R + 1, R + 8, R + 9] → s₂.regs r = s₁.regs r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hex₂.regs_eq_of_not_mem_writtenRegs (by rcases hr with rfl | rfl | rfl | rfl <;> wfr)
  -- the record
  obtain ⟨lv, hlv⟩ : ∃ lv, listOf lists v.val = lv := ⟨_, rfl⟩
  have hlvlt : ∀ y ∈ lv, y < N := hlv ▸ listOf_lt hadj₁'.2 v
  have hlvN : lv.length ≤ N := by rw [← hlv, listOf_fin]; exact (hadj₁'.2 v).2.2.1
  obtain ⟨Nv, hNv⟩ := exists_fin_list lv hlvlt
  obtain ⟨enc, henc⟩ : ∃ enc, s₂.arrs (A + 7) = enc := ⟨_, rfl⟩
  have hencR : IsRecordEnc (CrossRecord.contr
      { graph := G, verts := (S : Set (Fin N)), cycle := D, u := u, v := v }) enc := by
    refine ⟨Nv, ?_, ?_, ?_⟩
    · apply List.Nodup.of_map Fin.val
      rw [hNv, ← hlv]; exact listOf_nodup hadj₁'.2 _
    · intro y
      rw [← List.mem_map_of_injective Fin.val_injective, hNv, ← hlv, listOf_fin]
      exact (hadj₁'.2 v).2.2.2 y
    · rw [← henc, henc₂, hlv, ← hNv, List.length_map]
  have hencl : enc.length = lv.length + 7 := by
    rw [← henc, henc₂, hlv]; simp [withLength]
  -- phase 3
  have hrec₂ : IsRecordsAt a_rec recs s₂ := by
    obtain ⟨ls, hls, he⟩ := hrec
    exact ⟨ls, hls, by rw [hA₂ _ (by omega), hfa₁ _ hrecA, he]⟩
  have hrl₂ : (s₂.arrs a_rec).length = (s.arrs a_rec).length := by
    rw [hA₂ _ (by omega), hfa₁ _ hrecA]
  obtain ⟨s₃, t₃, hex₃, ht₃, hrec₃⟩ := contrApp_exec (w := w) a_rec A R hrecA hrec₂
    (by rw [henc]; exact le_of_isRecordEnc hencR)
    (by rw [hR₂ _ (by simp)]; exact h8₁) (by rw [henc, hencl, hrl₂]; omega)
  have hA₃ : ∀ x, x ≠ a_rec → x ≠ A + 8 → s₃.arrs x = s₂.arrs x := fun x h1 h2 =>
    hex₃.arrs_eq_of_not_mem_writtenArrs (by wfr)
  have hR₃ : ∀ r, r ∈ [R, R + 1, R + 8, R + 9] → s₃.regs r = s₂.regs r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hex₃.regs_eq_of_not_mem_writtenRegs (by rcases hr with rfl | rfl | rfl | rfl <;> wfr)
  have hA₃' : ∀ x, x ∈ [A, A + 1, A + 2, A + 6, a.alive] → s₃.arrs x = s₁.arrs x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rw [hA₃ _ (by aomega) (by aomega), hA₂ _ (by aomega)]
  -- phase 4
  obtain ⟨s₄, t₄, hex₄, ht₄, hst₄, hen₄, hent₄⟩ := contrRebuild_exec (w := w) a A R hokA huv
    (hadj₁'.of_arrs_eq (hA₃' _ (by simp)) (hA₃' _ (by simp)) (hA₃' _ (by simp)))
    (by rw [hA₃' _ (by simp)]; exact hent₁)
    (by rw [hR₃ _ (by simp), hR₂ _ (by simp)]; exact hu₁)
    (by rw [hR₃ _ (by simp), hR₂ _ (by simp)]; exact hv₁)
    (by rw [hR₃ _ (by simp), hR₂ _ (by simp)]; exact h8₁) hw4
  have hA₄ : ∀ x, x ∈ [A + 6, a.alive, a_rec] → s₄.arrs x = s₃.arrs x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hex₄.arrs_eq_of_not_mem_writtenArrs (by rcases hx with rfl | rfl | rfl <;> wfr)
  have hR₄ : ∀ r, r ∈ [R, R + 9] → s₄.regs r = s₃.regs r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hex₄.regs_eq_of_not_mem_writtenRegs (by rcases hr with rfl | rfl <;> wfr)
  -- phase 5
  obtain ⟨s₅, t₅, hex₅, ht₅, halive₅, hcyc₅⟩ := contrFinish_exec (w := w) (S := S) a A R hokA hD hDN
    (by rw [hA₄ _ (by simp), hA₃' _ (by simp), hfa₁ _ hal]; exact hinst.2.1)
    (by rw [hA₄ _ (by simp), hA₃' _ (by simp)]; exact hcyc₁)
    (by rw [hR₄ _ (by simp), hR₃ _ (by simp), hR₂ _ (by simp)]; exact hu₁)
    (by rw [hR₄ _ (by simp), hR₃ _ (by simp), hR₂ _ (by simp)]; exact h9₁) (by omega)
  have hA₅ : ∀ x, x ∈ [a.st, a.en, a.ent, a_rec] → s₅.arrs x = s₄.arrs x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hex₅.arrs_eq_of_not_mem_writtenArrs (by rcases hx with rfl | rfl | rfl | rfl <;> wfr)
  have hex : Exec w (contractProg a a_rec A R) s s₅ (t₁ + (t₂ + (t₃ + (t₄ + t₅)))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
  refine ⟨s₅, _, hex, ?_, ⟨fun r hr _ => hex.regs_eq_of_not_mem_writtenRegs (by wfr),
    fun x hx hxl => hex.arrs_eq_of_not_mem_writtenArrs ?_⟩, ?_, ?_⟩
  · -- the time
    rw [henc, hencl, hrl₂] at ht₃
    have : t₁ + (t₂ + (t₃ + (t₄ + t₅))) ≤ 655 * n := by rw [hn]; omega
    rw [← hn]
    omega
  · simp only [InstArrs.list, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hxl
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hxl
    wfr
  · -- the instance
    set L := contrList lists u.val v.val with hL
    have hfam : IsAdjListFamily (contractGraph G u v) (fun x => L x) :=
      isAdjListFamily_contrList hadj₁'.2 huv
    refine ⟨isSupportedOn_contractGraph hinst.1 huv, halive₅,
      ⟨fun x => L x, isListFamily_flatUpTo (by rw [hA₅ _ (by simp)]; exact hst₄)
        (by rw [hA₅ _ (by simp)]; exact hen₄) (by rw [hA₅ _ (by simp)]; exact hent₄), hfam⟩,
      by rw [hA₅ _ (by simp), hent₄]; exact length_flatUpTo_eq hfam, hcyc₅⟩
  · -- the records
    obtain ⟨ls, hls, he⟩ := hrec₂
    refine ⟨ls ++ [enc], List.rel_append hls (List.Forall₂.cons hencR .nil), ?_⟩
    rw [hA₅ _ (by simp), hA₄ _ (by simp), hrec₃, he, henc]
    simp

/-! ### The contraction with the records in a buffer -/

theorem contrAppBuf_exec {w N : ℕ} (a_rec r_rec A R : ℕ) (hA : a_rec < A) (hrr : r_rec < R)
    {recs : List (CrossRecord (Fin N))} {rec : CrossRecord (Fin N)} {k : ℕ} {s : State}
    (hbuf : IsRecBufAt a_rec r_rec recs k s) (hencR : IsRecordEnc rec (s.arrs (A + 7)))
    (h8 : s.regs (R + 8) = N) (hk : (s.arrs (A + 7)).length ≤ k)
    (hw : (s.arrs a_rec).length + (s.arrs (A + 7)).length + N + 2 < 2 ^ w) :
    ∃ s' t, Exec w (contrAppBuf a_rec r_rec A R) s s' t ∧
      t ≤ 16 * (s.arrs (A + 7)).length + 19 ∧
      IsRecBufAt a_rec r_rec (recs ++ [rec]) (k - (s.arrs (A + 7)).length) s' ∧
      (s'.arrs a_rec).length = (s.arrs a_rec).length := by
  obtain ⟨ls, hF, harr, hreg⟩ := hbuf
  obtain ⟨enc, henc⟩ : ∃ enc, s.arrs (A + 7) = enc := ⟨_, rfl⟩
  rw [henc] at hencR hk hw ⊢
  have hw1 : 1 < 2 ^ w := by omega
  have hlenP : (s.arrs a_rec).length = ls.flatten.length + k := by rw [harr]; simp
  obtain ⟨B, hB⟩ : ∃ B, B = N + (enc.length + 2) := ⟨_, rfl⟩
  obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = ((s.setReg (R + 11) B).setReg (R + 13) ls.flatten.length).setReg
    (R + 14) enc.length := ⟨_, rfl⟩
  have hex₁ : ∀ {s' : State} {t : ℕ}, Exec w (.seq (copyAtProg (A + 7) a_rec (R + 11) (R + 12)
      (R + 13) (R + 14)) (.assign r_rec (.op .add (.reg r_rec) (.len (A + 7))))) s₁ s' t →
      Exec w (contrAppBuf a_rec r_rec A R) s s' (6 + (2 + (2 + t))) := fun h => by
    rw [hs₁, hB] at h
    refine .seq (.assign (eval_add (eval_reg h8 (by omega)) (eval_add (eval_len henc (by omega))
      (eval_const (by omega)) (by omega)) (by omega))) (.seq (.assign (eval_reg (by
        rw [State.setReg_regs_ne _ _ (show r_rec ≠ R + 11 by omega)]; exact hreg) (by omega)))
      (.seq (.assign (eval_len (by simp only [State.setReg_arrs]; exact henc) (by omega))) h))
  have hA₁ : s₁.arrs = s.arrs := by rw [hs₁]; rfl
  obtain ⟨s₂, t₂, hex₂, ht₂, hd₂, ha₂, hr₂⟩ := copyAtProg_exec (w := w) (A + 7) a_rec (R + 11)
    (R + 12) (R + 13) (R + 14) (by omega) (by simp) (by simp) (by simp) (s := s₁) (B := B)
    (A := ls.flatten) (C := List.replicate (k - enc.length) 0)
    (by rw [hs₁]; simp [State.setReg_regs]) (by omega) hw1
    (by rw [hs₁]; simp [State.setReg_regs])
    (by rw [hs₁]; simp [State.setReg_regs, henc])
    (by rw [hA₁, harr, henc, List.append_assoc, ← List.replicate_add]; congr 2; omega)
    (by rw [hA₁, henc]; omega)
  rw [hA₁, henc] at hd₂ ht₂
  have hmin : enc.map (fun x => min x B) = enc := map_min_of_le fun x hx => by
    have := le_of_isRecordEnc hencR x hx; omega
  rw [hmin] at hd₂
  have hr₂' : s₂.regs r_rec = ls.flatten.length := by
    rw [hr₂ _ (show r_rec ≠ R + 12 by omega), hs₁,
      State.setReg_regs_ne _ _ (show r_rec ≠ R + 14 by omega),
      State.setReg_regs_ne _ _ (show r_rec ≠ R + 13 by omega),
      State.setReg_regs_ne _ _ (show r_rec ≠ R + 11 by omega), hreg]
  have he₂ : s₂.arrs (A + 7) = enc := by
    rw [ha₂ _ (show A + 7 ≠ a_rec by omega), hA₁, henc]
  have hex₃ : Exec w (.assign r_rec (.op .add (.reg r_rec) (.len (A + 7)))) s₂
      (s₂.setReg r_rec (ls.flatten.length + enc.length)) 4 :=
    .assign (eval_add (eval_reg hr₂' (by omega)) (eval_len he₂ (by omega)) (by omega))
  refine ⟨_, _, hex₁ (.seq hex₂ hex₃), ?_,
    ⟨ls ++ [enc], List.rel_append hF (List.Forall₂.cons hencR .nil), ?_, ?_⟩, ?_⟩
  · omega
  · rw [State.setReg_arrs, hd₂]; simp
  · simp
  · rw [State.setReg_arrs, hd₂, hlenP]; simp; omega

set_option maxHeartbeats 1000000 in
/-- **The contraction claim with the records in a buffer holds.** -/
theorem contractRecProgClaim_proved : ContractRecProgClaim := by
  intro a a_rec r_rec A R hok hrr
  refine ⟨contractBufProg a a_rec r_rec A R, 600, 4, fun w N inst G S D u v recs k s hw hinst
    hcyc htrial hu hv hrec hk => ?_⟩
  obtain rfl : inst = instDecidableEqFin N := Subsingleton.elim _ _
  -- the setting
  obtain ⟨n, hn⟩ : ∃ n, n = instSize N G + (s.arrs a_rec).length := ⟨_, rfl⟩
  have hw' : 16 * n + 16 < 2 ^ w := by
    have h1 := pow_lt_two_pow_wordSize (c := 4) (by omega) (instSize N G + (s.arrs a_rec).length)
    have h2 : 2 ^ wordSize 4 (instSize N G + (s.arrs a_rec).length) ≤ 2 ^ w :=
      Nat.pow_le_pow_right (by omega) hw
    have h3 := sixteen_le_pow n
    rw [← hn] at h1 h2
    omega
  have hsz : N + 1 ≤ instSize N G := by unfold instSize; omega
  have hw4 : 4 * instSize N G + 4 < 2 ^ w := by omega
  have hokA : ArrsOk a.list A := ⟨hok.1.sublist (List.sublist_append_left _ _),
    fun x hx => hok.2 x (List.mem_append_left _ hx)⟩
  have hrecA : a_rec < A := hok.2 a_rec (by simp)
  have hnd := hok.1
  simp only [InstArrs.list, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h12, h13, h14, h15, h1r⟩, ⟨h23, h24, h25, h2r⟩, ⟨h34, h35, h3r⟩, ⟨h45, h4r⟩, h5r⟩ := hnd
  have hal : a.alive < A := hokA.2 _ (by simp [InstArrs.list])
  have hst : a.st < A := hokA.2 _ (by simp [InstArrs.list])
  have hen : a.en < A := hokA.2 _ (by simp [InstArrs.list])
  have hent : a.ent < A := hokA.2 _ (by simp [InstArrs.list])
  have hcy : a.cyc < A := hokA.2 _ (by simp [InstArrs.list])
  have hD : D.Nodup := hcyc.2.1
  have hDN : D.length ≤ N := by simpa using hD.length_le_card
  have huv : G.Adj u v := htrial.1
  -- phase 1
  obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, hfa₁, hfr₁, h8₁, h9₁, h10₁⟩ :=
    contrPre_exec (w := w) a A R hokA hinst hDN hw4 hu hv
  obtain ⟨-, halive₁, ⟨lists, hadj₁⟩, hent₁, hcyc₁⟩ := hb₁
  have hadj₁' : IsAdjList G A (A + 1) (A + 2) lists s₁ := hadj₁
  have hu₁ : s₁.regs R = u.val := by rw [hfr₁ R (by omega)]; exact hu
  have hv₁ : s₁.regs (R + 1) = v.val := by rw [hfr₁ (R + 1) (by omega)]; exact hv
  -- phase 2
  obtain ⟨s₂, t₂, hex₂, ht₂, henc₂⟩ := contrEnc_exec (w := w) A R hadj₁' hent₁ hu₁ hv₁
    (by split_ifs <;> omega) (by split_ifs <;> omega) h9₁ h10₁ hw4
  have hA₂ : ∀ x, x ≠ A + 7 → s₂.arrs x = s₁.arrs x := fun x hx =>
    hex₂.arrs_eq_of_not_mem_writtenArrs (by wfr)
  have hR₂ : ∀ r, r ∈ [R, R + 1, R + 8, R + 9, r_rec] → s₂.regs r = s₁.regs r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hex₂.regs_eq_of_not_mem_writtenRegs
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> wfr)
  -- the record
  obtain ⟨lv, hlv⟩ : ∃ lv, listOf lists v.val = lv := ⟨_, rfl⟩
  have hlvlt : ∀ y ∈ lv, y < N := hlv ▸ listOf_lt hadj₁'.2 v
  have hlvN : lv.length ≤ N := by rw [← hlv, listOf_fin]; exact (hadj₁'.2 v).2.2.1
  obtain ⟨Nv, hNv⟩ := exists_fin_list lv hlvlt
  obtain ⟨enc, henc⟩ : ∃ enc, s₂.arrs (A + 7) = enc := ⟨_, rfl⟩
  have hencR : IsRecordEnc (CrossRecord.contr
      { graph := G, verts := (S : Set (Fin N)), cycle := D, u := u, v := v }) enc := by
    refine ⟨Nv, ?_, ?_, ?_⟩
    · apply List.Nodup.of_map Fin.val
      rw [hNv, ← hlv]; exact listOf_nodup hadj₁'.2 _
    · intro y
      rw [← List.mem_map_of_injective Fin.val_injective, hNv, ← hlv, listOf_fin]
      exact (hadj₁'.2 v).2.2.2 y
    · rw [← henc, henc₂, hlv, ← hNv, List.length_map]
  have hencl : enc.length = lv.length + 7 := by
    rw [← henc, henc₂, hlv]; simp [withLength]
  -- phase 3
  have hrec₂ : IsRecBufAt a_rec r_rec recs k s₂ := by
    obtain ⟨ls, hls, he, hr⟩ := hrec
    exact ⟨ls, hls, by rw [hA₂ _ (by omega), hfa₁ _ hrecA, he],
      by rw [hR₂ _ (by simp), hfr₁ _ (by omega), hr]⟩
  have hrl₂ : (s₂.arrs a_rec).length = (s.arrs a_rec).length := by
    rw [hA₂ _ (by omega), hfa₁ _ hrecA]
  obtain ⟨s₃, t₃, hex₃, ht₃, hrec₃, hrl₃⟩ := contrAppBuf_exec (w := w) a_rec r_rec A R hrecA hrr
    hrec₂ (by rw [henc]; exact hencR) (by rw [hR₂ _ (by simp)]; exact h8₁)
    (by rw [henc, hencl]; omega) (by rw [henc, hencl, hrl₂]; omega)
  have hA₃ : ∀ x, x ≠ a_rec → x ≠ A + 8 → s₃.arrs x = s₂.arrs x := fun x h1 h2 =>
    hex₃.arrs_eq_of_not_mem_writtenArrs (by wfr)
  have hR₃ : ∀ r, r ∈ [R, R + 1, R + 8, R + 9] → s₃.regs r = s₂.regs r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hex₃.regs_eq_of_not_mem_writtenRegs (by rcases hr with rfl | rfl | rfl | rfl <;> wfr)
  have hA₃' : ∀ x, x ∈ [A, A + 1, A + 2, A + 6, a.alive] → s₃.arrs x = s₁.arrs x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rw [hA₃ _ (by aomega) (by aomega), hA₂ _ (by aomega)]
  -- phase 4
  obtain ⟨s₄, t₄, hex₄, ht₄, hst₄, hen₄, hent₄⟩ := contrRebuild_exec (w := w) a A R hokA huv
    (hadj₁'.of_arrs_eq (hA₃' _ (by simp)) (hA₃' _ (by simp)) (hA₃' _ (by simp)))
    (by rw [hA₃' _ (by simp)]; exact hent₁)
    (by rw [hR₃ _ (by simp), hR₂ _ (by simp)]; exact hu₁)
    (by rw [hR₃ _ (by simp), hR₂ _ (by simp)]; exact hv₁)
    (by rw [hR₃ _ (by simp), hR₂ _ (by simp)]; exact h8₁) hw4
  have hA₄ : ∀ x, x ∈ [A + 6, a.alive, a_rec] → s₄.arrs x = s₃.arrs x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hex₄.arrs_eq_of_not_mem_writtenArrs (by rcases hx with rfl | rfl | rfl <;> wfr)
  have hR₄ : ∀ r, r ∈ [R, R + 9, r_rec] → s₄.regs r = s₃.regs r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact hex₄.regs_eq_of_not_mem_writtenRegs (by rcases hr with rfl | rfl | rfl <;> wfr)
  -- phase 5
  obtain ⟨s₅, t₅, hex₅, ht₅, halive₅, hcyc₅⟩ := contrFinish_exec (w := w) (S := S) a A R hokA hD hDN
    (by rw [hA₄ _ (by simp), hA₃' _ (by simp), hfa₁ _ hal]; exact hinst.2.1)
    (by rw [hA₄ _ (by simp), hA₃' _ (by simp)]; exact hcyc₁)
    (by rw [hR₄ _ (by simp), hR₃ _ (by simp), hR₂ _ (by simp)]; exact hu₁)
    (by rw [hR₄ _ (by simp), hR₃ _ (by simp), hR₂ _ (by simp)]; exact h9₁) (by omega)
  have hA₅ : ∀ x, x ∈ [a.st, a.en, a.ent, a_rec] → s₅.arrs x = s₄.arrs x := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hex₅.arrs_eq_of_not_mem_writtenArrs (by rcases hx with rfl | rfl | rfl | rfl <;> wfr)
  have hR₅ : s₅.regs r_rec = s₄.regs r_rec := hex₅.regs_eq_of_not_mem_writtenRegs (by wfr)
  have hex : Exec w (contractBufProg a a_rec r_rec A R) s s₅ (t₁ + (t₂ + (t₃ + (t₄ + t₅)))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
  rw [henc, hencl] at ht₃ hrec₃
  refine ⟨s₅, _, hex, ?_, ⟨fun r hr hr' => hex.regs_eq_of_not_mem_writtenRegs ?_,
    fun x hx hxl => hex.arrs_eq_of_not_mem_writtenArrs ?_⟩, ?_, k - (lv.length + 7), ?_, ?_,
    by omega⟩
  · -- the time
    omega
  · simp only [List.mem_singleton] at hr'
    wfr
  · simp only [InstArrs.list, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hxl
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hxl
    wfr
  · -- the instance
    set L := contrList lists u.val v.val with hL
    have hfam : IsAdjListFamily (contractGraph G u v) (fun x => L x) :=
      isAdjListFamily_contrList hadj₁'.2 huv
    refine ⟨isSupportedOn_contractGraph hinst.1 huv, halive₅,
      ⟨fun x => L x, isListFamily_flatUpTo (by rw [hA₅ _ (by simp)]; exact hst₄)
        (by rw [hA₅ _ (by simp)]; exact hen₄) (by rw [hA₅ _ (by simp)]; exact hent₄), hfam⟩,
      by rw [hA₅ _ (by simp), hent₄]; exact length_flatUpTo_eq hfam, hcyc₅⟩
  · -- the records
    obtain ⟨ls, hls, he, hr⟩ := hrec₃
    exact ⟨ls, hls, by rw [hA₅ _ (by simp), hA₄ _ (by simp), he],
      by rw [hR₅, hR₄ _ (by simp), hr]⟩
  · rw [hA₅ _ (by simp), hA₄ _ (by simp), hrl₃, hrl₂]

end GraphMinor.Compute.Crossing