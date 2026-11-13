module

public import GraphMinor.Compute.Graph
public import GraphMinor.Compute.BFS
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# The searches of Algorithm 5.1: a breadth-first search with forbidden vertices and targets

Humeau and Pous, proof of Proposition 5.9 (page 23): "All of these can be done using a *search
algorithm* (e.g. depth- or breadth-first searches) forbidding the traversal of some vertices
$X\subseteq V(G)$. We call *$X$-searches* such searches." and "An $X$-search can be done in $O(m)$
assuming that the relation $-\in X$ is an attribute of vertices of $G$ accessible in constant time."

`searchProg` is one such search on the Word RAM. The number of vertices `n` is read from register
`rN`, so one program serves every graph. The caller writes an initial label `L0 v ∈ {0, 2, 3}` for
every vertex into array `aLab` and a list of sources into array `aSrc`:
* label `0`: a free vertex, which the search may enter;
* label `2`: a forbidden vertex (a vertex of `X`);
* label `3`: a target: the search does not enter it, but when it sees one from a reached vertex `u`
  it writes the target to register `rHit` and `u` to register `rHitPar`.

The search starts from the free sources, enters free vertices only, and gives each reached vertex
label `1` and a parent (`n` for a source). `searchProg_exec` gives its result, the invariant `SInv` with an empty
queue, and its time, `O(n + |src| + m)`.

This file proves what the program does in terms of its queue; the walks that the parents give, and
the description of the reached set by walks, are in `TwoPathsSearchWalk.lean`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph

/-! ### Registers and arrays of the search -/

/-- Array of labels. -/
abbrev aLab : Arr := 60
/-- Array of parents. -/
abbrev aPar : Arr := 61
/-- Array of the queue. -/
abbrev aQue : Arr := 62
/-- Array of the sources. -/
abbrev aSrc : Arr := 63

/-- Queue head. -/
abbrev rHead : Reg := 60
/-- Queue tail. -/
abbrev rTail : Reg := 61
/-- Current vertex. -/
abbrev rU : Reg := 62
/-- Cursor in an adjacency list. -/
abbrev rK : Reg := 63
/-- End of an adjacency list. -/
abbrev rHi : Reg := 64
/-- Current neighbour. -/
abbrev rV : Reg := 65
/-- Label just read. -/
abbrev rL : Reg := 66
/-- Last target seen (`n` when none). -/
abbrev rHit : Reg := 67
/-- The reached vertex from which the last target was seen. -/
abbrev rHitPar : Reg := 68
/-- Index in the source list. -/
abbrev rI : Reg := 69
/-- Current source. -/
abbrev rX : Reg := 70

/-! ### The program -/

/-- What the search does with one neighbour `rV` of the current vertex `rU`. -/
def searchVisit : Cmd :=
  .seq (.assign rL (.read aLab (.reg rV)))
    (.ite (.op .eq (.reg rL) (.const 0))
      (.seq (.write aLab (.reg rV) (.const 1))
        (.seq (.write aPar (.reg rV) (.reg rU)) (queuePush aQue rTail (.reg rV))))
      (.ite (.op .eq (.reg rL) (.const 3))
        (.seq (.assign rHit (.reg rV)) (.assign rHitPar (.reg rU)))
        .skip))

/-- One round of the search: take the next vertex of the queue and visit its neighbours. -/
def searchStep (gS gE gEnt : Arr) : Cmd :=
  .seq (queuePop aQue rHead rU) (forList gS gE gEnt rU rK rHi rV searchVisit)

/-- The main loop of the search. -/
def searchLoop (gS gE gEnt : Arr) : Cmd :=
  .while (.op .lt (.reg rHead) (.reg rTail)) (searchStep gS gE gEnt)

/-- What the search does with one source `rX`. -/
def searchSource : Cmd :=
  .seq (.assign rX (.read aSrc (.reg rI)))
    (.seq (.assign rL (.read aLab (.reg rX)))
      (.ite (.op .eq (.reg rL) (.const 0))
        (.seq (.write aLab (.reg rX) (.const 1))
          (.seq (.write aPar (.reg rX) (.reg 40)) (queuePush aQue rTail (.reg rX))))
        .skip))

/-- The search: parents and queue, no target seen, the sources, then the main loop. The number of
vertices is in register `40`. -/
def searchProg (gS gE gEnt : Arr) : Cmd :=
  .seq (.alloc aPar (.reg 40))
    (.seq (queueInit aQue rHead rTail (.reg 40))
      (.seq (.assign rHit (.reg 40))
        (.seq (.assign rI (.const 0))
          (.seq (forUp rI (.len aSrc) searchSource)
            (searchLoop gS gE gEnt)))))

/-! ### Predicates -/

variable {n : ℕ}

/-- The parents of the reached vertices: a reached source has parent `n`; a reached vertex with
parent `n` is a source; any other reached vertex has as parent a neighbour that was reached before
it. -/
def ParentOK (G : SimpleGraph (Fin n)) (src items : List ℕ) (p : Fin n → ℕ) : Prop :=
  ∀ x : Fin n, x.1 ∈ items → (x.1 ∈ src → p x = n) ∧ ((p x = n ∧ x.1 ∈ src) ∨
    ∃ u : Fin n, p x = u.1 ∧ u.1 ∈ items ∧ items.idxOf u.1 < items.idxOf x.1 ∧ G.Adj u x)

/-- The target registers: either no target was seen from the scanned vertices (`S`), or the
registers hold a target and a reached neighbour of it. -/
def HitOK (G : SimpleGraph (Fin n)) (L0 : Fin n → ℕ) (items : List ℕ) (S : Fin n → Prop)
    (rh rp : ℕ) : Prop :=
  (rh = n ∧ ∀ v, S v → L0 v ≠ 3) ∨
    ∃ v u : Fin n, rh = v.1 ∧ rp = u.1 ∧ L0 v = 3 ∧ u.1 ∈ items ∧ G.Adj u v

/-- The vertices seen from the first `h` vertices of the queue. -/
def SeenFrom (G : SimpleGraph (Fin n)) (items : List ℕ) (h : ℕ) (v : Fin n) : Prop :=
  ∃ u : Fin n, u.1 ∈ items.take h ∧ G.Adj u v

/-- The registers and arrays the search does not write keep their values. -/
def SFrame (s₀ s : State) : Prop :=
  (∀ r, r < 60 ∨ 71 ≤ r → s.regs r = s₀.regs r) ∧
  (∀ a, a ≠ aLab → a ≠ aPar → a ≠ aQue → s.arrs a = s₀.arrs a)

/-- The invariant of the main loop of the search, with queue history `items` and head `h`. -/
structure SInv (G : SimpleGraph (Fin n)) (L0 : Fin n → ℕ) (src : List ℕ) (s₀ : State)
    (items : List ℕ) (h : ℕ) (s : State) : Prop where
  frame : SFrame s₀ s
  queue : IsQueueHistory aQue rHead rTail n items h s
  nodup : items.Nodup
  lt : ∀ x ∈ items, x < n
  free : ∀ x : Fin n, x.1 ∈ items → L0 x = 0
  lab : s.arrs aLab = List.ofFn (fun x : Fin n => if x.1 ∈ items then 1 else L0 x)
  par : ∃ p : Fin n → ℕ, s.arrs aPar = List.ofFn p ∧ ParentOK G src items p
  closed : ∀ u : Fin n, u.1 ∈ items.take h → ∀ v, G.Adj u v → L0 v ≠ 0 ∨ v.1 ∈ items
  hit : HitOK G L0 items (SeenFrom G items h) (s.regs rHit) (s.regs rHitPar)
  srcs : ∀ x : Fin n, x.1 ∈ src → L0 x = 0 → x.1 ∈ items

/-! ### Small facts -/

theorem ofFn_set {f : Fin n → ℕ} (x : Fin n) (v : ℕ) :
    (List.ofFn f).set x.1 v = List.ofFn (Function.update f x v) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_set, List.getElem_ofFn, Function.update_apply]
  by_cases hi : x.1 = i
  · subst hi; simp
  · have hne : (⟨i, by simpa using h₂⟩ : Fin n) ≠ x := fun h => hi (by rw [← h])
    simp [hi, hne]

theorem getElem_ofFn' {f : Fin n → ℕ} (x : Fin n) (h : x.1 < (List.ofFn f).length) :
    (List.ofFn f)[x.1]'h = f x := by
  simp

theorem idxOf_append_mem {l e : List ℕ} {a : ℕ} (h : a ∈ l) : (l ++ e).idxOf a = l.idxOf a :=
  List.idxOf_append_of_mem h

/-- The degree of a vertex number (`0` when it is not a vertex). -/
def degOf (lists : Fin n → List ℕ) (x : ℕ) : ℕ :=
  if hx : x < n then (lists ⟨x, hx⟩).length else 0

/-- The degrees of distinct vertices add up to at most the number of adjacency entries. -/
theorem sum_degOf_le (lists : Fin n → List ℕ) {l : List ℕ} (hnd : l.Nodup)
    (hlt : ∀ x ∈ l, x < n) : (l.map (degOf lists)).sum ≤ totalAdjEntries lists := by
  classical
  rw [← List.sum_toFinset _ hnd]
  have hsub : l.toFinset ⊆ Finset.range n := fun x hx =>
    Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  calc ∑ x ∈ l.toFinset, degOf lists x ≤ ∑ x ∈ Finset.range n, degOf lists x :=
        Finset.sum_le_sum_of_subset hsub
    _ = totalAdjEntries lists := by
        rw [totalAdjEntries, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [degOf, x.2]


/-! ### One neighbour -/

/-- The invariant while the neighbours of `u = items[h]` are visited: the first `j` neighbours are
done, and `extra` is what was added to the queue so far. -/
def VInv (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ) (L0 : Fin n → ℕ) (src : List ℕ)
    (s₀ : State) (items : List ℕ) (h : ℕ) (u : Fin n) (j : ℕ) (s : State) : Prop :=
  s.regs rU = u.1 ∧ ∃ extra : List ℕ,
    SFrame s₀ s ∧
    IsQueueHistory aQue rHead rTail n (items ++ extra) (h + 1) s ∧
    (items ++ extra).Nodup ∧
    (∀ x ∈ items ++ extra, x < n) ∧
    (∀ x : Fin n, x.1 ∈ items ++ extra → L0 x = 0) ∧
    s.arrs aLab = List.ofFn (fun x : Fin n => if x.1 ∈ items ++ extra then 1 else L0 x) ∧
    (∃ p : Fin n → ℕ, s.arrs aPar = List.ofFn p ∧ ParentOK G src (items ++ extra) p) ∧
    (∀ u' : Fin n, u'.1 ∈ items.take h → ∀ v, G.Adj u' v → L0 v ≠ 0 ∨ v.1 ∈ items ++ extra) ∧
    (∀ v : Fin n, v.1 ∈ (lists u).take j → L0 v ≠ 0 ∨ v.1 ∈ items ++ extra) ∧
    HitOK G L0 (items ++ extra) (fun v => SeenFrom G items h v ∨ v.1 ∈ (lists u).take j)
      (s.regs rHit) (s.regs rHitPar) ∧
    (∀ x : Fin n, x.1 ∈ src → L0 x = 0 → x.1 ∈ items ++ extra)

theorem SFrame.setReg {s₀ s : State} (hf : SFrame s₀ s) {r : Reg} (hr : 60 ≤ r ∧ r < 71) (v : ℕ) :
    SFrame s₀ (s.setReg r v) := by
  refine ⟨fun r' (hr' : r' < 60 ∨ 71 ≤ r') => ?_, fun a ha1 ha2 ha3 => hf.2 a ha1 ha2 ha3⟩
  have hne : r' ≠ r := by
    rcases hr' with h | h
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h hr.1)
    · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hr.2 h)
  rw [State.setReg_regs_ne s v hne]
  exact hf.1 r' hr'

theorem SFrame.writeArr {s₀ s : State} (hf : SFrame s₀ s) {a : Arr}
    (ha : a = aLab ∨ a = aPar ∨ a = aQue) (i v : ℕ) : SFrame s₀ (s.writeArr a i v) :=
  ⟨fun r hr => by simp only [State.writeArr_regs]; exact hf.1 r hr, fun a' h1 h2 h3 => by
    rw [State.writeArr_arrs_ne _ _ _ (by rcases ha with rfl | rfl | rfl <;> assumption)]
    exact hf.2 a' h1 h2 h3⟩

theorem HitOK.mono_items {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {items e : List ℕ}
    {S S' : Fin n → Prop} {rh rp : ℕ} (h : HitOK G L0 items S rh rp) (hS : ∀ v, S' v → S v) :
    HitOK G L0 (items ++ e) S' rh rp := by
  rcases h with ⟨h1, h2⟩ | ⟨v, u, h1, h2, h3, h4, h5⟩
  · exact Or.inl ⟨h1, fun v hv => h2 v (hS v hv)⟩
  · exact Or.inr ⟨v, u, h1, h2, h3, List.mem_append_left _ h4, h5⟩

theorem HitOK.extend {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {items e : List ℕ}
    {S S' : Fin n → Prop} {rh rp : ℕ} (h : HitOK G L0 items S rh rp)
    (hS : ∀ v, S' v → S v ∨ L0 v ≠ 3) : HitOK G L0 (items ++ e) S' rh rp := by
  rcases h with ⟨h1, h2⟩ | ⟨v, u, h1, h2, h3, h4, h5⟩
  · refine Or.inl ⟨h1, fun v hv => ?_⟩
    rcases hS v hv with h | h
    · exact h2 v h
    · exact h
  · exact Or.inr ⟨v, u, h1, h2, h3, List.mem_append_left _ h4, h5⟩

theorem eval_eq_const {w : ℕ} (s : State) (r : Reg) (c : ℕ) (hr : s.regs r < 2 ^ w)
    (hc : c < 2 ^ w) (hw : 1 < 2 ^ w) :
    (Expr.op .eq (.reg r) (.const c)).eval w s = some (if s.regs r = c then 1 else 0) := by
  by_cases h : s.regs r = c
  · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc, h, hw]
  · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hc, h, show 0 < 2 ^ w by omega]

theorem mem_take_succ_iff {l : List ℕ} {j : ℕ} (hj : j < l.length) {x : ℕ} :
    x ∈ l.take (j + 1) ↔ x ∈ l.take j ∨ x = l[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.mem_append,
    List.mem_singleton]

/-- **Visiting one neighbour.** From `VInv … j`, `searchVisit` on the `j`-th neighbour of `u` gives
`VInv … (j + 1)` in at most `19` steps. -/
theorem searchVisit_exec {w : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (hlists : IsAdjListFamily G lists) (L0 : Fin n → ℕ) (hL0 : ∀ x, L0 x ≤ 3) (src : List ℕ)
    (s₀ : State) (items : List ℕ) (h : ℕ) (u : Fin n) (hu : u.1 ∈ items)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (j : ℕ) (hj : j < (lists u).length)
    (s : State) (hs : VInv G lists L0 src s₀ items h u j s) (hrn : s₀.regs 40 = n) :
    ∃ s' t, Exec w searchVisit (s.setReg rV (lists u)[j]) s' t ∧ t ≤ 19 ∧
      VInv G lists L0 src s₀ items h u (j + 1) s' ∧
      s'.regs rK = s.regs rK ∧ s'.regs rHi = s.regs rHi := by
  obtain ⟨hru, extra, hfr, hq, hnd, hlt, hfree, hlab, ⟨p, hpar, hpok⟩, hcl, hclj, hhit, hsrc⟩ := hs
  set it := items ++ extra with hit_def
  have hvn : (lists u)[j] < n := (hlists u).1 _ (List.getElem_mem hj)
  set v : Fin n := ⟨(lists u)[j], hvn⟩ with hv_def
  have hadj : G.Adj u v := ((hlists u).2.2.2 v).1 (List.getElem_mem hj)
  have hvw : v.1 < 2 ^ w := lt_trans hvn hn
  have huw : u.1 < 2 ^ w := by omega
  have hL0w : L0 v < 2 ^ w := by have := hL0 v; omega
  set lv : ℕ := if v.1 ∈ it then 1 else L0 v with hlv
  have hlvw : lv < 2 ^ w := by simp only [lv]; split_ifs <;> omega
  have hlablen : v.1 < (s.arrs aLab).length := by rw [hlab]; simp
  have hlabv : (s.arrs aLab)[v.1]'hlablen = lv := by simp [hlab, lv, v]
  set s₁ := s.setReg rV v.1 with hs₁
  have hread : (Expr.read aLab (.reg rV)).eval w s₁ = some lv := by
    simp only [Expr.eval, s₁, State.setReg_regs_self, checkWord, hvw, ↓reduceIte,
      State.setReg_arrs, hlablen, ↓reduceDIte, hlabv, hlvw]
  set s₂ := s₁.setReg rL lv with hs₂
  have hex₂ : Exec w (.assign rL (.read aLab (.reg rV))) s₁ s₂ 3 := .assign hread
  have hrl : s₂.regs rL = lv := by simp [s₂]
  have hcond0 : (Expr.op .eq (.reg rL) (.const 0)).eval w s₂ =
      some (if lv = 0 then 1 else 0) := by
    rw [eval_eq_const s₂ rL 0 (by rw [hrl]; exact hlvw) (by omega) (by omega), hrl]
  have hcond3 : (Expr.op .eq (.reg rL) (.const 3)).eval w s₂ =
      some (if lv = 3 then 1 else 0) := by
    rw [eval_eq_const s₂ rL 3 (by rw [hrl]; exact hlvw) (by omega) (by omega), hrl]
  have hfr₂ : SFrame s₀ s₂ := (hfr.setReg (by decide) _).setReg (by decide) _
  have hcl' : ∀ e : List ℕ, (∀ v' : Fin n, v'.1 ∈ (lists u).take (j + 1) → v' = v →
      L0 v' ≠ 0 ∨ v'.1 ∈ it ++ e) →
      ∀ v' : Fin n, v'.1 ∈ (lists u).take (j + 1) → L0 v' ≠ 0 ∨ v'.1 ∈ it ++ e := by
    intro e he v' hv'
    rcases (mem_take_succ_iff hj).1 hv' with hv'' | hv''
    · rcases hclj v' hv'' with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (List.mem_append_left _ h1)
    · exact he v' hv' (Fin.ext hv'')
  by_cases hin : v.1 ∈ it
  · -- already reached: skip
    have hlv1 : lv = 1 := by simp [lv, hin]
    rw [hlv1] at hcond0 hcond3
    have hex : Exec w searchVisit s₁ s₂ (3 + (3 + (3 + 1))) :=
      .seq hex₂ (.ite_false (by simpa using hcond0) (.ite_false (by simpa using hcond3) (.skip _)))
    refine ⟨s₂, _, hex, by omega, ⟨by simp [s₂, s₁, hru], extra, ?_⟩, by simp [s₂, s₁],
      by simp [s₂, s₁]⟩
    refine ⟨hfr₂, hq.of_eq rfl (by simp [s₂, s₁]) (by simp [s₂, s₁]), hnd, hlt, hfree,
      by simp only [s₂, s₁, State.setReg_arrs]; exact hlab,
      ⟨p, by simp only [s₂, s₁, State.setReg_arrs]; exact hpar, hpok⟩, hcl,
      fun v' hv' => by
        have := hcl' [] (fun v' _ e => by rw [e]; exact Or.inr (by simpa using hin)) v' hv'
        simpa only [List.append_nil] using this,
      ?_, hsrc⟩
    have h67 : s₂.regs rHit = s.regs rHit := by simp [s₂, s₁]
    have h68 : s₂.regs rHitPar = s.regs rHitPar := by simp [s₂, s₁]
    rw [h67, h68]
    simpa using (hhit.extend (e := []) fun v' hv' => by
      rcases hv' with hv' | hv'
      · exact Or.inl (Or.inl hv')
      · rcases (mem_take_succ_iff hj).1 hv' with hv'' | hv''
        · exact Or.inl (Or.inr hv'')
        · have : v' = v := Fin.ext hv''
          right; rw [this, hfree v hin]; omega)
  · by_cases h0 : L0 v = 0
    · -- a new vertex: label it, set its parent, put it in the queue
      have hlv0 : lv = 0 := by simp [lv, hin, h0]
      rw [hlv0] at hcond0
      have hlablen₂ : v.1 < (s₂.arrs aLab).length := by simpa [s₂, s₁] using hlablen
      set s₃ := s₂.writeArr aLab v.1 1 with hs₃
      have hex₃ : Exec w (.write aLab (.reg rV) (.const 1)) s₂ s₃ (1 + 1 + 1) :=
        .write (by simp [Expr.eval, checkWord, s₂, s₁, hvw]) (by simp [Expr.eval, checkWord, show 1 < 2 ^ w by omega])
          hlablen₂
      have hparlen : v.1 < (s₃.arrs aPar).length := by simp [s₃, s₂, s₁, hpar]
      set s₄ := s₃.writeArr aPar v.1 u.1 with hs₄
      have hex₄ : Exec w (.write aPar (.reg rV) (.reg rU)) s₃ s₄ (1 + 1 + 1) :=
        .write (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hvw])
          (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hru, huw]) hparlen
      have hlen : it.length < n := length_lt_of_nodup_lt_not_mem hnd hlt hvn hin
      have hq₄ : IsQueueHistory aQue rHead rTail n it (h + 1) s₄ :=
        hq.of_eq (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
          (by simp [s₄, s₃, s₂, s₁])
      obtain ⟨s₅, t₅, hex₅, ht₅, hq₅⟩ := Triple.queuePush_spec aQue rHead rTail (.reg rV) n it
        (h + 1) v.1 (by decide) (by omega) hn hlen s₄
        ⟨hq₄, by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, hvw]⟩
      have hex : Exec w searchVisit s₁ s₅ (3 + (3 + ((1 + 1 + 1) + ((1 + 1 + 1) + t₅)))) :=
        .seq hex₂ (.ite_true (by simpa using hcond0) (by omega) (.seq hex₃ (.seq hex₄ hex₅)))
      simp only [Expr.cost] at ht₅
      have hnotR : ∀ r, r ∉ (queuePush aQue rTail (.reg rV)).writtenRegs → s₅.regs r = s₄.regs r :=
        fun r hr => Exec.regs_eq_of_not_mem_writtenRegs hex₅ hr
      have hnotA : ∀ a, a ∉ (queuePush aQue rTail (.reg rV)).writtenArrs →
          s₅.arrs a = s₄.arrs a := fun a ha => Exec.arrs_eq_of_not_mem_writtenArrs hex₅ ha
      have hR : ∀ r, r ≠ rTail → s₅.regs r = s₄.regs r := fun r hr =>
        hnotR r (by simp [queuePush, Cmd.writtenRegs, hr])
      have hA : ∀ a, a ≠ aQue → s₅.arrs a = s₄.arrs a := fun a ha =>
        hnotA a (by simp [queuePush, Cmd.writtenArrs, ha])
      refine ⟨s₅, _, hex, by omega, ⟨by rw [hR _ (by decide)]; simp [s₄, s₃, s₂, s₁, hru],
        extra ++ [v.1], ?_⟩, by rw [hR _ (by decide)]; simp [s₄, s₃, s₂, s₁],
        by rw [hR _ (by decide)]; simp [s₄, s₃, s₂, s₁]⟩
      have happ : items ++ (extra ++ [v.1]) = it ++ [v.1] := by simp [it]
      rw [happ]
      have hfr₅ : SFrame s₀ s₅ := by
        refine ⟨fun r (hr : r < 60 ∨ 71 ≤ r) => ?_, fun a h1 h2 h3 => ?_⟩
        · have hne : r ≠ 61 := by
            rcases hr with hh | hh
            · exact Nat.ne_of_lt (Nat.lt_trans hh (by decide))
            · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hh)
          rw [hR r hne]
          exact ((hfr₂.writeArr (Or.inl rfl) _ _).writeArr (Or.inr (Or.inl rfl)) _ _).1 r hr
        · rw [hA a h3]
          exact ((hfr₂.writeArr (Or.inl rfl) _ _).writeArr (Or.inr (Or.inl rfl)) _ _).2 a h1 h2 h3
      have hmem_new : ∀ x : ℕ, x ∈ it ++ [v.1] ↔ x ∈ it ∨ x = v.1 := by simp
      refine ⟨hfr₅, hq₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        exact ⟨hnd, List.nodup_singleton _, fun x hx y hy hxy => by
          simp at hy; subst hy; subst hxy; exact hin hx⟩
      · intro x hx
        rcases (hmem_new x).1 hx with hx | rfl
        · exact hlt x hx
        · exact hvn
      · intro x hx
        rcases (hmem_new x.1).1 hx with hx | hx
        · exact hfree x hx
        · rw [show x = v from Fin.ext hx]; exact h0
      · rw [hA _ (by decide)]
        simp only [s₄, s₃, State.writeArr_arrs_ne _ _ _ (show (60 : ℕ) ≠ 61 by decide),
          State.writeArr_arrs_self, s₂, s₁, State.setReg_arrs, hlab]
        rw [ofFn_set v]
        congr 1
        funext x
        simp only [Function.update_apply, hmem_new]
        by_cases hxv : x = v
        · subst hxv; simp
        · have : x.1 ≠ v.1 := fun e => hxv (Fin.ext e)
          simp [hxv, this]
      · refine ⟨Function.update p v u.1, ?_, ?_⟩
        · rw [hA _ (by decide)]
          simp only [s₄, State.writeArr_arrs_self, s₃,
            State.writeArr_arrs_ne _ _ _ (show (61 : ℕ) ≠ 60 by decide), s₂, s₁,
            State.setReg_arrs, hpar]
          exact ofFn_set v _
        · intro x hx
          rcases (hmem_new x.1).1 hx with hx' | hx'
          · have hxv : x ≠ v := fun e => hin (e ▸ hx')
            rw [Function.update_of_ne hxv]
            obtain ⟨h0, hrest⟩ := hpok x hx'
            refine ⟨h0, ?_⟩
            rcases hrest with h1 | ⟨u', h1, h2, h3, h4⟩
            · exact Or.inl h1
            · refine Or.inr ⟨u', h1, List.mem_append_left _ h2, ?_, h4⟩
              rw [idxOf_append_mem h2, idxOf_append_mem hx']
              exact h3
          · have hxv : x = v := Fin.ext hx'
            subst hxv
            rw [Function.update_self]
            have huit : u.1 ∈ it := List.mem_append_left _ hu
            refine ⟨fun hxs => absurd (hsrc v hxs h0) hin,
              Or.inr ⟨u, rfl, List.mem_append_left _ huit, ?_, hadj⟩⟩
            rw [idxOf_append_mem huit, List.idxOf_append_of_notMem hin]
            simp only [List.idxOf_cons_self, Nat.add_zero]
            exact List.idxOf_lt_length_of_mem huit
      · intro u' hu' v' hv'
        rcases hcl u' hu' v' hv' with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (List.mem_append_left _ h1)
      · exact hcl' [v.1] fun v' _ e => by subst e; exact Or.inr (by simp)
      · rw [hR _ (by decide), hR _ (by decide)]
        simp only [s₄, s₃, State.writeArr_regs, s₂, s₁,
          State.setReg_regs_ne _ _ (show (67 : ℕ) ≠ 66 by decide),
          State.setReg_regs_ne _ _ (show (67 : ℕ) ≠ 65 by decide),
          State.setReg_regs_ne _ _ (show (68 : ℕ) ≠ 66 by decide),
          State.setReg_regs_ne _ _ (show (68 : ℕ) ≠ 65 by decide)]
        refine hhit.extend fun v' hv' => ?_
        rcases hv' with hv' | hv'
        · exact Or.inl (Or.inl hv')
        · rcases (mem_take_succ_iff hj).1 hv' with hv'' | hv''
          · exact Or.inl (Or.inr hv'')
          · have : v' = v := Fin.ext hv''
            right; rw [this, h0]; omega
      · intro x hx1 hx2
        exact List.mem_append_left _ (hsrc x hx1 hx2)
    · -- a forbidden vertex or a target
      have hlvL : lv = L0 v := by simp [lv, hin]
      have hcond0' : (Expr.op .eq (.reg rL) (.const 0)).eval w s₂ = some 0 := by
        rw [hcond0, hlvL]; simp [h0]
      have hkeep : ∀ s' : State, s'.regs rU = s₂.regs rU → (∀ a, s'.arrs a = s₂.arrs a) →
          (∀ r, r ≠ rHit → r ≠ rHitPar → s'.regs r = s₂.regs r) →
          HitOK G L0 it (fun v' => SeenFrom G items h v' ∨ v'.1 ∈ (lists u).take (j + 1))
            (s'.regs rHit) (s'.regs rHitPar) →
          VInv G lists L0 src s₀ items h u (j + 1) s' := by
        intro s' hU hA hR hH
        refine ⟨by rw [hU]; simp [s₂, s₁, hru], extra, ?_, ?_, hnd, hlt, hfree, ?_, ?_, hcl, ?_,
          hH, hsrc⟩
        · refine ⟨fun r (hr : r < 60 ∨ 71 ≤ r) => ?_, fun a h1 h2 h3 => ?_⟩
          · have h1 : r ≠ 67 := by
              rcases hr with hh | hh
              · exact Nat.ne_of_lt (Nat.lt_trans hh (by decide))
              · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hh)
            have h2 : r ≠ 68 := by
              rcases hr with hh | hh
              · exact Nat.ne_of_lt (Nat.lt_trans hh (by decide))
              · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hh)
            rw [hR r h1 h2]; exact hfr₂.1 r hr
          · rw [hA a]; exact hfr₂.2 a h1 h2 h3
        · exact hq.of_eq (by rw [hA]; simp [s₂, s₁]) (by rw [hR _ (by decide) (by decide)]; simp [s₂, s₁])
            (by rw [hR _ (by decide) (by decide)]; simp [s₂, s₁])
        · rw [hA]; simp only [s₂, s₁, State.setReg_arrs]; exact hlab
        · exact ⟨p, by rw [hA]; simp only [s₂, s₁, State.setReg_arrs]; exact hpar, hpok⟩
        · intro v' hv'
          have := hcl' [] (fun v' _ e => by rw [e]; exact Or.inl h0) v' hv'
          simpa only [List.append_nil] using this
      by_cases h3 : L0 v = 3
      · have hcond3' : (Expr.op .eq (.reg rL) (.const 3)).eval w s₂ = some 1 := by
          rw [hcond3, hlvL]; simp [h3]
        set s₃ := s₂.setReg rHit v.1 with hs₃
        have hex₃ : Exec w (.assign rHit (.reg rV)) s₂ s₃ 2 :=
          .assign (by simp [Expr.eval, checkWord, s₂, s₁, hvw])
        set s₄ := s₃.setReg rHitPar u.1 with hs₄
        have hex₄ : Exec w (.assign rHitPar (.reg rU)) s₃ s₄ 2 :=
          .assign (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hru, huw])
        have hex : Exec w searchVisit s₁ s₄ (3 + (3 + (3 + (2 + 2)))) :=
          .seq hex₂ (.ite_false hcond0' (.ite_true hcond3' (by omega) (.seq hex₃ hex₄)))
        refine ⟨s₄, _, hex, by omega, hkeep s₄ (by simp [s₄, s₃]) (fun a => by simp [s₄, s₃])
          (fun r h1 h2 => by simp [s₄, s₃, h1, h2]) ?_, by simp [s₄, s₃, s₂, s₁],
          by simp [s₄, s₃, s₂, s₁]⟩
        exact Or.inr ⟨v, u, by simp [s₄, s₃], by simp [s₄], h3, List.mem_append_left _ hu, hadj⟩
      · have hcond3' : (Expr.op .eq (.reg rL) (.const 3)).eval w s₂ = some 0 := by
          rw [hcond3, hlvL]; simp [h3]
        have hex : Exec w searchVisit s₁ s₂ (3 + (3 + (3 + 1))) :=
          .seq hex₂ (.ite_false hcond0' (.ite_false hcond3' (.skip _)))
        refine ⟨s₂, _, hex, by omega, hkeep s₂ rfl (fun _ => rfl) (fun _ _ _ => rfl) ?_,
          by simp [s₂, s₁], by simp [s₂, s₁]⟩
        have h67 : s₂.regs rHit = s.regs rHit := by simp [s₂, s₁]
        have h68 : s₂.regs rHitPar = s.regs rHitPar := by simp [s₂, s₁]
        rw [h67, h68]
        simpa using (hhit.extend (e := []) fun v' hv' => by
          rcases hv' with hv' | hv'
          · exact Or.inl (Or.inl hv')
          · rcases (mem_take_succ_iff hj).1 hv' with hv'' | hv''
            · exact Or.inl (Or.inr hv'')
            · have : v' = v := Fin.ext hv''
              right; rw [this]; exact h3)


/-- `VInv` does not see the registers of the adjacency-list loop. -/
theorem VInv.setReg {G : SimpleGraph (Fin n)} {lists : Fin n → List ℕ} {L0 : Fin n → ℕ}
    {src : List ℕ} {s₀ : State} {items : List ℕ} {h : ℕ} {u : Fin n} {j : ℕ} {s : State}
    (hs : VInv G lists L0 src s₀ items h u j s) {r : Reg} (hr : r = rK ∨ r = rHi ∨ r = rV)
    (v : ℕ) : VInv G lists L0 src s₀ items h u j (s.setReg r v) := by
  have h62 : r ≠ 62 := by rcases hr with rfl | rfl | rfl <;> decide
  have h60 : r ≠ 60 := by rcases hr with rfl | rfl | rfl <;> decide
  have h61 : r ≠ 61 := by rcases hr with rfl | rfl | rfl <;> decide
  have h67 : r ≠ 67 := by rcases hr with rfl | rfl | rfl <;> decide
  have h68 : r ≠ 68 := by rcases hr with rfl | rfl | rfl <;> decide
  obtain ⟨hru, extra, hfr, hq, rest⟩ := hs
  refine ⟨by rw [State.setReg_regs_ne _ _ (Ne.symm h62)]; exact hru, extra,
    hfr.setReg (by rcases hr with rfl | rfl | rfl <;> decide) v,
    hq.of_eq rfl (by simp [Ne.symm h60]) (by simp [Ne.symm h61]), ?_⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := rest
  refine ⟨a1, a2, a3, by simpa using a4, by simpa using a5, a6, a7, ?_, a9⟩
  rwa [State.setReg_regs_ne _ _ (Ne.symm h67), State.setReg_regs_ne _ _ (Ne.symm h68)]

/-! ### One round -/

/-- **One round of the search.** From `SInv` with a vertex left in the queue, `searchStep` takes
the next vertex `u` and visits its neighbours, in at most `16 + 29 deg u` steps. -/
theorem searchStep_exec {w : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (gS gE gEnt : Arr) (hgS : gS < 60) (hgE : gE < 60) (hgEnt : gEnt < 60)
    (L0 : Fin n → ℕ) (hL0 : ∀ x, L0 x ≤ 3) (src : List ℕ) (s₀ : State)
    (hadj : IsAdjList G gS gE gEnt lists s₀) (hent : (s₀.arrs gEnt).length < 2 ^ w)
    (hrn : s₀.regs 40 = n) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (items : List ℕ) (h : ℕ) (hh : h < items.length) (s : State)
    (hs : SInv G L0 src s₀ items h s) :
    ∃ s' t extra, Exec w (searchStep gS gE gEnt) s s' t ∧
      t ≤ 16 + 29 * degOf lists items[h] ∧
      SInv G L0 src s₀ (items ++ extra) (h + 1) s' := by
  have hun : items[h] < n := hs.lt _ (List.getElem_mem hh)
  set u : Fin n := ⟨items[h], hun⟩ with hu_def
  have hu_mem : u.1 ∈ items := List.getElem_mem hh
  obtain ⟨s₁, t₁, hex₁, ht₁, hq₁, hru₁⟩ := Triple.queuePop_spec aQue rHead rTail rU n items h
    (by decide) (by decide) (by decide) (by omega) hn hh (by omega) s hs.queue
  dsimp only at ht₁
  have hR₁ : ∀ r, r ≠ rHead → r ≠ rU → s₁.regs r = s.regs r := fun r h1 h2 =>
    Exec.regs_eq_of_not_mem_writtenRegs hex₁ (by simp [queuePop, Cmd.writtenRegs, h1, h2])
  have hA₁ : ∀ a, s₁.arrs a = s.arrs a := fun a =>
    Exec.arrs_eq_of_not_mem_writtenArrs hex₁ (by simp [queuePop, Cmd.writtenArrs])
  have hgarr : ∀ a, a < 60 → ∀ st : State, SFrame s₀ st → st.arrs a = s₀.arrs a :=
    fun a ha st hf => hf.2 a (Nat.ne_of_lt ha) (Nat.ne_of_lt (Nat.lt_trans ha (by decide)))
      (Nat.ne_of_lt (Nat.lt_trans ha (by decide)))
  obtain ⟨st, en, hlist₀⟩ := hadj.1.2.2 u
  obtain ⟨hmem_lt, -, -, hadj_iff⟩ := hadj.2 u
  have hlistOf : ∀ st' : State, SFrame s₀ st' →
      IsListAt gS gE gEnt u.1 st en (lists u) st' := fun st' hf =>
    hlist₀.of_arrs_eq (hgarr gS hgS st' hf) (hgarr gE hgE st' hf) (hgarr gEnt hgEnt st' hf)
  have hfr₁ : SFrame s₀ s₁ := by
    refine ⟨fun r (hr : r < 60 ∨ 71 ≤ r) => ?_, fun a h1 h2 h3 => by rw [hA₁]; exact hs.frame.2 a h1 h2 h3⟩
    have h1 : r ≠ 60 := by
      rcases hr with hh | hh
      · exact Nat.ne_of_lt hh
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hh)
    have h2 : r ≠ 62 := by
      rcases hr with hh | hh
      · exact Nat.ne_of_lt (Nat.lt_trans hh (by decide))
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hh)
    rw [hR₁ r h1 h2]; exact hs.frame.1 r hr
  have hen_w : en < 2 ^ w := by
    obtain ⟨_, _, hle, _⟩ := hlist₀
    omega
  have hI0 : VInv G lists L0 src s₀ items h u 0 s₁ := by
    refine ⟨hru₁, [], ?_⟩
    simp only [List.append_nil, List.take_zero, List.not_mem_nil, false_or, IsEmpty.forall_iff,
      implies_true, true_and]
    refine ⟨hfr₁, hq₁, hs.nodup, hs.lt, hs.free, by rw [hA₁]; exact hs.lab,
      by obtain ⟨p, hp, hpo⟩ := hs.par; exact ⟨p, by rw [hA₁]; exact hp, hpo⟩, hs.closed, ?_,
      hs.srcs⟩
    rw [hR₁ _ (by decide) (by decide), hR₁ _ (by decide) (by decide)]
    simpa using (hs.hit.extend (e := []) fun v hv => Or.inl hv)
  have hfor := Triple.forList_const gS gE gEnt rU rK rHi rV u.1 st en (lists u)
    (VInv G lists L0 src s₀ items h u) 19 searchVisit (by decide) (by decide) (by omega)
    (by omega) hen_w (fun x hx => by have := hmem_lt x hx; omega)
    (fun st' hst' => ⟨hlistOf st' hst'.2.choose_spec.1, hst'.1,
      (hst'.setReg (Or.inl rfl) st).setReg (Or.inr (Or.inl rfl)) en⟩)
    (fun j _ st' hst' => hlistOf st' hst'.2.choose_spec.1)
    (fun j hj sv ⟨st', hI, hsv, hrk, hrhi⟩ => by
      subst hsv
      obtain ⟨s', t, hex, ht, hI', hk, hhi⟩ := searchVisit_exec G lists hadj.2 L0 hL0 src s₀ items
        h u hu_mem hw hn j hj st' hI hrn
      refine ⟨s', t, hex, ht, hI'.setReg (Or.inl rfl) _, by rw [hk]; simpa using hrk,
        by rw [hhi]; simpa using hrhi⟩)
  obtain ⟨s₂, t₂, hex₂, ht₂, hI⟩ := hfor s₁ hI0
  obtain ⟨hru₂, extra, hfr₂, hq₂, hnd₂, hlt₂, hfree₂, hlab₂, hpar₂, hcl₂, hclj₂, hhit₂, hsrc₂⟩ := hI
  rw [List.take_length] at hclj₂ hhit₂
  have htake : (items ++ extra).take (h + 1) = items.take h ++ [u.1] := take_succ_append_eq hh
  refine ⟨s₂, t₁ + t₂, extra, .seq hex₁ hex₂, ?_, ⟨hfr₂, hq₂, hnd₂, hlt₂, hfree₂, hlab₂, hpar₂,
    ?_, ?_, hsrc₂⟩⟩
  · have hdeg : degOf lists items[h] = (lists u).length := by simp [degOf, hun, u]
    rw [hdeg]; dsimp only at ht₂; omega
  · intro u' hu' v hv
    rw [htake, List.mem_append, List.mem_singleton] at hu'
    rcases hu' with hu' | hu'
    · exact hcl₂ u' hu' v hv
    · have : u' = u := Fin.ext hu'
      subst this
      exact hclj₂ v ((hadj_iff v).2 hv)
  · refine (hhit₂.extend (e := []) fun v hv => ?_).elim (fun h => Or.inl (by simpa using h))
      (fun h => Or.inr (by simpa using h))
    obtain ⟨u', hu', hadj'⟩ := hv
    rw [htake, List.mem_append, List.mem_singleton] at hu'
    rcases hu' with hu' | hu'
    · exact Or.inl (Or.inl ⟨u', hu', hadj'⟩)
    · have : u' = u := Fin.ext hu'
      subst this
      exact Or.inl (Or.inr ((hadj_iff v).2 hadj'))


/-! ### The main loop -/

theorem length_le_of_nodup_lt {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    l.length ≤ n := by
  classical
  have hsub : l.toFinset ⊆ Finset.range n := fun x hx =>
    Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this

/-- The degrees of the vertices taken from the queue so far. -/
def popDeg (lists : Fin n → List ℕ) (items : List ℕ) (h : ℕ) : ℕ :=
  ((items.take h).map (degOf lists)).sum

/-- **The main loop.** From `SInv` the loop runs until the queue is empty, within
`3 + 19 (n - h) + 29 (m₂ - popDeg)` steps, where `m₂` is the number of adjacency entries. -/
theorem searchLoop_exec {w : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (gS gE gEnt : Arr) (hgS : gS < 60) (hgE : gE < 60) (hgEnt : gEnt < 60)
    (L0 : Fin n → ℕ) (hL0 : ∀ x, L0 x ≤ 3) (src : List ℕ) (s₀ : State)
    (hadj : IsAdjList G gS gE gEnt lists s₀) (hent : (s₀.arrs gEnt).length < 2 ^ w)
    (hrn : s₀.regs 40 = n) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) :
    ∀ (k : ℕ) (items : List ℕ) (h : ℕ) (s : State), n - h = k → SInv G L0 src s₀ items h s →
      ∃ s' t items', Exec w (searchLoop gS gE gEnt) s s' t ∧
        t ≤ 3 + 19 * (n - h) + 29 * (totalAdjEntries lists - popDeg lists items h) ∧
        t + 19 * h + 29 * popDeg lists items h ≤ 3 + 19 * (items ++ items').length +
          29 * popDeg lists (items ++ items') (items ++ items').length ∧
        SInv G L0 src s₀ (items ++ items') (items ++ items').length s' := by
  intro k
  induction k with
  | zero =>
    intro items h s hk hs
    have hlen := length_le_of_nodup_lt hs.nodup hs.lt
    obtain ⟨-, -, hhd, htl, hle, -⟩ := hs.queue
    have hh : h = items.length := by omega
    have hcond : (Expr.op .lt (.reg rHead) (.reg rTail)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hhd, htl, hh,
        show items.length < 2 ^ w by omega, show 0 < 2 ^ w by omega]
    refine ⟨s, _, [], .while_false hcond, by simp only [Expr.cost]; omega,
      by simp only [Expr.cost, List.append_nil, ← hh]; omega, ?_⟩
    simpa [← hh] using hs
  | succ k ih =>
    intro items h s hk hs
    have hlen := length_le_of_nodup_lt hs.nodup hs.lt
    obtain ⟨-, -, hhd, htl, hle, -⟩ := hs.queue
    by_cases hh : h = items.length
    · have hcond : (Expr.op .lt (.reg rHead) (.reg rTail)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hhd, htl, hh,
          show items.length < 2 ^ w by omega, show 0 < 2 ^ w by omega]
      refine ⟨s, _, [], .while_false hcond, by simp only [Expr.cost]; omega,
        by simp only [Expr.cost, List.append_nil, ← hh]; omega, ?_⟩
      simpa [← hh] using hs
    have hlt : h < items.length := by omega
    have hcond : (Expr.op .lt (.reg rHead) (.reg rTail)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hhd, htl, hlt,
        show items.length < 2 ^ w by omega, show h < 2 ^ w by omega, show 1 < 2 ^ w by omega]
    obtain ⟨s₁, t₁, extra, hex₁, ht₁, hs₁⟩ := searchStep_exec G lists gS gE gEnt hgS hgE hgEnt L0
      hL0 src s₀ hadj hent hrn hw hn items h hlt s hs
    obtain ⟨s₂, t₂, items', hex₂, ht₂, ht₂', hs₂⟩ :=
      ih (items ++ extra) (h + 1) s₁ (by omega) hs₁
    have hpop : popDeg lists (items ++ extra) (h + 1) = popDeg lists items h +
        degOf lists items[h] := by
      rw [popDeg, popDeg, take_succ_append_eq hlt, List.map_append, List.sum_append]
      simp
    have hbound := sum_degOf_le lists (hs₁.nodup.sublist (List.take_sublist (h + 1) _))
      (fun x hx => hs₁.lt x (List.mem_of_mem_take hx))
    rw [← popDeg] at hbound
    refine ⟨s₂, _, extra ++ items', .while_true hcond (by omega) hex₁ hex₂, ?_, ?_, by
      simpa [List.append_assoc] using hs₂⟩
    · rw [hpop] at ht₂ hbound
      simp only [Expr.cost] at ⊢
      omega
    · rw [hpop, List.append_assoc] at ht₂'
      simp only [Expr.cost] at ⊢
      omega


/-! ### The sources -/

/-- The invariant of the loop over the sources: the first `i` sources are done. -/
def SrcInv (G : SimpleGraph (Fin n)) (L0 : Fin n → ℕ) (src : List ℕ) (s₀ : State) (i : ℕ)
    (s : State) : Prop :=
  s.regs rI = i ∧ ∃ items : List ℕ,
    SFrame s₀ s ∧ IsQueueHistory aQue rHead rTail n items 0 s ∧ items.Nodup ∧
    (∀ x ∈ items, x < n) ∧ (∀ x : Fin n, x.1 ∈ items → L0 x = 0) ∧
    s.arrs aLab = List.ofFn (fun x : Fin n => if x.1 ∈ items then 1 else L0 x) ∧
    (∃ p : Fin n → ℕ, s.arrs aPar = List.ofFn p ∧ ParentOK G src items p) ∧
    s.regs rHit = n ∧ (∀ x : Fin n, x.1 ∈ src.take i → L0 x = 0 → x.1 ∈ items)

/-- **One source.** -/
theorem searchSource_exec {w : ℕ} (G : SimpleGraph (Fin n)) (L0 : Fin n → ℕ)
    (hL0 : ∀ x, L0 x ≤ 3) (src : List ℕ) (hsrc : ∀ x ∈ src, x < n) (s₀ : State)
    (hsrc₀ : s₀.arrs aSrc = src) (hrn : s₀.regs 40 = n) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hsw : src.length < 2 ^ w) (i : ℕ) (hi : i < src.length) (s : State)
    (hs : SrcInv G L0 src s₀ i s) :
    ∃ s' t, Exec w searchSource s s' t ∧ t ≤ 22 ∧
      SrcInv G L0 src s₀ (i + 1) (s'.setReg rI (i + 1)) ∧ s'.regs rI = i := by
  obtain ⟨hri, items, hfr, hq, hnd, hlt, hfree, hlab, ⟨p, hpar, hpok⟩, hhit, hdone⟩ := hs
  have hxn : src[i] < n := hsrc _ (List.getElem_mem hi)
  set x : Fin n := ⟨src[i], hxn⟩ with hx_def
  have hxw : x.1 < 2 ^ w := lt_trans hxn hn
  have hsrcS : s.arrs aSrc = src := by rw [hfr.2 aSrc (by decide) (by decide) (by decide), hsrc₀]
  have hrnS : s.regs 40 = n := by rw [hfr.1 40 (Or.inl (by decide)), hrn]
  have hread₁ : (Expr.read aSrc (.reg rI)).eval w s = some x.1 := by
    simp [Expr.eval, checkWord, hri, hsrcS, hi, show i < 2 ^ w by omega, x, hxw]
  set s₁ := s.setReg rX x.1 with hs₁
  have hex₁ : Exec w (.assign rX (.read aSrc (.reg rI))) s s₁ 3 := .assign hread₁
  set lx : ℕ := if x.1 ∈ items then 1 else L0 x with hlx
  have hlxw : lx < 2 ^ w := by
    simp only [lx]; split_ifs
    · omega
    · have := hL0 x; omega
  have hread₂ : (Expr.read aLab (.reg rX)).eval w s₁ = some lx := by
    have hlen : x.1 < (s₁.arrs aLab).length := by simp [s₁, hlab]
    simp only [Expr.eval, s₁, State.setReg_regs_self, checkWord, hxw, ↓reduceIte,
      State.setReg_arrs]
    simp [hlab, lx, hlxw, x, hxn]
  set s₂ := s₁.setReg rL lx with hs₂
  have hex₂ : Exec w (.assign rL (.read aLab (.reg rX))) s₁ s₂ 3 := .assign hread₂
  have hrl : s₂.regs rL = lx := by simp [s₂]
  have hcond := eval_eq_const s₂ rL 0 (by rw [hrl]; exact hlxw) (by omega) (by omega)
  rw [hrl] at hcond
  have hfr₂ : SFrame s₀ s₂ := (hfr.setReg (by decide) _).setReg (by decide) _
  by_cases hnew : x.1 ∉ items ∧ L0 x = 0
  · have hlx0 : lx = 0 := by simp [lx, hnew.1, hnew.2]
    rw [hlx0] at hcond
    set s₃ := s₂.writeArr aLab x.1 1 with hs₃
    have hex₃ : Exec w (.write aLab (.reg rX) (.const 1)) s₂ s₃ 3 :=
      .write (by simp [Expr.eval, checkWord, s₂, s₁, hxw])
        (by simp [Expr.eval, checkWord, show 1 < 2 ^ w by omega]) (by simp [s₂, s₁, hlab])
    set s₄ := s₃.writeArr aPar x.1 n with hs₄
    have hex₄ : Exec w (.write aPar (.reg rX) (.reg 40)) s₃ s₄ 3 :=
      .write (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hxw])
        (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hrnS, hn]) (by simp [s₃, s₂, s₁, hpar])
    have hlen : items.length < n := length_lt_of_nodup_lt_not_mem hnd hlt hxn hnew.1
    have hq₄ : IsQueueHistory aQue rHead rTail n items 0 s₄ :=
      hq.of_eq (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
    obtain ⟨s₅, t₅, hex₅, ht₅, hq₅⟩ := Triple.queuePush_spec aQue rHead rTail (.reg rX) n items 0
      x.1 (by decide) (by omega) hn hlen s₄ ⟨hq₄, by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, hxw]⟩
    simp only [Expr.cost] at ht₅
    have hR : ∀ r, r ≠ rTail → s₅.regs r = s₄.regs r := fun r hr =>
      Exec.regs_eq_of_not_mem_writtenRegs hex₅ (by simp [queuePush, Cmd.writtenRegs, hr])
    have hA : ∀ a, a ≠ aQue → s₅.arrs a = s₄.arrs a := fun a ha =>
      Exec.arrs_eq_of_not_mem_writtenArrs hex₅ (by simp [queuePush, Cmd.writtenArrs, ha])
    have hex : Exec w searchSource s s₅ (3 + (3 + (3 + (3 + (3 + t₅))))) :=
      .seq hex₁ (.seq hex₂ (.ite_true (by simpa using hcond) (by omega) (.seq hex₃ (.seq hex₄ hex₅))))
    have hri₅ : s₅.regs rI = i := by rw [hR _ (by decide)]; simp [s₄, s₃, s₂, s₁, hri]
    refine ⟨s₅, _, hex, by omega, ⟨by simp, items ++ [x.1], ?_⟩, hri₅⟩
    have hmem : ∀ y : ℕ, y ∈ items ++ [x.1] ↔ y ∈ items ∨ y = x.1 := by simp
    refine ⟨?_, hq₅.of_eq rfl (by simp) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine (SFrame.setReg ?_ (by decide) _)
      refine ⟨fun r (hr : r < 60 ∨ 71 ≤ r) => ?_, fun a h1 h2 h3 => ?_⟩
      · have hne : r ≠ 61 := by
          rcases hr with hh | hh
          · exact Nat.ne_of_lt (Nat.lt_trans hh (by decide))
          · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hh)
        rw [hR r hne]
        exact ((hfr₂.writeArr (Or.inl rfl) _ _).writeArr (Or.inr (Or.inl rfl)) _ _).1 r hr
      · rw [hA a h3]
        exact ((hfr₂.writeArr (Or.inl rfl) _ _).writeArr (Or.inr (Or.inl rfl)) _ _).2 a h1 h2 h3
    · rw [List.nodup_append]
      exact ⟨hnd, List.nodup_singleton _, fun a ha b hb hab => by
        simp at hb; subst hb; subst hab; exact hnew.1 ha⟩
    · intro y hy
      rcases (hmem y).1 hy with hy | rfl
      · exact hlt y hy
      · exact hxn
    · intro y hy
      rcases (hmem y.1).1 hy with hy | hy
      · exact hfree y hy
      · rw [show y = x from Fin.ext hy]; exact hnew.2
    · simp only [State.setReg_arrs]
      rw [hA _ (by decide)]
      simp only [s₄, s₃, State.writeArr_arrs_ne _ _ _ (show (60 : ℕ) ≠ 61 by decide),
        State.writeArr_arrs_self, s₂, s₁, State.setReg_arrs, hlab]
      rw [ofFn_set x]
      congr 1
      funext y
      simp only [Function.update_apply, hmem]
      by_cases hyx : y = x
      · subst hyx; simp
      · have : y.1 ≠ x.1 := fun e => hyx (Fin.ext e)
        simp [hyx, this]
    · refine ⟨Function.update p x n, ?_, ?_⟩
      · simp only [State.setReg_arrs]
        rw [hA _ (by decide)]
        simp only [s₄, State.writeArr_arrs_self, s₃,
          State.writeArr_arrs_ne _ _ _ (show (61 : ℕ) ≠ 60 by decide), s₂, s₁,
          State.setReg_arrs, hpar]
        exact ofFn_set x _
      · intro y hy
        rcases (hmem y.1).1 hy with hy' | hy'
        · have hyx : y ≠ x := fun e => hnew.1 (e ▸ hy')
          rw [Function.update_of_ne hyx]
          obtain ⟨h0, hrest⟩ := hpok y hy'
          refine ⟨h0, ?_⟩
          rcases hrest with h1 | ⟨u', h1, h2, h3, h4⟩
          · exact Or.inl h1
          · refine Or.inr ⟨u', h1, List.mem_append_left _ h2, ?_, h4⟩
            rw [idxOf_append_mem h2, idxOf_append_mem hy']
            exact h3
        · rw [show y = x from Fin.ext hy', Function.update_self]
          exact ⟨fun _ => rfl, Or.inl ⟨rfl, List.getElem_mem hi⟩⟩
    · simp only [State.setReg_regs_ne _ _ (show (67 : ℕ) ≠ 69 by decide)]
      rw [hR _ (by decide)]
      simp [s₄, s₃, s₂, s₁, hhit]
    · intro y hy hy0
      rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.mem_append,
        List.mem_singleton] at hy
      rcases hy with hy | hy
      · exact List.mem_append_left _ (hdone y hy hy0)
      · exact (hmem y.1).2 (Or.inr hy)
  · have hlx : lx ≠ 0 := by
      simp only [lx]
      split_ifs with h
      · omega
      · intro h0; exact hnew ⟨h, h0⟩
    have hcond' : (Expr.op .eq (.reg rL) (.const 0)).eval w s₂ = some 0 := by
      rw [hcond]; simp [hlx]
    have hex : Exec w searchSource s s₂ (3 + (3 + (3 + 1))) :=
      .seq hex₁ (.seq hex₂ (.ite_false hcond' (.skip _)))
    refine ⟨s₂, _, hex, by omega, ⟨by simp, items, ?_⟩, by simp [s₂, s₁, hri]⟩
    refine ⟨hfr₂.setReg (by decide) _, hq.of_eq rfl (by simp [s₂, s₁]) (by simp [s₂, s₁]), hnd,
      hlt, hfree, by simp [s₂, s₁, hlab], ⟨p, by simp [s₂, s₁, hpar], hpok⟩,
      by simp [s₂, s₁, hhit], ?_⟩
    intro y hy hy0
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.mem_append,
      List.mem_singleton] at hy
    rcases hy with hy | hy
    · exact hdone y hy hy0
    · have hyx : y = x := Fin.ext hy
      subst hyx
      by_contra hc
      exact hnew ⟨hc, hy0⟩


/-- **The loop over the sources.** -/
theorem searchSources_exec {w : ℕ} (G : SimpleGraph (Fin n)) (L0 : Fin n → ℕ)
    (hL0 : ∀ x, L0 x ≤ 3) (src : List ℕ) (hsrc : ∀ x ∈ src, x < n) (s₀ : State)
    (hsrc₀ : s₀.arrs aSrc = src) (hrn : s₀.regs 40 = n) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hsw : src.length < 2 ^ w) :
    ⦃SrcInv G L0 src s₀ 0⦄[w] forUp rI (.len aSrc) searchSource
      ⦃SrcInv G L0 src s₀ src.length⦄ ≤ fun _ => 3 + src.length * 29 := by
  have h := Triple.forUp_const (SrcInv G L0 src s₀) src.length 22 (r_i := rI) (hi := .len aSrc)
    (body := searchSource) (w := w) (by omega) hsw ?_ ?_
  · exact h.mono_cost fun _ _ => by simp only [Expr.cost]; omega
  · intro i _ s hs
    refine ⟨hs.1, ?_⟩
    obtain ⟨-, items, hfr, -⟩ := hs
    have : s.arrs aSrc = src := by rw [hfr.2 aSrc (by decide) (by decide) (by decide), hsrc₀]
    simp [Expr.eval, checkWord, this, hsw]
  · intro i hi s hs
    obtain ⟨s', t, hex, ht, hI, hr⟩ :=
      searchSource_exec G L0 hL0 src hsrc s₀ hsrc₀ hrn hw hn hsw i hi s hs
    exact ⟨s', t, hex, ht, hI, hr⟩

/-- At the end of the loop over the sources, the invariant of the main loop holds with head `0`. -/
theorem SrcInv.sInv {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {src : List ℕ} {s₀ s : State}
    (hs : SrcInv G L0 src s₀ src.length s) : ∃ items, SInv G L0 src s₀ items 0 s := by
  obtain ⟨-, items, hfr, hq, hnd, hlt, hfree, hlab, hpar, hhit, hdone⟩ := hs
  refine ⟨items, hfr, hq, hnd, hlt, hfree, hlab, hpar, by simp, ?_, ?_⟩
  · exact Or.inl ⟨hhit, fun v ⟨u, hu, _⟩ => by simp at hu⟩
  · intro x hx hx0
    exact hdone x (by simpa using hx) hx0

/-- **The search.** It starts from the labels `L0` in array `aLab` and the sources in array
`aSrc`. It ends with the main-loop invariant for a queue history `items` that was fully
scanned. -/
theorem searchProg_exec {w : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (gS gE gEnt : Arr) (hgS : gS < 60) (hgE : gE < 60) (hgEnt : gEnt < 60)
    (L0 : Fin n → ℕ) (hL0 : ∀ x, L0 x ≤ 3) (src : List ℕ) (hsrc : ∀ x ∈ src, x < n)
    (s₀ : State) (hadj : IsAdjList G gS gE gEnt lists s₀) (hent : (s₀.arrs gEnt).length < 2 ^ w)
    (hrn : s₀.regs 40 = n) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hsw : src.length < 2 ^ w)
    (hlab₀ : s₀.arrs aLab = List.ofFn L0) (hsrc₀ : s₀.arrs aSrc = src) :
    ∃ s' t items, Exec w (searchProg gS gE gEnt) s₀ s' t ∧
      t ≤ 16 + 21 * n + 29 * src.length + 29 * totalAdjEntries lists ∧
      SInv G L0 src s₀ items items.length s' := by
  have hr40 : (Expr.reg 40).eval w s₀ = some n := by simp [checkWord, hrn, hn]
  set s₁ := s₀.setArr aPar (List.replicate n 0) with hs₁
  have hex₁ : Exec w (.alloc aPar (.reg 40)) s₀ s₁ (1 + n) := .alloc hr40
  set s₂ := s₁.setArr aQue (List.replicate n 0) with hs₂
  have hex₂ : Exec w (.alloc aQue (.reg 40)) s₁ s₂ (1 + n) :=
    .alloc (by simp [checkWord, s₁, hrn, hn])
  set s₃ := s₂.setReg rHead 0 with hs₃
  have hex₃ : Exec w (.assign rHead (.const 0)) s₂ s₃ (1 + 1) :=
    .assign (by simp [checkWord, show 0 < 2 ^ w by omega])
  set s₄ := s₃.setReg rTail 0 with hs₄
  have hex₄ : Exec w (.assign rTail (.const 0)) s₃ s₄ (1 + 1) :=
    .assign (by simp [checkWord, show 0 < 2 ^ w by omega])
  set s₅ := s₄.setReg rHit n with hs₅
  have hex₅ : Exec w (.assign rHit (.reg 40)) s₄ s₅ (1 + 1) :=
    .assign (by simp [checkWord, s₄, s₃, s₂, s₁, hrn, hn])
  set s₆ := s₅.setReg rI 0 with hs₆
  have hex₆ : Exec w (.assign rI (.const 0)) s₅ s₆ (1 + 1) :=
    .assign (by simp [checkWord, show 0 < 2 ^ w by omega])
  have hfr₂ : SFrame s₀ s₂ :=
    ⟨fun r _ => by simp [s₂, s₁], fun a h1 h2 h3 => by
      rw [hs₂, State.setArr_arrs_ne _ _ h3, hs₁, State.setArr_arrs_ne _ _ h2]⟩
  have hfr₆ : SFrame s₀ s₆ :=
    (((hfr₂.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _).setReg
      (by decide) _
  have hI0 : SrcInv G L0 src s₀ 0 s₆ := by
    refine ⟨by simp [s₆], [], hfr₆, ?_, List.nodup_nil, by simp, by simp, ?_,
      ⟨fun _ => 0, ?_, fun x hx => by simp at hx⟩, by simp [s₆, s₅], by simp⟩
    · refine ⟨by simp [s₆, s₅, s₄, s₃, s₂], by simp, by simp [s₆, s₅, s₄, s₃],
        by simp [s₆, s₅, s₄], le_rfl, fun i hi => by simp at hi⟩
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, hlab₀]
    · simp [s₆, s₅, s₄, s₃, s₂, s₁, List.ofFn_const]
  obtain ⟨s₇, t₇, hex₇, ht₇, hI₇⟩ :=
    searchSources_exec G L0 hL0 src hsrc s₀ hsrc₀ hrn hw hn hsw s₆ hI0
  obtain ⟨items, hS⟩ := hI₇.sInv
  obtain ⟨s₈, t₈, items', hex₈, ht₈, -, hS₈⟩ :=
    searchLoop_exec G lists gS gE gEnt hgS hgE hgEnt L0 hL0 src s₀ hadj hent hrn hw hn
      (n - 0) items 0 s₇ rfl hS
  refine ⟨s₈, _, items ++ items',
    .seq hex₁ (.seq (.seq hex₂ (.seq hex₃ hex₄)) (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))),
    ?_, hS₈⟩
  dsimp only at ht₇
  omega

end GraphMinor.Compute.TwoPaths
