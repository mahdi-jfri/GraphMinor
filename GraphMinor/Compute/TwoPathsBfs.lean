module

public import GraphMinor.Compute.TwoPathsSearchWalk
public import GraphMinor.Compute.TwoPathsAgree
public import GraphMinor.HP25.Sec5Search
import GraphMinor.Compute.TwoPathsChild
import GraphMinor.Compute.TwoPathsChord
import GraphMinor.Compute.TwoPathsSweep

/-!
# The search as a function

The extraction of Section 5.3 of Humeau and Pous searches for walks with inner vertices in a given
set ("$X$-searches", proof of Proposition 5.9, page 23). On the Word RAM such a search is
`searchProg` (`TwoPathsSearch.lean`), a breadth-first search over the adjacency lists, followed by
`traceProg` (`TwoPathsSearchWalk.lean`), which writes the walk it found.

This file turns that search into a function `bfsFind G gs ge gent allowed u v : Option (G.Walk u v)`
of the stored adjacency lists `gs`, `ge`, `gent` (arrays `40`, `41`, `42`):
* `bfsProg` is the search of a walk from `u` (register `rWU`) to `v` (register `rWV`) whose inner
  vertices lie in `allowed`. The caller writes the labels `bfsLabel allowed u v` into `aLab`: `v`
  is the target, `u` and the vertices of `allowed` are free, and all others are forbidden. The
  program first clears its scratch registers and arrays, then runs `searchProg` from `u`, then
  traces the walk to the vertex from which `v` was seen. It sets `rWFound` to `1` and writes into
  `aWalk` the walk without its last vertex `v`, or sets `rWFound` to `0`.
* `bfsFind` runs `bfsProg` with the interpreter `Cmd.run` from a fixed state that holds only the
  graph, the labels and `u`, `v`, and turns the result into a walk of `G` (`walkOfVals`).

Proved here, for arrays that store adjacency lists of `G` (`AdjArrays`):
* `bfsFind_support`: soundness, every vertex of the walk is `u`, `v` or in `allowed`;
* `bfsFind_isPath`: the walk is a path;
* `bfsFind_isSome`: completeness, it returns a walk whenever there is a walk from `u` to `v` whose
  inner vertices lie in `allowed`;
* `bfsFind_isWalkSearch`: the three together, as `HP25.IsWalkSearch G (bfsFind G gs ge gent)`;
* `bfsProg_find`: from every state that holds the graph, the labels, `u` and `v`, `bfsProg`
  writes the result of `bfsFind` in at most `150 + 50 N + 29 M` steps (`M` the number of
  adjacency entries), and changes only its scratch registers and arrays and the labels. The two
  runs agree because `bfsProg` clears its scratch space first and then reads only the input and
  the scratch space (`bfsProg_agree`, by `Exec.congr_used`).

Then the search becomes an instance of `HP25.WalkSearch (Fin N)`, built from the lists of one run
(`bfsSearch`): `bfsSearch_lawful` and `bfsProg_bfsSearch`.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph

/-! ### The program -/

/-- Register holding the start `u` of the searched walk. -/
abbrev rWU : Reg := 74
/-- Register holding the end `v` of the searched walk. -/
abbrev rWV : Reg := 75
/-- Register set to `1` when a walk was found, and to `0` otherwise. -/
abbrev rWFound : Reg := 76
/-- Array receiving the walk found, without its last vertex. -/
abbrev aWalk : Arr := 64

/-- Set the arrays `as` to `[]`. -/
def clearArrsProg : List Arr → Cmd
  | a :: as => .seq (.alloc a (.const 0)) (clearArrsProg as)
  | [] => .skip

/-- Set the registers `rs` to `0` and the arrays `as` to `[]`. Both definitions recurse on one
list, so that the kernel can run them. -/
def clearProg : List Reg → List Arr → Cmd
  | r :: rs, as => .seq (.assign r (.const 0)) (clearProg rs as)
  | [], as => clearArrsProg as

/-- The scratch registers of `bfsCore`. -/
def bfsScratchRegs : List Reg := List.range' 60 14 ++ [rWFound]

/-- The scratch arrays of `bfsCore`. -/
def bfsScratchArrs : List Arr := [aPar, aQue, aSrc, aWalk]

/-- The search of a walk from `rWU` to `rWV`, once the scratch space is clear. -/
def bfsCore : Cmd :=
  .ite (.op .eq (.reg rWU) (.reg rWV))
    (.seq (.assign rWFound (.const 1)) (.alloc aWalk (.const 0)))
    (.seq (.alloc aSrc (.const 1))
      (.seq (.write aSrc (.const 0) (.reg rWU))
        (.seq (searchProg 40 41 42)
          (.ite (.op .lt (.reg rHit) (.reg 40))
            (.seq (traceProg aWalk rHitPar) (.assign rWFound (.const 1)))
            (.assign rWFound (.const 0))))))

/-- The search of a walk from `rWU` to `rWV` through the free vertices of `aLab`. -/
def bfsProg : Cmd :=
  .seq (clearProg bfsScratchRegs bfsScratchArrs) bfsCore

/-! ### The model -/

/-- The labels of a search for a walk from `u` to `v` with inner vertices in `allowed`: `v` is the
target (`3`), `u` and the vertices of `allowed` are free (`0`), all others are forbidden (`2`). -/
def bfsLabel {N : ℕ} (allowed : List (Fin N)) (u v : Fin N) (x : Fin N) : ℕ :=
  if x = v then 3 else if x = u ∨ x ∈ allowed then 0 else 2

/-- The state from which the model runs `bfsProg`: the graph in arrays `40`, `41`, `42`, the
number of vertices in register `40`, the labels, and `u`, `v`. -/
def bfsState (gs ge gent : List ℕ) (N : ℕ) (lab : List ℕ) (u v : ℕ) : State where
  regs := fun r => if r = 40 then N else if r = rWU then u else if r = rWV then v else 0
  arrs := fun a => if a = 40 then gs else if a = 41 then ge else if a = 42 then gent
    else if a = aLab then lab else []

/-- The word size of the model's run. -/
def bfsW (N : ℕ) (gent : List ℕ) : ℕ := N + gent.length + 5

/-- The fuel of the model's run. -/
def bfsFuel (N : ℕ) : ℕ := 200 + 100 * N + 30 * (N * N)

/-- The vertex list found by the search, as numbers, or `none`. -/
def bfsVals (gs ge gent : List ℕ) {N : ℕ} (allowed : List (Fin N)) (u v : Fin N) :
    Option (List ℕ) :=
  match Cmd.run (bfsW N gent) (bfsFuel N) bfsProg
      (bfsState gs ge gent N (List.ofFn (bfsLabel allowed u v)) u.1 v.1) with
  | some (s, _) => if s.regs rWFound = 1 then some (s.arrs aWalk ++ [v.1]) else none
  | none => none

/-- The walk of `G` from `u` to `v` with vertex list `l`, if there is one. -/
def walkOfVals {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    (u v : Fin N) → List ℕ → Option (G.Walk u v)
  | _, _, [] => none
  | u, v, [x] => if h : x = u.1 ∧ u = v then some (h.2 ▸ Walk.nil) else none
  | u, v, x :: y :: rest =>
    if h : x = u.1 ∧ y < N then
      if ha : G.Adj u ⟨y, h.2⟩ then
        (walkOfVals G ⟨y, h.2⟩ v (y :: rest)).map (Walk.cons ha)
      else none
    else none

/-- **The search as a function.** The walk from `u` to `v` with inner vertices in `allowed` that
the breadth-first search `bfsProg` finds in the graph with adjacency lists `gs`, `ge`, `gent`. -/
def bfsFind {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (gs ge gent : List ℕ)
    (allowed : List (Fin N)) (u v : Fin N) : Option (G.Walk u v) :=
  (bfsVals gs ge gent allowed u v).bind (walkOfVals G u v)

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph

public section

variable {N : ℕ}

/-- `walkOfVals` recovers every walk from its vertex list. -/
theorem walkOfVals_support (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    ∀ {u v : Fin N} (W : G.Walk u v), walkOfVals G u v (W.support.map Fin.val) = some W
  | _, _, .nil => by simp [walkOfVals]
  | u, v, .cons (v := y) ha p => by
    have ih := walkOfVals_support G p
    rw [Walk.support_cons, List.map_cons]
    obtain ⟨T, hT⟩ : ∃ T, p.support = y :: T := ⟨p.support.tail, p.cons_tail_support.symm⟩
    rw [hT, List.map_cons] at ih ⊢
    simp only [walkOfVals, Fin.eta, ha, true_and, dite_true, y.2, ih, Option.map_some]

/-- A walk read by `walkOfVals` has the vertex list it was read from. -/
theorem walkOfVals_vals (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    ∀ {u v : Fin N} (L : List ℕ) {p : G.Walk u v}, walkOfVals G u v L = some p →
      p.support.map Fin.val = L
  | _, _, [], _, h => by simp [walkOfVals] at h
  | u, v, [x], p, h => by
    unfold walkOfVals at h
    split_ifs at h with hx
    obtain ⟨hxu, rfl⟩ := hx
    cases h
    simp [hxu]
  | u, v, x :: y :: rest, p, h => by
    unfold walkOfVals at h
    split_ifs at h with h1 h2
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [Walk.support_cons, List.map_cons, walkOfVals_vals G _ hq, h1.1]

/-! ### Clearing the scratch space -/

theorem clearProg_exec {w : ℕ} :
    ∀ (rs : List Reg) (as : List Arr) (s : State), ∃ s' t, Exec w (clearProg rs as) s s' t ∧
      t ≤ 3 * (rs.length + as.length) + 1 ∧
      (∀ r, s'.regs r = if r ∈ rs then 0 else s.regs r) ∧
      (∀ a, s'.arrs a = if a ∈ as then [] else s.arrs a)
  | r :: rs, as, s => by
    obtain ⟨s', t, hex, ht, hr, ha⟩ := clearProg_exec rs as (s.setReg r 0)
    refine ⟨s', _, by rw [clearProg]; exact .seq (.assign (const_eval' (Nat.two_pow_pos w))) hex,
      ?_, fun x => ?_, fun a => ?_⟩
    · simp only [Expr.cost, List.length_cons]; omega
    · rw [hr x]; by_cases h : x = r <;> by_cases h' : x ∈ rs <;> simp [h, h']
    · rw [ha a]; simp
  | [], a :: as, s => by
    obtain ⟨s', t, hex, ht, hr, ha⟩ := clearProg_exec [] as (s.setArr a (List.replicate 0 0))
    refine ⟨s', _, by
        rw [clearProg, clearArrsProg]; exact .seq (.alloc (const_eval' (Nat.two_pow_pos w))) hex,
      ?_, fun x => ?_, fun x => ?_⟩
    · simp only [Expr.cost, List.length_cons, List.length_nil] at ht ⊢; omega
    · rw [hr x]; simp
    · rw [ha x]; by_cases h : x = a <;> by_cases h' : x ∈ as <;> simp [h, h']
  | [], [], s => ⟨s, 1, by rw [clearProg, clearArrsProg]; exact .skip s, by simp, by simp, by simp⟩

/-! ### What one search does -/

/-- The input of `bfsProg`: the graph with adjacency lists `lists`, the number of vertices, the
labels `bfsLabel allowed u v`, and `u`, `v`. -/
structure BfsInput (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) (allowed : List (Fin N))
    (u v : Fin N) (s : State) : Prop where
  n : s.regs 40 = N
  ru : s.regs rWU = u.1
  rv : s.regs rWV = v.1
  adj : IsAdjList G 40 41 42 lists s
  lab : s.arrs aLab = List.ofFn (bfsLabel allowed u v)

theorem bfsLabel_le (allowed : List (Fin N)) (u v x : Fin N) : bfsLabel allowed u v x ≤ 3 := by
  unfold bfsLabel; split_ifs <;> omega

theorem bfsLabel_eq_three {allowed : List (Fin N)} {u v x : Fin N} :
    bfsLabel allowed u v x = 3 ↔ x = v := by
  unfold bfsLabel; split_ifs <;> simp_all

theorem bfsLabel_eq_zero {allowed : List (Fin N)} {u v x : Fin N} (h : bfsLabel allowed u v x = 0) :
    x ≠ v ∧ (x = u ∨ x ∈ allowed) := by
  unfold bfsLabel at h; split_ifs at h with h1 h2 <;> simp_all

theorem totalAdjEntries_le {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) : totalAdjEntries lists ≤ N * N := by
  unfold totalAdjEntries
  calc ∑ u : Fin N, (lists u).length ≤ ∑ _u : Fin N, N :=
        Finset.sum_le_sum fun u _ => (h u).2.2.1
    _ = N * N := by simp

/-- The result of `bfsCore`: the trivial walk when `u = v`; otherwise either a path `W` from `u` to
a vertex `x` next to `v` whose vertices are all free, or no walk from `u` to `v` with inner
vertices in `allowed` at all. -/
def BfsResult (G : SimpleGraph (Fin N)) (allowed : List (Fin N)) (u v : Fin N) (s : State) :
    Prop :=
  (u = v ∧ s.regs rWFound = 1 ∧ s.arrs aWalk = []) ∨
  (u ≠ v ∧ s.regs rWFound = 1 ∧ ∃ (x : Fin N) (W : G.Walk u x), G.Adj x v ∧ W.IsPath ∧
    (∀ y ∈ W.support, bfsLabel allowed u v y = 0) ∧ s.arrs aWalk = W.support.map Fin.val) ∨
  (u ≠ v ∧ s.regs rWFound = 0 ∧
    ∀ W : G.Walk u v, ¬ ∀ y ∈ W.support, y ≠ u → y ≠ v → y ∈ allowed)

theorem not_walk_of_noHit {G : SimpleGraph (Fin N)} {allowed : List (Fin N)} {u v : Fin N}
    (huv : u ≠ v) (items : List ℕ)
    (hreach : ∀ {y : Fin N} (W : G.Walk u y), (∀ z ∈ W.support, bfsLabel allowed u v z = 0) →
      y.1 ∈ items)
    (hno : ∀ {y z : Fin N}, y.1 ∈ items → G.Adj y z → bfsLabel allowed u v z ≠ 3) :
    ∀ W : G.Walk u v, ¬ ∀ y ∈ W.support, y ≠ u → y ≠ v → y ∈ allowed := by
  classical
  intro W hW
  set P := W.bypass
  have hP : P.reverse.IsPath := W.bypass_isPath.reverse
  cases hPr : P.reverse with
  | nil => exact huv rfl
  | @cons _ y _ hadj Q =>
    have hnd : (v :: Q.support).Nodup := by
      have := hP.support_nodup; rw [hPr, Walk.support_cons] at this; exact this
    have hQ : ∀ z ∈ Q.reverse.support, bfsLabel allowed u v z = 0 := by
      intro z hz
      rw [Walk.support_reverse, List.mem_reverse] at hz
      have hzv : z ≠ v := fun h => (List.nodup_cons.mp hnd).1 (h ▸ hz)
      have hzP : z ∈ P.support := by
        rw [← List.mem_reverse, ← Walk.support_reverse, hPr, Walk.support_cons]
        exact List.mem_cons_of_mem _ hz
      have hzW := W.support_bypass_subset_support hzP
      unfold bfsLabel
      by_cases hzu : z = u
      · simp [hzu, huv]
      · simp [hzv, hW z hzW hzu hzv]
    exact hno (hreach Q.reverse hQ) hadj.symm (bfsLabel_eq_three.mpr rfl)

/-- **One search.** From a state with the input of `bfsProg`, the program runs in at most
`150 + 50 N + 29 M` steps, changes only its scratch registers and arrays, and ends with
`BfsResult`. -/
theorem bfsProg_result {w : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {allowed : List (Fin N)} {u v : Fin N} {s : State} (hin : BfsInput G lists allowed u v s)
    (hw : N + 4 < 2 ^ w) (hent : (s.arrs 42).length < 2 ^ w) :
    ∃ s' t, Exec w bfsProg s s' t ∧ t ≤ 150 + 50 * N + 29 * totalAdjEntries lists ∧
      (∀ r, r ∉ bfsScratchRegs → s'.regs r = s.regs r) ∧
      (∀ a, a ∉ bfsScratchArrs → a ≠ aLab → s'.arrs a = s.arrs a) ∧
      BfsResult G allowed u v s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hr₁, ha₁⟩ := clearProg_exec (w := w) bfsScratchRegs bfsScratchArrs s
  have hk : ∀ r, r ∉ bfsScratchRegs → s₁.regs r = s.regs r := fun r h => by simp only [hr₁ r, h, ↓reduceIte]
  have hka : ∀ a, a ∉ bfsScratchArrs → s₁.arrs a = s.arrs a := fun a h => by simp only [ha₁ a, h, ↓reduceIte]
  have hu₁ : s₁.regs rWU = u.1 := by rw [hk _ (by decide)]; exact hin.ru
  have hv₁ : s₁.regs rWV = v.1 := by rw [hk _ (by decide)]; exact hin.rv
  have h40₁ : s₁.regs 40 = N := by rw [hk _ (by decide)]; exact hin.n
  have hadj₁ : IsAdjList G 40 41 42 lists s₁ :=
    hin.adj.of_arrs_eq (hka _ (by decide)) (hka _ (by decide)) (hka _ (by decide))
  have hlab₁ : s₁.arrs aLab = List.ofFn (bfsLabel allowed u v) := by
    rw [hka _ (by decide)]; exact hin.lab
  have hcl : (3 * (bfsScratchRegs.length + bfsScratchArrs.length) + 1) = 58 := by decide
  have hcond : (Expr.op .eq (.reg rWU) (.reg rWV)).eval w s₁ = some (if u.1 = v.1 then 1 else 0) :=
    eq_eval (reg_eval hu₁ (by have := u.2; omega)) (reg_eval hv₁ (by have := v.2; omega)) hw1
  have hM := totalAdjEntries_le hin.adj.2
  by_cases huv : u = v
  · -- the trivial walk
    subst huv
    simp only [↓reduceIte] at hcond
    set s₂ := s₁.setReg rWFound 1
    refine ⟨s₂.setArr aWalk (List.replicate 0 0), _, .seq hex₁ (.ite_true hcond one_ne_zero
      (.seq (.assign (const_eval' hw1)) (.alloc (const_eval' (by omega))))), ?_, ?_, ?_, ?_⟩
    · simp only [Expr.cost]; omega
    · intro r hr
      have : r ≠ rWFound := fun h => hr (by simp [h, bfsScratchRegs])
      simp [s₂, this, hk r hr]
    · intro a ha _
      have : a ≠ aWalk := fun h => ha (by simp [h, bfsScratchArrs])
      simp [s₂, this, hka a ha]
    · exact Or.inl ⟨rfl, by simp [s₂], by simp⟩
  · have hne : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
    simp only [hne, ↓reduceIte] at hcond
    -- the source `u`
    set s₂ := (s₁.setArr aSrc (List.replicate 1 0)).writeArr aSrc 0 u.1
    have hex₂a : Exec w (.alloc aSrc (.const 1)) s₁ (s₁.setArr aSrc (List.replicate 1 0))
        (1 + 1) := .alloc (const_eval' hw1)
    have hex₂b : Exec w (.write aSrc (.const 0) (.reg rWU)) (s₁.setArr aSrc (List.replicate 1 0))
        s₂ (1 + 1 + 1) :=
      .write (const_eval' (by omega)) (reg_eval (by simp [hu₁]) (by have := u.2; omega))
        (by simp)
    have hsrc₂ : s₂.arrs aSrc = [u.1] := by simp [s₂]
    have hadj₂ : IsAdjList G 40 41 42 lists s₂ :=
      hadj₁.of_arrs_eq (by simp [s₂]) (by simp [s₂]) (by simp [s₂])
    have hent₂ : (s₂.arrs 42).length < 2 ^ w := by
      simp only [s₂, State.writeArr_arrs_ne _ _ _ (show (42 : ℕ) ≠ aSrc by decide),
        State.setArr_arrs_ne _ _ (show (42 : ℕ) ≠ aSrc by decide)]
      rw [hka _ (by decide)]; exact hent
    obtain ⟨s₃, t₃, items, hex₃, ht₃, hS⟩ := searchProg_exec G lists 40 41 42 (by decide)
      (by decide) (by decide) (bfsLabel allowed u v) (bfsLabel_le allowed u v) [u.1]
      (by simp) s₂ hadj₂ hent₂ (by simp [s₂, h40₁]) (by omega) hnw (by rw [List.length_singleton]; exact hw1)
      (by simp [s₂, hlab₁]) hsrc₂
    have h40₃ : s₃.regs 40 = N := by rw [hS.frame.1 40 (Or.inl (by norm_num))]; simp [s₂, h40₁]
    have hfr₃r : ∀ r, r ∉ bfsScratchRegs → s₃.regs r = s.regs r := by
      intro r hr
      have : r < 60 ∨ 71 ≤ r := by
        rcases Nat.lt_or_ge r 60 with h | h
        · exact Or.inl h
        rcases Nat.lt_or_ge r 71 with h' | h'
        · exact absurd (by interval_cases r <;> decide) hr
        · exact Or.inr h'
      rw [hS.frame.1 r this]; simp [s₂, hk r hr]
    have hfr₃a : ∀ a, a ∉ bfsScratchArrs → a ≠ aLab → s₃.arrs a = s.arrs a := by
      intro a ha hl
      have h1 : a ≠ aPar := fun h => ha (by simp [h, bfsScratchArrs])
      have h2 : a ≠ aQue := fun h => ha (by simp [h, bfsScratchArrs])
      have h3 : a ≠ aSrc := fun h => ha (by simp [h, bfsScratchArrs])
      rw [hS.frame.2 a hl h1 h2]; simp [s₂, h3, hka a ha]
    have hreach : ∀ {y : Fin N} (W : G.Walk u y), (∀ z ∈ W.support, bfsLabel allowed u v z = 0) →
        y.1 ∈ items := fun W hW => hS.mem_of_walk (by simp) W hW
    obtain ⟨p, hpar, hp⟩ := hS.par
    have hlt : (Expr.op .lt (.reg rHit) (.reg 40)).eval w s₃ =
        some (if s₃.regs rHit < N then 1 else 0) := by
      have hhit : s₃.regs rHit ≤ N := by
        rcases hS.hit with ⟨h, -⟩ | ⟨v', -, h, -⟩
        · omega
        · have := v'.2; omega
      exact lt_eval (reg_eval rfl (by omega)) (reg_eval h40₃ hnw) hw1
    by_cases hh : s₃.regs rHit < N
    · -- a target was seen: trace the walk
      simp only [hh, ↓reduceIte] at hlt
      obtain ⟨v', x, hv', hx, hlv, hxi, hxv⟩ := hS.hit_of_ne (by omega)
      have hvv : v' = v := bfsLabel_eq_three.mp hlv
      subst hvv
      obtain ⟨s₄, t₄, r, W, hex₄, ht₄, hW, hr, hWi, -, hout, hreg₄, harr₄⟩ :=
        traceProg_exec hp hnw aWalk (by decide) rHitPar (by decide) (by decide) s₃ x hxi hx
          h40₃ hpar
      have hru : r = u := by simpa [Fin.ext_iff] using hr
      subst hru
      refine ⟨s₄.setReg rWFound 1, _, .seq hex₁ (.ite_false hcond (.seq hex₂a (.seq hex₂b
        (.seq hex₃ (.ite_true hlt one_ne_zero (.seq hex₄ (.assign (const_eval' hw1)))))))),
        ?_, ?_, ?_, ?_⟩
      · simp only [Expr.cost, List.length_singleton] at ht₃ ⊢; omega
      · intro r hr
        have h1 : r ≠ rWFound := fun h => hr (by simp [h, bfsScratchRegs])
        have h2 : r ≠ rCur := by rintro rfl; exact hr (by decide)
        have h3 : r ≠ rCnt := by rintro rfl; exact hr (by decide)
        simp [h1, hreg₄ r h2 h3, hfr₃r r hr]
      · intro a ha hl
        have h1 : a ≠ aWalk := fun h => ha (by simp [h, bfsScratchArrs])
        simp [harr₄ a h1, hfr₃a a ha hl]
      · refine Or.inr (Or.inl ⟨huv, by simp, x, W, hxv, hW, fun y hy => hS.free y (hWi y hy),
          by simp [hout]⟩)
    · -- no target was seen
      simp only [hh, ↓reduceIte] at hlt
      have hnoh : s₃.regs rHit = N := by
        rcases hS.hit with ⟨h, -⟩ | ⟨v', -, h, -⟩
        · exact h
        · exact absurd (h ▸ v'.2) hh
      refine ⟨s₃.setReg rWFound 0, _, .seq hex₁ (.ite_false hcond (.seq hex₂a (.seq hex₂b
        (.seq hex₃ (.ite_false hlt (.assign (const_eval' (by omega)))))))), ?_, ?_, ?_, ?_⟩
      · simp only [Expr.cost, List.length_singleton] at ht₃ ⊢; omega
      · intro r hr
        have h1 : r ≠ rWFound := fun h => hr (by simp [h, bfsScratchRegs])
        simp [h1, hfr₃r r hr]
      · intro a ha hl; simp [hfr₃a a ha hl]
      · exact Or.inr (Or.inr ⟨huv, by simp, not_walk_of_noHit huv items hreach
          (fun hy hadj => hS.noHit hnoh hy hadj)⟩)

/-! ### Runs from two states that agree where the program looks -/

/-- The registers that `bfsCore` reads or writes. -/
def bfsRegs : Finset Reg := {40, rWU, rWV} ∪ bfsScratchRegs.toFinset

/-- The arrays that `bfsCore` reads or writes. -/
def bfsArrs : Finset Arr := {40, 41, 42, aLab} ∪ bfsScratchArrs.toFinset

theorem bfsCore_usedRegs : ∀ r ∈ bfsCore.usedRegs, r ∈ (bfsRegs : Set Reg) := by
  have h : bfsCore.usedRegs ⊆ bfsRegs := by decide
  exact fun r hr => h hr

theorem bfsCore_usedArrs : ∀ a ∈ bfsCore.usedArrs, a ∈ (bfsArrs : Set Arr) := by
  have h : bfsCore.usedArrs ⊆ bfsArrs := by decide
  exact fun a ha => h ha

/-- Two runs of `bfsProg`, from states that agree on the input registers `40`, `rWU`, `rWV` and
the input arrays `40`, `41`, `42`, `aLab`, end with the same flag and the same walk, at any two
word sizes. The reason: `bfsProg` first clears its scratch space, and then it only looks at the
input and the scratch space. -/
theorem bfsProg_agree {w w' : ℕ} {s c s' m : State} {t t' : ℕ}
    (hreg : ∀ r ∈ ({40, rWU, rWV} : Finset Reg), c.regs r = s.regs r)
    (harr : ∀ a ∈ ({40, 41, 42, aLab} : Finset Arr), c.arrs a = s.arrs a)
    (h : Exec w bfsProg s s' t) (h' : Exec w' bfsProg c m t') :
    s'.regs rWFound = m.regs rWFound ∧ s'.arrs aWalk = m.arrs aWalk := by
  obtain ⟨s₁, ts, hs, -, hsr, hsa⟩ := clearProg_exec (w := w) bfsScratchRegs bfsScratchArrs s
  obtain ⟨c₁, tc, hc, -, hcr, hca⟩ := clearProg_exec (w := w) bfsScratchRegs bfsScratchArrs c
  have hag : AgreeOn bfsRegs bfsArrs s₁ c₁ := by
    refine ⟨fun r hr => ?_, fun a ha => ?_⟩
    · rw [hcr, hsr]
      by_cases h : r ∈ bfsScratchRegs
      · simp [h]
      · simp only [h, ↓reduceIte]
        simp only [bfsRegs, Finset.coe_union, Set.mem_union, Finset.mem_coe,
          List.mem_toFinset, h, or_false] at hr
        exact hreg r hr
    · rw [hca, hsa]
      by_cases h : a ∈ bfsScratchArrs
      · simp [h]
      · simp only [h, ↓reduceIte]
        simp only [bfsArrs, Finset.coe_union, Set.mem_union, Finset.mem_coe,
          List.mem_toFinset, h, or_false] at ha
        exact harr a ha
  rw [bfsProg] at h h'
  cases h with
  | seq h₁ h₂ =>
    obtain ⟨rfl, -⟩ := Exec.deterministic h₁ hs
    obtain ⟨m₁, hm, hagm⟩ := Exec.congr_used h₂ bfsCore_usedRegs bfsCore_usedArrs hag
    have hfull : Exec (max w w') (.seq (clearProg bfsScratchRegs bfsScratchArrs) bfsCore) c m₁ _ :=
      (Exec.seq hc hm).mono_wordSize (le_max_left _ _)
    obtain ⟨rfl, -⟩ := Exec.deterministic hfull (h'.mono_wordSize (le_max_right _ _))
    exact ⟨(hagm.1 _ (by simp [bfsRegs, bfsScratchRegs])).symm,
      (hagm.2 _ (by simp [bfsArrs, bfsScratchArrs])).symm⟩

/-! ### The model run -/

/-- The arrays `gs`, `ge`, `gent` store the adjacency lists `lists` of `G`. -/
def AdjArrays (G : SimpleGraph (Fin N)) (gs ge gent : List ℕ) (lists : Fin N → List ℕ) : Prop :=
  IsAdjList G 40 41 42 lists
    ⟨fun _ => 0, fun a => if a = 40 then gs else if a = 41 then ge else if a = 42 then gent
      else []⟩

theorem AdjArrays.isAdjList {G : SimpleGraph (Fin N)} {gs ge gent : List ℕ}
    {lists : Fin N → List ℕ} (h : AdjArrays G gs ge gent lists) {s : State}
    (h40 : s.arrs 40 = gs) (h41 : s.arrs 41 = ge) (h42 : s.arrs 42 = gent) :
    IsAdjList G 40 41 42 lists s :=
  h.of_arrs_eq (by simp [h40]) (by simp [h41]) (by simp [h42])

/-- The model run of `bfsProg` happens, and `bfsVals` reads its flag and its walk. -/
theorem bfsVals_run {G : SimpleGraph (Fin N)} {gs ge gent : List ℕ} {lists : Fin N → List ℕ}
    (hA : AdjArrays G gs ge gent lists) (allowed : List (Fin N)) (u v : Fin N) :
    ∃ m t, Exec (bfsW N gent) bfsProg
        (bfsState gs ge gent N (List.ofFn (bfsLabel allowed u v)) u.1 v.1) m t ∧
      BfsResult G allowed u v m ∧
      bfsVals gs ge gent allowed u v =
        if m.regs rWFound = 1 then some (m.arrs aWalk ++ [v.1]) else none := by
  have hlt := Nat.lt_two_pow_self (n := bfsW N gent)
  have hin : BfsInput G lists allowed u v
      (bfsState gs ge gent N (List.ofFn (bfsLabel allowed u v)) u.1 v.1) :=
    ⟨by simp [bfsState], by simp [bfsState], by simp [bfsState],
      hA.isAdjList (by simp [bfsState]) (by simp [bfsState]) (by simp [bfsState]),
      by simp [bfsState]⟩
  have hW : N + gent.length + 5 = bfsW N gent := rfl
  obtain ⟨m, t, hex, ht, -, -, hres⟩ := bfsProg_result (w := bfsW N gent) hin (by omega)
    (by simp [bfsState]; omega)
  have hM := totalAdjEntries_le hA.2
  refine ⟨m, t, hex, hres, ?_⟩
  unfold bfsVals
  rw [Cmd.run_complete hex _ (by unfold bfsFuel; nlinarith)]

/-- What a result of `bfsCore` says about the walk read from it: when the flag is `1`, the vertex
list is that of a path from `u` to `v` whose vertices are `u`, `v`, or in `allowed`; when the flag
is `0`, no walk from `u` to `v` has all its inner vertices in `allowed`. -/
theorem BfsResult.vals {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {allowed : List (Fin N)}
    {u v : Fin N} {m : State} (h : BfsResult G allowed u v m) :
    (m.regs rWFound = 1 ∧ ∃ p : G.Walk u v, walkOfVals G u v (m.arrs aWalk ++ [v.1]) = some p ∧
      p.IsPath ∧ ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed) ∨
    (m.regs rWFound = 0 ∧ ∀ W : G.Walk u v, ¬ ∀ y ∈ W.support, y ≠ u → y ≠ v → y ∈ allowed) := by
  rcases h with ⟨rfl, hf, hw⟩ | ⟨-, hf, x, W, hxv, hW, hlab, hw⟩ | ⟨-, hf, hno⟩
  · refine Or.inl ⟨hf, Walk.nil, ?_, Walk.IsPath.nil, by simp⟩
    rw [hw, List.nil_append]
    exact walkOfVals_support G (Walk.nil : G.Walk u u)
  · refine Or.inl ⟨hf, W.concat hxv, ?_, hW.concat (fun hv => ?_) hxv, fun y hy => ?_⟩
    · rw [hw, ← walkOfVals_support G (W.concat hxv), Walk.support_concat,
        List.map_append, List.map_singleton]
    · have := hlab v hv
      rw [show bfsLabel allowed u v v = 3 from bfsLabel_eq_three.mpr rfl] at this
      exact absurd this (by norm_num)
    · rw [Walk.support_concat, List.mem_append,
        List.mem_singleton] at hy
      rcases hy with hy | rfl
      · rcases (bfsLabel_eq_zero (hlab y hy)).2 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl rfl)
  · exact Or.inr ⟨hf, hno⟩

/-! ### The three properties of the model -/

section Model

variable {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {gs ge gent : List ℕ}
  {lists : Fin N → List ℕ}

theorem bfsFind_eq (hA : AdjArrays G gs ge gent lists) (allowed : List (Fin N)) (u v : Fin N) :
    (∃ p : G.Walk u v, bfsFind G gs ge gent allowed u v = some p ∧ p.IsPath ∧
      ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed) ∨
    (bfsFind G gs ge gent allowed u v = none ∧
      ∀ W : G.Walk u v, ¬ ∀ y ∈ W.support, y ≠ u → y ≠ v → y ∈ allowed) := by
  obtain ⟨m, t, -, hres, hvals⟩ := bfsVals_run hA allowed u v
  unfold bfsFind
  rcases hres.vals with ⟨hf, p, hp, hpath, hsupp⟩ | ⟨hf, hno⟩
  · refine Or.inl ⟨p, ?_, hpath, hsupp⟩
    simp only [hvals, hf, ↓reduceIte, Option.bind_some, hp]
  · refine Or.inr ⟨?_, hno⟩
    rw [hvals, hf]
    simp

/-- **Soundness.** Every vertex of the walk found is `u`, `v`, or in `allowed`. -/
theorem bfsFind_support (hA : AdjArrays G gs ge gent lists) {allowed : List (Fin N)}
    {u v : Fin N} {p : G.Walk u v} (h : bfsFind G gs ge gent allowed u v = some p) :
    ∀ x ∈ p.support, x = u ∨ x = v ∨ x ∈ allowed := by
  rcases bfsFind_eq hA allowed u v with ⟨q, hq, -, hs⟩ | ⟨hn, -⟩
  · rw [hq, Option.some_inj] at h; exact h ▸ hs
  · rw [hn] at h; cases h

/-- **Path-ness.** The walk found is a path. -/
theorem bfsFind_isPath (hA : AdjArrays G gs ge gent lists) {allowed : List (Fin N)}
    {u v : Fin N} {p : G.Walk u v} (h : bfsFind G gs ge gent allowed u v = some p) :
    p.IsPath := by
  rcases bfsFind_eq hA allowed u v with ⟨q, hq, hpath, -⟩ | ⟨hn, -⟩
  · rw [hq, Option.some_inj] at h; exact h ▸ hpath
  · rw [hn] at h; cases h

/-- **Completeness.** A walk is found whenever some walk from `u` to `v` has all its inner
vertices in `allowed`. -/
theorem bfsFind_isSome (hA : AdjArrays G gs ge gent lists) {allowed : List (Fin N)}
    {u v : Fin N} (q : G.Walk u v) (hq : ∀ x ∈ q.support, x ≠ u → x ≠ v → x ∈ allowed) :
    (bfsFind G gs ge gent allowed u v).isSome = true := by
  rcases bfsFind_eq hA allowed u v with ⟨p, hp, -⟩ | ⟨-, hno⟩
  · rw [hp]; rfl
  · exact absurd hq (hno q)

/-- The model is a walk search in the sense of `HP25.IsWalkSearch`. -/
theorem bfsFind_isWalkSearch (hA : AdjArrays G gs ge gent lists) :
    HP25.IsWalkSearch G (bfsFind G gs ge gent) :=
  ⟨bfsFind_support hA, bfsFind_isPath hA, bfsFind_isSome hA⟩

/-! ### The program computes the model -/

/-- **`bfsProg` computes `bfsFind`.** From a state with the input of a search, `bfsProg` runs in
at most `150 + 50 N + 29 M` steps, where `M` is the number of entries of the adjacency lists. It
changes only its scratch registers and arrays and the labels. When `bfsFind` finds a walk `p`,
the flag `rWFound` is `1` and `aWalk` holds the vertices of `p` before `v`. When `bfsFind` finds
nothing, the flag is `0`. -/
theorem bfsProg_find {w : ℕ} (hA : AdjArrays G gs ge gent lists) {allowed : List (Fin N)}
    {u v : Fin N} {s : State} (h40 : s.regs 40 = N) (hu : s.regs rWU = u.1)
    (hv : s.regs rWV = v.1) (hgs : s.arrs 40 = gs) (hge : s.arrs 41 = ge)
    (hgent : s.arrs 42 = gent) (hlab : s.arrs aLab = List.ofFn (bfsLabel allowed u v))
    (hw : N + 4 < 2 ^ w) (hent : gent.length < 2 ^ w) :
    ∃ s' t, Exec w bfsProg s s' t ∧ t ≤ 150 + 50 * N + 29 * totalAdjEntries lists ∧
      (∀ r, r ∉ bfsScratchRegs → s'.regs r = s.regs r) ∧
      (∀ a, a ∉ bfsScratchArrs → a ≠ aLab → s'.arrs a = s.arrs a) ∧
      ((∃ p, bfsFind G gs ge gent allowed u v = some p ∧ s'.regs rWFound = 1 ∧
          s'.arrs aWalk ++ [v.1] = p.support.map Fin.val) ∨
        (bfsFind G gs ge gent allowed u v = none ∧ s'.regs rWFound = 0)) := by
  obtain ⟨s', t, hex, ht, hr, ha, -⟩ := bfsProg_result
    ⟨h40, hu, hv, hA.isAdjList hgs hge hgent, hlab⟩ hw (by rw [hgent]; exact hent)
  obtain ⟨m, tm, hm, hres, hvals⟩ := bfsVals_run hA allowed u v
  obtain ⟨hf, hwk⟩ := bfsProg_agree (c := bfsState gs ge gent N
    (List.ofFn (bfsLabel allowed u v)) u.1 v.1)
    (by simp [bfsState, h40, hu, hv]) (by simp [bfsState, hgs, hge, hgent, hlab]) hex hm
  refine ⟨s', t, hex, ht, hr, ha, ?_⟩
  unfold bfsFind
  rcases hres.vals with ⟨hf₁, p, hp, -⟩ | ⟨hf₀, -⟩
  · refine Or.inl ⟨p, by simp only [hvals, hf₁, ↓reduceIte, Option.bind_some, hp], hf.trans hf₁, ?_⟩
    rw [hwk, walkOfVals_vals G _ hp]
  · exact Or.inr ⟨by rw [hvals, hf₀]; simp, hf.trans hf₀⟩

end Model

/-! ### The search as a `WalkSearch` instance

The class `HP25.WalkSearch (Fin N)` asks for one search for every graph on `Fin N`. The walk that
`bfsProg` finds depends on the order of the adjacency lists, so the instance is built from the
lists `lists` of one run. For a graph `G`, it scans the neighbours of `x` in the order of
`lists x`, keeps those that are `G`-neighbours, and then takes the other `G`-neighbours of `x` in
increasing order (`nbrOrder`). When `lists` are the adjacency lists of `G`, this order is
`lists` itself (`nbrOrder_eq`). -/

/-- The three arrays that store a family of lists in the canonical layout: the lists one after
the other in `gent`, list `x` from `gs[x]` to `ge[x]`. -/
@[expose] def encodeLists (L : Fin N → List ℕ) : List ℕ × List ℕ × List ℕ :=
  (List.ofFn fun x : Fin N => ((List.ofFn L).take x.1).flatten.length,
   List.ofFn fun x : Fin N => ((List.ofFn L).take x.1).flatten.length + (L x).length,
   (List.ofFn L).flatten)

theorem flatten_ofFn_split (L : Fin N → List ℕ) (x : Fin N) :
    (List.ofFn L).flatten =
      ((List.ofFn L).take x.1).flatten ++ (L x ++ ((List.ofFn L).drop (x.1 + 1)).flatten) := by
  have hx : x.1 < (List.ofFn L).length := by simp
  conv_lhs => rw [← List.take_append_drop x.1 (List.ofFn L), List.drop_eq_getElem_cons hx]
  simp

/-- The canonical layout stores the adjacency lists. -/
theorem encodeLists_adjArrays {G : SimpleGraph (Fin N)} {L : Fin N → List ℕ}
    (h : IsAdjListFamily G L) :
    AdjArrays G (encodeLists L).1 (encodeLists L).2.1 (encodeLists L).2.2 L := by
  refine ⟨⟨by simp [encodeLists], by simp [encodeLists], fun x => ?_⟩, h⟩
  have hsplit := flatten_ofFn_split L x
  refine ⟨((List.ofFn L).take x.1).flatten.length,
    ((List.ofFn L).take x.1).flatten.length + (L x).length, by simp [encodeLists], by
      simp [encodeLists], by simp only [encodeLists, ↓reduceIte]; rw [hsplit]; simp,
      by omega, by simp [encodeLists], by simp [encodeLists], by omega, fun k hk => ?_⟩
  simp only [encodeLists, show (42 : ℕ) ≠ 40 by decide, show (42 : ℕ) ≠ 41 by decide,
    ↓reduceIte]
  rw [List.getElem_of_eq hsplit, List.getElem_append_right (by omega),
    List.getElem_append_left (by simp; omega)]
  simp

/-- The neighbours of `x` in `G`, in the order of `lists x` first, and then the other
neighbours in increasing order. -/
def nbrOrder (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (lists : Fin N → List ℕ)
    (x : Fin N) : List ℕ :=
  (lists x).filter (fun y => decide (∃ h : y < N, G.Adj x ⟨y, h⟩)) ++
    ((List.finRange N).filter (fun y => G.Adj x y ∧ y.1 ∉ lists x)).map Fin.val

theorem nbrOrder_isAdjListFamily (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {lists : Fin N → List ℕ} (hl : ∀ x, (lists x).Nodup) :
    IsAdjListFamily G (nbrOrder G lists) := by
  intro x
  have hlt : ∀ y ∈ nbrOrder G lists x, y < N := by
    intro y hy
    simp only [nbrOrder, List.mem_append, List.mem_filter, List.mem_map] at hy
    rcases hy with ⟨-, hy⟩ | ⟨z, -, rfl⟩
    · simp only [decide_eq_true_eq] at hy; exact hy.1
    · exact z.2
  have hnd : (nbrOrder G lists x).Nodup := by
    unfold nbrOrder
    refine List.Nodup.append ((hl x).filter _)
      ((List.nodup_finRange N).filter _ |>.map Fin.val_injective) ?_
    intro a ha hb
    simp only [List.mem_map, List.mem_filter] at hb
    obtain ⟨z, ⟨-, hz⟩, rfl⟩ := hb
    simp only [decide_eq_true_eq] at hz
    exact hz.2 (List.mem_filter.mp ha).1
  refine ⟨hlt, hnd, ?_, fun v => ?_⟩
  · have hsub : (nbrOrder G lists x).Subperm (List.range N) :=
      hnd.subperm fun y hy => List.mem_range.mpr (hlt y hy)
    simpa using hsub.length_le
  · simp only [nbrOrder, List.mem_append, List.mem_filter, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro (⟨-, h, hadj⟩ | ⟨z, ⟨-, hadj, -⟩, hz⟩)
      · exact hadj
      · rwa [Fin.ext hz] at hadj
    · intro hadj
      by_cases hv : v.1 ∈ lists x
      · exact Or.inl ⟨hv, v.2, hadj⟩
      · exact Or.inr ⟨v, ⟨List.mem_finRange v, hadj, hv⟩, rfl⟩

/-- When `lists` are the adjacency lists of `G`, the order `nbrOrder G lists` is `lists`. -/
theorem nbrOrder_eq {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) : nbrOrder G lists = lists := by
  funext x
  unfold nbrOrder
  rw [List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr, List.map_nil, List.append_nil]
  · intro y _ hy
    simp only [decide_eq_true_eq] at hy
    exact hy.2 (((h x).2.2.2 y).mpr hy.1)
  · intro y hy
    have hyN := (h x).1 y hy
    simp only [decide_eq_true_eq]
    exact ⟨hyN, ((h x).2.2.2 ⟨y, hyN⟩).mp hy⟩

/-- In a graph `G` with more edges than the graph `G₀` of `lists` (a step graph), the order is
`lists x` followed by the new neighbours of `x` in increasing order. -/
theorem nbrOrder_of_le {G₀ G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G₀ lists) (hle : G₀ ≤ G) (x : Fin N) :
    nbrOrder G lists x = lists x ++
      ((List.finRange N).filter (fun y => G.Adj x y ∧ y.1 ∉ lists x)).map Fin.val := by
  unfold nbrOrder
  rw [List.filter_eq_self.mpr]
  intro y hy
  have hyN := (h x).1 y hy
  simp only [decide_eq_true_eq]
  exact ⟨hyN, hle (((h x).2.2.2 ⟨y, hyN⟩).mp hy)⟩

/-- In a graph `G` with fewer edges than the graph `G₀` of `lists` (for example `G₀` with some
edges left out), the order is `lists x` with the non-edges of `G` removed. -/
theorem nbrOrder_of_ge {G₀ G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G₀ lists) (hle : G ≤ G₀) (x : Fin N) :
    nbrOrder G lists x = (lists x).filter (fun y => decide (∃ h : y < N, G.Adj x ⟨y, h⟩)) := by
  have hnil : (List.finRange N).filter (fun y => decide (G.Adj x y ∧ y.1 ∉ lists x)) = [] := by
    refine List.filter_eq_nil_iff.mpr fun y _ hy => ?_
    simp only [decide_eq_true_eq] at hy
    exact hy.2 (((h x).2.2.2 y).mpr (hle hy.1))
  unfold nbrOrder
  rw [hnil, List.map_nil, List.append_nil]

/-- **The BFS search as a `WalkSearch` instance**, built from the lists `lists` of one run: in
`G`, it runs the model `bfsFind` on the lists `nbrOrder G lists` in the canonical layout. -/
@[expose, instance_reducible] def bfsSearch (lists : Fin N → List ℕ) : HP25.WalkSearch (Fin N) :=
  ⟨fun G _ allowed u v =>
    bfsFind G (encodeLists (nbrOrder G lists)).1 (encodeLists (nbrOrder G lists)).2.1
      (encodeLists (nbrOrder G lists)).2.2 allowed u v⟩

/-- **The BFS search is lawful**, when the lists `lists` have no repeats. -/
theorem bfsSearch_lawful {lists : Fin N → List ℕ} (hl : ∀ x, (lists x).Nodup) :
    @HP25.LawfulWalkSearch (Fin N) (bfsSearch lists) :=
  @HP25.LawfulWalkSearch.mk (Fin N) (bfsSearch lists) fun G _ =>
    bfsFind_isWalkSearch (encodeLists_adjArrays (nbrOrder_isAdjListFamily G hl))

/-- **`bfsProg` computes the instance `bfsSearch lists`** on the graph `G` whose adjacency lists
`lists` are stored in the canonical layout. -/
theorem bfsProg_bfsSearch {w : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    {lists : Fin N → List ℕ} (hG : IsAdjListFamily G lists) {allowed : List (Fin N)}
    {u v : Fin N} {s : State} (h40 : s.regs 40 = N) (hu : s.regs rWU = u.1)
    (hv : s.regs rWV = v.1) (hgs : s.arrs 40 = (encodeLists lists).1)
    (hge : s.arrs 41 = (encodeLists lists).2.1) (hgent : s.arrs 42 = (encodeLists lists).2.2)
    (hlab : s.arrs aLab = List.ofFn (bfsLabel allowed u v))
    (hw : N + 4 < 2 ^ w) (hent : (encodeLists lists).2.2.length < 2 ^ w) :
    ∃ s' t, Exec w bfsProg s s' t ∧ t ≤ 150 + 50 * N + 29 * totalAdjEntries lists ∧
      (∀ r, r ∉ bfsScratchRegs → s'.regs r = s.regs r) ∧
      (∀ a, a ∉ bfsScratchArrs → a ≠ aLab → s'.arrs a = s.arrs a) ∧
      ((∃ p, (bfsSearch lists).find G allowed u v = some p ∧ s'.regs rWFound = 1 ∧
          s'.arrs aWalk ++ [v.1] = p.support.map Fin.val) ∨
        ((bfsSearch lists).find G allowed u v = none ∧ s'.regs rWFound = 0)) := by
  have hfind : (bfsSearch lists).find G allowed u v =
      bfsFind G (encodeLists lists).1 (encodeLists lists).2.1 (encodeLists lists).2.2
        allowed u v := by
    change bfsFind G (encodeLists (nbrOrder G lists)).1 (encodeLists (nbrOrder G lists)).2.1
      (encodeLists (nbrOrder G lists)).2.2 allowed u v = _
    rw [nbrOrder_eq hG]
  rw [hfind]
  exact bfsProg_find (encodeLists_adjArrays hG) h40 hu hv hgs hge hgent hlab hw hent

end

end GraphMinor.Compute.TwoPaths
