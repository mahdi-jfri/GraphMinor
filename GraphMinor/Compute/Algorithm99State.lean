module

public import GraphMinor.Compute.Algorithm99Step1
import GraphMinor.Compute.Algorithm94Scan
import GraphMinor.Compute.Algorithm77Prog75Full

/-!
# Step (2) of Algorithm (9.9): the state of the recursion

Step (2) of the proof of (9.8) in Graph Minors XIII (page 104) reads: "(2) Now we perform a
recursion. We set $G_1 = G$, $Z_1 = \emptyset$, $H_1 = H$. At the beginning of the $i$ th
iteration we have (i) a subgraph $G_i$ of $G$ with … (ii) a subset $Z_i \subseteq V(G_i)$ with
$|Z_i| \le s - 3$ such that no vertex of $G_i \setminus Z_i$ is incident with an edge of $G$ not in
$G_i$, (iii) a wall $H_i$ in $G_i$ of height $h'$."

For the running time `O(vε)`, the program keeps `G_i` on its own vertex set `Fin v_i`, with a map
`orig : Fin v_i → Fin n` to the vertices of `G` (see `Algorithm99Relabel.lean`). A state is an
`Alg99Iter h' G`: the graph `G_i`, the map `orig`, the set `Z_i` and the wall `H_i`. The
conditions (ii) and (iii), and "subgraph" in (i), are `Alg99Iter.IsValid`. The bound on
`ε(G_i)` in (i) is about the running time; the loop of step (9) carries it.

A subgraph `G_i` of `G` is written by multiplicities, so we ask that `G_i` has, between two
vertices, either no edge or all the edges of `G` between their images. Every `G_i` of (9.9) has
this form: `G_1 = G`, and `G_{i+1}` takes every edge of `G_i` between the vertices it keeps
(step (8)).

The state is stored in arrays `B + 1` to `B + 4` (`Alg99Iter.StoredIn`). The program
`alg99InitProg` writes `G_1 = G`, `orig = id`, `Z_1 = ∅` and `H_1 = H` from the output of step
(1) (`alg99InitProg_exec`), and `Alg99Iter.init_isValid` says this is a valid state.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-! ### Section 1: The state and its invariants -/

/-- The data at the beginning of an iteration of (9.9) (step (2), page 104): the graph `G_i` on
its own vertex set `Fin v`, the map `orig` from its vertices to those of `G`, the set `Z_i`, and
the wall `H_i` of height `h'` in `G_i`. -/
structure Alg99Iter (h' : ℕ) {n : ℕ} (G : MultiDigraph n) where
  /-- The number `v = |V(G_i)|` of vertices of `G_i`. -/
  v : ℕ
  /-- The graph `G_i`. -/
  Gi : MultiDigraph v
  /-- The vertex of `G` that each vertex of `G_i` stands for. -/
  orig : Fin v → Fin n
  /-- The set `Z_i`. -/
  Z : Finset (Fin v)
  /-- The wall `H_i` in `G_i`. -/
  H : WallOfHeight h' Gi

/-- Conditions (i) (without the bound on `ε(G_i)`), (ii) and (iii) of step (2) of (9.9)
(page 104), for `s = C(p, 2) + 5`:
* `G_i` is a subgraph of `G`: `orig` is injective, and between two vertices `G_i` has either no
  edge or all the edges of `G` between their images;
* `|Z_i| ≤ s - 3`, and no vertex of `G_i \ Z_i` is incident with an edge of `G` not in `G_i`;
* `H_i` is a wall in `G_i`. -/
structure Alg99Iter.IsValid {h' n : ℕ} {G : MultiDigraph n} (st : Alg99Iter h' G) (s : ℕ) :
    Prop where
  /-- Different vertices of `G_i` stand for different vertices of `G`. -/
  orig_injective : Function.Injective st.orig
  /-- The edges of `G_i` between `u` and `w` are none or all of those of `G`. -/
  edgeMult_eq : ∀ u w, st.Gi.edgeMult u w = 0 ∨
    st.Gi.edgeMult u w = G.edgeMult (st.orig u) (st.orig w)
  /-- `|Z_i| ≤ s - 3`. -/
  card_Z : st.Z.card ≤ s - 3
  /-- An edge of `G` with tail `orig u`, for `u ∉ Z_i`, is in `G_i`. -/
  closed_out : ∀ u, u ∉ st.Z → ∀ y : Fin n, 0 < G.edgeMult (st.orig u) y →
    ∃ w, st.orig w = y ∧ st.Gi.edgeMult u w = G.edgeMult (st.orig u) y
  /-- An edge of `G` with head `orig u`, for `u ∉ Z_i`, is in `G_i`. -/
  closed_in : ∀ u, u ∉ st.Z → ∀ y : Fin n, 0 < G.edgeMult y (st.orig u) →
    ∃ w, st.orig w = y ∧ st.Gi.edgeMult w u = G.edgeMult y (st.orig u)
  /-- `H_i` is a wall in `G_i`. -/
  wall_isValid : st.H.IsValid

/-- The first state of (9.9) (step (2), page 104): "We set $G_1 = G$, $Z_1 = \emptyset$,
$H_1 = H$." -/
def Alg99Iter.init {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G) : Alg99Iter h' G where
  v := n
  Gi := G
  orig := id
  Z := ∅
  H := W

/-- The first state satisfies (i)–(iii) of step (2), for every `s ≥ 3`. -/
theorem Alg99Iter.init_isValid {h' n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h' G}
    (hW : W.IsValid) (s : ℕ) : (Alg99Iter.init W).IsValid s where
  orig_injective := Function.injective_id
  edgeMult_eq _ _ := Or.inr rfl
  card_Z := by simp [Alg99Iter.init]
  closed_out _ _ y _ := ⟨y, rfl, rfl⟩
  closed_in _ _ y _ := ⟨y, rfl, rfl⟩
  wall_isValid := hW

/-- The state `st` is stored in the arrays `B + 1` to `B + 4`: `G_i.enc`, the list of the
`orig u`, `bitSetList Z_i` and `H_i.encList`. -/
def Alg99Iter.StoredIn {h' n : ℕ} {G : MultiDigraph n} (st : Alg99Iter h' G) (B : ℕ)
    (s : State) : Prop :=
  s.arrs (B + 1) = st.Gi.enc ∧
  s.arrs (B + 2) = List.ofFn (fun u => (st.orig u).1) ∧
  s.arrs (B + 3) = bitSetList st.Z ∧
  s.arrs (B + 4) = st.H.encList

/-! ### Section 2: Two copying loops -/

/-- Writes `0, 1, …, n - 1` into `dst`, where `n` is in register `r_n`. -/
def iotaProg (dst : Arr) (r_n r_i : Reg) : Cmd :=
  .seq (.alloc dst (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (.write dst (.reg r_i) (.reg r_i))))

theorem iotaProg_exec {w : ℕ} (dst : Arr) (r_n r_i : ℕ) (hne : r_n ≠ r_i) (hw : 1 < 2 ^ w)
    {n : ℕ} (hn_w : n < 2 ^ w) {s : State} (hn : s.regs r_n = n) :
    ∃ s' t, Exec w (iotaProg dst r_n r_i) s s' t ∧ t ≤ 12 * n + 8 ∧
      s'.arrs dst = List.range n ∧
      (∀ a : ℕ, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_i → s'.regs r = s.regs r) := by
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have cn := checkWord_of_lt (w := w) (v := n) hn_w
  let s₁ := s.setArr dst (List.replicate n 0)
  have hex₁ : Exec w (.alloc dst (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp only [Expr.eval, hn, cn])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 := .assign (by simp only [Expr.eval, c0])
  let Inv (k : ℕ) (st : State) : Prop :=
    (st.arrs dst).length = n ∧
    (∀ j (hj : j < (st.arrs dst).length), j < k → (st.arrs dst)[j] = j) ∧
    st.regs r_n = n ∧ st.regs r_i = k ∧
    (∀ a : ℕ, a ≠ dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_i → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁], fun j _ hj => by omega, ?_, by simp [s₂], fun a ha => ?_,
      fun r hr => ?_⟩
    · simp only [s₂, s₁, State.setReg_regs_ne _ _ hne, State.setArr_regs, hn]
    · simp only [s₂, s₁, State.setReg_arrs]; exact State.setArr_arrs_ne _ _ ha
    · simp only [s₂, s₁, State.setReg_regs_ne _ _ hr, State.setArr_regs]
  have hLoop : ⦃Inv 0⦄[w] forUp r_i (.reg r_n) (.write dst (.reg r_i) (.reg r_i))
      ⦃Inv n⦄ ≤ fun _ => 3 + n * (7 + 3) := by
    apply Triple.forUp_const Inv n 3 hw hn_w
    · intro k _ st ⟨_, _, hrn, hri, _, _⟩
      exact ⟨hri, by simp only [Expr.eval, hrn, cn]⟩
    · intro k hk st ⟨hlen, hval, hrn, hri, harr, hreg⟩
      have ck := checkWord_of_lt (w := w) (v := k) (by omega)
      refine ⟨st.writeArr dst k k, 3, .write (i := k) (v := k) (by simp only [Expr.eval, hri, ck])
        (by simp only [Expr.eval, hri, ck])
        (by rw [hlen]; exact hk), le_rfl, ⟨?_, fun j hj hjk => ?_, ?_, by simp, fun a ha => ?_,
        fun r hr => ?_⟩, by simp [State.writeArr, hri]⟩
      · simp [State.writeArr, State.setReg, hlen]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_self] at hj ⊢
        rw [List.getElem_set]
        split_ifs with h
        · exact h
        · exact hval j (by simpa using hj) (by omega)
      · simp only [State.setReg_regs_ne _ _ hne, State.writeArr, State.setArr_regs, hrn]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_ne _ _ ha, harr a ha]
      · simp only [State.setReg_regs_ne _ _ hr, State.writeArr, State.setArr_regs, hreg r hr]
  obtain ⟨s₃, t₃, hex₃, ht₃, hlen₃, hval₃, _, _, harr₃, hreg₃⟩ := hLoop s₂ hInv₀
  have ht₃' : t₃ ≤ 3 + n * 10 := ht₃
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, ?_, harr₃, hreg₃⟩
  refine List.ext_getElem (by simp [hlen₃]) fun j h₁ h₂ => ?_
  rw [hval₃ j h₁ (by rw [hlen₃] at h₁; exact h₁), List.getElem_range]

/-- Writes `src[1], src[2], …` (all of `src` but its first word) into `dst`, using registers
`r_n` and `r_i`. -/
def copyTailProg (src dst : Arr) (r_n r_i : Reg) : Cmd :=
  .seq (.assign r_n (.op .sub (.len src) (.const 1)))
    (.seq (.alloc dst (.reg r_n))
      (.seq (.assign r_i (.const 0))
        (forUp r_i (.reg r_n)
          (.write dst (.reg r_i) (.read src (.op .add (.reg r_i) (.const 1)))))))

theorem copyTailProg_exec {w : ℕ} (src dst : Arr) (r_n r_i : ℕ) (hne_a : src ≠ dst)
    (hne : r_n ≠ r_i) (hw : 1 < 2 ^ w) {x : ℕ} {l : List ℕ} {s : State}
    (hs : s.arrs src = x :: l) (hlen_w : l.length + 1 < 2 ^ w) (hval_w : ∀ y ∈ l, y < 2 ^ w) :
    ∃ s' t, Exec w (copyTailProg src dst r_n r_i) s s' t ∧ t ≤ 20 * l.length + 14 ∧
      s'.arrs dst = l ∧
      (∀ a : ℕ, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_n → r ≠ r_i → s'.regs r = s.regs r) := by
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have c1 := checkWord_of_lt (w := w) (v := 1) (by omega)
  have cn := checkWord_of_lt (w := w) (v := l.length) (by omega)
  have cn1 := checkWord_of_lt (w := w) (v := l.length + 1) hlen_w
  let s₁ := s.setReg r_n l.length
  have hex₁ : Exec w (.assign r_n (.op .sub (.len src) (.const 1))) s s₁ 4 := by
    refine .assign ?_
    simp only [Expr.eval, hs, List.length_cons, cn1, c1, BinOp.eval, BinOp.raw,
      Nat.add_sub_cancel, cn]
  let s₂ := s₁.setArr dst (List.replicate l.length 0)
  have hex₂ : Exec w (.alloc dst (.reg r_n)) s₁ s₂ (1 + l.length) :=
    .alloc (by simp only [Expr.eval, s₁, State.setReg_regs_self, cn])
  let s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 := .assign (by simp only [Expr.eval, c0])
  let Inv (k : ℕ) (st : State) : Prop :=
    (st.arrs dst).length = l.length ∧
    (∀ j (hj : j < (st.arrs dst).length) (hj' : j < l.length), j < k → (st.arrs dst)[j] = l[j]) ∧
    st.regs r_n = l.length ∧ st.regs r_i = k ∧
    (∀ a : ℕ, a ≠ dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_n → r ≠ r_i → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₃ := by
    refine ⟨by simp [s₃, s₂], fun j _ _ hj => by omega, ?_, by simp [s₃], fun a ha => ?_,
      fun r hr hr' => ?_⟩
    · simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ hne, State.setArr_regs,
        State.setReg_regs_self]
    · simp only [s₃, s₂, s₁, State.setReg_arrs]; exact State.setArr_arrs_ne _ _ ha
    · simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr', State.setArr_regs,
        State.setReg_regs_ne _ _ hr]
  have hLoop : ⦃Inv 0⦄[w] forUp r_i (.reg r_n)
      (.write dst (.reg r_i) (.read src (.op .add (.reg r_i) (.const 1)))) ⦃Inv l.length⦄ ≤
      fun _ => 3 + l.length * (7 + 8) := by
    apply Triple.forUp_const Inv l.length 8 hw (by omega)
    · intro k _ st ⟨_, _, hrn, hri, _, _⟩
      exact ⟨hri, by simp only [Expr.eval, hrn, cn]⟩
    · intro k hk st ⟨hlen, hval, hrn, hri, harr, hreg⟩
      have ck := checkWord_of_lt (w := w) (v := k) (by omega)
      have ck1 := checkWord_of_lt (w := w) (v := k + 1) (by omega)
      have hsrc : st.arrs src = x :: l := (harr src hne_a).trans hs
      have hk1 : k + 1 < (st.arrs src).length := by rw [hsrc]; simp; omega
      have hget : (st.arrs src)[k + 1]'hk1 = l[k] := by simp [hsrc]
      have cl := checkWord_of_lt (w := w) (v := l[k]) (hval_w _ (List.getElem_mem hk))
      have hexw : Exec w (.write dst (.reg r_i) (.read src (.op .add (.reg r_i) (.const 1)))) st
          (st.writeArr dst k l[k])
          ((Expr.reg r_i).cost + (Expr.read src (.op .add (.reg r_i) (.const 1))).cost + 1) :=
        .write (by simp only [Expr.eval, hri, ck])
          (by simp only [Expr.eval, hri, ck, c1, BinOp.eval, BinOp.raw, ck1, hk1, ↓reduceDIte, hget,
            cl])
          (by rw [hlen]; exact hk)
      refine ⟨st.writeArr dst k l[k], _, hexw, by simp [Expr.cost], ⟨?_, fun j hj hj' hjk => ?_, ?_, by simp, fun a ha => ?_,
        fun r hr hr' => ?_⟩, by simp [State.writeArr, hri]⟩
      · simp [State.writeArr, State.setReg, hlen]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_self] at hj ⊢
        rw [List.getElem_set]
        split_ifs with h
        · subst h; rfl
        · exact hval j (by simpa using hj) hj' (by omega)
      · simp only [State.setReg_regs_ne _ _ hne, State.writeArr, State.setArr_regs, hrn]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_ne _ _ ha, harr a ha]
      · simp only [State.setReg_regs_ne _ _ hr', State.writeArr, State.setArr_regs,
          hreg r hr hr']
  obtain ⟨s₄, t₄, hex₄, ht₄, hlen₄, hval₄, _, _, harr₄, hreg₄⟩ := hLoop s₃ hInv₀
  have ht₄' : t₄ ≤ 3 + l.length * 15 := ht₄
  refine ⟨s₄, 4 + ((1 + l.length) + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, ?_, harr₄, hreg₄⟩
  refine List.ext_getElem (by simp [hlen₄]) fun j h₁ h₂ => ?_
  exact hval₄ j h₁ h₂ h₂

/-! ### Section 3: The first state -/

/-- Writes the first state of (9.9) from the saved input `G.enc` (array `B`) and the output
`1 :: H.encList` of step (1) (`outArr`): `G_1 = G` in `B + 1`, `orig = id` in `B + 2`,
`Z_1 = ∅` in `B + 3` and `H_1 = H` in `B + 4`. Registers `R` to `R + 2` are scratch. -/
def alg99InitProg (B R : ℕ) : Cmd :=
  .seq (copyArrLoopProg B (B + 1) R (R + 1))
    (.seq (.assign (R + 2) (.read B (.const 0)))
      (.seq (iotaProg (B + 2) (R + 2) R)
        (.seq (.alloc (B + 3) (.reg (R + 2)))
          (copyTailProg outArr (B + 4) R (R + 1)))))

theorem bitSetList_empty (n : ℕ) : bitSetList (∅ : Finset (Fin n)) = List.replicate n 0 := by
  refine List.ext_getElem (by simp) fun j h₁ _ => ?_
  simp only [length_bitSetList] at h₁
  simp [getElem_bitSetList _ _ h₁]

theorem ofFn_val_id (n : ℕ) : List.ofFn (fun u : Fin n => (id u).1) = List.range n := by
  refine List.ext_getElem (by simp) fun j h₁ _ => ?_
  simp

/-- **Step (2) of Algorithm (9.9)** (page 104), the start: "We set $G_1 = G$, $Z_1 = \emptyset$,
$H_1 = H$." From the saved input `G.enc` in array `B` and `1 :: W.encList` in `outArr`,
`alg99InitProg B R` stores the first state `Alg99Iter.init W` in arrays `B + 1` to `B + 4`. -/
theorem alg99InitProg_exec {w h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G)
    (hW : W.IsValid) (B R : ℕ) (hB : 2 ≤ B) (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w) (hlen_w : G.enc.length < 2 ^ w)
    (hh_w : h' < 2 ^ w) (hc_w : 3 + 2 * elemWallNumVerts h' < 2 ^ w)
    (hWlen_w : W.encList.length + 1 < 2 ^ w)
    {s : State} (hsB : s.arrs B = G.enc) (hout : s.arrs outArr = 1 :: W.encList) :
    ∃ s' t, Exec w (alg99InitProg B R) s s' t ∧
      t ≤ 15 * G.enc.length + 13 * n + 20 * W.encList.length + 50 ∧
      (Alg99Iter.init W).StoredIn B s' ∧
      (∀ a : ℕ, a < B + 1 ∨ B + 4 < a → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, R + 2 < r ∨ r < R → s'.regs r = s.regs r) := by
  have hval_G := mem_enc_lt_two_pow G hn_w hm_w
  obtain ⟨s₁, t₁, hex₁, ht₁, hB₁, harr₁, hreg₁⟩ :=
    copyArrLoopProg_exec B (B + 1) R (R + 1) (by romega) (by romega) hw1 s
      (by rw [hsB]; exact hlen_w) (by rw [hsB]; exact hval_G)
  rw [hsB] at ht₁ hB₁
  have hB₁' : s₁.arrs B = G.enc := by rw [harr₁ B (by romega), hsB]
  have hpos : 0 < (s₁.arrs B).length := by rw [hB₁']; simp
  have h0 : (s₁.arrs B)[0]'hpos = n := by simp [hB₁', MultiDigraph.enc]
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have cn := checkWord_of_lt (w := w) (v := n) hn_w
  let s₂ := s₁.setReg (R + 2) n
  have hex₂ : Exec w (.assign (R + 2) (.read B (.const 0))) s₁ s₂ 3 :=
    .assign (by simp only [Expr.eval, c0, hpos, ↓reduceDIte, h0, cn])
  obtain ⟨s₃, t₃, hex₃, ht₃, hB₃, harr₃, hreg₃⟩ :=
    iotaProg_exec (B + 2) (R + 2) R (by omega) hw1 hn_w (s := s₂) (by simp [s₂])
  let s₄ := s₃.setArr (B + 3) (List.replicate n 0)
  have hr₃ : s₃.regs (R + 2) = n := by rw [hreg₃ _ (by omega)]; simp [s₂]
  have hex₄ : Exec w (.alloc (B + 3) (.reg (R + 2))) s₃ s₄ (1 + n) :=
    .alloc (by simp only [Expr.eval, hr₃, cn])
  have hout₄ : s₄.arrs outArr = 1 :: W.encList := by
    simp only [s₄, State.setArr_arrs_ne _ _ (show (outArr : ℕ) ≠ B + 3 by romega)]
    rw [harr₃ _ (by romega)]
    simp only [s₂, State.setReg_arrs]
    rw [harr₁ _ (by romega), hout]
  have hWval := all_lt_encList_of_isValid W hW le_rfl hh_w hc_w hn_w
  obtain ⟨s₅, t₅, hex₅, ht₅, hB₅, harr₅, hreg₅⟩ :=
    copyTailProg_exec outArr (B + 4) R (R + 1) (by romega) (by omega) hw1 hout₄ hWlen_w hWval
  refine ⟨s₅, t₁ + (3 + (t₃ + ((1 + n) + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by omega, ⟨?_, ?_, ?_, hB₅⟩, ?_, ?_⟩
  · rw [harr₅ _ (by omega)]
    simp only [s₄, State.setArr_arrs_ne _ _ (show B + 1 ≠ B + 3 by omega)]
    rw [harr₃ _ (by omega)]
    simp only [s₂, State.setReg_arrs, hB₁]
    rfl
  · rw [harr₅ _ (by omega)]
    simp only [s₄, State.setArr_arrs_ne _ _ (show B + 2 ≠ B + 3 by omega), hB₃]
    exact (ofFn_val_id n).symm
  · rw [harr₅ _ (by omega)]
    simp only [s₄, State.setArr_arrs_self]
    exact (bitSetList_empty n).symm
  · intro a ha
    rw [harr₅ a (by omega)]
    simp only [s₄, State.setArr_arrs_ne _ _ (show a ≠ B + 3 by omega)]
    rw [harr₃ a (by omega)]
    simp only [s₂, State.setReg_arrs]
    exact harr₁ a (by romega)
  · intro r hr
    rw [hreg₅ r (by omega) (by omega)]
    simp only [s₄, State.setArr_regs]
    rw [hreg₃ r (by omega)]
    simp only [s₂, State.setReg_regs_ne _ _ (show r ≠ R + 2 by omega)]
    exact hreg₁ r (by romega) (by romega)

end GraphMinor.Compute
