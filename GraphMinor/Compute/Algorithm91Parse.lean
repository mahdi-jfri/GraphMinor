module

public import GraphMinor.Compute.Algorithm91Eye

/-!
# Graph Minors XIII, (9.1): Word RAM Algorithm (`Algorithm91.lean`)

This file implements the Word RAM algorithm of **Graph Minors XIII, (9.1)** (Section 9, page 98):
> "Moreover, a model of $K_p$ in $G$ can be found in time $\le C\varepsilon(G)$, where $C$ depends
> only on $p$ and the height of $H$."

Given `x : Alg91Input p h (alg91K p) (alg91R p)` encoded in `inArr` as `encAlg91In x`, the program
`alg91Prog p h`:
1. Parses `inArr` in a single linear pass to record the offset of `x.W.encList`, the offsets and
   lengths of the subdivision paths `x.W.internalVerts e` (`e : Fin (elemWallEdges h).length`), and
   for each `a : Fin (alg91K p)` the subwall height `x.h_sub a` and the offsets and lengths of the
   cross paths `x.P a` and `x.Q a`.
2. Matches the subwall parameters `cfg : Fin (alg91K p) → SubwallParam h` against the finite list
   `allSubwallConfigs h (alg91K p)` using `(x.h_sub a, (x.P a).head)` and
   `SubwallParam.eq_of_h'_eq_of_cornerIdx_zero_eq`.
3. Materializes the recipe `recOfCfg p h cfg` (`Algorithm91Eye.lean`) into `outArr` as
   `encBitSetsUpTo (evalRecipe x (recOfCfg p h cfg)) p` in time `O(ε(G))`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

namespace Alg91

/-! ### Section 1: List Prefix Splitting and Bitset Materialization Helpers -/

theorem flatMap_finRange_eq_take_append_drop {α : Type*} {m : ℕ} (f : Fin m → List α)
    (j : ℕ) :
    (List.finRange m).flatMap f =
      ((List.finRange m).take j).flatMap f ++ ((List.finRange m).drop j).flatMap f := by
  rw [← List.flatMap_append, List.take_append_drop]

theorem flatMap_take_succ_finRange {α : Type*} {m : ℕ} (f : Fin m → List α)
    {j : ℕ} (hj : j < m) :
    ((List.finRange m).take (j + 1)).flatMap f =
      ((List.finRange m).take j).flatMap f ++ f ⟨j, hj⟩ := by
  have hj_len : j < (List.finRange m).length := by simp [hj]
  rw [List.take_add_one, List.getElem?_eq_getElem hj_len, Option.toList_some,
    List.flatMap_append, List.flatMap_singleton]
  simp

theorem flatMap_drop_eq_cons {α : Type*} {m : ℕ} (f : Fin m → List α)
    {j : ℕ} (hj : j < m) :
    ((List.finRange m).drop j).flatMap f =
      f ⟨j, hj⟩ ++ ((List.finRange m).drop (j + 1)).flatMap f := by
  have hj_len : j < (List.finRange m).length := by simp [hj]
  rw [List.drop_eq_getElem_cons hj_len, List.flatMap_cons]
  simp

theorem bitSetList_empty (n : ℕ) :
    bitSetList (∅ : Finset (Fin n)) = List.replicate n 0 := by
  refine List.ext_getElem (by simp [length_bitSetList]) (fun i hi1 hi2 => ?_)
  simp [bitSetList]

theorem bitSetList_set_one {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    (bitSetList S).set v.1 1 = bitSetList (insert v S) := by
  have hlen : ((bitSetList S).set v.1 1).length = (bitSetList (insert v S)).length := by
    rw [List.length_set, length_bitSetList, length_bitSetList]
  refine List.ext_getElem hlen (fun i hi1 hi2 => ?_)
  have hi_n : i < n := by rw [length_bitSetList] at hi2; exact hi2
  by_cases hiv : i = v.1
  · subst hiv
    rw [List.getElem_set_self]
    simp [bitSetList]
  · rw [List.getElem_set_ne (Ne.symm hiv)]
    have hne_fin : (⟨i, hi_n⟩ : Fin n) ≠ v := fun heq => hiv (congrArg Fin.val heq)
    simp [bitSetList, hne_fin]

theorem take_add_one_toFinset {α : Type*} [DecidableEq α] (L : List α) {i : ℕ} (hi : i < L.length) :
    (L.take (i + 1)).toFinset = insert (L[i]'hi) (L.take i).toFinset := by
  ext x
  rw [List.mem_toFinset, Finset.mem_insert, List.mem_toFinset, List.take_add_one,
    List.getElem?_eq_getElem hi, Option.toList_some, List.mem_append, List.mem_singleton, or_comm]

theorem getElem_of_eq {α : Type*} {l₁ l₂ : List α} {i₁ i₂ : ℕ} {v : α}
    (hl : l₁ = l₂) (hi : i₁ = i₂) {h₁ : i₁ < l₁.length} {h₂ : i₂ < l₂.length}
    (h : l₂[i₂]'h₂ = v) : l₁[i₁]'h₁ = v := by
  subst hl; subst hi; exact h

theorem sum_map_le_length_mul {α : Type*} (l : List α) (g : α → ℕ) (B : ℕ)
    (h : ∀ a ∈ l, g a ≤ B) : (l.map g).sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    have ha := h a List.mem_cons_self
    have has := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    omega

/-! ### Section 2: Size Bounds on `encAlg91In x` -/

theorem numActivePairs_le_numEdges {n : ℕ} (G : MultiDigraph n) :
    G.numActivePairs ≤ G.numEdges := by
  have h1 : G.activePairsList.toFinset.card ≤
      ∑ p ∈ G.activePairsList.toFinset, G.edgeMult p.1 p.2 := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun p hp => ?_
    rw [List.mem_toFinset, MultiDigraph.mem_activePairsList] at hp
    exact hp
  have h2 : ∑ p ∈ G.activePairsList.toFinset, G.edgeMult p.1 p.2 ≤
      ∑ p : Fin n × Fin n, G.edgeMult p.1 p.2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have h3 : (∑ p : Fin n × Fin n, G.edgeMult p.1 p.2) = G.numEdges := by
    unfold MultiDigraph.numEdges
    rw [← Fintype.sum_prod_type']
  rw [MultiDigraph.numActivePairs, ← List.toFinset_card_of_nodup G.nodup_activePairsList]
  omega

theorem length_internalVerts_le_of_isValid {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) (e : Fin (elemWallEdges h).length) :
    (W.internalVerts e).length ≤ n := by
  have hnd := W.nodup_internalVerts_of_isValid hW e
  have hcard := Finset.card_le_univ (W.internalVerts e).toFinset
  rw [List.toFinset_card_of_nodup hnd, Fintype.card_fin] at hcard
  exact hcard

theorem sum_length_internalVerts_le_of_isValid {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    ((List.finRange (elemWallEdges h).length).map (fun e => (W.internalVerts e).length)).sum ≤
      n := by
  have hcard := W.card_vertexFinset_of_isValid hW
  have hle : W.vertexFinset.card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ W.vertexFinset
  omega

theorem length_encList_le_of_isValid {h n : ℕ} {G : MultiDigraph n}
    {W : WallOfHeight h G} (hW : W.IsValid) :
    W.encList.length ≤ 3 + elemWallNumVerts h + (elemWallEdges h).length + n := by
  rw [W.length_encList]
  have hsum := sum_length_internalVerts_le_of_isValid hW
  omega

theorem elemWallNumVerts_mono {h₁ h₂ : ℕ} (hle : h₁ ≤ h₂) :
    elemWallNumVerts h₁ ≤ elemWallNumVerts h₂ := by
  rw [elemWallNumVerts_eq, elemWallNumVerts_eq]
  have hmul : (h₁ + 1) * (2 * h₁ + 2) ≤ (h₂ + 1) * (2 * h₂ + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem length_elemWallEdges_le_four_mul (h : ℕ) :
    (elemWallEdges h).length ≤ 2 * elemWallNumVerts h :=
  length_elemWallEdges_le h

/-- Upper bound constant (depending only on `h` and `k`) on the length of `encAlg91In x` as a
multiple of `alg91Size x`. -/
def encAlg91LenFactor (h k : ℕ) : ℕ :=
  4 + (k + 1) * (8 + 3 * elemWallNumVerts h)

theorem length_encAlg91In_le {p h k r : ℕ} (x : Alg91Input p h k r) :
    (encAlg91In x).length ≤ encAlg91LenFactor h k * alg91Size x := by
  unfold encAlg91In alg91Size encAlg91LenFactor
  let s := x.G.numEdges + x.n + 1
  have hs_pos : 1 ≤ s := by dsimp [s]; omega
  have hn_le_s : x.n ≤ s := by dsimp [s]; omega
  have hG_len : x.G.enc.length ≤ 3 * s := by
    rw [MultiDigraph.length_enc]
    have := numActivePairs_le_numEdges x.G
    dsimp [s]
    omega
  have hW_len : x.W.encList.length ≤ (4 + 3 * elemWallNumVerts h) * s := by
    have h1 := length_encList_le_of_isValid x.hW_valid.2.2
    have h2 := length_elemWallEdges_le h
    have h3 : 3 + 3 * elemWallNumVerts h ≤ (3 + 3 * elemWallNumVerts h) * s :=
      Nat.le_mul_of_pos_right _ hs_pos
    have h4 : (3 + 3 * elemWallNumVerts h) * s + s = (4 + 3 * elemWallNumVerts h) * s := by ring
    omega
  have hsub_len : ∀ a : Fin k,
      ((x.W_sub a).encList ++
        ((x.P a).length :: (x.P a).map Fin.val) ++
        ((x.Q a).length :: (x.Q a).map Fin.val)).length ≤
      (8 + 3 * elemWallNumVerts h) * s := by
    intro a
    have hsub_valid : (x.W_sub a).IsValid :=
      x.W.isValid_of_isSubwallOf x.hW_valid.2.2 (x.hsub a)
    have hh_le : x.h_sub a ≤ h := (x.hsub a).2.2.1
    have hV_le : elemWallNumVerts (x.h_sub a) ≤ elemWallNumVerts h :=
      elemWallNumVerts_mono hh_le
    have hE_le : (elemWallEdges (x.h_sub a)).length ≤ 2 * elemWallNumVerts h :=
      (length_elemWallEdges_le (x.h_sub a)).trans (by omega)
    have hWa_len : (x.W_sub a).encList.length ≤ 3 + 3 * elemWallNumVerts h + x.n := by
      have h1 := length_encList_le_of_isValid hsub_valid
      omega
    have hP_len : (x.P a).length ≤ x.n := by
      have hcard := Finset.card_le_univ (x.P a).toFinset
      rw [List.toFinset_card_of_nodup (x.hcross a).nodup₁, Fintype.card_fin] at hcard
      exact hcard
    have hQ_len : (x.Q a).length ≤ x.n := by
      have hcard := Finset.card_le_univ (x.Q a).toFinset
      rw [List.toFinset_card_of_nodup (x.hcross a).nodup₂, Fintype.card_fin] at hcard
      exact hcard
    simp only [List.length_append, List.length_cons, List.length_map]
    have h1 : 5 + 3 * elemWallNumVerts h ≤ (5 + 3 * elemWallNumVerts h) * s :=
      Nat.le_mul_of_pos_right _ hs_pos
    have h2 : 3 * x.n ≤ 3 * s := Nat.mul_le_mul_left 3 hn_le_s
    have h3 : (5 + 3 * elemWallNumVerts h) * s + 3 * s = (8 + 3 * elemWallNumVerts h) * s := by
      rw [← Nat.add_mul]
      ring
    omega
  have hflat_len :
      ((List.finRange k).flatMap (fun a =>
        (x.W_sub a).encList ++
        ((x.P a).length :: (x.P a).map Fin.val) ++
        ((x.Q a).length :: (x.Q a).map Fin.val))).length ≤
      k * ((8 + 3 * elemWallNumVerts h) * s) := by
    rw [List.length_flatMap]
    simpa using sum_map_le_length_mul (List.finRange k) _
      ((8 + 3 * elemWallNumVerts h) * s) (fun a _ => hsub_len a)
  change (x.G.enc ++ x.W.encList ++ _).length ≤ (4 + (k + 1) * (8 + 3 * elemWallNumVerts h)) * s
  simp only [List.length_append]
  have hrhs :
      3 * s + (4 + 3 * elemWallNumVerts h) * s + k * ((8 + 3 * elemWallNumVerts h) * s) ≤
        (4 + (k + 1) * (8 + 3 * elemWallNumVerts h)) * s := by
    have hrew :
        (4 + (k + 1) * (8 + 3 * elemWallNumVerts h)) * s =
          4 * s + k * ((8 + 3 * elemWallNumVerts h) * s) + (8 + 3 * elemWallNumVerts h) * s := by
      ring
    have hle1 : 3 * s ≤ 4 * s := Nat.mul_le_mul_right s (by omega)
    have hle2 : (4 + 3 * elemWallNumVerts h) * s ≤ (8 + 3 * elemWallNumVerts h) * s :=
      Nat.mul_le_mul_right s (by omega)
    omega
  omega

/-! ### Section 3: Register Layout and Word RAM Parsing Gadgets -/

/-- Register holding the start offset in `inArr` of `x.W.internalVerts e`. -/
def rWStart {h : ℕ} (e : Fin (elemWallEdges h).length) : ℕ :=
  10 + 2 * e.1

/-- Register holding the length `(x.W.internalVerts e).length`. -/
def rWLen {h : ℕ} (e : Fin (elemWallEdges h).length) : ℕ :=
  10 + 2 * e.1 + 1

/-- Base register index for the `k` subwall-and-cross blocks. -/
def baseSubReg (h : ℕ) : ℕ :=
  10 + 2 * (elemWallEdges h).length

/-- Register holding `x.h_sub a`. -/
def rHSub (h : ℕ) {k : ℕ} (a : Fin k) : ℕ :=
  baseSubReg h + 5 * a.1

/-- Register holding the start offset in `inArr` of `(x.P a).map Fin.val`. -/
def rPStart (h : ℕ) {k : ℕ} (a : Fin k) : ℕ :=
  baseSubReg h + 5 * a.1 + 1

/-- Register holding `(x.P a).length`. -/
def rPLen (h : ℕ) {k : ℕ} (a : Fin k) : ℕ :=
  baseSubReg h + 5 * a.1 + 2

/-- Register holding the start offset in `inArr` of `(x.Q a).map Fin.val`. -/
def rQStart (h : ℕ) {k : ℕ} (a : Fin k) : ℕ :=
  baseSubReg h + 5 * a.1 + 3

/-- Register holding `(x.Q a).length`. -/
def rQLen (h : ℕ) {k : ℕ} (a : Fin k) : ℕ :=
  baseSubReg h + 5 * a.1 + 4

/-- Record the start offset (`r_pos + 1`) and length (`inArr[r_pos]`) of a length-prefixed list at
`r_pos`, and advance `r_pos` past the list. -/
def recordLenPrefixedProg (r_pos r_start r_len : Reg) : Cmd :=
  .seq (.assign r_len (.read inArr (.reg r_pos)))
    (.seq (.assign r_start (.op .add (.reg r_pos) (.const 1)))
      (.assign r_pos (.op .add (.reg r_start) (.reg r_len))))

theorem recordLenPrefixedProg_exec {w n : ℕ} {r_pos r_start r_len : ℕ}
    (hne_ps : r_pos ≠ r_start) (hne_pl : r_pos ≠ r_len) (hne_sl : r_start ≠ r_len)
    (pre : List ℕ) (L : List (Fin n)) (suf : List ℕ)
    (hw1 : 1 < 2 ^ w)
    (hnext_w : (pre ++ (L.length :: L.map Fin.val)).length < 2 ^ w)
    {s : State}
    (hin : s.arrs inArr = pre ++ (L.length :: L.map Fin.val) ++ suf)
    (hpos : s.regs r_pos = pre.length) :
    ∃ s' t,
      Exec w (recordLenPrefixedProg r_pos r_start r_len) s s' t ∧
      t ≤ 11 ∧
      s'.arrs inArr = s.arrs inArr ∧
      s'.regs r_start = pre.length + 1 ∧
      s'.regs r_len = L.length ∧
      s'.regs r_pos = (pre ++ (L.length :: L.map Fin.val)).length ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_start → r ≠ r_len → s'.regs r = s.regs r) := by
  have htot_len : (pre ++ (L.length :: L.map Fin.val)).length = pre.length + 1 + L.length := by
    simp [List.length_append]
    omega
  have hpos_w : pre.length < 2 ^ w := by omega
  have hlen_w : L.length < 2 ^ w := by omega
  have hp1_w : pre.length + 1 < 2 ^ w := by omega
  have hsum_w : pre.length + 1 + L.length < 2 ^ w := by omega
  have hin_len : pre.length < (s.arrs inArr).length := by
    rw [hin]
    simp [List.length_append]
  have hin_read : (s.arrs inArr)[pre.length]'hin_len = L.length := by
    let rest := (L.length :: L.map Fin.val) ++ suf
    have hsplit : s.arrs inArr = pre ++ rest := by
      rw [hin, List.append_assoc]
    have hlen2 : pre.length < (pre ++ rest).length := by
      simp [rest]
    apply getElem_of_eq hsplit rfl (h₂ := hlen2)
    rw [List.getElem_append_right (le_refl pre.length)]
    simp [rest]
  let s₁ := s.setReg r_len L.length
  have hex₁ : Exec w (.assign r_len (.read inArr (.reg r_pos))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hpos, hpos_w, hin_len, hin_read, hlen_w])
  let s₂ := s₁.setReg r_start (pre.length + 1)
  have hex₂ : Exec w (.assign r_start (.op .add (.reg r_pos) (.const 1))) s₁ s₂ 4 :=
    .assign (by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        State.setReg_regs_ne _ _ hne_pl, hpos, hpos_w, hw1, hp1_w])
  let s₃ := s₂.setReg r_pos (pre.length + 1 + L.length)
  have hex₃ : Exec w (.assign r_pos (.op .add (.reg r_start) (.reg r_len))) s₂ s₃ 4 :=
    .assign (by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        State.setReg_regs_ne _ _ hne_sl.symm, hp1_w, hlen_w, hsum_w])
  refine ⟨s₃, 3 + (4 + 4), .seq hex₁ (.seq hex₂ hex₃), by omega, rfl,
    by simp [s₃, s₂, State.setReg_regs_ne _ _ hne_ps.symm],
    by simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hne_pl.symm, State.setReg_regs_ne _ _ hne_sl.symm],
    by simp [s₃, htot_len],
    fun _ => rfl,
    fun r hr1 hr2 hr3 => by
      simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2,
        State.setReg_regs_ne _ _ hr3]⟩

/-- Parse the first `j` internal vertex lists of `x.W` (`j ≤ (elemWallEdges h).length`), advancing
`reg 4` (`r_pos`) and storing `(rWStart e, rWLen e)` for each `e.1 < j`. -/
def parseWEdgesUpTo (h : ℕ) : ℕ → Cmd
  | 0 => .skip
  | j + 1 =>
    .seq (parseWEdgesUpTo h j)
      (if hj : j < (elemWallEdges h).length then
        recordLenPrefixedProg 4 (rWStart ⟨j, hj⟩) (rWLen ⟨j, hj⟩)
      else .skip)

theorem parseWEdgesUpTo_exec {w h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (pre suf : List ℕ) (hw1 : 1 < 2 ^ w)
    (htot_w :
      (pre ++ (List.finRange (elemWallEdges h).length).flatMap
        (fun e => (W.internalVerts e).length :: (W.internalVerts e).map Fin.val)).length < 2 ^ w) :
    ∀ j (_hj : j ≤ (elemWallEdges h).length) {s : State}
      (_hin : s.arrs inArr =
        pre ++
          (List.finRange (elemWallEdges h).length).flatMap
            (fun e => (W.internalVerts e).length :: (W.internalVerts e).map Fin.val) ++
          suf)
      (_hpos : s.regs 4 = pre.length),
      ∃ s' t,
        Exec w (parseWEdgesUpTo h j) s s' t ∧
        t ≤ 1 + 11 * j ∧
        s'.arrs inArr = s.arrs inArr ∧
        s'.regs 4 =
          (pre ++ ((List.finRange (elemWallEdges h).length).take j).flatMap
            (fun e => (W.internalVerts e).length :: (W.internalVerts e).map Fin.val)).length ∧
        (∀ e : Fin (elemWallEdges h).length, e.1 < j →
          s'.regs (rWStart e) =
            (pre ++ ((List.finRange (elemWallEdges h).length).take e.1).flatMap
              (fun e' => (W.internalVerts e').length :: (W.internalVerts e').map Fin.val)).length + 1 ∧
          s'.regs (rWLen e) = (W.internalVerts e).length) ∧
        (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r ≠ 4 → (r < 10 ∨ 10 + 2 * j ≤ r) → s'.regs r = s.regs r)
  | 0, _, s, _, hpos => by
    exact ⟨s, 1, .skip s, le_rfl, rfl, by simpa using hpos,
      fun _ he => by omega, fun _ => rfl, fun _ _ _ => rfl⟩
  | j + 1, hj, s, hin, hpos => by
    have hj_lt : j < (elemWallEdges h).length := by omega
    let f : Fin (elemWallEdges h).length → List ℕ :=
      fun e => (W.internalVerts e).length :: (W.internalVerts e).map Fin.val
    rcases parseWEdgesUpTo_exec W pre suf hw1 htot_w j (by omega) hin hpos with
      ⟨s₁, t₁, hex₁, ht₁, hin₁, hpos₁, hprev₁, harr₁, hreg₁⟩
    let pre_j := pre ++ ((List.finRange (elemWallEdges h).length).take j).flatMap f
    let suf_j := ((List.finRange (elemWallEdges h).length).drop (j + 1)).flatMap f ++ suf
    have hsplit :
        pre ++ (List.finRange (elemWallEdges h).length).flatMap f ++ suf =
          pre_j ++ f ⟨j, hj_lt⟩ ++ suf_j := by
      rw [flatMap_finRange_eq_take_append_drop f j,
        flatMap_drop_eq_cons f hj_lt]
      simp [pre_j, suf_j, List.append_assoc]
    have hnext_le :
        (pre_j ++ f ⟨j, hj_lt⟩).length ≤
          (pre ++ (List.finRange (elemWallEdges h).length).flatMap f).length := by
      rw [flatMap_finRange_eq_take_append_drop f j,
        flatMap_drop_eq_cons f hj_lt]
      simp [pre_j, List.length_append]
    have hnext_w : (pre_j ++ f ⟨j, hj_lt⟩).length < 2 ^ w :=
      Nat.lt_of_le_of_lt hnext_le htot_w
    rcases recordLenPrefixedProg_exec (r_pos := 4) (r_start := rWStart ⟨j, hj_lt⟩)
        (r_len := rWLen ⟨j, hj_lt⟩)
        (by unfold rWStart; omega) (by unfold rWLen; omega) (by unfold rWStart rWLen; omega)
        pre_j (W.internalVerts ⟨j, hj_lt⟩) suf_j hw1 hnext_w
        (by rw [hin₁, hin, hsplit]) hpos₁ with
      ⟨s₂, t₂, hex₂, ht₂, hin₂, hstart₂, hlen₂, hpos₂, harr₂, hreg₂⟩
    have hpos₂' :
        s₂.regs 4 =
          (pre ++ ((List.finRange (elemWallEdges h).length).take (j + 1)).flatMap f).length := by
      rw [hpos₂, flatMap_take_succ_finRange f hj_lt, ← List.append_assoc]
    refine ⟨s₂, t₁ + t₂,
      by simpa [parseWEdgesUpTo, hj_lt] using Exec.seq hex₁ hex₂,
      by omega, hin₂.trans hin₁, hpos₂',
      fun e he => ?_,
      fun a => (harr₂ a).trans (harr₁ a),
      fun r hr4 hrb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp he with he_lt | he_eq
      · have h1 := hreg₂ (rWStart e) (by unfold rWStart; omega)
          (by unfold rWStart; dsimp; omega) (by unfold rWStart rWLen; dsimp; omega)
        have h2 := hreg₂ (rWLen e) (by unfold rWLen; omega)
          (by unfold rWLen rWStart; dsimp; omega) (by unfold rWLen; dsimp; omega)
        rw [h1, h2]
        exact hprev₁ e he_lt
      · have he_fin : e = ⟨j, hj_lt⟩ := Fin.ext he_eq
        subst he_fin
        exact ⟨hstart₂, hlen₂⟩
    · have h2 := hreg₂ r hr4
        (by unfold rWStart; dsimp; omega) (by unfold rWLen; dsimp; omega)
      rw [h2]
      rcases hrb with hlt | hge
      · exact hreg₁ r hr4 (Or.inl hlt)
      · exact hreg₁ r hr4 (Or.inr (by omega))

/-- Skip `m` length-prefixed lists in `inArr` starting at `reg 4` (`r_pos`), using `reg 5` (`r_idx`)
as loop counter and `reg 6` (`r_cnt = m`) as loop bound. -/
def skipLenPrefixedListsProg : Cmd :=
  .seq (.assign 5 (.const 0))
    (forUp 5 (.reg 6)
      (.assign 4 (.op .add (.op .add (.reg 4) (.const 1)) (.read inArr (.reg 4)))))

theorem skipLenPrefixedListsProg_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W_sub : WallOfHeight h' G) (pre suf : List ℕ)
    (hw1 : 1 < 2 ^ w)
    (hm_w : (elemWallEdges h').length < 2 ^ w)
    (htot_w :
      (pre ++ (List.finRange (elemWallEdges h').length).flatMap
        (fun e => (W_sub.internalVerts e).length :: (W_sub.internalVerts e).map Fin.val)).length <
        2 ^ w)
    {s : State}
    (hin : s.arrs inArr =
      pre ++
        (List.finRange (elemWallEdges h').length).flatMap
          (fun e => (W_sub.internalVerts e).length :: (W_sub.internalVerts e).map Fin.val) ++
        suf)
    (hpos : s.regs 4 = pre.length)
    (hcnt : s.regs 6 = (elemWallEdges h').length) :
    ∃ s' t,
      Exec w skipLenPrefixedListsProg s s' t ∧
      t ≤ 5 + 14 * (elemWallEdges h').length ∧
      s'.arrs inArr = s.arrs inArr ∧
      s'.regs 4 =
        (pre ++ (List.finRange (elemWallEdges h').length).flatMap
          (fun e => (W_sub.internalVerts e).length :: (W_sub.internalVerts e).map Fin.val)).length ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 4 → r ≠ 5 → s'.regs r = s.regs r) := by
  let m := (elemWallEdges h').length
  let f : Fin m → List ℕ :=
    fun e => (W_sub.internalVerts e).length :: (W_sub.internalVerts e).map Fin.val
  have h0_w : 0 < 2 ^ w := by omega
  let s₀ := s.setReg 5 0
  have hex₀ : Exec w (.assign 5 (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.arrs inArr = s.arrs inArr ∧
    st.regs 4 = (pre ++ ((List.finRange m).take i).flatMap f).length ∧
    st.regs 5 = i ∧
    st.regs 6 = m ∧
    (∀ a : ℕ, st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ 4 → r ≠ 5 → st.regs r = s.regs r)
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp 5 (.reg 6)
          (.assign 4 (.op .add (.op .add (.reg 4) (.const 1)) (.read inArr (.reg 4))))
      ⦃Inv m⦄ ≤ fun _ => 3 + m * (7 + 7) := by
    apply Triple.forUp_const Inv m 7 hw1 hm_w
    · intro i _ st ⟨_, _, hr5, hr6, _, _⟩
      exact ⟨hr5, by simp [Expr.eval, checkWord, hr6, m, hm_w]⟩
    · intro i hi st ⟨hin_st, hr4, hr5, hr6, harrs, hregs⟩
      let pre_i := pre ++ ((List.finRange m).take i).flatMap f
      let suf_i := ((List.finRange m).drop (i + 1)).flatMap f ++ suf
      have hsplit :
          pre ++ (List.finRange m).flatMap f ++ suf = pre_i ++ f ⟨i, hi⟩ ++ suf_i := by
        rw [flatMap_finRange_eq_take_append_drop f i, flatMap_drop_eq_cons f hi]
        simp [pre_i, suf_i, List.append_assoc]
      have hnext_le :
          (pre_i ++ f ⟨i, hi⟩).length ≤ (pre ++ (List.finRange m).flatMap f).length := by
        rw [flatMap_finRange_eq_take_append_drop f i, flatMap_drop_eq_cons f hi]
        simp [pre_i, List.length_append]
      have hnext_w : (pre_i ++ f ⟨i, hi⟩).length < 2 ^ w :=
        Nat.lt_of_le_of_lt hnext_le htot_w
      have htot_i :
          (pre_i ++ f ⟨i, hi⟩).length =
            pre_i.length + 1 + (W_sub.internalVerts ⟨i, hi⟩).length := by
        simp [f, List.length_append]
        omega
      have hpos_w : pre_i.length < 2 ^ w := by omega
      have hp1_w : pre_i.length + 1 < 2 ^ w := by omega
      have hlen_w : (W_sub.internalVerts ⟨i, hi⟩).length < 2 ^ w := by omega
      have hsum_w : pre_i.length + 1 + (W_sub.internalVerts ⟨i, hi⟩).length < 2 ^ w := by omega
      have hin_len : pre_i.length < (st.arrs inArr).length := by
        rw [hin_st, hin, hsplit]
        simp [f, List.length_append]
      have hin_read : (st.arrs inArr)[pre_i.length]'hin_len =
          (W_sub.internalVerts ⟨i, hi⟩).length := by
        let rest := f ⟨i, hi⟩ ++ suf_i
        have hsplit2 : st.arrs inArr = pre_i ++ rest := by
          rw [hin_st, hin, hsplit, List.append_assoc]
        have hlen2 : pre_i.length < (pre_i ++ rest).length := by
          simp [rest, f]
        apply getElem_of_eq hsplit2 rfl (h₂ := hlen2)
        rw [List.getElem_append_right (le_refl pre_i.length)]
        simp [rest, f]
      let st' := st.setReg 4 (pre_i.length + 1 + (W_sub.internalVerts ⟨i, hi⟩).length)
      have hr4' : st.regs 4 = pre_i.length := hr4
      have hex_step :
          Exec w (.assign 4 (.op .add (.op .add (.reg 4) (.const 1)) (.read inArr (.reg 4))))
            st st' 7 :=
        .assign (by
          simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4', hpos_w, hw1, hp1_w,
            hin_len, hin_read, hlen_w, hsum_w, ↓reduceIte, ↓reduceDIte])
      refine ⟨st', 7, hex_step, le_rfl, ?_, by simp [st', hr5]⟩
      have hpos_next :
          pre_i.length + 1 + (W_sub.internalVerts ⟨i, hi⟩).length =
            (pre ++ ((List.finRange m).take (i + 1)).flatMap f).length := by
        rw [← htot_i, flatMap_take_succ_finRange f hi, ← List.append_assoc]
      refine ⟨hin_st,
        by simp [st', hpos_next],
        State.setReg_regs_self st' 5 (i + 1),
        by simp [st', hr6],
        harrs,
        fun r hr4_ne hr5_ne => by
          simp [st', State.setReg_regs_ne _ _ hr4_ne, State.setReg_regs_ne _ _ hr5_ne, hregs r hr4_ne hr5_ne]⟩
  have hInv0 : Inv 0 s₀ := by
    refine ⟨rfl, by simpa [s₀] using hpos, by simp [s₀], by simp [s₀, hcnt, m],
      fun _ => rfl,
      fun r _ hr5 => by simp [s₀, State.setReg_regs_ne _ _ hr5]⟩
  rcases hLoop s₀ hInv0 with ⟨s₁, t₁, hex₁, ht₁, hin₁, hr4_1, _, _, harrs₁, hregs₁⟩
  dsimp only at ht₁
  have htake_all : (List.finRange m).take m = List.finRange m :=
    List.take_of_length_le (by simp)
  rw [htake_all] at hr4_1
  exact ⟨s₁, 2 + t₁, .seq hex₀ hex₁, by omega, hin₁, hr4_1, harrs₁, hregs₁⟩

/-- Parse one subwall-and-cross block `(x.W_sub a).encList ++ enc(x.P a) ++ enc(x.Q a)` starting at
`reg 4` (`r_pos`), recording `rHSub h a`, `rPStart h a`, `rPLen h a`, `rQStart h a`, `rQLen h a`
and advancing `reg 4` past the block. -/
def parseOneSubwallBlockProg (h : ℕ) {k : ℕ} (a : Fin k) : Cmd :=
  .seq (.assign (rHSub h a) (.read inArr (.reg 4)))
    (.seq (.assign 7 (.read inArr (.op .add (.reg 4) (.const 1))))
      (.seq (.assign 6 (.read inArr (.op .add (.reg 4) (.const 2))))
        (.seq (.assign 4 (.op .add (.op .add (.reg 4) (.const 3)) (.reg 7)))
          (.seq skipLenPrefixedListsProg
            (.seq (recordLenPrefixedProg 4 (rPStart h a) (rPLen h a))
              (recordLenPrefixedProg 4 (rQStart h a) (rQLen h a)))))))

theorem parseOneSubwallBlockProg_exec {w h k n : ℕ} {G : MultiDigraph n}
    (a : Fin k) {h_sub : ℕ} (W_sub : WallOfHeight h_sub G) (P Q : List (Fin n))
    (pre suf : List ℕ)
    (hw2 : 3 < 2 ^ w)
    (hh_w : h_sub < 2 ^ w)
    (hV_w : elemWallNumVerts h_sub < 2 ^ w)
    (hE_w : (elemWallEdges h_sub).length < 2 ^ w)
    (htot_w :
      (pre ++ (W_sub.encList ++ (P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val))).length <
        2 ^ w)
    {s : State}
    (hin : s.arrs inArr =
      pre ++ (W_sub.encList ++ (P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val)) ++ suf)
    (hpos : s.regs 4 = pre.length) :
    ∃ s' t,
      Exec w (parseOneSubwallBlockProg h a) s s' t ∧
      t ≤ 46 + 14 * (elemWallEdges h_sub).length ∧
      s'.arrs inArr = s.arrs inArr ∧
      s'.regs 4 =
        (pre ++ (W_sub.encList ++ (P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val))).length ∧
      s'.regs (rHSub h a) = h_sub ∧
      s'.regs (rPStart h a) = (pre ++ W_sub.encList).length + 1 ∧
      s'.regs (rPLen h a) = P.length ∧
      s'.regs (rQStart h a) = (pre ++ W_sub.encList ++ (P.length :: P.map Fin.val)).length + 1 ∧
      s'.regs (rQLen h a) = Q.length ∧
      (∀ arr : ℕ, s'.arrs arr = s.arrs arr) ∧
      (∀ r : ℕ,
        r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 →
        (r < baseSubReg h + 5 * a.1 ∨ baseSubReg h + 5 * (a.1 + 1) ≤ r) →
        s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  let hdr := [h_sub, elemWallNumVerts h_sub, (elemWallEdges h_sub).length] ++
    (List.finRange (elemWallNumVerts h_sub)).map (fun u => (W_sub.branchVert u).1)
  let edgesPart :=
    (List.finRange (elemWallEdges h_sub).length).flatMap
      (fun e => (W_sub.internalVerts e).length :: (W_sub.internalVerts e).map Fin.val)
  have hW_eq : W_sub.encList = hdr ++ edgesPart := by
    unfold WallOfHeight.encList
    rfl
  have hhdr_len : hdr.length = 3 + elemWallNumVerts h_sub := by
    simp [hdr]; omega
  have hpre_hdr_le : (pre ++ hdr).length ≤
      (pre ++ (W_sub.encList ++ (P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val))).length := by
    rw [hW_eq]
    simp [List.length_append]
  have hpre_W_le : (pre ++ W_sub.encList).length ≤
      (pre ++ (W_sub.encList ++ (P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val))).length := by
    simp [List.length_append]
  have hpre_WP_le : (pre ++ W_sub.encList ++ (P.length :: P.map Fin.val)).length ≤
      (pre ++ (W_sub.encList ++ (P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val))).length := by
    simp [List.length_append]
  have hpre_hdr_w : pre.length + (3 + elemWallNumVerts h_sub) < 2 ^ w := by
    have h := Nat.lt_of_le_of_lt hpre_hdr_le htot_w
    rwa [List.length_append, hhdr_len] at h
  have hpos_w : pre.length < 2 ^ w := by omega
  have hp1_w : pre.length + 1 < 2 ^ w := by omega
  have hp2_w : pre.length + 2 < 2 ^ w := by omega
  have hp3_w : pre.length + 3 < 2 ^ w := by omega
  have hphdr_w : pre.length + 3 + elemWallNumVerts h_sub < 2 ^ w := by omega
  have hin_len0 : pre.length < (s.arrs inArr).length := by
    rw [hin, hW_eq]; simp [hdr, List.length_append]
  have hin_len1 : pre.length + 1 < (s.arrs inArr).length := by
    rw [hin, hW_eq]; simp [hdr, List.length_append]
  have hin_len2 : pre.length + 2 < (s.arrs inArr).length := by
    rw [hin, hW_eq]; simp [hdr, List.length_append]
  have hsplit_hdr :
      s.arrs inArr =
        pre ++ ([h_sub, elemWallNumVerts h_sub, (elemWallEdges h_sub).length] ++
          ((List.finRange (elemWallNumVerts h_sub)).map (fun u => (W_sub.branchVert u).1) ++
            edgesPart ++ (P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val) ++ suf)) := by
    rw [hin, hW_eq]
    simp [hdr, List.append_assoc]
  have hread0 : (s.arrs inArr)[pre.length]'hin_len0 = h_sub := by
    apply getElem_of_eq hsplit_hdr rfl (h₂ := by rw [← hsplit_hdr]; exact hin_len0)
    rw [List.getElem_append_right (le_refl pre.length)]
    simp
  have hread1 : (s.arrs inArr)[pre.length + 1]'hin_len1 = elemWallNumVerts h_sub := by
    apply getElem_of_eq hsplit_hdr rfl (h₂ := by rw [← hsplit_hdr]; exact hin_len1)
    rw [List.getElem_append_right (by omega)]
    simp
  have hread2 : (s.arrs inArr)[pre.length + 2]'hin_len2 = (elemWallEdges h_sub).length := by
    apply getElem_of_eq hsplit_hdr rfl (h₂ := by rw [← hsplit_hdr]; exact hin_len2)
    rw [List.getElem_append_right (by omega)]
    simp
  have h4_ne_hsub : (4 : ℕ) ≠ rHSub h a := by
    unfold rHSub baseSubReg; omega
  let s₁ := s.setReg (rHSub h a) h_sub
  have hex₁ : Exec w (.assign (rHSub h a) (.read inArr (.reg 4))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hpos, hpos_w, hin_len0, hread0, hh_w])
  let s₂ := s₁.setReg 7 (elemWallNumVerts h_sub)
  have hex₂ : Exec w (.assign 7 (.read inArr (.op .add (.reg 4) (.const 1)))) s₁ s₂ 5 :=
    .assign (by
      have hr4 : s₁.regs 4 = pre.length := by
        rw [State.setReg_regs_ne _ _ h4_ne_hsub, hpos]
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hpos_w, hw1, hp1_w,
        hin_len1, hread1, hV_w])
  let s₃ := s₂.setReg 6 (elemWallEdges h_sub).length
  have hex₃ : Exec w (.assign 6 (.read inArr (.op .add (.reg 4) (.const 2)))) s₂ s₃ 5 :=
    .assign (by
      have hr4 : s₂.regs 4 = pre.length := by
        rw [State.setReg_regs_ne _ _ (by decide),
          State.setReg_regs_ne _ _ h4_ne_hsub, hpos]
      have harr2 : s₂.arrs inArr = s.arrs inArr := rfl
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, harr2, hpos_w,
        show 2 < 2 ^ w by omega, hp2_w, hin_len2, hread2, hE_w])
  let s₄ := s₃.setReg 4 (pre.length + 3 + elemWallNumVerts h_sub)
  have hex₄ : Exec w (.assign 4 (.op .add (.op .add (.reg 4) (.const 3)) (.reg 7))) s₃ s₄ 6 :=
    .assign (by
      have hr4 : s₃.regs 4 = pre.length := by
        rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_ne _ _ (by decide),
          State.setReg_regs_ne _ _ h4_ne_hsub, hpos]
      have hr7 : s₃.regs 7 = elemWallNumVerts h_sub := by
        rw [State.setReg_regs_ne _ _ (by decide)]
        exact State.setReg_regs_self s₁ 7 _
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr7, hpos_w, hw2, hp3_w,
        hV_w, hphdr_w])
  have hin₄ :
      s₄.arrs inArr =
        (pre ++ hdr) ++ edgesPart ++
          ((P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val) ++ suf) := by
    change s.arrs inArr = _
    rw [hin, hW_eq]
    simp [List.append_assoc]
  have hpos₄ : s₄.regs 4 = (pre ++ hdr).length := by
    simp [s₄, List.length_append, hhdr_len, Nat.add_assoc]
  have hcnt₄ : s₄.regs 6 = (elemWallEdges h_sub).length := by
    rw [State.setReg_regs_ne _ _ (by decide)]
    exact State.setReg_regs_self s₂ 6 _
  have htot_edges_w : ((pre ++ hdr) ++ edgesPart).length < 2 ^ w := by
    have : (pre ++ hdr) ++ edgesPart = pre ++ W_sub.encList := by
      rw [hW_eq, List.append_assoc]
    rw [this]
    exact Nat.lt_of_le_of_lt hpre_W_le htot_w
  rcases skipLenPrefixedListsProg_exec W_sub (pre ++ hdr)
      ((P.length :: P.map Fin.val) ++ (Q.length :: Q.map Fin.val) ++ suf)
      hw1 hE_w htot_edges_w hin₄ hpos₄ hcnt₄ with
    ⟨s₅, t₅, hex₅, ht₅, hin₅, hpos₅, harr₅, hreg₅⟩
  have hpos₅' : s₅.regs 4 = (pre ++ W_sub.encList).length := by
    rw [hpos₅, hW_eq, List.append_assoc]
  have hin₅' :
      s₅.arrs inArr =
        (pre ++ W_sub.encList) ++ (P.length :: P.map Fin.val) ++
          ((Q.length :: Q.map Fin.val) ++ suf) := by
    rw [hin₅]
    change s.arrs inArr = _
    rw [hin]
    simp [List.append_assoc]
  have htot_P_w : ((pre ++ W_sub.encList) ++ (P.length :: P.map Fin.val)).length < 2 ^ w :=
    Nat.lt_of_le_of_lt hpre_WP_le htot_w
  rcases recordLenPrefixedProg_exec (r_pos := 4) (r_start := rPStart h a) (r_len := rPLen h a)
      (by unfold rPStart baseSubReg; omega) (by unfold rPLen baseSubReg; omega)
      (by unfold rPStart rPLen baseSubReg; omega)
      (pre ++ W_sub.encList) P ((Q.length :: Q.map Fin.val) ++ suf)
      hw1 htot_P_w hin₅' hpos₅' with
    ⟨s₆, t₆, hex₆, ht₆, hin₆, hPstart₆, hPlen₆, hpos₆, harr₆, hreg₆⟩
  have hin₆' :
      s₆.arrs inArr =
        (pre ++ W_sub.encList ++ (P.length :: P.map Fin.val)) ++
          (Q.length :: Q.map Fin.val) ++ suf := by
    rw [hin₆, hin₅']
    simp [List.append_assoc]
  have htot_Q_w :
      ((pre ++ W_sub.encList ++ (P.length :: P.map Fin.val)) ++
        (Q.length :: Q.map Fin.val)).length < 2 ^ w := by
    simpa [List.append_assoc] using htot_w
  rcases recordLenPrefixedProg_exec (r_pos := 4) (r_start := rQStart h a) (r_len := rQLen h a)
      (by unfold rQStart baseSubReg; omega) (by unfold rQLen baseSubReg; omega)
      (by unfold rQStart rQLen baseSubReg; omega)
      (pre ++ W_sub.encList ++ (P.length :: P.map Fin.val)) Q suf
      hw1 htot_Q_w hin₆' hpos₆ with
    ⟨s₇, t₇, hex₇, ht₇, hin₇, hQstart₇, hQlen₇, hpos₇, harr₇, hreg₇⟩
  refine ⟨s₇, 3 + (5 + (5 + (6 + (t₅ + (t₆ + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by omega,
    by rw [hin₇, hin₆, hin₅]; rfl,
    by simpa [List.append_assoc] using hpos₇,
    ?_, ?_, ?_, hQstart₇, hQlen₇,
    fun arr => by rw [harr₇, harr₆, harr₅]; rfl,
    fun r hr4 hr5 hr6 hr7 hrb => ?_⟩
  · rw [hreg₇ (rHSub h a) (by unfold rHSub baseSubReg; omega)
      (by unfold rHSub rQStart baseSubReg; omega) (by unfold rHSub rQLen baseSubReg; omega),
      hreg₆ (rHSub h a) (by unfold rHSub baseSubReg; omega)
      (by unfold rHSub rPStart baseSubReg; omega) (by unfold rHSub rPLen baseSubReg; omega),
      hreg₅ (rHSub h a) (by unfold rHSub baseSubReg; omega) (by unfold rHSub baseSubReg; omega)]
    simp [s₄, s₃, s₂, s₁,
      State.setReg_regs_ne _ _ (by unfold rHSub baseSubReg; omega : rHSub h a ≠ 4),
      State.setReg_regs_ne _ _ (by unfold rHSub baseSubReg; omega : rHSub h a ≠ 6),
      State.setReg_regs_ne _ _ (by unfold rHSub baseSubReg; omega : rHSub h a ≠ 7)]
  · rw [hreg₇ (rPStart h a) (by unfold rPStart baseSubReg; omega)
      (by unfold rPStart rQStart baseSubReg; omega) (by unfold rPStart rQLen baseSubReg; omega)]
    exact hPstart₆
  · rw [hreg₇ (rPLen h a) (by unfold rPLen baseSubReg; omega)
      (by unfold rPLen rQStart baseSubReg; omega) (by unfold rPLen rQLen baseSubReg; omega)]
    exact hPlen₆
  · have hr_ne_hsub : r ≠ rHSub h a := by
      unfold rHSub
      rcases hrb with hlt | hge <;> omega
    have hr_ne_pstart : r ≠ rPStart h a := by
      unfold rPStart
      rcases hrb with hlt | hge <;> omega
    have hr_ne_plen : r ≠ rPLen h a := by
      unfold rPLen
      rcases hrb with hlt | hge <;> omega
    have hr_ne_qstart : r ≠ rQStart h a := by
      unfold rQStart
      rcases hrb with hlt | hge <;> omega
    have hr_ne_qlen : r ≠ rQLen h a := by
      unfold rQLen
      rcases hrb with hlt | hge <;> omega
    rw [hreg₇ r hr4 hr_ne_qstart hr_ne_qlen,
      hreg₆ r hr4 hr_ne_pstart hr_ne_plen,
      hreg₅ r hr4 hr5]
    simp [s₄, s₃, s₂, s₁,
      State.setReg_regs_ne _ _ hr4,
      State.setReg_regs_ne _ _ hr6,
      State.setReg_regs_ne _ _ hr7,
      State.setReg_regs_ne _ _ hr_ne_hsub]

/-- Parse the first `j` subwall-and-cross blocks (`j ≤ k`). -/
def parseSubwallsUpTo (h k : ℕ) : ℕ → Cmd
  | 0 => .skip
  | j + 1 =>
    .seq (parseSubwallsUpTo h k j)
      (if hj : j < k then
        parseOneSubwallBlockProg h ⟨j, hj⟩
      else .skip)

theorem parseSubwallsUpTo_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (hw2 : 3 < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hV_w : elemWallNumVerts h < 2 ^ w)
    (hE_w : 2 * elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w) :
    ∀ j (_hj : j ≤ k) {s : State}
      (_hin : s.arrs inArr = encAlg91In x)
      (_hpos : s.regs 4 = (x.G.enc ++ x.W.encList).length),
      ∃ s' t,
        Exec w (parseSubwallsUpTo h k j) s s' t ∧
        t ≤ 1 + j * (46 + 28 * elemWallNumVerts h) ∧
        s'.arrs inArr = s.arrs inArr ∧
        s'.regs 4 =
          ((x.G.enc ++ x.W.encList) ++
            ((List.finRange k).take j).flatMap (fun a =>
              (x.W_sub a).encList ++
              ((x.P a).length :: (x.P a).map Fin.val) ++
              ((x.Q a).length :: (x.Q a).map Fin.val))).length ∧
        (∀ a : Fin k, a.1 < j →
          let pre_a :=
            (x.G.enc ++ x.W.encList) ++
              ((List.finRange k).take a.1).flatMap (fun b =>
                (x.W_sub b).encList ++
                ((x.P b).length :: (x.P b).map Fin.val) ++
                ((x.Q b).length :: (x.Q b).map Fin.val))
          s'.regs (rHSub h a) = x.h_sub a ∧
          s'.regs (rPStart h a) = (pre_a ++ (x.W_sub a).encList).length + 1 ∧
          s'.regs (rPLen h a) = (x.P a).length ∧
          s'.regs (rQStart h a) =
            (pre_a ++ (x.W_sub a).encList ++ ((x.P a).length :: (x.P a).map Fin.val)).length + 1 ∧
          s'.regs (rQLen h a) = (x.Q a).length) ∧
        (∀ arr : ℕ, s'.arrs arr = s.arrs arr) ∧
        (∀ reg : ℕ,
          reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 →
          (reg < baseSubReg h ∨ baseSubReg h + 5 * j ≤ reg) →
          s'.regs reg = s.regs reg)
  | 0, _, s, _, hpos => by
    exact ⟨s, 1, .skip s, by omega, rfl, by simpa using hpos,
      fun _ ha => by omega, fun _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | j + 1, hj, s, hin, hpos => by
    have hj_lt : j < k := by omega
    let blk : Fin k → List ℕ := fun a =>
      (x.W_sub a).encList ++
      ((x.P a).length :: (x.P a).map Fin.val) ++
      ((x.Q a).length :: (x.Q a).map Fin.val)
    rcases parseSubwallsUpTo_exec x hw2 hh_w hV_w hE_w htot_w j (by omega) hin hpos with
      ⟨s₁, t₁, hex₁, ht₁, hin₁, hpos₁, hprev₁, harr₁, hreg₁⟩
    let pre_j := (x.G.enc ++ x.W.encList) ++ ((List.finRange k).take j).flatMap blk
    let suf_j := ((List.finRange k).drop (j + 1)).flatMap blk
    have hsplit : encAlg91In x = pre_j ++ blk ⟨j, hj_lt⟩ ++ suf_j := by
      unfold encAlg91In
      rw [flatMap_finRange_eq_take_append_drop blk j, flatMap_drop_eq_cons blk hj_lt]
      simp [pre_j, suf_j, List.append_assoc]
    have hnext_le : (pre_j ++ blk ⟨j, hj_lt⟩).length ≤ (encAlg91In x).length := by
      rw [hsplit]
      simp only [List.length_append]
      omega
    have hnext_w : (pre_j ++ blk ⟨j, hj_lt⟩).length < 2 ^ w :=
      Nat.lt_of_le_of_lt hnext_le htot_w
    have hh_le : x.h_sub ⟨j, hj_lt⟩ ≤ h := (x.hsub ⟨j, hj_lt⟩).2.2.1
    have hVj_le : elemWallNumVerts (x.h_sub ⟨j, hj_lt⟩) ≤ elemWallNumVerts h :=
      elemWallNumVerts_mono hh_le
    have hEj_le : (elemWallEdges (x.h_sub ⟨j, hj_lt⟩)).length ≤ 2 * elemWallNumVerts h :=
      (length_elemWallEdges_le _).trans (by omega)
    rcases parseOneSubwallBlockProg_exec (h := h) ⟨j, hj_lt⟩
        (x.W_sub ⟨j, hj_lt⟩) (x.P ⟨j, hj_lt⟩) (x.Q ⟨j, hj_lt⟩) pre_j suf_j
        hw2 (by omega) (by omega) (by omega) hnext_w
        (by rw [hin₁, hin, hsplit]) hpos₁ with
      ⟨s₂, t₂, hex₂, ht₂, hin₂, hpos₂, hhsub₂, hPstart₂, hPlen₂, hQstart₂, hQlen₂, harr₂, hreg₂⟩
    have hpos₂' :
        s₂.regs 4 = ((x.G.enc ++ x.W.encList) ++ ((List.finRange k).take (j + 1)).flatMap blk).length := by
      rw [hpos₂, flatMap_take_succ_finRange blk hj_lt]
      simp [pre_j, blk, List.append_assoc]
    have ht_step : t₂ ≤ 46 + 28 * elemWallNumVerts h := by nlinarith
    have ht_tot : t₁ + t₂ ≤ 1 + (j + 1) * (46 + 28 * elemWallNumVerts h) := by
      calc t₁ + t₂ ≤ (1 + j * (46 + 28 * elemWallNumVerts h)) + (46 + 28 * elemWallNumVerts h) :=
            Nat.add_le_add ht₁ ht_step
        _ = 1 + (j + 1) * (46 + 28 * elemWallNumVerts h) := by ring
    refine ⟨s₂, t₁ + t₂,
      by simpa [parseSubwallsUpTo, hj_lt] using Exec.seq hex₁ hex₂,
      ht_tot,
      hin₂.trans hin₁, hpos₂',
      fun a ha => ?_,
      fun arr => (harr₂ arr).trans (harr₁ arr),
      fun reg hr4 hr5 hr6 hr7 hrb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq
      · have h1 := hreg₂ (rHSub h a) (by unfold rHSub baseSubReg; omega)
          (by unfold rHSub baseSubReg; omega) (by unfold rHSub baseSubReg; omega)
          (by unfold rHSub baseSubReg; omega) (Or.inl (by unfold rHSub; dsimp; omega))
        have h2 := hreg₂ (rPStart h a) (by unfold rPStart baseSubReg; omega)
          (by unfold rPStart baseSubReg; omega) (by unfold rPStart baseSubReg; omega)
          (by unfold rPStart baseSubReg; omega) (Or.inl (by unfold rPStart; dsimp; omega))
        have h3 := hreg₂ (rPLen h a) (by unfold rPLen baseSubReg; omega)
          (by unfold rPLen baseSubReg; omega) (by unfold rPLen baseSubReg; omega)
          (by unfold rPLen baseSubReg; omega) (Or.inl (by unfold rPLen; dsimp; omega))
        have h4 := hreg₂ (rQStart h a) (by unfold rQStart baseSubReg; omega)
          (by unfold rQStart baseSubReg; omega) (by unfold rQStart baseSubReg; omega)
          (by unfold rQStart baseSubReg; omega) (Or.inl (by unfold rQStart; dsimp; omega))
        have h5 := hreg₂ (rQLen h a) (by unfold rQLen baseSubReg; omega)
          (by unfold rQLen baseSubReg; omega) (by unfold rQLen baseSubReg; omega)
          (by unfold rQLen baseSubReg; omega) (Or.inl (by unfold rQLen; dsimp; omega))
        rw [h1, h2, h3, h4, h5]
        exact hprev₁ a ha_lt
      · have ha_fin : a = ⟨j, hj_lt⟩ := Fin.ext ha_eq
        subst ha_fin
        exact ⟨hhsub₂, hPstart₂, hPlen₂, hQstart₂, hQlen₂⟩
    · rcases hrb with hlt | hge
      · have h2 : reg < baseSubReg h + 5 * (⟨j, hj_lt⟩ : Fin k).1 ∨
            baseSubReg h + 5 * ((⟨j, hj_lt⟩ : Fin k).1 + 1) ≤ reg :=
          Or.inl (Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _))
        rw [hreg₂ reg hr4 hr5 hr6 hr7 h2]
        exact hreg₁ reg hr4 hr5 hr6 hr7 (Or.inl hlt)
      · have h2 : reg < baseSubReg h + 5 * (⟨j, hj_lt⟩ : Fin k).1 ∨
            baseSubReg h + 5 * ((⟨j, hj_lt⟩ : Fin k).1 + 1) ≤ reg :=
          Or.inr hge
        have h1 : reg < baseSubReg h ∨ baseSubReg h + 5 * j ≤ reg :=
          Or.inr (Nat.le_trans (Nat.add_le_add_left (by omega : 5 * j ≤ 5 * (j + 1)) _) hge)
        rw [hreg₂ reg hr4 hr5 hr6 hr7 h2]
        exact hreg₁ reg hr4 hr5 hr6 hr7 h1

/-! ### Section 4: Marking Vertices and Slices into Bitset Array `2` -/

/-- Mark `x.W.branchVert u` in bitset array `2` by reading `inArr[r_offW + 3 + u.1]` (`r_offW = 3`). -/
def markBranchVertProg {h : ℕ} (u : Fin (elemWallNumVerts h)) : Cmd :=
  .write 2 (.read inArr (.op .add (.reg 3) (.const (3 + u.1)))) (.const 1)

theorem markBranchVertProg_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (u : Fin (elemWallNumVerts h))
    (pre suf : List ℕ) (S : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (pre ++ W.encList).length < 2 ^ w)
    {s : State}
    (hin : s.arrs inArr = pre ++ W.encList ++ suf)
    (hoffW : s.regs 3 = pre.length)
    (harr2 : s.arrs 2 = bitSetList S) :
    ∃ s' t,
      Exec w (markBranchVertProg u) s s' t ∧
      t ≤ 6 ∧
      s'.arrs 2 = bitSetList (insert (W.branchVert u) S) ∧
      (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, s'.regs r = s.regs r) := by
  have hu_lt := u.2
  have hoff_w : pre.length < 2 ^ w := by
    simp [List.length_append] at htot_w; omega
  have hc_lt_w : 3 + u.1 < 2 ^ w := by omega
  have hidx_w : pre.length + (3 + u.1) < 2 ^ w := by
    have hlen := W.length_encList
    simp [List.length_append] at htot_w
    omega
  have hin_len : pre.length + (3 + u.1) < (s.arrs inArr).length := by
    rw [hin]
    simp [List.length_append, W.length_encList]
    omega
  have hread : (s.arrs inArr)[pre.length + (3 + u.1)]'hin_len = (W.branchVert u).1 := by
    let hdr := pre ++ [h, elemWallNumVerts h, (elemWallEdges h).length]
    let bvs := (List.finRange (elemWallNumVerts h)).map (fun u' => (W.branchVert u').1)
    let rest :=
      (List.finRange (elemWallEdges h).length).flatMap
        (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ++ suf
    have hsplit : s.arrs inArr = hdr ++ (bvs ++ rest) := by
      rw [hin]
      unfold WallOfHeight.encList
      simp [hdr, bvs, rest, List.append_assoc]
    have hidx_eq : pre.length + (3 + u.1) = hdr.length + u.1 := by
      simp [hdr]
      omega
    apply getElem_of_eq hsplit hidx_eq (h₂ := by rw [← hsplit, ← hidx_eq]; exact hin_len)
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left (by simp [bvs, hu_lt])]
    simp [bvs]
  have hv_w : (W.branchVert u).1 < 2 ^ w := Nat.lt_of_lt_of_le (W.branchVert u).2 (by omega)
  have hidx_eval :
      (Expr.read inArr (.op .add (.reg 3) (.const (3 + u.1)))).eval w s =
        some (W.branchVert u).1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hoffW, hoff_w, hc_lt_w,
      hidx_w, hin_len, hread, hv_w]
  have hval_eval : (Expr.const 1).eval w s = some 1 := by
    simp [Expr.eval, checkWord, hw1]
  have hbound : (W.branchVert u).1 < (s.arrs 2).length := by
    rw [harr2, length_bitSetList]
    exact (W.branchVert u).2
  let s' := s.writeArr 2 (W.branchVert u).1 1
  have hex : Exec w (markBranchVertProg u) s s' 6 :=
    .write hidx_eval hval_eval hbound
  refine ⟨s', 6, hex, le_rfl, ?_,
    fun a ha => State.writeArr_arrs_ne s _ _ ha,
    fun _ => rfl⟩
  simp only [s', State.writeArr_arrs_self, harr2, bitSetList_set_one]

/-- Mark a list of branch vertices `us : List (Fin (elemWallNumVerts h))` in bitset array `2`. -/
def markBranchVertListProg {h : ℕ} : List (Fin (elemWallNumVerts h)) → Cmd
  | [] => .skip
  | u :: us => .seq (markBranchVertProg u) (markBranchVertListProg us)

theorem markBranchVertListProg_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (pre suf : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (pre ++ W.encList).length < 2 ^ w) :
    ∀ (us : List (Fin (elemWallNumVerts h))) (S : Finset (Fin n)) {s : State}
      (_hin : s.arrs inArr = pre ++ W.encList ++ suf)
      (_hoffW : s.regs 3 = pre.length)
      (_harr2 : s.arrs 2 = bitSetList S),
      ∃ s' t,
        Exec w (markBranchVertListProg us) s s' t ∧
        t ≤ 1 + 6 * us.length ∧
        s'.arrs 2 = bitSetList (S ∪ us.toFinset.image W.branchVert) ∧
        (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, s'.regs r = s.regs r)
  | [], S, s, _, _, harr2 => by
    exact ⟨s, 1, .skip s, le_rfl, by simpa using harr2, fun _ _ => rfl, fun _ => rfl⟩
  | u :: us, S, s, hin, hoffW, harr2 => by
    rcases markBranchVertProg_exec W u pre suf S hw1 hn_w hc_w htot_w hin hoffW harr2 with
      ⟨s₁, t₁, hex₁, ht₁, harr2_1, harr₁, hreg₁⟩
    rcases markBranchVertListProg_exec W pre suf hw1 hn_w hc_w htot_w us
        (insert (W.branchVert u) S)
        (by rw [harr₁ inArr (by decide), hin])
        (by rw [hreg₁ 3, hoffW])
        harr2_1 with
      ⟨s₂, t₂, hex₂, ht₂, harr2_2, harr₂, hreg₂⟩
    have hset_eq :
        insert (W.branchVert u) S ∪ us.toFinset.image W.branchVert =
          S ∪ (u :: us).toFinset.image W.branchVert := by
      ext x
      simp [or_left_comm]
    rw [hset_eq] at harr2_2
    exact ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by simp [List.length_cons]; omega, harr2_2,
      fun a ha => (harr₂ a ha).trans (harr₁ a ha),
      fun r => (hreg₂ r).trans (hreg₁ r)⟩

/-- Mark every vertex of a slice `L.map Fin.val` in `inArr` (starting at `reg 6` of length `reg 7`,
using `reg 5` as loop counter) into bitset array `2`. -/
def markSliceProg : Cmd :=
  .seq (.assign 5 (.const 0))
    (forUp 5 (.reg 7)
      (.write 2 (.read inArr (.op .add (.reg 6) (.reg 5))) (.const 1)))

theorem markSliceProg_exec {w n : ℕ} (pre : List ℕ) (L : List (Fin n)) (suf : List ℕ)
    (S : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (htot_w : (pre ++ L.map Fin.val).length < 2 ^ w)
    {s : State}
    (hin : s.arrs inArr = pre ++ L.map Fin.val ++ suf)
    (hstart : s.regs 6 = pre.length)
    (hlen : s.regs 7 = L.length)
    (harr2 : s.arrs 2 = bitSetList S) :
    ∃ s' t,
      Exec w markSliceProg s s' t ∧
      t ≤ 5 + 14 * L.length ∧
      s'.arrs 2 = bitSetList (S ∪ L.toFinset) ∧
      (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 5 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : L.length < 2 ^ w := by simp [List.length_append] at htot_w; omega
  have hpre_w : pre.length < 2 ^ w := by simp [List.length_append] at htot_w; omega
  let s₀ := s.setReg 5 0
  have hex₀ : Exec w (.assign 5 (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.arrs inArr = s.arrs inArr ∧
    st.arrs 2 = bitSetList (S ∪ (L.take i).toFinset) ∧
    st.regs 5 = i ∧
    st.regs 6 = pre.length ∧
    st.regs 7 = L.length ∧
    (∀ a : ℕ, a ≠ 2 → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ 5 → st.regs r = s.regs r)
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp 5 (.reg 7)
          (.write 2 (.read inArr (.op .add (.reg 6) (.reg 5))) (.const 1))
      ⦃Inv L.length⦄ ≤ fun _ => 3 + L.length * (7 + 6) := by
    apply Triple.forUp_const Inv L.length 6 hw1 hlen_w
    · intro i _ st ⟨_, _, hr5, _, hr7, _, _⟩
      exact ⟨hr5, by simp [Expr.eval, checkWord, hr7, hlen_w]⟩
    · intro i hi st ⟨hin_st, harr2_st, hr5, hr6, hr7, harrs, hregs⟩
      have hi_w : i < 2 ^ w := by omega
      have hadd_w : pre.length + i < 2 ^ w := by
        simp [List.length_append] at htot_w; omega
      have hin_len : pre.length + i < (st.arrs inArr).length := by
        rw [hin_st, hin]
        simp [List.length_append]
        omega
      have hread : (st.arrs inArr)[pre.length + i]'hin_len = (L[i]'hi).1 := by
        let rest := L.map Fin.val ++ suf
        have hsplit : st.arrs inArr = pre ++ rest := by
          rw [hin_st, hin, List.append_assoc]
        have hlen2 : pre.length + i < (pre ++ rest).length := by
          simp [rest, List.length_append]
          omega
        apply getElem_of_eq hsplit rfl (h₂ := hlen2)
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem_append_left (by simp [hi])]
        simp
      have hv_w : (L[i]'hi).1 < 2 ^ w := Nat.lt_of_lt_of_le (L[i]'hi).2 (by omega)
      have hidx_eval :
          (Expr.read inArr (.op .add (.reg 6) (.reg 5))).eval w st = some (L[i]'hi).1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6, hr5, hpre_w, hi_w,
          hadd_w, hin_len, hread, hv_w]
      have hval_eval : (Expr.const 1).eval w st = some 1 := by
        simp [Expr.eval, checkWord, hw1]
      have hbound : (L[i]'hi).1 < (st.arrs 2).length := by
        rw [harr2_st, length_bitSetList]
        exact (L[i]'hi).2
      let st' := st.writeArr 2 (L[i]'hi).1 1
      have hex_w : Exec w (.write 2 (.read inArr (.op .add (.reg 6) (.reg 5))) (.const 1)) st st' 6 :=
        .write hidx_eval hval_eval hbound
      refine ⟨st', 6, hex_w, le_rfl, ?_, by simp [st', hr5]⟩
      have hset_eq :
          insert (L[i]'hi) (S ∪ (L.take i).toFinset) = S ∪ (L.take (i + 1)).toFinset := by
        rw [take_add_one_toFinset L hi, Finset.union_insert]
      refine ⟨by simpa [st', State.writeArr_arrs_ne _ _ _ (by decide : inArr ≠ 2)] using hin_st,
        by simp [st', harr2_st, bitSetList_set_one, hset_eq],
        State.setReg_regs_self st' 5 (i + 1),
        by simp [st', hr6],
        by simp [st', hr7],
        fun a ha => by
          rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]
          exact harrs a ha,
        fun r hr => by
          rw [State.setReg_regs_ne _ _ hr, State.writeArr_regs]
          exact hregs r hr⟩
  have hInv0 : Inv 0 s₀ := by
    refine ⟨rfl, by simpa [s₀] using harr2, by simp [s₀], by simp [s₀, hstart],
      by simp [s₀, hlen], fun _ _ => rfl,
      fun r hr => by simp [s₀, State.setReg_regs_ne _ _ hr]⟩
  rcases hLoop s₀ hInv0 with ⟨s₁, t₁, hex₁, ht₁, _, harr2_1, _, _, _, harrs₁, hregs₁⟩
  dsimp only at ht₁
  rw [List.take_length] at harr2_1
  exact ⟨s₁, 2 + t₁, .seq hex₀ hex₁, by omega, harr2_1, harrs₁, hregs₁⟩

/-- Mark `x.W.internalVerts e` in bitset array `2`. -/
def markWallEdgeProg {h : ℕ} (e : Fin (elemWallEdges h).length) : Cmd :=
  .seq (.assign 6 (.reg (rWStart e)))
    (.seq (.assign 7 (.reg (rWLen e)))
      markSliceProg)

/-- Mark a list of wall edges `es : List (Fin (elemWallEdges h).length)` in bitset array `2`. -/
def markWallEdgeListProg {h : ℕ} : List (Fin (elemWallEdges h).length) → Cmd
  | [] => .skip
  | e :: es => .seq (markWallEdgeProg e) (markWallEdgeListProg es)

/-- Mark the internal vertices `((L.drop 1).dropLast)` of a cross path starting at `r_start` of
length `r_len` in bitset array `2`. -/
def markCrossPathProg (r_start r_len : Reg) : Cmd :=
  .seq (.assign 6 (.op .add (.reg r_start) (.const 1)))
    (.seq (.assign 7 (.op .sub (.reg r_len) (.const 2)))
      markSliceProg)

/-- Mark `((x.P a).drop 1).dropLast` for each `a ∈ as` in bitset array `2`. -/
def markCrossPListProg (h : ℕ) {k : ℕ} : List (Fin k) → Cmd
  | [] => .skip
  | a :: as => .seq (markCrossPathProg (rPStart h a) (rPLen h a)) (markCrossPListProg h as)

/-- Mark `((x.Q a).drop 1).dropLast` for each `a ∈ as` in bitset array `2`. -/
def markCrossQListProg (h : ℕ) {k : ℕ} : List (Fin k) → Cmd
  | [] => .skip
  | a :: as => .seq (markCrossPathProg (rQStart h a) (rQLen h a)) (markCrossQListProg h as)

/-- Copy `n` words (`reg 1`) from array `2` into `outArr` (`arr 1`) starting at offset `reg 8`
(`idx * n`), using `reg 5` as loop counter, then advance `reg 8` by `reg 1`. -/
def appendArr2ToOutProg : Cmd :=
  .seq
    (.seq (.assign 5 (.const 0))
      (forUp 5 (.reg 1)
        (.write outArr (.op .add (.reg 8) (.reg 5)) (.read 2 (.reg 5)))))
    (.assign 8 (.op .add (.reg 8) (.reg 1)))

theorem appendArr2ToOutProg_exec {w n p : ℕ} (X : Fin p → Finset (Fin n))
    (j : ℕ) (hj : j < p)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hpn_w : p * n < 2 ^ w)
    {s : State}
    (hr1 : s.regs 1 = n)
    (hr8 : s.regs 8 = j * n)
    (harr2 : s.arrs 2 = bitSetList (X ⟨j, hj⟩))
    (hout : s.arrs outArr = encBitSetsUpTo X j ++ List.replicate ((p - j) * n) 0) :
    ∃ s' t,
      Exec w appendArr2ToOutProg s s' t ∧
      t ≤ 9 + 14 * n ∧
      s'.arrs outArr = encBitSetsUpTo X (j + 1) ++ List.replicate ((p - (j + 1)) * n) 0 ∧
      s'.regs 8 = (j + 1) * n ∧
      (∀ a : ℕ, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 5 → r ≠ 8 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hjp1_le : (j + 1) * n ≤ p * n := Nat.mul_le_mul_right n hj
  have hjn_w : j * n < 2 ^ w := by
    have : j * n ≤ (j + 1) * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hjp1n_w : (j + 1) * n < 2 ^ w := by omega
  have hpre_len : (encBitSetsUpTo X j).length = j * n :=
    length_encBitSetsUpTo X j (by omega)
  have hout_len : (s.arrs outArr).length = p * n := by
    rw [hout, List.length_append, hpre_len, List.length_replicate]
    rw [← Nat.add_mul, Nat.add_sub_of_le (by omega)]
  let s₀ := s.setReg 5 0
  have hex₀ : Exec w (.assign 5 (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (i : ℕ) (st : State) : Prop :=
    ∃ (hi_le : i ≤ n) (hout_len_st : (st.arrs outArr).length = p * n),
      st.arrs 2 = bitSetList (X ⟨j, hj⟩) ∧
      (∀ idx (hidx_pn : idx < p * n),
        (st.arrs outArr)[idx]'(by rw [hout_len_st]; exact hidx_pn) =
          if hidx : idx < j * n + i then
            if hlt : idx < j * n then
              (encBitSetsUpTo X j)[idx]'(by rw [hpre_len]; exact hlt)
            else
              (bitSetList (X ⟨j, hj⟩))[idx - j * n]'(by rw [length_bitSetList]; omega)
          else 0) ∧
      st.regs 1 = n ∧
      st.regs 5 = i ∧
      st.regs 8 = j * n ∧
      (∀ a : ℕ, a ≠ outArr → st.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 5 → st.regs r = s.regs r)
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp 5 (.reg 1)
          (.write outArr (.op .add (.reg 8) (.reg 5)) (.read 2 (.reg 5)))
      ⦃Inv n⦄ ≤ fun _ => 3 + n * (7 + 6) := by
    apply Triple.forUp_const Inv n 6 hw1 hn_w
    · intro i _ st ⟨_, _, _, _, hr1_st, hr5_st, _, _, _⟩
      exact ⟨hr5_st, by simp [Expr.eval, checkWord, hr1_st, hn_w]⟩
    · intro i hi st ⟨_, hout_len_st, harr2_st, hout_get, hr1_st, hr5_st, hr8_st, harrs, hregs⟩
      have hi_w : i < 2 ^ w := by omega
      have hadd_w : j * n + i < 2 ^ w := by
        have : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
        omega
      have hi_arr2 : i < (st.arrs 2).length := by
        rw [harr2_st, length_bitSetList]; exact hi
      have hval_le : (st.arrs 2)[i]'hi_arr2 ≤ 1 := by
        have hlen_bs : i < (bitSetList (X ⟨j, hj⟩)).length := by
          rw [length_bitSetList]; exact hi
        have hget_bs : (st.arrs 2)[i]'hi_arr2 = (bitSetList (X ⟨j, hj⟩))[i]'hlen_bs :=
          getElem_of_eq harr2_st rfl rfl
        rw [hget_bs]
        exact getElem_bitSetList_le_one (X ⟨j, hj⟩) i hlen_bs
      have hval_w : (st.arrs 2)[i]'hi_arr2 < 2 ^ w := by omega
      have hidx_eval :
          (Expr.op .add (.reg 8) (.reg 5)).eval w st = some (j * n + i) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_st, hr5_st, hjn_w, hi_w, hadd_w]
      have hval_eval :
          (Expr.read 2 (.reg 5)).eval w st = some ((st.arrs 2)[i]'hi_arr2) := by
        simp [Expr.eval, checkWord, hr5_st, hi_w, hi_arr2, hval_w]
      have hbound_out : j * n + i < (st.arrs outArr).length := by
        rw [hout_len_st]
        have : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
        omega
      let st' := st.writeArr outArr (j * n + i) ((st.arrs 2)[i]'hi_arr2)
      have hex_w :
          Exec w (.write outArr (.op .add (.reg 8) (.reg 5)) (.read 2 (.reg 5))) st st' 6 :=
        .write hidx_eval hval_eval hbound_out
      refine ⟨st', 6, hex_w, le_rfl, ?_, by simp [st', hr5_st]⟩
      refine ⟨by omega, by simp [st', hout_len_st],
        by simpa [st', State.writeArr_arrs_ne _ _ _ (by decide : (2 : Arr) ≠ outArr)] using harr2_st,
        fun idx hidx_pn => ?_,
        by simp [st', hr1_st],
        State.setReg_regs_self st' 5 (i + 1),
        by simp [st', hr8_st],
        fun a ha => by
          rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]
          exact harrs a ha,
        fun r hr => by
          rw [State.setReg_regs_ne _ _ hr, State.writeArr_regs]
          exact hregs r hr⟩
      simp only [st', State.setReg_arrs, State.writeArr_arrs_self]
      by_cases h_eq : idx = j * n + i
      · subst h_eq
        rw [List.getElem_set_self]
        have hlt_succ : j * n + i < j * n + (i + 1) := by omega
        have hnot_lt : ¬ j * n + i < j * n := by omega
        simp [hlt_succ, hnot_lt, harr2_st]
      · rw [List.getElem_set_ne (Ne.symm h_eq)]
        rw [hout_get idx hidx_pn]
        by_cases hlt1 : idx < j * n + i
        · have hlt2 : idx < j * n + (i + 1) := by omega
          simp [hlt1, hlt2]
        · have hnot2 : ¬ idx < j * n + (i + 1) := by omega
          simp [hlt1, hnot2]
  have hInv0 : Inv 0 s₀ := by
    refine ⟨Nat.zero_le n, hout_len, harr2, fun idx hidx_pn => ?_, hr1, by simp [s₀], hr8,
      fun _ _ => rfl, fun r hr => by simp [s₀, State.setReg_regs_ne _ _ hr]⟩
    simp only [s₀, State.setReg_arrs, hout, Nat.add_zero]
    by_cases hlt : idx < j * n
    · simp only [hlt, ↓reduceDIte]
      exact List.getElem_append_left (by rw [hpre_len]; exact hlt)
    · simp only [hlt, ↓reduceDIte]
      rw [List.getElem_append_right (by rw [hpre_len]; omega)]
      simp
  rcases hLoop s₀ hInv0 with
    ⟨s₁, t₁, hex₁, ht₁, _, hout_len₁, _, hout_get₁, hr1_1, _, hr8_1, harrs₁, hregs₁⟩
  dsimp only at ht₁
  let s₂ := s₁.setReg 8 ((j + 1) * n)
  have hex₂ : Exec w (.assign 8 (.op .add (.reg 8) (.reg 1))) s₁ s₂ 4 :=
    .assign (by
      have hadd : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_1, hr1_1,
        hjn_w, hn_w, hadd, hjp1n_w])
  have hout_eq1 :
      s₁.arrs outArr = encBitSetsUpTo X (j + 1) ++ List.replicate ((p - (j + 1)) * n) 0 := by
    have hnext_len : (encBitSetsUpTo X (j + 1)).length = (j + 1) * n :=
      length_encBitSetsUpTo X (j + 1) hj
    have hrhs_len :
        (encBitSetsUpTo X (j + 1) ++ List.replicate ((p - (j + 1)) * n) 0).length = p * n := by
      rw [List.length_append, hnext_len, List.length_replicate,
        ← Nat.add_mul, Nat.add_sub_of_le hj]
    refine List.ext_getElem (hout_len₁.trans hrhs_len.symm) (fun idx h1 h2 => ?_)
    have hidx_pn : idx < p * n := by rw [← hrhs_len]; exact h2
    rw [hout_get₁ idx hidx_pn]
    have hjp1_eq : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
    by_cases hlt_jp1 : idx < j * n + n
    · simp only [hlt_jp1, ↓reduceDIte]
      have hlt_next : idx < (encBitSetsUpTo X (j + 1)).length := by
        rw [hnext_len, ← hjp1_eq]; exact hlt_jp1
      rw [List.getElem_append_left hlt_next]
      simp only [encBitSetsUpTo, hj, ↓reduceDIte]
      by_cases hlt_j : idx < j * n
      · simp only [hlt_j, ↓reduceDIte]
        exact (List.getElem_append_left (by rw [hpre_len]; exact hlt_j)).symm
      · simp only [hlt_j, ↓reduceDIte]
        rw [List.getElem_append_right (by rw [hpre_len]; omega)]
        simp [hpre_len]
    · simp only [hlt_jp1, ↓reduceDIte]
      rw [List.getElem_append_right (by rw [hnext_len, ← hjp1_eq]; omega)]
      simp
  refine ⟨s₂, (2 + t₁) + 4, .seq (.seq hex₀ hex₁) hex₂, by omega,
    hout_eq1, by simp [s₂], harrs₁,
    fun r hr5 hr8 => by
      simp [s₂, State.setReg_regs_ne _ _ hr8, hregs₁ r hr5]⟩

end Alg91

end GraphMinor.Compute
