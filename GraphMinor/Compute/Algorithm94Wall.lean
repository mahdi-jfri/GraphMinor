module

public import GraphMinor.Compute.Algorithm94Aux
public import GraphMinor.Compute.Algorithm91Parse

/-!
# Word RAM Wall-Union Construction and `WallOfHeight` Unpacking for GM XIII Section 9

This file provides the Word RAM subroutines for `WallOfHeight` and `MultiDigraph` shared by
`Algorithm94.lean`, `Algorithm97.lean`, and `Algorithm99.lean`:
1. `applySuccPairs`, `pairsFrom`, `IsWallSuccArrs`, and `isWallUnionEdgeExpr`: $O_h(1)$-time pure
   `Expr` testing whether a directed edge `(u, v)` belongs to `(G \ X) ∪ W` using per-subdivision-path
   successor arrays.
2. `buildWallUnionMultiDigraphProg` and `buildWallUnionCsrProg`: constructs both
   `(WallOfHeight.wallUnionMultiDigraph G X W).enc` and the CSR adjacency representation of
   `(WallOfHeight.wallUnionMultiDigraph G X W).toSimpleGraph` in $O_h(n + m')$ steps.
3. `parseFixedWallProg`, `unpackSubwallAtProg`, `skipLenPrefixedListsGenProg`, and
   `skipWallsGenProg`: linear-time Word RAM parsers and cursor-advancing primitives for
   `WallOfHeight.encList` and `encHPaths`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

/-! ### Section 1: Subdivision-Path Successor Arrays and `isWallUnionEdgeExpr` -/

/-- Apply a list of directed vertex pairs `(u, v)` to an array `arr`, setting `arr[u.1] := v.1 + 1`
for each `(u, v)` in order. -/
def applySuccPairs {n : ℕ} : List (Fin n × Fin n) → List ℕ → List ℕ
  | [], arr => arr
  | (u, v) :: rest, arr => applySuccPairs rest (arr.set u.1 (v.1 + 1))

@[simp]
theorem length_applySuccPairs {n : ℕ} :
    ∀ (pairs : List (Fin n × Fin n)) (arr : List ℕ),
      (applySuccPairs pairs arr).length = arr.length
  | [], arr => rfl
  | (u, v) :: rest, arr => by
    rw [applySuccPairs, length_applySuccPairs rest, List.length_set]

theorem applySuccPairs_append {n : ℕ} :
    ∀ (p₁ p₂ : List (Fin n × Fin n)) (arr : List ℕ),
      applySuccPairs (p₁ ++ p₂) arr = applySuccPairs p₂ (applySuccPairs p₁ arr)
  | [], _, _ => rfl
  | (u, v) :: rest, p₂, arr => by
    simp [applySuccPairs, applySuccPairs_append rest p₂]

theorem all_lt_applySuccPairs {n B : ℕ} (hn : n + 1 < B) :
    ∀ (pairs : List (Fin n × Fin n)) (arr : List ℕ),
      (∀ x ∈ arr, x < B) →
      ∀ x ∈ applySuccPairs pairs arr, x < B
  | [], arr, harr, x, hx => harr x hx
  | (u, v) :: rest, arr, harr, x, hx => by
    apply all_lt_applySuccPairs hn rest (arr.set u.1 (v.1 + 1)) ?_ x hx
    intro y hy
    rcases List.mem_or_eq_of_mem_set hy with hy_arr | rfl
    · exact harr y hy_arr
    · have := v.2; omega

theorem getElem_applySuccPairs_of_not_mem_fst {n : ℕ} :
    ∀ (pairs : List (Fin n × Fin n)) (arr : List ℕ) (u : Fin n)
      (_hu_not : u ∉ pairs.map Prod.fst) (hu_len : u.1 < arr.length),
      (applySuccPairs pairs arr)[u.1]'(by rw [length_applySuccPairs]; exact hu_len) =
        arr[u.1]'hu_len
  | [], _, _, _, _ => rfl
  | (x, y) :: rest, arr, u, hu_not, hu_len => by
    simp only [List.map_cons, List.mem_cons, not_or] at hu_not
    have hne_val : x.1 ≠ u.1 := fun h => hu_not.1 (Fin.ext h.symm)
    have hrec := getElem_applySuccPairs_of_not_mem_fst rest (arr.set x.1 (y.1 + 1)) u
      hu_not.2 (by rw [List.length_set]; exact hu_len)
    simpa [applySuccPairs, List.getElem_set_ne hne_val] using hrec

theorem getElem_applySuccPairs_of_mem {n : ℕ} :
    ∀ (pairs : List (Fin n × Fin n)) (arr : List ℕ)
      (_hnd : (pairs.map Prod.fst).Nodup) (hlen : arr.length = n)
      {u v : Fin n} (_hmem : (u, v) ∈ pairs),
      (applySuccPairs pairs arr)[u.1]'(by rw [length_applySuccPairs, hlen]; exact u.2) = v.1 + 1
  | [], _, _, _, _, _, hmem => by simp at hmem
  | (x, y) :: rest, arr, hnd, hlen, u, v, hmem => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with heq | hmem_rest
    · cases heq
      have hrec := getElem_applySuccPairs_of_not_mem_fst rest (arr.set x.1 (y.1 + 1)) x
        hnd.1 (by rw [List.length_set, hlen]; exact x.2)
      simpa [applySuccPairs] using hrec
    · exact getElem_applySuccPairs_of_mem rest (arr.set x.1 (y.1 + 1)) hnd.2
        (by rw [List.length_set, hlen]) hmem_rest

theorem getElem_applySuccPairs_eq_succ_iff {n : ℕ}
    {pairs : List (Fin n × Fin n)} (hnd : (pairs.map Prod.fst).Nodup) (u v : Fin n) :
    (applySuccPairs pairs (List.replicate n 0))[u.1]'(by
      rw [length_applySuccPairs, List.length_replicate]; exact u.2) = v.1 + 1 ↔
      (u, v) ∈ pairs := by
  constructor
  · intro heq
    by_cases hmem_fst : u ∈ pairs.map Prod.fst
    · rcases List.mem_map.mp hmem_fst with ⟨⟨u', v'⟩, hp_mem, hu'⟩
      dsimp at hu'
      subst hu'
      have hv' := getElem_applySuccPairs_of_mem pairs (List.replicate n 0) hnd
        List.length_replicate hp_mem
      have hvv' : v = v' := Fin.ext (by omega)
      subst hvv'
      exact hp_mem
    · have hzero := getElem_applySuccPairs_of_not_mem_fst pairs (List.replicate n 0) u
        hmem_fst (by rw [List.length_replicate]; exact u.2)
      rw [List.getElem_replicate] at hzero
      omega
  · intro hmem
    exact getElem_applySuccPairs_of_mem pairs (List.replicate n 0) hnd
      List.length_replicate hmem

/-- Consecutive pairs `(prev, x_0), (x_0, x_1), ...` starting from `prev`. -/
def pairsFrom {α : Type*} : α → List α → List (α × α)
  | _, [] => []
  | prev, x :: xs => (prev, x) :: pairsFrom x xs

theorem pairsFrom_eq_zip_drop_one {α : Type*} :
    ∀ (prev : α) (l : List α),
      pairsFrom prev l = (prev :: l).zip ((prev :: l).drop 1)
  | _, [] => rfl
  | prev, x :: xs => by
    simp [pairsFrom, pairsFrom_eq_zip_drop_one x xs]

theorem pairsFrom_append {α : Type*} :
    ∀ (prev : α) (l₁ l₂ : List α) (h : prev :: l₁ ≠ []),
      pairsFrom prev (l₁ ++ l₂) =
        pairsFrom prev l₁ ++ pairsFrom ((prev :: l₁).getLast h) l₂
  | prev, [], l₂, _ => by simp [pairsFrom]
  | prev, x :: xs, l₂, _ => by
    simp [pairsFrom, pairsFrom_append x xs l₂ (List.cons_ne_nil x xs)]

theorem mem_of_mem_map_fst_zip_drop_one {α : Type*} :
    ∀ {L : List α} {x : α}, x ∈ (L.zip (L.drop 1)).map Prod.fst → x ∈ L
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: rest, x, h => by
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.map_cons,
      List.mem_cons] at h
    rcases h with rfl | hrest
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_of_mem_map_fst_zip_drop_one hrest)

theorem nodup_map_fst_zip_drop_one {α : Type*} :
    ∀ {L : List α}, L.Nodup → ((L.zip (L.drop 1)).map Prod.fst).Nodup
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: rest, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.map_cons,
      List.nodup_cons]
    exact ⟨fun ha => hnd.1 (mem_of_mem_map_fst_zip_drop_one ha),
      nodup_map_fst_zip_drop_one hnd.2⟩

/-- State predicate asserting that for each `k : Fin (elemWallEdges h).length`, array
`baseSuccArr + k.1` holds the successor array of `W.subdivPathVerts k`. -/
def IsWallSuccArrs {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (baseSuccArr : ℕ) (s : State) : Prop :=
  ∀ k : Fin (elemWallEdges h).length,
    s.arrs (baseSuccArr + k.1) =
      applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
        (List.replicate n 0)

theorem IsWallSuccArrs.of_arrs_eq {h n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    {baseSuccArr : ℕ} {s s' : State} (hsucc : IsWallSuccArrs W baseSuccArr s)
    (heq : ∀ k : Fin (elemWallEdges h).length,
      s'.arrs (baseSuccArr + k.1) = s.arrs (baseSuccArr + k.1)) :
    IsWallSuccArrs W baseSuccArr s' :=
  fun k => (heq k).trans (hsucc k)

/-- Pure `0/1` boolean OR expression on Word RAM expressions returning `0` or `1`. -/
def or01Expr (e₁ e₂ : Expr) : Expr :=
  .op .lt (.const 0) (.op .add e₁ e₂)

theorem or01Expr_eval {w : ℕ} {s : State} {e₁ e₂ : Expr} {P Q : Prop}
    [Decidable P] [Decidable Q] (hw2 : 2 < 2 ^ w)
    (h1 : e₁.eval w s = some (if P then 1 else 0))
    (h2 : e₂.eval w s = some (if Q then 1 else 0)) :
    (or01Expr e₁ e₂).eval w s = some (if P ∨ Q then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  unfold or01Expr
  by_cases hP : P <;> by_cases hQ : Q <;>
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h1, h2, hP, hQ, h0_w, hw1, hw2]

/-- Pure `Expr` testing whether `(r_u, r_v)` or `(r_v, r_u)` is a consecutive edge in the
successor array `a_succ`. -/
def isWallEdgeOnEdgeExpr (a_succ : Arr) (r_u r_v : Reg) : Expr :=
  or01Expr
    (.op .eq (.read a_succ (.reg r_u)) (.op .add (.reg r_v) (.const 1)))
    (.op .eq (.read a_succ (.reg r_v)) (.op .add (.reg r_u) (.const 1)))

theorem isWallEdgeOnEdgeExpr_eval {w h n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    (hW : W.IsValid) {baseSuccArr : ℕ} {s : State}
    (hsucc : IsWallSuccArrs W baseSuccArr s)
    (k : Fin (elemWallEdges h).length) (r_u r_v : Reg) (u v : Fin n)
    (hw2 : 2 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hru : s.regs r_u = u.1) (hrv : s.regs r_v = v.1) :
    (isWallEdgeOnEdgeExpr (baseSuccArr + k.1) r_u r_v).eval w s =
      some (if (u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) ∨
               (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := by have := u.2; omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  have hu1_w : u.1 + 1 < 2 ^ w := by have := u.2; omega
  have hv1_w : v.1 + 1 < 2 ^ w := by have := v.2; omega
  have hk_arr := hsucc k
  have hnd : (((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1)).map Prod.fst).Nodup :=
    nodup_map_fst_zip_drop_one (hW.2.1 k).1
  have hlen_arr : (s.arrs (baseSuccArr + k.1)).length = n := by
    rw [hk_arr, length_applySuccPairs, List.length_replicate]
  have hu_len : u.1 < (s.arrs (baseSuccArr + k.1)).length := by rw [hlen_arr]; exact u.2
  have hv_len : v.1 < (s.arrs (baseSuccArr + k.1)).length := by rw [hlen_arr]; exact v.2
  have hall_w : ∀ x ∈ s.arrs (baseSuccArr + k.1), x < 2 ^ w := by
    rw [hk_arr]
    exact all_lt_applySuccPairs hn1_w _ _ (fun x hx => by
      rcases List.mem_replicate.mp hx with ⟨_, rfl⟩; omega)
  have hval_u_w : (s.arrs (baseSuccArr + k.1))[u.1]'hu_len < 2 ^ w :=
    hall_w _ (List.getElem_mem hu_len)
  have hval_v_w : (s.arrs (baseSuccArr + k.1))[v.1]'hv_len < 2 ^ w :=
    hall_w _ (List.getElem_mem hv_len)
  have hiff_uv :
      (s.arrs (baseSuccArr + k.1))[u.1]'hu_len = v.1 + 1 ↔
        (u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) := by
    have hget :
        (s.arrs (baseSuccArr + k.1))[u.1]'hu_len =
          (applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
            (List.replicate n 0))[u.1]'(by rw [length_applySuccPairs, List.length_replicate]; exact u.2) := by
      congr 1
    rw [hget]
    exact getElem_applySuccPairs_eq_succ_iff hnd u v
  have hiff_vu :
      (s.arrs (baseSuccArr + k.1))[v.1]'hv_len = u.1 + 1 ↔
        (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) := by
    have hget :
        (s.arrs (baseSuccArr + k.1))[v.1]'hv_len =
          (applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
            (List.replicate n 0))[v.1]'(by rw [length_applySuccPairs, List.length_replicate]; exact v.2) := by
      congr 1
    rw [hget]
    exact getElem_applySuccPairs_eq_succ_iff hnd v u
  have he1 :
      (Expr.op .eq (.read (baseSuccArr + k.1) (.reg r_u)) (.op .add (.reg r_v) (.const 1))).eval w s =
        some (if (u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) then 1 else 0) := by
    by_cases huv : (u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1)
    · have heq := hiff_uv.mpr huv
      simp only [huv, ↓reduceIte]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrv, hu_w, hv_w, hw1, hv1_w,
        hu_len, heq]
    · have hne : (s.arrs (baseSuccArr + k.1))[u.1]'hu_len ≠ v.1 + 1 :=
        fun h => huv (hiff_uv.mp h)
      simp only [huv, ↓reduceIte]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrv, hu_w, hv_w, hw1, hv1_w,
        hu_len, hval_u_w, hne, h0_w]
  have he2 :
      (Expr.op .eq (.read (baseSuccArr + k.1) (.reg r_v)) (.op .add (.reg r_u) (.const 1))).eval w s =
        some (if (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) then 1 else 0) := by
    by_cases hvu : (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1)
    · have heq := hiff_vu.mpr hvu
      simp only [hvu, ↓reduceIte]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrv, hu_w, hv_w, hw1, hu1_w,
        hv_len, heq]
    · have hne : (s.arrs (baseSuccArr + k.1))[v.1]'hv_len ≠ u.1 + 1 :=
        fun h => hvu (hiff_vu.mp h)
      simp only [hvu, ↓reduceIte]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrv, hu_w, hv_w, hw1, hu1_w,
        hv_len, hval_v_w, hne, h0_w]
  exact or01Expr_eval hw2 he1 he2

/-- Pure `Expr` testing whether `(r_u, r_v)` lies on any of the first `j` subdivision paths of `W`. -/
def isWallEdgeUpToExpr (baseSuccArr : ℕ) (r_u r_v : Reg) : ℕ → Expr
  | 0 => .const 0
  | j + 1 =>
    or01Expr (isWallEdgeUpToExpr baseSuccArr r_u r_v j)
      (isWallEdgeOnEdgeExpr (baseSuccArr + j) r_u r_v)

theorem isWallEdgeUpToExpr_eval {w h n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    (hW : W.IsValid) {baseSuccArr : ℕ} {s : State}
    (hsucc : IsWallSuccArrs W baseSuccArr s)
    (r_u r_v : Reg) (u v : Fin n)
    (hw2 : 2 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hru : s.regs r_u = u.1) (hrv : s.regs r_v = v.1) :
    ∀ j (_hj : j ≤ (elemWallEdges h).length),
      (isWallEdgeUpToExpr baseSuccArr r_u r_v j).eval w s =
        some (if ∃ k : Fin (elemWallEdges h).length, k.1 < j ∧
          ((u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) ∨
           (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1)) then 1 else 0)
  | 0, _ => by
    have h0_w : 0 < 2 ^ w := by omega
    simp [isWallEdgeUpToExpr, checkWord, h0_w]
  | j + 1, hj => by
    have hj_lt : j < (elemWallEdges h).length := by omega
    have hprev := isWallEdgeUpToExpr_eval hW hsucc r_u r_v u v hw2 hn1_w hru hrv j (by omega)
    have hstep := isWallEdgeOnEdgeExpr_eval hW hsucc ⟨j, hj_lt⟩ r_u r_v u v hw2 hn1_w hru hrv
    have hor := or01Expr_eval hw2 hprev hstep
    have hiff :
        ((∃ k : Fin (elemWallEdges h).length, k.1 < j ∧
            ((u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) ∨
             (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))) ∨
         ((u, v) ∈ (W.subdivPathVerts ⟨j, hj_lt⟩).zip ((W.subdivPathVerts ⟨j, hj_lt⟩).drop 1) ∨
          (v, u) ∈ (W.subdivPathVerts ⟨j, hj_lt⟩).zip ((W.subdivPathVerts ⟨j, hj_lt⟩).drop 1))) ↔
        (∃ k : Fin (elemWallEdges h).length, k.1 < j + 1 ∧
          ((u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) ∨
           (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))) := by
      constructor
      · rintro (⟨k, hk, hmem⟩ | hmem)
        · exact ⟨k, by omega, hmem⟩
        · exact ⟨⟨j, hj_lt⟩, by simp, hmem⟩
      · rintro ⟨k, hk, hmem⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
        · exact Or.inl ⟨k, hk_lt, hmem⟩
        · have hk_fin : k = ⟨j, hj_lt⟩ := Fin.ext hk_eq
          subst hk_fin
          exact Or.inr hmem
    rw [isWallEdgeUpToExpr, hor, if_congr hiff rfl rfl]

/-- Pure `Expr` testing `(u ∉ X ∧ v ∉ X) ∨ W.IsWallEdge u v` for `u` in `r_u` and `v` in `r_v`,
where `a_X` holds `bitSetList X` and `baseSuccArr` holds `IsWallSuccArrs W baseSuccArr`. -/
def isWallUnionEdgeExpr (h baseSuccArr : ℕ) (a_X : Arr) (r_u r_v : Reg) : Expr :=
  or01Expr
    (.op .mul
      (.op .eq (.read a_X (.reg r_u)) (.const 0))
      (.op .eq (.read a_X (.reg r_v)) (.const 0)))
    (isWallEdgeUpToExpr baseSuccArr r_u r_v (elemWallEdges h).length)

theorem isWallUnionEdgeExpr_eval {w h n : ℕ} {G : MultiDigraph n} {W : WallOfHeight h G}
    (hW : W.IsValid) {X : Finset (Fin n)} {baseSuccArr : ℕ} {a_X : Arr} {s : State}
    (hX : IsBitSet X a_X s) (hsucc : IsWallSuccArrs W baseSuccArr s)
    (r_u r_v : Reg) (u v : Fin n)
    (hw2 : 2 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hru : s.regs r_u = u.1) (hrv : s.regs r_v = v.1) :
    (isWallUnionEdgeExpr h baseSuccArr a_X r_u r_v).eval w s =
      some (if (u ∉ X ∧ v ∉ X) ∨ W.IsWallEdge u v then 1 else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := by have := u.2; omega
  have hv_w : v.1 < 2 ^ w := by have := v.2; omega
  have hu_len : u.1 < (s.arrs a_X).length := by rw [hX.1]; exact u.2
  have hv_len : v.1 < (s.arrs a_X).length := by rw [hX.1]; exact v.2
  have hX_u :
      (Expr.op .eq (.read a_X (.reg r_u)) (.const 0)).eval w s =
        some (if u ∉ X then 1 else 0) := by
    have hget := hX.getElem_eq_ite u
    by_cases hu : u ∈ X <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hu_w, hu_len, hget, hu, hw1, h0_w]
  have hX_v :
      (Expr.op .eq (.read a_X (.reg r_v)) (.const 0)).eval w s =
        some (if v ∉ X then 1 else 0) := by
    have hget := hX.getElem_eq_ite v
    by_cases hv : v ∈ X <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hv_w, hv_len, hget, hv, hw1, h0_w]
  have hmul :
      (Expr.op .mul
        (.op .eq (.read a_X (.reg r_u)) (.const 0))
        (.op .eq (.read a_X (.reg r_v)) (.const 0))).eval w s =
        some (if u ∉ X ∧ v ∉ X then 1 else 0) := by
    have hop :
        BinOp.eval w .mul (if u ∉ X then 1 else 0) (if v ∉ X then 1 else 0) =
          some (if u ∉ X ∧ v ∉ X then 1 else 0) := by
      by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;>
        simp [BinOp.eval, BinOp.raw, checkWord, hu, hv, hw1, h0_w]
    exact eval_op_some hX_u hX_v hop
  have hwe := isWallEdgeUpToExpr_eval hW hsucc r_u r_v u v hw2 hn1_w hru hrv
    (elemWallEdges h).length le_rfl
  have hwe_iff :
      (∃ k : Fin (elemWallEdges h).length, k.1 < (elemWallEdges h).length ∧
        ((u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) ∨
         (v, u) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))) ↔
      W.IsWallEdge u v := by
    unfold WallOfHeight.IsWallEdge
    exact ⟨fun ⟨k, _, h⟩ => ⟨k, h⟩, fun ⟨k, h⟩ => ⟨k, k.2, h⟩⟩
  have hwe' :
      (isWallEdgeUpToExpr baseSuccArr r_u r_v (elemWallEdges h).length).eval w s =
        some (if W.IsWallEdge u v then 1 else 0) := by
    rw [hwe, if_congr hwe_iff rfl rfl]
  exact or01Expr_eval hw2 hmul hwe'

/-! ### Section 2: Constructing `(WallOfHeight.wallUnionMultiDigraph G X W).enc` and CSR -/

/-- Filtered triple list for `WallOfHeight.wallUnionMultiDigraph G X W` on a suffix of
`G.activePairsList`. -/
noncomputable def wallUnionTriplesAux {h n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (W : WallOfHeight h G) : List (Fin n × Fin n) → List ℕ
  | [] => []
  | (u, v) :: ps =>
    if (u ∉ X ∧ v ∉ X) ∨ W.IsWallEdge u v then
      u.1 :: v.1 :: G.edgeMult u v :: wallUnionTriplesAux G X W ps
    else
      wallUnionTriplesAux G X W ps

theorem activePairsList_wallUnionMultiDigraph {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) :
    (WallOfHeight.wallUnionMultiDigraph G X W).activePairsList =
      G.activePairsList.filter (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2)) := by
  unfold MultiDigraph.activePairsList
  rw [List.filter_filter]
  refine List.filter_congr fun p _ => ?_
  simp only [WallOfHeight.wallUnionMultiDigraph_edgeMult]
  by_cases hcond : (p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2
  · simp [hcond]
  · simp [hcond]

theorem numActivePairs_wallUnionMultiDigraph {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) :
    (WallOfHeight.wallUnionMultiDigraph G X W).numActivePairs =
      (G.activePairsList.filter
        (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2))).length := by
  unfold MultiDigraph.numActivePairs
  rw [activePairsList_wallUnionMultiDigraph]

theorem numActivePairs_wallUnionMultiDigraph_le {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) :
    (WallOfHeight.wallUnionMultiDigraph G X W).numActivePairs ≤ G.numActivePairs := by
  rw [numActivePairs_wallUnionMultiDigraph]
  exact List.length_filter_le _ _

theorem wallUnionTriplesAux_eq_flatTriples {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) :
    ∀ (ps : List (Fin n × Fin n)),
      wallUnionTriplesAux G X W ps =
        (WallOfHeight.wallUnionMultiDigraph G X W).flatTriples
          (ps.filter (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2)))
  | [] => rfl
  | (u, v) :: ps => by
    by_cases hcond : (u ∉ X ∧ v ∉ X) ∨ W.IsWallEdge u v
    · simp [wallUnionTriplesAux, MultiDigraph.flatTriples,
        WallOfHeight.wallUnionMultiDigraph_edgeMult, hcond,
        wallUnionTriplesAux_eq_flatTriples G X W ps]
    · simp [wallUnionTriplesAux, hcond, wallUnionTriplesAux_eq_flatTriples G X W ps]

theorem enc_wallUnionMultiDigraph_eq {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) :
    (WallOfHeight.wallUnionMultiDigraph G X W).enc =
      [n, (WallOfHeight.wallUnionMultiDigraph G X W).numActivePairs] ++
        wallUnionTriplesAux G X W G.activePairsList := by
  unfold MultiDigraph.enc
  rw [wallUnionTriplesAux_eq_flatTriples, ← activePairsList_wallUnionMultiDigraph]

/-- Loop body for `buildWallUnionMultiDigraphProg`:
Register layout starting at `r_base`:
- `r_base`: `n`
- `r_base + 1`: `m_union` (active pairs of `(G \ X) ∪ W` emitted so far)
- `r_base + 2`: `m'` (`G.numActivePairs`)
- `r_base + 3`: loop counter `k` (`0 .. m'`)
- `r_base + 4`: buffer write position `pos` (starts at `2`)
- `r_base + 5`: triple offset `idx = 2 + 3 * k`
- `r_base + 6`: `u`
- `r_base + 7`: `v`
- `r_base + 8`: `mult = G.edgeMult u v` -/
def buildWallUnionMultiDigraphBody (h baseSuccArr : ℕ) (a_src a_X a_buf : Arr)
    (r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r_base + 3) (r_base + 5) (r_base + 6) (r_base + 7))
    (.ite (isWallUnionEdgeExpr h baseSuccArr a_X (r_base + 6) (r_base + 7))
      (.seq (.assign (r_base + 8) (.read a_src (.op .add (.reg (r_base + 5)) (.const 2))))
        (.seq (bufPush3 a_buf (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
          (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
      .skip)

/-- Word RAM program that reads `G.enc` from `a_src`, `IsBitSet X a_X`, and
`IsWallSuccArrs W baseSuccArr`, and writes `(WallOfHeight.wallUnionMultiDigraph G X W).enc` into
`a_dst` (using scratch buffer `a_buf` and scratch registers `r_base .. r_base + 8`). -/
def buildWallUnionMultiDigraphProg (h baseSuccArr : ℕ) (a_src a_X a_buf a_dst : Arr)
    (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_src (.const 0)))
    (.seq (.assign (r_base + 2) (.read a_src (.const 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 4) (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 2)))))
          (.seq (.alloc a_buf (.reg (r_base + 4)))
            (.seq (.write a_buf (.const 0) (.reg r_base))
              (.seq (.assign (r_base + 4) (.const 2))
                (.seq (.assign (r_base + 3) (.const 0))
                  (.seq (forUp (r_base + 3) (.reg (r_base + 2))
                          (buildWallUnionMultiDigraphBody h baseSuccArr a_src a_X a_buf r_base))
                    (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                      (readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 4)) (r_base + 5)))))))))))

theorem buildWallUnionMultiDigraphLoop_exec {w h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) (hW : W.IsValid) (extra : List ℕ)
    (baseSuccArr : ℕ) (a_src a_X a_buf : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_xb : a_X ≠ a_buf)
    (hsucc_ne : ∀ k : Fin (elemWallEdges h).length, baseSuccArr + k.1 ≠ a_buf)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (he_w : G.numEdges < 2 ^ w)
    (suff : List (Fin n × Fin n)) :
    let exprCost := (isWallUnionEdgeExpr h baseSuccArr a_X (r_base + 6) (r_base + 7)).cost
    ∀ (pref : List (Fin n × Fin n)),
      G.activePairsList = pref ++ suff →
      ∀ (pfx : List ℕ) (extra_buf m_acc : ℕ),
        pfx.length = 2 + 3 * m_acc →
        m_acc + (suff.filter
          (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2))).length ≤
          G.numActivePairs →
        ∀ {s : State},
          s.arrs a_src = G.enc ++ extra →
          IsBitSet X a_X s →
          IsWallSuccArrs W baseSuccArr s →
          s.arrs a_buf = pfx ++ List.replicate (3 * suff.length + extra_buf) 0 →
          s.regs r_base = n →
          s.regs (r_base + 1) = m_acc →
          s.regs (r_base + 2) = G.numActivePairs →
          s.regs (r_base + 3) = pref.length →
          s.regs (r_base + 4) = pfx.length →
          ∃ s' t extra_buf',
            Exec w (forUp (r_base + 3) (.reg (r_base + 2))
              (buildWallUnionMultiDigraphBody h baseSuccArr a_src a_X a_buf r_base)) s s' t ∧
            t ≤ 3 + (56 + exprCost) * suff.length ∧
            s'.arrs a_buf = pfx ++ wallUnionTriplesAux G X W suff ++ List.replicate extra_buf' 0 ∧
            s'.regs r_base = n ∧
            s'.regs (r_base + 1) =
              m_acc + (suff.filter
                (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2))).length ∧
            s'.regs (r_base + 4) = (pfx ++ wallUnionTriplesAux G X W suff).length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r : ℕ, r < r_base ∨ r_base + 8 < r → s'.regs r = s.regs r) := by
  intro exprCost
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff with
  | nil =>
    intro pref hsplit pfx extra_buf m_acc hpfx_len hm_bound
      s hsrc hX hsucc hbuf hr0 hr1 hr2 hr3 hr4
    have hlen_pref : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 2))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr2, hlen_pref, hm'_w]
    refine ⟨s, 3, extra_buf, .while_false hcond, by simp, ?_, hr0, ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa [wallUnionTriplesAux] using hbuf
    · simpa using hr1
    · simpa [wallUnionTriplesAux] using hr4
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    intro pref hsplit pfx extra_buf m_acc hpfx_len hm_bound
      s hsrc hX hsucc hbuf hr0 hr1 hr2 hr3 hr4
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 2))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr2, k, hk_m', hk_w, hm'_w, hw]
    -- 1. readTripleEndpoints a_src (r_base + 3) (r_base + 5) (r_base + 6) (r_base + 7)
    rcases readTripleEndpoints_exec G extra a_src (r_base + 3) (r_base + 5) (r_base + 6) (r_base + 7)
        k s (by omega) (by omega) (by omega)
        hw3 hn_w hm3_w hk_m' hsrc hr3 with
      ⟨s₁, t₁, hex₁, ht₁, hr5_1, hr6_1, hr7_1, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v := congrArg Prod.snd hget_k
    rw [hget_u] at hr6_1
    rw [hget_v] at hr7_1
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    have hX₁ : IsBitSet X a_X s₁ := hX.of_arr_eq (by rw [harr₁])
    have hsucc₁ : IsWallSuccArrs W baseSuccArr s₁ :=
      hsucc.of_arrs_eq (fun idx => by rw [harr₁])
    have heval_cond := isWallUnionEdgeExpr_eval hW hX₁ hsucc₁ (r_base + 6) (r_base + 7) u v
      hw2 hn1_w hr6_1 hr7_1
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    -- 2. Branch on (u ∉ X ∧ v ∉ X) ∨ W.IsWallEdge u v
    by_cases hkeep : (u ∉ X ∧ v ∉ X) ∨ W.IsWallEdge u v
    · have heval1 :
          (isWallUnionEdgeExpr h baseSuccArr a_X (r_base + 6) (r_base + 7)).eval w s₁ = some 1 := by
        simpa [hkeep] using heval_cond
      let m := G.edgeMult u v
      have hm_le : m ≤ G.numEdges := G.edgeMult_le_numEdges u v
      have hm_w : m < 2 ^ w := by omega
      obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G extra hsrc hk_m'
      rw [hget_u, hget_v] at hget_m
      have hidx_w : 2 + 3 * k < 2 ^ w := by omega
      have hidx2_w : 2 + 3 * k + 2 < 2 ^ w := by omega
      have hlen_m₁ : 2 + 3 * k + 2 < (s₁.arrs a_src).length := by rw [harr₁]; exact hlen_m
      have hget_m₁ : (s₁.arrs a_src)[2 + 3 * k + 2]'hlen_m₁ = m := by
        simpa [harr₁, m] using hget_m
      let s₂ := s₁.setReg (r_base + 8) m
      have hex₂ : Exec w (.assign (r_base + 8)
          (.read a_src (.op .add (.reg (r_base + 5)) (.const 2)))) s₁ s₂ 5 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr5_1,
          hidx_w, hw2, hidx2_w, hlen_m₁, hget_m₁, hm_w])
      have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate ((3 * ps.length + extra_buf) + 3) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = (3 * ps.length + extra_buf) + 3 := by
          simp; omega
        rw [← hlen_eq]
        simp [s₂, harr₁, hbuf]
      have hr4_2 : s₂.regs (r_base + 4) = pfx.length := by
        simp only [s₂, State.setReg_regs_ne _ _ (by omega : (r_base + 4 : Reg) ≠ r_base + 8)]
        rw [hreg₁ (r_base + 4) (by omega) (by omega) (by omega)]
        exact hr4
      have hr6_2 : s₂.regs (r_base + 6) = u.1 := by
        simp [s₂, hr6_1]
      have hr7_2 : s₂.regs (r_base + 7) = v.1 := by
        simp [s₂, hr7_1]
      have hr8_2 : s₂.regs (r_base + 8) = m := by simp [s₂]
      have hflt_uv :
          (List.filter (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2))
            ((u, v) :: ps)).length =
          (List.filter (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2)) ps).length + 1 := by
        simp [hkeep]
      have hm_acc_lt : m_acc + 1 ≤ G.numActivePairs := by
        rw [hflt_uv] at hm_bound
        omega
      have hpos_w : pfx.length + 3 < 2 ^ w := by omega
      rcases bufPush3_exec a_buf (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8)
          pfx (3 * ps.length + extra_buf) u.1 v.1 m
          hw3 hpos_w hu_w hv_w hm_w hbuf₂ hr4_2 hr6_2 hr7_2 hr8_2 with
        ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hr4_3, harr₃, hreg₃⟩
      have hr1_3 : s₃.regs (r_base + 1) = m_acc := by
        rw [hreg₃ _ (by omega)]
        simp only [s₂, State.setReg_regs_ne _ _ (by omega : (r_base + 1 : Reg) ≠ r_base + 8)]
        rw [hreg₁ (r_base + 1) (by omega) (by omega) (by omega)]
        exact hr1
      have hm_acc_w : m_acc < 2 ^ w := by omega
      have hm_acc1_w : m_acc + 1 < 2 ^ w := by omega
      let s₄ := s₃.setReg (r_base + 1) (m_acc + 1)
      have hex₄ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₃ s₄ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_3, hm_acc_w, hw, hm_acc1_w])
      have hex_ite : Exec w
          (.ite (isWallUnionEdgeExpr h baseSuccArr a_X (r_base + 6) (r_base + 7))
            (.seq (.assign (r_base + 8) (.read a_src (.op .add (.reg (r_base + 5)) (.const 2))))
              (.seq (bufPush3 a_buf (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
                (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
            .skip)
          s₁ s₄ (exprCost + (5 + (t₃ + 4))) :=
        .ite_true heval1 (by omega) (.seq hex₂ (.seq hex₃ hex₄))
      have hex_body :
          Exec w (buildWallUnionMultiDigraphBody h baseSuccArr a_src a_X a_buf r_base) s s₄
            (t₁ + (exprCost + (5 + (t₃ + 4)))) :=
        .seq hex₁ hex_ite
      have hr3_4 : s₄.regs (r_base + 3) = k := by
        simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 1)]
        rw [hreg₃ _ (by omega)]
        simp only [s₂, State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 8)]
        rw [hreg₁ (r_base + 3) (by omega) (by omega) (by omega)]
        exact hr3
      let s₅ := s₄.setReg (r_base + 3) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
          s₄ s₅ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_4, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hm_bound' :
          (m_acc + 1) + (ps.filter
            (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2))).length ≤
          G.numActivePairs := by
        rw [hflt_uv] at hm_bound
        omega
      have harr_s₅ : ∀ a : ℕ, a ≠ a_buf → s₅.arrs a = s.arrs a := by
        intro a ha
        simp only [s₅, s₄, State.setReg_arrs]
        rw [harr₃ a ha]
        simp [s₂, harr₁]
      rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [u.1, v.1, m]) extra_buf (m_acc + 1)
          (by simp [hpfx_len]; omega) hm_bound' (s := s₅)
          (by rw [harr_s₅ a_src hne_sb, hsrc])
          (hX.of_arr_eq (harr_s₅ a_X hne_xb))
          (hsucc.of_arrs_eq (fun idx => harr_s₅ (baseSuccArr + idx.1) (hsucc_ne idx)))
          (by simpa [s₅, s₄] using hbuf₃)
          (by simp only [s₅, s₄,
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 3),
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 1)];
              rw [hreg₃ _ (by omega)];
              simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₅, s₄])
          (by simp only [s₅, s₄,
              State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 3),
              State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 1)];
              rw [hreg₃ _ (by omega)];
              simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
          (by simp [s₅, k])
          (by simp [s₅, s₄, hr4_3]) with
        ⟨s₆, t₆, extra_buf', hex₆, ht₆, hbuf₆, hr0_6, hr1_6, hr4_6, harr₆, hreg₆⟩
      have haux_uv :
          wallUnionTriplesAux G X W ((u, v) :: ps) =
            u.1 :: v.1 :: m :: wallUnionTriplesAux G X W ps := by
        simp [wallUnionTriplesAux, hkeep, m]
      refine ⟨s₆, 3 + ((t₁ + (exprCost + (5 + (t₃ + 4)))) + 4) + t₆, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₆,
        by simp only [List.length_cons, Nat.mul_succ]; omega,
        by rw [haux_uv]; simpa [List.append_assoc] using hbuf₆,
        hr0_6,
        by rw [hflt_uv]; omega,
        by rw [haux_uv]; simpa [List.append_assoc] using hr4_6,
        fun a ha => (harr₆ a ha).trans (harr_s₅ a ha),
        fun r hr => by
          rw [hreg₆ r hr]
          simp only [s₅, s₄,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1)]
          rw [hreg₃ r (by omega)]
          simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 8),
            hreg₁ r (by omega) (by omega) (by omega)]⟩
    · have heval0 :
          (isWallUnionEdgeExpr h baseSuccArr a_X (r_base + 6) (r_base + 7)).eval w s₁ = some 0 := by
        simpa [hkeep] using heval_cond
      have hex_ite : Exec w
          (.ite (isWallUnionEdgeExpr h baseSuccArr a_X (r_base + 6) (r_base + 7))
            (.seq (.assign (r_base + 8) (.read a_src (.op .add (.reg (r_base + 5)) (.const 2))))
              (.seq (bufPush3 a_buf (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
                (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
            .skip)
          s₁ s₁ (exprCost + 1) :=
        .ite_false heval0 (.skip s₁)
      have hex_body :
          Exec w (buildWallUnionMultiDigraphBody h baseSuccArr a_src a_X a_buf r_base) s s₁
            (t₁ + (exprCost + 1)) :=
        .seq hex₁ hex_ite
      have hr3_1 : s₁.regs (r_base + 3) = k := by
        rw [hreg₁ (r_base + 3) (by omega) (by omega) (by omega)]; exact hr3
      let s₂ := s₁.setReg (r_base + 3) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
          s₁ s₂ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_1, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate (3 * ps.length + (extra_buf + 3)) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = 3 * ps.length + (extra_buf + 3) := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₂, harr₁] using hbuf
      have hm_bound' :
          m_acc + (ps.filter
            (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2))).length ≤
          G.numActivePairs := by
        simpa [hkeep] using hm_bound
      rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 3) m_acc
          hpfx_len hm_bound' (s := s₂)
          (by simp [s₂, harr₁, hsrc])
          (hX.of_arr_eq (by simp [s₂, harr₁]))
          (hsucc.of_arrs_eq (fun idx => by simp [s₂, harr₁]))
          hbuf₂
          (by simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
          (by simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
          (by simp [s₂, k])
          (by simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4]) with
        ⟨s₃, t₃, extra_buf', hex₃, ht₃, hbuf₃, hr0_3, hr1_3, hr4_3, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + ((t₁ + (exprCost + 1)) + 4) + t₃, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by simp only [List.length_cons, Nat.mul_succ]; omega,
        by simpa [wallUnionTriplesAux, hkeep] using hbuf₃,
        hr0_3,
        by simpa [hkeep] using hr1_3,
        by simpa [wallUnionTriplesAux, hkeep] using hr4_3,
        fun a ha => by rw [harr₃ a ha]; simp [s₂, harr₁],
        fun r hr => by
          rw [hreg₃ r hr]
          simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
            hreg₁ r (by omega) (by omega) (by omega)]⟩

/-- Specification of `buildWallUnionMultiDigraphProg`: writes
`(WallOfHeight.wallUnionMultiDigraph G X W).enc` into `a_dst` in $O_h(G.\text{numActivePairs} + 1)$
steps. -/
theorem buildWallUnionMultiDigraphProg_exec {w h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) (hW : W.IsValid) (extra : List ℕ)
    (baseSuccArr : ℕ) (a_src a_X a_buf a_dst : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_xb : a_X ≠ a_buf) (hne_bd : a_buf ≠ a_dst)
    (hsucc_ne : ∀ k : Fin (elemWallEdges h).length, baseSuccArr + k.1 ≠ a_buf)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (he_w : G.numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra)
    (hX : IsBitSet X a_X s)
    (hsucc : IsWallSuccArrs W baseSuccArr s) :
    let G' := WallOfHeight.wallUnionMultiDigraph G X W
    let exprCost := (isWallUnionEdgeExpr h baseSuccArr a_X (r_base + 6) (r_base + 7)).cost
    ∃ s' t,
      Exec w (buildWallUnionMultiDigraphProg h baseSuccArr a_src a_X a_buf a_dst r_base) s s' t ∧
      t ≤ 80 + (107 + exprCost) * G.numActivePairs ∧
      s'.arrs a_dst = G'.enc ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = G'.numActivePairs ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base ∨ r_base + 8 < r → s'.regs r = s.regs r) := by
  intro G' exprCost
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * G.numActivePairs < 2 ^ w := by omega
  -- 1. r_base := a_src[0]
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G extra hsrc
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_src (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  -- 2. r_base + 2 := a_src[1]
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G extra hsrc
  let s₂ := s₁.setReg (r_base + 2) G.numActivePairs
  have hex₂ : Exec w (.assign (r_base + 2) (.read a_src (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. r_base + 4 := 2 + 3 * (r_base + 2)
  let s₄ := s₃.setReg (r_base + 4) (2 + 3 * G.numActivePairs)
  have hex₄ : Exec w (.assign (r_base + 4)
      (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 2))))) s₃ s₄ 6 :=
    .assign (by simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm'_w, h3m'_w, hm3_w])
  -- 5. alloc a_buf (r_base + 4)
  let s₅ := s₄.setArr a_buf (List.replicate (2 + 3 * G.numActivePairs) 0)
  have hex₅ : Exec w (.alloc a_buf (.reg (r_base + 4))) s₄ s₅ (1 + (2 + 3 * G.numActivePairs)) :=
    .alloc (by simp [s₄, Expr.eval, checkWord, hm3_w])
  -- 6. write a_buf 0 r_base
  let s₆ := s₅.writeArr a_buf 0 n
  have hex₆ : Exec w (.write a_buf (.const 0) (.reg r_base)) s₅ s₆ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hn_w])
      (by simp [s₅])
  -- 7. r_base + 4 := 2
  let s₇ := s₆.setReg (r_base + 4) 2
  have hex₇ : Exec w (.assign (r_base + 4) (.const 2)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  -- 8. r_base + 3 := 0
  let s₈ := s₇.setReg (r_base + 3) 0
  have hex₈ : Exec w (.assign (r_base + 3) (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 9. buildWallUnionMultiDigraphLoop_exec
  have hbuf₈ : s₈.arrs a_buf = [n, 0] ++ List.replicate (3 * G.activePairsList.length + 0) 0 := by
    simp only [s₈, s₇, s₆, s₅, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self]
    have hrep : 2 + 3 * G.numActivePairs = 1 + (1 + 3 * G.activePairsList.length) := by
      simp [MultiDigraph.numActivePairs]; omega
    rw [hrep, List.replicate_add, List.replicate_add]
    rfl
  have hm_bound₈ :
      0 + (G.activePairsList.filter
        (fun p => decide ((p.1 ∉ X ∧ p.2 ∉ X) ∨ W.IsWallEdge p.1 p.2))).length ≤
      G.numActivePairs := by
    simp only [Nat.zero_add, MultiDigraph.numActivePairs]
    exact List.length_filter_le _ _
  have harr_s₈ : ∀ a : ℕ, a ≠ a_buf → s₈.arrs a = s.arrs a := by
    intro a ha
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_buf from ha]
  rcases buildWallUnionMultiDigraphLoop_exec G X W hW extra baseSuccArr a_src a_X a_buf r_base
      hne_sb hne_xb hsucc_ne hw3 hn1_w hm3_w he_w G.activePairsList [] rfl [n, 0] 0 0 rfl hm_bound₈
      (s := s₈)
      (by rw [harr_s₈ a_src hne_sb, hsrc])
      (hX.of_arr_eq (harr_s₈ a_X hne_xb))
      (hsucc.of_arrs_eq (fun idx => harr_s₈ (baseSuccArr + idx.1) (hsucc_ne idx)))
      hbuf₈
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp [s₈])
      (by simp [s₈, s₇]) with
    ⟨s₉, t₉, extra_buf', hex₉, ht₉, hbuf₉, hr0_9, hr1_9, hr4_9, harr₉, hreg₉⟩
  rw [Nat.zero_add, ← numActivePairs_wallUnionMultiDigraph] at hr1_9
  change s₉.regs (r_base + 1) = G'.numActivePairs at hr1_9
  -- 10. write a_buf 1 (r_base + 1)
  have hm'_union_le : G'.numActivePairs ≤ G.numActivePairs :=
    numActivePairs_wallUnionMultiDigraph_le G X W
  have hm'_union_w : G'.numActivePairs < 2 ^ w := by omega
  let s₁₀ := s₉.writeArr a_buf 1 G'.numActivePairs
  have hex₁₀ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₉ s₁₀ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hr1_9, hm'_union_w])
      (by simp [hbuf₉])
  have hbuf₁₀ : s₁₀.arrs a_buf = [] ++ G'.enc ++ List.replicate extra_buf' 0 := by
    simp only [s₁₀, State.writeArr_arrs_self, hbuf₉, G', enc_wallUnionMultiDigraph_eq]
    rfl
  -- 11. readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 4)) (r_base + 5)
  have hlen_enc : G'.enc.length = 2 + 3 * G'.numActivePairs := G'.length_enc
  have hr4_10 : s₁₀.regs (r_base + 4) = G'.enc.length := by
    simpa [s₁₀, G', enc_wallUnionMultiDigraph_eq] using hr4_9
  have henc_w : ∀ x ∈ G'.enc, x < 2 ^ w := by
    have he'_le : G'.numEdges ≤ G.numEdges := WallOfHeight.wallUnionMultiDigraph_numEdges_le G X W
    intro x hx
    unfold MultiDigraph.enc at hx
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx_tr
    · exact hn_w
    · exact hm'_union_w
    · have hall_tr : ∀ (ps : List (Fin n × Fin n)) (y : ℕ),
          y ∈ G'.flatTriples ps → y < 2 ^ w := by
        intro ps
        induction ps with
        | nil => intro y hy; simp [MultiDigraph.flatTriples] at hy
        | cons p ps ih =>
          rcases p with ⟨u, v⟩
          intro y hy
          simp only [MultiDigraph.flatTriples, List.mem_cons] at hy
          rcases hy with rfl | rfl | rfl | hy
          · exact Nat.lt_trans u.2 hn_w
          · exact Nat.lt_trans v.2 hn_w
          · have := G'.edgeMult_le_numEdges u v; omega
          · exact ih y hy
      exact hall_tr G'.activePairsList x hx_tr
  have hoff_len_w : 0 + G'.enc.length < 2 ^ w := by omega
  rcases readSliceProg_exec a_buf a_dst (.const 0) (r_base + 4) (r_base + 5)
      hne_bd (by omega) [] G'.enc (List.replicate extra_buf' 0)
      rfl rfl henc_w hw hoff_len_w
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₁₀ hr4_10 with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hdst₁₁, harr₁₁, _⟩
  have hnot_r11 : ∀ r : ℕ, r < r_base + 5 ∨ r_base + 8 < r →
      (r : Reg) ∉ (readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 4)) (r_base + 5)).writtenRegs := by
    intro r hr
    simp [readSliceProg, readSliceBody, forUp, Cmd.writtenRegs]
    omega
  change t₉ ≤ 3 + (56 + exprCost) * G.numActivePairs at ht₉
  rw [hlen_enc] at ht₁₁
  dsimp only [Expr.cost] at ht₁₁
  have h48_le : 48 * G'.numActivePairs ≤ 48 * G.numActivePairs :=
    Nat.mul_le_mul_left 48 hm'_union_le
  have hmul_eq :
      (56 + exprCost) * G.numActivePairs + 3 * G.numActivePairs + 48 * G.numActivePairs =
        (107 + exprCost) * G.numActivePairs := by ring
  refine ⟨s₁₁, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    by omega,
    hdst₁₁,
    by
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex₁₁ (hnot_r11 r_base (by omega))]
      exact hr0_9,
    by
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex₁₁ (hnot_r11 (r_base + 1) (by omega))]
      exact hr1_9,
    fun a hab had => by
      rw [harr₁₁ a had]
      simp only [s₁₀, State.writeArr_arrs_ne _ _ _ hab]
      exact (harr₉ a hab).trans (harr_s₈ a hab),
    fun r hr => by
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex₁₁ (hnot_r11 r (by omega))]
      simp only [s₁₀, State.writeArr_regs]
      rw [hreg₉ r hr]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]⟩

/-- Combined program for Step (2) of Algorithm (9.4) and Step (1) of Algorithm (9.7):
reads `G.enc` from `arr 9`, `IsBitSet X 16`, and `IsWallSuccArrs W baseSuccArr`, writes
`(WallOfHeight.wallUnionMultiDigraph G X W).enc` to `arr 23`, and builds its CSR representation in
`(20, 21, 22)` using scratch arrays `inArr (0), 34, 35` and scratch registers `3..12`. -/
def buildWallUnionCsrProg (h baseSuccArr : ℕ) : Cmd :=
  .seq (buildWallUnionMultiDigraphProg h baseSuccArr 9 16 34 23 3)
    (toSimpleGraphProg 23 34 35 20 21 22 3)

theorem buildWallUnionCsrProg_exec {w h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h G) (hW : W.IsValid)
    (baseSuccArr : ℕ) (hbase : 40 ≤ baseSuccArr)
    (hw3 : 3 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (he_w : G.numEdges < 2 ^ w)
    {s : State}
    (harr9 : s.arrs 9 = G.enc)
    (hX : IsBitSet X 16 s)
    (hsucc : IsWallSuccArrs W baseSuccArr s) :
    let G' := WallOfHeight.wallUnionMultiDigraph G X W
    let lists' := edgeNeighbors (edgeListOf G'.toSimpleGraph)
    let exprCost := (isWallUnionEdgeExpr h baseSuccArr 16 (3 + 6) (3 + 7)).cost
    ∃ s' t,
      Exec w (buildWallUnionCsrProg h baseSuccArr) s s' t ∧
      t ≤ 187 + 23 * n + (291 + exprCost) * G.numActivePairs ∧
      s'.arrs 23 = G'.enc ∧
      IsAdjList G'.toSimpleGraph 20 21 22 lists' s' ∧
      (s'.arrs 22).length = 2 * G'.toSimpleGraph.edgeFinset.card ∧
      totalAdjEntries lists' = 2 * G'.toSimpleGraph.edgeFinset.card ∧
      (∀ a : ℕ, a ≠ 0 → a ≠ 20 → a ≠ 21 → a ≠ 22 → a ≠ 23 → a ≠ 34 → a ≠ 35 →
        s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 ∨ 12 < r → s'.regs r = s.regs r) := by
  intro G' lists' exprCost
  have hn_w : n < 2 ^ w := by omega
  have hsucc_ne : ∀ k : Fin (elemWallEdges h).length, baseSuccArr + k.1 ≠ 34 := by
    intro k; omega
  rcases buildWallUnionMultiDigraphProg_exec G X W hW [] baseSuccArr 9 16 34 23 3
      (by decide) (by decide) (by decide) hsucc_ne hw3 hn1_w hm3_w he_w
      (by simpa using harr9) hX hsucc with
    ⟨s₁, t₁, hex₁, ht₁, harr23_1, _, _, harr₁, hreg₁⟩
  have hm'_le : G'.numActivePairs ≤ G.numActivePairs :=
    numActivePairs_wallUnionMultiDigraph_le G X W
  have hm'3_w : 2 + 3 * G'.numActivePairs < 2 ^ w := by omega
  rcases toSimpleGraphProg_exec G' [] 23 34 35 20 21 22 3
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw3 hn_w hm'3_w (by simpa using harr23_1) with
    ⟨s₂, t₂, hex₂, ht₂, _, _, _, hadj₂, hent₂, harr₂, _⟩
  have hnot_r2 : ∀ r : ℕ, r < 3 ∨ 12 < r →
      (r : Reg) ∉ (toSimpleGraphProg 23 34 35 20 21 22 3).writtenRegs := by
    intro r hr
    simp [toSimpleGraphProg, toSimpleGraphEdgeListProg, toSimpleGraphEdgeListBody,
      readTripleEndpoints, bufPush2, readSliceProg, readSliceBody,
      parseGraphProg, parsePass1Body, parsePrefixBody, parsePass2Body,
      readEdgeEndpoints, incArrAt, csrAppend, listAppend, forUp, Cmd.writtenRegs]
    omega
  have hcard_eq : (edgeListOf G'.toSimpleGraph).length = G'.toSimpleGraph.edgeFinset.card :=
    length_edgeListOf_eq_card_edgeFinset G'.toSimpleGraph
  have htot_eq : totalAdjEntries lists' = 2 * G'.toSimpleGraph.edgeFinset.card := by
    rw [totalAdjEntries_edgeNeighbors (edgeListOf G'.toSimpleGraph)
      (isSimpleEdgeList_edgeListOf G'.toSimpleGraph).1, hcard_eq]
  have ht₁_bound : t₁ ≤ 80 + (107 + exprCost) * G.numActivePairs := ht₁
  have ht₂_bound : t₂ ≤ 23 * n + 184 * G.numActivePairs + 107 := by
    have : 184 * G'.numActivePairs ≤ 184 * G.numActivePairs :=
      Nat.mul_le_mul_left 184 hm'_le
    omega
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
    by
      have : (107 + exprCost) * G.numActivePairs + 184 * G.numActivePairs =
          (291 + exprCost) * G.numActivePairs := by ring
      omega,
    by rw [harr₂ 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), harr23_1],
    hadj₂,
    by rw [hent₂, hcard_eq],
    htot_eq,
    fun a ha0 ha20 ha21 ha22 ha23 ha34 ha35 => by
      rw [harr₂ a ha34 ha0 ha35 ha20 ha21 ha22, harr₁ a ha34 ha23],
    fun r hr => by
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex₂ (hnot_r2 r hr)]
      exact hreg₁ r (by omega)⟩

end GraphMinor.Compute

end

