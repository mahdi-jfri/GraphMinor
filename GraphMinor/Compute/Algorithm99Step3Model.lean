module

public import GraphMinor.Compute.Algorithm99Step3

/-!
# Step (3) of Algorithm (9.9): writing the model of `K_p` in the labels of `G`

Step (3) of the proof of (9.8) in Graph Minors XIII (page 104) says: "If we obtain a model of
$K_p$ in $G_i$ and hence in $G$ we stop." The call of (9.7) writes the model in the labels of
`G_i`, as `0 :: encBitSetsUpTo K p`: `p` bit lists of length `v_i`. The model in `G` is
`fun j => (K j).map orig` (`IsCliqueModel.map_orig`), and output (ii) of (9.9) writes it as
`1 :: encBitSetsUpTo K' p`, with `p` bit lists of length `n`.

The program `alg99MapModelProg` allocates `1 + p n` zeros, writes the tag `1`, and then, for each
position `k = j v + u` of the input with bit `1`, writes `1` at position `1 + j n + orig u`
(`alg99MapModelProg_exec`). It takes time `O(p (v + n))`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### The words of `encBitSetsUpTo` -/

theorem getElem_encBitSetsUpTo_aux {n p : ℕ} (X : Fin p → Finset (Fin n)) (m : ℕ) (hm : m ≤ p)
    (j : Fin p) (hj : j.1 < m) (x : Fin n) (hlt : j.1 * n + x.1 < (encBitSetsUpTo X m).length) :
    (encBitSetsUpTo X m)[j.1 * n + x.1] = if x ∈ X j then 1 else 0 := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hmp : m < p := by omega
    have hlen : (encBitSetsUpTo X m).length = m * n := length_encBitSetsUpTo X m (by omega)
    simp only [encBitSetsUpTo, hmp, ↓reduceDIte] at hlt ⊢
    by_cases hjm : j.1 < m
    · have hlt' : j.1 * n + x.1 < (encBitSetsUpTo X m).length := by
        rw [hlen]
        have : (j.1 + 1) * n ≤ m * n := Nat.mul_le_mul_right n hjm
        rw [Nat.succ_mul] at this
        have := x.2
        omega
      rw [List.getElem_append_left hlt']
      exact ih (by omega) hjm hlt'
    · have hjeq : j.1 = m := by omega
      obtain ⟨j, hj⟩ := j
      simp only at hjeq
      subst hjeq
      have hge : (encBitSetsUpTo X j).length ≤ j * n + x.1 := by rw [hlen]; omega
      rw [List.getElem_append_right hge]
      simp only [bitSetList, List.getElem_ofFn, hlen, Nat.add_sub_cancel_left, Fin.eta]

/-- The word at position `j n + x` of `encBitSetsUpTo X p` is the bit of `x` in `X j`. -/
theorem getElem_encBitSetsUpTo {n p : ℕ} (X : Fin p → Finset (Fin n)) (j : Fin p) (x : Fin n)
    (hlt : j.1 * n + x.1 < (encBitSetsUpTo X p).length) :
    (encBitSetsUpTo X p)[j.1 * n + x.1] = if x ∈ X j then 1 else 0 :=
  getElem_encBitSetsUpTo_aux X p le_rfl j j.2 x hlt

/-! ### The program -/

/-- Body of the loop at position `r_i = j v + u` of the input model: if its bit is `1`, write
`1` at position `1 + j n + orig u` of `a_out`. -/
def alg99MapModelBody (a_in a_orig a_out : ℕ) (r_v r_n r_i : ℕ) : Cmd :=
  .ite (.op .eq (.read a_in (.op .add (.const 1) (.reg r_i))) (.const 0)) .skip
    (.write a_out
      (.op .add (.const 1)
        (.op .add (.op .mul (.op .div (.reg r_i) (.reg r_v)) (.reg r_n))
          (.read a_orig (.op .mod (.reg r_i) (.reg r_v)))))
      (.const 1))

/-- Writes `1 :: encBitSetsUpTo (fun j => (K j).map orig) p` into `a_out`, from
`0 :: encBitSetsUpTo K p` in `a_in`, the list of `orig` in `a_orig`, `v` in `r_v` and `n` in
`r_n`. -/
def alg99MapModelProg (p : ℕ) (a_in a_orig a_out : ℕ) (r_v r_n r_i : ℕ) : Cmd :=
  .seq (.alloc a_out (.op .add (.const 1) (.op .mul (.const p) (.reg r_n))))
    (.seq (.write a_out (.const 0) (.const 1))
      (.seq (.assign r_i (.const 0))
        (forUp r_i (.op .mul (.const p) (.reg r_v))
          (alg99MapModelBody a_in a_orig a_out r_v r_n r_i))))

/-- The positions `j v + u` with `u < v` are distinct. -/
private theorem mapModel_mul_add_inj {v : ℕ} {j j' u u' : ℕ} (hu : u < v) (hu' : u' < v)
    (h : j * v + u = j' * v + u') : j = j' ∧ u = u' := by
  have hv : 0 < v := by omega
  have h1 : (j * v + u) / v = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hv, Nat.div_eq_of_lt hu, Nat.zero_add]
  have h2 : (j' * v + u') / v = j' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hv, Nat.div_eq_of_lt hu', Nat.zero_add]
  have hj : j = j' := by rw [← h1, ← h2, h]
  subst hj
  exact ⟨rfl, by omega⟩

theorem div_lt_of_lt_mul_fin {n p i : ℕ} (hi : i < p * n) : i / n < p :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)

private theorem div_mul_add_mod_eq {n : ℕ} (j : ℕ) (x : Fin n) :
    (j * n + x.1) / n = j ∧ (j * n + x.1) % n = x.1 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) x.2
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt x.2, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt x.2]

/-- The contents of `a_out` after the positions below `k` of the input are read. -/
def mapModelList {v n p : ℕ} (K : Fin p → Finset (Fin v)) (orig : Fin v → Fin n) (k : ℕ) :
    List ℕ :=
  1 :: List.ofFn (fun i : Fin (p * n) =>
    if ∃ u : Fin v, u ∈ K ⟨i.1 / n, div_lt_of_lt_mul_fin i.2⟩ ∧ (orig u).1 = i.1 % n ∧
        i.1 / n * v + u.1 < k then 1 else 0)

theorem length_mapModelList {v n p : ℕ} (K : Fin p → Finset (Fin v)) (orig : Fin v → Fin n)
    (k : ℕ) : (mapModelList K orig k).length = 1 + p * n := by
  simp [mapModelList, Nat.add_comm]

theorem mapModelList_zero {v n p : ℕ} (K : Fin p → Finset (Fin v)) (orig : Fin v → Fin n) :
    mapModelList K orig 0 = (List.replicate (1 + p * n) 0).set 0 1 := by
  rw [Nat.add_comm, List.replicate_succ, List.set_cons_zero, mapModelList]
  congr 1
  refine List.ext_getElem (by simp) fun i _ _ => ?_
  simp

theorem mapModelList_of_le {v n p : ℕ} (K : Fin p → Finset (Fin v)) (orig : Fin v → Fin n)
    (hinj : Function.Injective orig) {k : ℕ} (hk : p * v ≤ k) :
    mapModelList K orig k = 1 :: encBitSetsUpTo (fun j => (K j).map ⟨orig, hinj⟩) p := by
  rw [mapModelList]
  congr 1
  refine List.ext_getElem (by simp [length_encBitSetsUpTo _ p le_rfl]) fun i hi₁ hi₂ => ?_
  have hi : i < p * n := by simpa using hi₁
  have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  let j : Fin p := ⟨i / n, div_lt_of_lt_mul_fin hi⟩
  let x : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩
  have hix : i = j.1 * n + x.1 := by simp only [j, x]; rw [Nat.mul_comm]; exact (Nat.div_add_mod i n).symm
  rw [List.getElem_ofFn]
  have hge := getElem_encBitSetsUpTo (fun j => (K j).map ⟨orig, hinj⟩) j x (hix ▸ hi₂)
  simp only [← hix] at hge
  rw [hge]
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk]
  congr 1
  apply propext
  constructor
  · rintro ⟨u, hu, hux, -⟩
    exact ⟨u, hu, Fin.ext hux⟩
  · rintro ⟨u, hu, hux⟩
    refine ⟨u, hu, congrArg Fin.val hux, ?_⟩
    have h1 : (j.1 + 1) * v ≤ p * v := Nat.mul_le_mul_right v j.2
    rw [Nat.succ_mul] at h1
    have := u.2
    change j.1 * v + u.1 < k
    omega

/-- Reading position `j v + u` with `u ∈ K j` sets the word `1 + j n + orig u`. -/
theorem mapModelList_succ_of_mem {v n p : ℕ} (K : Fin p → Finset (Fin v))
    (orig : Fin v → Fin n) (j : Fin p) (u : Fin v) (hu : u ∈ K j) :
    mapModelList K orig (j.1 * v + u.1 + 1) =
      (mapModelList K orig (j.1 * v + u.1)).set (1 + (j.1 * n + (orig u).1)) 1 := by
  rw [Nat.add_comm 1, mapModelList, mapModelList, List.set_cons_succ]
  congr 1
  refine List.ext_getElem (by simp) fun i hi₁ _ => ?_
  rw [List.getElem_set, List.getElem_ofFn, List.getElem_ofFn]
  have hi : i < p * n := by simpa using hi₁
  by_cases heq : j.1 * n + (orig u).1 = i
  · rw [ite_eq_left heq]
    obtain ⟨hd, hm⟩ := div_mul_add_mod_eq j.1 (orig u)
    subst heq
    refine ite_eq_left ⟨u, ?_, hm.symm, ?_⟩
    · have : (⟨(j.1 * n + (orig u).1) / n, div_lt_of_lt_mul_fin hi⟩ : Fin p) = j := Fin.ext hd
      rw [this]; exact hu
    · rw [hd]; omega
  · rw [ite_eq_right heq]
    congr 1
    apply propext
    constructor
    · rintro ⟨u', hu', hux, hlt⟩
      refine ⟨u', hu', hux, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq'
      · exact hlt
      · exfalso
        obtain ⟨hj, huu⟩ := mapModel_mul_add_inj u'.2 u.2 heq'
        apply heq
        have hu'u : u' = u := Fin.ext huu
        subst hu'u
        have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hi
        rw [← hj, hux, Nat.mul_comm]
        exact Nat.div_add_mod i n
    · rintro ⟨u', hu', hux, hlt⟩
      exact ⟨u', hu', hux, by omega⟩

/-- Reading position `j v + u` with `u ∉ K j` changes nothing. -/
theorem mapModelList_succ_of_not_mem {v n p : ℕ} (K : Fin p → Finset (Fin v))
    (orig : Fin v → Fin n) (j : Fin p) (u : Fin v) (hu : u ∉ K j) :
    mapModelList K orig (j.1 * v + u.1 + 1) = mapModelList K orig (j.1 * v + u.1) := by
  rw [mapModelList, mapModelList]
  congr 1
  refine List.ext_getElem (by simp) fun i hi₁ _ => ?_
  rw [List.getElem_ofFn, List.getElem_ofFn]
  have hi : i < p * n := by simpa using hi₁
  congr 1
  apply propext
  constructor
  · rintro ⟨u', hu', hux, hlt⟩
    refine ⟨u', hu', hux, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heq'
    · exact hlt
    · exfalso
      obtain ⟨hj, huu⟩ := mapModel_mul_add_inj u'.2 u.2 heq'
      have hu'u : u' = u := Fin.ext huu
      subst hu'u
      have : (⟨i / n, div_lt_of_lt_mul_fin hi⟩ : Fin p) = j := Fin.ext hj
      rw [this] at hu'
      exact hu hu'
  · rintro ⟨u', hu', hux, hlt⟩
    exact ⟨u', hu', hux, by omega⟩

/-- **Step (3) of Algorithm (9.9)** (page 104), the model "in $G_i$ and hence in $G$": from the
model `0 :: encBitSetsUpTo K p` of (9.7) in the labels of `G_i`, the program writes
`1 :: encBitSetsUpTo (fun j => (K j).map orig) p`, the output (ii) of (9.9) for the model of
`IsCliqueModel.map_orig`, in time `O(p (v + n))`. It changes only `a_out` and `r_i`. -/
theorem alg99MapModelProg_exec {w v n p : ℕ} (K : Fin p → Finset (Fin v)) (orig : Fin v → Fin n)
    (hinj : Function.Injective orig) (a_in a_orig a_out r_v r_n r_i : ℕ)
    (hne_io : a_in ≠ a_out) (hne_oo : a_orig ≠ a_out) (hne_vi : r_v ≠ r_i) (hne_ni : r_n ≠ r_i)
    (hw2 : 2 < 2 ^ w) (hp_w : p < 2 ^ w) (hv_w : v < 2 ^ w) (hn_w : n < 2 ^ w)
    (hpn_w : 1 + p * n < 2 ^ w) (hpv_w : 1 + p * v < 2 ^ w)
    {s : State} (hin : s.arrs a_in = 0 :: encBitSetsUpTo K p)
    (horig : s.arrs a_orig = List.ofFn (fun u : Fin v => (orig u).1))
    (hrv : s.regs r_v = v) (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (alg99MapModelProg p a_in a_orig a_out r_v r_n r_i) s s' t ∧
      t ≤ 30 * (p * v) + p * n + 20 ∧
      s'.arrs a_out = 1 :: encBitSetsUpTo (fun j => (K j).map ⟨orig, hinj⟩) p ∧
      (∀ a, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw2
  let s₁ := s.setArr a_out (List.replicate (1 + p * n) 0)
  have hex₁ : Exec w (.alloc a_out (.op .add (.const 1) (.op .mul (.const p) (.reg r_n)))) s s₁
      (5 + (1 + p * n)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrn, hp_w, hn_w,
      hpn_w, hw0, show p * n < 2 ^ w by omega])
  let s₂ := s₁.writeArr a_out 0 1
  have hex₂ : Exec w (.write a_out (.const 0) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, hw])
      (by simp [s₁])
  let s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (k : ℕ) (st : State) : Prop :=
    st.arrs a_out = mapModelList K orig k ∧ st.regs r_i = k ∧
    (∀ a, a ≠ a_out → st.arrs a = s.arrs a) ∧ (∀ r, r ≠ r_i → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₃ := by
    refine ⟨?_, by simp [s₃], fun a ha => ?_, fun r hr => ?_⟩
    · simp [s₃, s₂, s₁, mapModelList_zero]
    · simp [s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha, State.writeArr_arrs_ne _ _ _ ha]
    · simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr]
  have hpv : p * v < 2 ^ w := by omega
  have hLoop :
      ⦃Inv 0⦄[w] forUp r_i (.op .mul (.const p) (.reg r_v))
        (alg99MapModelBody a_in a_orig a_out r_v r_n r_i)
      ⦃Inv (p * v)⦄ ≤ fun _ => (3 + 2) + p * v * (3 + 6 + 20) := by
    apply Triple.forUp_const Inv (p * v) 20 hw hpv
    · intro k _ st ⟨_, hri_k, _, hreg_k⟩
      exact ⟨hri_k, by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg_k r_v hne_vi,
        hrv, hp_w, hv_w, hpv]⟩
    · intro k hk st ⟨hout_k, hri_k, harr_k, hreg_k⟩
      have hv0 : 0 < v := Nat.pos_of_ne_zero fun h => by simp [h] at hk
      have hk_w : k < 2 ^ w := by omega
      let j : Fin p := ⟨k / v, div_lt_of_lt_mul_fin hk⟩
      let u : Fin v := ⟨k % v, Nat.mod_lt _ hv0⟩
      have hku : k = j.1 * v + u.1 := by
        simp only [j, u]; rw [Nat.mul_comm]; exact (Nat.div_add_mod k v).symm
      have hin_st : st.arrs a_in = 0 :: encBitSetsUpTo K p := (harr_k a_in hne_io).trans hin
      have horig_st : st.arrs a_orig = List.ofFn (fun u : Fin v => (orig u).1) :=
        (harr_k a_orig hne_oo).trans horig
      have hlenE : (encBitSetsUpTo K p).length = p * v := length_encBitSetsUpTo K p le_rfl
      have hk_len : 1 + k < (st.arrs a_in).length := by
        rw [hin_st, List.length_cons, hlenE]; omega
      have hbit : (st.arrs a_in)[1 + k]'hk_len = if u ∈ K j then 1 else 0 := by
        have hlt : j.1 * v + u.1 < (encBitSetsUpTo K p).length := by rw [hlenE, ← hku]; exact hk
        have := getElem_encBitSetsUpTo K j u hlt
        simp only [hin_st, Nat.add_comm 1 k, List.getElem_cons_succ]
        simp only [← hku] at this
        exact this
      have hrv_st : st.regs r_v = v := (hreg_k r_v hne_vi).trans hrv
      have hrn_st : st.regs r_n = n := (hreg_k r_n hne_ni).trans hrn
      have h1k_w : 1 + k < 2 ^ w := by omega
      by_cases hu : u ∈ K j
      · have hcond : (Expr.op .eq (.read a_in (.op .add (.const 1) (.reg r_i)))
            (.const 0)).eval w st = some 0 := by
          rw [ite_eq_left hu] at hbit
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_k, hk_w, hw, h0_w, h1k_w,
            hk_len, hbit]
        have hjn : j.1 * n + (orig u).1 < p * n := by
          have h1 : (j.1 + 1) * n ≤ p * n := Nat.mul_le_mul_right n j.2
          rw [Nat.succ_mul] at h1
          have := (orig u).2
          omega
        have hjn_le : j.1 * n ≤ p * n := by omega
        have hu_len : k % v < (st.arrs a_orig).length := by
          rw [horig_st, List.length_ofFn]; exact u.2
        have hou : (st.arrs a_orig)[k % v]'hu_len = (orig u).1 := by
          simp only [horig_st, List.getElem_ofFn]; rfl
        have hidx : (Expr.op .add (.const 1)
            (.op .add (.op .mul (.op .div (.reg r_i) (.reg r_v)) (.reg r_n))
              (.read a_orig (.op .mod (.reg r_i) (.reg r_v))))).eval w st =
            some (1 + (j.1 * n + (orig u).1)) := by
          have hkv : k / v = j.1 := rfl
          have hmv : k % v < 2 ^ w := by have := Nat.mod_lt k hv0; omega
          have hj_w : j.1 < 2 ^ w := by have := j.2; omega
          have hou_w : (orig u).1 < 2 ^ w := by have := (orig u).2; omega
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_k, hk_w, hw,
            hrv_st, hrn_st, hv_w, hn_w, Nat.pos_iff_ne_zero.mp hv0, hmv, hu_len, hou,
            hou_w, hkv, hj_w, show j.1 * n < 2 ^ w by omega,
            show j.1 * n + (orig u).1 < 2 ^ w by omega, show 1 + (j.1 * n + (orig u).1) < 2 ^ w by omega]
        have hout_len : 1 + (j.1 * n + (orig u).1) < (st.arrs a_out).length := by
          rw [hout_k, length_mapModelList]; omega
        let st₁ := st.writeArr a_out (1 + (j.1 * n + (orig u).1)) 1
        have hex_w : Exec w (.write a_out
            (.op .add (.const 1)
              (.op .add (.op .mul (.op .div (.reg r_i) (.reg r_v)) (.reg r_n))
                (.read a_orig (.op .mod (.reg r_i) (.reg r_v)))))
            (.const 1)) st st₁ (12 + 1 + 1) :=
          .write hidx (by simp [Expr.eval, checkWord, hw]) hout_len
        refine ⟨st₁, 6 + (12 + 1 + 1), .ite_false hcond hex_w, by show 6 + (12 + 1 + 1) ≤ 20; omega,
          ⟨?_, by simp [st₁], fun a ha => by simp [st₁, State.writeArr_arrs_ne _ _ _ ha, harr_k a ha],
            fun r hr => by simp [st₁, State.setReg_regs_ne _ _ hr, hreg_k r hr]⟩,
            by simp [st₁, hri_k]⟩
        simp only [st₁, State.setReg_arrs, State.writeArr_arrs_self, hout_k, hku]
        exact (mapModelList_succ_of_mem K orig j u hu).symm
      · have hcond : (Expr.op .eq (.read a_in (.op .add (.const 1) (.reg r_i)))
            (.const 0)).eval w st = some 1 := by
          rw [ite_eq_right hu] at hbit
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_k, hk_w, hw, h0_w, h1k_w,
            hk_len, hbit]
        refine ⟨st, 6 + 1, .ite_true hcond (by decide) (.skip st), by show 6 + 1 ≤ 20; omega,
          ⟨?_, by simp, fun a ha => by simpa using harr_k a ha,
            fun r hr => by simp [State.setReg_regs_ne _ _ hr, hreg_k r hr]⟩, hri_k⟩
        simp only [State.setReg_arrs, hout_k, hku]
        exact (mapModelList_succ_of_not_mem K orig j u hu).symm
  rcases hLoop s₃ hInv₀ with ⟨s₄, t₄, hex₄, ht₄, hout₄, _, harr₄, hreg₄⟩
  dsimp only at ht₄
  refine ⟨s₄, 5 + (1 + p * n) + (3 + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, ?_, harr₄, hreg₄⟩
  rw [hout₄, mapModelList_of_le K orig hinj le_rfl]

end GraphMinor.Compute
