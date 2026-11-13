module

public import GraphMinor.Compute.Algorithm99Step4Count
public import GraphMinor.Compute.Logic
public import GraphMinor.Compute.BitSet

/-!
# Step (4) of Algorithm (9.9): counting the edges of a compass

Step (4) of Algorithm (9.9) (Graph Minors XIII, pages 104–105) compares
`ε(K^a) + d_a + |X|` with `ε(G_i)`. By `Algorithm99Step4Count`, the two edge counts are the
numbers of edges of `G_i` with both ends in the vertex set `V` of `K^a`, and with one end in `V`
and the other in `X`. This file gives the program that finds both numbers in one scan of the
triples of `G_i.enc`.

For the triple `(u, w, m)` the program adds `m · [u ∈ V] · [w ∈ V]` to the first count and
`m · ([u ∈ V] [w ∈ X] + [u ∈ X] [w ∈ V])` to the second, reading the bits from the bit sets of
`V` and `X` (`step4CountProg_exec`). Since `V` misses `X`, the second sum counts each edge from
`V` to `X` or from `X` to `V` once.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- Evaluation of a sum whose parts are known. -/
theorem step4_eval_add {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) (hw : v₁ + v₂ < 2 ^ w) :
    (Expr.op .add e₁ e₂).eval w s = some (v₁ + v₂) := by
  simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, hw]

/-- Evaluation of a product whose factors are known. -/
theorem step4_eval_mul {w : ℕ} {s : State} {e₁ e₂ : Expr} {v₁ v₂ : ℕ}
    (h₁ : e₁.eval w s = some v₁) (h₂ : e₂.eval w s = some v₂) (hw : v₁ * v₂ < 2 ^ w) :
    (Expr.op .mul e₁ e₂).eval w s = some (v₁ * v₂) := by
  simp [Expr.eval, h₁, h₂, BinOp.eval, BinOp.raw, checkWord, hw]

/-- Evaluation of a register. -/
theorem step4_eval_reg {w : ℕ} {s : State} {r : Reg} {v : ℕ} (h : s.regs r = v)
    (hw : v < 2 ^ w) : (Expr.reg r).eval w s = some v := by
  simp [Expr.eval, checkWord, h, hw]

/-- The multiplicities of `G.restrictMult P` summed over the active pairs of `G` give its number
of edges, since every active pair of `G.restrictMult P` is an active pair of `G`. -/
theorem MultiDigraph.sum_map_restrictMult_activePairsList {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] :
    (G.activePairsList.map (fun p => (G.restrictMult P).edgeMult p.1 p.2)).sum =
      (G.restrictMult P).numEdges := by
  have hH : (G.restrictMult P).activePairsList = G.activePairsList.filter
      (fun p => decide (0 < (G.restrictMult P).edgeMult p.1 p.2)) := by
    unfold MultiDigraph.activePairsList
    rw [List.filter_filter]
    apply List.filter_congr
    intro p _
    simp only [MultiDigraph.restrictMult]
    split_ifs <;> simp
  rw [← MultiDigraph.sumEdgeMult_eq_map_sum, ← MultiDigraph.sumEdgeMult_activePairsList, hH,
    MultiDigraph.sumEdgeMult_filter_pos]

/-- `G.restrictMult P` has at most the edges of `G`. -/
theorem MultiDigraph.numEdges_restrictMult_le {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] :
    (G.restrictMult P).numEdges ≤ G.numEdges := by
  unfold MultiDigraph.numEdges
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro w _
  simp only [MultiDigraph.restrictMult]
  split_ifs <;> omega

/-- A partial sum of the multiplicities of `G.restrictMult P` along the active pairs of `G` is at
most `|E(G)|`. -/
theorem MultiDigraph.sum_take_restrictMult_le {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] (i : ℕ) :
    ((G.activePairsList.take i).map (fun p => (G.restrictMult P).edgeMult p.1 p.2)).sum ≤
      G.numEdges := by
  calc ((G.activePairsList.take i).map (fun p => (G.restrictMult P).edgeMult p.1 p.2)).sum
      ≤ (G.activePairsList.map (fun p => (G.restrictMult P).edgeMult p.1 p.2)).sum := by
        conv_rhs => rw [← List.take_append_drop i G.activePairsList]
        rw [List.map_append, List.sum_append]
        omega
    _ = (G.restrictMult P).numEdges := G.sum_map_restrictMult_activePairsList P
    _ ≤ G.numEdges := G.numEdges_restrictMult_le P

/-- The word added to the first count for the triple `(u, w, m)`. -/
theorem step4_mul_in {n : ℕ} (V : Finset (Fin n)) (u w : Fin n) (m : ℕ) :
    m * ((if u ∈ V then 1 else 0) * (if w ∈ V then 1 else 0)) =
      if u ∈ V ∧ w ∈ V then m else 0 := by
  by_cases hu : u ∈ V <;> by_cases hw : w ∈ V <;> simp [hu, hw]

/-- The word added to the second count for the triple `(u, w, m)`, when `V` misses `X`. -/
theorem step4_mul_cross {n : ℕ} (V X : Finset (Fin n)) (hVX : Disjoint V X) (u w : Fin n)
    (m : ℕ) :
    m * ((if u ∈ V then 1 else 0) * (if w ∈ X then 1 else 0) +
        (if u ∈ X then 1 else 0) * (if w ∈ V then 1 else 0)) =
      if (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V) then m else 0 := by
  have hu : ¬ (u ∈ V ∧ u ∈ X) := fun h => Finset.disjoint_left.mp hVX h.1 h.2
  have hw : ¬ (w ∈ V ∧ w ∈ X) := fun h => Finset.disjoint_left.mp hVX h.1 h.2
  by_cases huV : u ∈ V <;> by_cases huX : u ∈ X <;> by_cases hwV : w ∈ V <;>
    by_cases hwX : w ∈ X <;> simp_all

/-- One triple of the scan: reads `u, w, m` from position `2 + 3 i` of `a_G` (`i` in register
`r`) and adds the two words to registers `r + 8` and `r + 9`. -/
def step4CountBody (a_G a_V a_X : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 1) (.read a_G (.op .add (.const 2) (.op .mul (.const 3) (.reg r)))))
    (.seq (.assign (r + 2) (.read a_G
        (.op .add (.op .add (.const 2) (.op .mul (.const 3) (.reg r))) (.const 1))))
      (.seq (.assign (r + 3) (.read a_G
          (.op .add (.op .add (.const 2) (.op .mul (.const 3) (.reg r))) (.const 2))))
        (.seq (.assign (r + 8) (.op .add (.reg (r + 8)) (.op .mul (.reg (r + 3))
            (.op .mul (.read a_V (.reg (r + 1))) (.read a_V (.reg (r + 2)))))))
          (.assign (r + 9) (.op .add (.reg (r + 9)) (.op .mul (.reg (r + 3))
            (.op .add (.op .mul (.read a_V (.reg (r + 1))) (.read a_X (.reg (r + 2))))
              (.op .mul (.read a_X (.reg (r + 1))) (.read a_V (.reg (r + 2)))))))))))

/-- The scan of step (4): the number of triples in register `r + 10`, the two counts in
registers `r + 8` and `r + 9`, the loop index in register `r`. -/
def step4CountProg (a_G a_V a_X : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 10) (.read a_G (.const 1)))
    (.seq (.assign (r + 8) (.const 0))
      (.seq (.assign (r + 9) (.const 0))
        (.seq (.assign r (.const 0))
          (forUp r (.reg (r + 10)) (step4CountBody a_G a_V a_X r)))))

/-- **The counts of step (4) of (9.9)** (Graph Minors XIII, page 105). From `G.enc` in `a_G`, the
bit set of `V` in `a_V` and the bit set of `X` in `a_X`, with `V` missing `X`, the program ends
with the number of edges of `G` with both ends in `V` in register `r + 8`, and the number of
edges with one end in `V` and the other in `X` in register `r + 9`. It changes no array and only
the registers `r, …, r + 10`, in time `≤ 60 m' + 20` (`m'` the number of triples). -/
theorem step4CountProg_exec {w n : ℕ} (G : MultiDigraph n) (V X : Finset (Fin n))
    (hVX : Disjoint V X) (a_G a_V a_X r : ℕ)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w) {s : State}
    (hG : s.arrs a_G = G.enc) (hV : IsBitSet V a_V s) (hX : IsBitSet X a_X s) :
    ∃ s' t, Exec w (step4CountProg a_G a_V a_X r) s s' t ∧
      t ≤ 60 * G.numActivePairs + 20 ∧
      s'.regs (r + 8) = (G.restrictMult (fun u w => u ∈ V ∧ w ∈ V)).numEdges ∧
      s'.regs (r + 9) =
        (G.restrictMult (fun u w => (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V))).numEdges ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < r ∨ r + 10 < q → s'.regs q = s.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  set L := G.activePairsList with hL
  have hLlen : L.length = G.numActivePairs := rfl
  set f1 : Fin n × Fin n → ℕ :=
    fun p => (G.restrictMult (fun u w => u ∈ V ∧ w ∈ V)).edgeMult p.1 p.2 with hf1
  set f2 : Fin n × Fin n → ℕ :=
    fun p => (G.restrictMult (fun u w => (u ∈ V ∧ w ∈ X) ∨ (u ∈ X ∧ w ∈ V))).edgeMult p.1 p.2
    with hf2
  -- The prelude.
  have hsrc : s.arrs a_G = G.enc ++ [] := by simp [hG]
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G [] hsrc
  let s₁ := s.setReg (r + 10) G.numActivePairs
  have hex₁ : Exec w (.assign (r + 10) (.read a_G (.const 1))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw1, h1_len, h1_val, hm'_w])
  let s₂ := s₁.setReg (r + 8) 0
  have hex₂ : Exec w (.assign (r + 8) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg (r + 9) 0
  have hex₃ : Exec w (.assign (r + 9) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg r 0
  have hex₄ : Exec w (.assign r (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- The loop invariant.
  let Inv (i : ℕ) (st : State) : Prop :=
    st.arrs = s.arrs ∧ st.regs r = i ∧ st.regs (r + 10) = G.numActivePairs ∧
    st.regs (r + 8) = ((L.take i).map f1).sum ∧ st.regs (r + 9) = ((L.take i).map f2).sum ∧
    (∀ q : ℕ, q < r ∨ r + 10 < q → st.regs q = s.regs q)
  have hInv₀ : Inv 0 s₄ := by
    refine ⟨rfl, by simp [s₄], ?_, ?_, ?_, ?_⟩
    · simp [s₄, s₃, s₂, s₁]
    · simp [s₄, s₃, s₂]
    · simp [s₄, s₃]
    · intro q hq
      simp [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ (show (q : Reg) ≠ r by romega),
        State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 9 by romega),
        State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 8 by romega),
        State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 10 by romega)]
  have hloop : ⦃Inv 0⦄[w] forUp r (.reg (r + 10)) (step4CountBody a_G a_V a_X r)
      ⦃Inv G.numActivePairs⦄ ≤
        fun _ => ((Expr.reg (r + 10)).cost + 2) +
          G.numActivePairs * ((Expr.reg (r + 10)).cost + 6 + 51) := by
    apply Triple.forUp_const Inv G.numActivePairs 51 hw1 hm'_w
    · intro i _ st ⟨_, hri, hr10, _⟩
      exact ⟨hri, by simp [hr10, checkWord, hm'_w]⟩
    · intro i hi st ⟨harr, hri, hr10, hr8, hr9, hreg⟩
      have hi_w : i < 2 ^ w := by omega
      have hiL : i < L.length := hi
      set u := (L[i]'hiL).1 with hu
      set v := (L[i]'hiL).2 with hv
      have hsrc_st : st.arrs a_G = G.enc ++ [] := by rw [harr, hG]; simp
      obtain ⟨hlen0, hget0⟩ := enc_getElem_triple_fst G [] hsrc_st hi
      obtain ⟨hlen1, hget1⟩ := enc_getElem_triple_snd G [] hsrc_st hi
      obtain ⟨hlen2, hget2⟩ := enc_getElem_triple_mult G [] hsrc_st hi
      change _ = (L[i]'hiL).1.1 at hget0
      change _ = (L[i]'hiL).2.1 at hget1
      change _ = G.edgeMult (L[i]'hiL).1 (L[i]'hiL).2 at hget2
      have hm_le : G.edgeMult u v ≤ G.numEdges := by
        unfold MultiDigraph.numEdges
        calc G.edgeMult u v ≤ ∑ v' : Fin n, G.edgeMult u v' :=
              Finset.single_le_sum (f := fun v' => G.edgeMult u v') (fun _ _ => Nat.zero_le _)
                (Finset.mem_univ v)
          _ ≤ ∑ u' : Fin n, ∑ v' : Fin n, G.edgeMult u' v' :=
              Finset.single_le_sum (f := fun u' => ∑ v' : Fin n, G.edgeMult u' v')
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
      have hmult_w : G.edgeMult u v < 2 ^ w := by omega
      have hu_w : u.1 < 2 ^ w := by omega
      have hv_w : v.1 < 2 ^ w := by omega
      have hV' : IsBitSet V a_V st := hV.of_arr_eq (by rw [harr])
      have hX' : IsBitSet X a_X st := hX.of_arr_eq (by rw [harr])
      have hVlen := hV'.1
      have hXlen := hX'.1
      have hVu := hV'.getElem_eq_ite u
      have hVv := hV'.getElem_eq_ite v
      have hXu := hX'.getElem_eq_ite u
      have hXv := hX'.getElem_eq_ite v
      have hu_V : u.1 < (st.arrs a_V).length := by rw [hVlen]; exact u.2
      have hv_V : v.1 < (st.arrs a_V).length := by rw [hVlen]; exact v.2
      have hu_X : u.1 < (st.arrs a_X).length := by rw [hXlen]; exact u.2
      have hv_X : v.1 < (st.arrs a_X).length := by rw [hXlen]; exact v.2
      have h3i_w : 3 * i < 2 ^ w := by omega
      have h2i_w : 2 + 3 * i < 2 ^ w := by omega
      have h2i1_w : 2 + 3 * i + 1 < 2 ^ w := by omega
      have h2i2_w : 2 + 3 * i + 2 < 2 ^ w := by omega
      have hw2 : 2 < 2 ^ w := by omega
      -- 1. `u`
      let st₁ := st.setReg (r + 1) u.1
      have hex₁ : Exec w (.assign (r + 1)
          (.read a_G (.op .add (.const 2) (.op .mul (.const 3) (.reg r))))) st st₁ 7 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hw2, hw3, hi_w,
          h3i_w, h2i_w, hlen0, hget0, hu_w, u])
      -- 2. `w`
      let st₂ := st₁.setReg (r + 2) v.1
      have hex₂ : Exec w (.assign (r + 2) (.read a_G
          (.op .add (.op .add (.const 2) (.op .mul (.const 3) (.reg r))) (.const 1)))) st₁ st₂ 9 :=
        .assign (by simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hri, hw1, hw2, hw3, hi_w,
          h3i_w, h2i_w, h2i1_w, hlen1, hget1, hv_w, v])
      -- 3. `m`
      let st₃ := st₂.setReg (r + 3) (G.edgeMult u v)
      have hex₃ : Exec w (.assign (r + 3) (.read a_G
          (.op .add (.op .add (.const 2) (.op .mul (.const 3) (.reg r))) (.const 2)))) st₂ st₃ 9 :=
        .assign (by simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hri, hw2, hw3, hi_w,
          h3i_w, h2i_w, h2i2_w, hlen2, hget2, hmult_w, u, v])
      have hr1_3 : st₃.regs (r + 1) = u.1 := by
        simp [st₃, st₂, st₁]
      have hr2_3 : st₃.regs (r + 2) = v.1 := by
        simp [st₃, st₂]
      have hr3_3 : st₃.regs (r + 3) = G.edgeMult u v := by simp [st₃]
      have hr8_3 : st₃.regs (r + 8) = ((L.take i).map f1).sum := by
        simp [st₃, st₂, st₁, hr8]
      have harr₃ : st₃.arrs = st.arrs := rfl
      -- the two words
      have hin_eq : G.edgeMult u v * ((if u ∈ V then 1 else 0) * (if v ∈ V then 1 else 0)) =
          f1 (L[i]'hiL) := by
        rw [step4_mul_in]; simp [hf1, MultiDigraph.restrictMult, u, v]
      have hcr_eq : G.edgeMult u v * ((if u ∈ V then 1 else 0) * (if v ∈ X then 1 else 0) +
          (if u ∈ X then 1 else 0) * (if v ∈ V then 1 else 0)) = f2 (L[i]'hiL) := by
        rw [step4_mul_cross V X hVX]; simp [hf2, MultiDigraph.restrictMult, u, v]
      have hsum_succ : ∀ f : Fin n × Fin n → ℕ,
          ((L.take (i + 1)).map f).sum = ((L.take i).map f).sum + f (L[i]'hiL) := by
        intro f
        rw [take_add_one_eq_append_getElem L i hiL, List.map_append, List.sum_append]
        simp
      have hle1 : ((L.take (i + 1)).map f1).sum ≤ G.numEdges :=
        MultiDigraph.sum_take_restrictMult_le G _ (i + 1)
      have hle2 : ((L.take (i + 1)).map f2).sum ≤ G.numEdges :=
        MultiDigraph.sum_take_restrictMult_le G _ (i + 1)
      rw [hsum_succ] at hle1 hle2
      have hbit : ∀ (P : Prop) [Decidable P], (if P then 1 else 0 : ℕ) < 2 ^ w := by
        intro P _; split_ifs <;> omega
      have hbit1 : ∀ (P : Prop) [Decidable P], (if P then 1 else 0 : ℕ) ≤ 1 := by
        intro P _; split_ifs <;> omega
      have hprod_le : ∀ (P Q : Prop) [Decidable P] [Decidable Q],
          (if P then 1 else 0 : ℕ) * (if Q then 1 else 0) ≤ 1 := by
        intro P Q _ _; split_ifs <;> omega
      have hsum2_le : (if u ∈ V then 1 else 0 : ℕ) * (if v ∈ X then 1 else 0) +
          (if u ∈ X then 1 else 0) * (if v ∈ V then 1 else 0) ≤ 1 := by
        have hu' : ¬ (u ∈ V ∧ u ∈ X) := fun h => Finset.disjoint_left.mp hVX h.1 h.2
        by_cases huV : u ∈ V <;> by_cases huX : u ∈ X <;> by_cases hwV : v ∈ V <;>
          by_cases hwX : v ∈ X <;> simp_all
      have hw_in : G.edgeMult u v * ((if u ∈ V then 1 else 0) * (if v ∈ V then 1 else 0)) ≤
          G.edgeMult u v := by
        have := hprod_le (u ∈ V) (v ∈ V)
        calc _ ≤ G.edgeMult u v * 1 := Nat.mul_le_mul_left _ this
          _ = _ := Nat.mul_one _
      have hw_cr : G.edgeMult u v * ((if u ∈ V then 1 else 0) * (if v ∈ X then 1 else 0) +
          (if u ∈ X then 1 else 0) * (if v ∈ V then 1 else 0)) ≤ G.edgeMult u v := by
        calc _ ≤ G.edgeMult u v * 1 := Nat.mul_le_mul_left _ hsum2_le
          _ = _ := Nat.mul_one _
      -- 4. the first count
      let st₄ := st₃.setReg (r + 8) (((L.take i).map f1).sum + f1 (L[i]'hiL))
      have hex₄ : Exec w (.assign (r + 8) (.op .add (.reg (r + 8)) (.op .mul (.reg (r + 3))
          (.op .mul (.read a_V (.reg (r + 1))) (.read a_V (.reg (r + 2))))))) st₃ st₄ 10 := by
        refine .assign ?_
        have e1 : (Expr.read a_V (.reg (r + 1))).eval w st₃ = some (if u ∈ V then 1 else 0) := by
          simp [Expr.eval, checkWord, hr1_3, hu_w, harr₃, hu_V, hVu, hbit]
        have e2 : (Expr.read a_V (.reg (r + 2))).eval w st₃ = some (if v ∈ V then 1 else 0) := by
          simp [Expr.eval, checkWord, hr2_3, hv_w, harr₃, hv_V, hVv, hbit]
        have hprod_w : (if u ∈ V then 1 else 0 : ℕ) * (if v ∈ V then 1 else 0) < 2 ^ w := by
          have := hprod_le (u ∈ V) (v ∈ V); omega
        have h8_w : ((L.take i).map f1).sum < 2 ^ w := by omega
        have hs_w : ((L.take i).map f1).sum + f1 (L[i]'hiL) < 2 ^ w := by omega
        rw [← hin_eq]
        exact step4_eval_add (step4_eval_reg hr8_3 h8_w)
          (step4_eval_mul (step4_eval_reg hr3_3 hmult_w) (step4_eval_mul e1 e2 hprod_w)
          (by omega)) (by rw [hin_eq]; exact hs_w)
      -- 5. the second count
      have hr1_4 : st₄.regs (r + 1) = u.1 := by
        simp [st₄, hr1_3]
      have hr2_4 : st₄.regs (r + 2) = v.1 := by
        simp [st₄, hr2_3]
      have hr3_4 : st₄.regs (r + 3) = G.edgeMult u v := by
        simp [st₄, hr3_3]
      have hr9_4 : st₄.regs (r + 9) = ((L.take i).map f2).sum := by
        simp [st₄, st₃, st₂, st₁, hr9]
      have harr₄ : st₄.arrs = st.arrs := rfl
      let st₅ := st₄.setReg (r + 9) (((L.take i).map f2).sum + f2 (L[i]'hiL))
      have hex₅ : Exec w (.assign (r + 9) (.op .add (.reg (r + 9)) (.op .mul (.reg (r + 3))
          (.op .add (.op .mul (.read a_V (.reg (r + 1))) (.read a_X (.reg (r + 2))))
            (.op .mul (.read a_X (.reg (r + 1))) (.read a_V (.reg (r + 2)))))))) st₄ st₅ 16 := by
        refine .assign ?_
        have e1 : (Expr.read a_V (.reg (r + 1))).eval w st₄ = some (if u ∈ V then 1 else 0) := by
          simp [Expr.eval, checkWord, hr1_4, hu_w, harr₄, hu_V, hVu, hbit]
        have e2 : (Expr.read a_V (.reg (r + 2))).eval w st₄ = some (if v ∈ V then 1 else 0) := by
          simp [Expr.eval, checkWord, hr2_4, hv_w, harr₄, hv_V, hVv, hbit]
        have e3 : (Expr.read a_X (.reg (r + 1))).eval w st₄ = some (if u ∈ X then 1 else 0) := by
          simp [Expr.eval, checkWord, hr1_4, hu_w, harr₄, hu_X, hXu, hbit]
        have e4 : (Expr.read a_X (.reg (r + 2))).eval w st₄ = some (if v ∈ X then 1 else 0) := by
          simp [Expr.eval, checkWord, hr2_4, hv_w, harr₄, hv_X, hXv, hbit]
        have hp1 : (if u ∈ V then 1 else 0 : ℕ) * (if v ∈ X then 1 else 0) < 2 ^ w := by
          have := hprod_le (u ∈ V) (v ∈ X); omega
        have hp2 : (if u ∈ X then 1 else 0 : ℕ) * (if v ∈ V then 1 else 0) < 2 ^ w := by
          have := hprod_le (u ∈ X) (v ∈ V); omega
        have hp3 : (if u ∈ V then 1 else 0 : ℕ) * (if v ∈ X then 1 else 0) +
            (if u ∈ X then 1 else 0) * (if v ∈ V then 1 else 0) < 2 ^ w := by omega
        have h9_w : ((L.take i).map f2).sum < 2 ^ w := by omega
        have hs_w : ((L.take i).map f2).sum + f2 (L[i]'hiL) < 2 ^ w := by omega
        rw [← hcr_eq]
        exact step4_eval_add (step4_eval_reg hr9_4 h9_w)
          (step4_eval_mul (step4_eval_reg hr3_4 hmult_w)
          (step4_eval_add (step4_eval_mul e1 e4 hp1) (step4_eval_mul e3 e2 hp2) hp3) (by omega))
          (by rw [hcr_eq]; exact hs_w)
      have hreg₅ : ∀ q : ℕ, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 3 → q ≠ r + 8 →
          q ≠ r + 9 → (st₅.setReg r (i + 1)).regs q = st.regs q := by
        intro q h0 h1 h2 h3 h8 h9
        simp only [st₅, st₄, st₃, st₂, st₁, State.setReg_regs_ne _ _ (show (q : Reg) ≠ r from h0),
          State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 1 from h1),
          State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 2 from h2),
          State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 3 from h3),
          State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 8 from h8),
          State.setReg_regs_ne _ _ (show (q : Reg) ≠ r + 9 from h9)]
      refine ⟨st₅, 7 + (9 + (9 + (10 + 16))),
        .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by norm_num,
          ⟨harr, by simp, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hreg₅ (r + 10) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hr10]
      · rw [hsum_succ]
        simp [st₅, st₄]
      · rw [hsum_succ]
        simp [st₅]
      · intro q hq
        rw [hreg₅ q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hreg q hq]
      · simp [st₅, st₄, st₃, st₂, st₁, hri]
  obtain ⟨s₅, t₅, hex₅, ht₅, harr₅, -, -, hr8₅, hr9₅, hreg₅⟩ := hloop s₄ hInv₀
  have htake : L.take G.numActivePairs = L := by rw [← hLlen, List.take_length]
  refine ⟨s₅, 3 + (2 + (2 + (2 + t₅))), .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    ?_, ?_, ?_, ?_, hreg₅⟩
  · simp only [Expr.cost] at ht₅
    omega
  · rw [hr8₅, htake, hf1]
    exact G.sum_map_restrictMult_activePairsList _
  · rw [hr9₅, htake, hf2]
    exact G.sum_map_restrictMult_activePairsList _
  · intro a
    rw [harr₅]

end GraphMinor.Compute
