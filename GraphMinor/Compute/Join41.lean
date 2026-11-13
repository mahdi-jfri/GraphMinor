module

public import GraphMinor.Compute.Algorithm105Step2

/-!
# Joining Step (2) of GM XIII Algorithm (10.5) to Algorithm (4.1) (`algorithm_4_1_code`)

This file connects Step (2) of Algorithm (10.5) (Robertson and Seymour, *Graph Minors. XIII. The
Disjoint Paths Problem*, page 109) to the Word RAM implementation of Algorithm (4.1)
(`algorithm_4_1_code` and `alg41Prog` in `GraphMinor/Compute/Algorithm41.lean`, pages 75–76).

## Main Definitions and Results

1. **`writtenToBDCode` and `writtenToAlg41CodeInput`:**
   Converts a written-out branch-decomposition `(t, par, f_tau)` of `G.toComputeDigraph` of width
   `≤ B` (`IsWrittenDigraphBD B G.toComputeDigraph t par f_tau`, produced by `convertBDProg` in
   `Algorithm105Step2.lean`) into a valid serialized branch-decomposition code `bdCode : List ℕ`
   of `G : MultiDigraph n` (`IsValidBranchDecompCode B G bdCode`) and an `Alg41CodeInput ξ B`
   instance `x`, proving exact slice-by-slice agreement with `encAlg41CodeIn x`.
2. **`normalizeBD41Prog`, `packAlg41InProg`, and `join41Prog`:**
   Word RAM program that normalizes the written branch-decomposition in `(r_52, b + 2, b + 3)`
   (handling both `|E(G)| ≤ 1` and `2 ≤ |E(G)|`), packs `encAlg41CodeIn x` into `inArr` (`arrs 0`)
   from the Step (2) registers and arrays (`r_26, r_28, r_52`, `b + 1, b + 2, b + 3, b + 5, b + 6`),
   and runs `alg41Prog δ ξ B`, all in linear time `O(v + ε)` (`≤ 250 * (n + |E(G)| + 1)`).
3. **`alg41Spec_proved`:**
   Proves `Alg105.Alg41Spec p ξ δ B` unconditionally from `algorithm_4_1_code`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Combinatorial Conversion from `IsWrittenDigraphBD` to `Alg41CodeInput` -/

/-- Convert a written-out branch-decomposition `(t, par, f_tau)` of `G.toComputeDigraph` into a
serialized branch-decomposition code `bdCode : List ℕ` of `G : MultiDigraph n`. -/
noncomputable def writtenToBDCode {n : ℕ} (G : MultiDigraph n) (t : ℕ) (par f_tau : ℕ → ℕ) :
    List ℕ :=
  if G.numEdges ≤ 1 then
    [0, G.numEdges] ++ List.replicate G.numEdges 0
  else
    encBranchDecomp t G.numEdges
      (List.ofFn (fun z : Fin t => if z.1 = 0 then 0 else par z.1))
      (List.ofFn (fun e : Fin G.numEdges => f_tau (G.computeToMultiEdgeEquiv.symm e).1))

/-- Any `IsWrittenDigraphBD B G.toComputeDigraph t par f_tau` yields a valid branch-decomposition
code `IsValidBranchDecompCode B G (writtenToBDCode G t par f_tau)` of width `≤ B`. -/
theorem isValidBranchDecompCode_writtenToBDCode {n B t : ℕ} (G : MultiDigraph n)
    {par f_tau : ℕ → ℕ}
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau) :
    IsValidBranchDecompCode B G (writtenToBDCode G t par f_tau) := by
  have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
  unfold writtenToBDCode
  split_ifs with hle1
  · exact isValidBranchDecompCode_le_one B G hle1
  · have hge2 : 2 ≤ G.numEdges := by omega
    rcases hbd with ⟨ht_pos, _, hp_lt, _, hle1_c | ⟨htau, hbd_c⟩⟩
    · rw [hm_eq] at hle1_c
      omega
    · let τ_c : Fin G.toComputeDigraph.numEdges → Fin t := fun e => ⟨f_tau e.1, htau e.1 e.2⟩
      let τ_m : Fin G.numEdges → Fin t := τ_c ∘ G.computeToMultiEdgeEquiv.symm
      have hbd_m : IsMultiBranchDecompOfWidthLe B G (parentTree t par) τ_m := by
        rw [← isDigraphBranchDecompOfWidthLe_toComputeDigraph_iff_isMultiBranchDecompOfWidthLe]
        have hcomp : τ_m ∘ G.computeToMultiEdgeEquiv = τ_c := by
          funext e
          dsimp [τ_m]
          rw [Equiv.symm_apply_apply]
        rw [hcomp]
        exact hbd_c
      have ht_le : t ≤ 2 * G.numEdges :=
        t_le_two_mul_numEdges_of_branchDecomp ht_pos hp_lt hbd_m
      let parList := List.ofFn (fun z : Fin t => if z.1 = 0 then 0 else par z.1)
      let tauList := List.ofFn (fun e : Fin G.numEdges => f_tau (G.computeToMultiEdgeEquiv.symm e).1)
      exact isValidBranchDecompCode_of_ge_two B G parList tauList par τ_m hge2 ht_pos ht_le
        (by simp [parList]) (by simp [tauList]) (by simp [parList])
        (fun z hz hz_pos => by simp [parList, Nat.ne_of_gt hz_pos])
        hp_lt
        (fun e => by simp [tauList, τ_m, τ_c])
        hbd_m

/-- Bundle `(G, Z, t, par, f_tau)` with `IsWrittenDigraphBD B G.toComputeDigraph t par f_tau` into
an `Alg41CodeInput ξ B`. -/
noncomputable def writtenToAlg41CodeInput {ξ B n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) (t : ℕ) (par f_tau : ℕ → ℕ)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau) :
    Alg41CodeInput ξ B where
  n := n
  G := G
  Z := Z
  hZ := hZ
  bdCode := writtenToBDCode G t par f_tau
  hbd := isValidBranchDecompCode_writtenToBDCode G hbd

theorem tCode_writtenToAlg41CodeInput_of_lt_two {ξ B n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) (t : ℕ) (par f_tau : ℕ → ℕ)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    (hlt2 : G.numEdges < 2) :
    tCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd) = 1 := by
  have hle1 : G.numEdges ≤ 1 := by omega
  unfold tCode writtenToAlg41CodeInput writtenToBDCode bdNumTreeVerts
  simp [hle1]

theorem ofFn_normParentCode_writtenToAlg41CodeInput_of_lt_two {ξ B n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) (t : ℕ) (par f_tau : ℕ → ℕ)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    (hlt2 : G.numEdges < 2) :
    List.ofFn (normParentCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd)) = [0] := by
  have ht : tCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd) = 1 :=
    tCode_writtenToAlg41CodeInput_of_lt_two G Z hZ t par f_tau hbd hlt2
  set x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
  apply List.ext_getElem (by simp [ht])
  intro i hi1 hi2
  have hi0 : i = 0 := by simp at hi2; omega
  subst hi0
  simp [normParentCode]

theorem ofFn_tauCode_writtenToAlg41CodeInput_of_lt_two {ξ B n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) (t : ℕ) (par f_tau : ℕ → ℕ)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    (hlt2 : G.numEdges < 2) :
    List.ofFn (fun e => (tauCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd) e).1) =
      List.replicate G.numEdges 0 := by
  have hle1 : G.numEdges ≤ 1 := by omega
  set x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
  have hbd0 : bdNumTreeVerts x.bdCode = 0 := by
    dsimp [x, writtenToAlg41CodeInput, writtenToBDCode, bdNumTreeVerts]
    simp [hle1]
  apply List.ext_getElem (by rw [List.length_ofFn, List.length_replicate]; exact G.length_directedEdgesList)
  intro i hi1 hi2
  rw [List.getElem_ofFn, List.getElem_replicate]
  unfold tauCode
  simp [hbd0]

theorem tCode_writtenToAlg41CodeInput_of_ge_two {ξ B n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) (t : ℕ) (par f_tau : ℕ → ℕ)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    (hge2 : 2 ≤ G.numEdges) :
    tCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd) = t := by
  have hnot_le1 : ¬ G.numEdges ≤ 1 := by omega
  have ht_pos : 0 < t := hbd.1
  unfold tCode writtenToAlg41CodeInput writtenToBDCode bdNumTreeVerts encBranchDecomp
  simp [hnot_le1, ht_pos]

theorem ofFn_normParentCode_writtenToAlg41CodeInput_of_ge_two {ξ B n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) (t : ℕ) (par f_tau : ℕ → ℕ)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    (hge2 : 2 ≤ G.numEdges) :
    List.ofFn (normParentCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd)) =
      List.ofFn (fun z : Fin t => if z.1 = 0 then 0 else par z.1) := by
  have hnot_le1 : ¬ G.numEdges ≤ 1 := by omega
  have ht : tCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd) = t :=
    tCode_writtenToAlg41CodeInput_of_ge_two G Z hZ t par f_tau hbd hge2
  set x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
  apply List.ext_getElem (by simp [ht])
  intro z hz1 hz2
  have hz_t : z < t := by simpa using hz2
  rw [List.getElem_ofFn, List.getElem_ofFn]
  unfold normParentCode pCode
  by_cases hz0 : z = 0
  · simp [hz0]
  · have hz_pos : 0 < z := Nat.pos_of_ne_zero hz0
    have hpar_z : bdParent x.bdCode z = par z := by
      dsimp [x, writtenToAlg41CodeInput, writtenToBDCode, bdParent, encBranchDecomp]
      rw [ite_eq_right_iff.mpr (fun h => False.elim (hnot_le1 h)), getD_two_add_cons_cons]
      have hlen_pt : z < (List.ofFn (fun z : Fin t => if z.1 = 0 then 0 else par z.1) ++
          List.ofFn (fun e : Fin G.numEdges => f_tau (G.computeToMultiEdgeEquiv.symm e).1)).length := by
        simp; omega
      rw [list_getD_eq_getElem _ _ _ hlen_pt, List.getElem_append_left (by simp [hz_t])]
      simp [hz0]
    have hlt_z : par z < z := hbd.2.2.1 z hz_pos hz_t
    simp [hz0, hpar_z, hlt_z]

theorem ofFn_tauCode_writtenToAlg41CodeInput_of_ge_two {ξ B n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (hZ : Z.card ≤ ξ) (t : ℕ) (par f_tau : ℕ → ℕ)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    (hge2 : 2 ≤ G.numEdges) :
    List.ofFn (fun e => (tauCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd) e).1) =
      List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => f_tau e.1) := by
  have hnot_le1 : ¬ G.numEdges ≤ 1 := by omega
  have ht_pos : 0 < t := hbd.1
  let x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
  have hbd_t : bdNumTreeVerts x.bdCode = t := by
    dsimp [x, writtenToAlg41CodeInput, writtenToBDCode, bdNumTreeVerts, encBranchDecomp]
    simp [hnot_le1]
  have ht_bd : 0 < bdNumTreeVerts x.bdCode := by rw [hbd_t]; exact ht_pos
  apply List.ext_getElem (by rw [List.length_ofFn, List.length_ofFn]; rfl)
  intro i hi1 hi2
  have hi_m : i < G.toComputeDigraph.numEdges := by simpa using hi2
  let e : Fin G.toComputeDigraph.numEdges := ⟨i, hi_m⟩
  rw [List.getElem_ofFn, List.getElem_ofFn]
  change (tauCode x e).1 = f_tau e.1
  simp only [tauCode, ht_bd, ↓reduceDIte]
  let e' : Fin G.numEdges := G.computeToMultiEdgeEquiv e
  have hget : x.bdCode.getD (2 + bdNumTreeVerts x.bdCode + e'.1) 0 = f_tau e.1 := by
    rw [hbd_t]
    dsimp [e', x, writtenToAlg41CodeInput, writtenToBDCode, encBranchDecomp]
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hnot_le1 h))]
    have hadd : 2 + t + (G.computeToMultiEdgeEquiv e).1 = 2 + (t + (G.computeToMultiEdgeEquiv e).1) := by omega
    rw [hadd, getD_two_add_cons_cons]
    let parList := List.ofFn (fun z : Fin t => if z.1 = 0 then 0 else par z.1)
    let tauList := List.ofFn (fun j : Fin G.numEdges => f_tau (G.computeToMultiEdgeEquiv.symm j).1)
    have hlen_pt : t + (G.computeToMultiEdgeEquiv e).1 < (parList ++ tauList).length := by
      simp [parList, tauList]
    rw [list_getD_eq_getElem (parList ++ tauList) (t + (G.computeToMultiEdgeEquiv e).1) 0 hlen_pt,
        List.getElem_append_right (by simp [parList])]
    have hsub : t + (G.computeToMultiEdgeEquiv e).1 - parList.length = (G.computeToMultiEdgeEquiv e).1 := by
      simp [parList]
    simp only [hsub, tauList, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  have hlt : f_tau e.1 < bdNumTreeVerts x.bdCode := by
    rw [hbd_t]
    exact hbd.2.2.2.1 e.1 e.2
  change (bdTau G x.bdCode ht_bd e').1 = f_tau e.1
  simp only [bdTau, hget, hlt, ↓reduceDIte]

/-! ### Section 2: Word RAM Program `join41Prog` and Execution Proof -/

private theorem arr_add_ne (b : Arr) {i j : ℕ} (h : i ≠ j) : b + i ≠ b + j := by
  dsimp [Arr]; omega

/-- Step 1 of `join41Prog`: normalize `(r_52, b + 2, b + 3)` so that when `r_28 < 2` (`m < 2`),
`r_52 = 1`, `b + 2 = [0]`, and `b + 3 = replicate m 0`; and when `2 ≤ r_28`, `(b + 2)[0] = 0`. -/
def normalizeBD41Prog (b : Arr) : Cmd :=
  .ite (.op .lt (.reg 28) (.const 2))
    (convertBDSmallProg b)
    (.write (b + 2) (.const 0) (.const 0))

theorem normalizeBD41Prog_exec {w ξ B n t : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (hZ : Z.card ≤ ξ) (b : Arr) (par f_tau : ℕ → ℕ)
    (hw2 : 2 < 2 ^ w)
    (hm_w : G.numEdges < 2 ^ w)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    {s : State}
    (hr28 : s.regs 28 = G.numEdges)
    (hr52 : s.regs 52 = t)
    (hb2_len : (s.arrs (b + 2)).length = t)
    (hb2_get : ∀ z < t, (s.arrs (b + 2)).getD z 0 = par z)
    (hb3_len : (s.arrs (b + 3)).length = G.numEdges)
    (hb3_get : ∀ e < G.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) :
    let x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
    ∃ s' time,
      Exec w (normalizeBD41Prog b) s s' time ∧
      time ≤ 8 + G.numEdges ∧
      s'.regs 52 = tCode x ∧
      s'.arrs (b + 2) = List.ofFn (normParentCode x) ∧
      s'.arrs (b + 3) = List.ofFn (fun e => (tauCode x e).1) ∧
      (∀ a : Arr, a ≠ b + 2 → a ≠ b + 3 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 52 → s'.regs r = s.regs r) := by
  set x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  by_cases hm_lt2 : G.numEdges < 2
  · have hcond : (.op .lt (.reg 28) (.const 2) : Expr).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr28, hm_lt2, h1_w, hw2, hm_w]
    let s₁ := s.setReg 52 1
    have hex₁ : Exec w (.assign 52 (.const 1)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, h1_w])
    let s₂ := s₁.setArr (b + 2) (List.replicate 1 0)
    have hex₂ : Exec w (.alloc (b + 2) (.const 1)) s₁ s₂ (1 + 1) :=
      .alloc (by simp [Expr.eval, checkWord, h1_w])
    let s₃ := s₂.setArr (b + 3) (List.replicate G.numEdges 0)
    have hex₃ : Exec w (.alloc (b + 3) (.reg 28)) s₂ s₃ (1 + G.numEdges) :=
      .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hr28, hm_w])
    have hex_small : Exec w (convertBDSmallProg b) s s₃ (2 + ((1 + 1) + (1 + G.numEdges))) :=
      .seq hex₁ (.seq hex₂ hex₃)
    have hex_ite : Exec w (normalizeBD41Prog b) s s₃ (3 + (2 + ((1 + 1) + (1 + G.numEdges)))) :=
      .ite_true hcond (by decide) hex_small
    refine ⟨s₃, 3 + (2 + ((1 + 1) + (1 + G.numEdges))), hex_ite, by omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [tCode_writtenToAlg41CodeInput_of_lt_two G Z hZ t par f_tau hbd hm_lt2]
      simp [s₃, s₂, s₁]
    · rw [ofFn_normParentCode_writtenToAlg41CodeInput_of_lt_two G Z hZ t par f_tau hbd hm_lt2]
      simp [s₃, s₂]
    · rw [ofFn_tauCode_writtenToAlg41CodeInput_of_lt_two G Z hZ t par f_tau hbd hm_lt2]
      simp [s₃]
    · intro a ha2 ha3
      simp [s₃, s₂, s₁, ha2, ha3]
    · intro r hr52'
      simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr52']
  · have hm_ge2 : 2 ≤ G.numEdges := by omega
    have hcond : (.op .lt (.reg 28) (.const 2) : Expr).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr28, hm_lt2, h0_w, hw2, hm_w]
    have ht_pos : 0 < t := hbd.1
    let s₁ := s.writeArr (b + 2) 0 0
    have hex_w : Exec w (.write (b + 2) (.const 0) (.const 0)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, h0_w])
        (by simp [Expr.eval, checkWord, h0_w])
        (by rw [hb2_len]; exact ht_pos)
    have hex_ite : Exec w (normalizeBD41Prog b) s s₁ (3 + 3) :=
      .ite_false hcond hex_w
    have hm_eq : G.toComputeDigraph.numEdges = G.numEdges := G.length_directedEdgesList
    refine ⟨s₁, 3 + 3, hex_ite, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tCode_writtenToAlg41CodeInput_of_ge_two G Z hZ t par f_tau hbd hm_ge2]
      exact hr52
    · rw [ofFn_normParentCode_writtenToAlg41CodeInput_of_ge_two G Z hZ t par f_tau hbd hm_ge2]
      simp only [s₁, State.writeArr_arrs_self]
      apply List.ext_getElem (by simp [hb2_len])
      intro z hz1 hz2
      have hz_t : z < t := by simpa using hz2
      rw [List.getElem_ofFn]
      by_cases hz0 : z = 0
      · subst hz0
        simp
      · rw [List.getElem_set_ne (Ne.symm hz0)]
        have h1 : (s.arrs (b + 2))[z]'(by rw [hb2_len]; exact hz_t) = (s.arrs (b + 2)).getD z 0 :=
          List.getElem_eq_getD (fallback := 0)
        rw [h1, hb2_get z hz_t]
        simp [hz0]
    · rw [ofFn_tauCode_writtenToAlg41CodeInput_of_ge_two G Z hZ t par f_tau hbd hm_ge2]
      have hs₁_b3 : s₁.arrs (b + 3) = s.arrs (b + 3) := by simp [s₁, State.writeArr]
      rw [hs₁_b3]
      exact eq_ofFn_of_getD_eq (by rw [hm_eq]; exact hb3_len)
        (fun e he => hb3_get e (by rw [← hm_eq]; exact he))
    · intro a ha2 _
      simp [s₁, ha2]
    · intro r _
      rfl

/-- Append the first `r_len` words of `a_src` into `a_dst` starting at cursor `r_57`, advancing
`r_57` by `r_len` (using `r_55` as loop counter and `r_56` as scratch word register). -/
def appendSliceProg (a_src a_dst : Arr) (r_len : Reg) : Cmd :=
  .seq (.assign 55 (.const 0))
    (forUp 55 (.reg r_len)
      (.seq (.assign 56 (.read a_src (.reg 55)))
        (.seq (.write a_dst (.reg 57) (.reg 56))
          (.assign 57 (.op .add (.reg 57) (.const 1))))))

theorem list_set_append_replicate_zero (L_pre L_seg : List ℕ) (c L_rem : ℕ)
    (hc : c < L_seg.length) :
    (L_pre ++ L_seg.take c ++ List.replicate (L_seg.length - c + L_rem) 0).set
      (L_pre.length + c) (L_seg[c]'hc) =
      L_pre ++ L_seg.take (c + 1) ++ List.replicate (L_seg.length - (c + 1) + L_rem) 0 := by
  have htake_len : (L_seg.take c).length = c := List.length_take_of_le (Nat.le_of_lt hc)
  have hpre_len : (L_pre ++ L_seg.take c).length = L_pre.length + c := by
    rw [List.length_append, htake_len]
  rw [List.set_append_right _ _ (by rw [hpre_len]), hpre_len, Nat.sub_self]
  have hrep_split :
      List.replicate (L_seg.length - c + L_rem) 0 =
        0 :: List.replicate (L_seg.length - (c + 1) + L_rem) 0 := by
    have h1 : L_seg.length - c + L_rem = (L_seg.length - (c + 1) + L_rem) + 1 := by omega
    rw [h1, List.replicate_succ]
  rw [hrep_split]
  simp only [List.set_cons_zero]
  have htake_succ : L_seg.take (c + 1) = L_seg.take c ++ [L_seg[c]'hc] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hc, Option.toList_some]
  rw [htake_succ]
  simp only [List.append_assoc, List.singleton_append]

theorem appendSliceProg_exec {w : ℕ} (L_pre L_seg : List ℕ) (L_rem : ℕ)
    (a_src a_dst : Arr) (r_len : Reg)
    (hne : a_src ≠ a_dst)
    (hr55 : r_len ≠ 55) (hr56 : r_len ≠ 56) (hr57 : r_len ≠ 57)
    (hw : 1 < 2 ^ w)
    (htot_w : L_pre.length + L_seg.length + L_rem < 2 ^ w)
    (hseg_w : ∀ u ∈ L_seg, u < 2 ^ w)
    {s : State}
    (hr_len : s.regs r_len = L_seg.length)
    (hr57_val : s.regs 57 = L_pre.length)
    (hsrc : s.arrs a_src = L_seg)
    (hdst : s.arrs a_dst = L_pre ++ List.replicate (L_seg.length + L_rem) 0) :
    ∃ s' t,
      Exec w (appendSliceProg a_src a_dst r_len) s s' t ∧
      t ≤ 17 * L_seg.length + 5 ∧
      s'.arrs a_dst = L_pre ++ L_seg ++ List.replicate L_rem 0 ∧
      s'.regs 57 = L_pre.length + L_seg.length ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 55 → r ≠ 56 → r ≠ 57 → s'.regs r = s.regs r) := by
  set k := L_seg.length
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  let s₁ := s.setReg 55 0
  have hex₁ : Exec w (.assign 55 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (c : ℕ) (st : State) : Prop :=
    c ≤ k ∧
    st.arrs a_dst = L_pre ++ L_seg.take c ++ List.replicate (k - c + L_rem) 0 ∧
    st.regs r_len = k ∧
    st.regs 55 = c ∧
    st.regs 57 = L_pre.length + c ∧
    (∀ a : Arr, a ≠ a_dst → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ 55 → r ≠ 56 → r ≠ 57 → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₁ :=
    ⟨Nat.zero_le k,
     by simp [s₁, hdst],
     by simp [s₁, State.setReg_regs_ne _ _ hr55, hr_len],
     by simp [s₁],
     by simp [s₁, hr57_val],
     fun a _ => by simp [s₁],
     fun r hr1 _ _ => by simp [s₁, State.setReg_regs_ne _ _ hr1]⟩
  have hLoop :
      ⦃Inv 0⦄[w] forUp 55 (.reg r_len)
        (.seq (.assign 56 (.read a_src (.reg 55)))
          (.seq (.write a_dst (.reg 57) (.reg 56))
            (.assign 57 (.op .add (.reg 57) (.const 1))))) ⦃Inv k⦄ ≤
        fun _ => 3 + k * (7 + 10) := by
    apply Triple.forUp_const Inv k 10 hw hk_w
    · intro c _ st ⟨_, _, hrk, hr55_c, _, _, _⟩
      exact ⟨hr55_c, by simp [Expr.eval, checkWord, hrk, hk_w]⟩
    · intro c hc st ⟨_, hdst_c, hrk, hr55_c, hr57_c, harr_c, hreg_c⟩
      have hc_w : c < 2 ^ w := by omega
      have hpos_w : L_pre.length + c < 2 ^ w := by omega
      have hpos1_w : L_pre.length + c + 1 < 2 ^ w := by omega
      have hsrc_eq : st.arrs a_src = L_seg := (harr_c a_src hne).trans hsrc
      have hc_src : c < (st.arrs a_src).length := by rw [hsrc_eq]; exact hc
      have hval_eq : (st.arrs a_src).getD c 0 = L_seg[c]'hc := by
        simp [hsrc_eq, List.getD, List.getElem?_eq_getElem hc]
      have hval_w : (st.arrs a_src).getD c 0 < 2 ^ w := by
        rw [hval_eq]
        exact hseg_w (L_seg[c]'hc) (List.getElem_mem hc)
      let st₁ := st.setReg 56 (L_seg[c]'hc)
      have hex_r : Exec w (.assign 56 (.read a_src (.reg 55))) st st₁ 3 :=
        exec_assign_read_getD 56 a_src 55 hr55_c hc_w hc_src hval_eq (by rw [← hval_eq]; exact hval_w)
      have hc_dst : L_pre.length + c < (st₁.arrs a_dst).length := by
        change L_pre.length + c < (st.arrs a_dst).length
        rw [hdst_c]
        simp only [List.length_append, List.length_take_of_le (Nat.le_of_lt hc), List.length_replicate]
        omega
      let st₂ := st₁.writeArr a_dst (L_pre.length + c) (L_seg[c]'hc)
      have hex_w : Exec w (.write a_dst (.reg 57) (.reg 56)) st₁ st₂ 3 :=
        exec_write_reg a_dst 57 56 (by simp [st₁, hr57_c]) (by simp [st₁]) hpos_w
          (by rw [← hval_eq]; exact hval_w) hc_dst
      let st₃ := st₂.setReg 57 (L_pre.length + c + 1)
      have hex_inc : Exec w (.assign 57 (.op .add (.reg 57) (.const 1))) st₂ st₃ 4 :=
        .assign (by simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hr57_c, hpos_w, hw, hpos1_w])
      refine ⟨st₃, 10, .seq hex_r (.seq hex_w hex_inc), le_refl 10,
        ⟨by omega,
         ?_,
         by simp [st₃, st₂, st₁, State.setReg_regs_ne _ _ hr55, State.setReg_regs_ne _ _ hr56,
           State.setReg_regs_ne _ _ hr57, hrk],
         by simp [st₃],
         by simp [st₃, Nat.add_assoc],
         fun a ha => by simp [st₃, st₂, st₁, ha, harr_c a ha],
         fun r hr1 hr2 hr3 => by
           simp [st₃, st₂, st₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2,
             State.setReg_regs_ne _ _ hr3, hreg_c r hr1 hr2 hr3]⟩,
        by simp [st₃, st₂, st₁, hr55_c]⟩
      simp only [st₃, st₂, st₁, State.setReg_arrs, State.writeArr_arrs_self]
      rw [hdst_c]
      exact list_set_append_replicate_zero L_pre L_seg c L_rem hc
  rcases hLoop s₁ hInv₀ with ⟨s₂, t₂, hex₂, ht₂, _, hdst₂, _, _, hr57_2, harr₂, hreg₂⟩
  dsimp only at ht₂
  have htake_full : L_seg.take k = L_seg := List.take_of_length_le (le_refl _)
  have hsub_zero : k - k + L_rem = L_rem := by omega
  rw [htake_full, hsub_zero] at hdst₂
  exact ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hdst₂, hr57_2, harr₂, hreg₂⟩

/-- Step 2 of `join41Prog`: allocate `inArr` (`arrs 0`) of length `3 + 3 * r_28 + r_26 + r_52`,
write `[r_26, r_28, r_52]` at indices `0, 1, 2`, and append `b + 6` (`head`), `b + 5` (`tail`),
`b + 1` (`bitSetList Z`), `b + 2` (`normParentCode`), and `b + 3` (`tauCode`) into `inArr`. -/
def packAlg41InProg (b : Arr) : Cmd :=
  .seq (.assign 55 (.op .add (.const 3)
      (.op .add (.op .mul (.const 3) (.reg 28))
        (.op .add (.reg 26) (.reg 52)))))
    (.seq (.alloc inArr (.reg 55))
      (.seq (.write inArr (.const 0) (.reg 26))
        (.seq (.write inArr (.const 1) (.reg 28))
          (.seq (.write inArr (.const 2) (.reg 52))
            (.seq (.assign 57 (.const 3))
              (.seq (appendSliceProg (b + 6) inArr 28)
                (.seq (appendSliceProg (b + 5) inArr 28)
                  (.seq (appendSliceProg (b + 1) inArr 26)
                    (.seq (appendSliceProg (b + 2) inArr 52)
                      (appendSliceProg (b + 3) inArr 28))))))))))

theorem packAlg41InProg_exec {w ξ B n t : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (hZ : Z.card ≤ ξ) (p : ℕ) (par f_tau : ℕ → ℕ)
    (hw3 : 3 < 2 ^ w)
    (hsz_w : 5 * (G.numEdges + n + 1) < 2 ^ w)
    (hbd : IsWrittenDigraphBD B G.toComputeDigraph t par f_tau)
    {s : State}
    (hr26 : s.regs 26 = n)
    (hr28 : s.regs 28 = G.numEdges)
    (hr52 : s.regs 52 = tCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd))
    (hb1 : s.arrs (alg105ArrBase p + 1) = bitSetList Z)
    (hb2 : s.arrs (alg105ArrBase p + 2) =
      List.ofFn (normParentCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd)))
    (hb3 : s.arrs (alg105ArrBase p + 3) =
      List.ofFn (fun e => (tauCode (writtenToAlg41CodeInput G Z hZ t par f_tau hbd) e).1))
    (hb5 : s.arrs (alg105ArrBase p + 5) =
      List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.tail e).1))
    (hb6 : s.arrs (alg105ArrBase p + 6) =
      List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.head e).1)) :
    let x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
    ∃ s' time,
      Exec w (packAlg41InProg (alg105ArrBase p)) s s' time ∧
      time ≤ 150 * (n + G.numEdges + 1) ∧
      s'.arrs inArr = encAlg41CodeIn x := by
  set x := writtenToAlg41CodeInput G Z hZ t par f_tau hbd
  set b := alg105ArrBase p
  set m := G.numEdges
  set tc := tCode x
  have hm_eq : G.toComputeDigraph.numEdges = m := G.length_directedEdgesList
  have htc_le : tc ≤ 2 * m + 1 := tCode_le x
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have htc_w : tc < 2 ^ w := by omega
  have h3m_w : 3 * m < 2 ^ w := by omega
  have hntc_w : n + tc < 2 ^ w := by omega
  have h3m_ntc_w : 3 * m + (n + tc) < 2 ^ w := by omega
  have htot_w : 3 + (3 * m + (n + tc)) < 2 ^ w := by omega
  set tot := 3 + (3 * m + (n + tc))
  -- 1. Compute `r_55 := tot` and allocate `inArr`
  let s₁ := s.setReg 55 tot
  have hex₁ : Exec w (.assign 55 (.op .add (.const 3)
      (.op .add (.op .mul (.const 3) (.reg 28))
        (.op .add (.reg 26) (.reg 52))))) s s₁ 10 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr28, hr26, hr52, hw3, hm_w, hn_w, htc_w, h3m_w, hntc_w, h3m_ntc_w, htot_w, tot])
  let s₂ := s₁.setArr inArr (List.replicate tot 0)
  have hex₂ : Exec w (.alloc inArr (.reg 55)) s₁ s₂ (1 + tot) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, htot_w])
  -- 2. Write `[n, m, tc]` at indices `0, 1, 2` and set `r_57 := 3`
  let s₃ := s₂.writeArr inArr 0 n
  have hex₃ : Exec w (.write inArr (.const 0) (.reg 26)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₂, s₁, Expr.eval, checkWord, hr26, hn_w])
      (by simp [s₂, tot])
  let s₄ := s₃.writeArr inArr 1 m
  have hex₄ : Exec w (.write inArr (.const 1) (.reg 28)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h1_w])
      (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr28, hm_w])
      (by simp [s₃, s₂, tot]; omega)
  let s₅ := s₄.writeArr inArr 2 tc
  have hex₅ : Exec w (.write inArr (.const 2) (.reg 52)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, h2_w])
      (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr52, htc_w])
      (by simp [s₄, s₃, s₂, tot]; omega)
  let s₆ := s₅.setReg 57 3
  have hex₆ : Exec w (.assign 57 (.const 3)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw3])
  let L_hdr : List ℕ := [n, m, tc]
  let L_head : List ℕ := List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.head e).1)
  let L_tail : List ℕ := List.ofFn (fun e : Fin G.toComputeDigraph.numEdges => (G.toComputeDigraph.tail e).1)
  let L_Z : List ℕ := bitSetList Z
  let L_par : List ℕ := List.ofFn (normParentCode x)
  let L_tau : List ℕ := List.ofFn (fun e => (tauCode x e).1)
  have hlen_head : L_head.length = m := by simp [L_head, m]
  have hlen_tail : L_tail.length = m := by simp [L_tail, m]
  have hlen_Z : L_Z.length = n := length_bitSetList Z
  have hlen_par : L_par.length = tc := by simp [L_par, tc]
  have hlen_tau : L_tau.length = m := by simp [L_tau, x, writtenToAlg41CodeInput, m]
  have hin₆ : s₆.arrs inArr = L_hdr ++ List.replicate (L_head.length + (m + n + tc + m)) 0 := by
    have htot_eq : tot = (L_head.length + (m + n + tc + m)) + 3 := by
      rw [hlen_head]; dsimp [tot]; omega
    change (((List.replicate tot 0).set 0 n).set 1 m).set 2 tc =
      [n, m, tc] ++ List.replicate (L_head.length + (m + n + tc + m)) 0
    rw [htot_eq]
    rfl
  have hhead_w : ∀ u ∈ L_head, u < 2 ^ w := by
    intro u hu
    rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩
    exact Nat.lt_trans (G.toComputeDigraph.head e).2 hn_w
  have htail_w : ∀ u ∈ L_tail, u < 2 ^ w := by
    intro u hu
    rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩
    exact Nat.lt_trans (G.toComputeDigraph.tail e).2 hn_w
  have hZ_w : ∀ u ∈ L_Z, u < 2 ^ w := by
    intro u hu
    dsimp [L_Z] at hu
    rcases List.getElem_of_mem hu with ⟨i, hi, rfl⟩
    have := getElem_bitSetList_le_one Z i hi
    omega
  have hpar_w : ∀ u ∈ L_par, u < 2 ^ w := by
    intro u hu
    rcases List.mem_ofFn.mp hu with ⟨z, rfl⟩
    exact Nat.lt_trans (normParentCode_lt x z) htc_w
  have htau_w : ∀ u ∈ L_tau, u < 2 ^ w := by
    intro u hu
    rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩
    exact Nat.lt_trans (tauCode x e).2 htc_w
  have hne1 : b + 1 ≠ inArr := by dsimp [b, alg105ArrBase, inArr, Arr]; omega
  have hne2 : b + 2 ≠ inArr := by dsimp [b, alg105ArrBase, inArr, Arr]; omega
  have hne3 : b + 3 ≠ inArr := by dsimp [b, alg105ArrBase, inArr, Arr]; omega
  have hne5 : b + 5 ≠ inArr := by dsimp [b, alg105ArrBase, inArr, Arr]; omega
  have hne6 : b + 6 ≠ inArr := by dsimp [b, alg105ArrBase, inArr, Arr]; omega
  have hs6_arr : ∀ a : Arr, a ≠ inArr → s₆.arrs a = s.arrs a := by
    intro a ha
    simp [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr, ha]
  -- 3. Append `b + 6` (`L_head`)
  rcases appendSliceProg_exec L_hdr L_head (m + n + tc + m) (b + 6) inArr 28
      hne6 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head]; omega) hhead_w (s := s₆)
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hr28, hlen_head, m])
      (by simp [s₆, L_hdr])
      ((hs6_arr (b + 6) hne6).trans hb6)
      hin₆ with
    ⟨s₇, t₇, hex₇, ht₇, hin₇, hr57_7, harr₇, hreg₇⟩
  -- 4. Append `b + 5` (`L_tail`)
  have hin₇' : s₇.arrs inArr = (L_hdr ++ L_head) ++ List.replicate (L_tail.length + (n + tc + m)) 0 := by
    rw [hin₇, hlen_tail, show m + n + tc + m = m + (n + tc + m) by omega]
  rcases appendSliceProg_exec (L_hdr ++ L_head) L_tail (n + tc + m) (b + 5) inArr 28
      hne5 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail]; omega) htail_w (s := s₇)
      (by rw [hreg₇ 28 (by decide) (by decide) (by decide)]; simp [s₆, s₅, s₄, s₃, s₂, s₁, hr28, hlen_tail, m])
      (by rw [hr57_7]; simp)
      ((harr₇ (b + 5) hne5).trans ((hs6_arr (b + 5) hne5).trans hb5))
      hin₇' with
    ⟨s₈, t₈, hex₈, ht₈, hin₈, hr57_8, harr₈, hreg₈⟩
  -- 5. Append `b + 1` (`L_Z`)
  have hin₈' : s₈.arrs inArr = (L_hdr ++ L_head ++ L_tail) ++ List.replicate (L_Z.length + (tc + m)) 0 := by
    rw [hin₈, hlen_Z, Nat.add_assoc]
  rcases appendSliceProg_exec (L_hdr ++ L_head ++ L_tail) L_Z (tc + m) (b + 1) inArr 26
      hne1 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail, hlen_Z]; omega) hZ_w (s := s₈)
      (by rw [hreg₈ 26 (by decide) (by decide) (by decide), hreg₇ 26 (by decide) (by decide) (by decide)];
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hr26, hlen_Z])
      (by rw [hr57_8]; simp; omega)
      ((harr₈ (b + 1) hne1).trans ((harr₇ (b + 1) hne1).trans ((hs6_arr (b + 1) hne1).trans hb1)))
      hin₈' with
    ⟨s₉, t₉, hex₉, ht₉, hin₉, hr57_9, harr₉, hreg₉⟩
  -- 6. Append `b + 2` (`L_par`)
  have hin₉' : s₉.arrs inArr = (L_hdr ++ L_head ++ L_tail ++ L_Z) ++ List.replicate (L_par.length + m) 0 := by
    rw [hin₉, hlen_par]
  rcases appendSliceProg_exec (L_hdr ++ L_head ++ L_tail ++ L_Z) L_par m (b + 2) inArr 52
      hne2 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail, hlen_Z, hlen_par]; omega) hpar_w (s := s₉)
      (by rw [hreg₉ 52 (by decide) (by decide) (by decide),
              hreg₈ 52 (by decide) (by decide) (by decide),
              hreg₇ 52 (by decide) (by decide) (by decide)];
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hr52, hlen_par, tc])
      (by rw [hr57_9]; simp; omega)
      ((harr₉ (b + 2) hne2).trans ((harr₈ (b + 2) hne2).trans
        ((harr₇ (b + 2) hne2).trans ((hs6_arr (b + 2) hne2).trans hb2))))
      hin₉' with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hin₁₀, hr57_10, harr₁₀, hreg₁₀⟩
  -- 7. Append `b + 3` (`L_tau`)
  have hin₁₀' : s₁₀.arrs inArr = (L_hdr ++ L_head ++ L_tail ++ L_Z ++ L_par) ++ List.replicate (L_tau.length + 0) 0 := by
    rw [hin₁₀, hlen_tau, Nat.add_zero]
  rcases appendSliceProg_exec (L_hdr ++ L_head ++ L_tail ++ L_Z ++ L_par) L_tau 0 (b + 3) inArr 28
      hne3 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail, hlen_Z, hlen_par, hlen_tau]; omega) htau_w (s := s₁₀)
      (by rw [hreg₁₀ 28 (by decide) (by decide) (by decide),
              hreg₉ 28 (by decide) (by decide) (by decide),
              hreg₈ 28 (by decide) (by decide) (by decide),
              hreg₇ 28 (by decide) (by decide) (by decide)];
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hr28, hlen_tau, m])
      (by rw [hr57_10]; simp; omega)
      ((harr₁₀ (b + 3) hne3).trans ((harr₉ (b + 3) hne3).trans ((harr₈ (b + 3) hne3).trans
        ((harr₇ (b + 3) hne3).trans ((hs6_arr (b + 3) hne3).trans hb3)))))
      hin₁₀' with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hin₁₁, _, _, _⟩
  rw [List.replicate_zero, List.append_nil] at hin₁₁
  have henc_eq : L_hdr ++ L_head ++ L_tail ++ L_Z ++ L_par ++ L_tau = encAlg41CodeIn x := by
    simp [encAlg41CodeIn, L_hdr, L_head, L_tail, L_Z, L_par, L_tau, x, writtenToAlg41CodeInput, m, tc]
  rw [henc_eq] at hin₁₁
  rw [hlen_head] at ht₇
  rw [hlen_tail] at ht₈
  rw [hlen_Z] at ht₉
  rw [hlen_par] at ht₁₀
  rw [hlen_tau] at ht₁₁
  refine ⟨s₁₁,
    10 + ((1 + tot) + (3 + (3 + (3 + (2 + (t₇ + (t₈ + (t₉ + (t₁₀ + t₁₁))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    by dsimp [tot]; omega,
    hin₁₁⟩

/-- Complete Word RAM join program for Step (2) of Algorithm (10.5) calling Algorithm (4.1):
1. Normalizes the written branch-decomposition in `(r_52, b + 2, b + 3)` (`normalizeBD41Prog b`),
2. Packs the input into `inArr` as `encAlg41CodeIn x` (`packAlg41InProg b`),
3. Runs `alg41Prog δ ξ B` (`Algorithm41.lean`). -/
def join41Prog (p ξ δ B : ℕ) : Cmd :=
  let b := alg105ArrBase p
  .seq (normalizeBD41Prog b)
    (.seq (packAlg41InProg b)
      (alg41Prog δ ξ B))

theorem join41Prog_exec {w p ξ δ B n_i t : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
    (par f_tau : ℕ → ℕ)
    (hw : wordSize (B_word41 δ ξ B + 3) (n_i + G_i.numEdges + 1) ≤ w)
    (hZ : Z_i.card ≤ ξ)
    (hbd : IsWrittenDigraphBD B G_i.toComputeDigraph t par f_tau)
    {s : State}
    (hb1 : s.arrs (alg105ArrBase p + 1) = bitSetList Z_i)
    (hr26 : s.regs 26 = n_i)
    (hr28 : s.regs 28 = G_i.numEdges)
    (hr52 : s.regs 52 = t)
    (hb2_len : (s.arrs (alg105ArrBase p + 2)).length = t)
    (hb2_get : ∀ z < t, (s.arrs (alg105ArrBase p + 2)).getD z 0 = par z)
    (hb3_len : (s.arrs (alg105ArrBase p + 3)).length = G_i.numEdges)
    (hb3_get : ∀ e < G_i.numEdges, (s.arrs (alg105ArrBase p + 3)).getD e 0 = f_tau e)
    (hb5 : s.arrs (alg105ArrBase p + 5) =
      List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1))
    (hb6 : s.arrs (alg105ArrBase p + 6) =
      List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1)) :
    let x := writtenToAlg41CodeInput G_i Z_i hZ t par f_tau hbd
    ∃ s' time,
      Exec w (join41Prog p ξ δ B) s s' time ∧
      time ≤ (250 + C_core41 δ ξ B) * (n_i + G_i.numEdges + 1) ∧
      IsValidAlg41ReadCodeOutput δ x (decAlg41CodeOut δ x (s'.arrs outArr)) := by
  set x := writtenToAlg41CodeInput G_i Z_i hZ t par f_tau hbd
  set b := alg105ArrBase p
  let N := n_i + G_i.numEdges + 1
  have hw_pack : wordSize 3 N ≤ w :=
    (wordSize_mono_left (show 3 ≤ B_word41 δ ξ B + 3 by omega) N).trans hw
  have hpow_w : (N + 2) ^ 3 < 2 ^ w :=
    Nat.lt_of_lt_of_le (pow_lt_two_pow_wordSize (c := 3) (by omega) N)
      (Nat.pow_le_pow_right (by omega) hw_pack)
  have hN_pos : 1 ≤ N := by dsimp [N]; omega
  have hpow_expand : 5 * (G_i.numEdges + n_i + 1) + 2 < (N + 2) ^ 3 := by
    have hcube : (N + 2) ^ 3 = (N + 2) * ((N + 2) * (N + 2)) := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, Nat.pow_succ, Nat.pow_two, Nat.mul_comm]
    have hge3 : 3 * ((N + 2) * (N + 2)) ≤ (N + 2) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_right _ (by omega : 3 ≤ N + 2)
    have hsq : 2 * N + 4 ≤ (N + 2) * (N + 2) := by
      rw [Nat.add_mul, Nat.mul_add]; omega
    dsimp [N] at *; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hm_w : G_i.numEdges < 2 ^ w := by dsimp [N] at *; omega
  have hsz_w : 5 * (G_i.numEdges + n_i + 1) < 2 ^ w := by omega
  -- 1. Normalize `(r_52, b + 2, b + 3)`
  rcases normalizeBD41Prog_exec G_i Z_i hZ b par f_tau hw2 hm_w hbd
      hr28 hr52 hb2_len hb2_get hb3_len hb3_get with
    ⟨s₁, t₁, hex₁, ht₁, hr52_1, hb2_1, hb3_1, harr₁, hreg₁⟩
  -- 2. Pack `encAlg41CodeIn x` into `inArr`
  rcases packAlg41InProg_exec G_i Z_i hZ p par f_tau hw3 hsz_w hbd
      ((hreg₁ 26 (by decide)).trans hr26)
      ((hreg₁ 28 (by decide)).trans hr28)
      hr52_1
      ((harr₁ (b + 1) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))).trans hb1)
      hb2_1 hb3_1
      ((harr₁ (b + 5) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))).trans hb5)
      ((harr₁ (b + 6) (arr_add_ne b (by decide)) (arr_add_ne b (by decide))).trans hb6) with
    ⟨s₂, t₂, hex₂, ht₂, hin₂⟩
  have hsz_eq : alg41CodeSize x = G_i.numEdges + n_i + 1 := rfl
  have hcore_word : wordSize (B_word41 δ ξ B + 1) (alg41CodeSize x) ≤ w := by
    rw [hsz_eq, Nat.add_comm G_i.numEdges n_i]
    exact (wordSize_mono_left (by omega) N).trans hw
  rcases alg41CodeProg_exec (δ := δ) x hin₂ with ⟨s₃, t₃, hex₃, ht₃, hvalid₃⟩
  rw [hsz_eq, Nat.add_comm G_i.numEdges n_i] at ht₃
  refine ⟨s₃, t₁ + (t₂ + t₃),
    .seq hex₁ (.seq hex₂ (hex₃.mono_wordSize hcore_word)), ?_, hvalid₃⟩
  rw [Nat.add_mul]
  omega

/-- **Proof of `Alg105.Alg41Spec` from `algorithm_4_1_code` (`alg41Prog`):**
For all `p, ξ, δ, B : ℕ`, `join41Prog p ξ δ B` satisfies `Alg105.Alg41Spec p ξ δ B` in time
`O(v + ε)` (`(250 + C_core41 δ ξ B) * (n_i + G_i.numEdges + 1)`). -/
theorem alg41Spec_proved (p ξ δ B : ℕ) : Alg105.Alg41Spec p ξ δ B := by
  refine ⟨join41Prog p ξ δ B, 250 + C_core41 δ ξ B, B_word41 δ ξ B + 3, by omega, by omega,
    fun {w n_i} G_i Z_i t par f_tau s hw hZ hbd _ hb1 hr26 hr28 hr52
      hb2_len hb2_get hb3_len hb3_get hb5 hb6 => ?_⟩
  rcases join41Prog_exec G_i Z_i par f_tau hw hZ hbd hb1 hr26 hr28 hr52
      hb2_len hb2_get hb3_len hb3_get hb5 hb6 with
    ⟨s', time, hex, htime, hvalid⟩
  exact ⟨s', time, writtenToBDCode G_i t par f_tau, isValidBranchDecompCode_writtenToBDCode G_i hbd,
    hex, htime, hvalid⟩

end GraphMinor.Compute
