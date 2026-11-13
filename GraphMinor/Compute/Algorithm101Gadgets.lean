module

public import GraphMinor.Compute.Algorithm101Stream

/-!
# Wall Section Stream Reader and Subset Indicator Builder for Algorithm (10.1) and (10.4)

This file implements and verifies the wall-section stream parser `readWallSectionProg` and the
generic wall vertex subset indicator builder `buildWallSubsetBitSetProg` used by Algorithm (10.1)
and Algorithm (10.4).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph


/-! ### Section 2: Wall Section Stream Reader and Subset Indicator Builder -/

/-- Index `u + 1` of the branch vertex `W.branchVert u = v` (`0` if `v` is not a branch vertex). -/
def wallBrOf {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) (v : Fin n) : ℕ :=
  match (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | some u => u.1 + 1
  | none => 0

/-- Index `k + 1` of the subdivision edge `v ∈ W.internalVerts k` (`0` if `v` is not an internal
subdivision vertex). -/
def wallEdgeOf {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) (v : Fin n) : ℕ :=
  match (List.finRange (elemWallEdges h).length).find? (fun k => decide (v ∈ W.internalVerts k)) with
  | some k => k.1 + 1
  | none => 0

theorem wallBrOf_eq_succ_iff {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid) (v : Fin n) (u : Fin (elemWallNumVerts h)) :
    wallBrOf W v = u.1 + 1 ↔ W.branchVert u = v := by
  unfold wallBrOf
  cases hfind : (List.finRange (elemWallNumVerts h)).find?
      (fun u' => decide (W.branchVert u' = v)) with
  | none =>
    dsimp only
    refine ⟨by omega, fun heq => ?_⟩
    have hfalse := List.find?_eq_none.mp hfind u (List.mem_finRange u)
    simp [heq] at hfalse
  | some u' =>
    dsimp only
    have hu' : W.branchVert u' = v := by simpa using List.find?_some hfind
    constructor
    · intro heq
      have hu_eq : u' = u := Fin.ext (by omega)
      rwa [← hu_eq]
    · intro heq
      have hu_eq : u' = u := hW.1 (hu'.trans heq.symm)
      rw [hu_eq]

theorem wallBrOf_eq_zero_iff {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (v : Fin n) :
    wallBrOf W v = 0 ↔ ∀ u : Fin (elemWallNumVerts h), W.branchVert u ≠ v := by
  unfold wallBrOf
  cases hfind : (List.finRange (elemWallNumVerts h)).find?
      (fun u' => decide (W.branchVert u' = v)) with
  | none =>
    dsimp only
    simp only [true_iff]
    intro u heq
    have hfalse := List.find?_eq_none.mp hfind u (List.mem_finRange u)
    simp [heq] at hfalse
  | some u' =>
    dsimp only
    have hu' : W.branchVert u' = v := by simpa using List.find?_some hfind
    refine ⟨by omega, fun hall => (hall u' hu').elim⟩

theorem wallBrOf_le {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) (v : Fin n) :
    wallBrOf W v ≤ elemWallNumVerts h := by
  unfold wallBrOf
  cases (List.finRange (elemWallNumVerts h)).find? (fun u => decide (W.branchVert u = v)) with
  | none => exact Nat.zero_le _
  | some u => exact u.2

theorem wallEdgeOf_eq_succ_iff {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid) (v : Fin n)
    (k : Fin (elemWallEdges h).length) :
    wallEdgeOf W v = k.1 + 1 ↔ v ∈ W.internalVerts k := by
  unfold wallEdgeOf
  cases hfind : (List.finRange (elemWallEdges h).length).find?
      (fun k' => decide (v ∈ W.internalVerts k')) with
  | none =>
    dsimp only
    refine ⟨by omega, fun hmem => ?_⟩
    have hfalse := List.find?_eq_none.mp hfind k (List.mem_finRange k)
    simp [hmem] at hfalse
  | some k' =>
    dsimp only
    have hk' : v ∈ W.internalVerts k' := by simpa using List.find?_some hfind
    constructor
    · intro heq
      have hk_eq : k' = k := Fin.ext (by omega)
      rwa [← hk_eq]
    · intro hmem
      by_contra hne
      have hk_ne : k' ≠ k := fun h => hne (by rw [h])
      exact hW.2.2.2 k' k hk_ne hk' hmem

theorem wallEdgeOf_eq_zero_iff {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (v : Fin n) :
    wallEdgeOf W v = 0 ↔ ∀ k : Fin (elemWallEdges h).length, v ∉ W.internalVerts k := by
  unfold wallEdgeOf
  cases hfind : (List.finRange (elemWallEdges h).length).find?
      (fun k' => decide (v ∈ W.internalVerts k')) with
  | none =>
    dsimp only
    simp only [true_iff]
    intro k hmem
    have hfalse := List.find?_eq_none.mp hfind k (List.mem_finRange k)
    simp [hmem] at hfalse
  | some k' =>
    dsimp only
    have hk' : v ∈ W.internalVerts k' := by simpa using List.find?_some hfind
    refine ⟨by omega, fun hall => (hall k' hk').elim⟩

theorem wallEdgeOf_le {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) (v : Fin n) :
    wallEdgeOf W v ≤ (elemWallEdges h).length := by
  unfold wallEdgeOf
  cases (List.finRange (elemWallEdges h).length).find? (fun k => decide (v ∈ W.internalVerts k)) with
  | none => exact Nat.zero_le _
  | some k => exact k.2

/-- Generic wall vertex subset indicator parameterized by branch-vertex predicate `brPred` and
subdivision-edge predicate `edgePred`. -/
def wallSubsetInd {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (brPred : Fin (elemWallNumVerts h) → Bool)
    (edgePred : Fin (elemWallEdges h).length → Bool) (v : Fin n) : Bool :=
  (if hbr : 0 < wallBrOf W v ∧ wallBrOf W v - 1 < elemWallNumVerts h then
    brPred ⟨wallBrOf W v - 1, hbr.2⟩
  else false) ||
  (if hedge : 0 < wallEdgeOf W v ∧ wallEdgeOf W v - 1 < (elemWallEdges h).length then
    edgePred ⟨wallEdgeOf W v - 1, hedge.2⟩
  else false)

theorem wallSubsetInd_eq_true_iff {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid)
    (brPred : Fin (elemWallNumVerts h) → Bool)
    (edgePred : Fin (elemWallEdges h).length → Bool) (v : Fin n) :
    wallSubsetInd W brPred edgePred v = true ↔
      (∃ u : Fin (elemWallNumVerts h), W.branchVert u = v ∧ brPred u = true) ∨
      (∃ k : Fin (elemWallEdges h).length, v ∈ W.internalVerts k ∧ edgePred k = true) := by
  unfold wallSubsetInd
  rw [Bool.or_eq_true]
  refine or_congr ?_ ?_
  · split_ifs with hbr
    · let u : Fin (elemWallNumVerts h) := ⟨wallBrOf W v - 1, hbr.2⟩
      have hu_eq : wallBrOf W v = u.1 + 1 := by dsimp [u]; omega
      have hbr_u : W.branchVert u = v := (wallBrOf_eq_succ_iff hW v u).mp hu_eq
      constructor
      · intro hp
        exact ⟨u, hbr_u, hp⟩
      · rintro ⟨u', hu', hp'⟩
        have : u' = u := hW.1 (hu'.trans hbr_u.symm)
        change brPred u = true
        rwa [← this]
    · simp only [false_iff, not_exists, not_and]
      intro u hu
      have hu_eq : wallBrOf W v = u.1 + 1 := (wallBrOf_eq_succ_iff hW v u).mpr hu
      exfalso
      exact hbr ⟨by omega, by omega⟩
  · split_ifs with hedge
    · let k : Fin (elemWallEdges h).length := ⟨wallEdgeOf W v - 1, hedge.2⟩
      have hk_eq : wallEdgeOf W v = k.1 + 1 := by dsimp [k]; omega
      have hmem_k : v ∈ W.internalVerts k := (wallEdgeOf_eq_succ_iff hW v k).mp hk_eq
      constructor
      · intro hp
        exact ⟨k, hmem_k, hp⟩
      · rintro ⟨k', hk', hp'⟩
        have hk'_eq : wallEdgeOf W v = k'.1 + 1 := (wallEdgeOf_eq_succ_iff hW v k').mpr hk'
        have : k' = k := Fin.ext (by omega)
        change edgePred k = true
        rwa [← this]
    · simp only [false_iff, not_exists, not_and]
      intro k hk
      have hk_eq : wallEdgeOf W v = k.1 + 1 := (wallEdgeOf_eq_succ_iff hW v k).mpr hk
      exfalso
      exact hedge ⟨by omega, by omega⟩

theorem wallSubsetInd_vertexFinset {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid) (v : Fin n) :
    wallSubsetInd W (fun _ => true) (fun _ => true) v = decide (v ∈ W.vertexFinset) := by
  rw [Bool.eq_iff_iff, wallSubsetInd_eq_true_iff hW, decide_eq_true_eq, W.mem_vertexFinset_iff_or]
  simp

/-- Decidable check that branch vertex `u : Fin (elemWallNumVerts h)` is an endpoint of at least
one perimeter edge of `elemWallEdges h`. -/
def isPerimBr (h : ℕ) (u : Fin (elemWallNumVerts h)) : Bool :=
  (List.finRange (elemWallEdges h).length).any fun k =>
    isElemWallPerimEdge h k &&
      decide (((elemWallEdges h)[k.1]'k.2).1 = u ∨ ((elemWallEdges h)[k.1]'k.2).2 = u)

theorem wallSubsetInd_perimFinset {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid) (v : Fin n) :
    wallSubsetInd W (isPerimBr h) (isElemWallPerimEdge h) v = decide (v ∈ W.perimFinset) := by
  rw [Bool.eq_iff_iff, wallSubsetInd_eq_true_iff hW, decide_eq_true_eq, W.mem_perimFinset_iff]
  constructor
  · rintro (⟨u, rfl, hper⟩ | ⟨k, hv, hper⟩)
    · unfold isPerimBr at hper
      simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
        decide_eq_true_eq] at hper
      rcases hper with ⟨k, hke, h1 | h2⟩
      · refine ⟨k, hke, ?_⟩
        rw [W.mem_subdivPathVerts_iff k, h1]
        exact Or.inl rfl
      · refine ⟨k, hke, ?_⟩
        rw [W.mem_subdivPathVerts_iff k, h2]
        exact Or.inr (Or.inr rfl)
    · refine ⟨k, hper, ?_⟩
      rw [W.mem_subdivPathVerts_iff k]
      exact Or.inr (Or.inl hv)
  · rintro ⟨k, hke, hv_sub⟩
    rw [W.mem_subdivPathVerts_iff k] at hv_sub
    rcases hv_sub with rfl | hv_int | rfl
    · left
      refine ⟨((elemWallEdges h)[k.1]'k.2).1, rfl, ?_⟩
      unfold isPerimBr
      rw [List.any_eq_true]
      exact ⟨k, List.mem_finRange k, by simp [hke]⟩
    · exact Or.inr ⟨k, hv_int, hke⟩
    · left
      refine ⟨((elemWallEdges h)[k.1]'k.2).2, rfl, ?_⟩
      unfold isPerimBr
      rw [List.any_eq_true]
      exact ⟨k, List.mem_finRange k, by simp [hke]⟩

/-- Partial `wallBrOf` after processing the first `m` branch vertices. -/
def wallBrOfPrefix {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (m : ℕ) (v : Fin n) : ℕ :=
  match ((List.finRange (elemWallNumVerts h)).take m).find?
      (fun u => decide (W.branchVert u = v)) with
  | some u => u.1 + 1
  | none => 0

theorem wallBrOfPrefix_zero {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    List.ofFn (wallBrOfPrefix W 0) = List.replicate n 0 := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp [wallBrOfPrefix]

theorem wallBrOfPrefix_full {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    wallBrOfPrefix W (elemWallNumVerts h) = wallBrOf W := by
  funext v
  unfold wallBrOfPrefix wallBrOf
  rw [List.take_of_length_le (by simp)]

theorem wallBrOfPrefix_step_apply {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid)
    (u : Fin (elemWallNumVerts h)) (v : Fin n) :
    wallBrOfPrefix W (u.1 + 1) v =
      if v = W.branchVert u then u.1 + 1 else wallBrOfPrefix W u.1 v := by
  have htake :
      (List.finRange (elemWallNumVerts h)).take (u.1 + 1) =
        (List.finRange (elemWallNumVerts h)).take u.1 ++ [u] := by
    have hlen : u.1 < (List.finRange (elemWallNumVerts h)).length := by simp [u.2]
    rw [take_add_one_eq_append_getElem _ u.1 hlen, List.getElem_finRange]
    simp
  unfold wallBrOfPrefix
  rw [htake, List.find?_append]
  by_cases hv : v = W.branchVert u
  · subst hv
    have hnone :
        ((List.finRange (elemWallNumVerts h)).take u.1).find?
          (fun u' => decide (W.branchVert u' = W.branchVert u)) = none := by
      rw [List.find?_eq_none]
      intro u' hu'
      rcases List.mem_take_iff_getElem.mp hu' with ⟨idx, hidx, heq⟩
      have hidx_eq : idx = u'.1 := by simpa using congrArg Fin.val heq
      have hidx_lt : idx < u.1 := Nat.lt_of_lt_of_le hidx (Nat.min_le_left _ _)
      have hne : u' ≠ u := fun h => by subst h; omega
      simp [hW.1.ne hne]
    rw [hnone]
    simp
  · have hne : W.branchVert u ≠ v := Ne.symm hv
    rw [if_neg hv]
    cases ((List.finRange (elemWallNumVerts h)).take u.1).find?
        (fun u' => decide (W.branchVert u' = v)) with
    | some _ => rfl
    | none => simp [hne]

theorem wallBrOfPrefix_step {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid)
    (u : Fin (elemWallNumVerts h)) :
    (List.ofFn (wallBrOfPrefix W u.1)).set (W.branchVert u).1 (u.1 + 1) =
      List.ofFn (wallBrOfPrefix W (u.1 + 1)) := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi_n : i < n := by simpa using hi₂
  let v : Fin n := ⟨i, hi_n⟩
  rw [List.getElem_ofFn]
  change ((List.ofFn (wallBrOfPrefix W u.1)).set (W.branchVert u).1 (u.1 + 1))[i]'hi₁ =
    wallBrOfPrefix W (u.1 + 1) v
  rw [wallBrOfPrefix_step_apply hW u v]
  by_cases hiv : i = (W.branchVert u).1
  · have hvu : v = W.branchVert u := Fin.ext hiv
    subst hiv
    rw [List.getElem_set_self hi₁, if_pos hvu]
  · have hvu : v ≠ W.branchVert u := fun h => hiv (congrArg Fin.val h)
    rw [List.getElem_set_ne (Ne.symm hiv), List.getElem_ofFn, if_neg hvu]

/-- Loop body populating `a_W_brOf` from `a_W_br`: sets `a_W_brOf[a_W_br[r_u]] := r_u + 1`. -/
def buildWallBrOfBody (a_W_br a_W_brOf : Arr) (r_u r_tmp : Reg) : Cmd :=
  .seq (.assign r_tmp (.read a_W_br (.reg r_u)))
    (.write a_W_brOf (.reg r_tmp) (.op .add (.reg r_u) (.const 1)))

/-- Build `a_W_brOf = List.ofFn (wallBrOf W)` from `a_W_br`. -/
def buildWallBrOfProg (a_W_br a_W_brOf : Arr) (r_nv r_n r_u r_tmp : Reg) : Cmd :=
  .seq (.alloc a_W_brOf (.reg r_n))
    (.seq (.assign r_u (.const 0))
      (forUp r_u (.reg r_nv) (buildWallBrOfBody a_W_br a_W_brOf r_u r_tmp)))

theorem buildWallBrOfLoop_exec {w h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (hW : W.IsValid)
    (a_W_br a_W_brOf r_nv r_u r_tmp : ℕ)
    (hne_arr : a_W_br ≠ a_W_brOf)
    (hne_nu : r_nv ≠ r_u) (hne_nt : r_nv ≠ r_tmp) (hne_ut : r_u ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hnv_w : elemWallNumVerts h < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = elemWallNumVerts h)
    {s : State}
    (hbr : s.arrs a_W_br =
      (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1))
    (hbrOf : s.arrs a_W_brOf = List.ofFn (wallBrOfPrefix W k))
    (hrnv : s.regs r_nv = elemWallNumVerts h)
    (hru : s.regs r_u = k) :
    ∃ s' t,
      Exec w (forUp r_u (.reg r_nv) (buildWallBrOfBody a_W_br a_W_brOf r_u r_tmp)) s s' t ∧
      t ≤ 3 + 15 * rem ∧
      s'.arrs a_W_brOf = List.ofFn (wallBrOf W) ∧
      (∀ a : ℕ, a ≠ a_W_brOf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_u → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = elemWallNumVerts h := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_nv)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrnv, hnv_w, h0_w]
    rw [wallBrOfPrefix_full] at hbrOf
    exact ⟨s, 3, .while_false hcond, by omega, hbrOf, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < elemWallNumVerts h := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    let u : Fin (elemWallNumVerts h) := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_nv)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrnv, hk_w, hnv_w, hk_lt, hw]
    have hbr_len : k < (s.arrs a_W_br).length := by simp [hbr, hk_lt]
    have hbr_get : (s.arrs a_W_br)[k]'hbr_len = (W.branchVert u).1 := by
      simp [hbr, u]
    have hbu_w : (W.branchVert u).1 < 2 ^ w := Nat.lt_trans (W.branchVert u).2 hn_w
    let s₁ := s.setReg r_tmp (W.branchVert u).1
    have hex₁ : Exec w (.assign r_tmp (.read a_W_br (.reg r_u))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hbr_len, hbr_get, hbu_w])
    have hru₁ : s₁.regs r_u = k := by simp [s₁, State.setReg, hne_ut, hru]
    have hbu_len : (W.branchVert u).1 < (s₁.arrs a_W_brOf).length := by
      simp [s₁, hbrOf, (W.branchVert u).2]
    let s₂ := s₁.writeArr a_W_brOf (W.branchVert u).1 (k + 1)
    have hex₂ :
        Exec w (.write a_W_brOf (.reg r_tmp) (.op .add (.reg r_u) (.const 1))) s₁ s₂ 5 :=
      .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hbu_w])
        (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hk_w, hw, hk1_w])
        hbu_len
    let s₃ := s₂.setReg r_u (k + 1)
    have hex₃ : Exec w (.assign r_u (.op .add (.reg r_u) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hk_w, hw, hk1_w])
    have hbrOf₃ : s₃.arrs a_W_brOf = List.ofFn (wallBrOfPrefix W (k + 1)) := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hbrOf]
      exact wallBrOfPrefix_step hW u
    rcases ih (k + 1) (by omega) (s := s₃)
        (by simp [s₃, s₂, s₁, hne_arr, hbr])
        hbrOf₃
        (by simp [s₃, s₂, s₁, State.setReg, hne_nu, hne_nt, hrnv])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hbrOf₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + 5) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hbrOf₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, s₁, ha],
      fun r hr₁ hr₂ => by rw [hreg₄ r hr₁ hr₂]; simp [s₃, s₂, s₁, State.setReg, hr₁, hr₂]⟩

theorem buildWallBrOfProg_exec {w h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (hW : W.IsValid)
    (a_W_br a_W_brOf r_nv r_n r_u r_tmp : ℕ)
    (hne_arr : a_W_br ≠ a_W_brOf)
    (hne_nu : r_nv ≠ r_u) (hne_nt : r_nv ≠ r_tmp) (hne_ut : r_u ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hnv_w : elemWallNumVerts h < 2 ^ w)
    {s : State}
    (hbr : s.arrs a_W_br =
      (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1))
    (hrnv : s.regs r_nv = elemWallNumVerts h)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (buildWallBrOfProg a_W_br a_W_brOf r_nv r_n r_u r_tmp) s s' t ∧
      t ≤ n + 15 * elemWallNumVerts h + 6 ∧
      s'.arrs a_W_brOf = List.ofFn (wallBrOf W) ∧
      (∀ a : ℕ, a ≠ a_W_brOf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_u → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_W_brOf (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_W_brOf (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_u 0
  have hex₂ : Exec w (.assign r_u (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hbrOf₂ : s₂.arrs a_W_brOf = List.ofFn (wallBrOfPrefix W 0) := by
    simp [s₂, s₁, wallBrOfPrefix_zero]
  rcases buildWallBrOfLoop_exec W hW a_W_br a_W_brOf r_nv r_u r_tmp
      hne_arr hne_nu hne_nt hne_ut hw hn_w hnv_w (elemWallNumVerts h) 0 (by omega)
      (s := s₂) (by simp [s₂, s₁, hne_arr, hbr]) hbrOf₂
      (by simp [s₂, s₁, State.setReg, hne_nu, hrnv]) (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hbrOf₃, harr₃, hreg₃⟩
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hbrOf₃,
    fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
    fun r hr₁ hr₂ => by rw [hreg₃ r hr₁ hr₂]; simp [s₂, s₁, State.setReg, hr₁]⟩

/-- Partial `wallEdgeOf` after processing the first `m` subdivision edges. -/
def wallEdgeOfPrefix {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (m : ℕ) (v : Fin n) : ℕ :=
  match ((List.finRange (elemWallEdges h).length).take m).find?
      (fun k => decide (v ∈ W.internalVerts k)) with
  | some k => k.1 + 1
  | none => 0

/-- Partial `wallEdgeOf` while processing the first `j` internal vertices of edge `k` on top of
`wallEdgeOfPrefix W k.1`. -/
def wallEdgeOfInEdge {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (k : Fin (elemWallEdges h).length) (j : ℕ) (v : Fin n) : ℕ :=
  if v ∈ (W.internalVerts k).take j then k.1 + 1 else wallEdgeOfPrefix W k.1 v

theorem wallEdgeOfPrefix_zero {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    List.ofFn (wallEdgeOfPrefix W 0) = List.replicate n 0 := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp [wallEdgeOfPrefix]

theorem wallEdgeOfPrefix_full {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    wallEdgeOfPrefix W (elemWallEdges h).length = wallEdgeOf W := by
  funext v
  unfold wallEdgeOfPrefix wallEdgeOf
  rw [List.take_of_length_le (by simp)]

theorem wallEdgeOfInEdge_zero {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (k : Fin (elemWallEdges h).length) :
    wallEdgeOfInEdge W k 0 = wallEdgeOfPrefix W k.1 := by
  funext v
  simp [wallEdgeOfInEdge]

theorem wallEdgeOfInEdge_step_apply {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (k : Fin (elemWallEdges h).length)
    {j : ℕ} (hj : j < (W.internalVerts k).length) (v : Fin n) :
    wallEdgeOfInEdge W k (j + 1) v =
      if v = (W.internalVerts k)[j]'hj then k.1 + 1 else wallEdgeOfInEdge W k j v := by
  let v₀ := (W.internalVerts k)[j]'hj
  have htake : (W.internalVerts k).take (j + 1) = (W.internalVerts k).take j ++ [v₀] :=
    take_add_one_eq_append_getElem (W.internalVerts k) j hj
  change wallEdgeOfInEdge W k (j + 1) v =
    if v = v₀ then k.1 + 1 else wallEdgeOfInEdge W k j v
  unfold wallEdgeOfInEdge
  rw [htake]
  by_cases hv : v = v₀
  · rw [if_pos hv, if_pos (List.mem_append_right _ (by simp [hv]))]
  · rw [if_neg hv]
    have hmem_iff : v ∈ (W.internalVerts k).take j ++ [v₀] ↔ v ∈ (W.internalVerts k).take j := by
      simp [hv]
    simp [hmem_iff]

theorem wallEdgeOfInEdge_step {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (k : Fin (elemWallEdges h).length)
    {j : ℕ} (hj : j < (W.internalVerts k).length) :
    let v₀ := (W.internalVerts k)[j]'hj
    (List.ofFn (wallEdgeOfInEdge W k j)).set v₀.1 (k.1 + 1) =
      List.ofFn (wallEdgeOfInEdge W k (j + 1)) := by
  intro v₀
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  have hi_n : i < n := by simpa using hi₂
  let v : Fin n := ⟨i, hi_n⟩
  rw [List.getElem_ofFn]
  change ((List.ofFn (wallEdgeOfInEdge W k j)).set v₀.1 (k.1 + 1))[i]'hi₁ =
    wallEdgeOfInEdge W k (j + 1) v
  rw [wallEdgeOfInEdge_step_apply W k hj v]
  by_cases hiv : i = v₀.1
  · have hvv₀ : v = v₀ := Fin.ext hiv
    subst hiv
    rw [List.getElem_set_self hi₁, if_pos hvv₀]
  · have hvv₀ : v ≠ v₀ := fun h => hiv (congrArg Fin.val h)
    rw [List.getElem_set_ne (Ne.symm hiv), List.getElem_ofFn, if_neg hvv₀]

theorem wallEdgeOfInEdge_full {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid)
    (k : Fin (elemWallEdges h).length) :
    wallEdgeOfInEdge W k (W.internalVerts k).length = wallEdgeOfPrefix W (k.1 + 1) := by
  funext v
  have htake_k :
      (List.finRange (elemWallEdges h).length).take (k.1 + 1) =
        (List.finRange (elemWallEdges h).length).take k.1 ++ [k] := by
    have hlen : k.1 < (List.finRange (elemWallEdges h).length).length := by simp [k.2]
    rw [take_add_one_eq_append_getElem _ k.1 hlen, List.getElem_finRange]
    simp
  unfold wallEdgeOfInEdge wallEdgeOfPrefix
  rw [List.take_of_length_le (le_rfl), htake_k, List.find?_append]
  by_cases hv : v ∈ W.internalVerts k
  · rw [if_pos hv]
    have hnone :
        ((List.finRange (elemWallEdges h).length).take k.1).find?
          (fun k' => decide (v ∈ W.internalVerts k')) = none := by
      rw [List.find?_eq_none]
      intro k' hk'
      rcases List.mem_take_iff_getElem.mp hk' with ⟨idx, hidx, heq⟩
      have hidx_eq : idx = k'.1 := by simpa using congrArg Fin.val heq
      have hidx_lt : idx < k.1 := Nat.lt_of_lt_of_le hidx (Nat.min_le_left _ _)
      have hne : k' ≠ k := fun h => by subst h; omega
      have hnot : v ∉ W.internalVerts k' := fun hm => hW.2.2.2 k' k hne hm hv
      simp [hnot]
    rw [hnone]
    simp [hv]
  · rw [if_neg hv]
    cases ((List.finRange (elemWallEdges h).length).take k.1).find?
        (fun k' => decide (v ∈ W.internalVerts k')) with
    | some _ => rfl
    | none => simp [hv]

theorem drop_eq_getElem_cons {α : Type*} (l : List α) {m : ℕ} (hm : m < l.length) :
    l.drop m = l[m]'hm :: l.drop (m + 1) := by
  have h1 : l.take m ++ l.drop m = l.take m ++ (l[m]'hm :: l.drop (m + 1)) := by
    rw [List.take_append_drop, List.append_cons,
      ← take_add_one_eq_append_getElem l m hm, List.take_append_drop]
  exact List.append_cancel_left h1

theorem WallOfHeight.IsValid.length_internalVerts_le {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid) (k : Fin (elemWallEdges h).length) :
    (W.internalVerts k).length ≤ n := by
  have hle1 : (W.internalVerts k).length ≤ (W.subdivPathVerts k).length := by
    simp [WallOfHeight.subdivPathVerts]; omega
  have hle2 : (W.subdivPathVerts k).length ≤ (List.finRange n).length :=
    (List.subperm_of_subset (hW.2.1 k).1 (fun x _ => List.mem_finRange x)).length_le
  exact hle1.trans (hle2.trans (by simp))

/-- Remaining subdivision-list stream starting from edge index `m`. -/
def wallSubdivStream {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (m : ℕ) : List ℕ :=
  ((List.finRange (elemWallEdges h).length).drop m).flatMap
    (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)

theorem wallSubdivStream_nil {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    wallSubdivStream W (elemWallEdges h).length = [] := by
  unfold wallSubdivStream
  rw [List.drop_of_length_le (by simp)]
  rfl

theorem wallSubdivStream_cons {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (k : Fin (elemWallEdges h).length) :
    wallSubdivStream W k.1 =
      ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ++
        wallSubdivStream W (k.1 + 1) := by
  unfold wallSubdivStream
  have hlen : k.1 < (List.finRange (elemWallEdges h).length).length := by simp [k.2]
  rw [drop_eq_getElem_cons _ hlen, List.getElem_finRange]
  rfl

/-- Inner loop body reading one internal subdivision vertex from `a_src` at `r_pos` into `r_tmp`
and setting `a_W_edgeOf[r_tmp] := r_k + 1`. -/
def readWallEdgeVertBody (a_src a_W_edgeOf : Arr) (r_pos r_k r_tmp : Reg) : Cmd :=
  .seq (readStreamWordProg a_src r_pos r_tmp)
    (.write a_W_edgeOf (.reg r_tmp) (.op .add (.reg r_k) (.const 1)))

theorem readWallEdgeVertLoop_exec {w h n a_src a_W_edgeOf off : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (hW : W.IsValid) (k : Fin (elemWallEdges h).length)
    (r_pos r_k r_len r_j r_tmp : ℕ)
    (hne_arr : a_src ≠ a_W_edgeOf)
    (hne_pk : r_pos ≠ r_k) (hne_pl : r_pos ≠ r_len) (hne_pj : r_pos ≠ r_j) (hne_pt : r_pos ≠ r_tmp)
    (_hne_kl : r_k ≠ r_len) (hne_kj : r_k ≠ r_j) (hne_kt : r_k ≠ r_tmp)
    (hne_lj : r_len ≠ r_j) (hne_lt : r_len ≠ r_tmp) (hne_jt : r_j ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hk1_w : k.1 + 1 < 2 ^ w)
    (rem j : ℕ) (hrem : j + rem = (W.internalVerts k).length)
    {tail : List ℕ} (hoff_w : off + rem < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (((W.internalVerts k).map Fin.val).drop j ++ tail) s)
    (hedgeOf : s.arrs a_W_edgeOf = List.ofFn (wallEdgeOfInEdge W k j))
    (hrpos : s.regs r_pos = off)
    (hrk : s.regs r_k = k.1)
    (hrlen : s.regs r_len = (W.internalVerts k).length)
    (hrj : s.regs r_j = j) :
    ∃ s' t,
      Exec w (forUp r_j (.reg r_len)
        (readWallEdgeVertBody a_src a_W_edgeOf r_pos r_k r_tmp)) s s' t ∧
      t ≤ 3 + 20 * rem ∧
      s'.arrs a_W_edgeOf = List.ofFn (wallEdgeOfInEdge W k (W.internalVerts k).length) ∧
      s'.regs r_pos = off + rem ∧
      s'.regs r_k = k.1 ∧
      AtStream a_src (off + rem) tail s' ∧
      (∀ a : ℕ, a ≠ a_W_edgeOf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_j → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : (W.internalVerts k).length < 2 ^ w :=
    Nat.lt_of_le_of_lt (hW.length_internalVerts_le k) hn_w
  induction rem generalizing j off s with
  | zero =>
    have hj_eq : j = (W.internalVerts k).length := by omega
    subst hj_eq
    have hcond : (Expr.op .lt (.reg r_j) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrlen, hlen_w, h0_w]
    have hdrop : ((W.internalVerts k).map Fin.val).drop (W.internalVerts k).length = [] := by
      rw [List.drop_of_length_le (by simp)]
    rw [hdrop, List.nil_append] at hstream
    exact ⟨s, 3, .while_false hcond, by omega, hedgeOf, by omega, hrk,
      by simpa using hstream, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hj_lt : j < (W.internalVerts k).length := by omega
    have hj_w : j < 2 ^ w := by omega
    have hj1_w : j + 1 < 2 ^ w := by omega
    have hk_w : k.1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_j) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrlen, hj_w, hlen_w, hj_lt, hw]
    let v₀ : Fin n := (W.internalVerts k)[j]'hj_lt
    have hv₀_w : v₀.1 < 2 ^ w := Nat.lt_trans v₀.2 hn_w
    have hdrop_cons :
        ((W.internalVerts k).map Fin.val).drop j =
          v₀.1 :: ((W.internalVerts k).map Fin.val).drop (j + 1) := by
      have hlen_map : j < ((W.internalVerts k).map Fin.val).length := by simp [hj_lt]
      rw [drop_eq_getElem_cons _ hlen_map, List.getElem_map]
    rw [hdrop_cons, List.cons_append] at hstream
    rcases readStreamWordProg_exec r_pos r_tmp hne_pt hw (by omega) hv₀_w hstream hrpos with
      ⟨s₁, t₁, hex₁, ht₁, hrtmp₁, hrpos₁, hstream₁, harr₁, hreg₁⟩
    have hrk₁ : s₁.regs r_k = k.1 := by rw [hreg₁ r_k hne_pk.symm hne_kt, hrk]
    have hrj₁ : s₁.regs r_j = j := by rw [hreg₁ r_j hne_pj.symm hne_jt, hrj]
    have hrlen₁ : s₁.regs r_len = (W.internalVerts k).length := by
      rw [hreg₁ r_len hne_pl.symm hne_lt, hrlen]
    have hedgeOf₁ : s₁.arrs a_W_edgeOf = List.ofFn (wallEdgeOfInEdge W k j) := by
      rw [harr₁ a_W_edgeOf, hedgeOf]
    have hv₀_len : v₀.1 < (s₁.arrs a_W_edgeOf).length := by simp [hedgeOf₁, v₀.2]
    let s₂ := s₁.writeArr a_W_edgeOf v₀.1 (k.1 + 1)
    have hex₂ :
        Exec w (.write a_W_edgeOf (.reg r_tmp) (.op .add (.reg r_k) (.const 1))) s₁ s₂ 5 :=
      .write (by simp [Expr.eval, checkWord, hrtmp₁, hv₀_w])
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₁, hk_w, hw, hk1_w])
        hv₀_len
    let s₃ := s₂.setReg r_j (j + 1)
    have hex₃ : Exec w (.assign r_j (.op .add (.reg r_j) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj₁, hj_w, hw, hj1_w])
    have hedgeOf₃ : s₃.arrs a_W_edgeOf = List.ofFn (wallEdgeOfInEdge W k (j + 1)) := by
      simp only [s₃, s₂, State.setReg_arrs, State.writeArr_arrs_self, hedgeOf₁]
      exact wallEdgeOfInEdge_step W k hj_lt
    have hstream₃ :
        AtStream a_src (off + 1) (((W.internalVerts k).map Fin.val).drop (j + 1) ++ tail) s₃ := by
      apply hstream₁.of_arr_eq
      simp [s₃, s₂, hne_arr]
    rcases ih (j + 1) (by omega) (off := off + 1) (by omega) (s := s₃)
        hstream₃ hedgeOf₃
        (by simp [s₃, s₂, State.setReg, hne_pj, hrpos₁])
        (by simp [s₃, s₂, State.setReg, hne_kj, hrk₁])
        (by simp [s₃, s₂, State.setReg, hne_lj, hrlen₁])
        (by simp [s₃]) with
      ⟨s₄, t₄, hex₄, ht₄, hedgeOf₄, hrpos₄, hrk₄, hstream₄, harr₄, hreg₄⟩
    have hoff_eq : off + 1 + rem = off + (rem + 1) := by omega
    rw [hoff_eq] at hrpos₄ hstream₄
    refine ⟨s₄, 3 + ((t₁ + 5) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex₂) hex₃) hex₄,
      by omega, hedgeOf₄, hrpos₄, hrk₄, hstream₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, ha, harr₁ a],
      fun r hr₁ hr₂ hr₃ => by
        rw [hreg₄ r hr₁ hr₂ hr₃]
        simp [s₃, s₂, State.setReg, hr₂, hreg₁ r hr₁ hr₃]⟩

/-- Outer loop body reading one subdivision edge list `len_k :: vs_k` from `a_src` at `r_pos`
and updating `a_W_edgeOf`. -/
def readWallEdgeOuterBody (a_src a_W_edgeOf : Arr) (r_pos r_k r_len r_j r_tmp : Reg) : Cmd :=
  .seq (readStreamWordProg a_src r_pos r_len)
    (.seq (.assign r_j (.const 0))
      (forUp r_j (.reg r_len) (readWallEdgeVertBody a_src a_W_edgeOf r_pos r_k r_tmp)))

/-- Read all `(elemWallEdges h).length` subdivision lists from `a_src` at `r_pos` and populate
`a_W_edgeOf = List.ofFn (wallEdgeOf W)`. -/
def readWallEdgesProg (a_src a_W_edgeOf : Arr)
    (r_pos r_ne r_n r_k r_len r_j r_tmp : Reg) : Cmd :=
  .seq (.alloc a_W_edgeOf (.reg r_n))
    (.seq (.assign r_k (.const 0))
      (forUp r_k (.reg r_ne)
        (readWallEdgeOuterBody a_src a_W_edgeOf r_pos r_k r_len r_j r_tmp)))

theorem readWallEdgesLoop_exec {w h n a_src a_W_edgeOf off : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (hW : W.IsValid)
    (r_pos r_ne r_k r_len r_j r_tmp : ℕ)
    (hne_arr : a_src ≠ a_W_edgeOf)
    (hne_pne : r_pos ≠ r_ne) (hne_pk : r_pos ≠ r_k) (hne_pl : r_pos ≠ r_len)
    (hne_pj : r_pos ≠ r_j) (hne_pt : r_pos ≠ r_tmp)
    (hne_nek : r_ne ≠ r_k) (hne_nel : r_ne ≠ r_len) (hne_nej : r_ne ≠ r_j) (hne_net : r_ne ≠ r_tmp)
    (hne_kl : r_k ≠ r_len) (hne_kj : r_k ≠ r_j) (hne_kt : r_k ≠ r_tmp)
    (hne_lj : r_len ≠ r_j) (hne_lt : r_len ≠ r_tmp) (hne_jt : r_j ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hne_w : (elemWallEdges h).length < 2 ^ w)
    (rem m : ℕ) (hrem : m + rem = (elemWallEdges h).length)
    {tail : List ℕ} (hoff_w : off + (wallSubdivStream W m).length < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (wallSubdivStream W m ++ tail) s)
    (hedgeOf : s.arrs a_W_edgeOf = List.ofFn (wallEdgeOfPrefix W m))
    (hrpos : s.regs r_pos = off)
    (hrne : s.regs r_ne = (elemWallEdges h).length)
    (hrk : s.regs r_k = m) :
    ∃ s' t,
      Exec w (forUp r_k (.reg r_ne)
        (readWallEdgeOuterBody a_src a_W_edgeOf r_pos r_k r_len r_j r_tmp)) s s' t ∧
      t ≤ 3 + 22 * (wallSubdivStream W m).length ∧
      s'.arrs a_W_edgeOf = List.ofFn (wallEdgeOf W) ∧
      s'.regs r_pos = off + (wallSubdivStream W m).length ∧
      AtStream a_src (off + (wallSubdivStream W m).length) tail s' ∧
      (∀ a : ℕ, a ≠ a_W_edgeOf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_k → r ≠ r_len → r ≠ r_j → r ≠ r_tmp → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing m off s with
  | zero =>
    have hm_eq : m = (elemWallEdges h).length := by omega
    subst hm_eq
    have hcond : (Expr.op .lt (.reg r_k) (.reg r_ne)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrne, hne_w, h0_w]
    simp only [wallSubdivStream_nil, List.nil_append, List.length_nil, Nat.add_zero] at hstream ⊢
    rw [wallEdgeOfPrefix_full] at hedgeOf
    exact ⟨s, 3, .while_false hcond, by omega, hedgeOf, hrpos, hstream,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hm_lt : m < (elemWallEdges h).length := by omega
    have hm_w : m < 2 ^ w := by omega
    have hm1_w : m + 1 < 2 ^ w := by omega
    let k : Fin (elemWallEdges h).length := ⟨m, hm_lt⟩
    have hcond : (Expr.op .lt (.reg r_k) (.reg r_ne)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrne, hm_w, hne_w, hm_lt, hw]
    have hsub_cons := wallSubdivStream_cons W k
    have hlen_sub :
        (wallSubdivStream W m).length =
          1 + (W.internalVerts k).length + (wallSubdivStream W (m + 1)).length := by
      change (wallSubdivStream W k.1).length = _
      rw [hsub_cons]
      simp [k]
      omega
    have hstream_k :
        AtStream a_src off
          ((W.internalVerts k).length ::
            (((W.internalVerts k).map Fin.val) ++ (wallSubdivStream W (m + 1) ++ tail))) s := by
      change AtStream a_src off (wallSubdivStream W k.1 ++ tail) s at hstream
      rw [hsub_cons] at hstream
      simpa [List.append_assoc] using hstream
    have hlen_k_w : (W.internalVerts k).length < 2 ^ w :=
      Nat.lt_of_le_of_lt (hW.length_internalVerts_le k) hn_w
    rcases readStreamWordProg_exec r_pos r_len hne_pl hw (by omega) hlen_k_w hstream_k hrpos with
      ⟨s₁, t₁, hex₁, ht₁, hrlen₁, hrpos₁, hstream₁, harr₁, hreg₁⟩
    let s₂ := s₁.setReg r_j 0
    have hex₂ : Exec w (.assign r_j (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have hedgeOf₂ : s₂.arrs a_W_edgeOf = List.ofFn (wallEdgeOfInEdge W k 0) := by
      rw [wallEdgeOfInEdge_zero]
      simp [s₂, harr₁ a_W_edgeOf, hedgeOf, k]
    have hstream₂ :
        AtStream a_src (off + 1)
          (((W.internalVerts k).map Fin.val).drop 0 ++ (wallSubdivStream W (m + 1) ++ tail)) s₂ :=
      hstream₁.of_arr_eq rfl
    have hrk₂ : s₂.regs r_k = k.1 := by
      have h1 := hreg₁ r_k hne_pk.symm hne_kl
      simp [s₂, State.setReg, hne_kj, h1, hrk, k]
    rcases readWallEdgeVertLoop_exec W hW k r_pos r_k r_len r_j r_tmp
        hne_arr hne_pk hne_pl hne_pj hne_pt hne_kl hne_kj hne_kt hne_lj hne_lt hne_jt
        hw hn_w hm1_w (W.internalVerts k).length 0 (by omega) (by omega)
        (s := s₂) hstream₂ hedgeOf₂
        (by simp [s₂, State.setReg, hne_pj, hrpos₁])
        hrk₂
        (by simp [s₂, State.setReg, hne_lj, hrlen₁])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hedgeOf₃, hrpos₃, hrk₃, hstream₃, harr₃, hreg₃⟩
    rw [wallEdgeOfInEdge_full hW k] at hedgeOf₃
    let s₄ := s₃.setReg r_k (m + 1)
    have hex₄ : Exec w (.assign r_k (.op .add (.reg r_k) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₃, k, hm_w, hw, hm1_w])
    have hrne₄ : s₄.regs r_ne = (elemWallEdges h).length := by
      have h3 := hreg₃ r_ne hne_pne.symm hne_nej hne_net
      have h1 := hreg₁ r_ne hne_pne.symm hne_nel
      simp [s₄, State.setReg, hne_nek, h3, s₂, hne_nej, h1, hrne]
    rcases ih (m + 1) (by omega) (off := off + 1 + (W.internalVerts k).length) (by omega)
        (s := s₄)
        (hstream₃.of_arr_eq rfl) hedgeOf₃
        (by simp [s₄, State.setReg, hne_pk, hrpos₃])
        hrne₄
        (by simp [s₄]) with
      ⟨s₅, t₅, hex₅, ht₅, hedgeOf₅, hrpos₅, hstream₅, harr₅, hreg₅⟩
    have hoff_eq :
        off + 1 + (W.internalVerts k).length + (wallSubdivStream W (m + 1)).length =
          off + (wallSubdivStream W m).length := by omega
    rw [hoff_eq] at hrpos₅ hstream₅
    refine ⟨s₅, 3 + ((t₁ + (2 + t₃)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex₃)) hex₄) hex₅,
      by omega, hedgeOf₅, hrpos₅, hstream₅,
      fun a ha => by
        rw [harr₅ a ha]
        simp only [s₄, State.setReg_arrs]
        rw [harr₃ a ha]
        simp [s₂, harr₁ a],
      fun r hr₁ hr₂ hr₃ hr₄ hr₅ => by
        rw [hreg₅ r hr₁ hr₂ hr₃ hr₄ hr₅]
        have h3 := hreg₃ r hr₁ hr₄ hr₅
        have h1 := hreg₁ r hr₁ hr₃
        simp [s₄, State.setReg, hr₂, h3, s₂, hr₄, h1]⟩

/-- Read Section 1 of a Case (iii) block (`W.encList`) from `a_src` starting at `r_pos`:
1. Reads `h, nv, ne` into `r_h, r_nv, r_ne`.
2. Reads the `nv` branch vertices into `a_W_br`.
3. Builds `a_W_brOf = List.ofFn (wallBrOf W)`.
4. Reads the `ne` subdivision lists and builds `a_W_edgeOf = List.ofFn (wallEdgeOf W)`.
Uses scratch registers `r_base .. r_base + 3`. -/
def readWallSectionProg (a_src a_W_br a_W_brOf a_W_edgeOf : Arr)
    (r_pos r_n r_h r_nv r_ne r_base : Reg) : Cmd :=
  .seq (readStreamWordProg a_src r_pos r_h)
    (.seq (readStreamWordProg a_src r_pos r_nv)
      (.seq (readStreamWordProg a_src r_pos r_ne)
        (.seq (readStreamSliceProg a_src a_W_br r_pos r_nv r_base)
          (.seq (buildWallBrOfProg a_W_br a_W_brOf r_nv r_n r_base (r_base + 1))
            (readWallEdgesProg a_src a_W_edgeOf r_pos r_ne r_n
              r_base (r_base + 1) (r_base + 2) (r_base + 3))))))

theorem readWallSectionProg_exec {w h n a_src a_W_br a_W_brOf a_W_edgeOf off : ℕ}
    {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (hW : W.IsValid) {rem : List ℕ}
    (r_pos r_n r_h r_nv r_ne r_base : ℕ)
    (hne_s_br : a_src ≠ a_W_br) (hne_s_brof : a_src ≠ a_W_brOf) (hne_s_eof : a_src ≠ a_W_edgeOf)
    (hne_br_brof : a_W_br ≠ a_W_brOf) (hne_br_eof : a_W_br ≠ a_W_edgeOf)
    (hne_brof_eof : a_W_brOf ≠ a_W_edgeOf)
    (hr_pos : r_pos < r_base) (hr_n : r_n < r_base)
    (hr_h : r_h < r_base) (hr_nv : r_nv < r_base) (hr_ne : r_ne < r_base)
    (hne_pn : r_pos ≠ r_n) (hne_ph : r_pos ≠ r_h) (hne_pnv : r_pos ≠ r_nv) (hne_pne : r_pos ≠ r_ne)
    (hne_nh : r_n ≠ r_h) (hne_nnv : r_n ≠ r_nv) (hne_nne : r_n ≠ r_ne)
    (hne_hnv : r_h ≠ r_nv) (hne_hne : r_h ≠ r_ne) (hne_nvne : r_nv ≠ r_ne)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hh_w : h < 2 ^ w)
    (hoff_w : off + W.encList.length < 2 ^ w)
    {s : State}
    (hstream : AtStream a_src off (W.encList ++ rem) s)
    (hrpos : s.regs r_pos = off)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (readWallSectionProg a_src a_W_br a_W_brOf a_W_edgeOf
        r_pos r_n r_h r_nv r_ne r_base) s s' t ∧
      t ≤ 2 * n + 35 * W.encList.length + 50 ∧
      s'.regs r_h = h ∧
      s'.regs r_nv = elemWallNumVerts h ∧
      s'.regs r_ne = (elemWallEdges h).length ∧
      s'.regs r_pos = off + W.encList.length ∧
      s'.arrs a_W_br = (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1) ∧
      s'.arrs a_W_brOf = List.ofFn (wallBrOf W) ∧
      s'.arrs a_W_edgeOf = List.ofFn (wallEdgeOf W) ∧
      AtStream a_src (off + W.encList.length) rem s' ∧
      (∀ a : ℕ, a ≠ a_W_br → a ≠ a_W_brOf → a ≠ a_W_edgeOf → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_pos → r ≠ r_h → r ≠ r_nv → r ≠ r_ne → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let brWords := (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1)
  have hbr_len : brWords.length = elemWallNumVerts h := by simp [brWords]
  have henc_eq :
      W.encList =
        [h, elemWallNumVerts h, (elemWallEdges h).length] ++ brWords ++ wallSubdivStream W 0 := by
    rfl
  have henc_len :
      W.encList.length = 3 + elemWallNumVerts h + (wallSubdivStream W 0).length := by
    rw [henc_eq]
    simp [brWords]
    omega
  have hne_ge : (elemWallEdges h).length ≤ (wallSubdivStream W 0).length := by
    have hlen_enc := W.length_encList
    have hsum_nonneg :
        0 ≤ ((List.finRange (elemWallEdges h).length).map
          (fun k => (W.internalVerts k).length)).sum := Nat.zero_le _
    omega
  have hnv_w : elemWallNumVerts h < 2 ^ w := by omega
  have hne_w : (elemWallEdges h).length < 2 ^ w := by omega
  have hbr_w : ∀ x ∈ brWords, x < 2 ^ w := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨u, _, rfl⟩
    exact Nat.lt_trans (W.branchVert u).2 hn_w
  -- 1. Read h, nv, ne
  have hstream₀ :
      AtStream a_src off
        (h :: elemWallNumVerts h :: (elemWallEdges h).length ::
          (brWords ++ (wallSubdivStream W 0 ++ rem))) s := by
    rw [henc_eq] at hstream
    simpa [List.append_assoc] using hstream
  rcases readStreamWordProg_exec r_pos r_h hne_ph hw (by omega) hh_w hstream₀ hrpos with
    ⟨s₁, t₁, hex₁, ht₁, hrh₁, hrpos₁, hstream₁, harr₁, hreg₁⟩
  rcases readStreamWordProg_exec r_pos r_nv hne_pnv hw (by omega) hnv_w hstream₁ hrpos₁ with
    ⟨s₂, t₂, hex₂, ht₂, hrnv₂, hrpos₂, hstream₂, harr₂, hreg₂⟩
  rcases readStreamWordProg_exec r_pos r_ne hne_pne hw (by omega) hne_w hstream₂ hrpos₂ with
    ⟨s₃, t₃, hex₃, ht₃, hrne₃, hrpos₃, hstream₃, harr₃, hreg₃⟩
  -- 2. Read brWords into a_W_br
  have hrnv₃ : s₃.regs r_nv = brWords.length := by
    rw [hreg₃ r_nv hne_pnv.symm hne_nvne, hrnv₂, hbr_len]
  rcases readStreamSliceProg_exec r_pos r_nv r_base hne_s_br hr_pos hr_nv hne_pnv
      hbr_w hw (by omega) hstream₃ hrpos₃ hrnv₃ with
    ⟨s₄, t₄, hex₄, ht₄, hbr₄, hrpos₄, hrnv₄, hstream₄, harr₄, hreg₄⟩
  rw [hbr_len] at ht₄ hrpos₄ hrnv₄ hstream₄
  -- 3. Build a_W_brOf
  have hrn₄ : s₄.regs r_n = n := by
    rw [hreg₄ r_n hr_n hne_pn.symm, hreg₃ r_n hne_pn.symm hne_nne,
      hreg₂ r_n hne_pn.symm hne_nnv, hreg₁ r_n hne_pn.symm hne_nh, hrn]
  rcases buildWallBrOfProg_exec W hW a_W_br a_W_brOf r_nv r_n r_base (r_base + 1)
      hne_br_brof (by omega) (by omega) (by omega) hw hn_w hnv_w
      (s := s₄) hbr₄ hrnv₄ hrn₄ with
    ⟨s₅, t₅, hex₅, ht₅, hbrOf₅, harr₅, hreg₅⟩
  -- 4. Read subdivision edges and build a_W_edgeOf
  have hrn₅ : s₅.regs r_n = n := by
    rw [hreg₅ r_n (by omega) (by omega), hrn₄]
  have hrne₅ : s₅.regs r_ne = (elemWallEdges h).length := by
    rw [hreg₅ r_ne (by omega) (by omega), hreg₄ r_ne hr_ne hne_pne.symm, hrne₃]
  have hrpos₅ : s₅.regs r_pos = off + 1 + 1 + 1 + elemWallNumVerts h := by
    rw [hreg₅ r_pos (by omega) (by omega), hrpos₄]
  let s₆ := s₅.setArr a_W_edgeOf (List.replicate n 0)
  have hex₆ : Exec w (.alloc a_W_edgeOf (.reg r_n)) s₅ s₆ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn₅, hn_w])
  let s₇ := s₆.setReg r_base 0
  have hex₇ : Exec w (.assign r_base (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hedgeOf₇ : s₇.arrs a_W_edgeOf = List.ofFn (wallEdgeOfPrefix W 0) := by
    simp [s₇, s₆, wallEdgeOfPrefix_zero]
  have hstream₇ :
      AtStream a_src (off + 1 + 1 + 1 + elemWallNumVerts h) (wallSubdivStream W 0 ++ rem) s₇ := by
    apply hstream₄.of_arr_eq
    simp [s₇, s₆, hne_s_eof, harr₅ a_src hne_s_brof]
  rcases readWallEdgesLoop_exec W hW r_pos r_ne r_base (r_base + 1) (r_base + 2) (r_base + 3)
      hne_s_eof hne_pne (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hw hn_w hne_w (elemWallEdges h).length 0 (by omega) (by omega)
      (s := s₇) hstream₇ hedgeOf₇
      (by simp [s₇, s₆, State.setReg, show r_pos ≠ r_base by omega, hrpos₅])
      (by simp [s₇, s₆, State.setReg, show r_ne ≠ r_base by omega, hrne₅])
      (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, hedgeOf₈, hrpos₈, hstream₈, harr₈, hreg₈⟩
  have hoff_final :
      off + 1 + 1 + 1 + elemWallNumVerts h + (wallSubdivStream W 0).length =
        off + W.encList.length := by omega
  rw [hoff_final] at hrpos₈ hstream₈
  refine ⟨s₈, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + ((1 + n) + (2 + t₈)))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by omega,
    ?_, ?_, ?_, hrpos₈, ?_, ?_, hedgeOf₈, hstream₈, ?_, ?_⟩
  · rw [hreg₈ r_h hne_ph.symm (by omega) (by omega) (by omega) (by omega)]
    simp [s₇, s₆, State.setReg, show r_h ≠ r_base by omega,
      hreg₅ r_h (by omega) (by omega), hreg₄ r_h hr_h hne_ph.symm,
      hreg₃ r_h hne_ph.symm hne_hne, hreg₂ r_h hne_ph.symm hne_hnv, hrh₁]
  · rw [hreg₈ r_nv hne_pnv.symm (by omega) (by omega) (by omega) (by omega)]
    simp [s₇, s₆, State.setReg, show r_nv ≠ r_base by omega,
      hreg₅ r_nv (by omega) (by omega), hrnv₄]
  · rw [hreg₈ r_ne hne_pne.symm (by omega) (by omega) (by omega) (by omega)]
    simp [s₇, s₆, State.setReg, show r_ne ≠ r_base by omega, hrne₅]
  · rw [harr₈ a_W_br hne_br_eof]
    simp [s₇, s₆, hne_br_eof, harr₅ a_W_br hne_br_brof, hbr₄, brWords]
  · rw [harr₈ a_W_brOf hne_brof_eof]
    simp [s₇, s₆, hne_brof_eof, hbrOf₅]
  · intro a ha₁ ha₂ ha₃
    rw [harr₈ a ha₃]
    simp [s₇, s₆, ha₃, harr₅ a ha₂, harr₄ a ha₁, harr₃ a, harr₂ a, harr₁ a]
  · intro r hr hne₁ hne₂ hne₃ hne₄
    rw [hreg₈ r hne₁ (by omega) (by omega) (by omega) (by omega)]
    simp [s₇, s₆, State.setReg, show r ≠ r_base by omega,
      hreg₅ r (by omega) (by omega), hreg₄ r hr hne₁,
      hreg₃ r hne₁ hne₄, hreg₂ r hne₁ hne₃, hreg₁ r hne₁ hne₂]

/-- 1-indexed lookup list of length `L + 1` for a boolean predicate `pred : Fin L → Bool`. -/
def predTableList {L : ℕ} (pred : Fin L → Bool) : List ℕ :=
  0 :: List.ofFn (fun i : Fin L => if pred i then 1 else 0)

/-- Value at index `idx` of `predTableList pred`. -/
def predTableVal {L : ℕ} (pred : Fin L → Bool) (idx : ℕ) : ℕ :=
  if h : 0 < idx ∧ idx - 1 < L then
    if pred ⟨idx - 1, h.2⟩ then 1 else 0
  else 0

theorem predTableVal_le_one {L : ℕ} (pred : Fin L → Bool) (idx : ℕ) :
    predTableVal pred idx ≤ 1 := by
  unfold predTableVal
  split_ifs <;> omega

theorem predTableVal_pos_iff {L : ℕ} (pred : Fin L → Bool) (idx : ℕ) :
    0 < predTableVal pred idx ↔
      (if h : 0 < idx ∧ idx - 1 < L then pred ⟨idx - 1, h.2⟩ else false) = true := by
  unfold predTableVal
  by_cases h1 : 0 < idx ∧ idx - 1 < L
  · rw [dite_eq_left h1, dite_eq_left h1]
    cases pred ⟨idx - 1, h1.2⟩ <;> simp
  · rw [dite_eq_right h1, dite_eq_right h1]
    simp

theorem ite_predTableVal_eq_wallSubsetInd {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del)
    (brPred : Fin (elemWallNumVerts h) → Bool)
    (edgePred : Fin (elemWallEdges h).length → Bool) (v : Fin n) :
    (if 0 < predTableVal brPred (wallBrOf W v) ∨
        0 < predTableVal edgePred (wallEdgeOf W v) then 1 else 0) =
      if wallSubsetInd W brPred edgePred v then 1 else 0 := by
  unfold wallSubsetInd
  simp only [predTableVal_pos_iff, ← Bool.or_eq_true]

theorem length_predTableList {L : ℕ} (pred : Fin L → Bool) :
    (predTableList pred).length = L + 1 := by
  simp [predTableList]

theorem getElem_predTableList {L : ℕ} (pred : Fin L → Bool) {idx : ℕ}
    (hlt : idx < (predTableList pred).length) :
    (predTableList pred)[idx]'hlt = predTableVal pred idx := by
  unfold predTableVal
  have hidx : idx < L + 1 := by rwa [length_predTableList] at hlt
  rcases idx with _ | m
  · simp [predTableList]
  · have hm : m < L := by omega
    have hcond : 0 < m + 1 ∧ (m + 1) - 1 < L := ⟨by omega, hm⟩
    rw [dite_eq_left hcond]
    simp [predTableList]

theorem eval_read_predTableList {w L : ℕ} (pred : Fin L → Bool) (s : State) (a r : ℕ)
    {idx : ℕ} (ha : s.arrs a = predTableList pred) (hr : s.regs r = idx)
    (hidx_w : idx < 2 ^ w) (hidx_lt : idx < L + 1) (hw : 1 < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some (predTableVal pred idx) := by
  have hlen : idx < (s.arrs a).length := by
    rw [ha, length_predTableList]; exact hidx_lt
  have hget : (s.arrs a)[idx]'hlen = predTableVal pred idx := by
    have hlt' : idx < (predTableList pred).length := by
      rw [length_predTableList]; exact hidx_lt
    have hcongr : (s.arrs a)[idx]'hlen = (predTableList pred)[idx]'hlt' := by
      congr 1
    rw [hcongr, getElem_predTableList]
  have hval_w : predTableVal pred idx < 2 ^ w :=
    Nat.lt_of_le_of_lt (predTableVal_le_one pred idx) hw
  simp [Expr.eval, checkWord, hr, hidx_w, hlen, hget, hval_w]

theorem predTableList_le_one {L : ℕ} (pred : Fin L → Bool) {x : ℕ}
    (hx : x ∈ predTableList pred) : x ≤ 1 := by
  unfold predTableList at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · omega
  · rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    split_ifs <;> omega

/-- Loop body of `buildWallSubsetBitSetProg`: reads `a_brTab[a_W_brOf[r_v]]` and
`a_edgeTab[a_W_edgeOf[r_v]]` and writes `1` if their sum is positive, else `0`. -/
def buildWallSubsetBody (a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out : Arr)
    (r_v r_t1 r_t2 : Reg) : Cmd :=
  .seq (.assign r_t1 (.read a_W_brOf (.reg r_v)))
    (.seq (.assign r_t1 (.read a_brTab (.reg r_t1)))
      (.seq (.assign r_t2 (.read a_W_edgeOf (.reg r_v)))
        (.seq (.assign r_t2 (.read a_edgeTab (.reg r_t2)))
          (.write a_out (.reg r_v)
            (.op .lt (.const 0) (.op .add (.reg r_t1) (.reg r_t2)))))))

/-- Build `bitSetList {v : Fin n | wallSubsetInd W brPred edgePred v = true}` in `a_out` from
`a_W_brOf` and `a_W_edgeOf` using scratch arrays `a_brTab, a_edgeTab` and registers
`r_base .. r_base + 2`. -/
def buildWallSubsetBitSetProg {h : ℕ}
    (brPred : Fin (elemWallNumVerts h) → Bool)
    (edgePred : Fin (elemWallEdges h).length → Bool)
    (a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out : Arr)
    (r_n r_base : Reg) : Cmd :=
  .seq (writeConstListProg a_brTab r_base (predTableList brPred))
    (.seq (writeConstListProg a_edgeTab r_base (predTableList edgePred))
      (.seq (.alloc a_out (.reg r_n))
        (.seq (.assign r_base (.const 0))
          (forUp r_base (.reg r_n)
            (buildWallSubsetBody a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out
              r_base (r_base + 1) (r_base + 2))))))

theorem buildWallSubsetLoop_exec {w h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del)
    (brPred : Fin (elemWallNumVerts h) → Bool)
    (edgePred : Fin (elemWallEdges h).length → Bool)
    (a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out r_n r_base : ℕ)
    (hne_bo : a_W_brOf ≠ a_out) (hne_eo : a_W_edgeOf ≠ a_out)
    (hne_bt : a_brTab ≠ a_out) (hne_et : a_edgeTab ≠ a_out)
    (hr_n : r_n < r_base)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hnv_w : elemWallNumVerts h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges h).length + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n)
    {s : State}
    (hbrOf : s.arrs a_W_brOf = List.ofFn (wallBrOf W))
    (hedgeOf : s.arrs a_W_edgeOf = List.ofFn (wallEdgeOf W))
    (hbrTab : s.arrs a_brTab = predTableList brPred)
    (hedgeTab : s.arrs a_edgeTab = predTableList edgePred)
    (hout : s.arrs a_out =
      (List.ofFn (fun v : Fin n => if wallSubsetInd W brPred edgePred v then 1 else 0)).take k ++
        List.replicate rem 0)
    (hrn : s.regs r_n = n)
    (hrv : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_n)
        (buildWallSubsetBody a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out
          r_base (r_base + 1) (r_base + 2))) s s' t ∧
      t ≤ 3 + 27 * rem ∧
      s'.arrs a_out =
        bitSetList (Finset.univ.filter (fun v : Fin n => wallSubsetInd W brPred edgePred v = true)) ∧
      (∀ a : ℕ, a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  let targetList :=
    List.ofFn (fun v : Fin n => if wallSubsetInd W brPred edgePred v then 1 else 0)
  have htarget_eq :
      targetList =
        bitSetList (Finset.univ.filter (fun v : Fin n => wallSubsetInd W brPred edgePred v = true)) := by
    apply List.ext_getElem (by simp [targetList])
    intro i hi₁ hi₂
    simp [targetList, bitSetList]
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hrv hout
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hrn, hn_w, h0_w]
    change s.arrs a_out = targetList.take n ++ List.replicate 0 0 at hout
    rw [List.take_of_length_le (by simp [targetList]), List.replicate_zero,
      List.append_nil, htarget_eq] at hout
    exact ⟨s, 3, .while_false hcond, by omega, hout, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    let v : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hrn, hk_w, hn_w, hk_lt, hw]
    have hbr_idx_lt : wallBrOf W v < elemWallNumVerts h + 1 :=
      Nat.lt_succ_of_le (wallBrOf_le W v)
    have hedge_idx_lt : wallEdgeOf W v < (elemWallEdges h).length + 1 :=
      Nat.lt_succ_of_le (wallEdgeOf_le W v)
    have hbr_idx_w : wallBrOf W v < 2 ^ w := by omega
    have hedge_idx_w : wallEdgeOf W v < 2 ^ w := by omega
    let b1 := predTableVal brPred (wallBrOf W v)
    let b2 := predTableVal edgePred (wallEdgeOf W v)
    have hb1_le : b1 ≤ 1 := predTableVal_le_one brPred (wallBrOf W v)
    have hb2_le : b2 ≤ 1 := predTableVal_le_one edgePred (wallEdgeOf W v)
    have hb1_w : b1 < 2 ^ w := by omega
    have hb2_w : b2 < 2 ^ w := by omega
    have hsum_w : b1 + b2 < 2 ^ w := by omega
    let s₁ := s.setReg (r_base + 1) (wallBrOf W v)
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_W_brOf (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrv, hk_w, hbrOf, hk_lt, v, hbr_idx_w])
    let s₂ := s₁.setReg (r_base + 1) b1
    have hex₂ : Exec w (.assign (r_base + 1) (.read a_brTab (.reg (r_base + 1)))) s₁ s₂ 3 :=
      .assign (eval_read_predTableList brPred s₁ a_brTab (r_base + 1)
        (by simp [s₁, hbrTab]) (by simp [s₁]) hbr_idx_w hbr_idx_lt hw)
    let s₃ := s₂.setReg (r_base + 2) (wallEdgeOf W v)
    have hex₃ : Exec w (.assign (r_base + 2) (.read a_W_edgeOf (.reg r_base))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, Expr.eval, checkWord, hrv, hk_w, hedgeOf, hk_lt, v, hedge_idx_w])
    let s₄ := s₃.setReg (r_base + 2) b2
    have hex₄ : Exec w (.assign (r_base + 2) (.read a_edgeTab (.reg (r_base + 2)))) s₃ s₄ 3 :=
      .assign (eval_read_predTableList edgePred s₃ a_edgeTab (r_base + 2)
        (by simp [s₃, s₂, s₁, hedgeTab]) (by simp [s₃]) hedge_idx_w hedge_idx_lt hw)
    let bit := if wallSubsetInd W brPred edgePred v then 1 else 0
    have hbit_eq : (if 0 < b1 ∨ 0 < b2 then 1 else 0) = bit :=
      ite_predTableVal_eq_wallSubsetInd W brPred edgePred v
    have hbit_w : bit < 2 ^ w := by dsimp [bit]; split_ifs <;> omega
    have hout_len : k < (s₄.arrs a_out).length := by
      simp [s₄, s₃, s₂, s₁, hout, Nat.min_eq_left (Nat.le_of_lt hk_lt)]
    let s₅ := s₄.writeArr a_out k bit
    have hex₅ :
        Exec w
          (.write a_out (.reg r_base)
            (.op .lt (.const 0) (.op .add (.reg (r_base + 1)) (.reg (r_base + 2)))))
          s₄ s₅ 7 :=
      .write (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hrv, hk_w])
        (by simp [s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hb1_w, hb2_w, hsum_w, h0_w, hbit_eq, hbit_w])
        hout_len
    let s₆ := s₅.setReg r_base (k + 1)
    have hex₆ : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrv, hk_w, hw, hk1_w])
    have hout₆ :
        s₆.arrs a_out = targetList.take (k + 1) ++ List.replicate rem 0 := by
      change s.arrs a_out = targetList.take k ++ List.replicate (rem + 1) 0 at hout
      have h6 : s₆.arrs a_out = (s.arrs a_out).set k bit := by
        simp [s₆, s₅, s₄, s₃, s₂, s₁]
      rw [h6]
      have hlen_t : k < targetList.length := by simp [targetList, hk_lt]
      have hget_t : targetList[k]'hlen_t = bit := by simp [targetList, bit, v]
      have hlen_take : (targetList.take k).length = k := by
        simp [targetList, Nat.min_eq_left (Nat.le_of_lt hk_lt)]
      rw [hout, List.set_append_right _ _ (by rw [hlen_take]), hlen_take, Nat.sub_self,
        take_add_one_eq_append_getElem targetList k hlen_t, hget_t]
      simp [List.replicate_succ, List.set_cons_zero, List.append_assoc]
    rcases ih (k + 1) (by omega) (s := s₆)
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_bo, hbrOf])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_eo, hedgeOf])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_bt, hbrTab])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hne_et, hedgeTab])
        hout₆
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
          show r_n ≠ r_base by omega,
          show r_n ≠ r_base + 1 by omega,
          show r_n ≠ r_base + 2 by omega, hrn])
        (by simp [s₆]) with
      ⟨s₇, t₇, hex₇, ht₇, hout₇, harr₇, hreg₇⟩
    refine ⟨s₇, 3 + ((3 + (3 + (3 + (3 + 7)))) + 4) + t₇,
      .while_true hcond (by omega)
        (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))) hex₆) hex₇,
      by omega, hout₇,
      fun a ha => by rw [harr₇ a ha]; simp [s₆, s₅, s₄, s₃, s₂, s₁, ha],
      fun r hr => by
        rw [hreg₇ r hr]
        simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg,
          show r ≠ r_base by omega,
          show r ≠ r_base + 1 by omega,
          show r ≠ r_base + 2 by omega]⟩

theorem buildWallSubsetBitSetProg_exec {w h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del)
    (brPred : Fin (elemWallNumVerts h) → Bool)
    (edgePred : Fin (elemWallEdges h).length → Bool)
    (a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out r_n r_base : ℕ)
    (hne_bo_bt : a_W_brOf ≠ a_brTab) (hne_bo_et : a_W_brOf ≠ a_edgeTab) (hne_bo : a_W_brOf ≠ a_out)
    (hne_eo_bt : a_W_edgeOf ≠ a_brTab) (hne_eo_et : a_W_edgeOf ≠ a_edgeTab) (hne_eo : a_W_edgeOf ≠ a_out)
    (hne_bt_et : a_brTab ≠ a_edgeTab) (hne_bt : a_brTab ≠ a_out) (hne_et : a_edgeTab ≠ a_out)
    (hr_n : r_n < r_base)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hnv_w : elemWallNumVerts h + 1 < 2 ^ w)
    (hne_w : (elemWallEdges h).length + 1 < 2 ^ w)
    {s : State}
    (hbrOf : s.arrs a_W_brOf = List.ofFn (wallBrOf W))
    (hedgeOf : s.arrs a_W_edgeOf = List.ofFn (wallEdgeOf W))
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (buildWallSubsetBitSetProg brPred edgePred
        a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out r_n r_base) s s' t ∧
      t ≤ 28 * n + 6 * elemWallNumVerts h + 6 * (elemWallEdges h).length + 28 ∧
      s'.arrs a_out =
        bitSetList (Finset.univ.filter (fun v : Fin n => wallSubsetInd W brPred edgePred v = true)) ∧
      (∀ a : ℕ, a ≠ a_brTab → a ≠ a_edgeTab → a ≠ a_out → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hbt_w : ∀ x ∈ predTableList brPred, x < 2 ^ w := fun x hx =>
    Nat.lt_of_le_of_lt (predTableList_le_one brPred hx) hw
  have het_w : ∀ x ∈ predTableList edgePred, x < 2 ^ w := fun x hx =>
    Nat.lt_of_le_of_lt (predTableList_le_one edgePred hx) hw
  rcases writeConstListProg_exec a_brTab r_base (predTableList brPred)
      hw (by rw [length_predTableList]; exact hnv_w) hbt_w s with
    ⟨s₁, t₁, hex₁, ht₁, hbt₁, harr₁, hreg₁⟩
  rcases writeConstListProg_exec a_edgeTab r_base (predTableList edgePred)
      hw (by rw [length_predTableList]; exact hne_w) het_w s₁ with
    ⟨s₂, t₂, hex₂, ht₂, het₂, harr₂, hreg₂⟩
  have hrn₂ : s₂.regs r_n = n := by
    rw [hreg₂ r_n (by omega), hreg₁ r_n (by omega), hrn]
  let s₃ := s₂.setArr a_out (List.replicate n 0)
  have hex₃ : Exec w (.alloc a_out (.reg r_n)) s₂ s₃ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn₂, hn_w])
  let s₄ := s₃.setReg r_base 0
  have hex₄ : Exec w (.assign r_base (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases buildWallSubsetLoop_exec W brPred edgePred
      a_W_brOf a_W_edgeOf a_brTab a_edgeTab a_out r_n r_base
      hne_bo hne_eo hne_bt hne_et hr_n hw2 hn_w hnv_w hne_w n 0 (by omega)
      (s := s₄)
      (by simp [s₄, s₃, hne_bo, harr₂ a_W_brOf hne_bo_et, harr₁ a_W_brOf hne_bo_bt, hbrOf])
      (by simp [s₄, s₃, hne_eo, harr₂ a_W_edgeOf hne_eo_et, harr₁ a_W_edgeOf hne_eo_bt, hedgeOf])
      (by simp [s₄, s₃, hne_bt, harr₂ a_brTab hne_bt_et, hbt₁])
      (by simp [s₄, s₃, hne_et, het₂])
      (by simp [s₄, s₃])
      (by simp [s₄, s₃, State.setReg, show r_n ≠ r_base by omega, hrn₂])
      (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, harr₅, hreg₅⟩
  simp only [length_predTableList] at ht₁ ht₂
  refine ⟨s₅, t₁ + (t₂ + ((1 + n) + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hout₅,
    fun a ha₁ ha₂ ha₃ => by
      rw [harr₅ a ha₃]
      simp [s₄, s₃, ha₃, harr₂ a ha₂, harr₁ a ha₁],
    fun r hr => by
      rw [hreg₅ r hr]
      simp [s₄, s₃, State.setReg, show r ≠ r_base by omega,
        hreg₂ r (by omega), hreg₁ r (by omega)]⟩

end GraphMinor.Compute

