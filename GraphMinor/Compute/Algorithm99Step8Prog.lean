module

public import GraphMinor.Compute.Algorithm99Step8Filter
public import GraphMinor.Compute.Algorithm99Tab
public import GraphMinor.Compute.Algorithm99MoveBlock
import GraphMinor.Compute.Algorithm99Step4Scan

/-!
# Step (8) of Algorithm (9.9): the program

Step (8) of Algorithm (9.9) (Graph Minors XIII, page 105) reads: "(8) If for some interior
$A \in \mathcal{A}$ we obtain a wall $H_{i+1}$ in $A$ of height $h'$, we let $G_{i+1}$ be the
subgraph of $G_i$ with vertex set $V(A) \cup X$ and edges those edges of $G_i$ with an end in
$V(A)$ and the other end in $V(A) \cup X$." Later the paper sets "$Z_{i+1} = X \cup \partial A$".
The next state is `Alg99Iter.step8` (`Algorithm99Step8.lean`).

The program `alg99Step8Prog` writes this next state over the stored state (arrays `B + 1` to
`B + 4`, `Alg99Iter.StoredIn`). It reads the bit sets of `X`, `V(A)` and `∂A`, and the code of
the wall `H_{i+1}` that steps (5) to (7) return (in the labels of `G_i`). With `U = V(A) ∪ X`:

1. it writes the bit sets of `U`, of the complement of `U`, and of `X ∪ ∂A`;
2. it keeps the edges of `G_i` between `V(A)` and `U` (`step8RestrictProg`), and renumbers the
   vertices of `U` as `0, 1, …` in their order (`deleteVerticesCompactProg`); this gives the code
   of `G_{i+1}` and the new number of each vertex;
3. it writes the old number of each new vertex (`compactOrigProg`), and composes `orig` with it;
4. it writes the bit set of the new `Z` (the new vertices whose old number is in `X ∪ ∂A`);
5. it copies the code of the wall and renames each vertex by its new number (`mvWall`).

The main result is `alg99Step8Prog_exec`: the program ends with `st.step8 X V_A Bd W_A` stored,
in time `O(|active pairs of G_i| + v_i + |code of the wall|)`.
-/

@[expose] public section

namespace GraphMinor.Compute

open WallOfHeight

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

variable {v n : ℕ}

/-! ### The words of the next state -/

/-- The bit set of the complement, entry by entry. -/
theorem ofFn_one_sub_bitSetList (U : Finset (Fin v)) :
    List.ofFn (fun i : Fin v => 1 - (if i ∈ U then 1 else 0)) = bitSetList Uᶜ := by
  unfold bitSetList
  congr 1
  funext i
  by_cases h : i ∈ U <;> simp [h]

/-- The code of a moved wall, renamed by `φ`, is the code of the wall moved by `f`, when `φ`
sends the image of each vertex under `e` to its image under `f`. -/
theorem renamedEncList_moveOrig {h m k : ℕ} {A : MultiDigraph v} {B : MultiDigraph m}
    {C : MultiDigraph k} (W : WallOfHeight h A) (e : Fin v → Fin m) (f : Fin v → Fin k)
    (φ : ℕ → ℕ) (hφ : ∀ u : Fin v, φ (e u).1 = (f u).1) :
    (W.moveOrig B e).renamedEncList φ = (W.moveOrig C f).encList := by
  simp [renamedEncList, encList, branchWords, internalRuns, mvRunsCode, moveOrig,
    List.flatMap_map, hφ, Function.comp_def]

/-- The new wall: renaming the code of `W_A` in the labels of `G_i` by the new numbers gives the
code of `H_{i+1}` of `st.step8`. -/
theorem renamedEncList_step8Wall {h : ℕ} (V_A X : Finset (Fin v)) {A_sub : MultiDigraph v}
    {D : MultiDigraph (V_A ∪ X)ᶜᶜ.card}
    (W_A : WallOfHeight h (A_sub.deleteVerticesCompact V_Aᶜ)) :
    (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).renamedEncList
        (fun x => (List.ofFn (fun u : Fin v => compactRank (V_A ∪ X)ᶜ u.1)).getD x 0) =
      (W_A.moveOrig D (step8WallMap V_A X)).encList := by
  apply renamedEncList_moveOrig
  intro u
  simp [step8WallMap, List.getD_eq_getElem?_getD]

/-! ### The program -/

/-- The program of step (8) of (9.9). The state is stored in arrays `B + 1` to `B + 4`; the bit
sets of `X`, `V(A)` and `∂A` are in `a_X`, `a_V`, `a_bd`, and the code of the wall in `a_wall`.
Arrays `T` to `T + 7` and registers from `R` on are scratch. -/
def alg99Step8Prog (B T : Arr) (a_X a_V a_bd a_wall : Arr) (R : Reg) : Cmd :=
  .seq (.assign R (.read (B + 1) (.const 0)))
  (.seq (unionBitSetProg a_V a_X T R (R + 2))
  (.seq (tabProg (T + 1) R (R + 2) (.op .sub (.const 1) (.read T (.reg (R + 2)))))
  (.seq (unionBitSetProg a_X a_bd (T + 7) R (R + 2))
  (.seq (step8RestrictProg (B + 1) a_V T (T + 3) (T + 2) (R + 10))
  (.seq (deleteVerticesCompactProg (T + 2) (T + 1) (T + 3) (T + 4) (B + 1) (R + 10))
  (.seq (.assign (R + 1) (.read (B + 1) (.const 0)))
  (.seq (compactOrigProg (T + 1) (T + 4) (T + 5) R (R + 1) (R + 2))
  (.seq (tabProg (T + 6) (R + 1) (R + 2) (.read (B + 2) (.read (T + 5) (.reg (R + 2)))))
  (.seq (copyArrLoopProg (T + 6) (B + 2) (R + 3) (R + 4))
  (.seq (tabProg (B + 3) (R + 1) (R + 2) (.read (T + 7) (.read (T + 5) (.reg (R + 2)))))
  (.seq (copyArrLoopProg a_wall (B + 4) (R + 3) (R + 4))
  (.seq (.assign (R + 3) (.const 0))
    (mvWall (B + 4) (T + 4) (R + 3))))))))))))))

/-! ### Reading words -/


theorem eval_reg_of_eq {w : ℕ} {s : State} {r : Reg} {i : ℕ} (hr : s.regs r = i)
    (hi : i < 2 ^ w) : (Expr.reg r).eval w s = some i := by
  simp [Expr.eval, checkWord, hr, hi]

theorem eval_op_of_eval {w : ℕ} {s : State} {bop : BinOp} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w s = some a) (h₂ : e₂.eval w s = some b) :
    (Expr.op bop e₁ e₂).eval w s = bop.eval w a b := by
  simp [Expr.eval, h₁, h₂]

theorem eval_read_of_eval {w : ℕ} {s : State} {a : Arr} {e : Expr} {l : List ℕ} {i : ℕ}
    (he : e.eval w s = some i) (ha : s.arrs a = l) (hi : i < l.length)
    (hl_w : l.getD i 0 < 2 ^ w) : (Expr.read a e).eval w s = some (l.getD i 0) := by
  have hi' : i < (s.arrs a).length := ha ▸ hi
  rw [List.getD_eq_getElem _ _ hi] at hl_w ⊢
  simp [Expr.eval, he, checkWord, ha]
  exact ⟨hi, hl_w⟩

/-! ### The execution theorem -/

/-- **Step (8) of Algorithm (9.9), the program** (Graph Minors XIII, page 105). Let the state
`st` be stored in arrays `B + 1` to `B + 4`, and let `a_X`, `a_V`, `a_bd` hold the bit sets of
`X`, `V(A)`, `∂A` and `a_wall` the code of the wall of height `h'` found in `A` (in the labels of
`G_i`). These arrays are at most `B`, and the scratch arrays `T, …, T + 7` are above `B + 4`. Then
`alg99Step8Prog` ends with the next state `st.step8 X V_A Bd W_A` stored in arrays `B + 1` to
`B + 4`, in time `≤ 300 m' + 150 v + 50 L + 400` (`m'` the number of active pairs of `G_i`, `L`
the length of the code of the wall). It changes no other array below `T` and no register below
`R`. -/
theorem alg99Step8Prog_exec {w h' : ℕ} {G : MultiDigraph n} {st : Alg99Iter h' G}
    (X V_A Bd : Finset (Fin st.v)) {A_sub : MultiDigraph st.v}
    (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ))
    {B T a_X a_V a_bd a_wall R : ℕ}
    (hXB : a_X < B + 1) (hVB : a_V < B + 1) (hbdB : a_bd < B + 1) (hwB : a_wall < B + 1)
    (hBT : B + 4 < T)
    (hw3 : 3 < 2 ^ w) (hv_w : st.v + 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * st.Gi.numActivePairs < 2 ^ w) (hE_w : st.Gi.numEdges < 2 ^ w)
    (hL_w : (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList.length < 2 ^ w)
    (hLv_w : ∀ x ∈ (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList, x < 2 ^ w)
    {s : State} (hst : st.StoredIn B s)
    (hX : s.arrs a_X = bitSetList X) (hV : s.arrs a_V = bitSetList V_A)
    (hBd : s.arrs a_bd = bitSetList Bd)
    (hW : s.arrs a_wall = (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList) :
    ∃ s' t, Exec w (alg99Step8Prog B T a_X a_V a_bd a_wall R) s s' t ∧
      t ≤ 300 * st.Gi.numActivePairs + 150 * st.v +
        50 * (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList.length + 400 ∧
      (st.step8 X V_A Bd W_A).StoredIn B s' ∧
      (∀ a : ℕ, a ≠ B + 1 → a ≠ B + 2 → a ≠ B + 3 → a ≠ B + 4 → (a < T ∨ T + 7 < a) →
        s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < R → s'.regs r = s.regs r) := by
  obtain ⟨hG1, hG2, hG3, hG4⟩ := hst
  set U := V_A ∪ X with hU
  set c := Uᶜᶜ.card with hc
  set GR := st.Gi.restrictMult (step8Pred V_A X) with hGR
  set L := (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList with hL
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hv_w' : st.v < 2 ^ w := by omega
  have hc_le : c ≤ st.v := by
    calc c ≤ (Finset.univ : Finset (Fin st.v)).card := Finset.card_le_univ _
      _ = st.v := Finset.card_fin _
  have hc_w : c < 2 ^ w := by omega
  -- 1. `R := v`.
  obtain ⟨h0len, h0val⟩ := enc_getElem_zero st.Gi [] (l := s.arrs (B + 1)) (by rw [hG1, List.append_nil])
  let s₁ := s.setReg R st.v
  have hex₁ : Exec w (.assign R (.read (B + 1) (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0len, h0val, hv_w', show (0 : ℕ) < 2 ^ w by omega])
  -- 2. The bit set of `U`.
  obtain ⟨s₂, t₂, hex₂, ht₂, hT₂, harr₂, hreg₂⟩ :=
    unionBitSetProg_exec V_A X a_V a_X T R (R + 2) (by romega) (by romega) (by romega) hw2 hv_w'
      (s := s₁) hV hX (by simp [s₁])
  -- 3. The bit set of the complement of `U`.
  obtain ⟨s₃, t₃, hex₃, ht₃, hT₃, harr₃, hreg₃⟩ :=
    tabProg_exec (T + 1) R (R + 2) (.op .sub (.const 1) (.read T (.reg (R + 2))))
      (fun i => 1 - (bitSetList U).getD i 0) (by romega) hw hv_w' (s := s₂)
      (by rw [hreg₂ R (by romega)]; simp [s₁])
      (fun s' ha hr i hi hri => by
        have hT' : s'.arrs T = bitSetList U := by rw [ha T (by romega), hT₂]
        have hread := eval_read_of_eval (eval_reg_of_eq hri (lt_trans hi hv_w')) hT'
          (by rw [length_bitSetList]; exact hi)
          (by rw [getD_bitSetList _ ⟨i, hi⟩]; split_ifs <;> omega)
        have hle : (bitSetList U).getD i 0 ≤ 1 := by
          rw [getD_bitSetList _ ⟨i, hi⟩]; split_ifs <;> omega
        rw [eval_op_of_eval (a := 1) (by simp [Expr.eval, checkWord, hw]) hread]
        simp only [BinOp.eval, BinOp.raw]
        exact checkWord_of_lt (by omega))
  have hT₃' : s₃.arrs (T + 1) = bitSetList Uᶜ := by
    rw [hT₃, ← ofFn_one_sub_bitSetList]
    congr 1
    funext i
    rw [getD_bitSetList _ i]
  -- 4. The bit set of `X ∪ ∂A`.
  obtain ⟨s₄, t₄, hex₄, ht₄, hT₄, harr₄, hreg₄⟩ :=
    unionBitSetProg_exec X Bd a_X a_bd (T + 7) R (R + 2) (by romega) (by romega) (by romega) hw2
      hv_w' (s := s₃)
      (by rw [harr₃ _ (by romega), harr₂ _ (by romega)]; exact hX)
      (by rw [harr₃ _ (by romega), harr₂ _ (by romega)]; exact hBd)
      (by rw [hreg₃ R (by romega), hreg₂ R (by romega)]; simp [s₁])
  -- 5. The kept edges.
  have hGi₄ : s₄.arrs (B + 1) = st.Gi.enc := by
    rw [harr₄ _ (by romega), harr₃ _ (by romega), harr₂ _ (by romega)]; exact hG1
  obtain ⟨s₅, t₅, hex₅, ht₅, hT₅, harr₅, hreg₅⟩ :=
    step8RestrictProg_exec st.Gi V_A X (B + 1) a_V T (T + 3) (T + 2) (R + 10)
      (by romega) (by romega) (by romega) (by romega) hw3 hv_w' hm3_w hE_w (s := s₄) hGi₄
      (by rw [harr₄ _ (by romega), harr₃ _ (by romega), harr₂ _ (by romega)]; exact hV)
      (by rw [harr₄ _ (by romega), harr₃ _ (by romega), hT₂])
  -- 6. Renumber the vertices of `U`.
  have hGRp : GR.numActivePairs ≤ st.Gi.numActivePairs :=
    MultiDigraph.numActivePairs_restrictMult_le _ _
  have hGRe : GR.numEdges ≤ st.Gi.numEdges := MultiDigraph.numEdges_restrictMult_le _ _
  obtain ⟨s₆, t₆, hex₆, ht₆, hB₆, hrank₆, harr₆, hreg₆⟩ :=
    deleteVerticesCompactProg_exec GR Uᶜ (T + 2) (T + 1) (T + 3) (T + 4) (B + 1) (R + 10)
      (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) hw3 hv_w' (by romega)
      (by romega) (s := s₅) hT₅
      (by rw [harr₅ _ (by romega) (by romega), harr₄ _ (by romega), hT₃'])
  -- 7. `R + 1 := |U|`.
  obtain ⟨h0len', h0val'⟩ := enc_getElem_zero (GR.deleteVerticesCompact Uᶜ) [] (l := s₆.arrs (B + 1))
    (by rw [hB₆, List.append_nil])
  let s₇ := s₆.setReg (R + 1) c
  have hex₇ : Exec w (.assign (R + 1) (.read (B + 1) (.const 0))) s₆ s₇ 3 :=
    .assign (by
      simp [Expr.eval, checkWord, h0len', h0val', show (0 : ℕ) < 2 ^ w by omega]
      exact ⟨by simpa [c] using hc_w, by simp [c]⟩)
  -- 8. The old number of each new vertex.
  have hR₇ : s₇.regs R = st.v := by
    simp only [s₇, State.setReg_regs_ne _ _ (show R ≠ R + 1 by omega)]
    rw [hreg₆ R (by romega), hreg₅ R (by romega), hreg₄ R (by romega), hreg₃ R (by romega),
      hreg₂ R (by romega)]
    simp [s₁]
  obtain ⟨s₈, t₈, hex₈, ht₈, hT₈, harr₈, hreg₈⟩ :=
    compactOrigProg_exec Uᶜ (T + 1) (T + 4) (T + 5) R (R + 1) (R + 2) (by romega) (by romega)
      (by romega) hw2 hv_w' (s := s₇)
      (by simp only [s₇, State.setReg_arrs]
          rw [harr₆ _ (by romega) (by romega) (by romega), harr₅ _ (by romega) (by romega)]
          rw [harr₄ _ (by romega)]; exact hT₃')
      (by simp only [s₇, State.setReg_arrs]; exact hrank₆) hR₇ (by simp [s₇, c])
  -- Facts about the lists read below.
  set embL := List.ofFn (fun j : Fin c => (compactEmb Uᶜ j).1) with hembL
  set origL := List.ofFn (fun u : Fin st.v => (st.orig u).1) with horigL
  set rankL := List.ofFn (fun u : Fin st.v => compactRank Uᶜ u.1) with hrankL
  have hemb_lt : ∀ i (hi : i < c), embL.getD i 0 < st.v := fun i hi => by
    rw [getD_ofFn _ hi]; exact (compactEmb Uᶜ ⟨i, hi⟩).2
  have hR1₈ : s₈.regs (R + 1) = c := by rw [hreg₈ _ (by romega)]; simp [s₇]
  have hB2₈ : s₈.arrs (B + 2) = origL := by
    rw [harr₈ _ (by romega)]
    simp only [s₇, State.setReg_arrs]
    rw [harr₆ _ (by romega) (by romega) (by romega), harr₅ _ (by romega) (by romega),
      harr₄ _ (by romega), harr₃ _ (by romega), harr₂ _ (by romega)]
    exact hG2
  -- 9. The new `orig`, in `T + 6`.
  obtain ⟨s₉, t₉, hex₉, ht₉, hT₉, harr₉, hreg₉⟩ :=
    tabProg_exec (T + 6) (R + 1) (R + 2) (.read (B + 2) (.read (T + 5) (.reg (R + 2))))
      (fun i => origL.getD (embL.getD i 0) 0) (by romega) hw hc_w (s := s₈) hR1₈
      (fun s' ha hr i hi hri => by
        have h5 : s'.arrs (T + 5) = embL := by rw [ha _ (by romega), hT₈]
        have h2 : s'.arrs (B + 2) = origL := by rw [ha _ (by romega), hB2₈]
        have he5 := eval_read_of_eval (eval_reg_of_eq hri (lt_trans hi hc_w)) h5 (by simpa [embL] using hi)
          (by have := hemb_lt i hi; romega)
        exact eval_read_of_eval he5 h2 (by simpa [origL] using hemb_lt i hi)
          (by rw [getD_ofFn _ (hemb_lt i hi)]; exact lt_trans (st.orig _).2 hn_w))
  -- 10. Copy it to `B + 2`.
  have horig_new : s₉.arrs (T + 6) =
      List.ofFn (fun j : Fin c => ((st.orig ∘ compactEmb Uᶜ) j).1) := by
    rw [hT₉]
    congr 1
    funext j
    rw [getD_ofFn _ j.2, horigL, getD_ofFn _ (compactEmb Uᶜ _).2]
    rfl
  obtain ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hB2₁₀, harr₁₀, hreg₁₀⟩ :=
    copyArrLoopProg_exec (T + 6) (B + 2) (R + 3) (R + 4) (by romega) (by romega) hw s₉
      (by rw [horig_new, List.length_ofFn]; exact hc_w)
      (by
        rw [horig_new]
        intro x hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
        exact lt_trans (st.orig _).2 hn_w)
  -- 11. The new `Z`, in `B + 3`.
  have hR1₁₀ : s₁₀.regs (R + 1) = c := by
    rw [hreg₁₀ _ (by romega) (by romega), hreg₉ _ (by romega), hR1₈]
  have hT5₁₀ : s₁₀.arrs (T + 5) = embL := by
    rw [harr₁₀ _ (by romega), harr₉ _ (by romega), hT₈]
  have hT7₁₀ : s₁₀.arrs (T + 7) = bitSetList (X ∪ Bd) := by
    rw [harr₁₀ _ (by romega), harr₉ _ (by romega), harr₈ _ (by romega)]
    simp only [s₇, State.setReg_arrs]
    rw [harr₆ _ (by romega) (by romega) (by romega), harr₅ _ (by romega) (by romega), hT₄]
  obtain ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hB3₁₁, harr₁₁, hreg₁₁⟩ :=
    tabProg_exec (B + 3) (R + 1) (R + 2) (.read (T + 7) (.read (T + 5) (.reg (R + 2))))
      (fun i => (bitSetList (X ∪ Bd)).getD (embL.getD i 0) 0) (by romega) hw hc_w (s := s₁₀)
      hR1₁₀
      (fun s' ha hr i hi hri => by
        have h5 : s'.arrs (T + 5) = embL := by rw [ha _ (by romega), hT5₁₀]
        have h7 : s'.arrs (T + 7) = bitSetList (X ∪ Bd) := by rw [ha _ (by romega), hT7₁₀]
        have he5 := eval_read_of_eval (eval_reg_of_eq hri (lt_trans hi hc_w)) h5
          (by simpa [embL] using hi) (by have := hemb_lt i hi; romega)
        exact eval_read_of_eval he5 h7 (by rw [length_bitSetList]; exact hemb_lt i hi)
          (by rw [getD_bitSetList _ ⟨_, hemb_lt i hi⟩]; split_ifs <;> omega))
  have hZ_new : s₁₁.arrs (B + 3) =
      bitSetList (Finset.univ.filter (fun j : Fin c => compactEmb Uᶜ j ∈ X ∪ Bd)) := by
    rw [hB3₁₁]
    unfold bitSetList
    congr 1
    funext j
    rw [getD_ofFn _ j.2]
    rw [show ((compactEmb Uᶜ) ⟨j.1, j.2⟩).1 = ((compactEmb Uᶜ) j).1 from rfl]
    rw [getD_ofFn (fun u : Fin st.v => if u ∈ X ∪ Bd then 1 else 0) (compactEmb Uᶜ j).2]
    simp
  -- 12. Copy the wall to `B + 4`.
  have hwall₁₁ : s₁₁.arrs a_wall = L := by
    rw [harr₁₁ _ (by romega), harr₁₀ _ (by romega), harr₉ _ (by romega),
      harr₈ _ (by romega)]
    simp only [s₇, State.setReg_arrs]
    rw [harr₆ _ (by romega) (by romega) (by romega), harr₅ _ (by romega) (by romega),
      harr₄ _ (by romega), harr₃ _ (by romega), harr₂ _ (by romega)]
    exact hW
  obtain ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hB4₁₂, harr₁₂, hreg₁₂⟩ :=
    copyArrLoopProg_exec a_wall (B + 4) (R + 3) (R + 4) (by romega) (by romega) hw s₁₁
      (by rw [hwall₁₁]; exact hL_w) (by rw [hwall₁₁]; exact hLv_w)
  -- 13. Rename the vertices of the wall.
  let s₁₃ := s₁₂.setReg (R + 3) 0
  have hex₁₃ : Exec w (.assign (R + 3) (.const 0)) s₁₂ s₁₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  have hrank₁₃ : s₁₃.arrs (T + 4) = rankL := by
    simp only [s₁₃, State.setReg_arrs]
    rw [harr₁₂ _ (by romega), harr₁₁ _ (by romega), harr₁₀ _ (by romega),
      harr₉ _ (by romega), harr₈ _ (by romega)]
    simp only [s₇, State.setReg_arrs]
    exact hrank₆
  obtain ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hB4₁₄, -, harr₁₄, hreg₁₄⟩ :=
    mvWall_exec (W_A.moveOrig A_sub (compactEmb V_Aᶜ)) (a := B + 4) (o := T + 4) (by romega)
      (R + 3) (s := s₁₃) (D := []) (T := [])
      (by simp only [s₁₃, State.setReg_arrs]; rw [hB4₁₂, hwall₁₁]; simpa using hL)
      (by simp [s₁₃])
      (by rw [hrank₁₃]; simp [rankL])
      (by omega)
      (by
        rw [hrank₁₃]
        intro y hy
        obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hy
        exact lt_of_le_of_lt (compactRank_le _ _) hv_w')
      hw (by simpa using hL_w)
  -- The end.
  have hB1_end : s₁₄.arrs (B + 1) = s₆.arrs (B + 1) := by
    rw [harr₁₄ _ (by romega)]
    simp only [s₁₃, State.setReg_arrs]
    rw [harr₁₂ _ (by romega), harr₁₁ _ (by romega), harr₁₀ _ (by romega),
      harr₉ _ (by romega), harr₈ _ (by romega)]
    rfl
  have hB2_end : s₁₄.arrs (B + 2) = s₁₀.arrs (B + 2) := by
    rw [harr₁₄ _ (by romega)]
    simp only [s₁₃, State.setReg_arrs]
    rw [harr₁₂ _ (by romega), harr₁₁ _ (by romega)]
  have hB3_end : s₁₄.arrs (B + 3) = s₁₁.arrs (B + 3) := by
    rw [harr₁₄ _ (by romega)]
    simp only [s₁₃, State.setReg_arrs]
    rw [harr₁₂ _ (by romega)]
  simp only [Expr.cost] at ht₃ ht₉ ht₁₁
  rw [horig_new, List.length_ofFn] at ht₁₀
  rw [hwall₁₁] at ht₁₂
  refine ⟨s₁₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
    (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂
    (.seq hex₁₃ hex₁₄)))))))))))), ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have := MultiDigraph.numActivePairs_restrictMult_le st.Gi (step8Pred V_A X)
    have h9 : (1 + 1 + 1 + 10) * c ≤ 13 * st.v := by omega
    have hL' : (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList.length = L.length := by rw [hL]
    rw [hL']
    omega
  · rw [hB1_end, hB₆]
    rfl
  · rw [hB2_end, hB2₁₀, horig_new]
  · rw [hB3_end, hZ_new]
  · rw [hB4₁₄]
    simp only [List.nil_append, List.append_nil]
    rw [hrank₁₃]
    exact renamedEncList_step8Wall V_A X W_A
  · intro a h1 h2 h3 h4 hT
    rw [harr₁₄ _ (by romega)]
    simp only [s₁₃, State.setReg_arrs]
    rw [harr₁₂ _ (by romega), harr₁₁ _ (by romega), harr₁₀ _ (by romega),
      harr₉ _ (by romega), harr₈ _ (by romega)]
    simp only [s₇, State.setReg_arrs]
    rw [harr₆ _ (by romega) (by romega) (by romega), harr₅ _ (by romega) (by romega),
      harr₄ _ (by romega), harr₃ _ (by romega), harr₂ _ (by romega)]
    rfl
  · intro r hr
    rw [hreg₁₄ _ (by romega) (by romega) (by romega) (by romega) (by romega)]
    simp only [s₁₃, State.setReg_regs_ne _ _ (show r ≠ R + 3 by omega)]
    rw [hreg₁₂ _ (by romega) (by romega), hreg₁₁ _ (by romega), hreg₁₀ _ (by romega) (by romega),
      hreg₉ _ (by romega), hreg₈ _ (by romega)]
    simp only [s₇, State.setReg_regs_ne _ _ (show r ≠ R + 1 by omega)]
    rw [hreg₆ _ (by romega), hreg₅ _ (by romega), hreg₄ _ (by romega), hreg₃ _ (by romega),
      hreg₂ _ (by romega)]
    simp only [s₁, State.setReg_regs_ne _ _ (show r ≠ R by omega)]

end GraphMinor.Compute
