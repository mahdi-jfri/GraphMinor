module

public import GraphMinor.Compute.TwoPathsUnion
public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.Restrict
public import GraphMinor.Compute.TwoPathsSplit

/-!
# The two sides of a split

After a completion that returned new edges `F` and a path `P' = a m b`, line 10 of Algorithm 5.1
splits the instance along `P'`. Side `1` is `P'` together with the vertices that `A` reaches in
`H' - P'`, where `H' = H + F`; side `2` is `P'` together with the other vertices (`sideOne`,
`sideTwo`).

`sideProg i` builds the lists of `H'` (`unionProg`), runs one search in `H' - P'` from the
vertices of `A`, and writes the bit set of side `i` in array `aY`. After the search a vertex has
label `1` when it was reached, `2` when it is on `P'`, and `0` otherwise. So side `1` is the set
of vertices with a label other than `0`, and side `2` the set of vertices with a label other than
`1` (`mem_items_iff` says that the reached vertices are those of `reachOff`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### Walks that avoid a set -/

/-- A walk of `restrict G S` that starts in `S` is a walk of `G` whose vertices all lie in `S`. -/
theorem exists_walk_of_restrict {V : Type*} {G : SimpleGraph V} {S : Set V} {u v : V}
    (W : (restrict G S).Walk u v) (hu : u ∈ S) : ∃ W' : G.Walk u v, ∀ y ∈ W'.support, y ∈ S := by
  induction W with
  | nil => exact ⟨.nil, by simpa using hu⟩
  | @cons x y z hxy W ih =>
    obtain ⟨W', hW'⟩ := ih hxy.2.2
    exact ⟨.cons hxy.1 W', by
      intro t ht
      rcases (Walk.mem_support_iff _).mp ht with rfl | ht
      · exact hu
      · exact hW' t ht⟩

/-- The labels of the side search: `P'` forbidden, everything else free. -/
def labQ (Pv : List (Fin n)) (v : Fin n) : ℕ := if v ∈ Pv then 2 else 0

/-- **The reached vertices are those of `reachOff`.** After a search from `A` with the vertices of
`P'` forbidden and no target, a vertex was reached exactly when `A` reaches it in `H' - P'`. -/
theorem mem_items_iff {G : SimpleGraph (Fin n)} {Pv A : List (Fin n)} {s₀ s : State}
    {items : List ℕ} (hs : SInv G (labQ Pv) (A.map Fin.val) s₀ items items.length s)
    (hAP : ∀ v ∈ A, v ∉ Pv) (v : Fin n) : v.1 ∈ items ↔ v ∈ reachOff G Pv A := by
  constructor
  · intro hv
    obtain ⟨p, -, hp⟩ := hs.par
    obtain ⟨r, W, -, hr, hall, -, -⟩ :=
      exists_walk_of_parentOK hp (items.idxOf v.1 + 1) v hv (Nat.lt_succ_self _)
    obtain ⟨u, hu, hur⟩ := List.mem_map.mp hr
    have hru : r = u := Fin.ext hur.symm
    subst hru
    refine ⟨r, hu, reachable_restrict_of_walk W fun y hy => ?_⟩
    have h0 := hs.free y (hall y hy).1
    show y ∉ Pv
    intro hyP
    simp [labQ, hyP] at h0
  · rintro ⟨u, hu, hreach⟩
    obtain ⟨W, hW⟩ := exists_walk_of_restrict hreach.some (show u ∉ Pv from hAP u hu)
    exact hs.mem_of_walk (List.mem_map_of_mem hu) W fun y hy => by
      simp [labQ, show y ∉ Pv from hW y hy]

/-- The vertex set of side `i` as a finite set: side `1` when `i = 1`, side `2` otherwise. -/
noncomputable def sideFin (G : SimpleGraph (Fin n)) (Pv A : List (Fin n)) (i : ℕ) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v =>
    v ∈ (if i = 1 then sideOne G Pv A else sideTwo G Pv A)

theorem mem_sideFin {G : SimpleGraph (Fin n)} {Pv A : List (Fin n)} {i : ℕ} {v : Fin n} :
    v ∈ sideFin G Pv A i ↔ v ∈ (if i = 1 then sideOne G Pv A else sideTwo G Pv A) := by
  classical
  unfold sideFin
  simp

/-- The restriction of `restrict.lean` to side `i` is the graph of subinstance `i`. -/
theorem restrictGraph_sideFin (G : SimpleGraph (Fin n)) (Pv A : List (Fin n)) (i : ℕ) :
    restrictGraph G (sideFin G Pv A i) = subGraph G Pv A i := by
  ext u v
  rw [restrictGraph_adj, mem_sideFin, mem_sideFin]
  by_cases hi : i = 1
  · subst hi
    simp only [if_true, subGraph, restrict]
    tauto
  · have : subGraph G Pv A i = restrict G (sideTwo G Pv A) := by
      rcases i with _ | _ | i
      · rfl
      · exact absurd rfl hi
      · rfl
    rw [this]
    simp only [if_neg hi, restrict]
    tauto

/-! ### Filling an array with computed values -/

/-- Fill `dst` (of length `hiE`) by `dst[i] := E`, where `E` may read the counter `rI`. -/
def tabProg (rI : Reg) (hiE : Expr) (dst : Arr) (E : Expr) : Cmd :=
  .seq (.alloc dst hiE) (.seq (.assign rI (.const 0)) (forUp rI hiE (.write dst (.reg rI) E)))

/-- **Filling an array.** `tabProg` writes `g i` at every index `i < k` of `dst`, where `g i` is
the value of `E` when the counter is `i`. -/
theorem tabProg_exec {w : ℕ} (rI : Reg) (hiE : Expr) (dst : Arr) (E : Expr) (k : ℕ)
    (g : ℕ → ℕ) (s : State) (hw : 1 < 2 ^ w) (hk : k < 2 ^ w)
    (hhi : ∀ st, Keeps [rI] [dst] s st → hiE.eval w st = some k)
    (hE : ∀ st i, Keeps [rI] [dst] s st → st.regs rI = i → i < k → E.eval w st = some (g i)) :
    ∃ s' t, Exec w (tabProg rI hiE dst E) s s' t ∧
      t ≤ 2 * hiE.cost + 4 + k * (hiE.cost + E.cost + 9) ∧ Keeps [rI] [dst] s s' ∧
      s'.arrs dst = (List.range k).map g := by
  set s₁ := s.setArr dst (List.replicate k 0) with hs₁
  have hex₁ : Exec w (.alloc dst hiE) s s₁ (hiE.cost + k) := .alloc (hhi s (Keeps.refl _ _ s))
  set s₂ := s₁.setReg rI 0 with hs₂
  have hex₂ : Exec w (.assign rI (.const 0)) s₁ s₂ (1 + 1) := .assign (by simp [checkWord])
  let I : ℕ → State → Prop := fun i st => Keeps [rI] [dst] s st ∧ st.regs rI = i ∧
    st.arrs dst = (List.range i).map g ++ List.replicate (k - i) 0
  have hI0 : I 0 s₂ := ⟨((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _, by simp [s₂],
    by simp [s₂, s₁]⟩
  have hloop := forUp_pot I (fun _ => 0) k (E.cost + 2) (r_i := rI) (hi := hiE)
    (body := .write dst (.reg rI) E) hw hk
    (fun i _ st hst => ⟨hst.2.1, hhi st hst.1⟩)
    (fun i hi st hst => by
      obtain ⟨hks, hri, hd⟩ := hst
      refine ⟨st.writeArr dst i (g i), _, .write (reg_eval hri (by omega)) (hE st i hks hri hi)
        (by rw [hd]; simp; omega), ?_, ⟨?_, by simp, ?_⟩, by simp [hri]⟩
      · simp only [Expr.cost]; omega
      · exact (hks.writeArr (by simp) _ _).setReg (by simp) _
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs, ite_true, hd]
        exact set_range_map g hi)
    0 (Nat.zero_le _) s₂ hI0
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, hd₃⟩ := hloop
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, hk₃, by simpa using hd₃⟩
  have : k * (hiE.cost + 6 + (E.cost + 2)) + k ≤ k * (hiE.cost + E.cost + 9) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  rw [Nat.sub_zero] at ht₃
  omega

/-! ### The program -/

/-- The bit set of the side. -/
abbrev aY : Arr := 54

/-- The bit of vertex `rI3` for side `i`: label not `0` for side `1`, label not `1` for side `2`. -/
def bitExpr (i : ℕ) : Expr :=
  if i = 1 then .op .lt (.const 0) (.read aLab (.reg rI3))
  else .op .mod (.op .add (.read aLab (.reg rI3)) (.const 1)) (.const 2)

/-- **Line 10 of Algorithm 5.1, first half.** Build the lists of `H + F`, search from `A` in
`H + F - P'`, and write the bit set of side `i` in `aY`. -/
def sideProg (i : ℕ) : Cmd :=
  .seq unionProg
    (.seq (.alloc aLab (.reg 40))
      (.seq (markProg rI2 (.const 0) (.len aNewPath) aLab aNewPath 2)
        (.seq (mapProg rI3 (.reg rLenA) aSrc aCyc (.op .add (.reg rI3) (.const 1)))
          (.seq (searchProg aUS aUE aUEnt) (tabProg rI3 (.reg 40) aY (bitExpr i))))))

/-- The registers that `sideProg` writes. -/
def sideRegs : List ℕ := List.range' 60 39 ++ uRegs

/-- The arrays that `sideProg` writes. -/
def sideArrs : List ℕ := [aLab, aPar, aQue, aSrc, aY] ++ uArrs

theorem bitExpr_cost (i : ℕ) : (bitExpr i).cost ≤ 9 := by
  unfold bitExpr; split_ifs <;> simp [Expr.cost]

/-- **The bit set of a side.** In at most `60 + 150 n + 50 M + 60 n |F|` steps, `sideProg i`
writes in `aUS`, `aUE`, `aUEnt` the lists of `H + F` and in `aY` the bit set of side `i`. -/
theorem sideProg_exec {w : ℕ} {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    {Pv : List (Fin n)} {a b : Fin n} {A B : List (Fin n)} (i : ℕ) {s : State}
    (hadj : IsAdjList H aStart aEnd aEnt lists s) (hF : IsNewEdgeList H Pv (s.arrs aF))
    (P' : (H ⊔ pairGraph n (s.arrs aF)).Walk a b)
    (hpath : s.arrs aNewPath = P'.support.map Fin.val) (hPn : P'.support.length ≤ n)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val) (hlenA : s.regs rLenA = A.length)
    (hAn : A.length + 2 ≤ n) (hAP : ∀ v ∈ A, v ∉ P'.support)
    (h40 : s.regs 40 = n) (hn : 4 * n + 4 < 2 ^ w)
    (hentw : (s.arrs aEnt).length < 2 ^ w) (hFw : (s.arrs aF).length < 2 ^ w)
    (hcapw : totalAdjEntries lists + n * (s.arrs aF).length < 2 ^ w) :
    ∃ s' t, Exec w (sideProg i) s s' t ∧
      t ≤ 60 + 150 * n + 50 * totalAdjEntries lists + 60 * (n * (s.arrs aF).length) ∧
      Keeps sideRegs sideArrs s s' ∧
      IsAdjList (H ⊔ pairGraph n (s.arrs aF)) aUS aUE aUEnt (unionList lists (s.arrs aF)) s' ∧
      (s'.arrs aUEnt).length = totalAdjEntries lists + n * (s.arrs aF).length ∧
      IsBitSet (sideFin (H ⊔ pairGraph n (s.arrs aF)) P'.support A i) aY s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  -- Step 1: the lists of `H + F`.
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hadj₁, hlen₁⟩ :=
    unionProg_exec hadj hF h40 hn hentw hFw hcapw
  have hk₁' : Keeps sideRegs sideArrs s s₁ := hk₁.mono (by decide) (by decide)
  -- Step 2: all labels free.
  set s₂ := s₁.setArr aLab (List.replicate n 0) with hs₂
  have hex₂ : Exec w (.alloc aLab (.reg 40)) s₁ s₂ (1 + n) :=
    .alloc (reg_eval (by rw [hk₁.1 40 (by decide)]; exact h40) hnw)
  have hpath₂ : s₂.arrs aNewPath = P'.support.map Fin.val := by
    simp only [s₂, State.setArr_arrs_ne _ _ (show aNewPath ≠ aLab by decide)]
    rw [hk₁.2 _ (by decide)]; exact hpath
  -- Step 3: `P'` is forbidden.
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hlab₃⟩ := markProg_exec rI2 (.const 0) (.len aNewPath) aLab
    aNewPath 2 (by decide) P'.support (fun _ => 0) 0 P'.support.length s₂ hw1 hnw
    (by omega) (Nat.zero_le _) le_rfl (by simp [checkWord])
    (fun st hst => by
      show checkWord w (st.arrs aNewPath).length = _
      rw [hst.2 aNewPath (by decide), hpath₂, List.length_map]
      simp only [checkWord, show P'.support.length < 2 ^ w by omega, if_true])
    hpath₂ (by simp [s₂, List.ofFn_const])
  have hlab₃' : s₃.arrs aLab = List.ofFn (labQ P'.support) := by
    rw [hlab₃, List.take_length, List.drop_zero]; rfl
  have hk₃' : Keeps sideRegs sideArrs s s₃ :=
    (hk₁'.setArr (by decide) _).trans hk₃ (by decide) (by decide)
  have hcyc₃ : s₃.arrs aCyc = (a :: A ++ b :: B).map Fin.val := by
    rw [hk₃'.2 aCyc (by decide)]; exact hcyc
  have hlenA₃ : s₃.regs rLenA = A.length := by rw [hk₃'.1 rLenA (by decide)]; exact hlenA
  -- Step 4: the sources `A`.
  have hCw : ∀ v ∈ (a :: A ++ b :: B).map Fin.val, v < 2 ^ w := fun v hv => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv; have := z.2; omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hsrc₄⟩ := mapProg_exec rI3 (.reg rLenA) aSrc aCyc
    (.op .add (.reg rI3) (.const 1)) (by decide) A.length (fun i => i + 1)
    ((a :: A ++ b :: B).map Fin.val) s₃ hw1
    (by omega) (fun st hst => reg_eval (by rw [hst.1 rLenA (by decide)]; exact hlenA₃) (by omega))
    (fun st i hst hri hi => op_eval (a := i) (b := 1) (reg_eval hri (by omega))
      (by simp [checkWord, hw1])
      (by simp [BinOp.eval, BinOp.raw, checkWord]; omega))
    (fun i hi => by simp; omega) hCw hcyc₃
  rw [map_getD_succ] at hsrc₄
  have hk₄' : Keeps sideRegs sideArrs s s₄ := hk₃'.trans hk₄ (by decide) (by decide)
  have hlab₄ : s₄.arrs aLab = List.ofFn (labQ P'.support) := by
    rw [hk₄.2 aLab (by decide)]; exact hlab₃'
  have hadj₄ : IsAdjList (H ⊔ pairGraph n (s.arrs aF)) aUS aUE aUEnt (unionList lists (s.arrs aF)) s₄ :=
    hadj₁.of_arrs_eq (by rw [hk₄.2 _ (by decide), hk₃.2 _ (by decide)]; rfl)
      (by rw [hk₄.2 _ (by decide), hk₃.2 _ (by decide)]; rfl)
      (by rw [hk₄.2 _ (by decide), hk₃.2 _ (by decide)]; rfl)
  have hlen₄ : (s₄.arrs aUEnt).length = totalAdjEntries lists + n * (s.arrs aF).length := by
    rw [hk₄.2 _ (by decide), hk₃.2 _ (by decide)]; exact hlen₁
  have h40₄ : s₄.regs 40 = n := by rw [hk₄'.1 40 (by decide)]; exact h40
  -- Step 5: the search.
  have hlabQ : ∀ v, labQ P'.support v ≤ 3 := fun v => by unfold labQ; split_ifs <;> omega
  have hTU : totalAdjEntries (unionList lists (s.arrs aF)) ≤ totalAdjEntries lists + n * (s.arrs aF).length := by
    have := sum_unionList_le lists (s.arrs aF); rwa [pre_n] at this
  obtain ⟨s₅, t₅, items, hex₅, ht₅, hsi⟩ := searchProg_exec (H ⊔ pairGraph n (s.arrs aF)) (unionList lists (s.arrs aF)) aUS aUE aUEnt
    (by decide) (by decide) (by decide) (labQ P'.support) hlabQ (A.map Fin.val)
    (fun x hx => by obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx; exact z.2)
    s₄ hadj₄ (by rw [hlen₄]; exact hcapw) h40₄ hw4 hnw (by simp; omega) hlab₄ hsrc₄
  have hk₅ : Keeps sideRegs sideArrs s s₅ :=
    ⟨fun r hr => by
      simp only [sideRegs, uRegs, List.mem_append, List.mem_range'_1, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hr
      have hlo : r < 60 ∨ 99 ≤ r := by omega
      rw [hsi.frame.1 r (hlo.imp id fun h => le_trans (by decide) h), hk₄'.1 r (by
        simp only [sideRegs, uRegs, List.mem_append, List.mem_range'_1, List.mem_cons,
          List.not_mem_nil, or_false, not_or]; exact hr)],
     fun x hx => by
      have hx' := hx
      simp only [sideArrs, uArrs, List.cons_append, List.mem_cons, List.nil_append,
        List.not_mem_nil, or_false, not_or] at hx'
      rw [hsi.frame.2 x hx'.1 hx'.2.1 hx'.2.2.1, hk₄'.2 x hx]⟩
  have hadj₅ : IsAdjList (H ⊔ pairGraph n (s.arrs aF)) aUS aUE aUEnt (unionList lists (s.arrs aF)) s₅ :=
    hadj₄.of_arrs_eq (hsi.frame.2 _ (by decide) (by decide) (by decide))
      (hsi.frame.2 _ (by decide) (by decide) (by decide))
      (hsi.frame.2 _ (by decide) (by decide) (by decide))
  have hlen₅ : (s₅.arrs aUEnt).length = totalAdjEntries lists + n * (s.arrs aF).length := by
    rw [hsi.frame.2 _ (by decide) (by decide) (by decide)]; exact hlen₄
  -- Step 6: the bit set.
  set lab : Fin n → ℕ := fun x => if x.1 ∈ items then 1 else labQ P'.support x with hlab
  have hlabv : ∀ x : Fin n, lab x ≤ 2 := fun x => by
    simp only [lab, labQ]; split_ifs <;> omega
  set bit : ℕ → ℕ := fun j => if i = 1 then (if 0 < (List.ofFn lab).getD j 0 then 1 else 0)
    else ((List.ofFn lab).getD j 0 + 1) % 2 with hbit
  obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, hY₆⟩ := tabProg_exec rI3 (.reg 40) aY (bitExpr i) n bit s₅ hw1
    hnw (fun st hst => reg_eval (v := n) (by
      rw [hst.1 40 (by decide), hsi.frame.1 40 (by decide)]; exact h40₄) hnw)
    (fun st j hst hrj hj => by
      have hlabst : st.arrs aLab = List.ofFn lab := by
        rw [hst.2 aLab (by decide), hsi.lab]
      have hr : (Expr.read aLab (.reg rI3)).eval w st = some (lab ⟨j, hj⟩) := by
        have hl := hlabv ⟨j, hj⟩
        simp [Expr.eval, checkWord, hrj, hlabst, hj, show j < 2 ^ w by omega,
          show lab ⟨j, hj⟩ < 2 ^ w by omega]
      have hg : (List.ofFn lab).getD j 0 = lab ⟨j, hj⟩ := by
        simp [List.getD_eq_getElem?_getD, hj]
      have hl2 := hlabv ⟨j, hj⟩
      have h0w : 0 < 2 ^ w := by omega
      have hl1 : lab ⟨j, hj⟩ + 1 < 2 ^ w := by omega
      have hm2 : (lab ⟨j, hj⟩ + 1) % 2 < 2 ^ w := by
        have := Nat.mod_lt (lab ⟨j, hj⟩ + 1) (show 0 < 2 by omega); omega
      unfold bitExpr
      by_cases hi : i = 1
      · simp only [hi, if_true, bit, hg]
        refine op_eval (a := 0) (b := lab ⟨j, hj⟩) (by simp [checkWord, h0w]) hr ?_
        by_cases h0 : 0 < lab ⟨j, hj⟩ <;> simp [BinOp.eval, BinOp.raw, checkWord, h0, hw1, h0w]
      · simp only [hi, if_false, bit, hg]
        exact op_eval (a := lab ⟨j, hj⟩ + 1) (b := 2)
          (op_eval (a := lab ⟨j, hj⟩) (b := 1) hr (by simp [checkWord, hw1])
            (by simp [BinOp.eval, BinOp.raw, checkWord, hl1]))
          (by simp [checkWord]; omega)
          (by simp [BinOp.eval, BinOp.raw, checkWord, hm2]))
  have hk₆' : Keeps sideRegs sideArrs s s₆ := hk₅.trans hk₆ (by decide) (by decide)
  refine ⟨s₆, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_, hk₆',
    hadj₅.of_arrs_eq (hk₆.2 _ (by decide)) (hk₆.2 _ (by decide)) (hk₆.2 _ (by decide)),
    by rw [hk₆.2 _ (by decide)]; exact hlen₅, ?_⟩
  · have hc := bitExpr_cost i
    simp only [Expr.cost, List.length_map] at ht₁ ht₃ ht₄ ht₅ ht₆ ⊢
    have := hTU
    have := Nat.mul_le_mul_right 11 hPn
    have := Nat.mul_le_mul_right 14 (show A.length ≤ n by omega)
    have := Nat.mul_le_mul_left n (show 1 + (bitExpr i).cost + 9 ≤ 19 by omega)
    have : n * (1 + (bitExpr i).cost + 9) ≤ 19 * n := by
      rw [Nat.mul_comm 19]; exact this
    omega
  · -- The bits are those of the side.
    have hAP' : ∀ v ∈ A, v ∉ P'.support := hAP
    have hlen : (s₆.arrs aY).length = n := by rw [hY₆]; simp
    refine ⟨hlen, fun u => ?_, fun u => ?_⟩
    · simp only [hY₆, List.getElem_map, List.getElem_range, bit]
      split_ifs <;> omega
    · have hg : (List.ofFn lab).getD u.1 0 = lab u := by
        simp [List.getD_eq_getElem?_getD, u.2]
      simp only [hY₆, List.getElem_map, List.getElem_range, bit, hg]
      rw [mem_sideFin]
      have hit := mem_items_iff hsi hAP' u
      have hoff : u ∈ reachOff (H ⊔ pairGraph n (s.arrs aF)) P'.support A → u ∉ P'.support :=
        notMem_of_mem_reachOff hAP'
      by_cases hi : i = 1
      · simp only [hi, if_true, sideOne, Set.mem_union, Set.mem_ofPred_eq]
        simp only [lab, labQ]
        by_cases h1 : u.1 ∈ items
        · simp [h1, hit.mp h1]
        · by_cases h2 : u ∈ P'.support
          · simp [h1, h2]
          · simp [h1, h2, (not_congr hit).mp h1]
      · simp only [hi, if_false, sideTwo, Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff]
        simp only [lab, labQ]
        by_cases h1 : u.1 ∈ items
        · simp [h1, hit.mp h1, hoff (hit.mp h1)]
        · by_cases h2 : u ∈ P'.support
          · simp [h1, h2]
          · simp [h1, h2, (not_congr hit).mp h1]

end GraphMinor.Compute.TwoPaths
