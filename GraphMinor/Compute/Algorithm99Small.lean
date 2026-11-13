module

public import GraphMinor.Compute.Specs9
public import GraphMinor.Compute.Case3Block
public import GraphMinor.Compute.Array
import GraphMinor.Compute.Neighborhood

/-!
# Algorithm (9.9) for `p ≤ 1`

The proof of (9.8) in Graph Minors XIII (page 104) begins: "We may assume that $p \ge 2$". This
file does the cases `p = 0` and `p = 1`. For `p = 0` the empty family is a model of `K_0`. For
`p = 1` any one vertex is a model of `K_1`. If there is no vertex, the graph has no edges, and
the empty branch-decomposition (case (i)) is the output. So both cases need only constant time,
or one pass over the indicator list of the deleted set in the form `Alg99Spec`.

The main result is `algorithm_9_9_of_le_one`: for `p ≤ 1`, every `h` and every `ω`, both parts
of `Algorithm99Statement case3Decoder` hold.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-! ### Section 1: Models of `K_0` and `K_1` -/

/-- Every family of zero sets is a model of `K_0`. -/
theorem isCliqueModel_zero {n : ℕ} (G : SimpleGraph (Fin n)) (K : Fin 0 → Finset (Fin n)) :
    IsCliqueModel G 0 K :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- One vertex is a model of `K_1`. -/
theorem isCliqueModel_one_singleton {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    IsCliqueModel G 1 (fun _ => {v}) :=
  ⟨fun _ => ⟨Finset.singleton_nonempty v, connected_induce_singleton G v⟩,
    fun i j hij => absurd (Subsingleton.elim i j) hij,
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩

theorem encBitSetsUpTo_zero {n p : ℕ} (K : Fin p → Finset (Fin n)) :
    encBitSetsUpTo K 0 = [] := rfl

theorem encBitSetsUpTo_one {n : ℕ} (K : Fin 1 → Finset (Fin n)) :
    encBitSetsUpTo K 1 = bitSetList (K 0) := by
  simp [encBitSetsUpTo]

/-- A graph with no vertices has no edges. -/
theorem MultiDigraph.numEdges_eq_zero_of_n_eq_zero {n : ℕ} (G : MultiDigraph n) (hn : n = 0) :
    G.numEdges = 0 := by
  subst hn
  simp [MultiDigraph.numEdges]

/-- Deleting every vertex leaves no edge. -/
theorem MultiDigraph.numEdges_deleteVertices_of_forall_mem {n : ℕ} (G : MultiDigraph n)
    {Z : Finset (Fin n)} (hZ : ∀ u, u ∈ Z) :
    (G.deleteVertices Z).numEdges = 0 := by
  simp [MultiDigraph.numEdges, hZ]

/-- The code `[0, 0]` is the empty branch-decomposition of a graph with no edges. -/
theorem isValidBranchDecompCode_of_numEdges_eq_zero (ω : ℕ) {n : ℕ} (G : MultiDigraph n)
    (hG : G.numEdges = 0) : IsValidBranchDecompCode ω G [0, 0] := by
  refine ⟨?_, ?_, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩ <;>
    simp [bdNumGraphEdges, bdNumTreeVerts, hG]

/-- The written one-vertex tree is a branch-decomposition of a graph with at most one edge. -/
theorem isWrittenDigraphBD_one (ω : ℕ) (D : ComputeDigraph) (hD : D.numEdges ≤ 1) :
    IsWrittenDigraphBD ω D 1 (fun _ => 0) (fun _ => 0) :=
  ⟨by omega, by omega, fun _ h₁ h₂ => by omega, fun _ _ => Nat.zero_lt_one, Or.inl hD⟩

/-! ### Section 2: The standalone programs -/

/-- Algorithm (9.9) for `p = 0`: write `[1]`, the tag of case (ii) followed by the empty model. -/
def alg99ZeroProg : Cmd :=
  .seq (.alloc outArr (.const 1)) (.write outArr (.const 0) (.const 1))

/-- Algorithm (9.9) for `p = 1`: read `n`. If `n = 0`, write `[0, 0, 0]` (case (i) with the empty
branch-decomposition). Otherwise write `1 :: bitSetList {0}` (case (ii)). -/
def alg99OneProg : Cmd :=
  .seq (.assign 2 (.read inArr (.const 0)))
    (.ite (.op .eq (.reg 2) (.const 0))
      (.alloc outArr (.const 3))
      (.seq (.alloc outArr (.op .add (.reg 2) (.const 1)))
        (.seq (.write outArr (.const 0) (.const 1)) (.write outArr (.const 1) (.const 1)))))

theorem one_le_alg99Size (x : Alg99Input) : x.n + 1 ≤ alg99Size x :=
  Nat.le_mul_of_pos_right _ (by omega)

theorem alg99ZeroProg_computes (h ω : ℕ) :
    ComputesArrRelInTime alg99Size encAlg99In (IsAlg99Output case3Decoder 0 h ω) alg99ZeroProg
      (fun m => m) := by
  refine ⟨5, 2, by omega, by omega, fun x s _ => ?_⟩
  have hw := two_mul_lt_two_pow_wordSize (n := alg99Size x) (le_refl 2)
  have hsz := one_le_alg99Size x
  generalize wordSize 2 (alg99Size x) = w at hw ⊢
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have c1 := checkWord_of_lt (w := w) (v := 1) (by omega)
  let s₁ := s.setArr outArr (List.replicate 1 0)
  have hex₁ : Exec w (.alloc outArr (.const 1)) s s₁ 2 :=
    .alloc (by simp only [Expr.eval, c1])
  have hex₂ : Exec w (.write outArr (.const 0) (.const 1)) s₁ (s₁.writeArr outArr 0 1) 3 :=
    .write (by simp only [Expr.eval, c0]) (by simp only [Expr.eval, c1]) (by simp [s₁])
  refine ⟨_, _, .seq hex₁ hex₂, by beta_reduce; omega,
    Or.inr (Or.inl ⟨Fin.elim0, ?_, isCliqueModel_zero _ _⟩)⟩
  simp [s₁, State.writeArr, encBitSetsUpTo_zero]

theorem alg99OneProg_computes (h ω : ℕ) :
    ComputesArrRelInTime alg99Size encAlg99In (IsAlg99Output case3Decoder 1 h ω) alg99OneProg
      (fun m => m) := by
  refine ⟨20, 2, by omega, by omega, fun x s hs => ?_⟩
  have hw := two_mul_lt_two_pow_wordSize (n := alg99Size x) (le_refl 2)
  have hsz := one_le_alg99Size x
  generalize wordSize 2 (alg99Size x) = w at hw ⊢
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have c1 := checkWord_of_lt (w := w) (v := 1) (by omega)
  have c3 := checkWord_of_lt (w := w) (v := 3) (by omega)
  have hin : s.arrs inArr = x.G.enc := hs
  have h0 : (s.arrs inArr)[0]? = some x.n := by simp [hin, MultiDigraph.enc]
  have hlen : 0 < (s.arrs inArr).length := by simp [hin]
  have h0' : (s.arrs inArr)[0]'hlen = x.n := by
    rw [List.getElem?_eq_getElem hlen] at h0; exact Option.some.inj h0
  have cn := checkWord_of_lt (w := w) (v := x.n) (by omega)
  let s₁ := s.setReg 2 x.n
  have hr2 : s₁.regs 2 = x.n := by simp [s₁]
  have hex₁ : Exec w (.assign 2 (.read inArr (.const 0))) s s₁ 3 :=
    .assign (by simp only [Expr.eval, c0, hlen, ↓reduceDIte, h0', cn])
  by_cases hn : x.n = 0
  · let s₂ := s₁.setArr outArr (List.replicate 3 0)
    have hex₂ : Exec w (.alloc outArr (.const 3)) s₁ s₂ 4 :=
      .alloc (by simp only [Expr.eval, c3])
    have hc : (Expr.op .eq (.reg 2) (.const 0)).eval w s₁ = some 1 := by
      simp only [Expr.eval, hr2, hn, c0, BinOp.eval, BinOp.raw, ↓reduceIte, c1]
    have hex : Exec w alg99OneProg s s₂ (3 + (3 + 4)) := .seq hex₁ (.ite_true hc one_ne_zero hex₂)
    refine ⟨_, _, hex, by beta_reduce; omega, Or.inl ⟨[0, 0], by simp [s₂], ?_⟩⟩
    exact isValidBranchDecompCode_of_numEdges_eq_zero ω x.G
      (x.G.numEdges_eq_zero_of_n_eq_zero hn)
  · have hn1 : 0 < x.n := Nat.pos_of_ne_zero hn
    have cn1 := checkWord_of_lt (w := w) (v := x.n + 1) (by omega)
    let s₂ := s₁.setArr outArr (List.replicate (x.n + 1) 0)
    have hex₂ : Exec w (.alloc outArr (.op .add (.reg 2) (.const 1))) s₁ s₂ (3 + (x.n + 1)) :=
      .alloc (by simp only [Expr.eval, hr2, cn, c1, BinOp.eval, BinOp.raw, cn1])
    let s₃ := s₂.writeArr outArr 0 1
    have hex₃ : Exec w (.write outArr (.const 0) (.const 1)) s₂ s₃ 3 :=
      .write (by simp only [Expr.eval, c0]) (by simp only [Expr.eval, c1]) (by simp [s₂])
    let s₄ := s₃.writeArr outArr 1 1
    have hex₄ : Exec w (.write outArr (.const 1) (.const 1)) s₃ s₄ 3 :=
      .write (by simp only [Expr.eval, c1]) (by simp only [Expr.eval, c1]) (by simp [s₃, s₂]; omega)
    have hex : Exec w alg99OneProg s s₄ (3 + (3 + (3 + (x.n + 1) + (3 + 3)))) :=
      .seq hex₁ (.ite_false (by simp only [Expr.eval, hr2, cn, c0, BinOp.eval, BinOp.raw, hn,
        ↓reduceIte]) (.seq hex₂ (.seq hex₃ hex₄)))
    refine ⟨_, _, hex, by beta_reduce; omega, Or.inr (Or.inl ⟨fun _ => {⟨0, hn1⟩}, ?_,
      isCliqueModel_one_singleton _ _⟩)⟩
    rw [encBitSetsUpTo_one]
    refine List.ext_getElem (by simp [s₄, s₃, s₂, State.writeArr]) fun j h₁ h₂ => ?_
    simp only [s₄, s₃, s₂, State.writeArr, State.setArr_arrs_self]
    rcases j with _ | _ | j
    · simp
    · simp [bitSetList]
    · simp [bitSetList]

/-! ### Section 3: The programs in the form `Alg99Spec` -/

/-- The form `Alg99Spec` for `p = 0`: tag `1` in register `51` and the empty model in array
`b + 2`. -/
def alg99ZeroSpecProg (b : ℕ) : Cmd :=
  .seq (.assign 51 (.const 1)) (.alloc (b + 2) (.const 0))

/-- The form `Alg99Spec` for `p = 1`: search `bitSetList Z` (array `b + 1`) for a vertex `v`
outside `Z`. If there is one, write tag `1` and `bitSetList {v}`. If not, every vertex is in `Z`,
`G \ Z` has no edge, and the program writes tag `0` and the one-vertex tree. -/
def alg99OneSpecProg (b : ℕ) : Cmd :=
  .seq (linearSearch (b + 1) (.const 0) 53 54)
    (.ite (.op .lt (.reg 53) (.len (b + 1)))
      (.seq (.assign 51 (.const 1))
        (.seq (.alloc (b + 2) (.len (b + 1))) (.write (b + 2) (.reg 53) (.const 1))))
      (.seq (.assign 51 (.const 0))
        (.seq (.assign 52 (.const 1)) (.seq (.alloc (b + 2) (.const 1)) (.alloc (b + 3) (.const 0))))))

/-- The bounds on words that the programs of this section need. -/
private theorem alg99Small_word {w N : ℕ} (hw : wordSize 2 N ≤ w) : 2 * (N + 2) < 2 ^ w :=
  lt_of_lt_of_le (two_mul_lt_two_pow_wordSize (n := N) (le_refl 2))
    (Nat.pow_le_pow_right (by omega) hw)

theorem alg99ZeroSpec (h ω : ℕ) : Alg99Spec case3Decoder 0 h ω := by
  refine ⟨alg99ZeroSpecProg (alg105ArrBase 0), 4, 2, by omega, by omega, ?_⟩
  intro w n_i G_i Z_i s D_del N hw _ _
  have hNw := alg99Small_word hw
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have c1 := checkWord_of_lt (w := w) (v := 1) (by omega)
  let s₁ := s.setReg 51 1
  have hex₁ : Exec w (.assign 51 (.const 1)) s s₁ 2 := .assign (by simp only [Expr.eval, c1])
  let s₂ := s₁.setArr (alg105ArrBase 0 + 2) (List.replicate 0 0)
  have hex₂ : Exec w (.alloc (alg105ArrBase 0 + 2) (.const 0)) s₁ s₂ 1 :=
    .alloc (by simp only [Expr.eval, c0])
  refine ⟨s₂, _, .seq hex₁ hex₂, ?_, fun r hr => ?_, fun a ha => ?_, Or.inr (Or.inl ⟨?_,
    Fin.elim0, ?_, fun j => j.elim0, isCliqueModel_zero _ _⟩)⟩
  · have : 1 ≤ (n_i + 1) * N := Nat.mul_pos (by omega) (by omega)
    rw [Nat.mul_assoc]; omega
  · exact State.setReg_regs_ne _ _ (by romega)
  · exact State.setArr_arrs_ne _ _ (by simp only [alg105ArrBase] at ha ⊢; romega)
  · rfl
  · simp [s₂, encBitSetsUpTo_zero]

theorem alg99OneSpec (h ω : ℕ) : Alg99Spec case3Decoder 1 h ω := by
  refine ⟨alg99OneSpecProg (alg105ArrBase 1), 60, 2, by omega, by omega, ?_⟩
  intro w n_i G_i Z_i s D_del N hw _ hZ
  have hNw := alg99Small_word hw
  have hN : n_i + 1 ≤ N := by simp only [N]; omega
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have c1 := checkWord_of_lt (w := w) (v := 1) (by omega)
  have cn := checkWord_of_lt (w := w) (v := n_i) (by omega)
  have hb : alg105ArrBase 1 = 31 := rfl
  rw [hb] at hZ ⊢
  have hframe : ∀ s' t, Exec w (alg99OneSpecProg 31) s s' t →
      (∀ r < 50, s'.regs r = s.regs r) ∧ (∀ a < 31, s'.arrs a = s.arrs a) := by
    intro s' t hex
    refine ⟨fun r hr => hex.regs_eq_of_not_mem_writtenRegs ?_,
      fun a ha => hex.arrs_eq_of_not_mem_writtenArrs ?_⟩
    · simp only [alg99OneSpecProg, linearSearch, forUp, Cmd.writtenRegs, Finset.mem_union,
        Finset.mem_singleton, Finset.notMem_empty, or_false]
      romega
    · simp only [alg99OneSpecProg, linearSearch, forUp, Cmd.writtenArrs, Finset.mem_union,
        Finset.mem_singleton, Finset.notMem_empty, false_or, or_self]
      romega
  have hwords : ∀ x ∈ bitSetList Z_i, x < 2 ^ w := by
    intro x hx
    simp only [bitSetList, List.mem_ofFn] at hx
    obtain ⟨u, rfl⟩ := hx
    split_ifs <;> omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hA₁, hres⟩ :=
    Triple.linearSearch_const (31 + 1) 0 53 54 (bitSetList Z_i) (by decide) (by omega)
      (by simp only [length_bitSetList]; omega) (by omega) hwords s hZ
  simp only [length_bitSetList] at ht₁ hres
  have hlen₁ : (s₁.arrs (31 + 1)).length = n_i := by rw [hA₁, length_bitSetList]
  rcases hres with ⟨hr53, hall⟩ | ⟨hv, hv0, _⟩
  · -- No vertex outside `Z`: case (i) with the one-vertex tree.
    have hallZ : ∀ u : Fin n_i, u ∈ Z_i := by
      intro u
      have := hall u.1 u.2
      rw [getElem_bitSetList _ _ u.2] at this
      by_contra hu
      exact this (by simp [hu])
    have hm : D_del.numEdges = 0 := G_i.numEdges_deleteVertices_of_forall_mem hallZ
    have hc : (Expr.op .lt (.reg 53) (.len (31 + 1))).eval w s₁ = some 0 := by
      simp only [Expr.eval, hr53, hlen₁, cn, BinOp.eval, BinOp.raw, lt_irrefl, ↓reduceIte, c0]
    let s₂ := s₁.setReg 51 0
    have hex₂ : Exec w (.assign 51 (.const 0)) s₁ s₂ 2 := .assign (by simp only [Expr.eval, c0])
    let s₃ := s₂.setReg 52 1
    have hex₃ : Exec w (.assign 52 (.const 1)) s₂ s₃ 2 := .assign (by simp only [Expr.eval, c1])
    let s₄ := s₃.setArr (31 + 2) (List.replicate 1 0)
    have hex₄ : Exec w (.alloc (31 + 2) (.const 1)) s₃ s₄ 2 := .alloc (by simp only [Expr.eval, c1])
    let s₅ := s₄.setArr (31 + 3) (List.replicate 0 0)
    have hex₅ : Exec w (.alloc (31 + 3) (.const 0)) s₄ s₅ 1 := .alloc (by simp only [Expr.eval, c0])
    have hex : Exec w (alg99OneSpecProg 31) s s₅ (t₁ + (3 + (2 + (2 + (2 + 1))))) :=
      .seq hex₁ (.ite_false hc (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))))
    obtain ⟨hreg, harr⟩ := hframe _ _ hex
    refine ⟨s₅, _, hex, ?_, hreg, harr, Or.inl ⟨by simp [s₅, s₄, s₃, s₂], 1, fun _ => 0,
      fun _ => 0, by simp [s₅, s₄, s₃], by simp [s₅, s₄], fun z hz => ?_, ?_, fun e he => ?_,
      isWrittenDigraphBD_one ω _ ?_⟩⟩
    · have : n_i + 1 ≤ (n_i + 1) * N := Nat.le_mul_of_pos_right _ (by omega)
      rw [Nat.mul_assoc]; omega
    · simp [s₅, s₄]
    · simp [s₅, hm]
    · omega
    · show D_del.directedEdgesList.length ≤ 1
      rw [MultiDigraph.length_directedEdgesList, hm]; omega
  · -- A vertex `v` outside `Z`: case (ii) with the model `{v}`.
    set v := s₁.regs 53 with hv_def
    have hvZ : (⟨v, hv⟩ : Fin n_i) ∉ Z_i := by
      intro hmem
      rw [getElem_bitSetList _ _ hv] at hv0
      simp [hmem] at hv0
    have cv := checkWord_of_lt (w := w) (v := v) (by omega)
    have hc : (Expr.op .lt (.reg 53) (.len (31 + 1))).eval w s₁ = some 1 := by
      simp only [Expr.eval, ← hv_def, cv, hlen₁, cn, BinOp.eval, BinOp.raw, hv, ↓reduceIte, c1]
    let s₂ := s₁.setReg 51 1
    have hex₂ : Exec w (.assign 51 (.const 1)) s₁ s₂ 2 := .assign (by simp only [Expr.eval, c1])
    let s₃ := s₂.setArr (31 + 2) (List.replicate n_i 0)
    have hex₃ : Exec w (.alloc (31 + 2) (.len (31 + 1))) s₂ s₃ (1 + n_i) :=
      .alloc (by simp only [Expr.eval, s₂, State.setReg_arrs, hlen₁, cn])
    let s₄ := s₃.writeArr (31 + 2) v 1
    have hex₄ : Exec w (.write (31 + 2) (.reg 53) (.const 1)) s₃ s₄ 3 :=
      .write (by simp only [Expr.eval, s₃, s₂, State.setArr_regs, State.setReg_regs,
          show (53 : ℕ) ≠ 51 by omega, ↓reduceIte, ← hv_def, cv])
        (by simp only [Expr.eval, c1]) (by simp [s₃, hv])
    have hex : Exec w (alg99OneSpecProg 31) s s₄ (t₁ + (3 + (2 + ((1 + n_i) + 3)))) :=
      .seq hex₁ (.ite_true hc one_ne_zero (.seq hex₂ (.seq hex₃ hex₄)))
    obtain ⟨hreg, harr⟩ := hframe _ _ hex
    refine ⟨s₄, _, hex, ?_, hreg, harr, Or.inr (Or.inl ⟨by simp [s₄, s₃, s₂],
      fun _ => {⟨v, hv⟩}, ?_, fun _ => Finset.disjoint_singleton_left.mpr hvZ,
      isCliqueModel_one_singleton _ _⟩)⟩
    · have : n_i + 1 ≤ (n_i + 1) * N := Nat.le_mul_of_pos_right _ (by omega)
      rw [Nat.mul_assoc]; omega
    · rw [encBitSetsUpTo_one]
      refine List.ext_getElem (by simp [s₄, s₃]) fun j h₁ h₂ => ?_
      simp only [s₄, s₃, State.writeArr, State.setArr_arrs_self, List.getElem_set,
        List.getElem_replicate]
      simp only [length_bitSetList] at h₂
      rw [getElem_bitSetList _ j h₂]
      by_cases hj : v = j
      · subst hj; simp
      · simp [hj, Fin.ext_iff, Ne.symm hj]

/-! ### Section 4: The cases `p ≤ 1` of (9.9) -/

/-- **Graph Minors XIII, (9.8) and Algorithm (9.9), for `p ≤ 1`** (page 104: "We may assume that
$p \ge 2$"). For `p ≤ 1`, every height `h` and every width `ω`, there is a program for (9.9) in
time `O(vε)`, and one in the form `Alg99Spec`. -/
theorem algorithm_9_9_of_le_one {p : ℕ} (hp : p ≤ 1) (h ω : ℕ) :
    (∃ P : Cmd,
      ComputesArrRelInTime alg99Size encAlg99In (IsAlg99Output case3Decoder p h ω) P
        (fun m => m)) ∧
    Alg99Spec case3Decoder p h ω := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
  · exact ⟨⟨_, alg99ZeroProg_computes h ω⟩, alg99ZeroSpec h ω⟩
  · exact ⟨⟨_, alg99OneProg_computes h ω⟩, alg99OneSpec h ω⟩

end GraphMinor.Compute
