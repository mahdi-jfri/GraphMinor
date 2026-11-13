module

public import GraphMinor.Compute.MultiDigraph
public import GraphMinor.Compute.Algorithm94Aux
public import GraphMinor.Compute.Algorithm94Wall
public import GraphMinor.Compute.Algorithm94Unpack
public import GraphMinor.Compute.Algorithm94Scan

/-!
# Graph Minors XIII, Algorithm (9.4): Base Cases and Initialization

This file provides the encoding helpers, base cases (`p = 0` and `p = 1`), and initialization
routine (`alg94InitProg`) for **Algorithm (9.4)** on the shared `MultiDigraph` and `WallOfHeight`
formats.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Encoding & Slice Helpers -/

/-- Wrapper around `readSliceProg_exec` that also records register preservation for
`r_base + 2 < r`. -/
theorem readSliceProg_exec_full {w n off : ℕ} (a_src a_dst : ℕ) (e_off : Expr)
    (r_len r_base : ℕ) (hne_arr : a_src ≠ a_dst) (hr_len : r_len < r_base)
    (pre mid suf : List ℕ) (hpre : pre.length = off) (hmid : mid.length = n)
    (hmid_w : ∀ x ∈ mid, x < 2 ^ w) (hw : 1 < 2 ^ w) (hoff_n_w : off + n < 2 ^ w)
    {s : State}
    (he_off : e_off.eval w s = some off)
    (hsrc : s.arrs a_src = pre ++ mid ++ suf)
    (hrlen_val : s.regs r_len = n) :
    ∃ s' t,
      Exec w (readSliceProg a_src e_off a_dst (.reg r_len) r_base) s s' t ∧
      t ≤ 16 * n + 8 + e_off.cost ∧
      s'.arrs a_dst = mid ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < r_base ∨ r_base + 2 < r → s'.regs r = s.regs r) := by
  rcases readSliceProg_exec a_src a_dst e_off r_len r_base hne_arr hr_len
      pre mid suf hpre hmid hmid_w hw hoff_n_w he_off hsrc hrlen_val with
    ⟨s', t, hex, ht, hdst, harr, hreg⟩
  refine ⟨s', t, hex, ht, hdst, harr, fun r hr => ?_⟩
  rcases hr with hlt | hgt
  · exact hreg r hlt
  · have hnot : (r : Reg) ∉ (readSliceProg a_src e_off a_dst (.reg r_len) r_base).writtenRegs := by
      simp [readSliceProg, readSliceBody, forUp, Cmd.writtenRegs]; omega
    exact Exec.regs_eq_of_not_mem_writtenRegs hex hnot

theorem all_lt_enc_multiDigraph {n w : ℕ} (G : MultiDigraph n)
    (hn_w : n < 2 ^ w) (hm_w : G.numActivePairs < 2 ^ w) (he_w : G.numEdges < 2 ^ w) :
    ∀ x ∈ G.enc, x < 2 ^ w := by
  intro x hx
  unfold MultiDigraph.enc at hx
  simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
  rcases hx with rfl | rfl | hx_tr
  · exact hn_w
  · exact hm_w
  · have hall_tr : ∀ (ps : List (Fin n × Fin n)) (y : ℕ),
        y ∈ G.flatTriples ps → y < 2 ^ w := by
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
        · have := G.edgeMult_le_numEdges u v; omega
        · exact ih y hy
    exact hall_tr G.activePairsList x hx_tr

theorem all_lt_bitSetList {n w : ℕ} (S : Finset (Fin n)) (hw1 : 1 < 2 ^ w) :
    ∀ x ∈ bitSetList S, x < 2 ^ w := by
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
  rw [length_bitSetList] at hi
  rw [getElem_bitSetList S i hi]
  split_ifs <;> omega

theorem mul_lt_two_pow_wordSize_of_succ_le {A c n : ℕ} (hc : A + 1 ≤ c) :
    A * (n + 2) < 2 ^ wordSize c n := by
  have h1 : A ≤ 2 ^ A := Nat.le_of_lt (Nat.lt_two_pow_self (n := A))
  have h2 : 2 ^ A ≤ (n + 2) ^ A := Nat.pow_le_pow_left (by omega) A
  have h3 : A * (n + 2) ≤ (n + 2) ^ (A + 1) := by
    calc A * (n + 2)
        ≤ (n + 2) ^ A * (n + 2) := Nat.mul_le_mul_right (n + 2) (h1.trans h2)
      _ = (n + 2) ^ (A + 1) := (Nat.pow_succ (n + 2) A).symm
  have h4 : (n + 2) ^ (A + 1) ≤ (n + 2) ^ c := Nat.pow_le_pow_right (by omega) hc
  exact Nat.lt_of_le_of_lt (h3.trans h4) (pow_lt_two_pow_wordSize (by omega) n)

theorem IsBitSet.of_arr_eq' {n : ℕ} {S : Finset (Fin n)} {a b : Arr} {s s' : State}
    (hS : IsBitSet S a s) (heq : s'.arrs b = s.arrs a) :
    IsBitSet S b s' := by
  rcases hS with ⟨hlen, hle, hmem⟩
  exact ⟨by rw [heq, hlen],
    fun u => by simp only [heq]; exact hle u,
    fun u => by simp only [heq]; exact hmem u⟩

theorem IsBitSet.all_lt {n w : ℕ} {S : Finset (Fin n)} {a : Arr} {s : State}
    (hS : IsBitSet S a s) (hw1 : 1 < 2 ^ w) :
    ∀ x ∈ s.arrs a, x < 2 ^ w := by
  rcases hS with ⟨_, hle, _⟩
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
  have hle_i := hle ⟨i, by omega⟩
  dsimp at hle_i
  omega

theorem ne_reg_of_ne {a b : ℕ} (h : a ≠ b) : (a : Reg) ≠ (b : Reg) := h

theorem all_lt_encBitSetsUpTo {n p w : ℕ} (K : Fin p → Finset (Fin n)) (hw1 : 1 < 2 ^ w) :
    ∀ k ≤ p, ∀ x ∈ encBitSetsUpTo K k, x < 2 ^ w
  | 0, _, x, hx => by simp [encBitSetsUpTo] at hx
  | k + 1, hk, x, hx => by
    have hk_lt : k < p := by omega
    simp only [encBitSetsUpTo, hk_lt, ↓reduceDIte, List.mem_append] at hx
    rcases hx with hx | hx
    · exact all_lt_encBitSetsUpTo K hw1 k (by omega) x hx
    · exact all_lt_bitSetList (K ⟨k, hk_lt⟩) hw1 x hx

theorem encUnderlyingGraphModel_split {n p : ℕ} {G : MultiDigraph n}
    (M : UnderlyingGraphModel (completeComputeDigraph p) G.toComputeDigraph) :
    ∃ pre : List ℕ,
      encUnderlyingGraphModel M =
        pre ++ encBitSetsUpTo (fun u => (M.vertMap u).verts) p ++ [] ∧
      pre.length = 2 + 2 * (completeGraphEdges p).length := by
  let pre := [(completeComputeDigraph p).numVerts, (completeComputeDigraph p).numEdges] ++
    (List.finRange (completeComputeDigraph p).numEdges).flatMap (fun e =>
      [(G.toComputeDigraph.tail (M.edgeMap e)).1, (G.toComputeDigraph.head (M.edgeMap e)).1])
  have hpre_len : pre.length = 2 + 2 * (completeGraphEdges p).length := by
    change ([_, _] ++ (List.finRange (completeComputeDigraph p).numEdges).flatMap _).length = _
    rw [List.length_append, List.length_flatMap]
    have hmap :
        List.map
          (fun e : Fin (completeComputeDigraph p).numEdges =>
            ([(G.toComputeDigraph.tail (M.edgeMap e)).1,
              (G.toComputeDigraph.head (M.edgeMap e)).1]).length)
          (List.finRange (completeComputeDigraph p).numEdges) =
        List.replicate (List.finRange (completeComputeDigraph p).numEdges).length 2 := by
      rw [List.map_eq_replicate_iff]
      intro _ _; rfl
    rw [hmap, List.length_finRange, List.sum_replicate, smul_eq_mul]
    change 2 + (completeGraphEdges p).length * 2 = 2 + 2 * (completeGraphEdges p).length
    omega
  refine ⟨pre, ?_, hpre_len⟩
  rw [List.append_nil]
  unfold encUnderlyingGraphModel
  rw [flatMap_finRange_bitSetList_eq_encBitSetsUpTo (fun u => (M.vertMap u).verts)]
  rfl

theorem edgeFinset_card_toSimpleGraph_le_numEdges {n : ℕ} (G : MultiDigraph n) :
    G.toSimpleGraph.edgeFinset.card ≤ G.numEdges := by
  have h1 : G.toSimpleGraph.edgeFinset.card = (edgeListOf G.toSimpleGraph).length :=
    (length_edgeListOf_eq_card_edgeFinset G.toSimpleGraph).symm
  have h2 : (edgeListOf G.toSimpleGraph).length ≤ G.numActivePairs := by
    rw [← G.toSimplePairsAux_activePairsList]
    exact length_toSimplePairsAux_le n n G.activePairsList
  have h3 := Alg91.numActivePairs_le_numEdges G
  omega

theorem parseWallCost_le_mul (h n sz : ℕ) (hsz1 : 1 ≤ sz) (hn : n ≤ sz) :
    parseWallCost h n ≤ (17 + 214 * elemWallNumVerts h) * sz := by
  unfold parseWallCost
  have h1 : (15 + 116 * elemWallNumVerts h) * 1 ≤ (15 + 116 * elemWallNumVerts h) * sz :=
    Nat.mul_le_mul_left _ hsz1
  have h2 : (2 + 98 * elemWallNumVerts h) * n ≤ (2 + 98 * elemWallNumVerts h) * sz :=
    Nat.mul_le_mul_left _ hn
  have h3 : 15 + 2 * n + 6 * elemWallNumVerts h + 2 * elemWallNumVerts h * (55 + 49 * n) =
      (15 + 116 * elemWallNumVerts h) * 1 + (2 + 98 * elemWallNumVerts h) * n := by ring
  have h4 : (15 + 116 * elemWallNumVerts h) * sz + (2 + 98 * elemWallNumVerts h) * sz =
      (17 + 214 * elemWallNumVerts h) * sz := by ring
  omega

theorem maxWallEncLen_le_mul (h n sz : ℕ) (hsz1 : 1 ≤ sz) (hn : n ≤ sz) :
    maxWallEncLen h n ≤ (4 + 3 * elemWallNumVerts h) * sz := by
  unfold maxWallEncLen
  have h1 : (3 + 3 * elemWallNumVerts h) * 1 ≤ (3 + 3 * elemWallNumVerts h) * sz :=
    Nat.mul_le_mul_left _ hsz1
  have h2 : (3 + 3 * elemWallNumVerts h) * sz + sz = (4 + 3 * elemWallNumVerts h) * sz := by ring
  omega

theorem length_encAlg94In_le {p t h k r : ℕ} (x : Alg94Input p t h k r) :
    (encAlg94In x).length ≤ (2 + 3 * x.G.numActivePairs) + (t + 1) * maxWallEncLen h x.n := by
  have hG : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hW : x.W.encList.length ≤ maxWallEncLen h x.n := by
    have h1 := Alg91.length_encList_le_of_isValid x.hW_valid.2.2
    have h2 := length_elemWallEdges_le h
    unfold maxWallEncLen; omega
  have hsub : ∀ xs : List (Fin t),
      (xs.flatMap (fun j => (x.W_sub j).encList)).length ≤ xs.length * maxWallEncLen h x.n := by
    intro xs
    induction xs with
    | nil => simp
    | cons j xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hj : (x.W_sub j).encList.length ≤ maxWallEncLen h x.n :=
        length_encList_le_maxWallEncLen x.hW_valid.2.2 (x.hsub j)
      rw [Nat.add_one_mul]; omega
  have hsub_tot := hsub (List.finRange t)
  rw [List.length_finRange] at hsub_tot
  unfold encAlg94In
  rw [List.length_append, List.length_append, Nat.add_mul, Nat.one_mul]
  omega

/-- Constant factor for `alg94ScanStepCost`. -/
def alg94ScanFactor (h k : ℕ) : ℕ :=
  357 + 4 * h + 214 * elemWallNumVerts h + 34 * (k + 1) * (4 + 3 * elemWallNumVerts h)

theorem alg94ScanStepCost_le_mul (h n m_edges k sz : ℕ)
    (hsz1 : 1 ≤ sz) (hn : n ≤ sz) (hm : m_edges ≤ sz) :
    alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges) ≤ alg94ScanFactor h k * sz := by
  unfold alg94ScanStepCost alg94ScanFactor
  have h1 : (120 + 4 * h) * 1 ≤ (120 + 4 * h) * sz := Nat.mul_le_mul_left _ hsz1
  have h2 := parseWallCost_le_mul h n sz hsz1 hn
  have h3 : 116 * n ≤ 116 * sz := Nat.mul_le_mul_left 116 hn
  have h4 : 104 * m_edges ≤ 104 * sz := Nat.mul_le_mul_left 104 hm
  have h5 : 34 * (k + 1) * maxWallEncLen h n ≤
      34 * (k + 1) * (4 + 3 * elemWallNumVerts h) * sz := by
    have hmax := maxWallEncLen_le_mul h n sz hsz1 hn
    have hmul := Nat.mul_le_mul_left (34 * (k + 1)) hmax
    calc 34 * (k + 1) * maxWallEncLen h n
        ≤ (34 * (k + 1)) * ((4 + 3 * elemWallNumVerts h) * sz) := hmul
      _ = 34 * (k + 1) * (4 + 3 * elemWallNumVerts h) * sz := by ring
  simp only [Nat.add_mul, Nat.mul_one] at h1 h2 ⊢
  omega

/-! ### Section 2: Base Cases `p = 0` and `p = 1` -/

/-- Word RAM program for Algorithm (9.4) when `p = 0`: allocates `[0]` in `outArr`. -/
def alg94ProgZero : Cmd :=
  .alloc outArr (.const 1)

theorem alg94_zero (t h : ℕ) :
    ComputesArrRelInTime (alg94Size (p := 0) (t := t) (h := h) (k := 0) (r := 0))
      (encAlg94In (p := 0) (t := t) (h := h) (k := 0) (r := 0))
      (IsAlg94Output 0 t 0) alg94ProgZero (fun s => s) := by
  refine ⟨2, 1, by omega, by omega, fun x s₀ _ => ?_⟩
  have h2 : (alg94Size x + 2) ^ 1 < 2 ^ wordSize 1 (alg94Size x) :=
    pow_lt_two_pow_wordSize (by omega) (alg94Size x)
  rw [Nat.pow_one] at h2
  have hw1 : 1 < 2 ^ wordSize 1 (alg94Size x) := by omega
  have hex : Exec (wordSize 1 (alg94Size x)) alg94ProgZero s₀
      (s₀.setArr outArr (List.replicate 1 0)) (1 + 1) :=
    .alloc (by simp only [Expr.eval, checkWord, hw1, ↓reduceIte])
  have hsz : 1 ≤ alg94Size x := by unfold alg94Size; omega
  refine ⟨s₀.setArr outArr [0], 2, hex, by dsimp; omega, Or.inl ⟨Fin.elim0, ?_, ?_⟩⟩
  · simp [encBitSetsUpTo]
  · refine ⟨fun u => u.elim0, fun u => u.elim0, fun u => u.elim0⟩

/-- Word RAM program for Algorithm (9.4) when `p = 1`: reads `n = inArr[0]` into `reg 1`,
allocates `arr 10` of length `n`, writes `1` at index `0` (`bitSetList {⟨0, hn_pos⟩}`),
and prepends tag `0` into `outArr`. -/
def alg94ProgOne : Cmd :=
  .seq (.assign 1 (.read inArr (.const 0)))
    (.seq (.alloc 10 (.reg 1))
      (.seq (.write 10 (.const 0) (.const 1))
        (prependWordProg (.const 0) 10 outArr 1 20)))

theorem alg94_one (t h : ℕ) :
    ComputesArrRelInTime (alg94Size (p := 1) (t := t) (h := h) (k := 0) (r := 0))
      (encAlg94In (p := 1) (t := t) (h := h) (k := 0) (r := 0))
      (IsAlg94Output 1 t 0) alg94ProgOne (fun s => s) := by
  refine ⟨30, 4, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let w := wordSize 4 (alg94Size x)
  have hmul_w : 2 * (alg94Size x + 2) < 2 ^ w :=
    mul_lt_two_pow_wordSize_of_succ_le (A := 2) (c := 4) (n := alg94Size x) (by omega)
  have hsz_def : alg94Size x = x.G.numEdges + x.n + 1 := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hn1_w : 1 + x.n < 2 ^ w := by omega
  have hn_pos : 0 < x.n := (x.W.branchVert (elemWallMiddle₁Idx x.hW_valid.1)).pos
  have hin_len : 0 < (s₀.arrs inArr).length := by
    rw [hs₀]; unfold encAlg94In MultiDigraph.enc; simp
  have hin_get0 : (s₀.arrs inArr)[0]'hin_len = x.n := by
    simp [hs₀, encAlg94In, MultiDigraph.enc]
  -- 1. reg 1 := inArr[0]
  let s₁ := s₀.setReg 1 x.n
  have hex₁ : Exec w (.assign 1 (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hin_len, hin_get0, hn_w])
  -- 2. alloc 10 (reg 1)
  let s₂ := s₁.setArr 10 (List.replicate x.n 0)
  have hex₂ : Exec w (.alloc 10 (.reg 1)) s₁ s₂ (1 + x.n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hn_w])
  -- 3. write 10 0 1
  let v₀ : Fin x.n := ⟨0, hn_pos⟩
  let s₃ := s₂.writeArr 10 0 1
  have hex₃ : Exec w (.write 10 (.const 0) (.const 1)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hw1])
      (by simp [s₂, hn_pos])
  have harr10_3 : s₃.arrs 10 = bitSetList ({v₀} : Finset (Fin x.n)) := by
    simp only [s₃, s₂, State.writeArr_arrs_self, State.setArr_arrs_self]
    rw [← Alg91.bitSetList_empty x.n]
    simpa [v₀] using Alg91.bitSetList_set_one (∅ : Finset (Fin x.n)) v₀
  -- 4. prependWordProg (.const 0) 10 outArr 1 20
  rcases prependWordProg_exec (tag := 0) (.const 0) 10 outArr 1 20
      (by decide) (by decide)
      (bitSetList ({v₀} : Finset (Fin x.n)))
      (all_lt_bitSetList {v₀} hw1) hw1
      (by rw [length_bitSetList]; exact hn1_w)
      (fun _ => by simp [Expr.eval, checkWord, h0_w])
      harr10_3 (by simp [s₃, s₂, s₁, length_bitSetList]) with
    ⟨s₄, t₄, hex₄, ht₄, hout₄, _, _⟩
  dsimp [Expr.cost] at ht₄
  rw [length_bitSetList] at ht₄
  refine ⟨s₄, 3 + ((1 + x.n) + (3 + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by dsimp; unfold alg94Size; omega,
    Or.inl ⟨fun _ : Fin 1 => {v₀}, ?_, ?_⟩⟩
  · rw [hout₄]
    simp [encBitSetsUpTo]
  · refine ⟨fun _ => ⟨⟨v₀, Finset.mem_singleton_self v₀⟩, ?_⟩,
      fun u v huv => absurd (Subsingleton.elim u v) huv,
      fun u v huv => absurd (Subsingleton.elim u v) huv⟩
    have : Nonempty (({v₀} : Finset (Fin x.n)) : Set (Fin x.n)) :=
      ⟨⟨v₀, Finset.mem_singleton_self v₀⟩⟩
    refine SimpleGraph.Connected.mk (fun a b => ?_)
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    subst ha hb
    exact SimpleGraph.Reachable.refl _

/-! ### Section 3: Persistent Layout and Initialization (`2 ≤ p`) -/

/-- Caller-safe base array index above `50` and above both subroutines `P77` and `P92`. -/
def alg94ArrBase (P77 P92 : Cmd) : ℕ :=
  max 50 (max (folioCallerArrBase P77) (folioCallerArrBase P92))

/-- Caller-safe base register index above `30` and above both subroutines `P77` and `P92`. -/
def alg94RegBase (P77 P92 : Cmd) : ℕ :=
  max 30 (max (folioCallerRegBase P77) (folioCallerRegBase P92))

/-- Initialization program for Algorithm (9.4) when `2 ≤ p`:
Given `inArr = encAlg94In x = x.G.enc ++ x.W.encList ++ sub_flat`:
1. Reads `x.n = inArr[0]` into `reg 1` and saves it in `reg B_reg`,
2. Computes `x.G.enc.length = 2 + 3 * inArr[1]` into `reg 18` and saves it in `reg 19`,
3. Copies `x.G.enc` into `arr B_arr`,
4. Runs `parseFixedWallProg h h2 true (B_arr + 6) inArr (B_arr + 2) 12 18` to populate
   `IsBitSet x.W.vertexFinset (B_arr + 2)` and `IsWallSuccArrs x.W (B_arr + 6)`, advancing `reg 18`
   to `(x.G.enc ++ x.W.encList).length`,
5. Copies `x.W.encList` into `arr (B_arr + 1)`,
6. Copies `sub_flat` into `arr (B_arr + 3)`,
7. Allocates `arr (B_arr + 4)` (`bitSetList ∅`, length `x.n`) and `arr (B_arr + 5)` (`[]`, length `0`). -/
def alg94InitProg (h : ℕ) (h2 : 2 ≤ h) (B_arr B_reg : ℕ) : Cmd :=
  let a_G : Arr := B_arr
  let a_W : Arr := B_arr + 1
  let a_WV : Arr := B_arr + 2
  let a_sub : Arr := B_arr + 3
  let a_X : Arr := B_arr + 4
  let a_stars : Arr := B_arr + 5
  let baseSuccArr : ℕ := B_arr + 6
  let r_n_save : Reg := B_reg
  .seq (.assign 1 (.read inArr (.const 0)))
    (.seq (.assign r_n_save (.reg 1))
      (.seq (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.read inArr (.const 1)))))
        (.seq (.assign 19 (.reg 18))
          (.seq (readSliceProg inArr (.const 0) a_G (.reg 18) 20)
            (.seq (parseFixedWallProg h h2 true baseSuccArr inArr a_WV 12 18)
              (.seq (.assign 14 (.op .sub (.reg 18) (.reg 19)))
                (.seq (readSliceProg inArr (.reg 19) a_W (.reg 14) 20)
                  (.seq (.assign 14 (.op .sub (.len inArr) (.reg 18)))
                    (.seq (readSliceProg inArr (.reg 18) a_sub (.reg 14) 20)
                      (.seq (.alloc a_X (.reg r_n_save))
                        (.alloc a_stars (.const 0))))))))))))

theorem alg94InitProg_exec {w p t h k r : ℕ} (h2 : 2 ≤ h)
    (x : Alg94Input p t h k r)
    (B_arr B_reg : ℕ) (hB_arr : 50 ≤ B_arr) (hB_reg : 30 ≤ B_reg)
    (hw3 : 3 < 2 ^ w)
    (hn1_w : x.n + 1 < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    (he_w : x.G.numEdges < 2 ^ w)
    (hin_w : (encAlg94In x).length < 2 ^ w)
    {s₀ : State} (hs₀ : s₀.arrs inArr = encAlg94In x) :
    ∃ s' time,
      Exec w (alg94InitProg h h2 B_arr B_reg) s₀ s' time ∧
      time ≤ 60 + 16 * (encAlg94In x).length + parseWallCost h x.n + x.n ∧
      s'.regs B_reg = x.n ∧
      s'.arrs B_arr = x.G.enc ∧
      s'.arrs (B_arr + 1) = x.W.encList ∧
      IsBitSet x.W.vertexFinset (B_arr + 2) s' ∧
      s'.arrs (B_arr + 3) = (List.finRange t).flatMap (fun j => (x.W_sub j).encList) ∧
      IsBitSet (∅ : Finset (Fin x.n)) (B_arr + 4) s' ∧
      s'.arrs (B_arr + 5) = [] ∧
      IsWallSuccArrs x.W (B_arr + 6) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hc_w : 3 + elemWallNumVerts h < 2 ^ w := by omega
  let sub_flat := (List.finRange t).flatMap (fun j => (x.W_sub j).encList)
  have hin_eq : encAlg94In x = x.G.enc ++ x.W.encList ++ sub_flat := rfl
  have hG_len : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hGW_len_le : (x.G.enc ++ x.W.encList).length ≤ (encAlg94In x).length := by
    rw [hin_eq]; simp [List.length_append]
  have hGW_w : (x.G.enc ++ x.W.encList).length < 2 ^ w := by omega
  have hG_len_w : x.G.enc.length < 2 ^ w := by
    simp [List.length_append] at hGW_w; omega
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hin_len0 : 0 < (s₀.arrs inArr).length := by
    rw [hs₀, hin_eq]; simp [MultiDigraph.enc]
  have hin_len1 : 1 < (s₀.arrs inArr).length := by
    rw [hs₀, hin_eq]; simp [MultiDigraph.enc]
  have hin_get0 : (s₀.arrs inArr)[0]'hin_len0 = x.n := by
    simp [hs₀, hin_eq, MultiDigraph.enc]
  have hin_get1 : (s₀.arrs inArr)[1]'hin_len1 = x.G.numActivePairs := by
    simp [hs₀, hin_eq, MultiDigraph.enc]
  -- 1. reg 1 := inArr[0]
  let s₁ := s₀.setReg 1 x.n
  have hex₁ : Exec w (.assign 1 (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hin_len0, hin_get0, hn_w])
  -- 2. reg B_reg := reg 1
  let s₂ := s₁.setReg B_reg x.n
  have hex₂ : Exec w (.assign B_reg (.reg 1)) s₁ s₂ 2 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hn_w])
  -- 3. reg 18 := 2 + 3 * inArr[1]
  let s₃ := s₂.setReg 18 x.G.enc.length
  have hex₃ :
      Exec w (.assign 18 (.op .add (.const 2) (.op .mul (.const 3) (.read inArr (.const 1)))))
        s₂ s₃ 7 :=
    .assign (by
      rw [hG_len]
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw1, hw3, hin_len1, hin_get1, hm_w, h3m_w, show 2 < 2 ^ w by omega,
        show 2 + 3 * x.G.numActivePairs < 2 ^ w by omega])
  -- 4. reg 19 := reg 18
  let s₄ := s₃.setReg 19 x.G.enc.length
  have hex₄ : Exec w (.assign 19 (.reg 18)) s₃ s₄ 2 :=
    .assign (by simp only [s₃, Expr.eval, checkWord, State.setReg_regs_self, hG_len_w, ↓reduceIte])
  -- 5. readSliceProg inArr 0 B_arr (reg 18) 20
  have hG_enc_w : ∀ v ∈ x.G.enc, v < 2 ^ w :=
    all_lt_enc_multiDigraph x.G hn_w hm_w he_w
  rcases readSliceProg_exec_full inArr B_arr (.const 0) 18 20
      (by change 0 ≠ B_arr; omega) (by decide) [] x.G.enc (x.W.encList ++ sub_flat)
      rfl rfl hG_enc_w hw1 (by simpa using hG_len_w) (s := s₄)
      (by simp [Expr.eval, checkWord, h0_w])
      (by
        change s₀.arrs inArr = [] ++ x.G.enc ++ (x.W.encList ++ sub_flat)
        rw [hs₀, hin_eq]; simp [List.append_assoc])
      rfl with
    ⟨s₅, t₅, hex₅, ht₅, harrG_5, harr₅, hreg₅⟩
  -- 6. parseFixedWallProg h h2 true (B_arr + 6) inArr (B_arr + 2) 12 18
  have hsucc_ne :
      (true = true) → ∀ idx : Fin (elemWallEdges h).length,
        (B_arr + 6) + idx.1 ≠ inArr ∧ (B_arr + 6) + idx.1 ≠ B_arr + 2 ∧ (B_arr + 6) + idx.1 ≠ 12 := by
    intro _ idx
    change B_arr + 6 + idx.1 ≠ 0 ∧ B_arr + 6 + idx.1 ≠ B_arr + 2 ∧ B_arr + 6 + idx.1 ≠ 12
    omega
  rcases parseFixedWallProg_exec h2 le_rfl x.W x.hW_valid.2.2 true (B_arr + 6)
      inArr (B_arr + 2) 12 18
      (by change 0 ≠ B_arr + 2; omega) (by decide) (by omega) hsucc_ne (by decide)
      x.G.enc sub_flat hw1 hn1_w hc_w hGW_w (s := s₅)
      (by rw [harr₅ inArr (by change 0 ≠ B_arr; omega)]; exact hs₀)
      (by
        rw [hreg₅ 1 (Or.inl (by decide))]
        dsimp [s₄, s₃, s₂, s₁]
        rw [State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 19),
          State.setReg_regs_ne _ _ (by decide : (1 : Reg) ≠ 18),
          State.setReg_regs_ne _ _ (ne_reg_of_ne (by omega)),
          State.setReg_regs_self])
      (by rw [hreg₅ 18 (Or.inl (by decide))]; rfl) with
    ⟨s₆, t₆, hex₆, ht₆, hr18_6, _, hWV_6, _, hsucc_6, harr₆, hreg₆⟩
  have hsucc_6' : IsWallSuccArrs x.W (B_arr + 6) s₆ := hsucc_6 rfl
  -- 7. reg 14 := reg 18 - reg 19
  have hr19_6 : s₆.regs 19 = x.G.enc.length := by
    rw [hreg₆ 19 (Or.inr (by decide)) (by decide) (by decide), hreg₅ 19 (Or.inl (by decide))]
    rfl
  have hr18_6' : s₆.regs 18 = x.G.enc.length + x.W.encList.length := by
    rw [hr18_6, List.length_append]
  have hW_len_w : x.W.encList.length < 2 ^ w := by
    simp [List.length_append] at hGW_w; omega
  let s₇ := s₆.setReg 14 x.W.encList.length
  have hex₇ : Exec w (.assign 14 (.op .sub (.reg 18) (.reg 19))) s₆ s₇ 4 :=
    .assign (by
      have htot_w : x.G.enc.length + x.W.encList.length < 2 ^ w := by
        simpa [List.length_append] using hGW_w
      simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18_6', hr19_6,
        hG_len_w, htot_w, hW_len_w, ↓reduceIte, Nat.add_sub_cancel_left])
  -- 8. readSliceProg inArr (reg 19) (B_arr + 1) (reg 14) 20
  have hW_enc_w : ∀ v ∈ x.W.encList, v < 2 ^ w :=
    all_lt_encList_of_isValid x.W x.hW_valid.2.2 le_rfl hh_w hc2_w hn_w
  have hin_7 : s₇.arrs inArr = x.G.enc ++ x.W.encList ++ sub_flat := by
    simp only [s₇, State.setReg_arrs]
    rw [harr₆ inArr (by change 0 ≠ B_arr + 2; omega) (by decide)
      (fun _ k => by change 0 ≠ B_arr + 6 + k.1; omega),
      harr₅ inArr (by change 0 ≠ B_arr; omega)]
    exact hs₀
  rcases readSliceProg_exec_full inArr (B_arr + 1) (.reg 19) 14 20
      (by change 0 ≠ B_arr + 1; omega) (by decide) x.G.enc x.W.encList sub_flat
      rfl rfl hW_enc_w hw1 (by simpa [List.length_append] using hGW_w) (s := s₇)
      (by
        have hr19_7 : s₇.regs 19 = x.G.enc.length := by simp [s₇, hr19_6]
        simp only [Expr.eval, checkWord, hr19_7, hG_len_w, ↓reduceIte])
      hin_7 (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, harrW_8, harr₈, hreg₈⟩
  -- 9. reg 14 := len inArr - reg 18
  have hin_8 : s₈.arrs inArr = (x.G.enc ++ x.W.encList) ++ sub_flat ++ [] := by
    rw [harr₈ inArr (by change 0 ≠ B_arr + 1; omega), hin_7]; simp
  have hr18_8 : s₈.regs 18 = (x.G.enc ++ x.W.encList).length := by
    rw [hreg₈ 18 (Or.inl (by decide))]; simp [s₇, hr18_6]
  have hin_len_8 : (s₈.arrs inArr).length = (x.G.enc ++ x.W.encList).length + sub_flat.length := by
    rw [hin_8, List.append_nil, List.length_append]
  have hin_len_eq : (s₈.arrs inArr).length = (encAlg94In x).length := by
    rw [hin_8, List.append_nil, ← hin_eq]
  have hsub_len_w : sub_flat.length < 2 ^ w := by omega
  let s₉ := s₈.setReg 14 sub_flat.length
  have hex₉ : Exec w (.assign 14 (.op .sub (.len inArr) (.reg 18))) s₈ s₉ 4 :=
    .assign (by
      have htot_w : (x.G.enc ++ x.W.encList).length + sub_flat.length < 2 ^ w := by omega
      simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hin_len_8, hr18_8,
        hGW_w, htot_w, hsub_len_w, ↓reduceIte, Nat.add_sub_cancel_left])
  -- 10. readSliceProg inArr (reg 18) (B_arr + 3) (reg 14) 20
  have hsub_enc_w : ∀ v ∈ sub_flat, v < 2 ^ w := by
    intro v hv
    dsimp [sub_flat] at hv
    rw [List.mem_flatMap] at hv
    rcases hv with ⟨j, _, hvj⟩
    exact all_lt_encList_of_isValid (x.W_sub j)
      (x.W.isValid_of_isSubwallOf x.hW_valid.2.2 (x.hsub j))
      (le_of_isSubwallOf (x.hsub j)) hh_w hc2_w hn_w v hvj
  rcases readSliceProg_exec_full inArr (B_arr + 3) (.reg 18) 14 20
      (by change 0 ≠ B_arr + 3; omega) (by decide) (x.G.enc ++ x.W.encList) sub_flat []
      rfl rfl hsub_enc_w hw1 (by omega) (s := s₉)
      (by
        have hr18_9 : s₉.regs 18 = (x.G.enc ++ x.W.encList).length := by
          simp [s₉, hr18_8]
        simp only [Expr.eval, checkWord, hr18_9, hGW_w, ↓reduceIte])
      hin_8 (by simp [s₉]) with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, harrSub_10, harr₁₀, hreg₁₀⟩
  -- 11. alloc (B_arr + 4) (reg B_reg)
  have hrB_10 : s₁₀.regs B_reg = x.n := by
    rw [hreg₁₀ B_reg (Or.inr (by omega))]
    simp only [s₉]
    rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14),
      hreg₈ B_reg (Or.inr (by omega))]
    simp only [s₇]
    rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14),
      hreg₆ B_reg (Or.inr (by omega)) (by omega) (by omega),
      hreg₅ B_reg (Or.inr (by omega))]
    simp [s₄, s₃, s₂, State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 19),
      State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 18)]
  let s₁₁ := s₁₀.setArr (B_arr + 4) (List.replicate x.n 0)
  have hex₁₁ : Exec w (.alloc (B_arr + 4) (.reg B_reg)) s₁₀ s₁₁ (1 + x.n) :=
    .alloc (by simp [Expr.eval, checkWord, hrB_10, hn_w])
  -- 12. alloc (B_arr + 5) 0
  let s₁₂ := s₁₁.setArr (B_arr + 5) (List.replicate 0 0)
  have hex₁₂ : Exec w (.alloc (B_arr + 5) (.const 0)) s₁₁ s₁₂ (1 + 0) :=
    .alloc (by simp [Expr.eval, checkWord, h0_w])
  dsimp [Expr.cost] at ht₅ ht₈ ht₁₀
  have ht_slices : t₅ + t₈ + t₁₀ ≤ 16 * (encAlg94In x).length + 28 := by
    have hlen_sum :
        x.G.enc.length + x.W.encList.length + sub_flat.length = (encAlg94In x).length := by
      rw [hin_eq, List.length_append, List.length_append]
    have hmul_sum :
        16 * x.G.enc.length + 16 * x.W.encList.length + 16 * sub_flat.length =
          16 * (encAlg94In x).length := by
      rw [← hlen_sum]; ring
    omega
  refine ⟨s₁₂,
    3 + (2 + (7 + (2 + (t₅ + (t₆ + (4 + (t₈ + (4 + (t₁₀ + ((1 + x.n) + (1 + 0))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by omega,
    by simp [s₁₂, s₁₁, hrB_10],
    by
      have ha5 : ((B_arr : ℕ) : Arr) ≠ B_arr + 5 := ne_arr_of_ne (by omega)
      have ha4 : ((B_arr : ℕ) : Arr) ≠ B_arr + 4 := ne_arr_of_ne (by omega)
      simp only [s₁₂, s₁₁, State.setArr_arrs_ne _ _ ha5, State.setArr_arrs_ne _ _ ha4]
      rw [harr₁₀ B_arr (by omega)]; dsimp [s₉]
      rw [harr₈ B_arr (by omega)]; dsimp [s₇]
      rw [harr₆ B_arr (by omega) (by omega) (fun _ k => by omega)]
      exact harrG_5,
    by
      have ha5 : ((B_arr + 1 : ℕ) : Arr) ≠ B_arr + 5 := ne_arr_of_ne (by omega)
      have ha4 : ((B_arr + 1 : ℕ) : Arr) ≠ B_arr + 4 := ne_arr_of_ne (by omega)
      simp only [s₁₂, s₁₁, State.setArr_arrs_ne _ _ ha5, State.setArr_arrs_ne _ _ ha4]
      rw [harr₁₀ (B_arr + 1) (by omega)]; exact harrW_8,
    hWV_6.of_arr_eq (by
      have ha5 : ((B_arr + 2 : ℕ) : Arr) ≠ B_arr + 5 := ne_arr_of_ne (by omega)
      have ha4 : ((B_arr + 2 : ℕ) : Arr) ≠ B_arr + 4 := ne_arr_of_ne (by omega)
      simp only [s₁₂, s₁₁, State.setArr_arrs_ne _ _ ha5, State.setArr_arrs_ne _ _ ha4]
      rw [harr₁₀ (B_arr + 2) (by omega)]; dsimp [s₉]
      rw [harr₈ (B_arr + 2) (by omega)]; rfl),
    by
      have ha5 : ((B_arr + 3 : ℕ) : Arr) ≠ B_arr + 5 := ne_arr_of_ne (by omega)
      have ha4 : ((B_arr + 3 : ℕ) : Arr) ≠ B_arr + 4 := ne_arr_of_ne (by omega)
      simp only [s₁₂, s₁₁, State.setArr_arrs_ne _ _ ha5, State.setArr_arrs_ne _ _ ha4]
      exact harrSub_10,
    IsBitSet.empty_of_replicate (by
      have ha5 : ((B_arr + 4 : ℕ) : Arr) ≠ B_arr + 5 := ne_arr_of_ne (by omega)
      simp only [s₁₂, s₁₁, State.setArr_arrs_ne _ _ ha5, State.setArr_arrs_self]),
    by simp [s₁₂],
    hsucc_6'.of_arrs_eq (fun k => by
      have ha5 : ((B_arr + 6 + k.1 : ℕ) : Arr) ≠ B_arr + 5 := ne_arr_of_ne (by omega)
      have ha4 : ((B_arr + 6 + k.1 : ℕ) : Arr) ≠ B_arr + 4 := ne_arr_of_ne (by omega)
      simp only [s₁₂, s₁₁, State.setArr_arrs_ne _ _ ha5, State.setArr_arrs_ne _ _ ha4]
      rw [harr₁₀ (B_arr + 6 + k.1) (by omega)]; dsimp [s₉]
      rw [harr₈ (B_arr + 6 + k.1) (by omega)]; rfl)⟩

/-- Constant factor for `alg94InitProg` time bound. -/
def alg94InitFactor (t h : ℕ) : ℕ :=
  158 + 214 * elemWallNumVerts h + 16 * (t + 1) * (4 + 3 * elemWallNumVerts h)

theorem alg94InitCost_le_mul {p t h k r : ℕ} (x : Alg94Input p t h k r) :
    60 + 16 * (encAlg94In x).length + parseWallCost h x.n + x.n ≤
      alg94InitFactor t h * alg94Size x := by
  have hsz1 : 1 ≤ alg94Size x := by unfold alg94Size; omega
  have hn : x.n ≤ alg94Size x := by unfold alg94Size; omega
  have hm : x.G.numActivePairs ≤ alg94Size x := by
    have := Alg91.numActivePairs_le_numEdges x.G
    unfold alg94Size; omega
  have hin := length_encAlg94In_le x
  have h1 : 60 * 1 ≤ 60 * alg94Size x := Nat.mul_le_mul_left 60 hsz1
  have h2 : 16 * (2 + 3 * x.G.numActivePairs) ≤ 80 * alg94Size x := by omega
  have h3 : 16 * ((t + 1) * maxWallEncLen h x.n) ≤
      16 * (t + 1) * (4 + 3 * elemWallNumVerts h) * alg94Size x := by
    have hmax := maxWallEncLen_le_mul h x.n (alg94Size x) hsz1 hn
    have hmul := Nat.mul_le_mul_left (16 * (t + 1)) hmax
    calc 16 * ((t + 1) * maxWallEncLen h x.n)
        = (16 * (t + 1)) * maxWallEncLen h x.n := by ring
      _ ≤ (16 * (t + 1)) * ((4 + 3 * elemWallNumVerts h) * alg94Size x) := hmul
      _ = 16 * (t + 1) * (4 + 3 * elemWallNumVerts h) * alg94Size x := by ring
  have h4 := parseWallCost_le_mul h x.n (alg94Size x) hsz1 hn
  rw [Nat.add_mul] at h4
  have h5 : 16 * (encAlg94In x).length ≤
      16 * (2 + 3 * x.G.numActivePairs) + 16 * ((t + 1) * maxWallEncLen h x.n) := by
    have := Nat.mul_le_mul_left 16 hin
    omega
  unfold alg94InitFactor
  simp only [Nat.add_mul]
  omega

end GraphMinor.Compute

end
