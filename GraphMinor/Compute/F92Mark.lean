module

public import GraphMinor.Compute.F92Unpack

/-!
# Marking a subwall and its inside

The input parser reads a subwall at the current position in a packed array. It marks the
vertices and perimeter, then subtracts the perimeter bitset from the vertex bitset. Thus the
three output arrays give the vertices, perimeter and inside of the subwall. The position is
advanced to the next subwall. The time is linear in the ambient vertex count for fixed height.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Read one subwall and mark its vertices, perimeter and inside. -/
def f92MarkSubwallProg (h : ℕ) (a_src a_V a_perim a_inside : ℕ)
    (r_base r_pos : ℕ) : Cmd :=
  .seq (f92UnpackSubwallAtProg h a_src a_V a_perim r_base r_pos)
    (sdiffBitSetProg a_V a_perim a_inside r_base (r_base + 4))

/-- The marking routine reads the encoded subwall at `pre.length` and advances past it.
It needs a valid subwall of positive height at most `h`, distinct source and output arrays,
a position register above the scratch registers, and the stated word bounds. -/
theorem f92MarkSubwallProg_exec {w h hs n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight hs G) (hW : W.IsValid) (hhs : 1 ≤ hs) (hle : hs ≤ h)
    (a_src a_V a_perim a_inside r_base r_pos : ℕ)
    (hsV : a_src ≠ a_V) (hsP : a_src ≠ a_perim) (hVP : a_V ≠ a_perim)
    (hVI : a_V ≠ a_inside) (hPI : a_perim ≠ a_inside)
    (hpos : r_base + 4 < r_pos) (pre suf : List ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hh : h < 2 ^ w)
    (hc : 3 + elemWallNumVerts h < 2 ^ w)
    (hlen : (pre ++ W.encList).length < 2 ^ w)
    {s : State} (hsrc : s.arrs a_src = pre ++ W.encList ++ suf)
    (hrn : s.regs r_base = n) (hrpos : s.regs r_pos = pre.length) :
    ∃ s' t, Exec w (f92MarkSubwallProg h a_src a_V a_perim a_inside r_base r_pos) s s' t ∧
      t ≤ 9 + 4 * h + parseWallCost h n + 15 * n ∧
      s'.regs r_pos = (pre ++ W.encList).length ∧
      IsBitSet W.vertexFinset a_V s' ∧
      IsBitSet W.perimeterFinset a_perim s' ∧
      IsBitSet W.insideFinset a_inside s' ∧
      (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → a ≠ a_inside → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, (q < r_base + 1 ∨ r_base + 4 < q) → q ≠ r_pos →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hpos₁, hV₁, hP₁, harr₁, hreg₁⟩ :=
    f92UnpackSubwallAtProg_exec hhs hle W hW a_src a_V a_perim r_base r_pos
      hsV hsP hVP hpos pre suf hw hn hh hc hlen hsrc hrn hrpos
  have hn₁ : s₁.regs r_base = n :=
    (hreg₁ r_base (Or.inl (by omega)) (by omega)).trans hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hI₂, harr₂, hreg₂⟩ :=
    sdiffBitSetProg_exec W.vertexFinset W.perimeterFinset a_V a_perim a_inside
      r_base (r_base + 4) hVI hPI (show (r_base : ℕ) ≠ r_base + 4 by omega) hw hn hV₁ hP₁ hn₁
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    (hreg₂ r_pos (by omega)).trans hpos₁,
    hV₁.of_arr_eq (harr₂ a_V hVI), hP₁.of_arr_eq (harr₂ a_perim hPI),
    hI₂, fun a hV hP hI => (harr₂ a hI).trans (harr₁ a hV hP), ?_⟩
  intro q hq hqp
  exact (hreg₂ q (by omega)).trans (hreg₁ q hq hqp)

/-- Mark the first `j` subwalls in their input order. The height bound is fixed, while each
subwall's own height and encoding length are read from the source array. -/
def f92MarkSubwallsUpTo (h a_base r_base : ℕ) : ℕ → Cmd
  | 0 => .skip
  | j + 1 => .seq (f92MarkSubwallsUpTo h a_base r_base j)
      (f92MarkSubwallProg h (aSub a_base) (aSubV a_base j) (aTmp2 a_base)
        (aSubIn a_base j) r_base (r_base + 5))

/-- Execution of the subwall marking loop. All input subwalls are valid subwalls by
`x.hnondiv`; no path-search or construction claim is assumed. -/
theorem f92MarkSubwallsUpTo_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (a_base r_base : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hh : h < 2 ^ w)
    (hc : 3 + elemWallNumVerts h < 2 ^ w)
    (hlen : ((List.finRange k).flatMap (fun i => (x.W_sub i).encList)).length < 2 ^ w) :
    ∀ j (_hj : j ≤ k) {s : State}
      (_hsrc : s.arrs (aSub a_base) =
        (List.finRange k).flatMap (fun i => (x.W_sub i).encList))
      (_hrn : s.regs r_base = x.n)
      (_hrpos : s.regs (r_base + 5) = 0),
    ∃ s' t, Exec w (f92MarkSubwallsUpTo h a_base r_base j) s s' t ∧
      t ≤ 1 + j * (9 + 4 * h + parseWallCost h x.n + 15 * x.n) ∧
      s'.regs (r_base + 5) =
        (((List.finRange k).take j).flatMap (fun i => (x.W_sub i).encList)).length ∧
      (∀ i : Fin k, i.val < j →
        IsBitSet (x.W_sub i).vertexFinset (aSubV a_base i.val) s' ∧
        IsBitSet (x.W_sub i).insideFinset (aSubIn a_base i.val) s') ∧
      (∀ a : ℕ, a ≠ aTmp2 a_base →
        (∀ i < j, a ≠ aSubV a_base i ∧ a ≠ aSubIn a_base i) →
        s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < r_base + 1 ∨ r_base + 5 < q → s'.regs q = s.regs q)
  | 0, _, s, _, _, hrpos => by
    exact ⟨s, 1, .skip s, by omega, by simpa using hrpos,
      fun i hi => by omega, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | j + 1, hj, s, hsrc, hrn, hrpos => by
    have hjk : j < k := by omega
    let f : Fin k → List ℕ := fun i => (x.W_sub i).encList
    let pre := ((List.finRange k).take j).flatMap f
    let suf := ((List.finRange k).drop (j + 1)).flatMap f
    obtain ⟨s₁, t₁, hex₁, ht₁, hpos₁, hbits₁, harr₁, hreg₁⟩ :=
      f92MarkSubwallsUpTo_exec x a_base r_base hw hn hh hc hlen j (by omega)
        hsrc hrn hrpos
    have hsrc₁ : s₁.arrs (aSub a_base) = (List.finRange k).flatMap f := by
      rw [harr₁ (aSub a_base) (by f92_omega) (fun i hi => by
        constructor <;> f92_omega)]
      exact hsrc
    have hsplit : s₁.arrs (aSub a_base) = pre ++ (x.W_sub ⟨j, hjk⟩).encList ++ suf := by
      rw [hsrc₁, Alg91.flatMap_finRange_eq_take_append_drop f j,
        Alg91.flatMap_drop_eq_cons f hjk]
      simp [pre, suf, List.append_assoc, f]
    have hlen₁ : (pre ++ (x.W_sub ⟨j, hjk⟩).encList).length < 2 ^ w := by
      have hb : (pre ++ (x.W_sub ⟨j, hjk⟩).encList).length ≤
          ((List.finRange k).flatMap f).length := by
        rw [Alg91.flatMap_finRange_eq_take_append_drop f j,
          Alg91.flatMap_drop_eq_cons f hjk]
        simp [pre, f, List.length_append]
      exact hb.trans_lt hlen
    have hsub := (x.hnondiv ⟨j, hjk⟩).1
    have hsmall : 1 ≤ x.h_sub ⟨j, hjk⟩ := by
      obtain ⟨h2, _⟩ := hsub
      omega
    have hle := le_of_isSubwallOf hsub
    obtain ⟨s₂, t₂, hex₂, ht₂, hpos₂, hV₂, _, hI₂, harr₂, hreg₂⟩ :=
      f92MarkSubwallProg_exec (x.W_sub ⟨j, hjk⟩)
        (x.W.isValid_of_isSubwallOf x.hW_valid.2.2 hsub) hsmall hle
        (aSub a_base) (aSubV a_base j) (aTmp2 a_base) (aSubIn a_base j)
        r_base (r_base + 5) (by f92_omega) (by f92_omega) (by f92_omega)
        (by f92_omega) (by f92_omega) (by omega) pre suf hw hn hh hc hlen₁
        hsplit ((hreg₁ r_base (Or.inl (by omega))).trans hrn) hpos₁
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]; omega
    · rw [hpos₂, Alg91.flatMap_take_succ_finRange f hjk]
    · intro i hi
      by_cases hij : i.val = j
      · have he : i = ⟨j, hjk⟩ := Fin.ext hij
        subst i
        exact ⟨hV₂, hI₂⟩
      · have hip : i.val < j := by omega
        obtain ⟨hV, hI⟩ := hbits₁ i hip
        exact ⟨hV.of_arr_eq (harr₂ _ (by f92_omega) (by f92_omega) (by f92_omega)),
          hI.of_arr_eq (harr₂ _ (by f92_omega) (by f92_omega) (by f92_omega))⟩
    · intro a ha hprev
      obtain ⟨haV, haI⟩ := hprev j (by omega)
      exact (harr₂ a haV ha haI).trans
        (harr₁ a ha (fun i hi => hprev i (by omega)))
    · intro q hq
      exact (hreg₂ q (by omega) (by omega)).trans (hreg₁ q hq)

/-- Start the packed-subwall cursor at zero and mark all subwalls. -/
def f92MarkSubwallsProg (h k a_base r_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 5) (.const 0)) (f92MarkSubwallsUpTo h a_base r_base k)

/-- All subwall vertex and inside arrays are correct after the marking program.
The source encoding, main-wall bitset and CSR arrays lie outside the arrays it writes. -/
theorem f92MarkSubwallsProg_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (a_base r_base : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hh : h < 2 ^ w)
    (hc : 3 + elemWallNumVerts h < 2 ^ w)
    (hlen : ((List.finRange k).flatMap (fun i => (x.W_sub i).encList)).length < 2 ^ w)
    {s : State} (hsrc : s.arrs (aSub a_base) =
      (List.finRange k).flatMap (fun i => (x.W_sub i).encList))
    (hrn : s.regs r_base = x.n) :
    ∃ s' t, Exec w (f92MarkSubwallsProg h k a_base r_base) s s' t ∧
      t ≤ 3 + k * (9 + 4 * h + parseWallCost h x.n + 15 * x.n) ∧
      (∀ i : Fin k, IsBitSet (x.W_sub i).vertexFinset (aSubV a_base i.val) s' ∧
        IsBitSet (x.W_sub i).insideFinset (aSubIn a_base i.val) s') ∧
      (∀ a : ℕ, a ≠ aTmp2 a_base →
        (∀ i < k, a ≠ aSubV a_base i ∧ a ≠ aSubIn a_base i) →
        s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q < r_base + 1 ∨ r_base + 5 < q → s'.regs q = s.regs q) := by
  let s₁ := s.setReg (r_base + 5) 0
  have hex₁ : Exec w (.assign (r_base + 5) (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  obtain ⟨s₂, t₂, hex₂, ht₂, _, hbits₂, harr₂, hreg₂⟩ :=
    f92MarkSubwallsUpTo_exec x a_base r_base hw hn hh hc hlen k le_rfl
      (s := s₁) hsrc (by simp [s₁, hrn]) (by simp [s₁])
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega,
    fun i => hbits₂ i i.isLt, harr₂, ?_⟩
  intro q hq
  rw [hreg₂ q hq]
  exact State.setReg_regs_ne s _ (by omega : (q : ℕ) ≠ r_base + 5)

/-- A constant depending only on the height and number of subwalls bounds the marking time
in units of the input size. -/
theorem f92MarkSubwallsCost_le_mul {l m p h k r : ℕ} (x : Alg92Input l m p h k r) :
    3 + k * (9 + 4 * h + parseWallCost h x.n + 15 * x.n) ≤
      (3 + k * (41 + 4 * h + 214 * elemWallNumVerts h)) * alg92Size x := by
  have hsz : 1 ≤ alg92Size x := by unfold alg92Size; omega
  have hn : x.n ≤ alg92Size x := by unfold alg92Size; omega
  have hp := parseWallCost_le_mul h x.n (alg92Size x) hsz hn
  have hconst := Nat.mul_le_mul_left (9 + 4 * h) hsz
  have hverts := Nat.mul_le_mul_left 15 hn
  have hstep : 9 + 4 * h + parseWallCost h x.n + 15 * x.n ≤
      (41 + 4 * h + 214 * elemWallNumVerts h) * alg92Size x := by
    simp only [Nat.add_mul] at hp hconst ⊢
    omega
  have htotal := Nat.mul_le_mul_left k hstep
  have hthree := Nat.mul_le_mul_left 3 hsz
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

end GraphMinor.Compute.Alg92
