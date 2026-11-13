module

public import GraphMinor.Compute.Algorithm99OutIII
public import GraphMinor.Compute.DPToDCS

/-!
# The program that writes output (iii) of (9.9) from output (a)

Output (iii) of Algorithm (9.9) (Graph Minors XIII, page 104) is the word list
`2 :: (bitSetList orig(X) ++ block)`. The program `alg99OutAProg` builds it from output (a) of
steps (5) to (7): it renames the block along `orig` (`alg99MoveAProg`), writes the head
`2 :: bitSetList (X.image orig)` (`bitImageProg`), and joins the two (`concatTwoArrsProg`).

* `alg99OutAProg_exec`: the program, in time linear in `n`, `v` and the length of the block.
-/

@[expose] public section

namespace GraphMinor.Compute

open Function

/-- `omega` after unfolding `Reg` and `Arr`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

variable {v n : ℕ} {G' : MultiDigraph v} {G : MultiDigraph n} {X : Finset (Fin v)}
  {orig : Fin v → Fin n}

/-- **The output program.** The block is in array `a`, `origList orig` in `o`, `bitSetList X`
in `a_X`, `n` in register `r_n`; the arrays `a_mv` and `a_hd` are scratch, and `a_dst` gets the
output. The registers used are `r, …, r + 23`. -/
def alg99OutAProg (a o a_X a_mv a_hd a_dst : Arr) (r_n r : Reg) : Cmd :=
  .seq (.assign r (.const 0))
    (.seq (alg99MoveAProg a o a_mv r)
      (.seq (bitImageProg a_X o a_hd r_n (r + 20))
        (.seq (.assign (r + 21) (.len a_hd))
          (.seq (.assign (r + 22) (.len a_mv))
            (concatTwoArrsProg a_hd a_mv a_dst (r + 21) (r + 22) (r + 23))))))

/-- **Running the output program.** If array `a` holds a block that parses to `p`, then
`alg99OutAProg` writes `2 :: (bitSetList (X.image orig) ++ p.movedBlock)` to `a_dst`. -/
theorem alg99OutAProg_exec {w : ℕ} {blk : List ℕ}
    (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    {p : ParsedCase3Block (G'.deleteVertices X) X}
    (hparse : parseCase3Block (G'.deleteVertices X) X blk = some p)
    {a o a_X a_mv a_hd a_dst : Arr}
    (hao : a ≠ o) (hamv : a ≠ a_mv) (hXa : a_X ≠ a) (hXmv : a_X ≠ a_mv) (homv : o ≠ a_mv)
    (hXhd : a_X ≠ a_hd) (hohd : o ≠ a_hd) (hmvhd : a_mv ≠ a_hd) (hdhd : a_dst ≠ a_hd) (hdmv : a_dst ≠ a_mv)
    {r_n r : Reg} (hnr : r_n < r) {s : State}
    (ha : s.arrs a = blk) (ho : s.arrs o = origList orig) (hX : s.arrs a_X = bitSetList X)
    (hn : s.regs r_n = n)
    (hblk_w : ∀ x ∈ blk, x < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hlen_w : n + 1 + blk.length < 2 ^ w) :
    ∃ s' t, Exec w (alg99OutAProg a o a_X a_mv a_hd a_dst r_n r) s s' t ∧
      t ≤ 131 * blk.length + 16 * v + 16 * n + 300 ∧
      s'.arrs a_dst = 2 :: (bitSetList (X.image orig) ++ p.movedBlock hinj hmult) ∧
      (p.movedBlock hinj hmult).length ≤ blk.length ∧
      (∀ b, b ≠ a → b ≠ a_mv → b ≠ a_hd → b ≠ a_dst → s'.arrs b = s.arrs b) ∧
      (∀ q < r, s'.regs q = s.regs q) := by
  have hvn : v ≤ n := le_of_injective_orig hinj
  have hn_w : n < 2 ^ w := by omega
  have hlen_w' : blk.length < 2 ^ w := by omega
  -- step 1: `r := 0`
  let s₀ := s.setReg r 0
  have hex₀ : Exec w (.assign r (.const 0)) s s₀ 2 := by
    have h := Exec.assign (w := w) (r := r) (e := .const 0) (s := s) (v := 0)
      (by simp [Expr.eval, checkWord])
    simpa [Expr.cost] using h
  -- step 2: rename the block into `a_mv`
  obtain ⟨s₁, t₁, hex₁, ht₁, hmv₁, hlen₁, hmvw₁, harr₁, hreg₁⟩ :=
    alg99MoveAProg_exec hinj hmult p hparse hao hamv r (s := s₀) (by simpa [s₀] using ha)
      (by simpa [s₀] using ho) (by simp [s₀]) hblk_w hn_w hw4 hlen_w'
  have hX₁ : s₁.arrs a_X = bitSetList X := by
    rw [harr₁ a_X hXa hXmv]; simpa [s₀] using hX
  have ho₁ : s₁.arrs o = origList orig := by
    rw [harr₁ o (Ne.symm hao) homv]; simpa [s₀] using ho
  have hn₁ : s₁.regs r_n = n := by
    rw [hreg₁ r_n hnr, State.setReg_regs_ne _ _ (by romega), hn]
  -- step 3: the head
  obtain ⟨s₂, t₂, hex₂, ht₂, hhd₂, harr₂, hreg₂⟩ :=
    bitImageProg_exec (w := w) (r_i := r + 20) X orig hXhd hohd (by omega) (by omega) (by omega)
      hX₁ ho₁ hn₁
  -- step 4: the two lengths
  set L := p.movedBlock hinj hmult
  have hmv₂ : s₂.arrs a_mv = L := by rw [harr₂ a_mv hmvhd]; exact hmv₁
  have hhd_len : (2 :: bitSetList (X.image orig)).length = n + 1 := by simp
  let s₃ := s₂.setReg (r + 21) (n + 1)
  have hex₃ : Exec w (.assign (r + 21) (.len a_hd)) s₂ s₃ 2 := by
    have h := Exec.assign (w := w) (r := r + 21) (e := .len a_hd) (s := s₂) (v := n + 1)
      (by simp only [Expr.eval_len, hhd₂, hhd_len, checkWord]; simp; omega)
    simpa [Expr.cost] using h
  let s₄ := s₃.setReg (r + 22) L.length
  have hex₄ : Exec w (.assign (r + 22) (.len a_mv)) s₃ s₄ 2 := by
    have h := Exec.assign (w := w) (r := r + 22) (e := .len a_mv) (s := s₃) (v := L.length)
      (by simp only [Expr.eval_len, s₃, State.setReg_arrs, hmv₂, checkWord]; simp; omega)
    simpa [Expr.cost] using h
  -- step 5: join
  have hhd_w : ∀ x ∈ 2 :: bitSetList (X.image orig), x < 2 ^ w := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      split_ifs <;> omega
  obtain ⟨s₅, t₅, hex₅, ht₅, hdst₅, harr₅, hreg₅⟩ :=
    concatTwoArrsProg_exec (w := w) (len₁ := n + 1) (len₂ := L.length) (s := s₄) a_hd a_mv a_dst (r + 21) (r + 22) (r + 23)
      (2 :: bitSetList (X.image orig)) [] L [] hdhd hdmv (by omega) (by omega) hhd_len rfl
      (by omega) (by omega) hhd_w hmvw₁
      (by simp only [s₄, s₃, State.setReg_arrs, hhd₂, List.append_nil])
      (by simp only [s₄, s₃, State.setReg_arrs, hmv₂, List.append_nil])
      (by simp [s₄, s₃]) (by simp [s₄])
  refine ⟨s₅, 2 + (t₁ + (t₂ + (2 + (2 + t₅)))),
    .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))), ?_, ?_, hlen₁, ?_, ?_⟩
  · have := hhd_len; omega
  · rw [hdst₅]; rfl
  · intro b hb hbmv hbhd hbd
    rw [harr₅ b hbd]
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harr₂ b hbhd, harr₁ b hb hbmv]
    simp [s₀]
  · intro q hq
    rw [hreg₅ q (by romega)]
    simp only [s₄, s₃]
    rw [State.setReg_regs_ne _ _ (by romega), State.setReg_regs_ne _ _ (by romega),
      hreg₂ q (by romega), hreg₁ q hq, State.setReg_regs_ne _ _ (by romega)]

end GraphMinor.Compute
