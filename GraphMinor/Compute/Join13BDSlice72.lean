module

public import GraphMinor.Compute.Join13BDWords72

/-!
# Preparing decomposition arrays for the (7.2) core call

A positive tree code is copied into separate parent and leaf arrays. An empty
tree code instead produces the one-node convention of the core program. Both
branches take time linear in the decomposition-code length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Copy a slice of an array, recording the exact list slice and the usual
memory preservation properties. -/
theorem readArraySlice72_exec {w : ℕ} (a_src a_dst r_len r_base off len : ℕ)
    (e_off : Expr) (L : List ℕ) (hne : a_src ≠ a_dst) (hr : r_len < r_base)
    (hw : 1 < 2 ^ w) (hbound : off + len ≤ L.length) (hword : off + len < 2 ^ w)
    (hwords : ∀ x ∈ (L.drop off).take len, x < 2 ^ w)
    (s : State) (he_off : e_off.eval w s = some off)
    (hsrc : s.arrs a_src = L) (hrlen : s.regs r_len = len) :
    ∃ s' t, Exec w (readSliceProg a_src e_off a_dst (.reg r_len) r_base) s s' t ∧
      t ≤ 16 * len + 8 + e_off.cost ∧ s'.arrs a_dst = (L.drop off).take len ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ j < r_base, s'.regs j = s.regs j) := by
  apply readSliceProg_exec a_src a_dst e_off r_len r_base hne hr
    (L.take off) ((L.drop off).take len) ((L.drop off).drop len)
    (by simp [List.length_take, Nat.min_eq_left (by omega : off ≤ L.length)])
    (by simp only [List.length_take, List.length_drop]; omega)
    hwords hw hword he_off
  · rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
    exact hsrc
  · exact hrlen

/-- Read the two decomposition slices, or make the one-node convention when
the caller's tree size in `r_t` is zero. -/
def prepareBD72Prog (a_bd a_par a_tau r_m r_t r_base : ℕ) : Cmd :=
  .ite (.reg r_t)
    (.seq (readSliceProg a_bd (.const 2) a_par (.reg r_t) r_base)
      (readSliceProg a_bd (.op .add (.const 2) (.reg r_t)) a_tau (.reg r_m) r_base))
    (.seq (.assign r_t (.const 1))
      (.seq (.alloc a_par (.const 1)) (.alloc a_tau (.reg r_m))))

/-- The prepared parent and leaf arrays encode the core input in the caller's
edge order. The effective tree size is left in `r_t`. -/
theorem prepareBD72Prog_exec {w n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode)
    (a_bd a_par a_tau r_m r_t r_base : ℕ)
    (hbd_par : a_bd ≠ a_par) (hbd_tau : a_bd ≠ a_tau) (hpar_tau : a_par ≠ a_tau)
    (hrm : r_m < r_base) (hrt : r_t < r_base) (hne_reg : r_m ≠ r_t)
    (s : State) (hw : 2 < 2 ^ w) (hcode : bdCode.length < 2 ^ w)
    (hsrc : s.arrs a_bd = bdCode) (hr_m : s.regs r_m = G.numEdges)
    (hr_t : s.regs r_t = bdNumTreeVerts bdCode) :
    let x := multiCoreInput72 G bdCode hbd
    ∃ s' t, Exec w (prepareBD72Prog a_bd a_par a_tau r_m r_t r_base) s s' t ∧
      t ≤ 100 * (G.numEdges + 1) ∧
      s'.arrs a_par = List.ofFn (fun z : Fin x.t => x.p z.1) ∧
      s'.arrs a_tau = List.ofFn (fun e : Fin G.numEdges => (x.τ e).1) ∧
      s'.regs r_t = x.t ∧
      (∀ a : ℕ, a ≠ a_par → a ≠ a_tau → s'.arrs a = s.arrs a) ∧
      (∀ j < r_base, j ≠ r_t → s'.regs j = s.regs j) := by
  let x := multiCoreInput72 G bdCode hbd
  have hlen : bdCode.length = 2 + bdNumTreeVerts bdCode + G.numEdges := by
    rw [← hbd.1]
    exact hbd.2.2.1
  have hsz : 2 + bdNumTreeVerts bdCode + G.numEdges < 2 ^ w := by rwa [hlen] at hcode
  have ht_le : bdNumTreeVerts bdCode ≤ 2 * G.numEdges := by simpa [hbd.1] using hbd.2.1
  have h1 : 1 < 2 ^ w := by omega
  by_cases ht : 0 < bdNumTreeVerts bdCode
  · have htree : x.t = bdNumTreeVerts bdCode := by exact (multiCoreInput72_t G bdCode hbd).trans (ite_eq_left ht)
    have hpar_words : ∀ y ∈ (bdCode.drop 2).take (bdNumTreeVerts bdCode), y < 2 ^ w := by
      rw [multiCoreInput72_parentWords G bdCode hbd ht]
      intro y hy
      obtain ⟨z, rfl⟩ := List.mem_ofFn.1 hy
      have hp : x.p z.1 < x.t := by
        by_cases hz : z.1 = 0
        · rw [hz, x.hp0]
          exact x.ht
        · exact (x.hp z.1 (by omega) z.2).trans z.2
      exact hp.trans_le (by omega)
    have hleaf_take : (bdCode.drop (2 + bdNumTreeVerts bdCode)).take G.numEdges =
        bdCode.drop (2 + bdNumTreeVerts bdCode) := List.take_of_length_le (by simp [hlen])
    have hτ_words : ∀ y ∈ (bdCode.drop (2 + bdNumTreeVerts bdCode)).take G.numEdges, y < 2 ^ w := by
      rw [hleaf_take, multiCoreInput72_leafWords G bdCode hbd ht]
      intro y hy
      obtain ⟨e, rfl⟩ := List.mem_ofFn.1 hy
      have he := (x.τ e).2
      exact he.trans_le (by omega)
    obtain ⟨s₁, t₁, hex₁, ht₁, hp₁, ha₁, hreg₁⟩ :=
      readArraySlice72_exec a_bd a_par r_t r_base 2 (bdNumTreeVerts bdCode) (.const 2) bdCode
        hbd_par hrt h1 (by omega) (by omega) hpar_words s
        (by simp [Expr.eval, checkWord, hw]) hsrc hr_t
    obtain ⟨s₂, t₂, hex₂, ht₂, hτ₂, ha₂, hreg₂⟩ :=
      readArraySlice72_exec a_bd a_tau r_m r_base (2 + bdNumTreeVerts bdCode) G.numEdges
        (.op .add (.const 2) (.reg r_t)) bdCode hbd_tau hrm h1 (by omega) (by omega) hτ_words s₁
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw,
            (hreg₁ _ hrt).trans hr_t,
            (show bdNumTreeVerts bdCode < 2 ^ w by omega),
            (show 2 + bdNumTreeVerts bdCode < 2 ^ w by omega)])
        ((ha₁ a_bd hbd_par).trans hsrc) ((hreg₁ _ hrm).trans hr_m)
    refine ⟨s₂, 1 + (t₁ + t₂), .ite_true (v := bdNumTreeVerts bdCode)
      (by simp [Expr.eval, checkWord, hr_t, show bdNumTreeVerts bdCode < 2 ^ w by omega])
      (by omega) (.seq hex₁ hex₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Expr.cost] at ht₁ ht₂
      omega
    · rw [ha₂ a_par hpar_tau, hp₁]
      exact multiCoreInput72_parentWords G bdCode hbd ht
    · rw [hτ₂, hleaf_take]
      exact multiCoreInput72_leafWords G bdCode hbd ht
    · rw [hreg₂ _ hrt, hreg₁ _ hrt, hr_t]
      exact htree.symm
    · intro a hpa hta
      exact (ha₂ a hta).trans (ha₁ a hpa)
    · intro j hj _
      exact (hreg₂ j hj).trans (hreg₁ j hj)
  · have ht0 : bdNumTreeVerts bdCode = 0 := by omega
    let s₁ := s.setReg r_t 1
    have hex₁ : Exec w (.assign r_t (.const 1)) s s₁ 2 := .assign (by simp [Expr.eval, checkWord, h1])
    let s₂ := s₁.setArr a_par [0]
    have hex₂ : Exec w (.alloc a_par (.const 1)) s₁ s₂ 2 := .alloc (m := 1) (by simp [Expr.eval, checkWord, h1])
    let s₃ := s₂.setArr a_tau (List.replicate G.numEdges 0)
    have hex₃ : Exec w (.alloc a_tau (.reg r_m)) s₂ s₃ (1 + G.numEdges) :=
      .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hne_reg, hr_m,
        show G.numEdges < 2 ^ w by omega])
    refine ⟨s₃, 1 + (2 + (2 + (1 + G.numEdges))), .ite_false
      (by simp [Expr.eval, checkWord, hr_t, ht0]) (.seq hex₁ (.seq hex₂ hex₃)), by omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [multiCoreInput72_parentWords_zero G bdCode hbd ht0]
      simp [s₃, s₂, hpar_tau]
    · rw [multiCoreInput72_leafWords_zero G bdCode hbd ht0]
      simp [s₃]
    · simp [s₃, s₂, s₁, multiCoreInput72_t, ht0]
    · intro a hpa hta
      simp [s₃, s₂, s₁, hpa, hta]
    · intro j _ hj
      simp [s₃, s₂, s₁, hj]

end GraphMinor.Compute
