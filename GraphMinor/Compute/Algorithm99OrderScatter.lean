module

public import GraphMinor.Compute.Algorithm99OrderRank
public import GraphMinor.Compute.Logic
import Mathlib.Data.List.GetD

/-!
# Scattering leaf assignments into tail buckets

Each edge reads and advances the cursor of its tail bucket. Its leaf assignment
is written at the old cursor position. The destination ranks proved in
`Algorithm99OrderRank` show that earlier assignments are preserved. The pass
works with any vertex-key stream and any word-valued leaf assignments.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Move one leaf assignment to the next position in its tail bucket. -/
def alg99ScatterBody (a_keys a_vals a_cursor a_dst r : ℕ) : Cmd :=
  .seq (.assign (r + 1) (.read a_keys (.reg r)))
    (.seq (.assign (r + 2) (.read a_cursor (.reg (r + 1))))
      (.seq (.write a_dst (.reg (r + 2)) (.read a_vals (.reg r)))
        (.write a_cursor (.reg (r + 1)) (.op .add (.reg (r + 2)) (.const 1)))))

/-- Allocate the destination and scatter all source assignments in order. -/
def alg99ScatterProg (a_keys a_vals a_cursor a_dst r : ℕ) : Cmd :=
  .seq (.alloc a_dst (.len a_keys))
    (.seq (.assign r (.const 0))
      (forUp r (.len a_keys) (alg99ScatterBody a_keys a_vals a_cursor a_dst r)))

/-- Stable scattering writes every source value at its bucket position. The
cursor array initially holds the bucket starts, as supplied by the prefix-sum
pass. All other arrays and registers outside the three scratch registers are
preserved. -/
theorem alg99ScatterProg_exec {w n : ℕ} (keys : List (Fin n)) (vals : List ℕ)
    (a_keys a_vals a_cursor a_dst r : ℕ)
    (hkcur : a_keys ≠ a_cursor) (hkdst : a_keys ≠ a_dst)
    (hvcur : a_vals ≠ a_cursor) (hvdst : a_vals ≠ a_dst)
    (hcd : a_cursor ≠ a_dst)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : keys.length < 2 ^ w)
    (hvlen : vals.length = keys.length) (hvword : ∀ v ∈ vals, v < 2 ^ w)
    (s : State) (hkeys : s.arrs a_keys = keys.map Fin.val)
    (hvals : s.arrs a_vals = vals)
    (hcursor : s.arrs a_cursor = List.ofFn (alg99BucketStart keys)) :
    ∃ s' t, Exec w (alg99ScatterProg a_keys a_vals a_cursor a_dst r) s s' t ∧
      t ≤ 27 * keys.length + 6 ∧
      (s'.arrs a_dst).length = keys.length ∧
      (∀ i : Fin keys.length, (s'.arrs a_dst).getD (alg99BucketPosition keys i) 0 =
        vals[i.1]'(by rw [hvlen]; exact i.2)) ∧
      s'.arrs a_cursor = List.ofFn (fun u : Fin n => alg99BucketStart keys u + keys.count u) ∧
      (∀ a : ℕ, a ≠ a_cursor → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ j : ℕ, j ≠ r → j ≠ r + 1 → j ≠ r + 2 → s'.regs j = s.regs j) := by
  let s₀ := s.setArr a_dst (List.replicate keys.length 0)
  have hex₀ : Exec w (.alloc a_dst (.len a_keys)) s s₀ (1 + keys.length) :=
    .alloc (by simp [Expr.eval, checkWord, hkeys, hlen])
  let si := s₀.setReg r 0
  have hexi : Exec w (.assign r (.const 0)) s₀ si 2 :=
    .assign (by simp [Expr.eval, checkWord])
  let I : ℕ → State → Prop := fun k st =>
    st.arrs a_keys = keys.map Fin.val ∧ st.arrs a_vals = vals ∧ st.regs r = k ∧
      (st.arrs a_dst).length = keys.length ∧
      st.arrs a_cursor = List.ofFn (fun u : Fin n =>
        alg99BucketStart keys u + (keys.take k).count u) ∧
      ∀ i : Fin keys.length, i.1 < k →
        (st.arrs a_dst).getD (alg99BucketPosition keys i) 0 =
          vals[i.1]'(by rw [hvlen]; exact i.2)
  have hloop : ⦃I 0⦄[w]
      forUp r (.len a_keys) (alg99ScatterBody a_keys a_vals a_cursor a_dst r)
      ⦃I keys.length⦄ ≤ fun _ => 3 + keys.length * 26 := by
    apply Triple.forUp_const I keys.length 19 hw hlen
    · intro k _ st hi
      exact ⟨hi.2.2.1, by simp [Expr.eval, checkWord, hi.1, hlen]⟩
    · intro k hk st hi
      obtain ⟨hks, hvs, hr, hdst, hcur, hprev⟩ := hi
      let i : Fin keys.length := ⟨k, hk⟩
      let u := keys[k]
      let pos := alg99BucketPosition keys i
      have hu_w : u.1 < 2 ^ w := u.2.trans hn
      have hk_w : k < 2 ^ w := hk.trans hlen
      have hp_lt : pos < keys.length := alg99BucketPosition_lt keys i
      have hp_w : pos < 2 ^ w := hp_lt.trans hlen
      have hp1_w : pos + 1 < 2 ^ w := by omega
      have hvk : k < vals.length := by omega
      have hv_w : vals[k] < 2 ^ w := hvword _ (List.getElem_mem hvk)
      let s₁ := st.setReg (r + 1) u.1
      have hex₁ : Exec w (.assign (r + 1) (.read a_keys (.reg r))) st s₁ 3 := by
        apply Exec.assign
        simp [Expr.eval, checkWord, hr, hk_w, hks, hk, hu_w, u]
      let s₂ := s₁.setReg (r + 2) pos
      have hex₂ : Exec w (.assign (r + 2) (.read a_cursor (.reg (r + 1)))) s₁ s₂ 3 := by
        apply Exec.assign
        simp [s₁, Expr.eval, checkWord, hu_w, hcur, u.2, pos,
          alg99BucketPosition, i, u]
        exact hp_w
      let s₃ := s₂.writeArr a_dst pos vals[k]
      have hex₃ : Exec w (.write a_dst (.reg (r + 2)) (.read a_vals (.reg r))) s₂ s₃ 4 := by
        apply Exec.write
        · simp [s₂, Expr.eval, checkWord, hp_w]
        · simp [s₂, s₁, Expr.eval, checkWord, hr, hk_w, hvs, hvk, hv_w]
        · simpa [s₂, s₁, hdst] using hp_lt
      let s₄ := s₃.writeArr a_cursor u.1 (pos + 1)
      have hex₄ : Exec w
          (.write a_cursor (.reg (r + 1)) (.op .add (.reg (r + 2)) (.const 1))) s₃ s₄ 5 := by
        apply Exec.write
        · simp [s₃, s₂, s₁, Expr.eval, checkWord, hu_w]
        · simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hp_w, hw, hp1_w]
        · simp [s₃, s₂, s₁, hcd, hcur, u.2]
      have hreg : s₄.regs r = k := by simp [s₄, s₃, s₂, s₁, hr]
      refine ⟨s₄, 15, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by dsimp only; omega, ?_, hreg⟩
      refine ⟨?_, ?_, by simp, ?_, ?_, ?_⟩
      · simp [s₄, s₃, s₂, s₁, hkcur, hkdst, hks]
      · simp [s₄, s₃, s₂, s₁, hvcur, hvdst, hvs]
      · simp [s₄, s₃, s₂, s₁, Ne.symm hcd, hdst]
      · have hcurs : s₄.arrs a_cursor =
            (List.ofFn (fun u : Fin n => alg99BucketStart keys u +
              (keys.take k).count u)).set u.1 (pos + 1) := by
          simp [s₄, s₃, s₂, s₁, hcd, hcur]
        dsimp only [State.setReg_arrs]
        rw [hcurs]
        apply List.ext_getElem (by simp)
        intro j hj hj'
        have hjn : j < n := by simpa using hj'
        rw [List.getElem_ofFn]
        simp only [List.take_add_one, List.getElem?_eq_getElem hk,
          Option.toList_some, List.count_append, List.count_singleton, beq_iff_eq]
        by_cases hju : (⟨j, hjn⟩ : Fin n) = u
        · have hval : j = u.1 := congrArg Fin.val hju
          subst j
          rw [List.getElem_set_self (by simp [u.2])]
          simp [pos, alg99BucketPosition, i, u, Nat.add_assoc]
        · have hval : u.1 ≠ j := by
            intro h
            exact hju (Fin.ext h.symm)
          rw [List.getElem_set_ne hval, List.getElem_ofFn]
          have hne : keys[k] ≠ (⟨j, hjn⟩ : Fin n) := Ne.symm hju
          simp [hne]
      · intro j hjk
        by_cases hji : j = i
        · subst j
          have hdstpos : alg99BucketPosition keys i < (st.arrs a_dst).length := by
            rw [hdst]
            exact hp_lt
          simp [s₄, s₃, s₂, s₁, Ne.symm hcd, pos,
            List.getElem?_set_self hdstpos, i]
        · have hjold : j.1 < k := by
            have hneq : j.1 ≠ k := fun h => hji (Fin.ext h)
            omega
          have hpos : pos ≠ alg99BucketPosition keys j := by
            intro h
            exact hji ((alg99BucketPosition_injective keys h).symm)
          simpa [s₄, s₃, s₂, s₁, Ne.symm hcd, State.writeArr,
            hpos, Ne.symm hpos] using hprev j hjold
  have hi : I 0 si := by
    refine ⟨?_, ?_, by simp [si], ?_, ?_, ?_⟩
    · simp [si, s₀, hkdst, hkeys]
    · simp [si, s₀, hvdst, hvals]
    · simp [si, s₀]
    · simpa [si, s₀, hcd] using hcursor
    · intro i hi
      omega
  obtain ⟨s', t, hex, ht, hout⟩ := hloop si hi
  have hexall : Exec w (alg99ScatterProg a_keys a_vals a_cursor a_dst r) s s'
      ((1 + keys.length) + (2 + t)) := .seq hex₀ (.seq hexi hex)
  refine ⟨s', (1 + keys.length) + (2 + t), hexall, by dsimp only at ht; omega,
    hout.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hout.2.2.2.2.2 i i.2
  · simpa using hout.2.2.2.2.1
  · intro a ha hc
    exact hexall.arrs_eq_of_not_mem_writtenArrs
      (by simp [alg99ScatterProg, alg99ScatterBody, forUp, ha, hc])
  · intro j hj hj1 hj2
    exact hexall.regs_eq_of_not_mem_writtenRegs
      (by simp [alg99ScatterProg, alg99ScatterBody, forUp, hj, hj1, hj2])

end GraphMinor.Compute
