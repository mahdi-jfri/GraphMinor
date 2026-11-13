module

public import GraphMinor.Compute.GM06Alg511ReflectCuff
public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06RestorePathWord
public import GraphMinor.Compute.GM06SelectRow
import GraphMinor.Compute.GM06RefreshContractedMasks
import GraphMinor.Compute.CrossingOpsCycleTest
import Mathlib.Tactic

/-!
# Reordering the stored path rows under reflection

Reflection changes the source order and preserves each ordinary
path's directed edge words. Copy the original path-table code to
a protected array. For each source index, select its reflected
source's original row and replace the corresponding output row.
All other drawing and binary integer arrays survive.

The proof follows these actual reads and replacements through a
prefix invariant. Every intermediate row is an original row, so
one uniform capacity bounds every table. This is the path-table
part of the orientation reversal in VI (5.11), page 134.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The reflection permutation acts only on path-row indices. -/
def gm06Alg511ReflectedPathRows (rows : List (List ℕ)) : List (List ℕ) :=
  List.ofFn (fun i : Fin rows.length => rows[(gm06Alg511ReflectFin i).val])

/-- Reflection retains the path-table row count. -/
theorem gm06Alg511ReflectedPathRows_length (rows : List (List ℕ)) :
    (gm06Alg511ReflectedPathRows rows).length = rows.length := List.length_ofFn

private theorem reflected_member {rows : List (List ℕ)} {row : List ℕ}
    (h : row ∈ gm06Alg511ReflectedPathRows rows) : row ∈ rows := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  exact List.getElem_mem _

private def reflectedPrefix (rows : List (List ℕ)) (i : ℕ) : List (List ℕ) :=
  (gm06Alg511ReflectedPathRows rows).take i ++ rows.drop i

private theorem prefix_length (rows : List (List ℕ)) (i : ℕ) :
    (reflectedPrefix rows i).length = rows.length := by
  simp only [reflectedPrefix, List.length_append, List.length_take, List.length_drop,
    gm06Alg511ReflectedPathRows_length]
  omega

private theorem prefix_zero (rows : List (List ℕ)) : reflectedPrefix rows 0 = rows := by
  simp [reflectedPrefix]

private theorem prefix_last (rows : List (List ℕ)) :
    reflectedPrefix rows rows.length = gm06Alg511ReflectedPathRows rows := by
  simp [reflectedPrefix, gm06Alg511ReflectedPathRows_length]

private theorem prefix_member {rows : List (List ℕ)} {i : ℕ} {row : List ℕ}
    (h : row ∈ reflectedPrefix rows i) : row ∈ rows := by
  rcases List.mem_append.mp h with h | h
  · exact reflected_member (List.mem_of_mem_take h)
  · exact List.mem_of_mem_drop h

private theorem prefix_step (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) :
    (reflectedPrefix rows i).set i ((gm06Alg511ReflectedPathRows rows)[i]'(by simpa only [gm06Alg511ReflectedPathRows_length] using hi)) =
      reflectedPrefix rows (i + 1) := by
  have ht : ((gm06Alg511ReflectedPathRows rows).take i).length = i :=
    List.length_take_of_le (by rw [gm06Alg511ReflectedPathRows_length]; exact hi.le)
  unfold reflectedPrefix
  rw [List.drop_eq_getElem_cons hi, List.set_append_right _ _ (by omega), ht, Nat.sub_self, List.set_cons_zero,
    List.take_succ_eq_append_getElem (by simpa only [gm06Alg511ReflectedPathRows_length] using hi)]
  simp only [List.singleton_append, List.append_assoc]

private theorem code_length (rows : List (List ℕ)) (n : ℕ) (hb : ∀ row ∈ rows, row.length ≤ n) :
    (gm06EncodeRows rows).length ≤ 1 + rows.length + rows.length * n := by
  have hflat : rows.flatten.length ≤ rows.length * n := by
    induction rows with
    | nil => simp
    | cons row rows ih =>
      have hr := hb row (by simp)
      have ht := ih (fun r hm => hb r (by simp [hm]))
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      nlinarith only [hr, ht]
  rw [gm06EncodeRows_length]
  omega

private theorem code_words {w : ℕ} (rows : List (List ℕ)) (n : ℕ)
    (hk : rows.length < 2 ^ w) (hn : n < 2 ^ w)
    (hb : ∀ row ∈ rows, row.length ≤ n ∧ ∀ v ∈ row, v < 2 ^ w) :
    ∀ v ∈ gm06EncodeRows rows, v < 2 ^ w := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hk
  · obtain ⟨row, hr, hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (hb row hr).1.trans_lt hn
    · exact (hb row hr).2 v hv

/-- Read a reflected source's row from the protected original
code, then install it at the current output source index. -/
def gm06Alg511BinaryReflectPathsBody : Cmd :=
  .seq (.assign 31 (.op .mod (.op .sub (.reg 52) (.reg 1701)) (.reg 52)))
    (.seq (gm06SelectRowProg 1700 13)
      (.seq (gm06Alg511CopyRowProg 13 27)
        (.seq (.assign 31 (.reg 1701)) gm06ReplacePathRowProg)))

/-- Copy and permute the exact ordinary path rows, retaining the
original code until every reflected source has been installed. -/
def gm06Alg511BinaryReflectPathsProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 8 1700)
    (.seq (.assign 1701 (.const 0)) (forUp 1701 (.reg 52) gm06Alg511BinaryReflectPathsBody))

private theorem body_exec {w : ℕ} (original current : List (List ℕ)) (i n : ℕ)
    (hi : i < original.length) (hcount : current.length = original.length) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hcap : 1 + original.length + original.length * n < 2 ^ w)
    (ho : ∀ row ∈ original, row.length ≤ n ∧ ∀ v ∈ row, v < 2 ^ w)
    (hc : ∀ row ∈ current, row.length ≤ n ∧ ∀ v ∈ row, v < 2 ^ w)
    (hnew : (gm06EncodeRows (current.set i ((gm06Alg511ReflectedPathRows original)[i]'(by simpa only [gm06Alg511ReflectedPathRows_length] using hi)))).length < 2 ^ w)
    (hO : s.arrs 1700 = gm06EncodeRows original) (hC : s.arrs 8 = gm06EncodeRows current)
    (hI : s.regs 1701 = i) (hK : s.regs 52 = original.length) :
    ∃ t u, Exec w gm06Alg511BinaryReflectPathsBody s t u ∧
      u ≤ 300 + 40 * original.length + 150 * n + 100 * (1 + original.length + original.length * n) ∧
      Keeps [31, 7, 8, 9, 11, 20, 4, 323, 324, 313, 98] [13, 27, 25, 8, 28] s t ∧
      t.arrs 8 = gm06EncodeRows (current.set i ((gm06Alg511ReflectedPathRows original)[i]'(by simpa only [gm06Alg511ReflectedPathRows_length] using hi))) := by
  let j := (gm06Alg511ReflectFin (⟨i, hi⟩ : Fin original.length)).val
  have hj : j < original.length := (gm06Alg511ReflectFin (⟨i, hi⟩ : Fin original.length)).isLt
  let row := original[j]'hj
  have hrow : (gm06Alg511ReflectedPathRows original)[i]'(by simpa only [gm06Alg511ReflectedPathRows_length] using hi) = row := by
    simp only [gm06Alg511ReflectedPathRows, List.getElem_ofFn]
    rfl
  have hrowBounds := ho row (List.getElem_mem hj)
  have hkfit : original.length < 2 ^ w := by omega
  have hlenO := code_length original n (fun r hr => (ho r hr).1)
  have hlenC := code_length current n (fun r hr => (hc r hr).1)
  have hfitO : (gm06EncodeRows original).length < 2 ^ w := hlenO.trans_lt hcap
  have hfitC : (gm06EncodeRows current).length < 2 ^ w := by rw [hcount] at hlenC; exact hlenC.trans_lt hcap
  have hwordsO := code_words original n hkfit hn ho
  have hwordsC := code_words current n (hcount ▸ hkfit) hn hc
  have hjmod : (original.length - i) % original.length = j := (gm06Alg511ReflectFin_eq_mod ⟨i, hi⟩).symm
  have heval : (Expr.op .mod (.op .sub (.reg 52) (.reg 1701)) (.reg 52)).eval w s = some j := by
    have h := Crossing.eval_mod (Crossing.eval_sub (Crossing.eval_reg hK hkfit) (Crossing.eval_reg hI (hi.trans hkfit)))
      (Crossing.eval_reg hK hkfit) (by omega : 0 < original.length)
    simpa only [hjmod] using h
  let s₀ := s.setReg 31 j
  have he₀ : Exec w (.assign 31 (.op .mod (.op .sub (.reg 52) (.reg 1701)) (.reg 52))) s s₀ 6 := .assign heval
  obtain ⟨s₁, u₁, he₁, ht₁, hr₁, _, _, hk₁⟩ := gm06SelectRowProg_exec (w := w) 1700 13 (by decide) original j hj s₀ hw
    hO hfitO hwordsO (by simp [s₀])
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hr₂⟩ := gm06Alg511CopyRowProg_exec (w := w) 13 27 (by decide) row s₁ hw
    (hrowBounds.1.trans_lt hn) hrowBounds.2 hr₁
  let s₃ := s₂.setReg 31 i
  have he₃ : Exec w (.assign 31 (.reg 1701)) s₂ s₃ 2 :=
    .assign (Crossing.eval_reg ((hk₂.1 1701 (by decide)).trans ((hk₁.1 1701 (by decide)).trans
      ((State.setReg_regs_ne _ _ (by decide)).trans hI))) (hi.trans hkfit))
  obtain ⟨t, u₄, he₄, ht₄, hk₄, hout, _⟩ := gm06ReplacePathRowProg_exec current i (by omega) row s₃ hw hfitC
    (by simpa only [hrow] using hnew) hwordsC hrowBounds.2
      ((hk₂.2 8 (by decide)).trans ((hk₁.2 8 (by decide)).trans hC)) hr₂ (by simp [s₃])
  let R := [31, 7, 8, 9, 11, 20, 4, 323, 324, 313, 98]
  let A := [13, 27, 25, 8, 28]
  have hk₀ : Keeps R A s s₀ := (Keeps.refl _ _ s).setReg (by simp [R]) j
  have hk₃ : Keeps R A s s₃ := ((hk₀.trans hk₁ (by simp [R]) (by simp [A])).trans hk₂
    (by simp [R]) (by simp [A])).setReg (by simp [R]) i
  have hkeep : Keeps R A s t := hk₃.trans hk₄ (by simp [R]) (by simp [A])
  refine ⟨t, 6 + (u₁ + (u₂ + (2 + u₄))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))), ?_, hkeep,
    by simpa only [hrow] using hout⟩
  have hcurrent := (hc _ (List.getElem_mem (show i < current.length by omega))).1
  change u₁ ≤ 16 + 17 * j + 22 * row.length at ht₁
  rw [hcount] at hlenC
  omega

/-- The concrete path-table reflection returns precisely the
reflection-permuted original rows. Its time is polynomial in the
ordinary graph/table capacity; all binary values and other drawing
fields are retained outside the explicit workspace. -/
theorem gm06Alg511BinaryReflectPathsProg_exec {w : ℕ} (rows : List (List ℕ)) (n : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hcap : 1 + rows.length + rows.length * n < 2 ^ w)
    (hb : ∀ row ∈ rows, row.length ≤ n ∧ ∀ v ∈ row, v < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows) (hK : s.regs 52 = rows.length) :
    ∃ t u, Exec w gm06Alg511BinaryReflectPathsProg s t u ∧
      u ≤ 11 + 12 * (1 + rows.length + rows.length * n) +
        rows.length * (307 + 40 * rows.length + 150 * n + 100 * (1 + rows.length + rows.length * n)) ∧
      Keeps [1701, 31, 7, 8, 9, 11, 20, 4, 323, 324, 313, 98] [1700, 13, 27, 25, 8, 28] s t ∧
      t.arrs 8 = gm06EncodeRows (gm06Alg511ReflectedPathRows rows) := by
  let C := 1 + rows.length + rows.length * n
  let B := 300 + 40 * rows.length + 150 * n + 100 * C
  let R := [1701, 31, 7, 8, 9, 11, 20, 4, 323, 324, 313, 98]
  let A := [1700, 13, 27, 25, 8, 28]
  have hkfit : rows.length < 2 ^ w := by omega
  have hlen := code_length rows n (fun r hr => (hb r hr).1)
  have hfit := hlen.trans_lt hcap
  have hwords := code_words rows n hkfit hn hb
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hbackup⟩ := gm06Alg511CopyRowProg_exec (w := w) 8 1700 (by decide)
    (gm06EncodeRows rows) s hw hfit hwords h8
  let s₂ := s₁.setReg 1701 0
  have he₂ : Exec w (.assign 1701 (.const 0)) s₁ s₂ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  let I : ℕ → State → Prop := fun i st => Keeps R A s st ∧ st.regs 1701 = i ∧ st.regs 52 = rows.length ∧
    st.arrs 1700 = gm06EncodeRows rows ∧ st.arrs 8 = gm06EncodeRows (reflectedPrefix rows i)
  have hI₀ : I 0 s₂ :=
    ⟨(hk₁.mono (by simp [R]) (by simp [A])).setReg (by simp [R]) 0, by simp [s₂],
      (State.setReg_regs_ne _ _ (by decide)).trans ((hk₁.1 52 (by decide)).trans hK), hbackup,
      by rw [prefix_zero]; exact (hk₁.2 8 (by decide)).trans h8⟩
  have hprefixBounds (i : ℕ) : ∀ row ∈ reflectedPrefix rows i, row.length ≤ n ∧ ∀ v ∈ row, v < 2 ^ w :=
    fun row hr => hb row (prefix_member hr)
  obtain ⟨t, ul, hel, htl, hI⟩ := Crossing.forUp_exec' I rows.length B (r_i := 1701) (hi := .reg 52)
    (body := gm06Alg511BinaryReflectPathsBody) hw hkfit
    (fun _ _ st hI => ⟨hI.2.1, Crossing.eval_reg hI.2.2.1 hkfit⟩)
    (fun i hi st hI => by
      have hnextCode : (gm06EncodeRows ((reflectedPrefix rows i).set i ((gm06Alg511ReflectedPathRows rows)[i]'(by
          simpa only [gm06Alg511ReflectedPathRows_length] using hi)))).length < 2 ^ w := by
        rw [prefix_step rows i hi]
        have hh := code_length (reflectedPrefix rows (i + 1)) n (fun r hr => (hprefixBounds _ r hr).1)
        rw [prefix_length] at hh
        exact hh.trans_lt hcap
      obtain ⟨st', u, hex, ht, hk, hout⟩ := body_exec rows (reflectedPrefix rows i) i n hi (prefix_length rows i)
        st hw hn hcap hb (hprefixBounds i) hnextCode hI.2.2.2.1 hI.2.2.2.2 hI.2.1 hI.2.2.1
      have hkAll : Keeps R A s st' := hI.1.trans hk (by simp [R]) (by simp [A])
      refine ⟨st', u, hex, ht, ?_, (hk.1 1701 (by decide)).trans hI.2.1⟩
      refine ⟨hkAll.setReg (by simp [R]) _, by simp,
        (State.setReg_regs_ne _ _ (by decide)).trans ((hk.1 52 (by decide)).trans hI.2.2.1),
        (hk.2 1700 (by decide)).trans hI.2.2.2.1, ?_⟩
      exact hout.trans (congrArg gm06EncodeRows (prefix_step rows i hi))) s₂ hI₀
  refine ⟨t, u₁ + (2 + ul), .seq he₁ (.seq he₂ hel), ?_, hI.1, ?_⟩
  · change ul ≤ 3 + rows.length * (7 + B) at htl
    have hbudget : 7 + B = 307 + 40 * rows.length + 150 * n + 100 * C := by dsimp only [B]; omega
    rw [hbudget] at htl
    change u₁ + (2 + ul) ≤ 11 + 12 * C + rows.length * (307 + 40 * rows.length + 150 * n + 100 * C)
    omega
  · exact hI.2.2.2.2.trans (congrArg gm06EncodeRows (prefix_last rows))

end GraphMinor.Compute
