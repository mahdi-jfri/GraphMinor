module

public import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Reordering prescribed cuffs after orientation reversal

In the reflection used for VI (5.11), page 134, source zero is fixed
and the other prescribed indices occur in reverse order. Compute
this permutation by reading position `(length - i) % length`. The
same verified array loop works for either cuff and also for an empty
row, where no array read is performed.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The index permutation induced by reflection about source zero. -/
def gm06Alg511ReflectFin {k : ℕ} (i : Fin k) : Fin k :=
  ⟨if i.val = 0 then 0 else k - i.val, by split <;> omega⟩

/-- Reversing the prescribed cuff indices twice gives the original index. -/
theorem gm06Alg511ReflectFin_involutive {k : ℕ} :
    Function.Involutive (@gm06Alg511ReflectFin k) := by
  intro i
  apply Fin.ext
  dsimp only [gm06Alg511ReflectFin]
  split_ifs <;> omega

/-- The modulus expression used by the RAM gives the same permutation. -/
theorem gm06Alg511ReflectFin_eq_mod {k : ℕ} (i : Fin k) :
    (gm06Alg511ReflectFin i).val = (k - i.val) % k := by
  by_cases hi : i.val = 0
  · simp [gm06Alg511ReflectFin, hi]
  · simp only [gm06Alg511ReflectFin, hi, ite_false]
    apply (Nat.mod_eq_of_lt _).symm
    omega

/-- Reorder a supplied cuff row by the reflection index permutation. -/
def gm06Alg511ReflectCuffWords (xs : List ℕ) : List ℕ :=
  (List.range xs.length).map (fun i => xs.getD ((xs.length - i) % xs.length) 0)

/-- On an ordered cuff enumeration, the computed row is exactly
that enumeration composed with the reflection permutation. -/
theorem gm06Alg511ReflectCuffWords_ofFn {k : ℕ} (f : Fin k → ℕ) :
    gm06Alg511ReflectCuffWords (List.ofFn f) = List.ofFn (fun i => f (gm06Alg511ReflectFin i)) := by
  apply List.ext_getElem (by simp [gm06Alg511ReflectCuffWords])
  intro i hi hi'
  have hik : i < k := by simpa using hi'
  have hk : 0 < k := by omega
  have hm : (k - i) % k < k := Nat.mod_lt _ hk
  simp only [gm06Alg511ReflectCuffWords, List.length_ofFn, List.getElem_map,
    List.getElem_range, List.getElem_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hm)]
  simp only [List.getElem_ofFn, Option.getD_some]
  congr 1
  apply Fin.ext
  exact (gm06Alg511ReflectFin_eq_mod ⟨i, hik⟩).symm

/-- Reflect a cuff row into a distinct scratch array, using counter 20. -/
def gm06Alg511ReflectCuffProg (src dst : Arr) : Cmd :=
  mapProg 20 (.len src) dst src
    (.op .mod (.op .sub (.len src) (.reg 20)) (.len src))

/-- The cuff reflection is computed in linear time, preserving its
source and every other array outside the destination. -/
theorem gm06Alg511ReflectCuffProg_exec {w : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (xs : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hwords : ∀ v ∈ xs, v < 2 ^ w)
    (ha : s.arrs src = xs) :
    ∃ s' t, Exec w (gm06Alg511ReflectCuffProg src dst) s s' t ∧
      t ≤ 6 + 16 * xs.length ∧ Keeps [20] [dst] s s' ∧
      s'.arrs dst = gm06Alg511ReflectCuffWords xs := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := mapProg_exec 20 (.len src) dst src
    (.op .mod (.op .sub (.len src) (.reg 20)) (.len src)) hne.symm
    xs.length (fun i => (xs.length - i) % xs.length) xs s hw hn
    (fun st h => Crossing.eval_len ((h.2 src (by simpa using hne)).trans ha) hn)
    (fun st i h hi hilt => by
      have ha' : st.arrs src = xs := (h.2 src (by simpa using hne)).trans ha
      have hkpos : xs.length ≠ 0 := by omega
      have hr : (xs.length - i) % xs.length < 2 ^ w :=
        (Nat.mod_lt _ (by omega)).trans hn
      have hdiff : xs.length - i < 2 ^ w := (Nat.sub_le _ _).trans_lt hn
      simp [Expr.eval, ha', hi, BinOp.eval, BinOp.raw, checkWord,
        hn, hilt.trans hn, hdiff, hr, hkpos])
    (fun i hi => Nat.mod_lt _ (by omega)) hwords ha
  refine ⟨s', t, he, ?_, hk, hout⟩
  norm_num [Expr.cost] at ht
  simpa only [Nat.mul_comm] using ht

end GraphMinor.Compute
