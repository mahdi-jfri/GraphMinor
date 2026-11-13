module

public import GraphMinor.Compute.GM02TupleExpressions
public import GraphMinor.Compute.GM02TupleVertices
public import GraphMinor.Compute.GM02ComponentSearch
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Initializing the component-search labels

For each vertex, compare its number with the fixed candidate slots.
Write two when a slot contains it and zero otherwise. The Word RAM
array-writing loop therefore builds exactly the forbidden-vertex labels
used by the component search in II (3.1), in linear time for a fixed
number of slots.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical

/-- The labels obtained from the absence bit of the candidate slots. -/
def gm02ComponentLabelExpr (base : Reg) (k : ℕ) : Expr :=
  .op .mul (.const 2) (.op .sub (.const 1) (gm02TupleFreeExpr base (.reg 180) k))

/-- Fill the forbidden-vertex label array for a single component search. -/
def gm02ComponentLabelsProg (base : Reg) (k : ℕ) : Cmd :=
  gm13TabulateProg 180 (.reg 40) (gm02ComponentLabelExpr base k) TwoPaths.aLab

/-- The numeric-slot absence expression has the indicated vertex-set meaning. -/
theorem gm02TupleFreeExpr_eval_slots {n k w : ℕ} (base vertexReg : Reg)
    (f : Fin k → ℕ) (v : Fin n) (s : State) (hw : 1 < 2 ^ w)
    (hv : s.regs vertexReg = v.val) (hvn : n < 2 ^ w)
    (hf : ∀ i, f i ≤ n) (hslots : ∀ i, s.regs (base + i.val) = f i) :
    (gm02TupleFreeExpr base (.reg vertexReg) k).eval w s =
      some (if v ∉ gm02SlotVertices (n := n) f then 1 else 0) := by
  have he := gm02TupleFreeExpr_eval base (.reg vertexReg) k v.val s hw
    (eval_reg hv (v.isLt.trans hvn))
    (fun i hi => by rw [hslots ⟨i, hi⟩]; exact (hf ⟨i, hi⟩).trans_lt hvn)
  have hiff : (∀ i < k, v.val ≠ s.regs (base + i)) ↔ v ∉ gm02SlotVertices (n := n) f := by
    rw [mem_gm02SlotVertices]
    constructor
    · intro h ⟨i, hi⟩
      exact h i.val i.isLt ((hslots i).trans hi).symm
    · intro h i hi heq
      exact h ⟨⟨i, hi⟩, (hslots ⟨i, hi⟩).symm.trans heq.symm⟩
  simpa only [hiff] using he

/-- Initialization writes precisely the separator-forbidden labels and
preserves every register except the loop counter and every other array. -/
theorem gm02ComponentLabelsProg_exec {n k w : ℕ} (base : Reg) (hbase : 200 ≤ base)
    (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hrn : s.regs 40 = n)
    (hslots : ∀ i, s.regs (base + i.val) = f i) :
    ∃ s' t, Exec w (gm02ComponentLabelsProg base k) s s' t ∧
      t ≤ 6 + n * (k * 6 + 19) ∧
      Keeps [180] [TwoPaths.aLab] s s' ∧
      s'.arrs TwoPaths.aLab = List.ofFn (gm02ComponentLabels (gm02SlotVertices (n := n) f)) := by
  let words := List.ofFn (gm02ComponentLabels (gm02SlotVertices (n := n) f))
  obtain ⟨s', t, hex, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w) 180 (.reg 40)
    (gm02ComponentLabelExpr base k) TwoPaths.aLab words s (by omega) (by simpa [words] using hn)
    (fun st hkeep => by
      simp only [words, List.length_ofFn]
      apply eval_reg _ hn
      exact (hkeep.1 40 (by simp)).trans hrn)
    (fun st i hi hkeep hri => by
      have hin : i < n := by simpa only [words, List.length_ofFn] using hi
      let v : Fin n := ⟨i, hin⟩
      have hslt : ∀ j, st.regs (base + j.val) = f j := by
        intro j
        have hne : base + j.val ≠ 180 := by
          dsimp only [Reg] at hbase ⊢
          omega
        exact (hkeep.1 _ (by simpa only [List.mem_singleton] using hne)).trans (hslots j)
      have he := gm02TupleFreeExpr_eval_slots base 180 f v st (by omega) hri hn hf hslt
      have hsub := eval_sub (eval_const (show 1 < 2 ^ w by omega)) he
      have hb : 2 * (1 - (if v ∉ gm02SlotVertices (n := n) f then 1 else 0)) < 2 ^ w := by
        split_ifs <;> omega
      have hmul := eval_mul (eval_const hw) hsub hb
      have hword : words[i] = gm02ComponentLabels (gm02SlotVertices (n := n) f) v := by
        simp only [words, List.getElem_ofFn]
        rfl
      rw [hword]
      by_cases hx : v ∈ gm02SlotVertices (n := n) f
      · simpa only [gm02ComponentLabelExpr, gm02ComponentLabels, ite_eq_left hx,
          not_true_eq_false, ite_eq_right (not_not_intro hx), Nat.sub_zero, Nat.mul_one] using hmul
      · simpa only [gm02ComponentLabelExpr, gm02ComponentLabels, ite_eq_right hx,
          ite_eq_left hx, Nat.sub_self, Nat.mul_zero] using hmul)
  refine ⟨s', t, hex, ?_, hk, hout⟩
  have hc := gm02TupleFreeExpr_cost base (.reg 180) k
  simp only [Expr.cost] at hc
  simp only [gm02ComponentLabelExpr, Expr.cost, hc, words, List.length_ofFn] at ht
  have hm : n * (1 + (1 + (1 + (1 + k * (1 + 5)) + 1) + 1) + 11) ≤
      n * (k * 6 + 19) := Nat.mul_le_mul_left n (by omega)
  exact ht.trans (Nat.add_le_add_left hm 6)

end GraphMinor.Compute
