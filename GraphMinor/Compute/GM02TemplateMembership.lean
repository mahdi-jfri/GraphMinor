module

public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Testing membership in expanded boundary templates

A fixed catalogue branch knows its reserved vertices and terminal
endpoints as boundary indices. Each index is looked up in the old-name
array. Multiplying the resulting inequality bits tests absence from the
expanded template without adding any data to the parent input.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Test absence from the old names at a fixed list of boundary indices. -/
def gm02TemplateFreeExpr (orig : Arr) (vertex : Expr) : List ℕ → Expr
  | [] => .const 1
  | i :: is => .op .mul (gm02TemplateFreeExpr orig vertex is)
      (.op .sub (.const 1) (.op .eq vertex (.read orig (.const i))))

/-- Expression size is linear in the fixed template length. -/
theorem gm02TemplateFreeExpr_cost (orig : Arr) (vertex : Expr) (indices : List ℕ) :
    (gm02TemplateFreeExpr orig vertex indices).cost =
      1 + indices.length * (vertex.cost + 6) := by
  induction indices with
  | nil => simp only [gm02TemplateFreeExpr, Expr.cost, List.length_nil, Nat.zero_mul, Nat.add_zero]
  | cons i is ih =>
    simp only [gm02TemplateFreeExpr, Expr.cost, List.length_cons, ih, Nat.add_mul,
      Nat.one_mul]
    omega

/-- Every factor is an inequality bit, so the product gives exact absence. -/
theorem gm02TemplateFreeExpr_eval {w : ℕ} (orig : Arr) (vertex : Expr)
    (indices : List ℕ) (v : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hv : vertex.eval w s = some v)
    (hindices : ∀ i ∈ indices, i < (s.arrs orig).length ∧ i < 2 ^ w)
    (hwords : ∀ i (hi : i < (s.arrs orig).length), (s.arrs orig)[i] < 2 ^ w) :
    (gm02TemplateFreeExpr orig vertex indices).eval w s =
      some (if ∀ i ∈ indices, (s.arrs orig)[i]! ≠ v then 1 else 0) := by
  induction indices with
  | nil => simpa only [gm02TemplateFreeExpr, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, ↓reduceIte] using eval_const hw
  | cons i is ih =>
    have hi := hindices i (List.mem_cons_self ..)
    have ht := ih (fun j hj => hindices j (List.mem_cons_of_mem _ hj))
    have hr := eval_read (a := orig) (eval_const hi.2) hi.1 (hwords i hi.1)
    have hc := eval_eq hv hr hw
    have hs := eval_sub (eval_const hw) hc
    have hb : (if ∀ j ∈ is, (s.arrs orig)[j]! ≠ v then 1 else 0) *
        (1 - if v = (s.arrs orig)[i] then 1 else 0) < 2 ^ w := by
      split_ifs <;> omega
    have he := eval_mul ht hs hb
    have hget : (s.arrs orig)[i]! = (s.arrs orig)[i] := getElem!_pos _ i hi.1
    have heq : (if ∀ j ∈ is, (s.arrs orig)[j]! ≠ v then 1 else 0) *
        (1 - if v = (s.arrs orig)[i] then 1 else 0) =
        (if ∀ j ∈ i :: is, (s.arrs orig)[j]! ≠ v then 1 else 0) := by
      simp only [List.mem_cons, forall_eq_or_imp, hget]
      by_cases hq : v = (s.arrs orig)[i] <;> simp [hq, eq_comm]

    simpa only [gm02TemplateFreeExpr, heq] using he

/-- With an old-name table, template absence is absence from its image set. -/
theorem gm02TemplateFreeExpr_eval_names {n b w : ℕ} (f : Fin b → Fin n)
    (indices : List (Fin b)) (orig : Arr) (vertex : Expr) (v : Fin n) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hb : b < 2 ^ w)
    (horig : s.arrs orig = List.ofFn (fun i => (f i).val))
    (hv : vertex.eval w s = some v.val) :
    (gm02TemplateFreeExpr orig vertex (indices.map Fin.val)).eval w s =
      some (if v ∈ indices.toFinset.image f then 0 else 1) := by
  have he := gm02TemplateFreeExpr_eval orig vertex (indices.map Fin.val) v.val s hw hv
    (by
      intro i hi
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      simpa only [horig, List.length_ofFn] using And.intro j.isLt (j.isLt.trans hb))
    (by
      intro i hi
      have hib : i < b := by simpa only [horig, List.length_ofFn] using hi
      simpa only [horig, List.getElem_ofFn] using (f ⟨i, hib⟩).isLt.trans hn)
  have hget (j : Fin b) : (List.ofFn (fun i : Fin b => (f i).val))[j.val]! = (f j).val := by
    rw [getElem!_pos _ _ (by simpa only [List.length_ofFn] using j.isLt)]
    simp only [List.getElem_ofFn]
  have hp : (∀ i ∈ indices.map Fin.val, (s.arrs orig)[i]! ≠ v.val) ↔
      v ∉ indices.toFinset.image f := by
    simp only [horig, List.forall_mem_map, hget,
      Finset.mem_image, List.mem_toFinset, not_exists, not_and]
    constructor
    · intro h j hj heq
      exact h j hj (congrArg Fin.val heq)
    · intro h j hj heq
      exact h j hj (Fin.ext heq)
  simpa only [hp, ite_not] using he

end GraphMinor.Compute
