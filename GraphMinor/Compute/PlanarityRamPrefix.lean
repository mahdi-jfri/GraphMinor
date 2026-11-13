module

public import GraphMinor.Compute.PlanarityRamLayout

/-!
# Updating live prefixes in search arenas

The DFS in Part I, Section 1 creates records at the end of the live edge
prefix and updates lowpoints in existing records. These lemmas justify
both operations without allocating a new array. They also recover individual
words for RAM reads from the prefix relation.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- Changing unrelated arrays does not change a prefix representation. -/
theorem PrefixAt.of_arr_eq {s s' : State} {a capacity : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) (heq : s'.arrs a = s.arrs a) :
    PrefixAt s' a capacity xs := by
  simpa only [PrefixAt, heq] using h

/-- Writing the next free slot extends a live prefix by one word. -/
theorem PrefixAt.write_end {s : State} {a capacity : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) (hfree : xs.length < capacity) (v : ℕ) :
    PrefixAt (s.writeArr a xs.length v) a capacity (xs ++ [v]) := by
  rcases h with ⟨hlen, hle, htake⟩
  refine ⟨by simp [hlen], by simp; omega, ?_⟩
  simp only [State.writeArr_arrs_self, List.length_append, List.length_singleton]
  rw [List.take_add_one, List.take_set_of_le (Nat.le_refl _), htake]
  have hb : xs.length < (s.arrs a).length := by omega
  rw [List.getElem?_set_self hb]
  rfl

/-- Updating a live record changes its prefix word and preserves capacity. -/
theorem PrefixAt.write_existing {s : State} {a capacity : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) (i v : ℕ) :
    PrefixAt (s.writeArr a i v) a capacity (xs.set i v) := by
  rcases h with ⟨hlen, hle, htake⟩
  refine ⟨by simp [hlen], by simpa using hle, ?_⟩
  simp only [State.writeArr_arrs_self, List.length_set, List.take_set, htake]

/-- A live prefix gives the exact optional array lookup. -/
theorem PrefixAt.getElem? {s : State} {a capacity : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) {i : ℕ} (hi : i < xs.length) :
    (s.arrs a)[i]? = xs[i]? := by
  have ht := congrArg (fun l : List ℕ => l[i]?) h.2.2
  simpa only [List.getElem?_take, hi, ↓reduceIte] using ht

/-- Every live word fits in the allocated array. -/
theorem PrefixAt.index_lt {s : State} {a capacity : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) {i : ℕ} (hi : i < xs.length) :
    i < (s.arrs a).length := by
  exact h.1.symm ▸ Nat.lt_of_lt_of_le hi h.2.1

/-- A bounded word in a live prefix is a valid RAM read. -/
theorem PrefixAt.read_eval {s : State} {a capacity w i : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) (hi : i < xs.length)
    (hidx : i < 2 ^ w) (hval : xs[i] < 2 ^ w) :
    (Expr.read a (.const i)).eval w s = some xs[i] := by
  have hb := h.index_lt hi
  have he : (s.arrs a)[i] = xs[i] := by
    have ht := h.getElem? hi
    simpa only [List.getElem?_eq_getElem hb, List.getElem?_eq_getElem hi,
      Option.some.injEq] using ht
  simp only [Expr.eval, checkWord_of_lt hidx, hb, ↓reduceDIte, he,
    checkWord_of_lt hval]

/-- A register holding a live index can read its represented word. -/
theorem PrefixAt.read_reg_eval {s : State} {a capacity w i r : ℕ} {xs : List ℕ}
    (h : PrefixAt s a capacity xs) (hi : i < xs.length)
    (hr : s.regs r = i) (hidx : i < 2 ^ w) (hval : xs[i] < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some xs[i] := by
  have he := h.read_eval hi hidx hval
  simpa only [Expr.eval, hr, checkWord_of_lt hidx] using he

/-- Search representation depends only on its two live counters and arrays. -/
theorem SearchAt.setReg {N M : ℕ} {s : State} {search : LRPlanarity.Search}
    (h : SearchAt N M s search) (r v : ℕ) (h37 : r ≠ 37) (h39 : r ≠ 39) :
    SearchAt N M (s.setReg r v) search := by
  simpa only [SearchAt, PrefixAt, State.setReg_arrs,
    State.setReg_regs_ne s v (Ne.symm h37),
    State.setReg_regs_ne s v (Ne.symm h39)] using h

/-- Removing the optional-word tag recovers the depth with default zero. -/
theorem optionWord_sub_one (depth : Option ℕ) : optionWord depth - 1 = depth.getD 0 := by
  cases depth <;> simp [optionWord]

end GraphMinor.Compute.PlanarityRam
