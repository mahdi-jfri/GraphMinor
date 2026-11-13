module

public import GraphMinor.Compute.PlanarityRamPrefix

/-!
# Reading represented search records

The finishing and frame programs read fixed columns by a register holding
an edge identifier. Each lemma below derives that read from `SearchAt`,
with explicit bounds on the index and the word being read.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- An encoded optional entry can be read from its represented array. -/
theorem PrefixAt.read_option_reg {s : State} {a capacity w i r : ℕ}
    {values : Array (Option ℕ)}
    (h : PrefixAt s a capacity (values.toList.map optionWord))
    (hi : i < values.size) (hr : s.regs r = i) (hiw : i < 2 ^ w)
    (hval : optionWord values[i] < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some (optionWord values[i]) := by
  have hh := h.read_reg_eval (by simpa using hi) hr hiw (by simpa using hval)
  simpa using hh

/-- Read the tail column at a represented edge. -/
theorem SearchAt.read_tail {N M w i r : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hi : i < search.edges.size)
    (hr : s.regs r = i) (hiw : i < 2 ^ w) (hval : search.edges[i].source < 2 ^ w) :
    (Expr.read Field.tail.array (.reg r)).eval w s = some search.edges[i].source := by
  obtain ⟨_, _, _, _, _, _, _, _, htail, hhead, htree, hlow, hlow2, hkey, _⟩ := h
  have hh := htail.read_reg_eval (by simpa using hi) hr hiw (by simpa using hval)
  simpa using hh

/-- Read the head column at a represented edge. -/
theorem SearchAt.read_head {N M w i r : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hi : i < search.edges.size)
    (hr : s.regs r = i) (hiw : i < 2 ^ w) (hval : search.edges[i].target < 2 ^ w) :
    (Expr.read Field.head.array (.reg r)).eval w s = some search.edges[i].target := by
  obtain ⟨_, _, _, _, _, _, _, _, htail, hhead, htree, hlow, hlow2, hkey, _⟩ := h
  have hh := hhead.read_reg_eval (by simpa using hi) hr hiw (by simpa using hval)
  simpa using hh

/-- Read the tree column at a represented edge. -/
theorem SearchAt.read_tree {N M w i r : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hi : i < search.edges.size)
    (hr : s.regs r = i) (hiw : i < 2 ^ w) (hval : search.edges[i].tree.toNat < 2 ^ w) :
    (Expr.read Field.tree.array (.reg r)).eval w s = some search.edges[i].tree.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, htail, hhead, htree, hlow, hlow2, hkey, _⟩ := h
  have hh := htree.read_reg_eval (by simpa using hi) hr hiw (by simpa using hval)
  simpa using hh

/-- Read the low column at a represented edge. -/
theorem SearchAt.read_low {N M w i r : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hi : i < search.edges.size)
    (hr : s.regs r = i) (hiw : i < 2 ^ w) (hval : search.edges[i].pair.low < 2 ^ w) :
    (Expr.read Field.low.array (.reg r)).eval w s = some search.edges[i].pair.low := by
  obtain ⟨_, _, _, _, _, _, _, _, htail, hhead, htree, hlow, hlow2, hkey, _⟩ := h
  have hh := hlow.read_reg_eval (by simpa using hi) hr hiw (by simpa using hval)
  simpa using hh

/-- Read the low2 column at a represented edge. -/
theorem SearchAt.read_low2 {N M w i r : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hi : i < search.edges.size)
    (hr : s.regs r = i) (hiw : i < 2 ^ w) (hval : search.edges[i].pair.second < 2 ^ w) :
    (Expr.read Field.low2.array (.reg r)).eval w s = some search.edges[i].pair.second := by
  obtain ⟨_, _, _, _, _, _, _, _, htail, hhead, htree, hlow, hlow2, hkey, _⟩ := h
  have hh := hlow2.read_reg_eval (by simpa using hi) hr hiw (by simpa using hval)
  simpa using hh

/-- Read the key column at a represented edge. -/
theorem SearchAt.read_key {N M w i r : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (hi : i < search.edges.size)
    (hr : s.regs r = i) (hiw : i < 2 ^ w) (hval : search.edges[i].key < 2 ^ w) :
    (Expr.read Field.key.array (.reg r)).eval w s = some search.edges[i].key := by
  obtain ⟨_, _, _, _, _, _, _, _, htail, hhead, htree, hlow, hlow2, hkey, _⟩ := h
  have hh := hkey.read_reg_eval (by simpa using hi) hr hiw (by simpa using hval)
  simpa using hh

end GraphMinor.Compute.PlanarityRam
