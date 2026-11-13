module

public import GraphMinor.Compute.GM06LoopErasure
public import GraphMinor.Compute.StackQueue

/-!
# Stack and position-table invariants for chronological loop erasure

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) stores a
simple vertex stack, its directed dart stack and the position of every
present vertex. Pushing a new head installs its old stack length.
Popping a vertex clears exactly that vertex's entry. These list
identities justify the direct RAM stack operations and their
comparison with the already-defined chronological erasure function.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Taking a dart prefix takes the corresponding vertex prefix. -/
theorem gm06WalkVertices_take {D V : Type*} (head : D → V) (source : V) (stack : List D) (j : ℕ) :
    gm06WalkVertices head source (stack.take j) = (gm06WalkVertices head source stack).take (j + 1) := by
  simp only [gm06WalkVertices, List.map_take, List.take_succ_cons]

/-- A new dart adds precisely its head at the top of the vertex stack. -/
theorem gm06WalkVertices_append_one {D V : Type*} (head : D → V) (source : V) (stack : List D) (d : D) :
    gm06WalkVertices head source (stack ++ [d]) = gm06WalkVertices head source stack ++ [head d] := by
  simp only [gm06WalkVertices, List.map_append, List.map_cons, List.map_nil, List.cons_append]

/-- Erasure keeps its vertex stack repetition-free for every head row,
independently of the later walk interpretation. -/
theorem gm06EraseClosedStep_nodup {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (stack : List D) (d : D) (hn : (gm06WalkVertices head source stack).Nodup) :
    (gm06WalkVertices head source (gm06EraseClosedStep head source stack d)).Nodup := by
  unfold gm06EraseClosedStep
  dsimp only
  split_ifs with hmem
  · rw [gm06WalkVertices_take]
    exact hn.take
  · rw [gm06WalkVertices_append_one]
    refine List.nodup_append.mpr ⟨hn, by simp, ?_⟩
    intro a ha b hb hab
    have hb' : b = head d := List.mem_singleton.mp hb
    subst b
    subst a
    exact hmem ha

/-- One update keeps darts in their old order or appends the new dart. -/
theorem gm06EraseClosedStep_sublist {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (stack : List D) (d : D) : (gm06EraseClosedStep head source stack d).Sublist (stack ++ [d]) := by
  unfold gm06EraseClosedStep
  dsimp only
  split_ifs
  · exact (List.take_sublist _ _).trans (List.sublist_append_left _ _)
  · exact List.Sublist.refl _

/-- Processing two input lists is the corresponding pair of stack folds. -/
theorem gm06EraseClosedAux_append {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (stack xs ys : List D) :
    gm06EraseClosedAux head source stack (xs ++ ys) =
      gm06EraseClosedAux head source (gm06EraseClosedAux head source stack xs) ys := by
  induction xs generalizing stack with
  | nil => rfl
  | cons d xs ih => exact ih (gm06EraseClosedStep head source stack d)

/-- Every input-prefix extension is one chronological stack update. -/
theorem gm06EraseClosedSubwalks_take_succ {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (ds : List D) (i : ℕ) (hi : i < ds.length) :
    gm06EraseClosedSubwalks head source (ds.take (i + 1)) =
      gm06EraseClosedStep head source (gm06EraseClosedSubwalks head source (ds.take i)) ds[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [gm06EraseClosedSubwalks, gm06EraseClosedAux_append, gm06EraseClosedAux]

/-- The stack fold preserves vertex uniqueness without a supplied path. -/
theorem gm06EraseClosedAux_nodup {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (stack ds : List D) (hn : (gm06WalkVertices head source stack).Nodup) :
    (gm06WalkVertices head source (gm06EraseClosedAux head source stack ds)).Nodup := by
  induction ds generalizing stack with
  | nil => exact hn
  | cons d ds ih => exact ih _ (gm06EraseClosedStep_nodup head source stack d hn)

/-- The stack fold retains an ordered sublist of the processed darts. -/
theorem gm06EraseClosedAux_sublist {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (stack ds : List D) : (gm06EraseClosedAux head source stack ds).Sublist (stack ++ ds) := by
  induction ds generalizing stack with
  | nil => simpa only [gm06EraseClosedAux, List.append_nil] using List.Sublist.refl stack
  | cons d ds ih =>
    exact (ih (gm06EraseClosedStep head source stack d)).trans (by
      simpa only [List.append_assoc, List.singleton_append] using
        (gm06EraseClosedStep_sublist head source stack d).append_right ds)

/-- Every pure output stack fits within its processed input length. -/
theorem gm06EraseClosedSubwalks_sublist {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (ds : List D) : (gm06EraseClosedSubwalks head source ds).Sublist ds := by
  simpa only [gm06EraseClosedSubwalks, List.nil_append] using gm06EraseClosedAux_sublist head source [] ds

/-- The erased stack's vertices are distinct for every input head list. -/
theorem gm06EraseClosedSubwalks_nodup {D V : Type*} [DecidableEq V] (head : D → V) (source : V)
    (ds : List D) : (gm06WalkVertices head source (gm06EraseClosedSubwalks head source ds)).Nodup := by
  simpa only [gm06EraseClosedSubwalks] using
    gm06EraseClosedAux_nodup head source [] ds (by simp [gm06WalkVertices])

/-- Stack contents survive changes to unrelated arrays and registers. -/
theorem IsStack.of_preserve {a r cap : ℕ} {stack : List ℕ} {s t : State}
    (h : IsStack a r cap stack s) (ha : t.arrs a = s.arrs a) (hr : t.regs r = s.regs r) :
    IsStack a r cap stack t := by
  obtain ⟨hlen, hcap, htop, hget⟩ := h
  refine ⟨by simpa only [ha] using hlen, hcap, hr.trans htop, ?_⟩
  intro i hi
  simpa only [ha] using hget i hi

/-- Dense stack positions, with an explicit absent sentinel. -/
def gm06StackPositions (n absent : ℕ) (vertices : List ℕ) : List ℕ :=
  List.ofFn (fun v : Fin n => if v.val ∈ vertices then vertices.idxOf v.val else absent)

/-- The position table covers every permanent vertex label. -/
theorem gm06StackPositions_length (n absent : ℕ) (vertices : List ℕ) :
    (gm06StackPositions n absent vertices).length = n := by
  simp only [gm06StackPositions, List.length_ofFn]

/-- Position lookup is precisely membership followed by the first index. -/
theorem gm06StackPositions_get {n absent v : ℕ} (vertices : List ℕ) (hv : v < n) :
    (gm06StackPositions n absent vertices)[v]?.getD absent =
      if v ∈ vertices then vertices.idxOf v else absent := by
  simp only [gm06StackPositions, List.getElem?_ofFn, hv, ↓reduceDIte, Option.getD_some]

/-- Initializing absent positions and marking the source constructs its
one-vertex stack table. -/
theorem gm06StackPositions_nil (n absent : ℕ) : gm06StackPositions n absent [] = List.replicate n absent := by
  apply List.ext_getElem
  · simp only [gm06StackPositions_length, List.length_replicate]
  · intro i hi hi'
    simp only [gm06StackPositions, List.getElem_ofFn, List.not_mem_nil, ↓reduceIte, List.getElem_replicate]

/-- Pushing a new vertex installs exactly its new stack index. -/
theorem gm06StackPositions_append {n absent v : ℕ} (vertices : List ℕ)
    (_hv : v < n) (hnot : v ∉ vertices) :
    gm06StackPositions n absent (vertices ++ [v]) =
      (gm06StackPositions n absent vertices).set v vertices.length := by
  apply List.ext_getElem
  · simp only [gm06StackPositions_length, List.length_set]
  · intro i hi hi'
    have hin : i < n := by simpa only [gm06StackPositions_length] using hi
    by_cases hiv : i = v
    · subst i
      rw [List.getElem_set_self hi']
      simp only [gm06StackPositions, List.getElem_ofFn, List.mem_append, List.mem_singleton, or_true,
        ↓reduceIte, List.idxOf_append, hnot, List.idxOf_cons_self, Nat.zero_add]
    · rw [List.getElem_set_ne (by omega)]
      by_cases hm : i ∈ vertices
      · simp only [gm06StackPositions, List.getElem_ofFn, List.mem_append, hm, true_or, ↓reduceIte,
          List.idxOf_append_of_mem hm]
      · simp only [gm06StackPositions, List.getElem_ofFn, List.mem_append, List.mem_singleton, hm,
          hiv, or_false, ↓reduceIte]

/-- Popping the last vertex clears its position and preserves every
remaining stack index. -/
theorem gm06StackPositions_pop {n absent v : ℕ} (vertices : List ℕ)
    (hv : v < n) (hnot : v ∉ vertices) :
    (gm06StackPositions n absent (vertices ++ [v])).set v absent = gm06StackPositions n absent vertices := by
  rw [gm06StackPositions_append vertices hv hnot, List.set_set]
  apply List.ext_getElem
  · simp only [List.length_set]
  · intro i hi hi'
    by_cases hiv : i = v
    · subst i
      rw [List.getElem_set_self hi]
      simp only [gm06StackPositions, List.getElem_ofFn, hnot, ↓reduceIte]
    · exact List.getElem_set_ne (by omega : v ≠ i) hi

/-- A present stack position is strictly below the absent sentinel. -/
theorem gm06StackPositions_present {n absent v : ℕ} (vertices : List ℕ)
    (hv : v < n) (hlen : vertices.length ≤ absent) (hmem : v ∈ vertices) :
    (gm06StackPositions n absent vertices)[v]?.getD absent = vertices.idxOf v ∧ vertices.idxOf v < absent := by
  exact ⟨by rw [gm06StackPositions_get vertices hv, ite_eq_left hmem],
    (List.idxOf_lt_length_of_mem hmem).trans_le hlen⟩

/-- Every position is either a real stack index or the absent sentinel. -/
theorem gm06StackPositions_words {n absent : ℕ} (vertices : List ℕ) (hlen : vertices.length ≤ absent) :
    ∀ value ∈ gm06StackPositions n absent vertices, value ≤ absent := by
  intro value hv
  obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hv
  split_ifs with hm
  · exact (List.idxOf_lt_length_of_mem hm).le.trans hlen
  · exact le_rfl

/-- The absent sentinel is equivalent to absence from the vertex stack. -/
theorem gm06StackPositions_absent_iff {n absent v : ℕ} (vertices : List ℕ)
    (hv : v < n) (hlen : vertices.length ≤ absent) :
    (gm06StackPositions n absent vertices)[v]?.getD absent = absent ↔ v ∉ vertices := by
  rw [gm06StackPositions_get vertices hv]
  by_cases hmem : v ∈ vertices
  · have hi := (List.idxOf_lt_length_of_mem hmem).trans_le hlen
    simp only [hmem, ↓reduceIte, not_true_eq_false, iff_false]
    omega
  · simp only [hmem, ↓reduceIte, not_false_eq_true]

end GraphMinor.Compute
