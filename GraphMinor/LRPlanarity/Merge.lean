module

public import GraphMinor.LRPlanarity.Trim
public import GraphMinor.LRPlanarity.Aggregation

/-!
# Merging Summaries in Bucket Order (Part I, Section 4 and Part II)

This module proves `MergeStatement` from `GraphMinor/LRPlanarity/Statements.lean`,
following Part I, Section 4 (`MERGE`) and Part II ("Child half of merge",
"Old half of merge", and "List ordering and stack ordering") of
`docs/planarity/planarity_test.tex`.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-! ## `listMaximum`, `Block.maximum`, and `OrderedNodes` -/

theorem listMaximum_gt_iff_of_ordered {l : List ReturnNode} (hord : OrderedNodes l) (b : ℕ) :
    listMaximum l > (b : Int) ↔ ∃ x ∈ l, b < x.depth := by
  rcases l with _ | ⟨x, xs⟩
  · simp [listMaximum]
  · rw [OrderedNodes, List.pairwise_cons] at hord
    simp only [listMaximum, gt_iff_lt, Int.ofNat_lt, List.mem_cons]
    constructor
    · intro hbx
      exact ⟨x, Or.inl rfl, hbx⟩
    · rintro ⟨y, rfl | hy, hby⟩
      · exact hby
      · exact lt_of_lt_of_le hby (hord.1 y hy)

theorem listMaximum_le_iff_of_ordered {l : List ReturnNode} (hord : OrderedNodes l) (b : ℕ) :
    ¬ (listMaximum l > (b : Int)) ↔ ∀ x ∈ l, x.depth ≤ b := by
  rw [listMaximum_gt_iff_of_ordered hord b]
  push Not
  rfl

theorem Block.maximum_gt_iff_of_ordered {q : Block}
    (hordL : OrderedNodes q.left) (hordR : OrderedNodes q.right) (b : ℕ) :
    q.maximum > (b : Int) ↔ ∃ x ∈ q.nodes, b < x.depth := by
  unfold Block.maximum Block.nodes
  rw [gt_iff_lt, lt_max_iff, ← gt_iff_lt, ← gt_iff_lt,
    listMaximum_gt_iff_of_ordered hordL b, listMaximum_gt_iff_of_ordered hordR b]
  constructor
  · rintro (⟨x, hx, hbx⟩ | ⟨x, hx, hbx⟩)
    · exact ⟨x, List.mem_append_left _ hx, hbx⟩
    · exact ⟨x, List.mem_append_right _ hx, hbx⟩
  · rintro ⟨x, hx, hbx⟩
    rcases List.mem_append.mp hx with hxL | hxR
    · exact Or.inl ⟨x, hxL, hbx⟩
    · exact Or.inr ⟨x, hxR, hbx⟩

theorem Block.maximum_le_iff_of_ordered {q : Block}
    (hordL : OrderedNodes q.left) (hordR : OrderedNodes q.right) (b : ℕ) :
    ¬ (q.maximum > (b : Int)) ↔ ∀ x ∈ q.nodes, x.depth ≤ b := by
  rw [Block.maximum_gt_iff_of_ordered hordL hordR b]
  push Not
  rfl

theorem orderedNodes_append {l₁ l₂ : List ReturnNode}
    (h₁ : OrderedNodes l₁) (h₂ : OrderedNodes l₂)
    (h12 : ∀ x ∈ l₁, ∀ y ∈ l₂, y.depth ≤ x.depth) :
    OrderedNodes (l₁ ++ l₂) := by
  unfold OrderedNodes at *
  rw [List.pairwise_append]
  exact ⟨h₁, h₂, h12⟩

theorem orderedNodes_flatMap {α : Type*} {xs : List α} {f : α → List ReturnNode}
    (hord : ∀ a ∈ xs, OrderedNodes (f a))
    (hpair : xs.Pairwise (fun u l => ∀ x ∈ f u, ∀ y ∈ f l, y.depth ≤ x.depth)) :
    OrderedNodes (xs.flatMap f) := by
  induction xs with
  | nil => simp [OrderedNodes]
  | cons a rest ih =>
    rw [List.pairwise_cons] at hpair
    simp only [List.flatMap_cons]
    refine orderedNodes_append (hord a List.mem_cons_self)
      (ih (fun b hb => hord b (List.mem_cons_of_mem a hb)) hpair.2) ?_
    intro x hx y hy
    rw [List.mem_flatMap] at hy
    rcases hy with ⟨b, hb, hyb⟩
    exact hpair.1 b hb x hx y hyb

theorem orderedNodes_of_const_depth {l : List ReturnNode} {d : ℕ}
    (hd : ∀ x ∈ l, x.depth = d) : OrderedNodes l := by
  induction l with
  | nil => simp [OrderedNodes]
  | cons x xs ih =>
    rw [OrderedNodes, List.pairwise_cons]
    refine ⟨fun y hy => ?_, ih (fun y hy => hd y (List.mem_cons_of_mem x hy))⟩
    rw [hd x List.mem_cons_self, hd y (List.mem_cons_of_mem x hy)]

theorem Block.Holds.symm {q : Block} {color : ℕ → Color} (h : q.Holds color) :
    (⟨q.right, q.left⟩ : Block).Holds color :=
  ⟨h.2.1, h.1, fun i hi j hj => (h.2.2 j hj i hi).symm⟩

theorem Block.holds_swap_iff {q : Block} {color : ℕ → Color} :
    (⟨q.right, q.left⟩ : Block).Holds color ↔ q.Holds color :=
  ⟨Block.Holds.symm, Block.Holds.symm⟩

theorem nodeSet_perm {l₁ l₂ : List ReturnNode} (h : l₁.Perm l₂) :
    nodeSet l₁ = nodeSet l₂ := by
  ext i
  simp only [mem_nodeSet_iff, List.mem_map]
  constructor <;> rintro ⟨b, hb, rfl⟩
  · exact ⟨b, h.subset hb, rfl⟩
  · exact ⟨b, h.symm.subset hb, rfl⟩

/-! ## Part II: Child Half of `MERGE` (`mergeChild`) -/

theorem mergeChild_eq_none_iff (blocks : List Block) (acc : List ReturnNode) :
    mergeChild blocks acc = none ↔ ∃ q ∈ blocks, q.left ≠ [] ∧ q.right ≠ [] := by
  induction blocks generalizing acc with
  | nil =>
    simp [mergeChild]
  | cons q rest ih =>
    unfold mergeChild
    by_cases hboth : (!q.left.isEmpty && !q.right.isEmpty) = true
    · simp only [hboth, ↓reduceIte, true_iff, List.mem_cons]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hboth
      exact ⟨q, Or.inl rfl, hboth⟩
    · simp only [hboth, Bool.false_eq_true, ↓reduceIte, ih]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, not_and_or,
        not_not] at hboth
      constructor
      · rintro ⟨r, hr, hrL, hrR⟩
        exact ⟨r, List.mem_cons_of_mem q hr, hrL, hrR⟩
      · rintro ⟨r, hr, hrL, hrR⟩
        rcases List.mem_cons.mp hr with rfl | hr_rest
        · rcases hboth with hL | hR
          · exact absurd hL hrL
          · exact absurd hR hrR
        · exact ⟨r, hr_rest, hrL, hrR⟩

theorem mergeChild_eq_some_iff (blocks : List Block) (acc res : List ReturnNode) :
    mergeChild blocks acc = some res ↔
      (∀ q ∈ blocks, q.left = [] ∨ q.right = []) ∧
      res = acc ++ blocks.flatMap Block.nodes := by
  induction blocks generalizing acc with
  | nil =>
    simp [mergeChild, eq_comm]
  | cons q rest ih =>
    unfold mergeChild
    by_cases hboth : (!q.left.isEmpty && !q.right.isEmpty) = true
    · simp only [hboth, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hboth
      intro hall _
      rcases hall q List.mem_cons_self with hL | hR
      · exact hboth.1 hL
      · exact hboth.2 hR
    · simp only [hboth, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, not_and_or,
        not_not] at hboth
      have hside : (if q.left.isEmpty then q.right else q.left) = q.nodes := by
        rcases hboth with hL | hR
        · simp [Block.nodes, hL]
        · by_cases hL : q.left.isEmpty
          · have hL' : q.left = [] := List.isEmpty_iff.mp hL
            simp [Block.nodes, hL']
          · simp [Block.nodes, hL, hR]
      rw [hside, ih]
      constructor
      · rintro ⟨hrest, rfl⟩
        refine ⟨?_, by simp [List.append_assoc]⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr_rest
        · exact hboth
        · exact hrest r hr_rest
      · rintro ⟨hall, rfl⟩
        exact ⟨fun r hr => hall r (List.mem_cons_of_mem q hr), by simp [List.append_assoc]⟩

theorem Block.holds_iff_monochromatic_of_one_sided {q : Block}
    (hone : q.left = [] ∨ q.right = []) (color : ℕ → Color) :
    q.Holds color ↔ Monochromatic color (nodeSet q.nodes) := by
  rcases hone with hL | hR
  · simp [Block.Holds, Block.nodes, hL]
  · simp [Block.Holds, Block.nodes, hR]

theorem new_filter_eq_of_eq {old new : Summary} (hnew : new.Valid)
    (heq : old.least = new.least) :
    new.nodes.filter (fun b => decide (old.least < b.depth)) =
      new.blocks.flatMap Block.nodes := by
  rcases hnew with ⟨_, hanc_depth, hblocks_valid, _, _⟩
  unfold Summary.nodes
  rw [List.filter_append]
  have hanc_nil : new.anchor.filter (fun b => decide (old.least < b.depth)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    rw [heq, hanc_depth b hb]
    simp
  have hblocks_all : (new.blocks.flatMap Block.nodes).filter
      (fun b => decide (old.least < b.depth)) = new.blocks.flatMap Block.nodes := by
    rw [List.filter_eq_self]
    intro b hb
    rw [List.mem_flatMap] at hb
    rcases hb with ⟨q, hq, hbq⟩
    have hlt := (hblocks_valid q hq).2.2.2 b hbq
    simp [heq, hlt]
  rw [hanc_nil, hblocks_all, List.nil_append]

theorem new_filter_eq_of_lt {old new : Summary} (hnew : new.Valid)
    (hlt : old.least < new.least) :
    new.nodes.filter (fun b => decide (old.least < b.depth)) = new.nodes := by
  rcases hnew with ⟨_, hanc_depth, hblocks_valid, _, _⟩
  rw [List.filter_eq_self]
  intro b hb
  rcases List.mem_append.mp hb with hb_anc | hb_blk
  · have hd := hanc_depth b hb_anc
    simp [hd, hlt]
  · rw [List.mem_flatMap] at hb_blk
    rcases hb_blk with ⟨q, hq, hbq⟩
    have hd := (hblocks_valid q hq).2.2.2 b hbq
    simp [Nat.lt_trans hlt hd]

/-! ## Part II: Old Half of `MERGE` (`mergeOld`) -/

/-- Part I, Section 4: orient a popped old block so any depth `> b` is on the left. -/
def orientBlock (b : ℕ) (q : Block) : Block :=
  if listMaximum q.right > (b : Int) then ⟨q.right, q.left⟩ else q

@[simp]
theorem orientBlock_holds_iff (b : ℕ) (q : Block) (color : ℕ → Color) :
    (orientBlock b q).Holds color ↔ q.Holds color := by
  unfold orientBlock
  split_ifs
  · exact Block.holds_swap_iff
  · rfl

theorem orientBlock_nodes_perm (b : ℕ) (q : Block) :
    (orientBlock b q).nodes.Perm q.nodes := by
  unfold orientBlock Block.nodes
  split_ifs
  · exact List.perm_append_comm
  · exact List.Perm.refl _

theorem orientBlock_mem_nodes_iff (b : ℕ) (q : Block) (x : ReturnNode) :
    x ∈ (orientBlock b q).nodes ↔ x ∈ q.nodes :=
  (orientBlock_nodes_perm b q).mem_iff

theorem orientBlock_ordered (b : ℕ) {q : Block}
    (hL : OrderedNodes q.left) (hR : OrderedNodes q.right) :
    OrderedNodes (orientBlock b q).left ∧ OrderedNodes (orientBlock b q).right := by
  unfold orientBlock
  split_ifs
  · exact ⟨hR, hL⟩
  · exact ⟨hL, hR⟩

theorem orientBlock_left_gt_of_max_gt {b : ℕ} {q : Block}
    (hmax : q.maximum > (b : Int)) :
    listMaximum (orientBlock b q).left > (b : Int) := by
  unfold orientBlock
  split_ifs with hR
  · exact hR
  · unfold Block.maximum at hmax
    rw [gt_iff_lt, lt_max_iff] at hmax
    rcases hmax with hL | hR'
    · exact hL
    · exact absurd hR' hR

theorem orientBlock_right_gt_iff {b : ℕ} {q : Block} :
    listMaximum (orientBlock b q).right > (b : Int) ↔
      listMaximum q.left > (b : Int) ∧ listMaximum q.right > (b : Int) := by
  unfold orientBlock
  split_ifs with hR
  · simp [hR]
  · simp [hR]

theorem mergeOld_cons (b : ℕ) (q : Block) (rest : List Block) (left right : List ReturnNode) :
    mergeOld b (q :: rest) left right =
      if q.maximum > (b : Int) then
        if listMaximum (orientBlock b q).right > (b : Int) then none
        else mergeOld b rest (left ++ (orientBlock b q).left) (right ++ (orientBlock b q).right)
      else some (q :: rest, left, right) := rfl

theorem mergeOld_acc (b : ℕ) (blocks : List Block) (left right : List ReturnNode) :
    mergeOld b blocks left right =
      (mergeOld b blocks [] []).map (fun (rem, L, R) => (rem, left ++ L, right ++ R)) := by
  induction blocks generalizing left right with
  | nil =>
    simp [mergeOld]
  | cons q rest ih =>
    rw [mergeOld_cons, mergeOld_cons]
    split_ifs with hmax hboth
    · rfl
    · rw [ih (left ++ (orientBlock b q).left) (right ++ (orientBlock b q).right)]
      rw [ih ([] ++ (orientBlock b q).left) ([] ++ (orientBlock b q).right)]
      rcases mergeOld b rest [] [] with _ | ⟨rem, L, R⟩
      · rfl
      · simp [List.append_assoc]
    · simp

theorem mergeOld_eq_none_imp {b : ℕ} {blocks : List Block} {left right : List ReturnNode}
    (h : mergeOld b blocks left right = none) :
    ∃ q ∈ blocks, listMaximum q.left > (b : Int) ∧ listMaximum q.right > (b : Int) := by
  induction blocks generalizing left right with
  | nil =>
    simp [mergeOld] at h
  | cons q rest ih =>
    rw [mergeOld_cons] at h
    split_ifs at h with hmax hboth
    · exact ⟨q, List.mem_cons_self, orientBlock_right_gt_iff.mp hboth⟩
    · obtain ⟨r, hr, hL, hR⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem q hr, hL, hR⟩

theorem mergeOld_eq_some {b : ℕ} {blocks rem : List Block} {L R : List ReturnNode}
    (h : mergeOld b blocks [] [] = some (rem, L, R)) :
    ∃ popped : List Block,
      blocks = popped ++ rem ∧
      (∀ q ∈ popped, q.maximum > (b : Int) ∧ ¬ (listMaximum (orientBlock b q).right > (b : Int))) ∧
      L = popped.flatMap (fun q => (orientBlock b q).left) ∧
      R = popped.flatMap (fun q => (orientBlock b q).right) ∧
      (rem = [] ∨ ∃ r₀ rest_rem, rem = r₀ :: rest_rem ∧ ¬ (r₀.maximum > (b : Int))) := by
  induction blocks generalizing rem L R with
  | nil =>
    simp only [mergeOld, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact ⟨[], rfl, by simp, rfl, rfl, Or.inl rfl⟩
  | cons q rest ih =>
    rw [mergeOld_cons] at h
    split_ifs at h with hmax hboth
    · rw [List.nil_append, List.nil_append, mergeOld_acc] at h
      simp only [Option.map_eq_some_iff] at h
      rcases h with ⟨⟨rem', L', R'⟩, hrest, hprod⟩
      simp only [Prod.mk.injEq] at hprod
      rcases hprod with ⟨rfl, rfl, rfl⟩
      obtain ⟨popped, rfl, hpop, rfl, rfl, hrem⟩ := ih hrest
      refine ⟨q :: popped, rfl, ?_, rfl, rfl, hrem⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr_pop
      · exact ⟨hmax, hboth⟩
      · exact hpop r hr_pop
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨[], rfl, by simp, rfl, rfl, Or.inr ⟨q, rest, rfl, hmax⟩⟩

theorem flatMap_orientBlock_perm (b : ℕ) (popped : List Block) :
    (popped.flatMap (fun q => (orientBlock b q).left) ++
      popped.flatMap (fun q => (orientBlock b q).right)).Perm
    (popped.flatMap Block.nodes) := by
  induction popped with
  | nil =>
    exact List.Perm.refl []
  | cons q ps ih =>
    simp only [List.flatMap_cons]
    have hmid :
        (((orientBlock b q).left ++ ps.flatMap (fun r => (orientBlock b r).left)) ++
          ((orientBlock b q).right ++ ps.flatMap (fun r => (orientBlock b r).right))).Perm
        (((orientBlock b q).left ++ (orientBlock b q).right) ++
          (ps.flatMap (fun r => (orientBlock b r).left) ++
            ps.flatMap (fun r => (orientBlock b r).right))) := by
      simp only [List.append_assoc]
      exact List.Perm.append_left (orientBlock b q).left
        (List.perm_append_comm_assoc
          (ps.flatMap (fun r => (orientBlock b r).left))
          (orientBlock b q).right
          (ps.flatMap (fun r => (orientBlock b r).right)))
    exact hmid.trans ((orientBlock_nodes_perm b q).append ih)

/-! ## Proof of `MergeStatement` -/

/-- Part II, child/old halves and list ordering: `MERGE` rejects exactly when
the aggregated formula is unsatisfiable, and otherwise represents it exactly. -/
theorem mergeStatement : MergeStatement := by
  intro old new hold hnew hleast hnodup hUB
  rcases hold with ⟨hold_anc_ne, hold_anc_depth, hold_blk_valid, hold_blk_pair, _⟩
  rcases hnew with ⟨hnew_anc_ne, hnew_anc_depth, hnew_blk_valid, hnew_blk_pair, _⟩
  have hold_valid : old.Valid := ⟨hold_anc_ne, hold_anc_depth, hold_blk_valid, hold_blk_pair,
    (List.nodup_append.mp (List.map_append ▸ hnodup)).1⟩
  have hnew_valid : new.Valid := ⟨hnew_anc_ne, hnew_anc_depth, hnew_blk_valid, hnew_blk_pair,
    (List.nodup_append.mp (List.map_append ▸ hnodup)).2.1⟩
  -- Unfold `merge (some old) (some new)` and split on `mergeChild`
  rcases hchild : mergeChild new.blocks [] with _ | right₀
  · -- Rejection in `mergeChild`: some child block is two-sided
    have hmerge : merge (some old) (some new) = none := by
      simp [merge, hchild]
    rw [hmerge]
    obtain ⟨q, hq, hL_ne, hR_ne⟩ := (mergeChild_eq_none_iff new.blocks []).mp hchild
    rintro ⟨color, _, hnew_holds, hB_mono, _, _, _⟩
    rcases hL : q.left with _ | ⟨xL, xsL⟩
    · exact absurd hL hL_ne
    rcases hR : q.right with _ | ⟨xR, xsR⟩
    · exact absurd hR hR_ne
    have hq_holds : q.Holds color := hnew_holds.2 q hq
    have hxL_in : xL.edge ∈ nodeSet q.left := by simp [hL]
    have hxR_in : xR.edge ∈ nodeSet q.right := by simp [hR]
    have hne_col : color xL.edge ≠ color xR.edge := hq_holds.2.2 xL.edge hxL_in xR.edge hxR_in
    have hxL_nodes : xL ∈ new.nodes := by
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, ?_⟩)
      exact List.mem_append_left _ (by simp [hL])
    have hxR_nodes : xR ∈ new.nodes := by
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, ?_⟩)
      exact List.mem_append_right _ (by simp [hR])
    have hxL_depth : old.least < xL.depth :=
      lt_of_le_of_lt hleast ((hnew_blk_valid q hq).2.2.2 xL (List.mem_append_left _ (by simp [hL])))
    have hxR_depth : old.least < xR.depth :=
      lt_of_le_of_lt hleast ((hnew_blk_valid q hq).2.2.2 xR (List.mem_append_right _ (by simp [hR])))
    have hxL_B : xL.edge ∈ nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth))) := by
      rw [mem_nodeSet_iff, List.mem_map]
      exact ⟨xL, List.mem_filter.mpr ⟨hxL_nodes, decide_eq_true hxL_depth⟩, rfl⟩
    have hxR_B : xR.edge ∈ nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth))) := by
      rw [mem_nodeSet_iff, List.mem_map]
      exact ⟨xR, List.mem_filter.mpr ⟨hxR_nodes, decide_eq_true hxR_depth⟩, rfl⟩
    exact hne_col (hB_mono xL.edge hxL_B xR.edge hxR_B)
  · -- `mergeChild` succeeded with `right₀`
    obtain ⟨hnew_one, hright₀_eq⟩ := (mergeChild_eq_some_iff new.blocks [] right₀).mp hchild
    rw [List.nil_append] at hright₀_eq
    let anchor := if new.least = old.least then old.anchor ++ new.anchor else old.anchor
    let right₁ := if new.least = old.least then right₀ else right₀ ++ new.anchor
    -- Next, split on `mergeOld new.least old.blocks [] []`
    rcases hold_base : mergeOld new.least old.blocks [] [] with _ | ⟨rem, L, R⟩
    · -- Rejection in `mergeOld`: some old block has both sides meeting `> new.least`
      have hold_merge : mergeOld new.least old.blocks [] right₁ = none := by
        rw [mergeOld_acc, hold_base]; rfl
      have hmerge : merge (some old) (some new) = none := by
        simp [merge, hchild, right₁, hold_merge]
      rw [hmerge]
      obtain ⟨q, hq, hL_gt, hR_gt⟩ := mergeOld_eq_none_imp hold_base
      rintro ⟨color, hold_holds, _, _, hU_mono, _, _⟩
      have hq_ordL := (hold_blk_valid q hq).2.1
      have hq_ordR := (hold_blk_valid q hq).2.2.1
      obtain ⟨xL, hxL_mem, hxL_gt⟩ := (listMaximum_gt_iff_of_ordered hq_ordL new.least).mp hL_gt
      obtain ⟨xR, hxR_mem, hxR_gt⟩ := (listMaximum_gt_iff_of_ordered hq_ordR new.least).mp hR_gt
      have hq_holds : q.Holds color := hold_holds.2 q hq
      have hxL_in : xL.edge ∈ nodeSet q.left := by
        rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hxL_mem
      have hxR_in : xR.edge ∈ nodeSet q.right := by
        rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hxR_mem
      have hne_col : color xL.edge ≠ color xR.edge := hq_holds.2.2 xL.edge hxL_in xR.edge hxR_in
      have hxL_old : xL ∈ old.nodes :=
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_left _ hxL_mem⟩)
      have hxR_old : xR ∈ old.nodes :=
        List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, List.mem_append_right _ hxR_mem⟩)
      have hxL_U : xL.edge ∈ nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth))) := by
        rw [mem_nodeSet_iff, List.mem_map]
        exact ⟨xL, List.mem_filter.mpr ⟨hxL_old, decide_eq_true hxL_gt⟩, rfl⟩
      have hxR_U : xR.edge ∈ nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth))) := by
        rw [mem_nodeSet_iff, List.mem_map]
        exact ⟨xR, List.mem_filter.mpr ⟨hxR_old, decide_eq_true hxR_gt⟩, rfl⟩
      exact hne_col (hU_mono xL.edge hxL_U xR.edge hxR_U)
    · -- `mergeOld` succeeded!
      obtain ⟨popped, hold_blocks_eq, hpopped, hL_eq, hR_eq, hrem_stop⟩ :=
        mergeOld_eq_some hold_base
      let blocks' := if L.isEmpty && (right₁ ++ R).isEmpty then rem else ⟨L, right₁ ++ R⟩ :: rem
      let merged : Summary := ⟨old.least, anchor, blocks'⟩
      have hold_merge : mergeOld new.least old.blocks [] right₁ = some (rem, L, right₁ ++ R) := by
        rw [mergeOld_acc, hold_base]; rfl
      have hmerge : merge (some old) (some new) = some (some merged) := by
        simp [merge, hchild, anchor, right₁, hold_merge, blocks', merged]
      rw [hmerge]
      -- Establish key properties of `right₁`, `L`, `R`, `rem`, and `merged`
      have hright₁_filter :
          right₁.Perm (new.nodes.filter (fun b => decide (old.least < b.depth))) := by
        by_cases heq : new.least = old.least
        · simp only [right₁, heq, ↓reduceIte, hright₀_eq]
          rw [new_filter_eq_of_eq hnew_valid heq.symm]
        · have hlt : old.least < new.least := lt_of_le_of_ne hleast (Ne.symm heq)
          simp only [right₁, heq, ↓reduceIte, hright₀_eq]
          rw [new_filter_eq_of_lt hnew_valid hlt]
          exact List.perm_append_comm
      have hB_eq : nodeSet right₁ = nodeSet (new.nodes.filter (fun b => decide (old.least < b.depth))) :=
        nodeSet_perm hright₁_filter
      -- Remaining blocks `rem` have all depths `≤ new.least`
      have hrem_le : ∀ r ∈ rem, ∀ z ∈ r.nodes, z.depth ≤ new.least := by
        rcases hrem_stop with rfl | ⟨r₀, rest_rem, rfl, hr₀_max⟩
        · intro r hr; nomatch hr
        · have hr₀_in : r₀ ∈ old.blocks := by
            rw [hold_blocks_eq]; exact List.mem_append_right _ List.mem_cons_self
          have hr₀_valid := hold_blk_valid r₀ hr₀_in
          have hr₀_le : ∀ x ∈ r₀.nodes, x.depth ≤ new.least :=
            (Block.maximum_le_iff_of_ordered hr₀_valid.2.1 hr₀_valid.2.2.1 new.least).mp hr₀_max
          rcases hr₀_nodes : r₀.nodes with _ | ⟨x₀, _⟩
          · exact absurd hr₀_nodes hr₀_valid.1
          have hx₀_mem : x₀ ∈ r₀.nodes := by rw [hr₀_nodes]; exact List.mem_cons_self
          have hx₀_le : x₀.depth ≤ new.least := hr₀_le x₀ hx₀_mem
          have hpair_rem : (r₀ :: rest_rem).Pairwise
              (fun upper lower => ∀ b ∈ upper.nodes, ∀ c ∈ lower.nodes, c.depth ≤ b.depth) := by
            rw [hold_blocks_eq, List.pairwise_append] at hold_blk_pair
            exact hold_blk_pair.2.1
          rw [List.pairwise_cons] at hpair_rem
          intro r hr z hz
          rcases List.mem_cons.mp hr with rfl | hr_rest
          · exact hr₀_le z hz
          · exact le_trans (hpair_rem.1 r hr_rest x₀ hx₀_mem z hz) hx₀_le
      -- Popped blocks have `(orientBlock new.least q).left` meeting `> new.least` and `.right` `≤ new.least`
      have hpopped_in : ∀ q ∈ popped, q ∈ old.blocks := by
        intro q hq; rw [hold_blocks_eq]; exact List.mem_append_left _ hq
      have hpopped_ord : ∀ q ∈ popped,
          OrderedNodes (orientBlock new.least q).left ∧
          OrderedNodes (orientBlock new.least q).right := by
        intro q hq
        have hv := hold_blk_valid q (hpopped_in q hq)
        exact orientBlock_ordered new.least hv.2.1 hv.2.2.1
      have hpopped_left_gt : ∀ q ∈ popped,
          ∃ x ∈ (orientBlock new.least q).left, new.least < x.depth := by
        intro q hq
        exact (listMaximum_gt_iff_of_ordered (hpopped_ord q hq).1 new.least).mp
          (orientBlock_left_gt_of_max_gt (hpopped q hq).1)
      have hpopped_right_le : ∀ q ∈ popped,
          ∀ y ∈ (orientBlock new.least q).right, y.depth ≤ new.least := by
        intro q hq
        exact (listMaximum_le_iff_of_ordered (hpopped_ord q hq).2 new.least).mp (hpopped q hq).2
      have hR_le : ∀ y ∈ R, y.depth ≤ new.least := by
        intro y hy
        rw [hR_eq, List.mem_flatMap] at hy
        rcases hy with ⟨q, hq, hyq⟩
        exact hpopped_right_le q hq y hyq
      -- Every node in `old.nodes` with depth `> new.least` belongs to `L`
      have hold_gt_mem_L : ∀ x ∈ old.nodes, new.least < x.depth → x ∈ L := by
        intro x hx hgt
        rcases List.mem_append.mp hx with hx_anc | hx_blk
        · have hd := hold_anc_depth x hx_anc
          omega
        · rw [hold_blocks_eq, List.flatMap_append, List.mem_append] at hx_blk
          rcases hx_blk with hx_pop | hx_rem
          · rw [List.mem_flatMap] at hx_pop
            rcases hx_pop with ⟨q, hq, hxq⟩
            rw [← orientBlock_mem_nodes_iff new.least q, Block.nodes, List.mem_append] at hxq
            rcases hxq with hxL | hxR
            · rw [hL_eq, List.mem_flatMap]
              exact ⟨q, hq, hxL⟩
            · have hle := hpopped_right_le q hq x hxR
              omega
          · rw [List.mem_flatMap] at hx_rem
            rcases hx_rem with ⟨r, hr, hxr⟩
            have hle := hrem_le r hr x hxr
            omega
      have hU_sub_L :
          nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth))) ⊆ nodeSet L := by
        intro j hj
        rw [mem_nodeSet_iff, List.mem_map] at hj ⊢
        rcases hj with ⟨x, hx, rfl⟩
        rw [List.mem_filter, decide_eq_true_eq] at hx
        exact ⟨x, hold_gt_mem_L x hx.1 hx.2, rfl⟩
      -- Permutation: `merged.nodes.Perm (old.nodes ++ new.nodes)`
      have hblocks'_flatMap :
          blocks'.flatMap Block.nodes = L ++ (right₁ ++ R) ++ rem.flatMap Block.nodes := by
        unfold blocks'
        split_ifs with hemp
        · simp only [Bool.and_eq_true, List.isEmpty_iff] at hemp
          simp [hemp.1, hemp.2]
        · simp [Block.nodes, List.append_assoc]
      have hLR_perm : (L ++ R).Perm (popped.flatMap Block.nodes) := by
        rw [hL_eq, hR_eq]
        exact flatMap_orientBlock_perm new.least popped
      have hanc_right₁_perm : (anchor ++ right₁).Perm (old.anchor ++ new.nodes) := by
        by_cases heq : new.least = old.least
        · simp only [anchor, right₁, heq, ↓reduceIte, hright₀_eq, Summary.nodes, List.append_assoc]
          exact List.Perm.refl _
        · simp only [anchor, right₁, heq, ↓reduceIte, hright₀_eq, Summary.nodes]
          exact List.Perm.append_left old.anchor List.perm_append_comm
      have hmerged_perm : merged.nodes.Perm (old.nodes ++ new.nodes) := by
        unfold Summary.nodes
        dsimp [merged]
        rw [hblocks'_flatMap]
        -- Rearrange `anchor ++ (L ++ (right₁ ++ R) ++ rem.flatMap Block.nodes)`
        -- to `(anchor ++ right₁) ++ ((L ++ R) ++ rem.flatMap Block.nodes)`
        have hrearr :
            (anchor ++ (L ++ (right₁ ++ R) ++ rem.flatMap Block.nodes)).Perm
            ((anchor ++ right₁) ++ ((L ++ R) ++ rem.flatMap Block.nodes)) := by
          simp only [List.append_assoc]
          refine List.Perm.append_left anchor ?_
          have h1 : (L ++ (right₁ ++ (R ++ rem.flatMap Block.nodes))).Perm
              (right₁ ++ (L ++ (R ++ rem.flatMap Block.nodes))) :=
            List.perm_append_comm_assoc L right₁ (R ++ rem.flatMap Block.nodes)
          simpa [List.append_assoc] using h1
        have hold_blk_perm :
            ((L ++ R) ++ rem.flatMap Block.nodes).Perm (old.blocks.flatMap Block.nodes) := by
          rw [hold_blocks_eq, List.flatMap_append]
          exact hLR_perm.append_right (rem.flatMap Block.nodes)
        have hstep := hrearr.trans (hanc_right₁_perm.append hold_blk_perm)
        -- Now `(old.anchor ++ new.nodes) ++ old.blocks.flatMap Block.nodes`
        -- is a permutation of `(old.anchor ++ old.blocks.flatMap Block.nodes) ++ new.nodes`
        refine hstep.trans ?_
        simp only [List.append_assoc]
        exact List.Perm.append_left old.anchor List.perm_append_comm
      refine ⟨?_, ?_, nodeSet_perm hmerged_perm⟩
      · -- 1. Formula equivalence: `∀ color, SummaryFormula (some merged) color ↔ MergeFormula old new color`
        intro color
        dsimp [SummaryFormula, Summary.Holds, merged, MergeFormula]
        rw [← hB_eq]
        let B := nodeSet right₁
        let U := nodeSet (old.nodes.filter (fun b => decide (new.least < b.depth)))
        -- Express `∀ b ∈ blocks', b.Holds color` uniformly
        have hblocks'_holds :
            (∀ b ∈ blocks', b.Holds color) ↔
              (⟨L, right₁ ++ R⟩ : Block).Holds color ∧ (∀ r ∈ rem, r.Holds color) := by
          unfold blocks'
          split_ifs with hemp
          · simp only [Bool.and_eq_true, List.isEmpty_iff] at hemp
            simp [Block.Holds, hemp.1, hemp.2]
          · simp
        rw [hblocks'_holds]
        constructor
        · -- `merged.Holds color → MergeFormula old new color`
          rintro ⟨hanc_mono, ⟨hL_mono, hR_mono, hLR_opp⟩, hrem_holds⟩
          rw [nodeSet_append] at hR_mono hLR_opp
          have hB_mono : Monochromatic color B :=
            hR_mono.subset Set.subset_union_left
          have hU_mono : Monochromatic color U :=
            hL_mono.subset hU_sub_L
          have hBU_opp : ∀ i ∈ B, ∀ j ∈ U, color i ≠ color j := by
            intro i hi j hj
            exact (hLR_opp j (hU_sub_L hj) i (Or.inl hi)).symm
          have hold_anc_mono : Monochromatic color (nodeSet old.anchor) := by
            by_cases heq : new.least = old.least
            · simp only [anchor, heq, ↓reduceIte, nodeSet_append] at hanc_mono
              exact hanc_mono.subset Set.subset_union_left
            · simp only [anchor, heq, ↓reduceIte] at hanc_mono
              exact hanc_mono
          have hnew_anc_mono : Monochromatic color (nodeSet new.anchor) := by
            by_cases heq : new.least = old.least
            · simp only [anchor, heq, ↓reduceIte, nodeSet_append] at hanc_mono
              exact hanc_mono.subset Set.subset_union_right
            · have hsub : nodeSet new.anchor ⊆ B := by
                simp only [B, right₁, heq, ↓reduceIte, nodeSet_append]
                exact Set.subset_union_right
              exact hB_mono.subset hsub
          have hnew_blk_holds : ∀ q ∈ new.blocks, q.Holds color := by
            intro q hq
            rw [Block.holds_iff_monochromatic_of_one_sided (hnew_one q hq)]
            refine hB_mono.subset ?_
            have hsub0 : nodeSet q.nodes ⊆ nodeSet right₀ := by
              intro i hi
              rw [hright₀_eq]
              rw [mem_nodeSet_iff, List.mem_map] at hi ⊢
              rcases hi with ⟨x, hx, rfl⟩
              exact ⟨x, List.mem_flatMap.mpr ⟨q, hq, hx⟩, rfl⟩
            by_cases heq : new.least = old.least
            · simpa [B, right₁, heq] using hsub0
            · simp only [B, right₁, heq, ↓reduceIte, nodeSet_append]
              exact hsub0.trans Set.subset_union_left
          have hold_blk_holds : ∀ q ∈ old.blocks, q.Holds color := by
            intro q hq
            rw [hold_blocks_eq, List.mem_append] at hq
            rcases hq with hq_pop | hq_rem
            · rw [← orientBlock_holds_iff new.least q color]
              have hsubL : nodeSet (orientBlock new.least q).left ⊆ nodeSet L := by
                intro i hi
                rw [hL_eq]
                rw [mem_nodeSet_iff, List.mem_map] at hi ⊢
                rcases hi with ⟨x, hx, rfl⟩
                exact ⟨x, List.mem_flatMap.mpr ⟨q, hq_pop, hx⟩, rfl⟩
              have hsubR : nodeSet (orientBlock new.least q).right ⊆ B ∪ nodeSet R := by
                intro i hi
                right
                rw [hR_eq]
                rw [mem_nodeSet_iff, List.mem_map] at hi ⊢
                rcases hi with ⟨x, hx, rfl⟩
                exact ⟨x, List.mem_flatMap.mpr ⟨q, hq_pop, hx⟩, rfl⟩
              refine ⟨hL_mono.subset hsubL, hR_mono.subset hsubR, ?_⟩
              intro i hi j hj
              exact hLR_opp i (hsubL hi) j (hsubR hj)
            · exact hrem_holds q hq_rem
          refine ⟨⟨hold_anc_mono, hold_blk_holds⟩, ⟨hnew_anc_mono, hnew_blk_holds⟩,
            hB_mono, hU_mono, hBU_opp, ?_⟩
          intro heq
          simpa [anchor, heq.symm] using hanc_mono
        · -- `MergeFormula old new color → merged.Holds color`
          rintro ⟨⟨hold_anc_mono, hold_blk_holds⟩, ⟨_, _⟩, hB_mono, hU_mono, hBU_opp, hanc_eq⟩
          have hanc_mono : Monochromatic color (nodeSet anchor) := by
            by_cases heq : new.least = old.least
            · simpa [anchor, heq] using hanc_eq heq.symm
            · simpa [anchor, heq] using hold_anc_mono
          have hrem_holds : ∀ r ∈ rem, r.Holds color := by
            intro r hr
            refine hold_blk_holds r ?_
            rw [hold_blocks_eq]
            exact List.mem_append_right _ hr
          refine ⟨hanc_mono, ?_, hrem_holds⟩
          rcases hpop_cases : popped with _ | ⟨q₀, ps⟩
          · -- No old blocks were popped: `L = []` and `R = []`
            have hL_nil : L = [] := by simp [hL_eq, hpop_cases]
            have hR_nil : R = [] := by simp [hR_eq, hpop_cases]
            simp [Block.Holds, hL_nil, hR_nil, hB_mono]
          · -- At least one old block `q₀` was popped
            have hq₀_pop : q₀ ∈ popped := by rw [hpop_cases]; exact List.mem_cons_self
            obtain ⟨x₀, hx₀_mem, hx₀_gt⟩ := hpopped_left_gt q₀ hq₀_pop
            have hx₀_old : x₀ ∈ old.nodes := by
              refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨q₀, hpopped_in q₀ hq₀_pop, ?_⟩)
              rw [← orientBlock_mem_nodes_iff new.least q₀]
              exact List.mem_append_left _ hx₀_mem
            have hx₀_U : x₀.edge ∈ U := by
              dsimp [U]
              rw [mem_nodeSet_iff, List.mem_map]
              exact ⟨x₀, List.mem_filter.mpr ⟨hx₀_old, decide_eq_true hx₀_gt⟩, rfl⟩
            obtain ⟨y₀, hy₀_new, hy₀_gt⟩ := hUB ⟨x₀, hx₀_old, hx₀_gt⟩
            have hy₀_B : y₀.edge ∈ B := by
              dsimp [B]
              rw [hB_eq, mem_nodeSet_iff, List.mem_map]
              exact ⟨y₀, List.mem_filter.mpr ⟨hy₀_new, decide_eq_true hy₀_gt⟩, rfl⟩
            -- Every `j ∈ nodeSet L` has color `color x₀.edge`
            have hL_color : ∀ j ∈ nodeSet L, color j = color x₀.edge := by
              intro j hj
              rw [hL_eq, mem_nodeSet_iff, List.mem_map] at hj
              rcases hj with ⟨x, hx, rfl⟩
              rw [List.mem_flatMap] at hx
              rcases hx with ⟨q, hq, hxq⟩
              obtain ⟨u_q, hu_q_mem, hu_q_gt⟩ := hpopped_left_gt q hq
              have hu_q_old : u_q ∈ old.nodes := by
                refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hpopped_in q hq, ?_⟩)
                rw [← orientBlock_mem_nodes_iff new.least q]
                exact List.mem_append_left _ hu_q_mem
              have hu_q_U : u_q.edge ∈ U := by
                dsimp [U]
                rw [mem_nodeSet_iff, List.mem_map]
                exact ⟨u_q, List.mem_filter.mpr ⟨hu_q_old, decide_eq_true hu_q_gt⟩, rfl⟩
              have hq'_holds : (orientBlock new.least q).Holds color :=
                (orientBlock_holds_iff new.least q color).mpr (hold_blk_holds q (hpopped_in q hq))
              have hx_in : x.edge ∈ nodeSet (orientBlock new.least q).left := by
                rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hxq
              have hu_in : u_q.edge ∈ nodeSet (orientBlock new.least q).left := by
                rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hu_q_mem
              exact (hq'_holds.1 x.edge hx_in u_q.edge hu_in).trans
                (hU_mono u_q.edge hu_q_U x₀.edge hx₀_U)
            -- Every `i ∈ B ∪ nodeSet R` has color `color y₀.edge`
            have hBR_color : ∀ i ∈ nodeSet (right₁ ++ R), color i = color y₀.edge := by
              intro i hi
              rw [nodeSet_append] at hi
              rcases hi with hi_B | hi_R
              · exact hB_mono i hi_B y₀.edge hy₀_B
              · rw [hR_eq, mem_nodeSet_iff, List.mem_map] at hi_R
                rcases hi_R with ⟨y, hy, rfl⟩
                rw [List.mem_flatMap] at hy
                rcases hy with ⟨q, hq, hyq⟩
                obtain ⟨u_q, hu_q_mem, hu_q_gt⟩ := hpopped_left_gt q hq
                have hu_q_L : u_q.edge ∈ nodeSet L := by
                  rw [hL_eq, mem_nodeSet_iff, List.mem_map]
                  exact ⟨u_q, List.mem_flatMap.mpr ⟨q, hq, hu_q_mem⟩, rfl⟩
                have hu_col : color u_q.edge = color x₀.edge := hL_color u_q.edge hu_q_L
                have hq'_holds : (orientBlock new.least q).Holds color :=
                  (orientBlock_holds_iff new.least q color).mpr (hold_blk_holds q (hpopped_in q hq))
                have hu_in : u_q.edge ∈ nodeSet (orientBlock new.least q).left := by
                  rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hu_q_mem
                have hy_in : y.edge ∈ nodeSet (orientBlock new.least q).right := by
                  rw [mem_nodeSet_iff]; exact List.mem_map_of_mem hyq
                have hne1 : color x₀.edge ≠ color y.edge :=
                  hu_col ▸ hq'_holds.2.2 u_q.edge hu_in y.edge hy_in
                have hne2 : color x₀.edge ≠ color y₀.edge :=
                  Ne.symm (hBU_opp y₀.edge hy₀_B x₀.edge hx₀_U)
                exact Color.eq_of_ne_of_ne hne1 hne2
            refine ⟨?_, ?_, ?_⟩
            · intro j₁ hj₁ j₂ hj₂
              rw [hL_color j₁ hj₁, hL_color j₂ hj₂]
            · intro i₁ hi₁ i₂ hi₂
              rw [hBR_color i₁ hi₁, hBR_color i₂ hi₂]
            · intro j hj i hi
              rw [hL_color j hj, hBR_color i hi]
              exact Ne.symm (hBU_opp y₀.edge hy₀_B x₀.edge hx₀_U)
      · -- 2. Validity: `∀ s, some merged = some s → s.Valid`
        intro s hs
        injection hs with hs_eq
        subst hs_eq
        have hpair_split := hold_blk_pair
        rw [hold_blocks_eq, List.pairwise_append] at hpair_split
        rcases hpair_split with ⟨hpair_pop, hpair_rem, hpop_above_rem⟩
        -- Prove `OrderedNodes L` and `OrderedNodes (right₁ ++ R)`
        have hord_L : OrderedNodes L := by
          rw [hL_eq]
          refine orderedNodes_flatMap (fun q hq => (hpopped_ord q hq).1) ?_
          refine hpair_pop.imp_of_mem ?_
          intro u l _ _ h_ul x hx y hy
          have hxu : x ∈ u.nodes :=
            (orientBlock_mem_nodes_iff new.least u x).mp (List.mem_append_left _ hx)
          have hyl : y ∈ l.nodes :=
            (orientBlock_mem_nodes_iff new.least l y).mp (List.mem_append_left _ hy)
          exact h_ul x hxu y hyl
        have hord_R : OrderedNodes R := by
          rw [hR_eq]
          refine orderedNodes_flatMap (fun q hq => (hpopped_ord q hq).2) ?_
          refine hpair_pop.imp_of_mem ?_
          intro u l _ _ h_ul x hx y hy
          have hxu : x ∈ u.nodes :=
            (orientBlock_mem_nodes_iff new.least u x).mp (List.mem_append_right _ hx)
          have hyl : y ∈ l.nodes :=
            (orientBlock_mem_nodes_iff new.least l y).mp (List.mem_append_right _ hy)
          exact h_ul x hxu y hyl
        have hord_right₀ : OrderedNodes right₀ := by
          rw [hright₀_eq]
          refine orderedNodes_flatMap ?_ hnew_blk_pair
          intro q hq
          rcases hnew_one q hq with hL | hR
          · simpa [Block.nodes, hL] using (hnew_blk_valid q hq).2.2.1
          · simpa [Block.nodes, hR] using (hnew_blk_valid q hq).2.1
        have hright₀_ge : ∀ x ∈ right₀, new.least ≤ x.depth := by
          intro x hx
          rw [hright₀_eq, List.mem_flatMap] at hx
          rcases hx with ⟨q, hq, hxq⟩
          exact le_of_lt ((hnew_blk_valid q hq).2.2.2 x hxq)
        have hord_right₁ : OrderedNodes right₁ := by
          by_cases heq : new.least = old.least
          · simpa [right₁, heq] using hord_right₀
          · simp only [right₁, heq, ↓reduceIte]
            refine orderedNodes_append hord_right₀
              (orderedNodes_of_const_depth hnew_anc_depth) ?_
            intro x hx y hy
            rw [hnew_anc_depth y hy]
            exact hright₀_ge x hx
        have hright₁_ge : ∀ x ∈ right₁, new.least ≤ x.depth := by
          intro x hx
          by_cases heq : new.least = old.least
          · simp only [right₁, heq, ↓reduceIte] at hx
            exact hright₀_ge x hx
          · simp only [right₁, heq, ↓reduceIte, List.mem_append] at hx
            rcases hx with hx₀ | hx_anc
            · exact hright₀_ge x hx₀
            · rw [hnew_anc_depth x hx_anc]
        have hord_right₁_R : OrderedNodes (right₁ ++ R) :=
          orderedNodes_append hord_right₁ hord_R
            (fun x hx y hy => le_trans (hR_le y hy) (hright₁_ge x hx))
        -- Depth bound `> old.least` for `L ++ (right₁ ++ R)`
        have htop_gt : ∀ b ∈ L ++ (right₁ ++ R), old.least < b.depth := by
          intro b hb
          rcases List.mem_append.mp hb with hb_L | hb_rR
          · rw [hL_eq, List.mem_flatMap] at hb_L
            rcases hb_L with ⟨q, hq, hbq⟩
            have hbq_nodes : b ∈ q.nodes :=
              (orientBlock_mem_nodes_iff new.least q b).mp (List.mem_append_left _ hbq)
            exact (hold_blk_valid q (hpopped_in q hq)).2.2.2 b hbq_nodes
          · rcases List.mem_append.mp hb_rR with hb_r₁ | hb_R
            · have hb_filt := hright₁_filter.subset hb_r₁
              rw [List.mem_filter, decide_eq_true_eq] at hb_filt
              exact hb_filt.2
            · rw [hR_eq, List.mem_flatMap] at hb_R
              rcases hb_R with ⟨q, hq, hbq⟩
              have hbq_nodes : b ∈ q.nodes :=
                (orientBlock_mem_nodes_iff new.least q b).mp (List.mem_append_right _ hbq)
              exact (hold_blk_valid q (hpopped_in q hq)).2.2.2 b hbq_nodes
        -- Top block is above `rem`
        have htop_above_rem :
            ∀ r ∈ rem, ∀ b ∈ L ++ (right₁ ++ R), ∀ c ∈ r.nodes, c.depth ≤ b.depth := by
          intro r hr b hb c hc
          rcases List.mem_append.mp hb with hb_L | hb_rR
          · rw [hL_eq, List.mem_flatMap] at hb_L
            rcases hb_L with ⟨q, hq, hbq⟩
            have hbq_nodes : b ∈ q.nodes :=
              (orientBlock_mem_nodes_iff new.least q b).mp (List.mem_append_left _ hbq)
            exact hpop_above_rem q hq r hr b hbq_nodes c hc
          · rcases List.mem_append.mp hb_rR with hb_r₁ | hb_R
            · exact le_trans (hrem_le r hr c hc) (hright₁_ge b hb_r₁)
            · rw [hR_eq, List.mem_flatMap] at hb_R
              rcases hb_R with ⟨q, hq, hbq⟩
              have hbq_nodes : b ∈ q.nodes :=
                (orientBlock_mem_nodes_iff new.least q b).mp (List.mem_append_right _ hbq)
              exact hpop_above_rem q hq r hr b hbq_nodes c hc
        dsimp [Summary.Valid, merged]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · -- `anchor ≠ []`
          by_cases heq : new.least = old.least
          · simp [anchor, heq, hold_anc_ne]
          · simp [anchor, heq, hold_anc_ne]
        · -- `∀ b ∈ anchor, b.depth = old.least`
          intro b hb
          by_cases heq : new.least = old.least
          · simp only [anchor, heq, ↓reduceIte, List.mem_append] at hb
            rcases hb with hb_old | hb_new
            · exact hold_anc_depth b hb_old
            · exact (hnew_anc_depth b hb_new).trans heq
          · simp only [anchor, heq, ↓reduceIte] at hb
            exact hold_anc_depth b hb
        · -- Block validity for `blocks'`
          intro q hq
          unfold blocks' at hq
          split_ifs at hq with hemp
          · exact hold_blk_valid q (by rw [hold_blocks_eq]; exact List.mem_append_right _ hq)
          · rcases List.mem_cons.mp hq with rfl | hq_rem
            · refine ⟨?_, hord_L, hord_right₁_R, htop_gt⟩
              simp only [Bool.and_eq_true, List.isEmpty_iff, not_and_or] at hemp
              rcases hemp with hL_ne | hR_ne
              · simp [Block.nodes, hL_ne]
              · simp [Block.nodes, hR_ne]
            · exact hold_blk_valid q (by rw [hold_blocks_eq]; exact List.mem_append_right _ hq_rem)
        · -- Pairwise stack ordering for `blocks'`
          unfold blocks'
          split_ifs with hemp
          · exact hpair_rem
          · rw [List.pairwise_cons]
            exact ⟨htop_above_rem, hpair_rem⟩
        · -- `Nodup` of `merged.nodes.map ReturnNode.edge`
          exact (hmerged_perm.map ReturnNode.edge).nodup_iff.mpr hnodup

end GraphMinor.LRPlanarity
