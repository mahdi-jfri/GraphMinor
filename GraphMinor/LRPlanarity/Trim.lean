module

public import GraphMinor.LRPlanarity.Statements

/-!
# Trimming Summaries at the Parent Depth (Part I, Section 5 and Part II)

This module proves `TrimStatement` from `GraphMinor/LRPlanarity/Statements.lean`,
following Part I, Section 5 (`TRIM`) and Part II ("Trim at the parent") of
`docs/planarity/planarity_test.tex`.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-! ## Basic Lemmas on `nodeSet`, `Monochromatic`, and `Nodup` -/

@[simp]
theorem mem_nodeSet_iff {nodes : List ReturnNode} {i : ℕ} :
    i ∈ nodeSet nodes ↔ i ∈ nodes.map ReturnNode.edge := by
  simp [nodeSet]

@[simp]
theorem nodeSet_nil : nodeSet [] = ∅ := by
  ext i; simp

@[simp]
theorem nodeSet_cons (b : ReturnNode) (l : List ReturnNode) :
    nodeSet (b :: l) = insert b.edge (nodeSet l) := by
  ext i; simp

@[simp]
theorem nodeSet_append (l₁ l₂ : List ReturnNode) :
    nodeSet (l₁ ++ l₂) = nodeSet l₁ ∪ nodeSet l₂ := by
  ext i; simp

theorem disjoint_nodeSet_of_nodup {l₁ l₂ : List ReturnNode}
    (h : ((l₁ ++ l₂).map ReturnNode.edge).Nodup) :
    Disjoint (nodeSet l₁) (nodeSet l₂) := by
  rw [List.map_append, List.nodup_append] at h
  rw [Set.disjoint_left]
  intro i hi1 hi2
  rw [mem_nodeSet_iff] at hi1 hi2
  exact h.2.2 i hi1 i hi2 rfl

theorem Monochromatic.congr_on {α : Type*} {c₁ c₂ : α → Color} {s : Set α}
    (h : Monochromatic c₁ s) (heq : ∀ x ∈ s, c₁ x = c₂ x) :
    Monochromatic c₂ s := by
  intro x hx y hy
  rw [← heq x hx, ← heq y hy]
  exact h x hx y hy

theorem Monochromatic.subset {α : Type*} {c : α → Color} {s t : Set α}
    (h : Monochromatic c t) (hst : s ⊆ t) :
    Monochromatic c s :=
  fun x hx y hy => h x (hst hx) y (hst hy)

@[simp]
theorem Monochromatic.empty {α : Type*} (c : α → Color) :
    Monochromatic c (∅ : Set α) := by
  intro x hx; simp at hx

theorem Block.Holds.congr_on {q : Block} {c₁ c₂ : ℕ → Color}
    (h : q.Holds c₁) (heq : ∀ i ∈ nodeSet q.nodes, c₁ i = c₂ i) :
    q.Holds c₂ := by
  have heqL : ∀ i ∈ nodeSet q.left, c₁ i = c₂ i :=
    fun i hi => heq i (by simp [Block.nodes, hi])
  have heqR : ∀ i ∈ nodeSet q.right, c₁ i = c₂ i :=
    fun i hi => heq i (by simp [Block.nodes, hi])
  refine ⟨h.1.congr_on heqL, h.2.1.congr_on heqR, ?_⟩
  intro i hi j hj
  rw [← heqL i hi, ← heqR j hj]
  exact h.2.2 i hi j hj

/-! ## Ordering, `listMinimum`, and `Block.minimum` -/

theorem listMinimum_mem_of_ne_nil {l : List ReturnNode} (hl : l ≠ []) :
    ∃ b ∈ l, b.depth = listMinimum l := by
  refine ⟨l.getLast hl, List.getLast_mem hl, ?_⟩
  unfold listMinimum
  rw [List.getLast?_eq_some_getLast hl]
  rfl

theorem listMinimum_le_of_ordered {l : List ReturnNode} (hord : OrderedNodes l)
    {b : ReturnNode} (hb : b ∈ l) :
    listMinimum l ≤ b.depth := by
  induction l with
  | nil => simp at hb
  | cons x xs ih =>
    rw [OrderedNodes, List.pairwise_cons] at hord
    rcases xs with _ | ⟨y, ys⟩
    · simp only [List.mem_singleton] at hb
      subst hb
      simp [listMinimum]
    · have hne : y :: ys ≠ [] := List.cons_ne_nil y ys
      have hmin_eq : listMinimum (x :: y :: ys) = listMinimum (y :: ys) := by
        unfold listMinimum
        rw [List.getLast?_cons_cons]
      rw [hmin_eq]
      rcases List.mem_cons.mp hb with rfl | hb_xs
      · obtain ⟨z, hz_mem, hz_eq⟩ := listMinimum_mem_of_ne_nil hne
        rw [← hz_eq]
        exact hord.1 z hz_mem
      · exact ih hord.2 hb_xs

theorem Block.minimum_mem {q : Block} (hne : q.nodes ≠ []) :
    ∃ b ∈ q.nodes, b.depth = q.minimum := by
  unfold Block.minimum Block.nodes
  by_cases hL : q.left.isEmpty
  · simp only [hL, ↓reduceIte]
    have hL_nil : q.left = [] := List.isEmpty_iff.mp hL
    have hR_ne : q.right ≠ [] := by
      intro hR; apply hne; simp [Block.nodes, hL_nil, hR]
    obtain ⟨b, hb, hd⟩ := listMinimum_mem_of_ne_nil hR_ne
    exact ⟨b, List.mem_append_right _ hb, hd⟩
  · simp only [hL, Bool.false_eq_true, ↓reduceIte]
    have hL_ne : q.left ≠ [] := fun h => hL (List.isEmpty_iff.mpr h)
    by_cases hR : q.right.isEmpty
    · simp only [hR, ↓reduceIte]
      obtain ⟨b, hb, hd⟩ := listMinimum_mem_of_ne_nil hL_ne
      exact ⟨b, List.mem_append_left _ hb, hd⟩
    · simp only [hR, Bool.false_eq_true, ↓reduceIte]
      have hR_ne : q.right ≠ [] := fun h => hR (List.isEmpty_iff.mpr h)
      obtain ⟨b₁, hb₁, hd₁⟩ := listMinimum_mem_of_ne_nil hL_ne
      obtain ⟨b₂, hb₂, hd₂⟩ := listMinimum_mem_of_ne_nil hR_ne
      rcases min_choice (listMinimum q.left) (listMinimum q.right) with hmin | hmin
      · exact ⟨b₁, List.mem_append_left _ hb₁, hd₁.trans hmin.symm⟩
      · exact ⟨b₂, List.mem_append_right _ hb₂, hd₂.trans hmin.symm⟩

theorem Block.minimum_le {q : Block} (hordL : OrderedNodes q.left) (hordR : OrderedNodes q.right)
    {b : ReturnNode} (hb : b ∈ q.nodes) :
    q.minimum ≤ b.depth := by
  unfold Block.minimum
  rcases List.mem_append.mp hb with hbL | hbR
  · have hL_ne : q.left.isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hbL)
    simp only [hL_ne, Bool.false_eq_true, ↓reduceIte]
    have hle := listMinimum_le_of_ordered hordL hbL
    split_ifs
    · exact hle
    · exact le_trans (Nat.min_le_left _ _) hle
  · have hR_ne : q.right.isEmpty = false :=
      List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hbR)
    simp only [hR_ne, Bool.false_eq_true, ↓reduceIte]
    have hle := listMinimum_le_of_ordered hordR hbR
    split_ifs with hL
    · exact hle
    · exact le_trans (Nat.min_le_right _ _) hle

/-! ## Prefix Deletion (`dropWhile`) and `trimBlocks` -/

theorem dropWhile_eq_filter_of_ordered {l : List ReturnNode} {c : ℕ}
    (hord : OrderedNodes l) (hle : ∀ b ∈ l, b.depth ≤ c) :
    l.dropWhile (fun b => b.depth == c) = l.filter (fun b => decide (b.depth < c)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [OrderedNodes, List.pairwise_cons] at hord
    have hx_le : x.depth ≤ c := hle x List.mem_cons_self
    have hxs_le : ∀ b ∈ xs, b.depth ≤ c := fun b hb => hle b (List.mem_cons_of_mem x hb)
    simp only [List.dropWhile_cons, List.filter_cons]
    by_cases hxc : x.depth = c
    · have hbeq : (x.depth == c) = true := beq_iff_eq.mpr hxc
      have hlt : decide (x.depth < c) = false := decide_eq_false (by omega)
      rw [hbeq, hlt]
      simp only [↓reduceIte]
      exact ih hord.2 hxs_le
    · have hbeq : (x.depth == c) = false := beq_eq_false_iff_ne.mpr hxc
      have hx_lt : x.depth < c := Nat.lt_of_le_of_ne hx_le hxc
      have hlt : decide (x.depth < c) = true := decide_eq_true hx_lt
      rw [hbeq, hlt]
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      symm
      rw [List.filter_eq_self]
      intro y hy
      rw [decide_eq_true_eq]
      exact lt_of_le_of_lt (hord.1 y hy) hx_lt

theorem filter_lt_eq_self_of_lt {l : List ReturnNode} {c : ℕ}
    (hlt : ∀ b ∈ l, b.depth < c) :
    l.filter (fun b => decide (b.depth < c)) = l := by
  rw [List.filter_eq_self]
  intro b hb
  exact decide_eq_true (hlt b hb)

theorem filter_lt_eq_nil_of_eq {l : List ReturnNode} {c : ℕ}
    (heq : ∀ b ∈ l, b.depth = c) :
    l.filter (fun b => decide (b.depth < c)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro b hb
  simp [heq b hb]

/-- Characterization of `trimBlocks` on a valid stack of blocks with all depths `≤ c`. -/
theorem trimBlocks_spec {blocks : List Block} {least c : ℕ}
    (hblocks : ∀ q ∈ blocks, q.nodes ≠ [] ∧ OrderedNodes q.left ∧ OrderedNodes q.right ∧
      ∀ b ∈ q.nodes, least < b.depth)
    (hpair : blocks.Pairwise (fun upper lower =>
      ∀ b ∈ upper.nodes, ∀ d ∈ lower.nodes, d.depth ≤ b.depth))
    (hle : ∀ q ∈ blocks, ∀ b ∈ q.nodes, b.depth ≤ c) :
    (trimBlocks c blocks).flatMap Block.nodes =
      (blocks.flatMap Block.nodes).filter (fun b => decide (b.depth < c)) ∧
    (∀ q' ∈ trimBlocks c blocks, q'.nodes ≠ [] ∧ OrderedNodes q'.left ∧ OrderedNodes q'.right ∧
      ∀ b ∈ q'.nodes, least < b.depth) ∧
    (trimBlocks c blocks).Pairwise (fun upper lower =>
      ∀ b ∈ upper.nodes, ∀ d ∈ lower.nodes, d.depth ≤ b.depth) ∧
    (∀ q ∈ blocks,
      (⟨q.left.filter (fun b => decide (b.depth < c)),
        q.right.filter (fun b => decide (b.depth < c))⟩ : Block) ∈ trimBlocks c blocks ∨
      (q.left.filter (fun b => decide (b.depth < c)) = [] ∧
        q.right.filter (fun b => decide (b.depth < c)) = [])) := by
  induction blocks with
  | nil =>
    simp [trimBlocks]
  | cons q rest ih =>
    rw [List.pairwise_cons] at hpair
    have hq := hblocks q List.mem_cons_self
    have hrest_blocks : ∀ r ∈ rest, r.nodes ≠ [] ∧ OrderedNodes r.left ∧ OrderedNodes r.right ∧
        ∀ b ∈ r.nodes, least < b.depth :=
      fun r hr => hblocks r (List.mem_cons_of_mem q hr)
    have hq_le : ∀ b ∈ q.nodes, b.depth ≤ c := hle q List.mem_cons_self
    have hrest_le : ∀ r ∈ rest, ∀ b ∈ r.nodes, b.depth ≤ c :=
      fun r hr => hle r (List.mem_cons_of_mem q hr)
    unfold trimBlocks
    by_cases hmin : q.minimum = c
    · simp only [hmin, ↓reduceIte]
      have hq_all_c : ∀ b ∈ q.nodes, b.depth = c := by
        intro b hb
        have h1 : c ≤ b.depth := hmin ▸ q.minimum_le hq.2.1 hq.2.2.1 hb
        have h2 : b.depth ≤ c := hq_le b hb
        omega
      have hqL_nil : q.left.filter (fun b => decide (b.depth < c)) = [] :=
        filter_lt_eq_nil_of_eq (fun b hb => hq_all_c b (List.mem_append_left _ hb))
      have hqR_nil : q.right.filter (fun b => decide (b.depth < c)) = [] :=
        filter_lt_eq_nil_of_eq (fun b hb => hq_all_c b (List.mem_append_right _ hb))
      have hq_nodes_nil : q.nodes.filter (fun b => decide (b.depth < c)) = [] := by
        simp [Block.nodes, List.filter_append, hqL_nil, hqR_nil]
      obtain ⟨ih_flat, ih_valid, ih_pair, ih_mem⟩ := ih hrest_blocks hpair.2 hrest_le
      refine ⟨?_, ih_valid, ih_pair, ?_⟩
      · simp only [List.flatMap_cons, List.filter_append, hq_nodes_nil, List.nil_append]
        exact ih_flat
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr_rest
        · exact Or.inr ⟨hqL_nil, hqR_nil⟩
        · exact ih_mem r hr_rest
    · simp only [hmin, ↓reduceIte]
      obtain ⟨b₀, hb₀_mem, hb₀_eq⟩ := q.minimum_mem hq.1
      have hb₀_le : b₀.depth ≤ c := hq_le b₀ hb₀_mem
      have hb₀_lt : b₀.depth < c := by omega
      have hqL_drop : q.left.dropWhile (fun b => b.depth == c) =
          q.left.filter (fun b => decide (b.depth < c)) :=
        dropWhile_eq_filter_of_ordered hq.2.1 (fun b hb => hq_le b (List.mem_append_left _ hb))
      have hqR_drop : q.right.dropWhile (fun b => b.depth == c) =
          q.right.filter (fun b => decide (b.depth < c)) :=
        dropWhile_eq_filter_of_ordered hq.2.2.1 (fun b hb => hq_le b (List.mem_append_right _ hb))
      let q' : Block :=
        { left := q.left.filter (fun b => decide (b.depth < c))
          right := q.right.filter (fun b => decide (b.depth < c)) }
      have hq'_nodes : q'.nodes = q.nodes.filter (fun b => decide (b.depth < c)) := by
        simp [q', Block.nodes, List.filter_append]
      have hrest_lt : ∀ r ∈ rest, ∀ d ∈ r.nodes, d.depth < c := by
        intro r hr d hd
        exact lt_of_le_of_lt (hpair.1 r hr b₀ hb₀_mem d hd) hb₀_lt
      have hrest_filter_flat :
          (rest.flatMap Block.nodes).filter (fun b => decide (b.depth < c)) =
            rest.flatMap Block.nodes := by
        apply filter_lt_eq_self_of_lt
        intro d hd
        obtain ⟨r, hr, hd_r⟩ := List.mem_flatMap.mp hd
        exact hrest_lt r hr d hd_r
      rw [hqL_drop, hqR_drop]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.flatMap_cons, List.filter_append]
        rw [← hq'_nodes, hrest_filter_flat]
      · intro r' hr'
        rcases List.mem_cons.mp hr' with rfl | hr'_rest
        · refine ⟨?_, hq.2.1.filter _, hq.2.2.1.filter _, ?_⟩
          · rw [hq'_nodes]
            intro hnil
            have hb₀_filt : b₀ ∈ q.nodes.filter (fun b => decide (b.depth < c)) :=
              List.mem_filter.mpr ⟨hb₀_mem, decide_eq_true hb₀_lt⟩
            rw [hnil] at hb₀_filt
            nomatch hb₀_filt
          · intro b hb
            rw [hq'_nodes, List.mem_filter] at hb
            exact hq.2.2.2 b hb.1
        · exact hrest_blocks r' hr'_rest
      · rw [List.pairwise_cons]
        refine ⟨?_, hpair.2⟩
        intro r hr b hb d hd
        rw [hq'_nodes, List.mem_filter] at hb
        exact hpair.1 r hr b hb.1 d hd
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr_rest
        · exact Or.inl List.mem_cons_self
        · left
          have hL_eq : r.left.filter (fun b => decide (b.depth < c)) = r.left :=
            filter_lt_eq_self_of_lt (fun d hd => hrest_lt r hr_rest d (List.mem_append_left _ hd))
          have hR_eq : r.right.filter (fun b => decide (b.depth < c)) = r.right :=
            filter_lt_eq_self_of_lt (fun d hd => hrest_lt r hr_rest d (List.mem_append_right _ hd))
          rw [hL_eq, hR_eq]
          exact List.mem_cons_of_mem _ hr_rest

/-! ## Existential Projection of Block Formulas -/

/-- Flip a color between `.left` and `.right`. -/
def Color.flip : Color → Color
  | .left => .right
  | .right => .left

theorem Color.flip_ne (c : Color) : c.flip ≠ c := by
  cases c <;> decide

theorem Block.Holds.exists_side_colors {q : Block} {color : ℕ → Color} (h : q.Holds color) :
    ∃ cL cR : Color, cL ≠ cR ∧
      (∀ i ∈ nodeSet q.left, color i = cL) ∧
      (∀ j ∈ nodeSet q.right, color j = cR) := by
  rcases q with ⟨_ | ⟨bL, restL⟩, _ | ⟨bR, restR⟩⟩
  · exact ⟨.left, .right, by decide, by simp, by simp⟩
  · refine ⟨(color bR.edge).flip, color bR.edge, Color.flip_ne _, by simp, ?_⟩
    intro j hj
    exact h.2.1 j hj bR.edge (by simp)
  · refine ⟨color bL.edge, (color bL.edge).flip, (Color.flip_ne _).symm, ?_, by simp⟩
    intro i hi
    exact h.1 i hi bL.edge (by simp)
  · refine ⟨color bL.edge, color bR.edge, ?_, ?_, ?_⟩
    · exact h.2.2 bL.edge (by simp) bR.edge (by simp)
    · intro i hi
      exact h.1 i hi bL.edge (by simp)
    · intro j hj
      exact h.2.1 j hj bR.edge (by simp)

/-- Existential extension for a stack of blocks with disjoint edge variables. -/
theorem extend_blocks_coloring (P : ReturnNode → Bool) :
    ∀ (blocks : List Block) (color : ℕ → Color),
      ((blocks.flatMap Block.nodes).map ReturnNode.edge).Nodup →
      (∀ q ∈ blocks, (⟨q.left.filter P, q.right.filter P⟩ : Block).Holds color) →
      ∃ ext : ℕ → Color,
        (∀ q ∈ blocks, q.Holds ext) ∧
        (∀ i ∉ nodeSet (blocks.flatMap Block.nodes), ext i = color i) ∧
        (∀ i ∈ nodeSet ((blocks.flatMap Block.nodes).filter P), ext i = color i) := by
  intro blocks
  induction blocks with
  | nil =>
    intro color _ _
    exact ⟨color, by simp, by simp, by simp⟩
  | cons q rest ih =>
    intro color hnodup hholds
    simp only [List.flatMap_cons] at hnodup
    have hdisj_q_rest : Disjoint (nodeSet q.nodes) (nodeSet (rest.flatMap Block.nodes)) :=
      disjoint_nodeSet_of_nodup hnodup
    rw [List.map_append, List.nodup_append] at hnodup
    have hnodup_q : (q.nodes.map ReturnNode.edge).Nodup := hnodup.1
    have hnodup_rest : ((rest.flatMap Block.nodes).map ReturnNode.edge).Nodup := hnodup.2.1
    have hdisj_LR : Disjoint (nodeSet q.left) (nodeSet q.right) :=
      disjoint_nodeSet_of_nodup hnodup_q
    obtain ⟨ext₁, hext₁_holds, hext₁_out, hext₁_filt⟩ :=
      ih color hnodup_rest (fun r hr => hholds r (List.mem_cons_of_mem q hr))
    obtain ⟨cL, cR, hne_LR, hcL, hcR⟩ :=
      (hholds q List.mem_cons_self).exists_side_colors
    let ext : ℕ → Color := fun i =>
      if i ∈ nodeSet q.left then cL
      else if i ∈ nodeSet q.right then cR
      else ext₁ i
    have hext_L : ∀ i ∈ nodeSet q.left, ext i = cL := by
      intro i hi
      simp only [ext, hi, ↓reduceIte]
    have hext_R : ∀ j ∈ nodeSet q.right, ext j = cR := by
      intro j hj
      have hj_not_L : j ∉ nodeSet q.left := Set.disjoint_right.mp hdisj_LR hj
      simp only [ext, hj_not_L, hj, ↓reduceIte]
    have hext_not_q : ∀ i ∉ nodeSet q.nodes, ext i = ext₁ i := by
      intro i hi
      have hiL : i ∉ nodeSet q.left := fun h => hi (by simp [Block.nodes, h])
      have hiR : i ∉ nodeSet q.right := fun h => hi (by simp [Block.nodes, h])
      simp only [ext, hiL, hiR, ↓reduceIte]
    refine ⟨ext, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr_rest
      · refine ⟨?_, ?_, ?_⟩
        · intro i₁ hi₁ i₂ hi₂
          rw [hext_L i₁ hi₁, hext_L i₂ hi₂]
        · intro j₁ hj₁ j₂ hj₂
          rw [hext_R j₁ hj₁, hext_R j₂ hj₂]
        · intro i hi j hj
          rw [hext_L i hi, hext_R j hj]
          exact hne_LR
      · apply (hext₁_holds r hr_rest).congr_on
        intro i hi
        have hi_rest : i ∈ nodeSet (rest.flatMap Block.nodes) := by
          rw [mem_nodeSet_iff] at hi ⊢
          exact List.mem_map.mpr (by
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
            exact ⟨b, List.mem_flatMap.mpr ⟨r, hr_rest, hb⟩, rfl⟩)
        have hi_not_q : i ∉ nodeSet q.nodes :=
          Set.disjoint_right.mp hdisj_q_rest hi_rest
        exact (hext_not_q i hi_not_q).symm
    · intro i hi
      simp only [List.flatMap_cons, nodeSet_append, Set.mem_union, not_or] at hi
      rw [hext_not_q i hi.1, hext₁_out i hi.2]
    · intro i hi
      simp only [List.flatMap_cons, List.filter_append, nodeSet_append, Set.mem_union] at hi
      rcases hi with hi_q | hi_rest
      · simp only [Block.nodes, List.filter_append, nodeSet_append, Set.mem_union] at hi_q
        rcases hi_q with hiL | hiR
        · have hiL' : i ∈ nodeSet q.left := by
            rw [mem_nodeSet_iff] at hiL ⊢
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hiL
            exact List.mem_map_of_mem (List.mem_filter.mp hb).1
          rw [hext_L i hiL', hcL i hiL]
        · have hiR' : i ∈ nodeSet q.right := by
            rw [mem_nodeSet_iff] at hiR ⊢
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hiR
            exact List.mem_map_of_mem (List.mem_filter.mp hb).1
          rw [hext_R i hiR', hcR i hiR]
      · have hi_rest' : i ∈ nodeSet (rest.flatMap Block.nodes) := by
          rw [mem_nodeSet_iff] at hi_rest ⊢
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi_rest
          exact List.mem_map_of_mem (List.mem_filter.mp hb).1
        have hi_not_q : i ∉ nodeSet q.nodes :=
          Set.disjoint_right.mp hdisj_q_rest hi_rest'
        rw [hext_not_q i hi_not_q, hext₁_filt i hi_rest]

/-! ## Proof of `TrimStatement` -/

theorem mem_trimBlocks_subset {c : ℕ} {blocks : List Block} {q' : Block}
    (hq' : q' ∈ trimBlocks c blocks) :
    ∃ q ∈ blocks, nodeSet q'.left ⊆ nodeSet q.left ∧ nodeSet q'.right ⊆ nodeSet q.right := by
  induction blocks with
  | nil => nomatch hq'
  | cons q rest ih =>
    unfold trimBlocks at hq'
    split_ifs at hq' with hmin
    · obtain ⟨r, hr, hL, hR⟩ := ih hq'
      exact ⟨r, List.mem_cons_of_mem q hr, hL, hR⟩
    · rcases List.mem_cons.mp hq' with rfl | hq'_rest
      · refine ⟨q, List.mem_cons_self, ?_, ?_⟩
        · intro i hi
          rw [mem_nodeSet_iff] at hi ⊢
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
          exact List.mem_map_of_mem ((List.dropWhile_sublist _).subset hb)
        · intro j hj
          rw [mem_nodeSet_iff] at hj ⊢
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hj
          exact List.mem_map_of_mem ((List.dropWhile_sublist _).subset hb)
      · exact ⟨q', List.mem_cons_of_mem q hq'_rest, Set.Subset.refl _, Set.Subset.refl _⟩

/-- Part II, trim at the parent: deleting parent-depth nodes is exact existential
projection, and preserves the summary representation. -/
theorem trimStatement : TrimStatement := by
  intro s c hvalid hle result
  rcases hvalid with ⟨hanchor_ne, hanchor_depth, hblocks_valid, hblocks_pair, hnodup⟩
  have hleast_le : s.least ≤ c := by
    rcases hanc : s.anchor with _ | ⟨b, _⟩
    · exact absurd hanc hanchor_ne
    · have hb_anc : b ∈ s.anchor := by rw [hanc]; exact List.mem_cons_self
      have hb_mem : b ∈ s.nodes := List.mem_append_left _ hb_anc
      have hb_eq : b.depth = s.least := hanchor_depth b hb_anc
      exact hb_eq ▸ hle b hb_mem
  by_cases hleast_eq : s.least = c
  · -- Case 1: `s.least = c`, so `trim (some s) c = none` and no nodes have depth `< c`.
    have hresult : result = none := by
      simp [result, trim, hleast_eq]
    have hblocks_nil : s.blocks = [] := by
      rcases hblk : s.blocks with _ | ⟨q, rest⟩
      · rfl
      · exfalso
        have hq_mem : q ∈ s.blocks := by rw [hblk]; exact List.mem_cons_self
        have hq := hblocks_valid q hq_mem
        rcases hqn : q.nodes with _ | ⟨b, _⟩
        · exact hq.1 hqn
        · have hb_q : b ∈ q.nodes := by rw [hqn]; exact List.mem_cons_self
          have hb_gt : s.least < b.depth := hq.2.2.2 b hb_q
          have hb_mem : b ∈ s.nodes :=
            List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq_mem, hb_q⟩)
          have hb_le : b.depth ≤ c := hle b hb_mem
          omega
    have hfilter_nil : s.nodes.filter (fun b => decide (b.depth < c)) = [] := by
      apply filter_lt_eq_nil_of_eq
      intro b hb
      simp only [Summary.nodes, hblocks_nil, List.flatMap_nil, List.append_nil] at hb
      exact (hanchor_depth b hb).trans hleast_eq
    rw [hresult]
    refine ⟨?_, ?_, ?_⟩
    · intro color
      simp only [SummaryFormula, hfilter_nil, nodeSet_nil, Set.mem_empty_iff_false,
        IsEmpty.forall_iff, implies_true, and_true, true_iff]
      refine ⟨fun _ => .left, ?_⟩
      simp [Summary.Holds, hblocks_nil, Monochromatic]
    · simp [summaryNodes, hfilter_nil]
    · intro t ht
      nomatch ht
  · -- Case 2: `s.least < c`, so `s.anchor` survives and `trimBlocks` filters `< c`.
    have hleast_lt : s.least < c := Nat.lt_of_le_of_ne hleast_le hleast_eq
    let t : Summary := { s with blocks := trimBlocks c s.blocks }
    have hresult : result = some t := by
      simp [result, trim, hleast_eq, t]
    have hblocks_le : ∀ q ∈ s.blocks, ∀ b ∈ q.nodes, b.depth ≤ c := by
      intro q hq b hb
      exact hle b (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, hb⟩))
    obtain ⟨htrim_flat, htrim_valid, htrim_pair, htrim_mem⟩ :=
      trimBlocks_spec hblocks_valid hblocks_pair hblocks_le
    have hanchor_filter : s.anchor.filter (fun b => decide (b.depth < c)) = s.anchor := by
      apply filter_lt_eq_self_of_lt
      intro b hb
      rw [hanchor_depth b hb]
      exact hleast_lt
    have ht_nodes : t.nodes = s.nodes.filter (fun b => decide (b.depth < c)) := by
      simp only [t, Summary.nodes, List.filter_append, hanchor_filter, htrim_flat]
    rw [hresult]
    refine ⟨?_, ?_, ?_⟩
    · intro color
      simp only [SummaryFormula]
      constructor
      · intro ht_holds
        have hnodup_split : ((s.anchor ++ s.blocks.flatMap Block.nodes).map ReturnNode.edge).Nodup :=
          hnodup
        have hdisj_anc : Disjoint (nodeSet s.anchor) (nodeSet (s.blocks.flatMap Block.nodes)) :=
          disjoint_nodeSet_of_nodup hnodup_split
        rw [List.map_append, List.nodup_append] at hnodup_split
        have hq_filt_holds : ∀ q ∈ s.blocks,
            (⟨q.left.filter (fun b => decide (b.depth < c)),
              q.right.filter (fun b => decide (b.depth < c))⟩ : Block).Holds color := by
          intro q hq
          rcases htrim_mem q hq with hmem_trim | ⟨hL_nil, hR_nil⟩
          · exact ht_holds.2 _ hmem_trim
          · simp [Block.Holds, hL_nil, hR_nil]
        obtain ⟨ext, hext_blocks, hext_out, hext_filt⟩ :=
          extend_blocks_coloring (fun b => decide (b.depth < c)) s.blocks color
            hnodup_split.2.1 hq_filt_holds
        refine ⟨ext, ⟨?_, hext_blocks⟩, ?_⟩
        · apply ht_holds.1.congr_on
          intro i hi
          have hi_not_blocks : i ∉ nodeSet (s.blocks.flatMap Block.nodes) :=
            Set.disjoint_left.mp hdisj_anc hi
          exact (hext_out i hi_not_blocks).symm
        · intro i hi
          simp only [Summary.nodes, List.filter_append, hanchor_filter,
            nodeSet_append, Set.mem_union] at hi
          rcases hi with hi_anc | hi_filt
          · have hi_not_blocks : i ∉ nodeSet (s.blocks.flatMap Block.nodes) :=
              Set.disjoint_left.mp hdisj_anc hi_anc
            exact hext_out i hi_not_blocks
          · exact hext_filt i hi_filt
      · rintro ⟨ext, ⟨hext_anc, hext_blocks⟩, hext_eq⟩
        have hext_anc_eq : ∀ i ∈ nodeSet s.anchor, ext i = color i := by
          intro i hi
          apply hext_eq i
          simp only [Summary.nodes, List.filter_append, hanchor_filter,
            nodeSet_append, Set.mem_union]
          exact Or.inl hi
        refine ⟨hext_anc.congr_on hext_anc_eq, ?_⟩
        intro q' hq'
        have hq'_sub : nodeSet q'.nodes ⊆ nodeSet (s.nodes.filter (fun b => decide (b.depth < c))) := by
          rw [← ht_nodes]
          intro i hi
          rw [mem_nodeSet_iff] at hi ⊢
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
          exact List.mem_map_of_mem (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q', hq', hb⟩))
        have hq'_congr : ∀ i ∈ nodeSet q'.nodes, ext i = color i :=
          fun i hi => hext_eq i (hq'_sub hi)
        obtain ⟨q, hq_mem, hsubL, hsubR⟩ := mem_trimBlocks_subset hq'
        have hq_ext := hext_blocks q hq_mem
        have hq'_ext : q'.Holds ext :=
          ⟨hq_ext.1.subset hsubL, hq_ext.2.1.subset hsubR,
            fun i hi j hj => hq_ext.2.2 i (hsubL hi) j (hsubR hj)⟩
        exact hq'_ext.congr_on hq'_congr
    · simp only [summaryNodes, ht_nodes]
    · intro t' ht'
      injection ht' with ht'_eq
      subst ht'_eq
      refine ⟨hanchor_ne, hanchor_depth, htrim_valid, htrim_pair, ?_⟩
      rw [ht_nodes]
      exact hnodup.sublist (List.Sublist.map _ (List.filter_sublist))

end GraphMinor.LRPlanarity
