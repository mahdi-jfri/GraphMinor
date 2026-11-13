module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Pigeonhole
public import GraphMinor.Compute.BFS

/-!
# Vertex-Disjoint Paths by Augmenting Paths in the Word RAM Model

This file formalizes `k` rounds of augmenting-path search for vertex-disjoint paths between two
vertex sets `A, B ⊆ Fin n` in a finite simple graph `G : SimpleGraph (Fin n)` in time
`O(k (n + m))`:
- `ABWalk`, `PairwiseVertexDisjoint`, `IsABSeparator`, and the Menger separator duality bound
  `card_le_of_disjoint_walks_and_separator`: any `r` pairwise vertex-disjoint `A`-`B` walks and
  any `A`-`B` vertex separator `S` satisfy `r ≤ S.card`.
- The `2n`-vertex split residual network (`inNode`, `outNode`, `ResidualAdj`, `ResReachable`),
  exact characterization of residual BFS reachability (`mem_iff_resReachable`), and the residual
  cut certificate (`isABSeparator_used_of_no_target_reached`): when no `outNode b` (`b ∈ B`) is
  reachable in the residual network, the saturated vertices `{u | used u ≠ 0}` form an `A`-`B`
  vertex separator in `G`.
- Extraction of valid `G.Walk`s from the successor array encoding (`ValidPathState`, `IsSuccPath`,
  `walkOfSuccPath`).
- Word RAM programs `tryPushReg`, `initSourcesProg`, `resBfsStepProg`, `resBfsLoopProg`,
  `findTargetProg`, `augmentTraceProg`, and `disjointPathsProg` using a register-offset and
  array-offset discipline (`r_base + i`, `a_base + j`), with proved `O(k (n + m))` running time
  (`Triple.disjointPathsProg_spec`).
-/

@[expose] public section

namespace GraphMinor.Compute

/-! ### Section 1: `A`-`B` Walks, Vertex Disjointness, and Separator Duality -/

/-- A walk in `G` from a vertex in `A` to a vertex in `B`. -/
structure ABWalk {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) where
  /-- Starting vertex of the walk. -/
  start : Fin n
  /-- Ending vertex of the walk. -/
  finish : Fin n
  /-- The starting vertex belongs to `A`. -/
  start_mem : start ∈ A
  /-- The ending vertex belongs to `B`. -/
  finish_mem : finish ∈ B
  /-- The underlying walk in `G`. -/
  walk : G.Walk start finish

/-- A family of `k` `A`-`B` walks is pairwise vertex-disjoint if distinct walks have disjoint
supports. -/
def PairwiseVertexDisjoint {n k : ℕ} {G : SimpleGraph (Fin n)} {A B : Finset (Fin n)}
    (P : Fin k → ABWalk G A B) : Prop :=
  ∀ i j : Fin k, i ≠ j → List.Disjoint (P i).walk.support (P j).walk.support

/-- A vertex set `S ⊆ Fin n` is an `A`-`B` vertex separator in `G` if every walk from `A` to `B`
in `G` contains a vertex in `S`. -/
def IsABSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (A B S : Finset (Fin n)) : Prop :=
  ∀ w : ABWalk G A B, ∃ x ∈ S, x ∈ w.walk.support

/-- Weak Menger duality: if `P` is a family of `k` pairwise vertex-disjoint `A`-`B` walks in `G`
and `S` is an `A`-`B` vertex separator in `G`, then `k ≤ S.card`. -/
theorem card_le_of_disjoint_walks_and_separator {n k : ℕ} {G : SimpleGraph (Fin n)}
    {A B S : Finset (Fin n)} (P : Fin k → ABWalk G A B)
    (hdisj : PairwiseVertexDisjoint P) (hsep : IsABSeparator G A B S) :
    k ≤ S.card := by
  classical
  have hchoose : ∀ i : Fin k, ∃ x ∈ S, x ∈ (P i).walk.support := fun i => hsep (P i)
  choose f hfS hf_supp using hchoose
  have hinj : Set.InjOn f ( ↑(Finset.univ : Finset (Fin k)) ) := by
    intro i _ j _ hij
    by_contra hne
    have hmem_j : f i ∈ (P j).walk.support := hij ▸ hf_supp j
    exact hdisj i j hne (hf_supp i) hmem_j
  have hmaps : Set.MapsTo f ( ↑(Finset.univ : Finset (Fin k)) ) ( ↑S ) := by
    intro i _
    exact hfS i
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  simpa using hcard

/-! ### Section 2: Split Residual Network and Separator Certificate -/

/-- The in-node `u⁻` (`u.1 < n`) of vertex `u : Fin n` in the `2n`-vertex split network. -/
def inNode {n : ℕ} (u : Fin n) : Fin (2 * n) :=
  ⟨u.1, by omega⟩

/-- The out-node `u⁺` (`u.1 + n < 2 * n`) of vertex `u : Fin n` in the `2n`-vertex split network. -/
def outNode {n : ℕ} (u : Fin n) : Fin (2 * n) :=
  ⟨u.1 + n, by omega⟩

@[simp]
theorem inNode_val {n : ℕ} (u : Fin n) : (inNode u).1 = u.1 := rfl

@[simp]
theorem outNode_val {n : ℕ} (u : Fin n) : (outNode u).1 = u.1 + n := rfl

/-- Directed adjacency relation of the `2n`-vertex split residual network for vertex-disjoint paths.
- From `inNode u` (`x.1 < n`):
  - If `used u = 0`, there is a forward internal edge to `outNode u` (`y.1 = x.1 + n`).
  - If `used u ≠ 0` and `pred u < n`, there is a backward edge to `outNode ⟨pred u, _⟩`
    (`y.1 = pred u + n`).
- From `outNode u` (`n ≤ x.1 < 2 * n`, where `u = x.1 - n`):
  - If `used u ≠ 0`, there is a backward internal edge to `inNode u` (`y.1 = x.1 - n`).
  - For every neighbor `v` of `u` in `G` with `v.1 ≠ succ u`, there is a forward edge to
    `inNode v` (`y.1 = v.1`). -/
def ResidualAdj {n : ℕ} (G : SimpleGraph (Fin n)) (used pred succ : Fin n → ℕ)
    (x y : Fin (2 * n)) : Prop :=
  if hx : x.1 < n then
    let u : Fin n := ⟨x.1, hx⟩
    if used u = 0 then
      y.1 = u.1 + n
    else
      pred u < n ∧ y.1 = pred u + n
  else
    let u : Fin n := ⟨x.1 - n, by omega⟩
    (used u ≠ 0 ∧ y.1 = u.1) ∨
      ∃ (hy : y.1 < n), y.1 ≠ succ u ∧ G.Adj u ⟨y.1, hy⟩

/-- The initial source nodes of the residual BFS: `inNode u` for all unsaturated `u ∈ A`. -/
def InitialSources {n : ℕ} (A : Finset (Fin n)) (used : Fin n → ℕ) : Set (Fin (2 * n)) :=
  {x | ∃ u ∈ A, used u = 0 ∧ x = inNode u}

/-- Reachability in a directed graph `Adj` on `Fin (2 * n)` from an initial source set `S₀`. -/
def ResReachable {m : ℕ} (Adj : Fin m → Fin m → Prop) (S₀ : Set (Fin m)) (y : Fin m) : Prop :=
  ∃ x ∈ S₀, Relation.ReflTransGen Adj x y

/-- Exact characterization of BFS reachability from a set of initial sources `S₀`: if `items`
contains `S₀`, every element of `items` is reachable from `S₀`, and `items` is closed under
`Adj`, then membership in `items` is equivalent to `ResReachable Adj S₀`. -/
theorem mem_iff_resReachable {m : ℕ} {Adj : Fin m → Fin m → Prop} {S₀ : Set (Fin m)}
    {items : List ℕ}
    (hinit : ∀ x ∈ S₀, x.1 ∈ items)
    (hreach : ∀ y : Fin m, y.1 ∈ items → ResReachable Adj S₀ y)
    (hclosed : ∀ x : Fin m, x.1 ∈ items → ∀ y : Fin m, Adj x y → y.1 ∈ items)
    (y : Fin m) :
    y.1 ∈ items ↔ ResReachable Adj S₀ y := by
  constructor
  · exact hreach y
  · rintro ⟨x, hxS, hpath⟩
    induction hpath with
    | refl => exact hinit x hxS
    | tail _ hadj ih => exact hclosed _ ih _ hadj

/-- Walk propagation lemma in the residual network: if every vertex along a walk `w : G.Walk u v`
is unsaturated (`used x = 0` and `succ x = n`), and `inNode u` is reachable in the residual
network, then `outNode v` is reachable in the residual network. -/
theorem resReachable_outNode_of_walk_unsaturated {n : ℕ} {G : SimpleGraph (Fin n)}
    {used pred succ : Fin n → ℕ} {S₀ : Set (Fin (2 * n))}
    (hsucc_unused : ∀ x : Fin n, used x = 0 → succ x = n)
    {u v : Fin n} (w : G.Walk u v)
    (hunsat : ∀ x ∈ w.support, used x = 0)
    (hu_reach : ResReachable (ResidualAdj G used pred succ) S₀ (inNode u)) :
    ResReachable (ResidualAdj G used pred succ) S₀ (outNode v) := by
  induction w with
  | nil =>
    rename_i u
    have hu0 : used u = 0 := hunsat u (by simp)
    rcases hu_reach with ⟨s₀, hs₀, hpath⟩
    refine ⟨s₀, hs₀, hpath.tail ?_⟩
    simp [ResidualAdj, inNode, outNode, u.2, hu0]
  | @cons u y v hadj w ih =>
    have hu0 : used u = 0 := hunsat u (by simp)
    have hsucc_u : succ u = n := hsucc_unused u hu0
    have hout_u : ResReachable (ResidualAdj G used pred succ) S₀ (outNode u) := by
      rcases hu_reach with ⟨s₀, hs₀, hpath⟩
      refine ⟨s₀, hs₀, hpath.tail ?_⟩
      simp [ResidualAdj, inNode, outNode, u.2, hu0]
    have hin_y : ResReachable (ResidualAdj G used pred succ) S₀ (inNode y) := by
      rcases hout_u with ⟨s₀, hs₀, hpath⟩
      refine ⟨s₀, hs₀, hpath.tail ?_⟩
      have hnot_lt : ¬ (u.1 + n < n) := by omega
      simp only [ResidualAdj, outNode_val, hnot_lt, ↓reduceDIte, Nat.add_sub_cancel]
      have hu_eq : (⟨u.1, by omega⟩ : Fin n) = u := rfl
      rw [hu_eq, hsucc_u]
      exact Or.inr ⟨y.2, ne_of_lt y.2, hadj⟩
    exact ih (fun x hx => hunsat x (by simp [hx])) hin_y

/-- Residual cut certificate: if no `b ∈ B` has `outNode b` reachable from `InitialSources A used`
in the residual network (and unsaturated vertices have `succ x = n`), then the finset of
currently saturated vertices `{x | used x ≠ 0}` is an `A`-`B` vertex separator in `G`. -/
theorem isABSeparator_used_of_no_target_reached {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (used pred succ : Fin n → ℕ)
    (hsucc_unused : ∀ x : Fin n, used x = 0 → succ x = n)
    (hno_target : ∀ b ∈ B,
      ¬ ResReachable (ResidualAdj G used pred succ) (InitialSources A used) (outNode b)) :
    IsABSeparator G A B (Finset.univ.filter (fun x : Fin n => used x ≠ 0)) := by
  intro w
  by_contra hnot
  have hunsat : ∀ x ∈ w.walk.support, used x = 0 := by
    intro x hx
    by_contra hne
    exact hnot ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hne⟩, hx⟩
  have hstart0 : used w.start = 0 := hunsat w.start w.walk.start_mem_support
  have hin_start : ResReachable (ResidualAdj G used pred succ)
      (InitialSources A used) (inNode w.start) :=
    ⟨inNode w.start, ⟨w.start, w.start_mem, hstart0, rfl⟩, Relation.ReflTransGen.refl⟩
  have hout_finish := resReachable_outNode_of_walk_unsaturated hsucc_unused w.walk hunsat hin_start
  exact hno_target w.finish w.finish_mem hout_finish

/-! ### Section 3: Path Encoding and Walk Extraction from `a_succ` -/

/-- Validity invariant for the path encoding arrays `(a_used, a_pred, a_succ)` of length `n`. -/
def ValidPathState {n : ℕ} (G : SimpleGraph (Fin n)) (a_used a_pred a_succ : ℕ)
    (s : State) : Prop :=
  ∃ (hu : (s.arrs a_used).length = n)
    (hp : (s.arrs a_pred).length = n)
    (hs : (s.arrs a_succ).length = n),
    (∀ u : Fin n, (s.arrs a_used)[u.1]'(by rw [hu]; exact u.2) ≤ 1) ∧
    (∀ u : Fin n, (s.arrs a_pred)[u.1]'(by rw [hp]; exact u.2) ≤ n) ∧
    (∀ u : Fin n, (s.arrs a_succ)[u.1]'(by rw [hs]; exact u.2) ≤ n) ∧
    (∀ u : Fin n, (s.arrs a_used)[u.1]'(by rw [hu]; exact u.2) = 0 →
      (s.arrs a_succ)[u.1]'(by rw [hs]; exact u.2) = n) ∧
    (∀ u v : Fin n, (s.arrs a_succ)[u.1]'(by rw [hs]; exact u.2) = v.1 → G.Adj u v)

theorem ValidPathState.of_arrs_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    {a_used a_pred a_succ : ℕ} {s s' : State}
    (h : ValidPathState G a_used a_pred a_succ s)
    (hu : s'.arrs a_used = s.arrs a_used)
    (hp : s'.arrs a_pred = s.arrs a_pred)
    (hs : s'.arrs a_succ = s.arrs a_succ) :
    ValidPathState G a_used a_pred a_succ s' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  exact ⟨by rw [hu, h1], by rw [hp, h2], by rw [hs, h3],
    fun u => by simp only [hu]; exact h4 u,
    fun u => by simp only [hp]; exact h5 u,
    fun u => by simp only [hs]; exact h6 u,
    fun u h0 => by simp only [hu, hs] at h0 ⊢; exact h7 u h0,
    fun u v heq => by simp only [hs] at heq; exact h8 u v heq⟩

/-- A chain of vertices in `Fin n` following the successor array `a_succ` in state `s`. -/
inductive IsSuccChain {n : ℕ} (a_succ : ℕ) (s : State) :
    Fin n → Fin n → List (Fin n) → Prop
  | single (u : Fin n) : IsSuccChain a_succ s u u [u]
  | cons {u v z : Fin n} {vs : List (Fin n)}
      (hs_len : (s.arrs a_succ).length = n)
      (hsucc : (s.arrs a_succ)[u.1]'(by rw [hs_len]; exact u.2) = v.1)
      (htail : IsSuccChain a_succ s v z vs) :
      IsSuccChain a_succ s u z (u :: vs)

/-- Any `IsSuccChain` in a state satisfying `ValidPathState` induces a walk in `G` with the exact
same vertex support. -/
theorem IsSuccChain.exists_walk {n : ℕ} {G : SimpleGraph (Fin n)} {a_used a_pred a_succ : ℕ}
    {s : State} (hvalid : ValidPathState G a_used a_pred a_succ s)
    {u z : Fin n} {vs : List (Fin n)} (hchain : IsSuccChain a_succ s u z vs) :
    ∃ w : G.Walk u z, w.support = vs := by
  induction hchain with
  | single u => exact ⟨.nil, rfl⟩
  | cons _ hsucc _ ih =>
    rcases ih with ⟨w_tail, hsupp⟩
    exact ⟨.cons (hvalid.2.2.2.2.2.2.2 _ _ hsucc) w_tail, by simp [hsupp]⟩

/-! ### Section 4: Residual BFS Queue & `tryPushReg` Helper -/

/-- Queue, visited-array, and parent-array state during the `2n`-node residual BFS. -/
def ResQueueState {n : ℕ} (a_vis a_parent a_q : ℕ) (r_head r_tail : ℕ)
    (items : List ℕ) (headIdx : ℕ) (s : State) : Prop :=
  IsQueueHistory a_q r_head r_tail (2 * n) items headIdx s ∧
  items.Nodup ∧
  (∀ x ∈ items, x < 2 * n) ∧
  ∃ (hvis : (s.arrs a_vis).length = 2 * n) (hpar : (s.arrs a_parent).length = 2 * n),
    (∀ x : ℕ, (hx : x < 2 * n) →
      (((s.arrs a_vis)[x]'(by rw [hvis]; exact hx) ≠ 0 ↔ x ∈ items) ∧
       (s.arrs a_vis)[x]'(by rw [hvis]; exact hx) ≤ 1)) ∧
    (∀ x : ℕ, (hx : x < 2 * n) →
      (s.arrs a_parent)[x]'(by rw [hpar]; exact hx) < 2 * n)

/-- Soundness of forward graph edges recorded in `a_parent`: whenever `v < n` has
`a_parent[v] = u + n` with `u ≠ v`, the pair `(u, v)` is an edge of `G`. -/
def ParentEdgeSound {n : ℕ} (G : SimpleGraph (Fin n)) (a_parent : ℕ) (s : State) : Prop :=
  ∃ (hpar : (s.arrs a_parent).length = 2 * n),
    ∀ (v u : Fin n), u ≠ v →
      (s.arrs a_parent)[v.1]'(by rw [hpar]; have := v.2; omega) = u.1 + n →
      G.Adj u v

/-- Helper command: if `a_vis[r_node] == 0`, mark `a_vis[r_node] := 1`, record
`a_parent[r_node] := r_par`, and push `r_node` onto the queue `a_q`. -/
def tryPushReg (a_vis a_parent a_q : Arr) (r_tail r_vis r_node r_par : Reg) : Cmd :=
  .seq (.assign r_vis (.read a_vis (.reg r_node)))
    (.ite (.reg r_vis)
      .skip
      (.seq (.write a_vis (.reg r_node) (.const 1))
        (.seq (.write a_parent (.reg r_node) (.reg r_par))
          (queuePush a_q r_tail (.reg r_node)))))

/-- Execution lemma for `tryPushReg`: executes in at most `17` steps, appending `extra` (`[]` or
`[y]`) to `items` so that `z ∈ items ++ extra ↔ z ∈ items ∨ z = y`, while preserving
`ResQueueState` and `ParentEdgeSound`. -/
theorem tryPushReg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (a_vis a_parent a_q : ℕ) (r_head r_tail r_vis r_node r_par : ℕ)
    (hne_vp : a_vis ≠ a_parent) (hne_vq : a_vis ≠ a_q) (hne_pq : a_parent ≠ a_q)
    (hne_ht : r_head ≠ r_tail) (hne_hv : r_head ≠ r_vis)
    (hne_tv : r_tail ≠ r_vis) (_hne_tn : r_tail ≠ r_node) (_hne_tp : r_tail ≠ r_par)
    (hne_vn : r_vis ≠ r_node) (hne_vp_reg : r_vis ≠ r_par)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {headIdx y x : ℕ} {s : State}
    (hqstate : ResQueueState (n := n) a_vis a_parent a_q r_head r_tail items headIdx s)
    (hpar_sound : ParentEdgeSound G a_parent s)
    (hr_node : s.regs r_node = y) (hy_lt : y < 2 * n)
    (hr_par : s.regs r_par = x) (hx_lt : x < 2 * n)
    (hpar_edge : ∀ (v u : Fin n), v.1 = y → x = u.1 + n → u ≠ v → G.Adj u v) :
    ∃ s' t extra,
      Exec w (tryPushReg a_vis a_parent a_q r_tail r_vis r_node r_par) s s' t ∧
      t ≤ 17 ∧
      ResQueueState (n := n) a_vis a_parent a_q r_head r_tail (items ++ extra) headIdx s' ∧
      ParentEdgeSound G a_parent s' ∧
      (∀ z, z ∈ items ++ extra ↔ z ∈ items ∨ z = y) ∧
      (∀ a : ℕ, a ≠ a_vis → a ≠ a_parent → a ≠ a_q → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_tail → r ≠ r_vis → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hy_w : y < 2 ^ w := by omega
  have hx_w : x < 2 ^ w := by omega
  have hne_vp' : (a_vis : Arr) ≠ a_parent := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := by omega
  have hne_pq' : (a_parent : Arr) ≠ a_q := by omega
  have hne_hv' : (r_head : Reg) ≠ r_vis := by omega
  have hne_tv' : (r_tail : Reg) ≠ r_vis := by omega
  have hne_vn' : (r_vis : Reg) ≠ r_node := by omega
  have hne_vp_reg' : (r_vis : Reg) ≠ r_par := by omega
  rcases hqstate with ⟨hq, hnodup, hlt_items, hvis_len, hpar_len, hvis_iff, hpar_lt⟩
  have hy_vis : y < (s.arrs a_vis).length := by rw [hvis_len]; exact hy_lt
  let vis_y := (s.arrs a_vis)[y]'hy_vis
  have hvy_le1 : vis_y ≤ 1 := (hvis_iff y hy_lt).2
  have hvy_w : vis_y < 2 ^ w := by omega
  let s₁ := s.setReg r_vis vis_y
  have hex_rd : Exec w (.assign r_vis (.read a_vis (.reg r_node))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hr_node, hy_w, hy_vis, vis_y, hvy_w])
  by_cases hy_mem : y ∈ items
  · -- Already visited: vis_y != 0
    have hvy_ne0 : vis_y ≠ 0 := (hvis_iff y hy_lt).1.mpr hy_mem
    have hcond : (Expr.reg r_vis).eval w s₁ = some vis_y := by
      simp [s₁, Expr.eval, checkWord, hvy_w]
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.write a_vis (.reg r_node) (.const 1))
          (.seq (.write a_parent (.reg r_node) (.reg r_par))
            (queuePush a_q r_tail (.reg r_node))))) s₁ s₁ 2 :=
      .ite_true hcond hvy_ne0 (.skip s₁)
    refine ⟨s₁, 3 + 2, [], .seq hex_rd hex_ite, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.append_nil]
      refine ⟨hq.of_eq rfl (by simp [s₁, State.setReg, hne_hv']) (by simp [s₁, State.setReg, hne_tv']),
        hnodup, hlt_items, hvis_len, hpar_len, hvis_iff, hpar_lt⟩
    · exact ⟨hpar_len, hpar_sound.2⟩
    · intro z
      simp only [List.append_nil, iff_self_or]
      rintro rfl
      exact hy_mem
    · intro a _ _ _
      rfl
    · intro r _ hr_vis
      simp [s₁, State.setReg, hr_vis]
  · -- Not yet visited: vis_y = 0
    have hvy_eq0 : vis_y = 0 := by
      by_contra hne
      exact hy_mem ((hvis_iff y hy_lt).1.mp hne)
    have hcond : (Expr.reg r_vis).eval w s₁ = some 0 := by
      simp [s₁, Expr.eval, checkWord, hvy_eq0, h0_w]
    -- 1. .write a_vis (.reg r_node) (.const 1)
    have hrn₁ : s₁.regs r_node = y := by simp [s₁, State.setReg, hne_vn'.symm, hr_node]
    have hrp₁ : s₁.regs r_par = x := by simp [s₁, State.setReg, hne_vp_reg'.symm, hr_par]
    let s₂ := s₁.writeArr a_vis y 1
    have hex_wvis : Exec w (.write a_vis (.reg r_node) (.const 1)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hrn₁, hy_w])
        (by simp [Expr.eval, checkWord, hw]) (by simp [s₁, hy_vis])
    -- 2. .write a_parent (.reg r_node) (.reg r_par)
    have hy_par : y < (s₂.arrs a_parent).length := by
      simp [s₂, s₁, hne_vp'.symm, hpar_len, hy_lt]
    let s₃ := s₂.writeArr a_parent y x
    have hex_wpar : Exec w (.write a_parent (.reg r_node) (.reg r_par)) s₂ s₃ 3 :=
      .write (by simp [s₂, Expr.eval, checkWord, hrn₁, hy_w])
        (by simp [s₂, Expr.eval, checkWord, hrp₁, hx_w]) hy_par
    -- 3. queuePush a_q r_tail (.reg r_node)
    have hq₃ : IsQueueHistory a_q r_head r_tail (2 * n) items headIdx s₃ :=
      hq.of_eq (by simp [s₃, s₂, s₁, hne_pq'.symm, hne_vq'.symm])
        (by simp [s₃, s₂, s₁, State.setReg, hne_hv'])
        (by simp [s₃, s₂, s₁, State.setReg, hne_tv'])
    have hitems_lt_2n : items.length < 2 * n :=
      length_lt_of_nodup_lt_not_mem hnodup hlt_items hy_lt hy_mem
    rcases Triple.queuePush_spec a_q r_head r_tail (.reg r_node) (2 * n) items headIdx y
        hne_ht hw h2n_w hitems_lt_2n s₃
        ⟨hq₃, by simp [s₃, s₂, Expr.eval, checkWord, hrn₁, hy_w]⟩ with
      ⟨s₄, t_push, hex_push, ht_push, hq₄⟩
    dsimp [Expr.cost] at ht_push
    have hex_else : Exec w (.seq (.write a_vis (.reg r_node) (.const 1))
        (.seq (.write a_parent (.reg r_node) (.reg r_par))
          (queuePush a_q r_tail (.reg r_node)))) s₁ s₄ (3 + (3 + t_push)) :=
      .seq hex_wvis (.seq hex_wpar hex_push)
    have hex_ite : Exec w (.ite (.reg r_vis) .skip
        (.seq (.write a_vis (.reg r_node) (.const 1))
          (.seq (.write a_parent (.reg r_node) (.reg r_par))
            (queuePush a_q r_tail (.reg r_node))))) s₁ s₄ (1 + (3 + (3 + t_push))) :=
      .ite_false hcond hex_else
    have hnot_push_vis : (a_vis : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_vq']
    have hnot_push_par : (a_parent : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
      simp [queuePush, Cmd.writtenArrs, hne_pq']
    have hvis₄ : s₄.arrs a_vis = (s.arrs a_vis).set y 1 := by
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_vis]
      simp [s₃, s₂, s₁, hne_vp']
    have hpar₄ : s₄.arrs a_parent = (s.arrs a_parent).set y x := by
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_push_par]
      simp [s₃, s₂, s₁, hne_vp'.symm]
    refine ⟨s₄, 3 + (1 + (3 + (3 + t_push))), [y], .seq hex_rd hex_ite, by omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨hq₄, hnodup.append (List.nodup_singleton y) ?_,
        fun z hz => by
          rw [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | rfl
          · exact hlt_items z hz
          · exact hy_lt,
        by simp [hvis₄, hvis_len],
        by simp [hpar₄, hpar_len],
        fun z hz => ?_,
        fun z hz => ?_⟩
      · intro a ha hb
        rw [List.mem_singleton] at hb
        subst hb
        exact hy_mem ha
      · simp only [hvis₄, List.mem_append, List.mem_singleton]
        by_cases hzy : z = y
        · subst hzy
          rw [List.getElem_set_self (by simp [hvis_len, hz])]
          exact ⟨by simp, le_rfl⟩
        · rw [List.getElem_set_ne (Ne.symm hzy)]
          rcases hvis_iff z hz with ⟨hiff, hle⟩
          exact ⟨by simp [hiff, hzy], hle⟩
      · simp only [hpar₄]
        by_cases hzy : z = y
        · subst hzy
          rw [List.getElem_set_self (by simp [hpar_len, hz])]
          exact hx_lt
        · rw [List.getElem_set_ne (Ne.symm hzy)]
          exact hpar_lt z hz
    · refine ⟨by simp [hpar₄, hpar_len], fun v u huv hget => ?_⟩
      simp only [hpar₄] at hget
      by_cases hvy : v.1 = y
      · simp only [hvy] at hget
        rw [List.getElem_set_self (by simp [hpar_len, hy_lt])] at hget
        exact hpar_edge v u hvy hget huv
      · rw [List.getElem_set_ne (Ne.symm hvy)] at hget
        exact hpar_sound.2 v u huv hget
    · intro z
      simp [List.mem_append]
    · intro a ha_vis ha_par ha_q
      have ha_q' : (a : Arr) ≠ a_q := ha_q
      have hnot_a : (a : Arr) ∉ (queuePush a_q r_tail (.reg r_node)).writtenArrs := by
        simp [queuePush, Cmd.writtenArrs, ha_q']
      rw [Exec.arrs_eq_of_not_mem_writtenArrs hex_push hnot_a]
      simp [s₃, s₂, s₁, show (a : Arr) ≠ a_parent from ha_par, show (a : Arr) ≠ a_vis from ha_vis]
    · intro r hr_tail hr_vis
      have hr_tail' : (r : Reg) ≠ r_tail := hr_tail
      have hnot_r : (r : Reg) ∉ (queuePush a_q r_tail (.reg r_node)).writtenRegs := by
        simp [queuePush, Cmd.writtenRegs, hr_tail']
      rw [Exec.regs_eq_of_not_mem_writtenRegs hex_push hnot_r]
      simp [s₃, s₂, s₁, State.setReg, show (r : Reg) ≠ r_vis from hr_vis]

/-! ### Section 5: Residual BFS, Augmentation, and `disjointPathsProg` -/

/-- Potential weight of a split node `z : Fin (2 * n)` in the residual BFS. -/
def resNodeWeight {n : ℕ} (lists : Fin n → List ℕ) (z : Fin (2 * n)) : ℕ :=
  if h : z.1 < n then 44 else 51 + 31 * (lists ⟨z.1 - n, by omega⟩).length

/-- Embedding of `Fin n` as in-nodes `< n` in `Fin (2 * n)`. -/
def inEmb (n : ℕ) : Fin n ↪ Fin (2 * n) :=
  ⟨inNode, fun u v h => Fin.ext (by simpa [inNode] using congrArg Fin.val h)⟩

@[simp] theorem inEmb_val {n : ℕ} (u : Fin n) : (inEmb n u).1 = u.1 := rfl

/-- Embedding of `Fin n` as out-nodes `≥ n` in `Fin (2 * n)`. -/
def outEmb (n : ℕ) : Fin n ↪ Fin (2 * n) :=
  ⟨outNode, fun u v h => Fin.ext (by have := congrArg Fin.val h; dsimp [outNode] at this; omega)⟩

@[simp] theorem outEmb_val {n : ℕ} (u : Fin n) : (outEmb n u).1 = u.1 + n := rfl

theorem sum_resNodeWeight_univ {n : ℕ} (lists : Fin n → List ℕ) :
    (∑ z : Fin (2 * n), resNodeWeight lists z) = 95 * n + 31 * totalAdjEntries lists := by
  have hdisj : Disjoint (Finset.univ.map (inEmb n)) (Finset.univ.map (outEmb n)) := by
    rw [Finset.disjoint_left]
    intro z hzin hzout
    rcases Finset.mem_map.mp hzin with ⟨u, _, rfl⟩
    rcases Finset.mem_map.mp hzout with ⟨v, _, heq⟩
    have hval := congrArg Fin.val heq
    simp only [inEmb_val, outEmb_val] at hval
    have := u.2
    omega
  have hunion : (Finset.univ : Finset (Fin (2 * n))) =
      Finset.univ.map (inEmb n) ∪ Finset.univ.map (outEmb n) := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, true_and, true_iff]
    by_cases hz : z.1 < n
    · exact Or.inl ⟨⟨z.1, hz⟩, Fin.ext rfl⟩
    · exact Or.inr ⟨⟨z.1 - n, by omega⟩, Fin.ext (by simp [outEmb_val]; omega)⟩
  rw [hunion, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map]
  have hsum_in : (∑ u : Fin n, resNodeWeight lists (inEmb n u)) = 44 * n := by
    have hcongr : ∀ u : Fin n, resNodeWeight lists (inEmb n u) = 44 := by
      intro u
      simp [resNodeWeight]
    simp [hcongr, mul_comm]
  have hsum_out : (∑ u : Fin n, resNodeWeight lists (outEmb n u)) =
      51 * n + 31 * totalAdjEntries lists := by
    have hcongr : ∀ u : Fin n, resNodeWeight lists (outEmb n u) = 51 + 31 * (lists u).length := by
      intro u
      have hnot_lt : ¬ (outEmb n u).1 < n := by
        simp only [outEmb_val]
        omega
      have hsub : (⟨(outEmb n u).1 - n, by omega⟩ : Fin n) = u := by
        ext
        simp [outEmb_val]
      simp only [resNodeWeight, hnot_lt, ↓reduceDIte, hsub]
    simp only [hcongr]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_comm n 51, ← Finset.mul_sum, totalAdjEntries]
  omega

theorem sum_resNodeWeight_pop {n : ℕ} (lists : Fin n → List ℕ)
    {items extra : List ℕ} {headIdx : ℕ}
    (hno : items.Nodup) (hhead : headIdx < items.length) (hx : items[headIdx] < 2 * n) :
    resNodeWeight lists ⟨items[headIdx], hx⟩ +
      (∑ z ∈ Finset.univ \ listFinset (2 * n) ((items ++ extra).take (headIdx + 1)),
        resNodeWeight lists z) =
      ∑ z ∈ Finset.univ \ listFinset (2 * n) (items.take headIdx), resNodeWeight lists z := by
  rw [sdiff_listFinset_take_succ_append Finset.univ hhead hx]
  have hmem : (⟨items[headIdx], hx⟩ : Fin (2 * n)) ∈
      Finset.univ \ listFinset (2 * n) (items.take headIdx) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, not_mem_listFinset_take_of_nodup hno hhead hx⟩
  exact Finset.add_sum_erase _ _ hmem

theorem sum_resNodeWeight_le_univ {n : ℕ} (lists : Fin n → List ℕ) (S : Finset (Fin (2 * n))) :
    (∑ z ∈ S, resNodeWeight lists z) ≤ 95 * n + 31 * totalAdjEntries lists := by
  calc
    (∑ z ∈ S, resNodeWeight lists z) ≤ ∑ z : Fin (2 * n), resNodeWeight lists z :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = 95 * n + 31 * totalAdjEntries lists := sum_resNodeWeight_univ lists

/-- Register and array conventions for `disjointPathsProg`:
- Arrays: `a_used = a_base`, `a_pred = a_base + 1`, `a_succ = a_base + 2`,
  `a_vis = a_base + 3`, `a_parent = a_base + 4`, `a_q = a_base + 5`.
- Registers: `r_head = r_base`, `r_tail = r_base + 1`, `r_x = r_base + 2`,
  `r_u = r_base + 3`, `r_k = r_base + 4`, `r_hi = r_base + 5`,
  `r_v = r_base + 6`, `r_vis = r_base + 7`, `r_succ = r_base + 8`,
  `r_round = r_base + 9`, `r_found = r_base + 10`, `r_target = r_base + 11`. -/
def initSourcesBody (a_A a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 7) (.read a_A (.reg (r_base + 3))))
    (.ite (.reg (r_base + 7))
      (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
        (.ite (.reg (r_base + 7))
          .skip
          (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
            (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3))))
      .skip)

/-- Initialize `a_vis`, `a_parent`, and queue pointers `r_head, r_tail`, then seed the queue with
all unsaturated source vertices in `A`. -/
def initSourcesProg (n : ℕ) (a_A a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (allocFillArr (a_base + 3) (.const (2 * n)) (.const 0) (r_base + 3))
    (.seq (allocFillArr (a_base + 4) (.const (2 * n)) (.const 0) (r_base + 3))
      (.seq (.assign r_base (.const 0))
        (.seq (.assign (r_base + 1) (.const 0))
          (.seq (.assign (r_base + 3) (.const 0))
            (forUp (r_base + 3) (.const n) (initSourcesBody a_A a_base r_base))))))

theorem initSourcesLoop_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (a_A a_base : ℕ) (r_base : ℕ)
    (ha_A : a_A < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {items : List ℕ} {s : State}
    (hA_len : (s.arrs a_A).length = n)
    (hA_bound : ∀ u : Fin n, (s.arrs a_A)[u.1]'(by rw [hA_len]; exact u.2) ≤ 1)
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s)
    (hqstate : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items 0 s)
    (hpar_sound : ParentEdgeSound G (a_base + 4) s)
    (hru : s.regs (r_base + 3) = k) :
    ∃ s' t items',
      Exec w (forUp (r_base + 3) (.const n) (initSourcesBody a_A a_base r_base)) s s' t ∧
      t ≤ 3 + 32 * rem ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items' 0 s' ∧
      ParentEdgeSound G (a_base + 4) s' ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing k items s with
  | zero =>
    have hru_n : s.regs (r_base + 3) = n := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.const n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_n, hn_w, h0_w]
    exact ⟨s, 3, items, .while_false hcond, by omega, hvalid, hqstate, hpar_sound,
      fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.const n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hk_w, hn_w, hk_lt, hw]
    have hk_A : k < (s.arrs a_A).length := by rw [hA_len]; exact hk_lt
    let valA := (s.arrs a_A)[k]'hk_A
    have hvalA_le : valA ≤ 1 := hA_bound ⟨k, hk_lt⟩
    have hvalA_w : valA < 2 ^ w := by omega
    let s₁ := s.setReg (r_base + 7) valA
    have hex_rdA : Exec w (.assign (r_base + 7) (.read a_A (.reg (r_base + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_A, valA, hvalA_w])
    -- Execute the ite on r_base + 7
    have hbody_step : ∃ s_b t_b items_b,
        Exec w (initSourcesBody a_A a_base r_base) s s_b t_b ∧
        t_b ≤ 25 ∧
        ValidPathState G a_base (a_base + 1) (a_base + 2) s_b ∧
        ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) items_b 0 s_b ∧
        ParentEdgeSound G (a_base + 4) s_b ∧
        s_b.regs (r_base + 3) = k ∧
        (∀ a < a_base + 3, s_b.arrs a = s.arrs a) := by
      by_cases hvalA_ne : valA ≠ 0
      · have hcondA : (Expr.reg (r_base + 7)).eval w s₁ = some valA := by
          simp [s₁, Expr.eval, checkWord, hvalA_w]
        have hu_len : (s.arrs a_base).length = n := hvalid.1
        have hk_u : k < (s.arrs a_base).length := by rw [hu_len]; exact hk_lt
        let valU := (s.arrs a_base)[k]'hk_u
        have hvalU_le : valU ≤ 1 := hvalid.2.2.2.1 ⟨k, hk_lt⟩
        have hvalU_w : valU < 2 ^ w := by omega
        let s₂ := s₁.setReg (r_base + 7) valU
        have hex_rdU : Exec w (.assign (r_base + 7) (.read a_base (.reg (r_base + 3)))) s₁ s₂ 3 :=
          .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hru, hk_w, hk_u, valU, hvalU_w])
        by_cases hvalU_ne : valU ≠ 0
        · have hcondU : (Expr.reg (r_base + 7)).eval w s₂ = some valU := by
            simp [s₂, Expr.eval, checkWord, hvalU_w]
          have hex_iteU : Exec w (.ite (.reg (r_base + 7)) .skip
              (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3))) s₂ s₂ 2 :=
            .ite_true hcondU hvalU_ne (.skip s₂)
          have hex_iteA : Exec w (.ite (.reg (r_base + 7))
              (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
                (.ite (.reg (r_base + 7)) .skip
                  (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                    (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3)))) .skip) s₁ s₂ 6 :=
            .ite_true hcondA hvalA_ne (.seq hex_rdU hex_iteU)
          refine ⟨s₂, 3 + 6, items, .seq hex_rdA hex_iteA, by omega, hvalid, ?_, hpar_sound,
            by simp [s₂, s₁, State.setReg, hru],
            fun _ _ => rfl⟩
          rcases hqstate with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          exact ⟨hq.of_eq rfl
            (by simp [s₂, s₁, State.setReg])
            (by simp [s₂, s₁, State.setReg]),
            hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
        · have hvalU_eq0 : valU = 0 := by omega
          have hcondU : (Expr.reg (r_base + 7)).eval w s₂ = some 0 := by
            simp [s₂, Expr.eval, checkWord, hvalU_eq0, h0_w]
          have hq₂ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) items 0 s₂ := by
            rcases hqstate with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
            exact ⟨hq.of_eq rfl
              (by simp [s₂, s₁, State.setReg])
              (by simp [s₂, s₁, State.setReg]),
              hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          have hru₂ : s₂.regs (r_base + 3) = k := by
            simp [s₂, s₁, State.setReg, hru]
          rcases tryPushReg_exec G (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              hw h2n_w hq₂ hpar_sound hru₂ (by omega) hru₂ (by omega)
              (fun v u _ hget _ => by omega) with
            ⟨s₃, t_push, extra, hex_push, ht_push, hq₃, hpar₃, _, harr₃, hreg₃⟩
          have hex_iteU : Exec w (.ite (.reg (r_base + 7)) .skip
              (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3))) s₂ s₃ (1 + t_push) :=
            .ite_false hcondU hex_push
          have hex_iteA : Exec w (.ite (.reg (r_base + 7))
              (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
                (.ite (.reg (r_base + 7)) .skip
                  (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                    (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3)))) .skip)
              s₁ s₃ (1 + (3 + (1 + t_push))) :=
            .ite_true hcondA hvalA_ne (.seq hex_rdU hex_iteU)
          refine ⟨s₃, 3 + (1 + (3 + (1 + t_push))), items ++ extra,
            .seq hex_rdA hex_iteA, by omega,
            hvalid.of_arrs_eq (harr₃ a_base (by omega) (by omega) (by omega))
              (harr₃ (a_base + 1) (by omega) (by omega) (by omega))
              (harr₃ (a_base + 2) (by omega) (by omega) (by omega)),
            hq₃, hpar₃,
            by rw [hreg₃ (r_base + 3) (by omega) (by omega)]; exact hru₂,
            fun a ha => harr₃ a (by omega) (by omega) (by omega)⟩
      · have hvalA_eq0 : valA = 0 := by omega
        have hcondA : (Expr.reg (r_base + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hvalA_eq0, h0_w]
        have hex_iteA : Exec w (.ite (.reg (r_base + 7))
            (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
              (.ite (.reg (r_base + 7)) .skip
                (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                  (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 3)))) .skip) s₁ s₁ 2 :=
          .ite_false hcondA (.skip s₁)
        refine ⟨s₁, 3 + 2, items, .seq hex_rdA hex_iteA, by omega, hvalid, ?_, hpar_sound,
          by simp [s₁, State.setReg, hru],
          fun _ _ => rfl⟩
        rcases hqstate with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
        exact ⟨hq.of_eq rfl
          (by simp [s₁, State.setReg])
          (by simp [s₁, State.setReg]),
          hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
    rcases hbody_step with ⟨s_b, t_b, items_b, hex_b, ht_b, hvalid_b, hq_b, hpar_b, hru_b, harr_b⟩
    have hinc : (Expr.op .add (.reg (r_base + 3)) (.const 1)).eval w s_b = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_b, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s_next := s_b.setReg (r_base + 3) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
        s_b s_next 4 := .assign hinc
    have hq_next : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items_b 0 s_next := by
      rcases hq_b with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
      exact ⟨hq.of_eq rfl
        (by simp [s_next, State.setReg])
        (by simp [s_next, State.setReg]),
        hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
    have hA_eq : s_next.arrs a_A = s.arrs a_A := harr_b a_A (by omega)
    rcases ih (k + 1) (by omega) (s := s_next) (by rw [hA_eq]; exact hA_len)
        (fun u => by simp only [hA_eq]; exact hA_bound u)
        hvalid_b hq_next hpar_b (by simp [s_next]) with
      ⟨s_end, t_end, items_end, hex_end, ht_end, hvalid_end, hq_end, hpar_end, harr_end⟩
    refine ⟨s_end, 3 + (t_b + 4) + t_end, items_end,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex_end,
      by omega, hvalid_end, hq_end, hpar_end,
      fun a ha => by rw [harr_end a ha]; exact harr_b a ha⟩

theorem initSourcesProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (a_A a_base : ℕ) (r_base : ℕ)
    (ha_A : a_A < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {s : State}
    (hA_len : (s.arrs a_A).length = n)
    (hA_bound : ∀ u : Fin n, (s.arrs a_A)[u.1]'(by rw [hA_len]; exact u.2) ≤ 1)
    (hq_len : (s.arrs (a_base + 5)).length = 2 * n)
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s) :
    ∃ s' t items,
      Exec w (initSourcesProg n a_A a_base r_base) s s' t ∧
      t ≤ 84 * n + 23 ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items 0 s' ∧
      ParentEdgeSound G (a_base + 4) s' ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) ∧
      s'.regs (r_base + 9) = s.regs (r_base + 9) ∧
      s'.regs (r_base + 10) = s.regs (r_base + 10) := by
  have h0_w : 0 < 2 ^ w := by omega
  -- 1. allocFillArr (a_base + 3) (.const (2 * n)) (.const 0) (r_base + 3)
  rcases Triple.allocFillArr_const (a_base + 3) (2 * n) 0 (r_base + 3) hw h2n_w h0_w s trivial with
    ⟨s₁, t₁, hex₁, ht₁, harr_vis₁⟩
  dsimp only at ht₁
  -- 2. allocFillArr (a_base + 4) (.const (2 * n)) (.const 0) (r_base + 3)
  rcases Triple.allocFillArr_const (a_base + 4) (2 * n) 0 (r_base + 3) hw h2n_w h0_w s₁ trivial with
    ⟨s₂, t₂, hex₂, ht₂, harr_par₂⟩
  dsimp only at ht₂
  have hnot2_vis : (a_base + 3 : Arr) ∉
      (allocFillArr (a_base + 4) (.const (2 * n)) (.const 0) (r_base + 3)).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs]
  have harr_vis₂ : s₂.arrs (a_base + 3) = List.replicate (2 * n) 0 := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2_vis, harr_vis₁]
  have harr_lt₂ : ∀ a < a_base + 3, s₂.arrs a = s.arrs a := by
    intro a ha
    have hnot1 : (a : Arr) ∉
        (allocFillArr (a_base + 3) (.const (2 * n)) (.const 0) (r_base + 3)).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, show (a : Arr) ≠ a_base + 3 by omega]
    have hnot2 : (a : Arr) ∉
        (allocFillArr (a_base + 4) (.const (2 * n)) (.const 0) (r_base + 3)).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, show (a : Arr) ≠ a_base + 4 by omega]
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2,
      Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1]
  have hnot1_q : (a_base + 5 : Arr) ∉
      (allocFillArr (a_base + 3) (.const (2 * n)) (.const 0) (r_base + 3)).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs]
  have hnot2_q : (a_base + 5 : Arr) ∉
      (allocFillArr (a_base + 4) (.const (2 * n)) (.const 0) (r_base + 3)).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs]
  have hq_len₂ : (s₂.arrs (a_base + 5)).length = 2 * n := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2_q,
      Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1_q, hq_len]
  -- 3. .assign r_base (.const 0), .assign (r_base + 1) (.const 0), .assign (r_base + 3) (.const 0)
  let s₃ := s₂.setReg r_base 0
  have hex₃ : Exec w (.assign r_base (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setReg (r_base + 1) 0
  have hex₄ : Exec w (.assign (r_base + 1) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg (r_base + 3) 0
  have hex₅ : Exec w (.assign (r_base + 3) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hqstate₅ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) [] 0 s₅ := by
    refine ⟨⟨by simp [s₅, s₄, s₃, hq_len₂], Nat.zero_le _,
      by simp [s₅, s₄, s₃, State.setReg],
      by simp [s₅, s₄, State.setReg],
      le_rfl, fun i hi => by simp at hi⟩,
      List.nodup_nil, fun x hx => by simp at hx,
      by simp [s₅, s₄, s₃, harr_vis₂],
      by simp [s₅, s₄, s₃, harr_par₂],
      fun x hx => by simp [s₅, s₄, s₃, harr_vis₂],
      fun x hx => by simp [s₅, s₄, s₃, harr_par₂]; omega⟩
  have hpar₅ : ParentEdgeSound G (a_base + 4) s₅ := by
    refine ⟨by simp [s₅, s₄, s₃, harr_par₂], fun v u _ hget => ?_⟩
    simp only [s₅, s₄, s₃, State.setReg_arrs, harr_par₂, List.getElem_replicate] at hget
    have := v.2
    omega
  have hvalid₅ : ValidPathState G a_base (a_base + 1) (a_base + 2) s₅ :=
    hvalid.of_arrs_eq (harr_lt₂ a_base (by omega))
      (harr_lt₂ (a_base + 1) (by omega)) (harr_lt₂ (a_base + 2) (by omega))
  have hA₅ : s₅.arrs a_A = s.arrs a_A := harr_lt₂ a_A (by omega)
  rcases initSourcesLoop_exec G a_A a_base r_base ha_A hw h2n_w n 0 (by omega)
      (by rw [hA₅]; exact hA_len) (fun u => by simp only [hA₅]; exact hA_bound u)
      hvalid₅ hqstate₅ hpar₅ (by simp [s₅]) with
    ⟨s₆, t₆, items, hex₆, ht₆, hvalid₆, hq₆, hpar₆, harr₆⟩
  have hex_all : Exec w (initSourcesProg n a_A a_base r_base) s s₆
      (t₁ + (t₂ + (2 + (2 + (2 + t₆))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))
  have hnot_r9 : (r_base + 9 : Reg) ∉ (initSourcesProg n a_A a_base r_base).writtenRegs := by
    simp [initSourcesProg, initSourcesBody, tryPushReg, queuePush, allocFillArr, fillArr,
      forUp, Cmd.writtenRegs]
  have hnot_r10 : (r_base + 10 : Reg) ∉ (initSourcesProg n a_A a_base r_base).writtenRegs := by
    simp [initSourcesProg, initSourcesBody, tryPushReg, queuePush, allocFillArr, fillArr,
      forUp, Cmd.writtenRegs]
  refine ⟨s₆, t₁ + (t₂ + (2 + (2 + (2 + t₆)))), items, hex_all, by omega,
    hvalid₆, hq₆, hpar₆,
    fun a ha => by rw [harr₆ a ha]; exact harr_lt₂ a ha,
    Exec.regs_eq_of_not_mem_writtenRegs hex_all hnot_r9,
    Exec.regs_eq_of_not_mem_writtenRegs hex_all hnot_r10⟩

/-- One step of the residual BFS queue loop on the `2n`-vertex split graph. -/
def resBfsStepProg (n : ℕ) (a_start a_end a_entries a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (queuePop (a_base + 5) r_base (r_base + 2))
    (.ite (.op .lt (.reg (r_base + 2)) (.const n))
      -- In-node x < n
      (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 2))))
        (.ite (.reg (r_base + 7))
          -- used[x] != 0: check pred[x] < n
          (.seq (.assign (r_base + 3) (.read (a_base + 1) (.reg (r_base + 2))))
            (.ite (.op .lt (.reg (r_base + 3)) (.const n))
              (.seq (.assign (r_base + 6) (.op .add (.reg (r_base + 3)) (.const n)))
                (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                  (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))
              .skip))
          -- used[x] == 0: push x + n
          (.seq (.assign (r_base + 6) (.op .add (.reg (r_base + 2)) (.const n)))
            (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
              (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))))
      -- Out-node x >= n (u = x - n)
      (.seq (.assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.const n)))
        (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
          (.seq (.ite (.reg (r_base + 7))
              (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 2))
              .skip)
            (.seq (.assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3))))
              (forList a_start a_end a_entries (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6)
                (.ite (.op .eq (.reg (r_base + 6)) (.reg (r_base + 8)))
                  .skip
                  (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                    (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))))))))

/-- The residual BFS `while` loop (`while r_head < r_tail`). -/
def resBfsLoopProg (n : ℕ) (a_start a_end a_entries a_base : Arr) (r_base : Reg) : Cmd :=
  .while (.op .lt (.reg r_base) (.reg (r_base + 1)))
    (resBfsStepProg n a_start a_end a_entries a_base r_base)

theorem resBfsStepProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_base : ℕ) (r_base : ℕ)
    (ha_start : a_start < a_base) (ha_end : a_end < a_base) (ha_ent : a_entries < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s)
    (hqstate : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items headIdx s)
    (hpar_sound : ParentEdgeSound G (a_base + 4) s)
    (hhead : headIdx < items.length) :
    ∃ s' t extra,
      Exec w (resBfsStepProg n a_start a_end a_entries a_base r_base) s s' t ∧
      t + 3 ≤ resNodeWeight lists ⟨items[headIdx], hqstate.2.2.1 items[headIdx] (List.getElem_mem hhead)⟩ ∧
      IsAdjList G a_start a_end a_entries lists s' ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) (items ++ extra) (headIdx + 1) s' ∧
      ParentEdgeSound G (a_base + 4) s' ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let x := items[headIdx]
  have hx_lt : x < 2 * n := hqstate.2.2.1 x (List.getElem_mem hhead)
  have hx_w : x < 2 ^ w := by omega
  -- 1. queuePop (a_base + 5) r_base (r_base + 2)
  rcases Triple.queuePop_spec (a_base + 5) r_base (r_base + 1) (r_base + 2) (2 * n) items headIdx
      (by omega) (by omega) (by omega) hw h2n_w hhead hx_w s hqstate.1 with
    ⟨s₁, t_pop, hex_pop, ht_pop, hq₁, hrx₁⟩
  change s₁.regs (r_base + 2) = x at hrx₁
  dsimp only at ht_pop
  have hnot_pop_arr : ∀ a : Arr, s₁.arrs a = s.arrs a :=
    fun a => Exec.arrs_eq_of_not_mem_writtenArrs hex_pop (by simp [queuePop, Cmd.writtenArrs])
  have hqstate₁ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items (headIdx + 1) s₁ := by
    rcases hqstate with ⟨_, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
    exact ⟨hq₁, hno, hlt_it,
      by rw [hnot_pop_arr]; exact hv_len,
      by rw [hnot_pop_arr]; exact hp_len,
      fun z hz => by simp only [hnot_pop_arr]; exact hv_iff z hz,
      fun z hz => by simp only [hnot_pop_arr]; exact hp_lt z hz⟩
  have hpar₁ : ParentEdgeSound G (a_base + 4) s₁ := by
    rcases hpar_sound with ⟨hp_len, hp_adj⟩
    exact ⟨by rw [hnot_pop_arr]; exact hp_len,
      fun v u huv hget => by simp only [hnot_pop_arr] at hget; exact hp_adj v u huv hget⟩
  by_cases hx_n : x < n
  · -- Branch x < n
    have hcond_x : (Expr.op .lt (.reg (r_base + 2)) (.const n)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hx_w, hn_w, hx_n, hw]
    have hu_len : (s₁.arrs a_base).length = n := by rw [hnot_pop_arr]; exact hvalid.1
    have hx_u : x < (s₁.arrs a_base).length := by rw [hu_len]; exact hx_n
    let valU := (s₁.arrs a_base)[x]'hx_u
    have hvalU_le : valU ≤ 1 := by
      simp only [valU, hnot_pop_arr]
      exact hvalid.2.2.2.1 ⟨x, hx_n⟩
    have hvalU_w : valU < 2 ^ w := by omega
    let s₂ := s₁.setReg (r_base + 7) valU
    have hex_rdU : Exec w (.assign (r_base + 7) (.read a_base (.reg (r_base + 2)))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrx₁, hx_w, hx_u, valU, hvalU_w])
    have hrx₂ : s₂.regs (r_base + 2) = x := by
      simp [s₂, State.setReg, hrx₁]
    have hqstate₂ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items (headIdx + 1) s₂ := by
      rcases hqstate₁ with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
      exact ⟨hq.of_eq rfl
        (by simp [s₂, State.setReg])
        (by simp [s₂, State.setReg]),
        hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
    by_cases hvalU_ne : valU ≠ 0
    · -- used[x] != 0: check pred[x] < n
      have hcondU : (Expr.reg (r_base + 7)).eval w s₂ = some valU := by
        simp [s₂, Expr.eval, checkWord, hvalU_w]
      have hp_len : (s₂.arrs (a_base + 1)).length = n := by
        simp only [s₂, State.setReg_arrs, hnot_pop_arr]
        exact hvalid.2.1
      have hx_p : x < (s₂.arrs (a_base + 1)).length := by rw [hp_len]; exact hx_n
      let valP := (s₂.arrs (a_base + 1))[x]'hx_p
      have hvalP_le : valP ≤ n := by
        simp only [valP, s₂, State.setReg_arrs, hnot_pop_arr]
        exact hvalid.2.2.2.2.1 ⟨x, hx_n⟩
      have hvalP_w : valP < 2 ^ w := by omega
      let s₃ := s₂.setReg (r_base + 3) valP
      have hex_rdP : Exec w (.assign (r_base + 3) (.read (a_base + 1) (.reg (r_base + 2)))) s₂ s₃ 3 :=
        .assign (by simp [Expr.eval, checkWord, hrx₂, hx_w, hx_p, valP, hvalP_w])
      have hrx₃ : s₃.regs (r_base + 2) = x := by
        simp [s₃, State.setReg, hrx₂]
      have hqstate₃ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) items (headIdx + 1) s₃ := by
        rcases hqstate₂ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
        exact ⟨hq.of_eq rfl
          (by simp [s₃, State.setReg])
          (by simp [s₃, State.setReg]),
          hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
      by_cases hvalP_lt : valP < n
      · have hcondP : (Expr.op .lt (.reg (r_base + 3)) (.const n)).eval w s₃ = some 1 := by
          simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvalP_w, hn_w, hvalP_lt, hw]
        have hpn_w : valP + n < 2 ^ w := by omega
        let s₄ := s₃.setReg (r_base + 6) (valP + n)
        have hex_addP : Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 3)) (.const n))) s₃ s₄ 4 :=
          .assign (by simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvalP_w, hn_w, hpn_w])
        have hqstate₄ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) items (headIdx + 1) s₄ := by
          rcases hqstate₃ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
          exact ⟨hq.of_eq rfl
            (by simp [s₄, State.setReg])
            (by simp [s₄, State.setReg]),
            hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
        have hrx₄ : s₄.regs (r_base + 2) = x := by
          simp [s₄, State.setReg, hrx₃]
        rcases tryPushReg_exec G (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw h2n_w (y := valP + n) hqstate₄ hpar₁ (by simp [s₄]) (by omega) hrx₄ hx_lt
            (fun v u hvy _ _ => by have := v.2; omega) with
          ⟨s₅, t_push, extra, hex_push, ht_push, hq₅, hpar₅, _, harr₅, _⟩
        have harr_lt₅ : ∀ a < a_base + 3, s₅.arrs a = s.arrs a := by
          intro a ha
          rw [harr₅ a (by omega) (by omega) (by omega)]
          exact hnot_pop_arr a
        refine ⟨s₅, t_pop + (3 + (3 + (1 + (3 + (3 + (4 + t_push)))))), extra,
          .seq hex_pop (.ite_true hcond_x (by omega) (.seq hex_rdU
            (.ite_true hcondU hvalU_ne (.seq hex_rdP
              (.ite_true hcondP (by omega) (.seq hex_addP hex_push)))))),
          by simp [resNodeWeight, show items[headIdx] < n from hx_n]; omega,
          hadj.of_arrs_eq (harr_lt₅ a_start (by omega))
            (harr_lt₅ a_end (by omega)) (harr_lt₅ a_entries (by omega)),
          hvalid.of_arrs_eq (harr_lt₅ a_base (by omega))
            (harr_lt₅ (a_base + 1) (by omega)) (harr_lt₅ (a_base + 2) (by omega)),
          hq₅, hpar₅, harr_lt₅⟩
      · have hcondP : (Expr.op .lt (.reg (r_base + 3)) (.const n)).eval w s₃ = some 0 := by
          simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvalP_w, hn_w, hvalP_lt, h0_w]
        refine ⟨s₃, t_pop + (3 + (3 + (1 + (3 + 4)))), [],
          .seq hex_pop (.ite_true hcond_x (by omega) (.seq hex_rdU
            (.ite_true hcondU hvalU_ne (.seq hex_rdP (.ite_false hcondP (.skip s₃)))))),
          by simp [resNodeWeight, show items[headIdx] < n from hx_n]; omega,
          hadj.of_arrs_eq (hnot_pop_arr a_start) (hnot_pop_arr a_end) (hnot_pop_arr a_entries),
          hvalid.of_arrs_eq (hnot_pop_arr a_base) (hnot_pop_arr (a_base + 1)) (hnot_pop_arr (a_base + 2)),
          by simpa using hqstate₃, hpar₁, fun a _ => hnot_pop_arr a⟩
    · -- used[x] == 0: push x + n
      have hvalU_eq0 : valU = 0 := by omega
      have hcondU : (Expr.reg (r_base + 7)).eval w s₂ = some 0 := by
        simp [s₂, Expr.eval, checkWord, hvalU_eq0, h0_w]
      have hxn_w : x + n < 2 ^ w := by omega
      let s₃ := s₂.setReg (r_base + 6) (x + n)
      have hex_addX : Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 2)) (.const n))) s₂ s₃ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₂, hx_w, hn_w, hxn_w])
      have hqstate₃ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) items (headIdx + 1) s₃ := by
        rcases hqstate₂ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
        exact ⟨hq.of_eq rfl
          (by simp [s₃, State.setReg])
          (by simp [s₃, State.setReg]),
          hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
      have hrx₃ : s₃.regs (r_base + 2) = x := by
        simp [s₃, State.setReg, hrx₂]
      rcases tryPushReg_exec G (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          hw h2n_w (y := x + n) hqstate₃ hpar₁ (by simp [s₃]) (by omega) hrx₃ hx_lt
          (fun v u hvy _ _ => by have := v.2; omega) with
        ⟨s₄, t_push, extra, hex_push, ht_push, hq₄, hpar₄, _, harr₄, _⟩
      have harr_lt₄ : ∀ a < a_base + 3, s₄.arrs a = s.arrs a := by
        intro a ha
        rw [harr₄ a (by omega) (by omega) (by omega)]
        exact hnot_pop_arr a
      refine ⟨s₄, t_pop + (3 + (3 + (1 + (4 + t_push)))), extra,
        .seq hex_pop (.ite_true hcond_x (by omega) (.seq hex_rdU
          (.ite_false hcondU (.seq hex_addX hex_push)))),
        by simp [resNodeWeight, show items[headIdx] < n from hx_n]; omega,
        hadj.of_arrs_eq (harr_lt₄ a_start (by omega))
          (harr_lt₄ a_end (by omega)) (harr_lt₄ a_entries (by omega)),
        hvalid.of_arrs_eq (harr_lt₄ a_base (by omega))
          (harr_lt₄ (a_base + 1) (by omega)) (harr_lt₄ (a_base + 2) (by omega)),
        hq₄, hpar₄, harr_lt₄⟩
  · -- Branch x >= n (u = x - n < n)
    have hcond_x : (Expr.op .lt (.reg (r_base + 2)) (.const n)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hx_w, hn_w, hx_n, h0_w]
    let u := x - n
    have hu_lt : u < n := by omega
    have hu_w : u < 2 ^ w := by omega
    -- 1. .assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.const n))
    let s₂ := s₁.setReg (r_base + 3) u
    have hex_sub : Exec w (.assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.const n))) s₁ s₂ 4 :=
      .assign (by
        have hsub_w : x - n < 2 ^ w := hu_w
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hx_w, hn_w, hsub_w]
        rfl)
    -- 2. .assign (r_base + 7) (.read a_base (.reg (r_base + 3)))
    have hu_len : (s₂.arrs a_base).length = n := by
      simp only [s₂, State.setReg_arrs, hnot_pop_arr]; exact hvalid.1
    have hu_idx : u < (s₂.arrs a_base).length := by rw [hu_len]; exact hu_lt
    let valU := (s₂.arrs a_base)[u]'hu_idx
    have hvalU_le : valU ≤ 1 := by
      simp only [valU, s₂, State.setReg_arrs, hnot_pop_arr]
      exact hvalid.2.2.2.1 ⟨u, hu_lt⟩
    have hvalU_w : valU < 2 ^ w := by omega
    have hru₂ : s₂.regs (r_base + 3) = u := by simp [s₂]
    let s₃ := s₂.setReg (r_base + 7) valU
    have hex_rdU : Exec w (.assign (r_base + 7) (.read a_base (.reg (r_base + 3)))) s₂ s₃ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru₂, hu_w, hu_idx, valU, hvalU_w])
    have hrx₃ : s₃.regs (r_base + 2) = x := by
      simp [s₃, s₂, State.setReg, hrx₁]
    have hru₃ : s₃.regs (r_base + 3) = u := by
      simp [s₃, s₂, State.setReg]
    have hqstate₃ : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items (headIdx + 1) s₃ := by
      rcases hqstate₁ with ⟨hq, hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
      exact ⟨hq.of_eq rfl
        (by simp [s₃, s₂, State.setReg])
        (by simp [s₃, s₂, State.setReg]),
        hno, hlt_it, hv_len, hpar_len, hv_iff, hp_lt⟩
    -- 3. ite on r_base + 7 (push u if used[u] != 0)
    have hback_step : ∃ s₄ t_back extra₁,
        Exec w (.ite (.reg (r_base + 7))
          (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
            (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 2))
          .skip) s₃ s₄ t_back ∧
        t_back ≤ 18 ∧
        ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) (items ++ extra₁) (headIdx + 1) s₄ ∧
        ParentEdgeSound G (a_base + 4) s₄ ∧
        s₄.regs (r_base + 2) = x ∧
        s₄.regs (r_base + 3) = u ∧
        (∀ a < a_base + 3, s₄.arrs a = s.arrs a) := by
      by_cases hvalU_ne : valU ≠ 0
      · have hcondU : (Expr.reg (r_base + 7)).eval w s₃ = some valU := by
          simp [s₃, Expr.eval, checkWord, hvalU_w]
        rcases tryPushReg_exec G (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) (r_base + 7) (r_base + 3) (r_base + 2)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)
            hw h2n_w hqstate₃ hpar₁ hru₃ (by omega) hrx₃ hx_lt
            (fun v u' hvy hxu huv => by
              have hveq : u' = v := Fin.ext (by omega)
              exact absurd hveq huv) with
          ⟨s₄, t_push, extra₁, hex_push, ht_push, hq₄, hpar₄, _, harr₄, hreg₄⟩
        refine ⟨s₄, 1 + t_push, extra₁, .ite_true hcondU hvalU_ne hex_push, by omega,
          hq₄, hpar₄,
          by rw [hreg₄ (r_base + 2) (by omega) (by omega)]; exact hrx₃,
          by rw [hreg₄ (r_base + 3) (by omega) (by omega)]; exact hru₃,
          fun a ha => by rw [harr₄ a (by omega) (by omega) (by omega)]; exact hnot_pop_arr a⟩
      · have hvalU_eq0 : valU = 0 := by omega
        have hcondU : (Expr.reg (r_base + 7)).eval w s₃ = some 0 := by
          simp [s₃, Expr.eval, checkWord, hvalU_eq0, h0_w]
        refine ⟨s₃, 2, [], .ite_false hcondU (.skip s₃), by omega,
          by simpa using hqstate₃, hpar₁, hrx₃, hru₃,
          fun a _ => hnot_pop_arr a⟩
    rcases hback_step with ⟨s₄, t_back, extra₁, hex_back, ht_back, hq₄, hpar₄, hrx₄, hru₄, harr₄⟩
    -- 4. .assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3)))
    have hs_len₄ : (s₄.arrs (a_base + 2)).length = n := by
      rw [harr₄ (a_base + 2) (by omega)]; exact hvalid.2.2.1
    have hu_s₄ : u < (s₄.arrs (a_base + 2)).length := by rw [hs_len₄]; exact hu_lt
    let valS := (s₄.arrs (a_base + 2))[u]'hu_s₄
    have hvalS_le : valS ≤ n := by
      simp only [valS, harr₄ (a_base + 2) (by omega)]
      exact hvalid.2.2.2.2.2.1 ⟨u, hu_lt⟩
    have hvalS_w : valS < 2 ^ w := by omega
    let s₅ := s₄.setReg (r_base + 8) valS
    have hex_rdS : Exec w (.assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3)))) s₄ s₅ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru₄, hu_w, hu_s₄, valS, hvalS_w])
    -- 5. forList over neighbors of u
    let uFin : Fin n := ⟨u, hu_lt⟩
    have hadj₅ : IsAdjList G a_start a_end a_entries lists s₅ :=
      hadj.of_arrs_eq (harr₄ a_start (by omega)) (harr₄ a_end (by omega)) (harr₄ a_entries (by omega))
    obtain ⟨st_u, en_u, hlist_u⟩ := hadj₅.1.2.2 uFin
    obtain ⟨hmem_lt_u, _, _, hadj_iff_u⟩ := hadj₅.2 uFin
    have hen_w : en_u < 2 ^ w := by
      rcases hlist_u with ⟨_, _, hen_ent, _, _, _, _, _⟩
      have hent₅ : s₅.arrs a_entries = s.arrs a_entries := harr₄ a_entries (by omega)
      rw [hent₅] at hen_ent
      omega
    let InnerInv (j : ℕ) (st : State) : Prop :=
      IsListAt a_start a_end a_entries u st_u en_u (lists uFin) st ∧
      st.regs (r_base + 2) = x ∧
      st.regs (r_base + 3) = u ∧
      st.regs (r_base + 8) = valS ∧
      (∀ a < a_base + 3, st.arrs a = s.arrs a) ∧
      ∃ extra₂ : List ℕ,
        ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
          r_base (r_base + 1) (items ++ extra₁ ++ extra₂) (headIdx + 1) st ∧
        ParentEdgeSound G (a_base + 4) st
    have hInner₀ : InnerInv 0 s₅ := by
      refine ⟨hlist_u,
        by simp [s₅, State.setReg, hrx₄],
        by simp [s₅, State.setReg, hru₄],
        by simp [s₅], harr₄, [],
        by
          rcases hq₄ with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          simpa using ⟨hq.of_eq rfl
            (by simp [s₅, State.setReg])
            (by simp [s₅, State.setReg]),
            hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩,
        hpar₄⟩
    have hforList :
        ⦃InnerInv 0⦄[w]
          forList a_start a_end a_entries (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6)
            (.ite (.op .eq (.reg (r_base + 6)) (.reg (r_base + 8)))
              .skip
              (tryPushReg (a_base + 3) (a_base + 4) (a_base + 5)
                (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)))
        ⦃InnerInv (lists uFin).length⦄ ≤
          fun _ => 9 + (lists uFin).length * (10 + 21) := by
      apply Triple.forList_const a_start a_end a_entries
        (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6)
        u st_u en_u (lists uFin) InnerInv 21 _
        (by omega) (by omega) hw hu_w hen_w
      · intro z hz
        have := hmem_lt_u z hz
        omega
      · intro st₀ ⟨hlist₀, hrx₀, hru₀, hrs₀, harr₀, extra₂, hq₀, hpar₀⟩
        refine ⟨hlist₀, hru₀, hlist₀,
          by simp [State.setReg, hrx₀],
          by simp [State.setReg, hru₀],
          by simp [State.setReg, hrs₀],
          harr₀, extra₂,
          by
            rcases hq₀ with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
            exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
              hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩,
          hpar₀⟩
      · intro j _ st_j ⟨hlist_j, _, _, _, _, _⟩
        exact hlist_j
      · intro j hj sb_v ⟨sb, ⟨hlist_b, hrx_b, hru_b, hrs_b, harr_b, extra₂, hq_b, hpar_b⟩,
          hsb_v, hrk_b, hrhi_b⟩
        subst hsb_v
        let v_val := (lists uFin)[j]
        have hv_mem : v_val ∈ lists uFin := List.getElem_mem hj
        have hv_lt_n : v_val < n := hmem_lt_u v_val hv_mem
        have hv_w : v_val < 2 ^ w := by omega
        have hadj_uv : G.Adj uFin ⟨v_val, hv_lt_n⟩ := (hadj_iff_u ⟨v_val, hv_lt_n⟩).mp hv_mem
        have hrv_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 6) = v_val := by
          simp [State.setReg]
        have hrx_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 2) = x := by
          simp [State.setReg, hrx_b]
        have hrk_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 4) = st_u + j := by
          simp [State.setReg, hrk_b]
        have hrhi_v : (sb.setReg (r_base + 6) v_val).regs (r_base + 5) = en_u := by
          simp [State.setReg, hrhi_b]
        have hq_v : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
            r_base (r_base + 1) (items ++ extra₁ ++ extra₂) (headIdx + 1)
            (sb.setReg (r_base + 6) v_val) := by
          rcases hq_b with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
            hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
        by_cases heq_vs : v_val = valS
        · have hcond_vs : (Expr.op .eq (.reg (r_base + 6)) (.reg (r_base + 8))).eval w
              (sb.setReg (r_base + 6) v_val) = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, State.setReg, hrs_b, heq_vs, hvalS_w, hw]
          have hq_next : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) (items ++ extra₁ ++ extra₂) (headIdx + 1)
              ((sb.setReg (r_base + 6) v_val).setReg (r_base + 4) (st_u + (j + 1))) := by
            rcases hq_b with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
            exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
              hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          refine ⟨sb.setReg (r_base + 6) v_val, 4,
            .ite_true hcond_vs (by omega) (.skip _), show 4 ≤ 21 by omega,
            ⟨hlist_b,
              by simp [State.setReg, hrx_b],
              by simp [State.setReg, hru_b],
              by simp [State.setReg, hrs_b],
              harr_b, extra₂, hq_next, hpar_b⟩,
            hrk_v, hrhi_v⟩
        · have hcond_vs : (Expr.op .eq (.reg (r_base + 6)) (.reg (r_base + 8))).eval w
              (sb.setReg (r_base + 6) v_val) = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, State.setReg, hrs_b, hv_w, hvalS_w, heq_vs, h0_w]
          rcases tryPushReg_exec G (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) (r_base + 7) (r_base + 6) (r_base + 2)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              hw h2n_w hq_v hpar_b hrv_v (by omega) hrx_v hx_lt
              (fun v' u' hvy hxu _ => by
                have hv_eq : v' = ⟨v_val, hv_lt_n⟩ := Fin.ext hvy
                have huFin_val : uFin.1 = x - n := rfl
                have hu_eq : u' = uFin := Fin.ext (by omega)
                rw [hu_eq, hv_eq]
                exact hadj_uv) with
            ⟨sb', t_push, extra₃, hex_push, ht_push, hq_b', hpar_b', _, harr_b', hreg_b'⟩
          have hex_ite : Exec w (.ite (.op .eq (.reg (r_base + 6)) (.reg (r_base + 8))) .skip _)
              (sb.setReg (r_base + 6) v_val) sb' (3 + t_push) :=
            .ite_false hcond_vs hex_push
          have harr_lt' : ∀ a < a_base + 3, sb'.arrs a = s.arrs a := by
            intro a ha
            rw [harr_b' a (by omega) (by omega) (by omega)]
            exact harr_b a ha
          have hlist_next : IsListAt a_start a_end a_entries u st_u en_u (lists uFin)
              (sb'.setReg (r_base + 4) (st_u + (j + 1))) :=
            (hlist_b.of_arrs_eq
              (harr_b' a_start (by omega) (by omega) (by omega))
              (harr_b' a_end (by omega) (by omega) (by omega))
              (harr_b' a_entries (by omega) (by omega) (by omega)))
          have hq_next : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
              r_base (r_base + 1) (items ++ extra₁ ++ (extra₂ ++ extra₃)) (headIdx + 1)
              (sb'.setReg (r_base + 4) (st_u + (j + 1))) := by
            rw [← List.append_assoc]
            rcases hq_b' with ⟨hq, hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
            exact ⟨hq.of_eq rfl (by simp [State.setReg]) (by simp [State.setReg]),
              hno, hlt_it, hv_len, hp_len, hv_iff, hp_lt⟩
          refine ⟨sb', 3 + t_push, hex_ite, show 3 + t_push ≤ 21 by omega,
            ⟨hlist_next,
              by simp [State.setReg, hreg_b' (r_base + 2) (by omega) (by omega), hrx_b],
              by simp [State.setReg, hreg_b' (r_base + 3) (by omega) (by omega), hru_b],
              by simp [State.setReg, hreg_b' (r_base + 8) (by omega) (by omega), hrs_b],
              harr_lt', extra₂ ++ extra₃, hq_next, hpar_b'⟩,
            by rw [hreg_b' (r_base + 4) (by omega) (by omega)]; exact hrk_v,
            by rw [hreg_b' (r_base + 5) (by omega) (by omega)]; exact hrhi_v⟩
    rcases hforList s₅ hInner₀ with
      ⟨s₆, t_list, hex_list, ht_list, _, _, _, _, harr₆, extra₂, hq₆, hpar₆⟩
    dsimp only [uFin, u, x] at ht_list
    rw [List.append_assoc] at hq₆
    have hex_else : Exec w
        (.seq (.assign (r_base + 3) (.op .sub (.reg (r_base + 2)) (.const n)))
          (.seq (.assign (r_base + 7) (.read a_base (.reg (r_base + 3))))
            (.seq (.ite (.reg (r_base + 7)) _ .skip)
              (.seq (.assign (r_base + 8) (.read (a_base + 2) (.reg (r_base + 3))))
                (forList a_start a_end a_entries (r_base + 3) (r_base + 4) (r_base + 5) (r_base + 6) _)))))
        s₁ s₆ (4 + (3 + (t_back + (3 + t_list)))) :=
      .seq hex_sub (.seq hex_rdU (.seq hex_back (.seq hex_rdS hex_list)))
    refine ⟨s₆, t_pop + (3 + (4 + (3 + (t_back + (3 + t_list))))), extra₁ ++ extra₂,
      .seq hex_pop (.ite_false hcond_x hex_else),
      by simp [resNodeWeight, show ¬ items[headIdx] < n from hx_n]; omega,
      hadj.of_arrs_eq (harr₆ a_start (by omega))
        (harr₆ a_end (by omega)) (harr₆ a_entries (by omega)),
      hvalid.of_arrs_eq (harr₆ a_base (by omega))
        (harr₆ (a_base + 1) (by omega)) (harr₆ (a_base + 2) (by omega)),
      hq₆, hpar₆, harr₆⟩

theorem resBfsLoopProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_base : ℕ) (r_base : ℕ)
    (ha_start : a_start < a_base) (ha_end : a_end < a_base) (ha_ent : a_entries < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {items : List ℕ} {headIdx : ℕ} {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s)
    (hqstate : ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
      r_base (r_base + 1) items headIdx s)
    (hpar_sound : ParentEdgeSound G (a_base + 4) s) :
    ∃ s' t items',
      Exec w (resBfsLoopProg n a_start a_end a_entries a_base r_base) s s' t ∧
      t ≤ 3 + (∑ z ∈ Finset.univ \ listFinset (2 * n) (items.take headIdx), resNodeWeight lists z) ∧
      IsAdjList G a_start a_end a_entries lists s' ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      ResQueueState (n := n) (a_base + 3) (a_base + 4) (a_base + 5)
        r_base (r_base + 1) items' items'.length s' ∧
      ParentEdgeSound G (a_base + 4) s' ∧
      (∀ a < a_base + 3, s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  generalize hB : (∑ z ∈ Finset.univ \ listFinset (2 * n) (items.take headIdx), resNodeWeight lists z) = B
  induction B using Nat.strong_induction_on generalizing items headIdx s with
  | _ B ih =>
    rcases hqstate.1 with ⟨_, hle_2n, hrhead, hrtail, hhead_le, _⟩
    have htail_w : items.length < 2 ^ w := by omega
    have hhead_w : headIdx < 2 ^ w := by omega
    by_cases hhead_lt : headIdx < items.length
    · have hcond : (Expr.op .lt (.reg r_base) (.reg (r_base + 1))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail,
          hhead_w, htail_w, hhead_lt, hw]
      rcases resBfsStepProg_exec G lists a_start a_end a_entries a_base r_base
          ha_start ha_end ha_ent hw h2n_w hadj hent_w hvalid hqstate hpar_sound hhead_lt with
        ⟨s₁, t₁, extra, hex₁, ht₁, hadj₁, hvalid₁, hq₁, hpar₁, harr₁⟩
      have hx_lt : items[headIdx] < 2 * n := hqstate.2.2.1 items[headIdx] (List.getElem_mem hhead_lt)
      have hpop_sum := sum_resNodeWeight_pop (extra := extra) lists hqstate.2.1 hhead_lt hx_lt
      rw [hB] at hpop_sum
      set B' := ∑ z ∈ Finset.univ \ listFinset (2 * n) ((items ++ extra).take (headIdx + 1)),
        resNodeWeight lists z
      have hB'_lt : B' < B := by omega
      have hent_w₁ : (s₁.arrs a_entries).length < 2 ^ w := by
        rw [harr₁ a_entries (by omega)]; exact hent_w
      rcases ih B' hB'_lt hadj₁ hent_w₁ hvalid₁ hq₁ hpar₁ rfl with
        ⟨s₂, t₂, items', hex₂, ht₂, hadj₂, hvalid₂, hq₂, hpar₂, harr₂⟩
      refine ⟨s₂, 3 + t₁ + t₂, items', .while_true hcond (by omega) hex₁ hex₂,
        by omega, hadj₂, hvalid₂, hq₂, hpar₂,
        fun a ha => by rw [harr₂ a ha, harr₁ a ha]⟩
    · have hhead_eq : headIdx = items.length := by omega
      subst hhead_eq
      have hcond : (Expr.op .lt (.reg r_base) (.reg (r_base + 1))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrhead, hrtail, htail_w, h0_w]
      exact ⟨s, 3, items, .while_false hcond, by omega, hadj, hvalid, hqstate, hpar_sound,
        fun _ _ => rfl⟩

/-! ### Target Search and Augmentation Along `a_parent` -/

/-- Scan `u = 0, …, n - 1` to find a target vertex `u ∈ B` whose out-node `u + n` was visited
(`a_vis[u + n] != 0`), storing it in `r_target = r_base + 11` (or `n` if none was reached). -/
def findTargetProg (n : ℕ) (a_B a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 11) (.const n))
    (.seq (.assign (r_base + 3) (.const 0))
      (forUp (r_base + 3) (.const n)
        (.seq (.assign (r_base + 7) (.read a_B (.reg (r_base + 3))))
          (.ite (.reg (r_base + 7))
            (.seq (.assign (r_base + 7) (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.const n))))
              (.ite (.reg (r_base + 7))
                (.assign (r_base + 11) (.reg (r_base + 3)))
                .skip))
            .skip))))

theorem findTargetLoop_exec {w n : ℕ} (a_B a_base : ℕ) (r_base : ℕ)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hB_len : (s.arrs a_B).length = n)
    (hB_bound : ∀ u : Fin n, (s.arrs a_B)[u.1]'(by rw [hB_len]; exact u.2) ≤ 1)
    (hvis_len : (s.arrs (a_base + 3)).length = 2 * n)
    (hvis_bound : ∀ x : ℕ, (hx : x < 2 * n) →
      (s.arrs (a_base + 3))[x]'(by rw [hvis_len]; exact hx) ≤ 1)
    (hru : s.regs (r_base + 3) = k)
    (htarg : s.regs (r_base + 11) ≤ n) :
    ∃ s' t,
      Exec w (forUp (r_base + 3) (.const n)
        (.seq (.assign (r_base + 7) (.read a_B (.reg (r_base + 3))))
          (.ite (.reg (r_base + 7))
            (.seq (.assign (r_base + 7) (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.const n))))
              (.ite (.reg (r_base + 7))
                (.assign (r_base + 11) (.reg (r_base + 3)))
                .skip))
            .skip))) s s' t ∧
      t ≤ 3 + 19 * rem ∧
      s'.regs (r_base + 11) ≤ n ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hru_n : s.regs (r_base + 3) = n := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.const n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_n, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, htarg, fun _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.const n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hk_w, hn_w, hk_lt, hw]
    have hk_B : k < (s.arrs a_B).length := by rw [hB_len]; exact hk_lt
    let valB := (s.arrs a_B)[k]'hk_B
    have hvalB_le : valB ≤ 1 := hB_bound ⟨k, hk_lt⟩
    have hvalB_w : valB < 2 ^ w := by omega
    let s₁ := s.setReg (r_base + 7) valB
    have hex_rdB : Exec w (.assign (r_base + 7) (.read a_B (.reg (r_base + 3)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_B, valB, hvalB_w])
    have hbody_step : ∃ s_b t_b,
        Exec w (.seq (.assign (r_base + 7) (.read a_B (.reg (r_base + 3))))
          (.ite (.reg (r_base + 7))
            (.seq (.assign (r_base + 7) (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.const n))))
              (.ite (.reg (r_base + 7))
                (.assign (r_base + 11) (.reg (r_base + 3)))
                .skip))
            .skip)) s s_b t_b ∧
        t_b ≤ 12 ∧
        s_b.regs (r_base + 3) = k ∧
        s_b.regs (r_base + 11) ≤ n ∧
        (∀ a : Arr, s_b.arrs a = s.arrs a) := by
      by_cases hvalB_ne : valB ≠ 0
      · have hcondB : (Expr.reg (r_base + 7)).eval w s₁ = some valB := by
          simp [s₁, Expr.eval, checkWord, hvalB_w]
        have hkn_lt : k + n < 2 * n := by omega
        have hkn_w : k + n < 2 ^ w := by omega
        have hkn_vis : k + n < (s₁.arrs (a_base + 3)).length := by
          simp [s₁, hvis_len, hkn_lt]
        let valV := (s₁.arrs (a_base + 3))[k + n]'hkn_vis
        have hvalV_le : valV ≤ 1 := hvis_bound (k + n) hkn_lt
        have hvalV_w : valV < 2 ^ w := by omega
        have hru₁ : s₁.regs (r_base + 3) = k := by
          simp [s₁, State.setReg, hru]
        let s₂ := s₁.setReg (r_base + 7) valV
        have hex_rdV : Exec w (.assign (r_base + 7)
            (.read (a_base + 3) (.op .add (.reg (r_base + 3)) (.const n)))) s₁ s₂ 5 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hk_w, hn_w, hkn_w,
            hkn_vis, valV, hvalV_w])
        by_cases hvalV_ne : valV ≠ 0
        · have hcondV : (Expr.reg (r_base + 7)).eval w s₂ = some valV := by
            simp [s₂, Expr.eval, checkWord, hvalV_w]
          have hru₂ : s₂.regs (r_base + 3) = k := by
            simp [s₂, State.setReg, hru₁]
          let s₃ := s₂.setReg (r_base + 11) k
          have hex_setT : Exec w (.assign (r_base + 11) (.reg (r_base + 3))) s₂ s₃ 2 :=
            .assign (by simp [Expr.eval, checkWord, hru₂, hk_w])
          have hex_iteV : Exec w (.ite (.reg (r_base + 7)) (.assign (r_base + 11) (.reg (r_base + 3))) .skip)
              s₂ s₃ 3 := .ite_true hcondV hvalV_ne hex_setT
          have hex_iteB : Exec w (.ite (.reg (r_base + 7)) _ .skip) s₁ s₃ (1 + (5 + 3)) :=
            .ite_true hcondB hvalB_ne (.seq hex_rdV hex_iteV)
          refine ⟨s₃, 3 + (1 + (5 + 3)), .seq hex_rdB hex_iteB, by omega,
            by simp [s₃, State.setReg, hru₂],
            by simp [s₃]; omega,
            fun _ => rfl⟩
        · have hvalV_eq0 : valV = 0 := by omega
          have hcondV : (Expr.reg (r_base + 7)).eval w s₂ = some 0 := by
            simp [s₂, Expr.eval, checkWord, hvalV_eq0, h0_w]
          have hex_iteV : Exec w (.ite (.reg (r_base + 7)) (.assign (r_base + 11) (.reg (r_base + 3))) .skip)
              s₂ s₂ 2 := .ite_false hcondV (.skip s₂)
          have hex_iteB : Exec w (.ite (.reg (r_base + 7)) _ .skip) s₁ s₂ (1 + (5 + 2)) :=
            .ite_true hcondB hvalB_ne (.seq hex_rdV hex_iteV)
          refine ⟨s₂, 3 + (1 + (5 + 2)), .seq hex_rdB hex_iteB, by omega,
            by simp [s₂, State.setReg, hru₁],
            by simp [s₂, s₁, State.setReg, htarg],
            fun _ => rfl⟩
      · have hvalB_eq0 : valB = 0 := by omega
        have hcondB : (Expr.reg (r_base + 7)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, checkWord, hvalB_eq0, h0_w]
        refine ⟨s₁, 3 + 2, .seq hex_rdB (.ite_false hcondB (.skip s₁)), by omega,
          by simp [s₁, State.setReg, hru],
          by simp [s₁, State.setReg, htarg],
          fun _ => rfl⟩
    rcases hbody_step with ⟨s_b, t_b, hex_b, ht_b, hru_b, htarg_b, harr_b⟩
    have hinc : (Expr.op .add (.reg (r_base + 3)) (.const 1)).eval w s_b = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru_b, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s_next := s_b.setReg (r_base + 3) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
        s_b s_next 4 := .assign hinc
    have hB_eq : s_next.arrs a_B = s.arrs a_B := harr_b a_B
    have hvis_eq : s_next.arrs (a_base + 3) = s.arrs (a_base + 3) := harr_b (a_base + 3)
    rcases ih (k + 1) (by omega) (s := s_next) (by rw [hB_eq]; exact hB_len)
        (fun u => by simp only [hB_eq]; exact hB_bound u)
        (by rw [hvis_eq]; exact hvis_len)
        (fun x hx => by simp only [hvis_eq]; exact hvis_bound x hx)
        (by simp [s_next])
        (by simp [s_next, State.setReg, htarg_b]) with
      ⟨s_end, t_end, hex_end, ht_end, htarg_end, harr_end⟩
    refine ⟨s_end, 3 + (t_b + 4) + t_end,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex_end,
      by omega, htarg_end, fun a => by rw [harr_end a]; exact harr_b a⟩

/-- Trace `a_parent` from `r_target + n` for `2 * n` steps and update `a_used, a_pred, a_succ`. -/
def augmentTraceStepBody (n : ℕ) (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 7) (.read (a_base + 4) (.reg (r_base + 2))))
    (.seq
      (.ite (.op .lt (.reg (r_base + 2)) (.const n))
        (.ite (.op .le (.const n) (.reg (r_base + 7)))
          (.seq (.assign (r_base + 3) (.op .sub (.reg (r_base + 7)) (.const n)))
            (.ite (.op .eq (.reg (r_base + 3)) (.reg (r_base + 2)))
              .skip
              (.seq (.write (a_base + 2) (.reg (r_base + 3)) (.reg (r_base + 2)))
                (.seq (.write (a_base + 1) (.reg (r_base + 2)) (.reg (r_base + 3)))
                  (.seq (.write a_base (.reg (r_base + 3)) (.const 1))
                    (.write a_base (.reg (r_base + 2)) (.const 1)))))))
          (.write a_base (.reg (r_base + 2)) (.const 1)))
        .skip)
      (.assign (r_base + 2) (.reg (r_base + 7))))

def augmentTraceProg (n : ℕ) (a_base : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 10) (.op .add (.reg (r_base + 10)) (.const 1)))
    (.seq (.write a_base (.reg (r_base + 11)) (.const 1))
      (.seq (.assign (r_base + 2) (.op .add (.reg (r_base + 11)) (.const n)))
        (.seq (.assign (r_base + 4) (.const 0))
          (forUp (r_base + 4) (.const (2 * n)) (augmentTraceStepBody n a_base r_base)))))

theorem ValidPathState.write_used_one {n : ℕ} {G : SimpleGraph (Fin n)}
    {a_used a_pred a_succ : ℕ} {s : State}
    (h : ValidPathState G a_used a_pred a_succ s)
    (hne_up : a_used ≠ a_pred) (hne_us : a_used ≠ a_succ)
    {v : ℕ} (hv : v < n) :
    ValidPathState G a_used a_pred a_succ (s.writeArr a_used v 1) := by
  have hne_up' : (a_used : Arr) ≠ a_pred := by omega
  have hne_us' : (a_used : Arr) ≠ a_succ := by omega
  rcases h with ⟨hu, hp, hs, h1, h2, h3, h4, h5⟩
  refine ⟨by simp [hu], by simp [hne_up'.symm, hp], by simp [hne_us'.symm, hs],
    fun u => ?_,
    fun u => by simp only [State.writeArr_arrs_ne _ _ _ hne_up'.symm]; exact h2 u,
    fun u => by simp only [State.writeArr_arrs_ne _ _ _ hne_us'.symm]; exact h3 u,
    fun u h0 => ?_,
    fun u w' heq => by simp only [State.writeArr_arrs_ne _ _ _ hne_us'.symm] at heq; exact h5 u w' heq⟩
  · simp only [State.writeArr_arrs_self]
    by_cases huv : u.1 = v
    · simp only [huv]
      rw [List.getElem_set_self (by simp [hu, hv])]
    · rw [List.getElem_set_ne (Ne.symm huv)]; exact h1 u
  · simp only [State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ hne_us'.symm] at h0 ⊢
    by_cases huv : u.1 = v
    · simp only [huv] at h0
      rw [List.getElem_set_self (by simp [hu, hv])] at h0
      omega
    · rw [List.getElem_set_ne (Ne.symm huv)] at h0
      exact h4 u h0

theorem ValidPathState.augment_edge {n : ℕ} {G : SimpleGraph (Fin n)}
    {a_used a_pred a_succ : ℕ} {s : State}
    (h : ValidPathState G a_used a_pred a_succ s)
    (hne_up : a_used ≠ a_pred) (hne_us : a_used ≠ a_succ) (hne_ps : a_pred ≠ a_succ)
    (u v : Fin n) (hadj : G.Adj u v) :
    ValidPathState G a_used a_pred a_succ
      ((((s.writeArr a_succ u.1 v.1).writeArr a_pred v.1 u.1).writeArr a_used u.1 1).writeArr a_used v.1 1) := by
  apply ValidPathState.write_used_one _ hne_up hne_us v.2
  have hne_up' : (a_used : Arr) ≠ a_pred := by omega
  have hne_us' : (a_used : Arr) ≠ a_succ := by omega
  have hne_ps' : (a_pred : Arr) ≠ a_succ := by omega
  rcases h with ⟨hu, hp, hs, h1, h2, h3, h4, h5⟩
  refine ⟨by simp [hne_up', hne_us', hu],
    by simp [hne_up'.symm, hne_ps', hp],
    by simp [hne_us'.symm, hne_ps'.symm, hs],
    fun z => ?_,
    fun z => ?_,
    fun z => ?_,
    fun z h0 => ?_,
    fun z w' heq => ?_⟩
  · simp only [State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ hne_up',
      State.writeArr_arrs_ne _ _ _ hne_us']
    by_cases hzu : z.1 = u.1
    · simp only [hzu]
      rw [List.getElem_set_self (by simp [hu, u.2])]
    · rw [List.getElem_set_ne (Ne.symm hzu)]; exact h1 z
  · simp only [State.writeArr_arrs_ne _ _ _ hne_up'.symm, State.writeArr_arrs_self,
      State.writeArr_arrs_ne _ _ _ hne_ps']
    by_cases hzv : z.1 = v.1
    · simp only [hzv]
      rw [List.getElem_set_self (by simp [hp, v.2])]
      exact le_of_lt u.2
    · rw [List.getElem_set_ne (Ne.symm hzv)]; exact h2 z
  · simp only [State.writeArr_arrs_ne _ _ _ hne_us'.symm, State.writeArr_arrs_ne _ _ _ hne_ps'.symm,
      State.writeArr_arrs_self]
    by_cases hzu : z.1 = u.1
    · simp only [hzu]
      rw [List.getElem_set_self (by simp [hs, u.2])]
      exact le_of_lt v.2
    · rw [List.getElem_set_ne (Ne.symm hzu)]; exact h3 z
  · simp only [State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ hne_up',
      State.writeArr_arrs_ne _ _ _ hne_us', State.writeArr_arrs_ne _ _ _ hne_us'.symm,
      State.writeArr_arrs_ne _ _ _ hne_ps'.symm] at h0 ⊢
    by_cases hzu : z.1 = u.1
    · simp only [hzu] at h0
      rw [List.getElem_set_self (by simp [hu, u.2])] at h0
      omega
    · rw [List.getElem_set_ne (Ne.symm hzu)] at h0 ⊢
      exact h4 z h0
  · simp only [State.writeArr_arrs_ne _ _ _ hne_us'.symm, State.writeArr_arrs_ne _ _ _ hne_ps'.symm,
      State.writeArr_arrs_self] at heq
    by_cases hzu : z.1 = u.1
    · simp only [hzu] at heq
      rw [List.getElem_set_self (by simp [hs, u.2])] at heq
      have hz_eq : z = u := Fin.ext hzu
      have hw_eq : w' = v := Fin.ext heq.symm
      rw [hz_eq, hw_eq]
      exact hadj
    · rw [List.getElem_set_ne (Ne.symm hzu)] at heq
      exact h5 z w' heq

theorem augmentTraceLoop_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (a_base : ℕ) (r_base : ℕ)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = 2 * n) {s : State}
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s)
    (hpar_sound : ParentEdgeSound G (a_base + 4) s)
    (hpar_lt : ∀ x : ℕ, (hx : x < 2 * n) →
      (s.arrs (a_base + 4))[x]'(by rw [hpar_sound.1]; exact hx) < 2 * n)
    (hrk : s.regs (r_base + 4) = k)
    (hrx : s.regs (r_base + 2) < 2 * n) :
    ∃ s' t,
      Exec w (forUp (r_base + 4) (.const (2 * n)) (augmentTraceStepBody n a_base r_base)) s s' t ∧
      t ≤ 3 + 38 * rem ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      s'.arrs (a_base + 5) = s.arrs (a_base + 5) ∧
      s'.regs (r_base + 9) = s.regs (r_base + 9) ∧
      s'.regs (r_base + 10) = s.regs (r_base + 10) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hrk_2n : s.regs (r_base + 4) = 2 * n := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.const (2 * n))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_2n, h2n_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hvalid, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ rem ih =>
    have hk_lt : k < 2 * n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.const (2 * n))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hk_w, h2n_w, hk_lt, hw]
    let x := s.regs (r_base + 2)
    have hx_lt : x < 2 * n := hrx
    have hx_w : x < 2 ^ w := by omega
    have hx_par : x < (s.arrs (a_base + 4)).length := by rw [hpar_sound.1]; exact hx_lt
    let p := (s.arrs (a_base + 4))[x]'hx_par
    have hp_lt : p < 2 * n := hpar_lt x hx_lt
    have hp_w : p < 2 ^ w := by omega
    let s₁ := s.setReg (r_base + 7) p
    have hex_rdP : Exec w (.assign (r_base + 7) (.read (a_base + 4) (.reg (r_base + 2)))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, x, hx_w, hx_par, p, hp_w])
    have hrx₁ : s₁.regs (r_base + 2) = x := by
      simp [s₁, State.setReg, x]
    have hbody_mid : ∃ s_m t_m,
        Exec w (.ite (.op .lt (.reg (r_base + 2)) (.const n))
          (.ite (.op .le (.const n) (.reg (r_base + 7)))
            (.seq (.assign (r_base + 3) (.op .sub (.reg (r_base + 7)) (.const n)))
              (.ite (.op .eq (.reg (r_base + 3)) (.reg (r_base + 2)))
                .skip
                (.seq (.write (a_base + 2) (.reg (r_base + 3)) (.reg (r_base + 2)))
                  (.seq (.write (a_base + 1) (.reg (r_base + 2)) (.reg (r_base + 3)))
                    (.seq (.write a_base (.reg (r_base + 3)) (.const 1))
                      (.write a_base (.reg (r_base + 2)) (.const 1)))))))
            (.write a_base (.reg (r_base + 2)) (.const 1)))
          .skip) s₁ s_m t_m ∧
        t_m ≤ 26 ∧
        ValidPathState G a_base (a_base + 1) (a_base + 2) s_m ∧
        s_m.regs (r_base + 7) = p ∧
        s_m.regs (r_base + 4) = k ∧
        s_m.arrs (a_base + 4) = s.arrs (a_base + 4) ∧
        s_m.arrs (a_base + 5) = s.arrs (a_base + 5) ∧
        (∀ a < a_base, s_m.arrs a = s.arrs a) ∧
        s_m.regs (r_base + 9) = s.regs (r_base + 9) ∧
        s_m.regs (r_base + 10) = s.regs (r_base + 10) := by
      by_cases hx_n : x < n
      · have hcondX : (Expr.op .lt (.reg (r_base + 2)) (.const n)).eval w s₁ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hx_w, hn_w, hx_n, hw]
        by_cases hp_ge : n ≤ p
        · have hcondP : (Expr.op .le (.const n) (.reg (r_base + 7))).eval w s₁ = some 1 := by
            simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hn_w, hp_w, hp_ge, hw]
          let u := p - n
          have hu_lt : u < n := by omega
          have hu_w : u < 2 ^ w := by omega
          let s₂ := s₁.setReg (r_base + 3) u
          have hex_sub : Exec w (.assign (r_base + 3) (.op .sub (.reg (r_base + 7)) (.const n))) s₁ s₂ 4 :=
            .assign (by
              have hsub_w : p - n < 2 ^ w := hu_w
              simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hp_w, hn_w, hsub_w]
              rfl)
          have hrx₂ : s₂.regs (r_base + 2) = x := by
            simp [s₂, State.setReg, hrx₁]
          have hru₂ : s₂.regs (r_base + 3) = u := by
            simp [s₂, State.setReg]
          by_cases huv_eq : u = x
          · have hcondEQ : (Expr.op .eq (.reg (r_base + 3)) (.reg (r_base + 2))).eval w s₂ = some 1 := by
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₂, hrx₂, huv_eq, hx_w, hw]
            refine ⟨s₂, 3 + (3 + (4 + 4)),
              .ite_true hcondX (by omega) (.ite_true hcondP (by omega)
                (.seq hex_sub (.ite_true hcondEQ (by omega) (.skip s₂)))),
              by omega, hvalid,
              by simp [s₂, s₁, State.setReg],
              by simp [s₂, s₁, State.setReg, hrk],
              rfl, rfl, fun _ _ => rfl,
              by simp [s₂, s₁, State.setReg],
              by simp [s₂, s₁, State.setReg]⟩
          · have hcondEQ : (Expr.op .eq (.reg (r_base + 3)) (.reg (r_base + 2))).eval w s₂ = some 0 := by
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₂, hrx₂, hu_w, hx_w, huv_eq, h0_w]
            have hadj_ux : G.Adj ⟨u, hu_lt⟩ ⟨x, hx_n⟩ := by
              apply hpar_sound.2 ⟨x, hx_n⟩ ⟨u, hu_lt⟩ (fun heq => huv_eq (congrArg Fin.val heq))
              dsimp [p, u]
              omega
            let s₃ := s₂.writeArr (a_base + 2) u x
            have hex_ws : Exec w (.write (a_base + 2) (.reg (r_base + 3)) (.reg (r_base + 2))) s₂ s₃ 3 :=
              .write (by simp [Expr.eval, checkWord, hru₂, hu_w])
                (by simp [Expr.eval, checkWord, hrx₂, hx_w])
                (by simp [s₂, s₁, hvalid.2.2.1, hu_lt])
            let s₄ := s₃.writeArr (a_base + 1) x u
            have hex_wp : Exec w (.write (a_base + 1) (.reg (r_base + 2)) (.reg (r_base + 3))) s₃ s₄ 3 :=
              .write (by simp [s₃, Expr.eval, checkWord, hrx₂, hx_w])
                (by simp [s₃, Expr.eval, checkWord, hru₂, hu_w])
                (by simp [s₃, s₂, s₁, hvalid.2.1, hx_n])
            let s₅ := s₄.writeArr a_base u 1
            have hex_wu1 : Exec w (.write a_base (.reg (r_base + 3)) (.const 1)) s₄ s₅ 3 :=
              .write (by simp [s₄, s₃, Expr.eval, checkWord, hru₂, hu_w])
                (by simp [Expr.eval, checkWord, hw])
                (by simp [s₄, s₃, s₂, s₁, hvalid.1, hu_lt])
            let s₆ := s₅.writeArr a_base x 1
            have hex_wu2 : Exec w (.write a_base (.reg (r_base + 2)) (.const 1)) s₅ s₆ 3 :=
              .write (by simp [s₅, s₄, s₃, Expr.eval, checkWord, hrx₂, hx_w])
                (by simp [Expr.eval, checkWord, hw])
                (by simp [s₅, s₄, s₃, s₂, s₁, hvalid.1, hx_n])
            have hvalid₆ : ValidPathState G a_base (a_base + 1) (a_base + 2) s₆ :=
              hvalid.augment_edge (by omega) (by omega) (by omega) ⟨u, hu_lt⟩ ⟨x, hx_n⟩ hadj_ux
            refine ⟨s₆, 3 + (3 + (4 + (3 + (3 + (3 + (3 + 3)))))),
              .ite_true hcondX (by omega) (.ite_true hcondP (by omega)
                (.seq hex_sub (.ite_false hcondEQ (.seq hex_ws (.seq hex_wp (.seq hex_wu1 hex_wu2)))))),
              by omega, hvalid₆,
              by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg],
              by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hrk],
              by simp [s₆, s₅, s₄, s₃, s₂, s₁],
              by simp [s₆, s₅, s₄, s₃, s₂, s₁],
              fun a ha => by
                simp [s₆, s₅, s₄, s₃, s₂, s₁,
                  show (a : Arr) ≠ a_base by omega,
                  show (a : Arr) ≠ a_base + 1 by omega,
                  show (a : Arr) ≠ a_base + 2 by omega],
              by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg],
              by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg]⟩
        · have hcondP : (Expr.op .le (.const n) (.reg (r_base + 7))).eval w s₁ = some 0 := by
            simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hn_w, hp_w, hp_ge, h0_w]
          let s₂ := s₁.writeArr a_base x 1
          have hex_wu : Exec w (.write a_base (.reg (r_base + 2)) (.const 1)) s₁ s₂ 3 :=
            .write (by simp [Expr.eval, checkWord, hrx₁, hx_w])
              (by simp [Expr.eval, checkWord, hw])
              (by simp [s₁, hvalid.1, hx_n])
          refine ⟨s₂, 3 + (3 + 3),
            .ite_true hcondX (by omega) (.ite_false hcondP hex_wu),
            by omega,
            hvalid.write_used_one (by omega) (by omega) hx_n,
            by simp [s₂, s₁],
            by simp [s₂, s₁, State.setReg, hrk],
            by simp [s₂, s₁],
            by simp [s₂, s₁],
            fun a ha => by simp [s₂, s₁, show (a : Arr) ≠ a_base by omega],
            by simp [s₂, s₁, State.setReg],
            by simp [s₂, s₁, State.setReg]⟩
      · have hcondX : (Expr.op .lt (.reg (r_base + 2)) (.const n)).eval w s₁ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx₁, hx_w, hn_w, hx_n, h0_w]
        refine ⟨s₁, 4, .ite_false hcondX (.skip s₁), by omega, hvalid,
          by simp [s₁],
          by simp [s₁, State.setReg, hrk],
          rfl, rfl, fun _ _ => rfl,
          by simp [s₁, State.setReg],
          by simp [s₁, State.setReg]⟩
    rcases hbody_mid with ⟨s_m, t_m, hex_m, ht_m, hvalid_m, hr7_m, hrk_m, hpar_m, hq_m, harr_m, hr9_m, hr10_m⟩
    let s_b := s_m.setReg (r_base + 2) p
    have hex_adv : Exec w (.assign (r_base + 2) (.reg (r_base + 7))) s_m s_b 2 :=
      .assign (by simp [Expr.eval, checkWord, hr7_m, hp_w])
    have hex_body : Exec w (augmentTraceStepBody n a_base r_base) s s_b (3 + (t_m + 2)) :=
      .seq hex_rdP (.seq hex_m hex_adv)
    have hrk_b : s_b.regs (r_base + 4) = k := by
      simp [s_b, State.setReg, hrk_m]
    have hinc : (Expr.op .add (.reg (r_base + 4)) (.const 1)).eval w s_b = some (k + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_b, hk_w, hw,
        show k + 1 < 2 ^ w by omega]
    let s_next := s_b.setReg (r_base + 4) (k + 1)
    have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
        s_b s_next 4 := .assign hinc
    have hpar_sound_next : ParentEdgeSound G (a_base + 4) s_next := by
      rcases hpar_sound with ⟨hp_len, hp_adj⟩
      exact ⟨by simp [s_next, s_b, hpar_m, hp_len],
        fun v u huv hget => by simp only [s_next, s_b, State.setReg_arrs, hpar_m] at hget; exact hp_adj v u huv hget⟩
    have hvalid_next : ValidPathState G a_base (a_base + 1) (a_base + 2) s_next := hvalid_m
    rcases ih (k + 1) (by omega) hvalid_next hpar_sound_next
        (fun z hz => by simp only [s_next, s_b, State.setReg_arrs, hpar_m]; exact hpar_lt z hz)
        (by simp [s_next])
        (by simp [s_next, s_b, State.setReg, hp_lt]) with
      ⟨s_end, t_end, hex_end, ht_end, hvalid_end, harr_end, hq_end, hr9_end, hr10_end⟩
    refine ⟨s_end, 3 + ((3 + (t_m + 2)) + 4) + t_end,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex_end,
      by omega, hvalid_end,
      fun a ha => by rw [harr_end a ha]; exact harr_m a ha,
      by rw [hq_end]; exact hq_m,
      by rw [hr9_end]; simp [s_next, s_b, State.setReg, hr9_m],
      by rw [hr10_end]; simp [s_next, s_b, State.setReg, hr10_m]⟩

theorem augmentTraceProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (a_base : ℕ) (r_base : ℕ)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {s : State}
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s)
    (hpar_sound : ParentEdgeSound G (a_base + 4) s)
    (hpar_lt : ∀ x : ℕ, (hx : x < 2 * n) →
      (s.arrs (a_base + 4))[x]'(by rw [hpar_sound.1]; exact hx) < 2 * n)
    (htarg : s.regs (r_base + 11) < n)
    (hfound_w : s.regs (r_base + 10) + 1 < 2 ^ w) :
    ∃ s' t,
      Exec w (augmentTraceProg n a_base r_base) s s' t ∧
      t ≤ 76 * n + 16 ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      s'.arrs (a_base + 5) = s.arrs (a_base + 5) ∧
      s'.regs (r_base + 9) = s.regs (r_base + 9) ∧
      s'.regs (r_base + 10) ≤ s.regs (r_base + 10) + 1 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let targ := s.regs (r_base + 11)
  have htarg_w : targ < 2 ^ w := by omega
  let found := s.regs (r_base + 10)
  have hfound_lt : found < 2 ^ w := by omega
  -- 1. .assign (r_base + 10) (.op .add (.reg (r_base + 10)) (.const 1))
  let s₁ := s.setReg (r_base + 10) (found + 1)
  have hex₁ : Exec w (.assign (r_base + 10) (.op .add (.reg (r_base + 10)) (.const 1))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, found, hfound_lt, hw, hfound_w])
  -- 2. .write a_base (.reg (r_base + 11)) (.const 1)
  have htarg₁ : s₁.regs (r_base + 11) = targ := by
    simp [s₁, State.setReg, targ]
  let s₂ := s₁.writeArr a_base targ 1
  have hex₂ : Exec w (.write a_base (.reg (r_base + 11)) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, htarg₁, htarg_w])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₁, hvalid.1, targ, htarg])
  -- 3. .assign (r_base + 2) (.op .add (.reg (r_base + 11)) (.const n))
  have htn_w : targ + n < 2 ^ w := by omega
  let s₃ := s₂.setReg (r_base + 2) (targ + n)
  have hex₃ : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 11)) (.const n))) s₂ s₃ 4 :=
    .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, htarg₁, htarg_w, hn_w, htn_w])
  -- 4. .assign (r_base + 4) (.const 0)
  let s₄ := s₃.setReg (r_base + 4) 0
  have hex₄ : Exec w (.assign (r_base + 4) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hvalid₄ : ValidPathState G a_base (a_base + 1) (a_base + 2) s₄ :=
    hvalid.write_used_one (by omega) (by omega) htarg
  have hpar₄ : ParentEdgeSound G (a_base + 4) s₄ := by
    rcases hpar_sound with ⟨hp_len, hp_adj⟩
    exact ⟨by simp [s₄, s₃, s₂, s₁, hp_len],
      fun v u huv hget => by
        simp only [s₄, s₃, s₂, s₁, State.setReg_arrs,
          State.writeArr_arrs_ne _ _ _ (show (a_base + 4 : Arr) ≠ a_base by omega)] at hget
        exact hp_adj v u huv hget⟩
  rcases augmentTraceLoop_exec G a_base r_base hw h2n_w (2 * n) 0 (by omega)
      hvalid₄ hpar₄
      (fun x hx => by
        simp only [s₄, s₃, s₂, s₁, State.setReg_arrs,
          State.writeArr_arrs_ne _ _ _ (show (a_base + 4 : Arr) ≠ a_base by omega)]
        exact hpar_lt x hx)
      (by simp [s₄])
      (by simp [s₄, s₃, State.setReg]; omega) with
    ⟨s₅, t₅, hex₅, ht₅, hvalid₅, harr₅, hq₅, hr9₅, hr10₅⟩
  refine ⟨s₅, 4 + (3 + (4 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hvalid₅,
    fun a ha => by rw [harr₅ a ha]; simp [s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_base by omega],
    by rw [hq₅]; simp [s₄, s₃, s₂, s₁],
    by rw [hr9₅]; simp [s₄, s₃, s₂, s₁, State.setReg],
    by rw [hr10₅]; simp [s₄, s₃, s₂, s₁, State.setReg, found]⟩

/-- One full augmenting-path round (`initSourcesProg`, `resBfsLoopProg`, `findTargetProg`, and
conditional `augmentTraceProg`). -/
def disjointPathsRoundProg (n : ℕ) (a_start a_end a_entries a_A a_B a_base : Arr)
    (r_base : Reg) : Cmd :=
  .seq (initSourcesProg n a_A a_base r_base)
    (.seq (resBfsLoopProg n a_start a_end a_entries a_base r_base)
      (.seq (findTargetProg n a_B a_base r_base)
        (.ite (.op .lt (.reg (r_base + 11)) (.const n))
          (augmentTraceProg n a_base r_base)
          .skip)))

/-- Main program for `k` vertex-disjoint paths between `A` and `B` by `k` rounds of
augmenting-path search on the `2n`-vertex split residual network. -/
def disjointPathsProg (n k : ℕ) (a_start a_end a_entries a_A a_B a_base : Arr)
    (r_base : Reg) : Cmd :=
  .seq (allocFillArr a_base (.const n) (.const 0) (r_base + 3))
    (.seq (allocFillArr (a_base + 1) (.const n) (.const n) (r_base + 3))
      (.seq (allocFillArr (a_base + 2) (.const n) (.const n) (r_base + 3))
        (.seq (.alloc (a_base + 5) (.const (2 * n)))
          (.seq (.assign (r_base + 10) (.const 0))
            (.seq (.assign (r_base + 9) (.const 0))
              (forUp (r_base + 9) (.const k)
                (disjointPathsRoundProg n a_start a_end a_entries a_A a_B a_base r_base)))))))

theorem disjointPathsRoundProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_A a_B a_base : ℕ) (r_base : ℕ)
    (ha_start : a_start < a_base) (ha_end : a_end < a_base) (ha_ent : a_entries < a_base)
    (ha_A : a_A < a_base) (ha_B : a_B < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hA_len : (s.arrs a_A).length = n)
    (hA_bound : ∀ u : Fin n, (s.arrs a_A)[u.1]'(by rw [hA_len]; exact u.2) ≤ 1)
    (hB_len : (s.arrs a_B).length = n)
    (hB_bound : ∀ u : Fin n, (s.arrs a_B)[u.1]'(by rw [hB_len]; exact u.2) ≤ 1)
    (hq_len : (s.arrs (a_base + 5)).length = 2 * n)
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s)
    (hfound_w : s.regs (r_base + 10) + 1 < 2 ^ w) :
    ∃ s' t,
      Exec w (disjointPathsRoundProg n a_start a_end a_entries a_A a_B a_base r_base) s s' t ∧
      t ≤ 274 * n + 31 * totalAdjEntries lists + 52 ∧
      IsAdjList G a_start a_end a_entries lists s' ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      (s'.arrs (a_base + 5)).length = 2 * n ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      s'.regs (r_base + 9) = s.regs (r_base + 9) ∧
      s'.regs (r_base + 10) ≤ s.regs (r_base + 10) + 1 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  -- 1. initSourcesProg
  rcases initSourcesProg_exec G a_A a_base r_base ha_A hw h2n_w hA_len hA_bound hq_len hvalid with
    ⟨s₁, t₁, items₁, hex₁, ht₁, hvalid₁, hq₁, hpar₁, harr₁, hr9₁, hr10₁⟩
  have hadj₁ : IsAdjList G a_start a_end a_entries lists s₁ :=
    hadj.of_arrs_eq (harr₁ a_start (by omega)) (harr₁ a_end (by omega)) (harr₁ a_entries (by omega))
  have hent_w₁ : (s₁.arrs a_entries).length < 2 ^ w := by
    rw [harr₁ a_entries (by omega)]; exact hent_w
  -- 2. resBfsLoopProg
  rcases resBfsLoopProg_exec G lists a_start a_end a_entries a_base r_base
      ha_start ha_end ha_ent hw h2n_w hadj₁ hent_w₁ hvalid₁ hq₁ hpar₁ with
    ⟨s₂, t₂, items₂, hex₂, ht₂, hadj₂, hvalid₂, hq₂, hpar₂, harr₂⟩
  have hsum_le := sum_resNodeWeight_le_univ lists
    (Finset.univ \ listFinset (2 * n) (items₁.take 0))
  have hnot_bfs_r9 : (r_base + 9 : Reg) ∉
      (resBfsLoopProg n a_start a_end a_entries a_base r_base).writtenRegs := by
    simp [resBfsLoopProg, resBfsStepProg, queuePop, tryPushReg, queuePush, forList, forUp,
      Cmd.writtenRegs]
  have hnot_bfs_r10 : (r_base + 10 : Reg) ∉
      (resBfsLoopProg n a_start a_end a_entries a_base r_base).writtenRegs := by
    simp [resBfsLoopProg, resBfsStepProg, queuePop, tryPushReg, queuePush, forList, forUp,
      Cmd.writtenRegs]
  have hr9₂ : s₂.regs (r_base + 9) = s.regs (r_base + 9) := by
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₂ hnot_bfs_r9, hr9₁]
  have hr10₂ : s₂.regs (r_base + 10) = s.regs (r_base + 10) := by
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₂ hnot_bfs_r10, hr10₁]
  -- 3. findTargetProg
  let s₂_a := s₂.setReg (r_base + 11) n
  have hex_ft1 : Exec w (.assign (r_base + 11) (.const n)) s₂ s₂_a 2 :=
    .assign (by simp [Expr.eval, checkWord, hn_w])
  let s₂_b := s₂_a.setReg (r_base + 3) 0
  have hex_ft2 : Exec w (.assign (r_base + 3) (.const 0)) s₂_a s₂_b 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hB₂ : s₂_b.arrs a_B = s.arrs a_B := by
    simp only [s₂_b, s₂_a, State.setReg_arrs]
    rw [harr₂ a_B (by omega), harr₁ a_B (by omega)]
  rcases hq₂ with ⟨hq_hist₂, _, _, hvis_len₂, hpar_len₂, hvis_iff₂, hpar_lt₂⟩
  rcases findTargetLoop_exec a_B a_base r_base hw h2n_w n 0 (by omega) (s := s₂_b)
      (by rw [hB₂]; exact hB_len)
      (fun u => by simp only [hB₂]; exact hB_bound u)
      hvis_len₂ (fun x hx => (hvis_iff₂ x hx).2)
      (by simp [s₂_b])
      (by simp [s₂_b, s₂_a, State.setReg]) with
    ⟨s₃, t_ft, hex_ft3, ht_ft, htarg₃, harr₃⟩
  dsimp only [s₂_b, s₂_a, State.setReg_arrs] at harr₃
  have hex₃ : Exec w (findTargetProg n a_B a_base r_base) s₂ s₃ (2 + (2 + t_ft)) :=
    .seq hex_ft1 (.seq hex_ft2 hex_ft3)
  have hnot_ft_r9 : (r_base + 9 : Reg) ∉ (findTargetProg n a_B a_base r_base).writtenRegs := by
    simp [findTargetProg, forUp, Cmd.writtenRegs]
  have hnot_ft_r10 : (r_base + 10 : Reg) ∉ (findTargetProg n a_B a_base r_base).writtenRegs := by
    simp [findTargetProg, forUp, Cmd.writtenRegs]
  have hr9₃ : s₃.regs (r_base + 9) = s.regs (r_base + 9) := by
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₃ hnot_ft_r9, hr9₂]
  have hr10₃ : s₃.regs (r_base + 10) = s.regs (r_base + 10) := by
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₃ hnot_ft_r10, hr10₂]
  have hvalid₃ : ValidPathState G a_base (a_base + 1) (a_base + 2) s₃ :=
    hvalid₂.of_arrs_eq (harr₃ a_base) (harr₃ (a_base + 1)) (harr₃ (a_base + 2))
  have hadj₃ : IsAdjList G a_start a_end a_entries lists s₃ :=
    hadj₂.of_arrs_eq (harr₃ a_start) (harr₃ a_end) (harr₃ a_entries)
  have hpar₃ : ParentEdgeSound G (a_base + 4) s₃ := by
    rcases hpar₂ with ⟨hp_len, hp_adj⟩
    exact ⟨by rw [harr₃]; exact hp_len,
      fun v u huv hget => by simp only [harr₃] at hget; exact hp_adj v u huv hget⟩
  -- 4. Conditional augmentTraceProg
  let targ := s₃.regs (r_base + 11)
  have htarg_w : targ < 2 ^ w := by omega
  by_cases htarg_lt : targ < n
  · have hcondT : (Expr.op .lt (.reg (r_base + 11)) (.const n)).eval w s₃ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, targ, htarg_w, hn_w, htarg_lt, hw]
    rcases augmentTraceProg_exec G a_base r_base hw h2n_w hvalid₃ hpar₃
        (fun x hx => by simp only [harr₃]; exact hpar_lt₂ x hx)
        htarg_lt (by rw [hr10₃]; exact hfound_w) with
      ⟨s₄, t₄, hex₄, ht₄, hvalid₄, harr₄, hq₄, hr9₄, hr10₄⟩
    have hex_iteT : Exec w (.ite (.op .lt (.reg (r_base + 11)) (.const n))
        (augmentTraceProg n a_base r_base) .skip) s₃ s₄ (3 + t₄) :=
      .ite_true hcondT (by omega) hex₄
    have harr_lt₄ : ∀ a < a_base, s₄.arrs a = s.arrs a := by
      intro a ha
      rw [harr₄ a ha, harr₃ a, harr₂ a (by omega), harr₁ a (by omega)]
    refine ⟨s₄, t₁ + (t₂ + ((2 + (2 + t_ft)) + (3 + t₄))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_iteT)),
      by omega,
      hadj.of_arrs_eq (harr_lt₄ a_start ha_start) (harr_lt₄ a_end ha_end) (harr_lt₄ a_entries ha_ent),
      hvalid₄,
      by rw [hq₄, harr₃, hq_hist₂.1],
      harr_lt₄,
      by rw [hr9₄, hr9₃],
      by rw [hr10₃] at hr10₄; exact hr10₄⟩
  · have hcondT : (Expr.op .lt (.reg (r_base + 11)) (.const n)).eval w s₃ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, targ, htarg_w, hn_w, htarg_lt, h0_w]
    have hex_iteT : Exec w (.ite (.op .lt (.reg (r_base + 11)) (.const n))
        (augmentTraceProg n a_base r_base) .skip) s₃ s₃ 4 :=
      .ite_false hcondT (.skip s₃)
    have harr_lt₃ : ∀ a < a_base, s₃.arrs a = s.arrs a := by
      intro a ha
      rw [harr₃ a, harr₂ a (by omega), harr₁ a (by omega)]
    refine ⟨s₃, t₁ + (t₂ + ((2 + (2 + t_ft)) + 4)),
      .seq hex₁ (.seq hex₂ (.seq hex₃ hex_iteT)),
      by omega,
      hadj₃, hvalid₃,
      by rw [harr₃, hq_hist₂.1],
      harr_lt₃, hr9₃, by omega⟩

theorem disjointPathsOuterLoop_exec {w n k : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_A a_B a_base : ℕ) (r_base : ℕ)
    (ha_start : a_start < a_base) (ha_end : a_end < a_base) (ha_ent : a_entries < a_base)
    (ha_A : a_A < a_base) (ha_B : a_B < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hk_w : k < 2 ^ w)
    (rem round : ℕ) (hrem : round + rem = k) {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hA_len : (s.arrs a_A).length = n)
    (hA_bound : ∀ u : Fin n, (s.arrs a_A)[u.1]'(by rw [hA_len]; exact u.2) ≤ 1)
    (hB_len : (s.arrs a_B).length = n)
    (hB_bound : ∀ u : Fin n, (s.arrs a_B)[u.1]'(by rw [hB_len]; exact u.2) ≤ 1)
    (hq_len : (s.arrs (a_base + 5)).length = 2 * n)
    (hvalid : ValidPathState G a_base (a_base + 1) (a_base + 2) s)
    (hr9 : s.regs (r_base + 9) = round)
    (hr10 : s.regs (r_base + 10) ≤ round) :
    ∃ s' t,
      Exec w (forUp (r_base + 9) (.const k)
        (disjointPathsRoundProg n a_start a_end a_entries a_A a_B a_base r_base)) s s' t ∧
      t ≤ 3 + rem * (274 * n + 31 * totalAdjEntries lists + 59) ∧
      IsAdjList G a_start a_end a_entries lists s' ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      s'.regs (r_base + 10) ≤ k := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing round s with
  | zero =>
    have hr9_k : s.regs (r_base + 9) = k := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 9)) (.const k)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_k, hk_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by simp, hadj, hvalid, by omega⟩
  | succ rem ih =>
    have hround_lt : round < k := by omega
    have hround_w : round < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 9)) (.const k)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hround_w, hk_w, hround_lt, hw]
    rcases disjointPathsRoundProg_exec G lists a_start a_end a_entries a_A a_B a_base r_base
        ha_start ha_end ha_ent ha_A ha_B hw h2n_w hadj hent_w hA_len hA_bound hB_len hB_bound
        hq_len hvalid (by omega) with
      ⟨s₁, t₁, hex₁, ht₁, hadj₁, hvalid₁, hq_len₁, harr₁, hr9₁, hr10₁⟩
    have hr9_s₁ : s₁.regs (r_base + 9) = round := by rw [hr9₁, hr9]
    have hinc : (Expr.op .add (.reg (r_base + 9)) (.const 1)).eval w s₁ = some (round + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_s₁, hround_w, hw,
        show round + 1 < 2 ^ w by omega]
    let s₂ := s₁.setReg (r_base + 9) (round + 1)
    have hex_inc : Exec w (.assign (r_base + 9) (.op .add (.reg (r_base + 9)) (.const 1)))
        s₁ s₂ 4 := .assign hinc
    have hA_eq : s₂.arrs a_A = s.arrs a_A := harr₁ a_A ha_A
    have hB_eq : s₂.arrs a_B = s.arrs a_B := harr₁ a_B ha_B
    have hent_eq : s₂.arrs a_entries = s.arrs a_entries := harr₁ a_entries ha_ent
    rcases ih (round + 1) (by omega) (s := s₂) hadj₁ (by rw [hent_eq]; exact hent_w)
        (by rw [hA_eq]; exact hA_len) (fun u => by simp only [hA_eq]; exact hA_bound u)
        (by rw [hB_eq]; exact hB_len) (fun u => by simp only [hB_eq]; exact hB_bound u)
        hq_len₁ hvalid₁ (by simp [s₂])
        (by simp [s₂, State.setReg]; omega) with
      ⟨s₃, t₃, hex₃, ht₃, hadj₃, hvalid₃, hr10₃⟩
    have hmul : (rem + 1) * (274 * n + 31 * totalAdjEntries lists + 59) =
        (274 * n + 31 * totalAdjEntries lists + 59) +
          rem * (274 * n + 31 * totalAdjEntries lists + 59) := by
      rw [Nat.add_one_mul, Nat.add_comm]
    refine ⟨s₃, 3 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, hadj₃, hvalid₃, hr10₃⟩

/-- Specification for `disjointPathsProg`: executes `k` rounds of augmenting-path search on `G`
in at most `k * (274 * n + 31 * totalAdjEntries lists + 59) + 41 * n + 29` steps (`O(k (n + m))`
time), preserving `IsAdjList` and producing a valid path encoding
`ValidPathState G a_base (a_base + 1) (a_base + 2) s'` with `s'.regs (r_base + 10) ≤ k`. -/
theorem Triple.disjointPathsProg_spec {w n k : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ)
    (a_start a_end a_entries a_A a_B a_base : ℕ) (r_base : ℕ)
    (ha_start : a_start < a_base) (ha_end : a_end < a_base) (ha_ent : a_entries < a_base)
    (ha_A : a_A < a_base) (ha_B : a_B < a_base)
    (hw : 1 < 2 ^ w) (h2n_w : 2 * n < 2 ^ w) (hk_w : k < 2 ^ w)
    (hent_w : ∀ s, IsAdjList G a_start a_end a_entries lists s →
      (s.arrs a_entries).length < 2 ^ w) :
    ⦃fun s => IsAdjList G a_start a_end a_entries lists s ∧
      ∃ (hA : (s.arrs a_A).length = n) (hB : (s.arrs a_B).length = n),
        (∀ u : Fin n, (s.arrs a_A)[u.1]'(by rw [hA]; exact u.2) ≤ 1) ∧
        (∀ u : Fin n, (s.arrs a_B)[u.1]'(by rw [hB]; exact u.2) ≤ 1)⦄[w]
      disjointPathsProg n k a_start a_end a_entries a_A a_B a_base r_base
    ⦃fun s' => IsAdjList G a_start a_end a_entries lists s' ∧
      ValidPathState G a_base (a_base + 1) (a_base + 2) s' ∧
      s'.regs (r_base + 10) ≤ k⦄ ≤
      fun _ => k * (274 * n + 31 * totalAdjEntries lists + 59) + 41 * n + 29 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  intro s₀ ⟨hadj₀, hA_len₀, hB_len₀, hA_bound₀, hB_bound₀⟩
  -- 1. allocFillArr a_base (.const n) (.const 0) (r_base + 3)
  rcases Triple.allocFillArr_const a_base n 0 (r_base + 3) hw hn_w h0_w s₀ trivial with
    ⟨s₁, t₁, hex₁, ht₁, harr_u₁⟩
  dsimp only at ht₁
  -- 2. allocFillArr (a_base + 1) (.const n) (.const n) (r_base + 3)
  rcases Triple.allocFillArr_const (a_base + 1) n n (r_base + 3) hw hn_w hn_w s₁ trivial with
    ⟨s₂, t₂, hex₂, ht₂, harr_p₂⟩
  dsimp only at ht₂
  -- 3. allocFillArr (a_base + 2) (.const n) (.const n) (r_base + 3)
  rcases Triple.allocFillArr_const (a_base + 2) n n (r_base + 3) hw hn_w hn_w s₂ trivial with
    ⟨s₃, t₃, hex₃, ht₃, harr_s₃⟩
  dsimp only at ht₃
  have harr_lt₃ : ∀ a < a_base, s₃.arrs a = s₀.arrs a := by
    intro a ha
    have hnot1 : (a : Arr) ∉ (allocFillArr a_base (.const n) (.const 0) (r_base + 3)).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, show (a : Arr) ≠ a_base by omega]
    have hnot2 : (a : Arr) ∉ (allocFillArr (a_base + 1) (.const n) (.const n) (r_base + 3)).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, show (a : Arr) ≠ a_base + 1 by omega]
    have hnot3 : (a : Arr) ∉ (allocFillArr (a_base + 2) (.const n) (.const n) (r_base + 3)).writtenArrs := by
      simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs, show (a : Arr) ≠ a_base + 2 by omega]
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₃ hnot3,
      Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2,
      Exec.arrs_eq_of_not_mem_writtenArrs hex₁ hnot1]
  have hnot2_u : (a_base : Arr) ∉ (allocFillArr (a_base + 1) (.const n) (.const n) (r_base + 3)).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs]
  have hnot3_u : (a_base : Arr) ∉ (allocFillArr (a_base + 2) (.const n) (.const n) (r_base + 3)).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs]
  have hnot3_p : (a_base + 1 : Arr) ∉ (allocFillArr (a_base + 2) (.const n) (.const n) (r_base + 3)).writtenArrs := by
    simp [allocFillArr, fillArr, forUp, Cmd.writtenArrs]
  have harr_u₃ : s₃.arrs a_base = List.replicate n 0 := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₃ hnot3_u,
      Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot2_u, harr_u₁]
  have harr_p₃ : s₃.arrs (a_base + 1) = List.replicate n n := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₃ hnot3_p, harr_p₂]
  -- 4. .alloc (a_base + 5) (.const (2 * n))
  let s₄ := s₃.setArr (a_base + 5) (List.replicate (2 * n) 0)
  have hex₄ : Exec w (.alloc (a_base + 5) (.const (2 * n))) s₃ s₄ (1 + 2 * n) :=
    .alloc (by simp [Expr.eval, checkWord, h2n_w])
  -- 5. .assign (r_base + 10) (.const 0), .assign (r_base + 9) (.const 0)
  let s₅ := s₄.setReg (r_base + 10) 0
  have hex₅ : Exec w (.assign (r_base + 10) (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg (r_base + 9) 0
  have hex₆ : Exec w (.assign (r_base + 9) (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr_lt₆ : ∀ a < a_base, s₆.arrs a = s₀.arrs a := by
    intro a ha
    simp only [s₆, s₅, s₄, State.setReg_arrs,
      State.setArr_arrs_ne _ _ (show (a : Arr) ≠ a_base + 5 by omega)]
    exact harr_lt₃ a ha
  have hadj₆ : IsAdjList G a_start a_end a_entries lists s₆ :=
    hadj₀.of_arrs_eq (harr_lt₆ a_start ha_start) (harr_lt₆ a_end ha_end) (harr_lt₆ a_entries ha_ent)
  have hvalid₆ : ValidPathState G a_base (a_base + 1) (a_base + 2) s₆ := by
    refine ⟨by simp [s₆, s₅, s₄, harr_u₃],
      by simp [s₆, s₅, s₄, harr_p₃],
      by simp [s₆, s₅, s₄, harr_s₃],
      fun u => by simp [s₆, s₅, s₄, harr_u₃],
      fun u => by simp [s₆, s₅, s₄, harr_p₃],
      fun u => by simp [s₆, s₅, s₄, harr_s₃],
      fun u _ => by simp [s₆, s₅, s₄, harr_s₃],
      fun u v heq => by
        simp only [s₆, s₅, s₄, State.setReg_arrs,
          State.setArr_arrs_ne _ _ (show (a_base + 2 : Arr) ≠ a_base + 5 by omega),
          harr_s₃, List.getElem_replicate] at heq
        have := v.2
        omega⟩
  have hA₆ : s₆.arrs a_A = s₀.arrs a_A := harr_lt₆ a_A ha_A
  have hB₆ : s₆.arrs a_B = s₀.arrs a_B := harr_lt₆ a_B ha_B
  -- 6. Outer loop
  rcases disjointPathsOuterLoop_exec G lists a_start a_end a_entries a_A a_B a_base r_base
      ha_start ha_end ha_ent ha_A ha_B hw h2n_w hk_w k 0 (by omega)
      hadj₆ (hent_w s₆ hadj₆)
      (by rw [hA₆]; exact hA_len₀) (fun u => by simp only [hA₆]; exact hA_bound₀ u)
      (by rw [hB₆]; exact hB_len₀) (fun u => by simp only [hB₆]; exact hB_bound₀ u)
      (by simp [s₆, s₅, s₄]) hvalid₆ (by simp [s₆])
      (by simp [s₆, s₅, State.setReg]) with
    ⟨s₇, t₇, hex₇, ht₇, hadj₇, hvalid₇, hr10₇⟩
  refine ⟨s₇, t₁ + (t₂ + (t₃ + ((1 + 2 * n) + (2 + (2 + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by dsimp only; omega,
    hadj₇, hvalid₇, hr10₇⟩

end GraphMinor.Compute


