module

public import GraphMinor.Compute.Algorithm41Aux2

/-!
# Pass 1 Preprocessing, Base Configurations, and Boundary Merging for GM XIII (4.1)

This file implements Pass 1 (`alg41PreprocProg`), the 13 canonical local base configurations
(`baseCfg < 13`), and the sorted boundary-list merge gadget (`mergeBoundaryLists`,
`mergeBoundaryProg`) for the Word RAM implementation of Algorithm (4.1) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem* (pages 75–76).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Unified Core Input `Alg41CoreInput` and Parent-Normalization Congruence -/

/-- Unified core input for the Word RAM implementation of GM XIII Algorithm (4.1) with parameters
`ξ, ω : ℕ`. Both `Alg41Input ξ ω` and `Alg41CodeInput ξ ω` convert directly into
`Alg41CoreInput ξ ω`. -/
structure Alg41CoreInput (ξ ω : ℕ) where
  /-- The input digraph `G`. -/
  G : ComputeDigraph
  /-- The root subset `Z ⊆ V(G)`. -/
  Z : Finset (Fin G.numVerts)
  /-- Bound `|Z| ≤ ξ`. -/
  hZ : Z.card ≤ ξ
  /-- Number of vertices `t` of the branch-decomposition tree `T`. -/
  t : ℕ
  /-- The tree `T` is non-empty (`0 < t`). -/
  ht : 0 < t
  /-- Linear size bound `t ≤ 2 * |E(G)| + 1`. -/
  ht_le : t ≤ 2 * G.numEdges + 1
  /-- Normalized parent map `p : ℕ → ℕ` with `p 0 = 0`. -/
  p : ℕ → ℕ
  /-- Root parent normalization `p 0 = 0`. -/
  hp0 : p 0 = 0
  /-- Parent invariant `p z < z` for all `0 < z < t`. -/
  hp : ∀ z, 0 < z → z < t → p z < z
  /-- Leaf assignment `τ : Fin G.numEdges → Fin t`. -/
  τ : Fin G.numEdges → Fin t
  /-- Every tree vertex `x : Fin t` has at most 3 children (`(childrenFinset t p x.1).card ≤ 3`). -/
  hch : ∀ x : Fin t, (childrenFinset t p x.1).card ≤ 3
  /-- At most 1 edge `e` of `G` maps to any tree node `x`. -/
  hleaf : ∀ x : ℕ, (Finset.univ.filter (fun e : Fin G.numEdges => (τ e).1 = x)).card ≤ 1
  /-- Intermediate boundary size bound `≤ 2 + 3 * (ω + ξ)`. -/
  hQ_acc : ∀ x < t, ∀ k, x + 1 ≤ k → k ≤ t →
    (pieceZ G Z (dpAccEB G p τ x k)).card ≤ 2 + 3 * (ω + ξ)
  /-- Subtree boundary size bound `≤ ω + ξ` at every non-root node `0 < c < t`. -/
  hQ_child : ∀ c, 0 < c → c < t →
    (pieceZ G Z (dpEB G p τ c)).card ≤ ω + ξ

/-- Size parameter `ε(G) = |E(G)| + |V(G)| + 1` for `Alg41CoreInput ξ ω`. -/
def alg41CoreSize {ξ ω : ℕ} (x : Alg41CoreInput ξ ω) : ℕ :=
  x.G.numEdges + x.G.numVerts + 1

/-- Flat word-list encoding of `Alg41CoreInput ξ ω`:
`[numVerts, numEdges, t] ++ head ++ tail ++ bitSetList Z ++ p ++ τ`. -/
def encAlg41CoreIn {ξ ω : ℕ} (x : Alg41CoreInput ξ ω) : List ℕ :=
  [x.G.numVerts, x.G.numEdges, x.t] ++
  List.ofFn (fun e => (x.G.head e).1) ++
  List.ofFn (fun e => (x.G.tail e).1) ++
  bitSetList x.Z ++
  List.ofFn (fun z : Fin x.t => x.p z.1) ++
  List.ofFn (fun e => (x.τ e).1)

theorem p_lt_t_of_core {ξ ω : ℕ} (x : Alg41CoreInput ξ ω) (z : Fin x.t) :
    x.p z.1 < x.t := by
  by_cases hz : z.1 = 0
  · rw [hz, x.hp0]; exact x.ht
  · exact Nat.lt_trans (x.hp z.1 (Nat.pos_of_ne_zero hz) z.2) z.2

theorem inSubtree_congr_pos {p₁ p₂ : ℕ → ℕ} (h : ∀ z > 0, p₁ z = p₂ z) (x : ℕ) :
    ∀ y : ℕ, inSubtree p₁ x y = inSubtree p₂ x y := by
  intro y
  induction y using Nat.strong_induction_on with
  | h y ih =>
    cases y with
    | zero =>
      unfold inSubtree
      rfl
    | succ y =>
      unfold inSubtree
      rw [h (y + 1) (by omega)]
      split_ifs with hyx hpy
      · rfl
      · exact ih (p₂ (y + 1)) hpy
      · rfl

theorem parentTree_congr_pos {t : ℕ} {p₁ p₂ : ℕ → ℕ} (h : ∀ z > 0, p₁ z = p₂ z) :
    parentTree t p₁ = parentTree t p₂ := by
  ext u v
  simp only [parentTree]
  constructor <;> rintro ⟨hne, h1 | h2⟩
  · refine ⟨hne, Or.inl ⟨h1.1, ?_⟩⟩
    rw [← h u.1 (by omega), h1.2]
  · refine ⟨hne, Or.inr ⟨h2.1, ?_⟩⟩
    rw [← h v.1 (by omega), h2.2]
  · refine ⟨hne, Or.inl ⟨h1.1, ?_⟩⟩
    rw [h u.1 (by omega), h1.2]
  · refine ⟨hne, Or.inr ⟨h2.1, ?_⟩⟩
    rw [h v.1 (by omega), h2.2]

theorem dpEB_congr_pos {t : ℕ} (G : ComputeDigraph) {p₁ p₂ : ℕ → ℕ}
    (h : ∀ z > 0, p₁ z = p₂ z) (τ : Fin G.numEdges → Fin t) (x : ℕ) :
    dpEB G p₁ τ x = dpEB G p₂ τ x := by
  ext e
  simp [dpEB, inSubtree_congr_pos h x (τ e).1]

theorem dpAccEB_congr_pos {t : ℕ} (G : ComputeDigraph) {p₁ p₂ : ℕ → ℕ}
    (h : ∀ z > 0, p₁ z = p₂ z) (τ : Fin G.numEdges → Fin t) (x k : ℕ) :
    dpAccEB G p₁ τ x k = dpAccEB G p₂ τ x k := by
  ext e
  simp only [dpAccEB, Finset.mem_filter, Finset.mem_univ, true_and]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨c, hxc, hck, hpc, hsub⟩
    rw [h c.1 (by omega)] at hpc
    rw [inSubtree_congr_pos h c.1 (τ e).1] at hsub
    exact ⟨c, hxc, hck, hpc, hsub⟩
  · rintro ⟨c, hxc, hck, hpc, hsub⟩
    rw [← h c.1 (by omega)] at hpc
    rw [← inSubtree_congr_pos h c.1 (τ e).1] at hsub
    exact ⟨c, hxc, hck, hpc, hsub⟩

theorem childrenFinset_congr_pos {t : ℕ} {p₁ p₂ : ℕ → ℕ}
    (h : ∀ z > 0, p₁ z = p₂ z) (x : ℕ) :
    childrenFinset t p₁ x = childrenFinset t p₂ x := by
  ext c
  simp only [childrenFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun hxc => ?_
  rw [h c.1 (by omega)]

/-! ### Section 2: Pure Preprocessing Functions (`incCountAt`, `leafEdgeAt`, `childrenUpTo`) -/

/-- Edges `< k` incident with vertex `v`. -/
def incEdgesBefore (G : ComputeDigraph) (k : ℕ) (v : Fin G.numVerts) :
    Finset (Fin G.numEdges) :=
  Finset.univ.filter (fun e : Fin G.numEdges => e.1 < k ∧ digraphIncident G v e)

/-- Recursive accumulator for incident edge counts after scanning the first `k` edges. -/
def incCountAt (G : ComputeDigraph) : ℕ → Fin G.numVerts → ℕ
  | 0, _ => 0
  | k + 1, v =>
    incCountAt G k v +
      if hk : k < G.numEdges then
        if v = G.head ⟨k, hk⟩ ∨ v = G.tail ⟨k, hk⟩ then 1 else 0
      else 0

theorem incEdgesBefore_zero (G : ComputeDigraph) (v : Fin G.numVerts) :
    incEdgesBefore G 0 v = ∅ := by
  ext e
  simp [incEdgesBefore]

theorem incEdgesBefore_full (G : ComputeDigraph) (v : Fin G.numVerts) :
    incEdgesBefore G G.numEdges v = incEdges G v := by
  ext e
  simp [incEdgesBefore, incEdges]

theorem incEdgesBefore_succ (G : ComputeDigraph) {k : ℕ} (hk : k < G.numEdges)
    (v : Fin G.numVerts) :
    incEdgesBefore G (k + 1) v =
      if v = G.head ⟨k, hk⟩ ∨ v = G.tail ⟨k, hk⟩ then
        insert ⟨k, hk⟩ (incEdgesBefore G k v)
      else
        incEdgesBefore G k v := by
  split_ifs with hinc <;> ext e <;>
    simp only [incEdgesBefore, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] <;>
    unfold digraphIncident
  · constructor
    · rintro ⟨hlt, he⟩
      by_cases hek : e.1 = k
      · exact Or.inl (Fin.ext hek)
      · exact Or.inr ⟨by omega, he⟩
    · rintro (heq | ⟨hlt, he⟩)
      · subst heq
        rcases hinc with h1 | h2
        · exact ⟨Nat.lt_succ_self _, Or.inl h1.symm⟩
        · exact ⟨Nat.lt_succ_self _, Or.inr h2.symm⟩
      · exact ⟨by omega, he⟩
  · constructor
    · rintro ⟨hlt, he⟩
      have hek : e.1 ≠ k := by
        intro heq
        have he_eq : e = ⟨k, hk⟩ := Fin.ext heq
        subst he_eq
        rcases he with h1 | h2
        · exact hinc (Or.inl h1.symm)
        · exact hinc (Or.inr h2.symm)
      exact ⟨by omega, he⟩
    · rintro ⟨hlt, he⟩
      exact ⟨by omega, he⟩

theorem incCountAt_eq_card_incEdgesBefore (G : ComputeDigraph) (k : ℕ) (hk : k ≤ G.numEdges)
    (v : Fin G.numVerts) :
    incCountAt G k v = (incEdgesBefore G k v).card := by
  induction k with
  | zero => simp [incCountAt, incEdgesBefore_zero]
  | succ k ih =>
    have hk_lt : k < G.numEdges := by omega
    simp only [incCountAt, hk_lt, ↓reduceDIte, ih (by omega), incEdgesBefore_succ G hk_lt v]
    split_ifs with hinc
    · have hnotMem : (⟨k, hk_lt⟩ : Fin G.numEdges) ∉ incEdgesBefore G k v := by
        simp [incEdgesBefore]
      rw [Finset.card_insert_of_notMem hnotMem]
    · omega

theorem incCountAt_full (G : ComputeDigraph) (v : Fin G.numVerts) :
    incCountAt G G.numEdges v = totalInc G v := by
  rw [incCountAt_eq_card_incEdgesBefore G G.numEdges (le_refl _), incEdgesBefore_full, totalInc]

/-- Recursive accumulator for the unique leaf edge `e + 1` assigned to tree node `x`. -/
def leafEdgeAt {m t : ℕ} (τ : Fin m → Fin t) : ℕ → Fin t → ℕ
  | 0, _ => 0
  | k + 1, x =>
    if hk : k < m then
      if τ ⟨k, hk⟩ = x then k + 1 else leafEdgeAt τ k x
    else
      leafEdgeAt τ k x

theorem leafEdgeAt_le {m t : ℕ} (τ : Fin m → Fin t) (k : ℕ) (x : Fin t) :
    leafEdgeAt τ k x ≤ m := by
  induction k with
  | zero => simp [leafEdgeAt]
  | succ k ih =>
    simp only [leafEdgeAt]
    split_ifs with hk hτ
    · omega
    · exact ih
    · exact ih

theorem leafEdgeAt_spec {m t : ℕ} (τ : Fin m → Fin t) (k : ℕ) (hk : k ≤ m) (x : Fin t) :
    (leafEdgeAt τ k x = 0 → ∀ e : Fin m, e.1 < k → τ e ≠ x) ∧
    (∀ e₀ : ℕ, leafEdgeAt τ k x = e₀ + 1 →
      ∃ he₀ : e₀ < k, τ ⟨e₀, Nat.lt_of_lt_of_le he₀ hk⟩ = x) := by
  induction k with
  | zero =>
    refine ⟨fun _ e he => by omega, fun e₀ h => by simp [leafEdgeAt] at h⟩
  | succ k ih =>
    have hk_lt : k < m := by omega
    rcases ih (by omega) with ⟨ih0, ihS⟩
    simp only [leafEdgeAt, hk_lt, ↓reduceDIte]
    by_cases hτ : τ ⟨k, hk_lt⟩ = x <;> simp only [hτ, ↓reduceIte]
    · refine ⟨fun h _ _ => by omega, fun e₀ h => ?_⟩
      have heq : k = e₀ := Nat.succ.inj h
      subst heq
      exact ⟨Nat.lt_succ_self k, hτ⟩
    · refine ⟨fun h0 e he => ?_, fun e₀ hS => ?_⟩
      · by_cases hek : e.1 = k
        · have he_eq : e = ⟨k, hk_lt⟩ := Fin.ext hek
          rw [he_eq]
          exact hτ
        · exact ih0 h0 e (by omega)
      · rcases ihS e₀ hS with ⟨he₀, hτ₀⟩
        exact ⟨by omega, hτ₀⟩

theorem filter_tau_eq_empty_of_leafEdgeAt_zero {m t : ℕ} (τ : Fin m → Fin t) (x : Fin t)
    (h0 : leafEdgeAt τ m x = 0) :
    Finset.univ.filter (fun e : Fin m => (τ e).1 = x.1) = ∅ := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro heq
  exact (leafEdgeAt_spec τ m (le_refl m) x).1 h0 e e.2 (Fin.ext heq)

theorem filter_tau_eq_singleton_of_leafEdgeAt_succ {m t : ℕ} (τ : Fin m → Fin t) (x : Fin t)
    (hleaf : (Finset.univ.filter (fun e : Fin m => (τ e).1 = x.1)).card ≤ 1)
    {e₀ : ℕ} (hS : leafEdgeAt τ m x = e₀ + 1) :
    ∃ he₀ : e₀ < m,
      (τ ⟨e₀, he₀⟩).1 = x.1 ∧
      Finset.univ.filter (fun e : Fin m => (τ e).1 = x.1) = {⟨e₀, he₀⟩} := by
  rcases (leafEdgeAt_spec τ m (le_refl m) x).2 e₀ hS with ⟨he₀, hτ₀⟩
  have hτ_val : (τ ⟨e₀, he₀⟩).1 = x.1 := congrArg Fin.val hτ₀
  refine ⟨he₀, hτ_val, ?_⟩
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro he
    exact Finset.card_le_one.mp hleaf e
      (Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩)
      ⟨e₀, he₀⟩
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ_val⟩)
  · rintro rfl
    exact hτ_val

/-- List of children `< k` of tree node `x` in increasing order:
`c ∈ [1, k)` with `p c = x`. -/
def childrenUpTo (p : ℕ → ℕ) (x k : ℕ) : List ℕ :=
  (List.range k).filter (fun c => decide (0 < c ∧ p c = x))

@[simp]
theorem childrenUpTo_zero (p : ℕ → ℕ) (x : ℕ) : childrenUpTo p x 0 = [] := rfl

@[simp]
theorem childrenUpTo_one (p : ℕ → ℕ) (x : ℕ) : childrenUpTo p x 1 = [] := rfl

theorem childrenUpTo_succ_of_pos (p : ℕ → ℕ) (x : ℕ) {k : ℕ} (hk : 0 < k) :
    childrenUpTo p x (k + 1) =
      if p k = x then childrenUpTo p x k ++ [k] else childrenUpTo p x k := by
  unfold childrenUpTo
  rw [List.range_succ, List.filter_append]
  by_cases hpk : p k = x
  · simp [hk, hpk]
  · simp [hk, hpk]

theorem childrenUpTo_eq_nil_of_le {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) {x k : ℕ} (hx : x < t) (hk : k ≤ x + 1) :
    childrenUpTo p x k = [] := by
  unfold childrenUpTo
  rw [List.filter_eq_nil_iff]
  intro c hc
  rw [List.mem_range] at hc
  simp only [decide_eq_true_eq, not_and]
  intro hc_pos
  have hpc : p c < c := hp c hc_pos (by omega)
  omega

theorem mem_childrenUpTo_iff {p : ℕ → ℕ} {x k c : ℕ} :
    c ∈ childrenUpTo p x k ↔ c < k ∧ 0 < c ∧ p c = x := by
  simp [childrenUpTo]

theorem length_childrenUpTo_le_card_childrenFinset {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (x : ℕ) {k : ℕ} (hk : k ≤ t) :
    (childrenUpTo p x k).length ≤ (childrenFinset t p x).card := by
  rcases Nat.eq_zero_or_pos t with rfl | ht_pos
  · have hk0 : k = 0 := by omega
    subst hk0
    simp
  have hnodup : (childrenUpTo p x k).Nodup :=
    List.Nodup.filter _ List.nodup_range
  let f : ℕ → Fin t := fun c => if hc : c < t then ⟨c, hc⟩ else ⟨0, ht_pos⟩
  have hinj : ∀ a ∈ childrenUpTo p x k, ∀ b ∈ childrenUpTo p x k, f a = f b → a = b := by
    intro a ha b hb hfab
    have ha_lt : a < t := Nat.lt_of_lt_of_le (mem_childrenUpTo_iff.mp ha).1 hk
    have hb_lt : b < t := Nat.lt_of_lt_of_le (mem_childrenUpTo_iff.mp hb).1 hk
    simpa [f, ha_lt, hb_lt] using congrArg Fin.val hfab
  have hsub : ((childrenUpTo p x k).map f).toFinset ⊆ childrenFinset t p x := by
    intro c hc
    rw [List.mem_toFinset, List.mem_map] at hc
    rcases hc with ⟨a, ha, rfl⟩
    rcases mem_childrenUpTo_iff.mp ha with ⟨ha_k, ha_pos, hpa⟩
    have ha_t : a < t := Nat.lt_of_lt_of_le ha_k hk
    have hxa : x < a := hpa ▸ hp a ha_pos ha_t
    simp [f, ha_t, childrenFinset, hxa, hpa]
  have hcard_map : ((childrenUpTo p x k).map f).toFinset.card = (childrenUpTo p x k).length := by
    rw [List.card_toFinset, List.dedup_eq_self.mpr (hnodup.map_on hinj), List.length_map]
  rw [← hcard_map]
  exact Finset.card_le_card hsub

theorem childrenUpTo_eq_drop_filter {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) {x : ℕ} (hx : x < t) :
    childrenUpTo p x t = ((List.range t).drop (x + 1)).filter (fun c => decide (p c = x)) := by
  have hsplit : List.range t = List.range (x + 1) ++ (List.range t).drop (x + 1) := by
    have h1 := (List.take_append_drop (x + 1) (List.range t)).symm
    rw [List.take_range, Nat.min_eq_left (by omega)] at h1
    exact h1
  unfold childrenUpTo
  conv_lhs => rw [hsplit, List.filter_append]
  have hnil : (List.range (x + 1)).filter (fun c => decide (0 < c ∧ p c = x)) = [] :=
    childrenUpTo_eq_nil_of_le hp hx (le_refl _)
  rw [hnil, List.nil_append]
  apply List.filter_congr
  intro c hc
  have hc_ge : x + 1 ≤ c := by
    rcases List.mem_iff_getElem.mp hc with ⟨i, hi, rfl⟩
    simp
  have hc_pos : 0 < c := by omega
  simp [hc_pos]

theorem drop_range_filter_eq_nil {t k : ℕ} {P : ℕ → Bool}
    (h : ((List.range t).drop k).filter P = []) :
    ∀ k', k ≤ k' → k' < t → P k' = false := by
  generalize hrem : t - k = rem
  induction rem generalizing k with
  | zero =>
    intro k' hk1 hk2; omega
  | succ rem ih =>
    have hk_lt : k < t := by omega
    have hdrop : (List.range t).drop k = k :: (List.range t).drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [hk_lt]), List.getElem_range]
    rw [hdrop, List.filter_cons] at h
    cases hPk : P k
    · simp only [hPk, Bool.false_eq_true, ↓reduceIte] at h
      intro k' hk1 hk2
      by_cases heq : k' = k
      · subst heq; exact hPk
      · exact ih h (by omega) k' (by omega) hk2
    · simp [hPk] at h

theorem drop_range_filter_eq_cons {t k c : ℕ} {P : ℕ → Bool} {cs' : List ℕ}
    (h : ((List.range t).drop k).filter P = c :: cs') :
    k ≤ c ∧ c < t ∧ P c = true ∧
    (∀ k', k ≤ k' → k' < c → P k' = false) ∧
    ((List.range t).drop (c + 1)).filter P = cs' := by
  generalize hrem : t - k = rem
  induction rem generalizing k with
  | zero =>
    have hle : (List.range t).length ≤ k := by simp; omega
    rw [List.drop_of_length_le hle] at h
    simp at h
  | succ rem ih =>
    have hk_lt : k < t := by omega
    have hdrop : (List.range t).drop k = k :: (List.range t).drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [hk_lt]), List.getElem_range]
    rw [hdrop, List.filter_cons] at h
    cases hPk : P k
    · simp only [hPk, Bool.false_eq_true, ↓reduceIte] at h
      rcases ih h (by omega) with ⟨hk1_c, hc_t, hPc, hfalse, hrest⟩
      refine ⟨by omega, hc_t, hPc, fun k' hk'1 hk'2 => ?_, hrest⟩
      by_cases heq : k' = k
      · subst heq; exact hPk
      · exact hfalse k' (by omega) hk'2
    · simp only [hPk, ↓reduceIte, List.cons.injEq] at h
      rcases h with ⟨ rfl, rfl ⟩
      exact ⟨le_refl k, hk_lt, hPk, fun _ h1 h2 => by omega, rfl⟩

/-! ### Section 3: Pass 1 Word RAM Program (`alg41PreprocProg`) and Execution Proof -/

/-- Array index constants for Algorithm (4.1). -/
abbrev a_head : Arr := 10
abbrev a_tail : Arr := 11
abbrev a_Z : Arr := 12
abbrev a_p : Arr := 13
abbrev a_tau : Arr := 14
abbrev a_tot : Arr := 15
abbrev a_edge : Arr := 16
abbrev a_cap : Arr := 17
abbrev a_degC : Arr := 18
abbrev a_ch : Arr := 19

/-- Loop body of `edgeScanProg` at edge `r_10 = e`. -/
def edgeScanBody : Cmd :=
  .seq (.assign 11 (.read a_head (.reg 10)))
    (.seq (.assign 12 (.read a_tail (.reg 10)))
      (.seq (.assign 13 (.read a_tau (.reg 10)))
        (.seq (.assign 14 (.read a_tot (.reg 11)))
          (.seq (.write a_tot (.reg 11) (.op .add (.reg 14) (.const 1)))
            (.seq (.ite (.op .eq (.reg 12) (.reg 11))
                .skip
                (.seq (.assign 14 (.read a_tot (.reg 12)))
                  (.write a_tot (.reg 12) (.op .add (.reg 14) (.const 1)))))
              (.write a_edge (.reg 13) (.op .add (.reg 10) (.const 1))))))))

/-- Scan edges `e = 0 .. m - 1` to populate `a_tot` (`totalInc`) and `a_edge` (`leafEdgeAt`). -/
def edgeScanProg : Cmd :=
  .seq (.alloc a_tot (.reg 0))
    (.seq (.alloc a_edge (.reg 2))
      (.seq (.assign 10 (.const 0))
        (forUp 10 (.reg 1) edgeScanBody)))

/-- Loop body of `capInitProg` at vertex `r_10 = v`. -/
def capInitBody : Cmd :=
  .seq (.assign 11 (.read a_Z (.reg 10)))
    (.ite (.op .eq (.reg 11) (.const 1))
      (.write a_cap (.reg 10) (.op .add (.reg 1) (.const 1)))
      (.seq (.assign 12 (.read a_tot (.reg 10)))
        (.write a_cap (.reg 10) (.reg 12))))

/-- Populate `a_cap[v] = capVal G Z v` for `v = 0 .. n - 1`. -/
def capInitProg : Cmd :=
  .seq (.alloc a_cap (.reg 0))
    (.seq (.assign 10 (.const 0))
      (forUp 10 (.reg 0) capInitBody))

/-- Loop body of `childScanProg` at node `r_10 = c` (`1 ≤ c < t`). -/
def childScanBody : Cmd :=
  .seq (.assign 11 (.read a_p (.reg 10)))
    (.seq (.assign 12 (.read a_degC (.reg 11)))
      (.seq (.assign 13 (.op .add (.op .mul (.const 3) (.reg 11)) (.reg 12)))
        (.seq (.write a_ch (.reg 13) (.reg 10))
          (.write a_degC (.reg 11) (.op .add (.reg 12) (.const 1))))))

/-- Scan tree nodes `c = 1 .. t - 1` to populate `a_degC` and `a_ch`. -/
def childScanProg : Cmd :=
  .seq (.alloc a_degC (.reg 2))
    (.seq (.assign 10 (.op .mul (.const 3) (.reg 2)))
      (.seq (.alloc a_ch (.reg 10))
        (.seq (.assign 10 (.const 1))
          (forUp 10 (.reg 2) childScanBody))))

/-- Complete Pass 1 preprocessing program (`alg41PreprocProg`) in `O(ε)` time. -/
def alg41PreprocProg : Cmd :=
  .seq (.assign 0 (.read inArr (.const 0)))
    (.seq (.assign 1 (.read inArr (.const 1)))
      (.seq (.assign 2 (.read inArr (.const 2)))
        (.seq (readSliceProg inArr (.const 3) a_head (.reg 1) 10)
          (.seq (readSliceProg inArr (.op .add (.const 3) (.reg 1)) a_tail (.reg 1) 10)
            (.seq (readSliceProg inArr
                (.op .add (.const 3) (.op .mul (.const 2) (.reg 1))) a_Z (.reg 0) 10)
              (.seq (readSliceProg inArr
                  (.op .add (.op .add (.const 3) (.op .mul (.const 2) (.reg 1))) (.reg 0))
                  a_p (.reg 2) 10)
                (.seq (readSliceProg inArr
                    (.op .add (.op .add (.op .add (.const 3) (.op .mul (.const 2) (.reg 1))) (.reg 0)) (.reg 2))
                    a_tau (.reg 1) 10)
                  (.seq edgeScanProg
                    (.seq capInitProg childScanProg)))))))))

private theorem set_ofFn {n : ℕ} (f : Fin n → ℕ) (i : Fin n) (val : ℕ) :
    (List.ofFn f).set i.1 val = List.ofFn (fun j : Fin n => if j = i then val else f j) := by
  apply List.ext_getElem (by simp)
  intro k hk1 hk2
  have hk_n : k < n := by simpa using hk2
  rw [List.getElem_ofFn]
  by_cases hki : k = i.1
  · have hki_fin : (⟨k, hk_n⟩ : Fin n) = i := Fin.ext hki
    subst hki
    rw [List.getElem_set_self hk1]
    simp [hki_fin]
  · have hki_fin : (⟨k, hk_n⟩ : Fin n) ≠ i := fun h => hki (congrArg Fin.val h)
    rw [List.getElem_set_ne (Ne.symm hki) hk1, List.getElem_ofFn]
    simp [hki_fin]

theorem edgeScanLoop_exec {w ξ ω : ℕ} (x : Alg41CoreInput ξ ω)
    (hw : 1 < 2 ^ w) (hn_w : x.G.numVerts < 2 ^ w) (hm1_w : x.G.numEdges + 1 < 2 ^ w)
    (ht_w : x.t < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = x.G.numEdges) {s : State}
    (hr0 : s.regs 0 = x.G.numVerts)
    (hr1 : s.regs 1 = x.G.numEdges)
    (hr2 : s.regs 2 = x.t)
    (hr10 : s.regs 10 = k)
    (hhead : s.arrs a_head = List.ofFn (fun e => (x.G.head e).1))
    (htail : s.arrs a_tail = List.ofFn (fun e => (x.G.tail e).1))
    (htau : s.arrs a_tau = List.ofFn (fun e => (x.τ e).1))
    (htot : s.arrs a_tot = List.ofFn (incCountAt x.G k))
    (hedge : s.arrs a_edge = List.ofFn (leafEdgeAt x.τ k)) :
    ∃ s' time,
      Exec w (forUp 10 (.reg 1) edgeScanBody) s s' time ∧
      time ≤ 3 + 45 * rem ∧
      s'.arrs a_tot = List.ofFn (totalInc x.G) ∧
      s'.arrs a_edge = List.ofFn (leafEdgeAt x.τ x.G.numEdges) ∧
      (∀ a : Arr, a ≠ a_tot → a ≠ a_edge → s'.arrs a = s.arrs a) ∧
      (∀ r < 10, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : x.G.numEdges < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = x.G.numEdges := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 10) (.reg 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr1, hm_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, hedge, fun _ _ _ => rfl, fun _ _ => rfl⟩
    rw [htot]
    congr 1
    funext v
    exact incCountAt_full x.G v
  | succ rem ih =>
    have hk_lt : k < x.G.numEdges := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 10) (.reg 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr1, hk_w, hm_w, hk_lt, hw]
    let e : Fin x.G.numEdges := ⟨k, hk_lt⟩
    let u_h := x.G.head e
    let u_t := x.G.tail e
    let z_e := x.τ e
    have huh_w : u_h.1 < 2 ^ w := Nat.lt_trans u_h.2 hn_w
    have hut_w : u_t.1 < 2 ^ w := Nat.lt_trans u_t.2 hn_w
    have hze_w : z_e.1 < 2 ^ w := Nat.lt_trans z_e.2 ht_w
    -- Read `a_head[k]`, `a_tail[k]`, `a_tau[k]`
    let s₁ := s.setReg 11 u_h.1
    have hex₁ : Exec w (.assign 11 (.read a_head (.reg 10))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr10, hk_w, hhead, hk_lt, e, u_h, huh_w])
    let s₂ := s₁.setReg 12 u_t.1
    have hex₂ : Exec w (.assign 12 (.read a_tail (.reg 10))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr10, hk_w, htail, hk_lt, e, u_t, hut_w])
    let s₃ := s₂.setReg 13 z_e.1
    have hex₃ : Exec w (.assign 13 (.read a_tau (.reg 10))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hr10, hk_w, htau, hk_lt, e, z_e, hze_w])
    -- Read `a_tot[u_h]` and write `a_tot[u_h] := c_h + 1`
    let c_h := incCountAt x.G k u_h
    have hch_le : c_h ≤ k := by
      dsimp [c_h]
      rw [incCountAt_eq_card_incEdgesBefore x.G k (by omega)]
      have hsub : incEdgesBefore x.G k u_h ⊆ Finset.univ.filter (fun d : Fin x.G.numEdges => d.1 < k) := by
        intro d hd; simp [incEdgesBefore] at hd; simp [hd.1]
      refine (Finset.card_le_card hsub).trans ?_
      have hcard_lt : (Finset.univ.filter (fun d : Fin x.G.numEdges => d.1 < k)).card ≤ (Finset.range k).card := by
        rw [← Finset.card_image_of_injective _ Fin.val_injective]
        refine Finset.card_le_card fun a ha => ?_
        rcases Finset.mem_image.mp ha with ⟨d, hd, rfl⟩
        simp at hd ⊢; exact hd
      simpa using hcard_lt
    have hch_w : c_h < 2 ^ w := by omega
    have hch1_w : c_h + 1 < 2 ^ w := by omega
    let s₄ := s₃.setReg 14 c_h
    have hex₄ : Exec w (.assign 14 (.read a_tot (.reg 11))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, htot, u_h.2, c_h, huh_w, hch_w])
    let s₅ := s₄.writeArr a_tot u_h.1 (c_h + 1)
    have hex₅ : Exec w (.write a_tot (.reg 11) (.op .add (.reg 14) (.const 1))) s₄ s₅ 5 :=
      .write (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, huh_w])
        (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hch_w, hw, hch1_w])
        (by simp [s₄, s₃, s₂, s₁, htot, u_h.2])
    have htot₅ : s₅.arrs a_tot =
        List.ofFn (fun v : Fin x.G.numVerts => if v = u_h then c_h + 1 else incCountAt x.G k v) := by
      simp only [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, htot]
      exact set_ofFn (incCountAt x.G k) u_h (c_h + 1)
    -- Conditional increment on `u_t ≠ u_h`
    have hex₆_ex : ∃ s₆ t₆,
        Exec w (.ite (.op .eq (.reg 12) (.reg 11))
          .skip
          (.seq (.assign 14 (.read a_tot (.reg 12)))
            (.write a_tot (.reg 12) (.op .add (.reg 14) (.const 1))))) s₅ s₆ t₆ ∧
        t₆ ≤ 11 ∧
        s₆.arrs a_tot = List.ofFn (incCountAt x.G (k + 1)) ∧
        (∀ a : Arr, a ≠ a_tot → s₆.arrs a = s₅.arrs a) ∧
        (∀ r : Reg, r ≠ 14 → s₆.regs r = s₅.regs r) := by
      by_cases h_eq : u_t.1 = u_h.1
      · have h_fin_eq : u_t = u_h := Fin.ext h_eq
        have hcond_eq : (Expr.op .eq (.reg 12) (.reg 11)).eval w s₅ = some 1 := by
          simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            h_eq, huh_w, hw]
        refine ⟨s₅, 3 + 1, .ite_true hcond_eq (by decide) (.skip s₅), by omega, ?_,
          fun _ _ => rfl, fun _ _ => rfl⟩
        rw [htot₅]
        congr 1
        funext v
        simp only [incCountAt, hk_lt, ↓reduceDIte]
        change (if v = u_h then c_h + 1 else incCountAt x.G k v) =
          incCountAt x.G k v + if v = u_h ∨ v = u_t then 1 else 0
        simp only [h_fin_eq, or_self]
        by_cases hvu : v = u_h <;> simp [hvu, c_h]
      · have h_fin_ne : u_t ≠ u_h := fun h => h_eq (congrArg Fin.val h)
        have hcond_ne : (Expr.op .eq (.reg 12) (.reg 11)).eval w s₅ = some 0 := by
          simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            h_eq, huh_w, hut_w, h0_w]
        let c_t := incCountAt x.G k u_t
        have hct_le : c_t ≤ k := by
          dsimp [c_t]
          rw [incCountAt_eq_card_incEdgesBefore x.G k (by omega)]
          have hsub : incEdgesBefore x.G k u_t ⊆ Finset.univ.filter (fun d : Fin x.G.numEdges => d.1 < k) := by
            intro d hd; simp [incEdgesBefore] at hd; simp [hd.1]
          refine (Finset.card_le_card hsub).trans ?_
          have hcard_lt : (Finset.univ.filter (fun d : Fin x.G.numEdges => d.1 < k)).card ≤ (Finset.range k).card := by
            rw [← Finset.card_image_of_injective _ Fin.val_injective]
            refine Finset.card_le_card fun a ha => ?_
            rcases Finset.mem_image.mp ha with ⟨d, hd, rfl⟩
            simp at hd ⊢; exact hd
          simpa using hcard_lt
        have hct_w : c_t < 2 ^ w := by omega
        have hct1_w : c_t + 1 < 2 ^ w := by omega
        have hr12_5 : s₅.regs 12 = u_t.1 := by simp [s₅, s₄, s₃, s₂]
        let s₅' := s₅.setReg 14 c_t
        have hex_r : Exec w (.assign 14 (.read a_tot (.reg 12))) s₅ s₅' 3 :=
          .assign (by simp [Expr.eval, checkWord, hr12_5, htot₅, u_t.2, h_fin_ne, c_t, hut_w, hct_w])
        let s₆ := s₅'.writeArr a_tot u_t.1 (c_t + 1)
        have hex_w : Exec w (.write a_tot (.reg 12) (.op .add (.reg 14) (.const 1))) s₅' s₆ 5 :=
          .write (by simp [s₅', Expr.eval, checkWord, hr12_5, hut_w])
            (by simp [s₅', Expr.eval, BinOp.eval, BinOp.raw,
              checkWord, hct_w, hw, hct1_w])
            (by simp [s₅', htot₅, u_t.2])
        refine ⟨s₆, 3 + (3 + 5), .ite_false hcond_ne (.seq hex_r hex_w), by omega, ?_,
          fun a ha => by simp [s₆, s₅', ha],
          fun r hr => by simp [s₆, s₅', State.setReg_regs_ne _ _ hr]⟩
        simp only [s₆, s₅', State.writeArr_arrs_self, State.setReg_arrs, htot₅, set_ofFn]
        congr 1
        funext v
        simp only [incCountAt, hk_lt, ↓reduceDIte]
        change (if v = u_t then c_t + 1 else if v = u_h then c_h + 1 else incCountAt x.G k v) =
          incCountAt x.G k v + if v = u_h ∨ v = u_t then 1 else 0
        by_cases hvt : v = u_t
        · subst hvt; simp [h_fin_ne, c_t]
        · by_cases hvh : v = u_h
          · subst hvh; simp [hvt, c_h]
          · simp [hvt, hvh]
    rcases hex₆_ex with ⟨s₆, t₆, hex₆, ht₆, htot₆, harr₆, hreg₆⟩
    -- Write `a_edge[z_e] := k + 1`
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hedge₆ : s₆.arrs a_edge = List.ofFn (leafEdgeAt x.τ k) := by
      rw [harr₆ a_edge (by decide)]
      simp [s₅, s₄, s₃, s₂, s₁, hedge]
    have hr13_6 : s₆.regs 13 = z_e.1 := by
      rw [hreg₆ 13 (by decide)]; simp [s₅, s₄, s₃]
    have hr10_6 : s₆.regs 10 = k := by
      rw [hreg₆ 10 (by decide)]; simp [s₅, s₄, s₃, s₂, s₁, hr10]
    let s₇ := s₆.writeArr a_edge z_e.1 (k + 1)
    have hex₇ : Exec w (.write a_edge (.reg 13) (.op .add (.reg 10) (.const 1))) s₆ s₇ 5 :=
      .write (by simp [Expr.eval, checkWord, hr13_6, hze_w])
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_6, hk_w, hw, hk1_w])
        (by simp [hedge₆, z_e.2])
    have hedge₇ : s₇.arrs a_edge = List.ofFn (leafEdgeAt x.τ (k + 1)) := by
      simp only [s₇, State.writeArr_arrs_self, hedge₆, set_ofFn]
      congr 1
      funext z
      simp only [leafEdgeAt, hk_lt, ↓reduceDIte]
      change (if z = z_e then k + 1 else leafEdgeAt x.τ k z) =
        if z_e = z then k + 1 else leafEdgeAt x.τ k z
      by_cases hzz : z = z_e
      · subst hzz; simp
      · have hne : z_e ≠ z := Ne.symm hzz
        simp [hzz, hne]
    -- Increment `r_10 := k + 1`
    let s₈ := s₇.setReg 10 (k + 1)
    have hex_inc : Exec w (.assign 10 (.op .add (.reg 10) (.const 1))) s₇ s₈ 4 :=
      .assign (by simp [s₇, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_6, hk_w, hw, hk1_w])
    have hex_body : Exec w edgeScanBody s s₇ (3 + (3 + (3 + (3 + (5 + (t₆ + 5)))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
    rcases ih (k + 1) (by omega) (s := s₈)
        (by simp [s₈, s₇, hreg₆ 0 (by decide), s₅, s₄, s₃, s₂, s₁, hr0])
        (by simp [s₈, s₇, hreg₆ 1 (by decide), s₅, s₄, s₃, s₂, s₁, hr1])
        (by simp [s₈, s₇, hreg₆ 2 (by decide), s₅, s₄, s₃, s₂, s₁, hr2])
        (by simp [s₈])
        (by simp [s₈, s₇, harr₆ a_head (by decide), s₅, s₄, s₃, s₂, s₁, hhead])
        (by simp [s₈, s₇, harr₆ a_tail (by decide), s₅, s₄, s₃, s₂, s₁, htail])
        (by simp [s₈, s₇, harr₆ a_tau (by decide), s₅, s₄, s₃, s₂, s₁, htau])
        (by simp [s₈, s₇, htot₆])
        (by simp [s₈, hedge₇]) with
      ⟨s₉, t₉, hex₉, ht₉, htot₉, hedge₉, harr₉, hreg₉⟩
    refine ⟨s₉, 3 + ((3 + (3 + (3 + (3 + (5 + (t₆ + 5)))))) + 4) + t₉,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex₉,
      by omega, htot₉, hedge₉,
      fun a ha_tot ha_edge => by
        rw [harr₉ a ha_tot ha_edge]
        simp [s₈, s₇, ha_edge, harr₆ a ha_tot, s₅, s₄, s₃, s₂, s₁, ha_tot],
      fun r hr => by
        rw [hreg₉ r hr, State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega)]
        simp only [s₇, State.writeArr_regs, hreg₆ r (by dsimp [Reg] at hr ⊢; omega),
          s₅, s₄, s₃, s₂, s₁, State.setReg_regs]
        split_ifs <;> first | rfl | (dsimp [Reg] at *; omega)⟩

theorem capInitLoop_exec {w ξ ω : ℕ} (x : Alg41CoreInput ξ ω)
    (hw : 1 < 2 ^ w) (hn_w : x.G.numVerts < 2 ^ w) (hm1_w : x.G.numEdges + 1 < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = x.G.numVerts) {s : State}
    (hr0 : s.regs 0 = x.G.numVerts)
    (hr1 : s.regs 1 = x.G.numEdges)
    (hr10 : s.regs 10 = k)
    (hZ : s.arrs a_Z = bitSetList x.Z)
    (htot : s.arrs a_tot = List.ofFn (totalInc x.G))
    (hcap : s.arrs a_cap =
      List.ofFn (fun v : Fin x.G.numVerts => if v.1 < k then capVal x.G x.Z v else 0)) :
    ∃ s' time,
      Exec w (forUp 10 (.reg 0) capInitBody) s s' time ∧
      time ≤ 3 + 22 * rem ∧
      s'.arrs a_cap = List.ofFn (capVal x.G x.Z) ∧
      (∀ a : Arr, a ≠ a_cap → s'.arrs a = s.arrs a) ∧
      (∀ r < 10, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : x.G.numEdges < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = x.G.numVerts := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 10) (.reg 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr0, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    rw [hcap]
    congr 1
    funext v
    simp [v.2]
  | succ rem ih =>
    have hk_lt : k < x.G.numVerts := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 10) (.reg 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr0, hk_w, hn_w, hk_lt, hw]
    let v : Fin x.G.numVerts := ⟨k, hk_lt⟩
    let b_z := if v ∈ x.Z then 1 else 0
    have hbz_w : b_z < 2 ^ w := by dsimp [b_z]; split_ifs <;> omega
    let s₁ := s.setReg 11 b_z
    have hex₁ : Exec w (.assign 11 (.read a_Z (.reg 10))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr10, hk_w, hZ, bitSetList, hk_lt, v, b_z, hbz_w])
    have hex₂_ex : ∃ s₂ t₂,
        Exec w (.ite (.op .eq (.reg 11) (.const 1))
          (.write a_cap (.reg 10) (.op .add (.reg 1) (.const 1)))
          (.seq (.assign 12 (.read a_tot (.reg 10)))
            (.write a_cap (.reg 10) (.reg 12)))) s₁ s₂ t₂ ∧
        t₂ ≤ 10 ∧
        s₂.arrs a_cap =
          List.ofFn (fun u : Fin x.G.numVerts => if u.1 < k + 1 then capVal x.G x.Z u else 0) ∧
        (∀ a : Arr, a ≠ a_cap → s₂.arrs a = s.arrs a) ∧
        (∀ r ≤ 10, s₂.regs r = s.regs r) := by
      by_cases hvZ : v ∈ x.Z
      · have hbz_1 : b_z = 1 := by simp [b_z, hvZ]
        have hcond_z : (Expr.op .eq (.reg 11) (.const 1)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hbz_1, hw]
        let s₂ := s₁.writeArr a_cap k (x.G.numEdges + 1)
        have hex_w : Exec w (.write a_cap (.reg 10) (.op .add (.reg 1) (.const 1))) s₁ s₂ 5 :=
          .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hr10, hk_w])
            (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hr1, hm_w, hw, hm1_w])
            (by simp [s₁, hcap, hk_lt])
        refine ⟨s₂, 3 + 5, .ite_true hcond_z (by decide) hex_w, by omega, ?_,
          fun a ha => by simp [s₂, s₁, ha],
          fun r hr => by simp only [s₂, s₁, State.writeArr_regs, State.setReg_regs]; split_ifs <;> first | rfl | (dsimp [Reg] at *; omega)⟩
        simp only [s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs, hcap]
        change (List.ofFn _).set v.1 (x.G.numEdges + 1) = _
        rw [set_ofFn]
        congr 1
        funext u
        by_cases huv : u = v
        · subst huv; simp [v, capVal, hvZ]
        · have hne : u.1 ≠ k := fun h => huv (Fin.ext h)
          simp only [huv, ↓reduceIte]
          split_ifs <;> omega
      · have hbz_0 : b_z = 0 := by simp [b_z, hvZ]
        have hcond_z : (Expr.op .eq (.reg 11) (.const 1)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hbz_0, h0_w, hw]
        let tot_v := totalInc x.G v
        have htot_le : tot_v ≤ x.G.numEdges := totalInc_le_numEdges x.G v
        have htot_w : tot_v < 2 ^ w := by omega
        let s₁' := s₁.setReg 12 tot_v
        have hex_r : Exec w (.assign 12 (.read a_tot (.reg 10))) s₁ s₁' 3 :=
          .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr10, hk_w, htot, hk_lt, v, tot_v, htot_w])
        let s₂ := s₁'.writeArr a_cap k tot_v
        have hex_w : Exec w (.write a_cap (.reg 10) (.reg 12)) s₁' s₂ 3 :=
          .write (by simp [s₁', s₁, State.setReg, Expr.eval, checkWord, hr10, hk_w])
            (by simp [s₁', Expr.eval, checkWord, htot_w])
            (by simp [s₁', s₁, hcap, hk_lt])
        refine ⟨s₂, 3 + (3 + 3), .ite_false hcond_z (.seq hex_r hex_w), by omega, ?_,
          fun a ha => by simp [s₂, s₁', s₁, ha],
          fun r hr => by simp only [s₂, s₁', s₁, State.writeArr_regs, State.setReg_regs]; split_ifs <;> first | rfl | (dsimp [Reg] at *; omega)⟩
        simp only [s₂, s₁', s₁, State.writeArr_arrs_self, State.setReg_arrs, hcap]
        change (List.ofFn _).set v.1 tot_v = _
        rw [set_ofFn]
        congr 1
        funext u
        by_cases huv : u = v
        · subst huv; simp [v, capVal, hvZ, tot_v]
        · have hne : u.1 ≠ k := fun h => huv (Fin.ext h)
          simp only [huv, ↓reduceIte]
          split_ifs <;> omega
    rcases hex₂_ex with ⟨s₂, t₂, hex₂, ht₂, hcap₂, harr₂, hreg₂⟩
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hr10_2 : s₂.regs 10 = k := (hreg₂ 10 (le_refl 10)).trans hr10
    let s₃ := s₂.setReg 10 (k + 1)
    have hex_inc : Exec w (.assign 10 (.op .add (.reg 10) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10_2, hk_w, hw, hk1_w])
    have hex_body : Exec w capInitBody s s₂ (3 + t₂) := .seq hex₁ hex₂
    rcases ih (k + 1) (by omega) (s := s₃)
        (by simp [s₃, hreg₂ 0 (by decide), hr0])
        (by simp [s₃, hreg₂ 1 (by decide), hr1])
        (by simp [s₃])
        (by simp [s₃, harr₂ a_Z (by decide), hZ])
        (by simp [s₃, harr₂ a_tot (by decide), htot])
        (by simp [s₃, hcap₂]) with
      ⟨s₄, t₄, hex₄, ht₄, hcap₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + t₂) + 4) + t₄,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
      by omega, hcap₄,
      fun a ha => by rw [harr₄ a ha]; simp [s₃, harr₂ a ha],
      fun r hr => by
        rw [hreg₄ r hr, State.setReg_regs_ne _ _ (by dsimp [Reg] at hr ⊢; omega)]
        exact hreg₂ r (by dsimp [Reg] at hr ⊢; omega)⟩

theorem childScanLoop_exec {w ξ ω : ℕ} (x : Alg41CoreInput ξ ω)
    (hw3 : 3 < 2 ^ w) (ht3_w : 3 * x.t < 2 ^ w)
    (rem k : ℕ) (hk_pos : 1 ≤ k) (hrem : k + rem = x.t) {s : State}
    (hr2 : s.regs 2 = x.t)
    (hr10 : s.regs 10 = k)
    (hp_arr : s.arrs a_p = List.ofFn (fun z : Fin x.t => x.p z.1))
    (hdegC : s.arrs a_degC = List.ofFn (fun z : Fin x.t => (childrenUpTo x.p z.1 k).length))
    (hch : s.arrs a_ch =
      List.ofFn (fun idx : Fin (3 * x.t) => (childrenUpTo x.p (idx.1 / 3) k).getD (idx.1 % 3) 0)) :
    ∃ s' time,
      Exec w (forUp 10 (.reg 2) childScanBody) s s' time ∧
      time ≤ 3 + 30 * rem ∧
      s'.arrs a_degC = List.ofFn (fun z : Fin x.t => (childrenUpTo x.p z.1 x.t).length) ∧
      s'.arrs a_ch =
        List.ofFn (fun idx : Fin (3 * x.t) => (childrenUpTo x.p (idx.1 / 3) x.t).getD (idx.1 % 3) 0) ∧
      (∀ a : Arr, a ≠ a_degC → a ≠ a_ch → s'.arrs a = s.arrs a) ∧
      (∀ r < 10, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have ht_w : x.t < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = x.t := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 10) (.reg 2)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr2, ht_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hdegC, hch, fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < x.t := by omega
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 10) (.reg 2)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr2, hk_w, ht_w, hk_lt, hw]
    let px_val := x.p k
    have hpx_lt_k : px_val < k := x.hp k (by omega) hk_lt
    have hpx_lt_t : px_val < x.t := by omega
    have hpx_w : px_val < 2 ^ w := by omega
    let px : Fin x.t := ⟨px_val, hpx_lt_t⟩
    let d := (childrenUpTo x.p px_val k).length
    have hd_lt3 : d < 3 := by
      have hle3 : (childrenUpTo x.p px_val (k + 1)).length ≤ 3 :=
        (length_childrenUpTo_le_card_childrenFinset x.hp px_val (by omega)).trans (x.hch px)
      rw [childrenUpTo_succ_of_pos x.p px_val (by omega)] at hle3
      simp only [px_val, ↓reduceIte, List.length_append, List.length_singleton] at hle3
      dsimp [d, px_val] at hle3 ⊢
      omega
    have hd_w : d < 2 ^ w := by omega
    have hd1_w : d + 1 < 2 ^ w := by omega
    have h3px_w : 3 * px_val < 2 ^ w := by omega
    have hidx_lt : 3 * px_val + d < 3 * x.t := by omega
    have hidx_w : 3 * px_val + d < 2 ^ w := by omega
    -- 1. `r_11 := a_p[k]` (`= px_val`)
    let s₁ := s.setReg 11 px_val
    have hex₁ : Exec w (.assign 11 (.read a_p (.reg 10))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr10, hk_w, hp_arr, hk_lt, px_val, hpx_w])
    -- 2. `r_12 := a_degC[px_val]` (`= d`)
    let s₂ := s₁.setReg 12 d
    have hex₂ : Exec w (.assign 12 (.read a_degC (.reg 11))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hpx_w, hdegC, hpx_lt_t, d, hd_w])
    -- 3. `r_13 := 3 * r_11 + r_12`
    let s₃ := s₂.setReg 13 (3 * px_val + d)
    have hex₃ : Exec w (.assign 13 (.op .add (.op .mul (.const 3) (.reg 11)) (.reg 12))) s₂ s₃ 6 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw3, hpx_w, h3px_w, hd_w, hidx_w])
    -- 4. `a_ch[3 * px_val + d] := k`
    let s₄ := s₃.writeArr a_ch (3 * px_val + d) k
    have hex₄ : Exec w (.write a_ch (.reg 13) (.reg 10)) s₃ s₄ 3 :=
      .write (by simp [s₃, State.setReg, Expr.eval, checkWord, hidx_w])
        (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr10, hk_w])
        (by simp [s₃, s₂, s₁, hch, hidx_lt])
    -- 5. `a_degC[px_val] := d + 1`
    let s₅ := s₄.writeArr a_degC px_val (d + 1)
    have hex₅ : Exec w (.write a_degC (.reg 11) (.op .add (.reg 12) (.const 1))) s₄ s₅ 5 :=
      .write (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hpx_w])
        (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hd_w, hw, hd1_w])
        (by simp [s₄, s₃, s₂, s₁, hdegC, hpx_lt_t])
    have hdegC₅ : s₅.arrs a_degC = List.ofFn (fun z : Fin x.t => (childrenUpTo x.p z.1 (k + 1)).length) := by
      simp only [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_self,
        State.writeArr_arrs_ne _ _ _ (by decide : a_degC ≠ a_ch), State.setReg_arrs, hdegC]
      change (List.ofFn _).set px.1 (d + 1) = _
      rw [set_ofFn]
      congr 1
      funext z
      rw [childrenUpTo_succ_of_pos x.p z.1 (by omega)]
      by_cases hzp : z = px
      · subst hzp; simp [px, px_val, d]
      · have hne : x.p k ≠ z.1 := fun h => hzp (Fin.ext h.symm)
        simp [hzp, hne]
    have hch₅ : s₅.arrs a_ch =
        List.ofFn (fun idx : Fin (3 * x.t) => (childrenUpTo x.p (idx.1 / 3) (k + 1)).getD (idx.1 % 3) 0) := by
      simp only [s₅, s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ (by decide : a_ch ≠ a_degC),
        State.writeArr_arrs_self, State.setReg_arrs, hch]
      let target : Fin (3 * x.t) := ⟨3 * px_val + d, hidx_lt⟩
      change (List.ofFn _).set target.1 k = _
      rw [set_ofFn]
      congr 1
      funext idx
      rw [childrenUpTo_succ_of_pos x.p (idx.1 / 3) (by omega)]
      by_cases h_div : x.p k = idx.1 / 3
      · simp only [h_div, ↓reduceIte]
        have hlen_eq : (childrenUpTo x.p (idx.1 / 3) k).length = d := by
          rw [← h_div]
        by_cases h_mod : idx.1 % 3 = d
        · have h_idx : idx = target := by
            ext
            have := Nat.div_add_mod idx.1 3
            dsimp [target]
            omega
          simp only [h_idx, ↓reduceIte]
          have hdiv_t : target.1 / 3 = px_val := by dsimp [target]; omega
          have hmod_t : target.1 % 3 = d := by dsimp [target]; omega
          rw [hdiv_t, hmod_t, List.getD_eq_getElem?_getD,
              List.getElem?_append_right (le_refl d), Nat.sub_self, List.getElem?_cons_zero]
          rfl
        · have h_idx : idx ≠ target := by
            intro heq
            have hmod_t : target.1 % 3 = d := by dsimp [target]; omega
            exact h_mod (congrArg (fun u : Fin (3 * x.t) => u.1 % 3) heq |>.trans hmod_t)
          simp only [h_idx, ↓reduceIte]
          by_cases hlt_d : idx.1 % 3 < d
          · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_append_left (by omega)]
          · have hgt_d : d + 1 ≤ idx.1 % 3 := by omega
            rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
      · have h_idx : idx ≠ target := by
          intro heq
          have hdiv_t : target.1 / 3 = px_val := by dsimp [target]; omega
          exact h_div (hdiv_t.symm.trans (congrArg (fun u : Fin (3 * x.t) => u.1 / 3) heq).symm)
        simp [h_div, h_idx]
    -- 6. Increment `r_10 := k + 1`
    have hk1_w : k + 1 < 2 ^ w := by omega
    let s₆ := s₅.setReg 10 (k + 1)
    have hex_inc : Exec w (.assign 10 (.op .add (.reg 10) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw,
        checkWord, hr10, hk_w, hw, hk1_w])
    have hex_body : Exec w childScanBody s s₅ (3 + (3 + (6 + (3 + 5)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
    rcases ih (k + 1) (by omega) (by omega) (s := s₆)
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hr2])
        (by simp [s₆])
        (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hp_arr])
        (by simp [s₆, hdegC₅])
        (by simp [s₆, hch₅]) with
      ⟨s₇, t₇, hex₇, ht₇, hdegC₇, hch₇, harr₇, hreg₇⟩
    refine ⟨s₇, 3 + ((3 + (3 + (6 + (3 + 5)))) + 4) + t₇,
      .while_true hcond (by omega) (.seq hex_body hex_inc) hex₇,
      by omega, hdegC₇, hch₇,
      fun a ha1 ha2 => by
        rw [harr₇ a ha1 ha2]
        simp [s₆, s₅, s₄, s₃, s₂, s₁, ha1, ha2],
      fun r hr => by
        rw [hreg₇ r hr]
        simp only [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_regs, State.writeArr_regs]
        split_ifs <;> first | rfl | (dsimp [Reg] at *; omega)⟩

theorem alg41PreprocProg_exec {w ξ ω : ℕ} (x : Alg41CoreInput ξ ω)
    (hw3 : 3 < 2 ^ w)
    (hsz_w : 7 * alg41CoreSize x < 2 ^ w)
    {s₀ : State}
    (hs₀ : s₀.arrs inArr = encAlg41CoreIn x) :
    ∃ s' time,
      Exec w alg41PreprocProg s₀ s' time ∧
      time ≤ 250 * alg41CoreSize x ∧
      s'.regs 0 = x.G.numVerts ∧
      s'.regs 1 = x.G.numEdges ∧
      s'.regs 2 = x.t ∧
      s'.arrs a_head = List.ofFn (fun e => (x.G.head e).1) ∧
      s'.arrs a_tail = List.ofFn (fun e => (x.G.tail e).1) ∧
      s'.arrs a_Z = bitSetList x.Z ∧
      s'.arrs a_p = List.ofFn (fun z : Fin x.t => x.p z.1) ∧
      s'.arrs a_tau = List.ofFn (fun e => (x.τ e).1) ∧
      s'.arrs a_tot = List.ofFn (totalInc x.G) ∧
      s'.arrs a_edge = List.ofFn (leafEdgeAt x.τ x.G.numEdges) ∧
      s'.arrs a_cap = List.ofFn (capVal x.G x.Z) ∧
      s'.arrs a_degC = List.ofFn (fun z : Fin x.t => (childrenUpTo x.p z.1 x.t).length) ∧
      s'.arrs a_ch =
        List.ofFn (fun idx : Fin (3 * x.t) => (childrenUpTo x.p (idx.1 / 3) x.t).getD (idx.1 % 3) 0) := by
  let n := x.G.numVerts
  let m := x.G.numEdges
  let t := x.t
  have ht_le := x.ht_le
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by unfold alg41CoreSize at hsz_w; omega
  have hm_w : m < 2 ^ w := by unfold alg41CoreSize at hsz_w; omega
  have hm1_w : m + 1 < 2 ^ w := by unfold alg41CoreSize at hsz_w; omega
  have ht_w : t < 2 ^ w := by unfold alg41CoreSize at hsz_w; omega
  have ht3_w : 3 * t < 2 ^ w := by unfold alg41CoreSize at hsz_w; omega
  have hlen_in : 3 ≤ (s₀.arrs inArr).length := by simp [hs₀, encAlg41CoreIn]
  -- Read `r_0 := n`, `r_1 := m`, `r_2 := t`
  let s₁ := s₀.setReg 0 n
  have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hs₀, encAlg41CoreIn, n, hn_w])
  let s₂ := s₁.setReg 1 m
  have hex₂ : Exec w (.assign 1 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw1, hs₀, encAlg41CoreIn, m, hm_w])
  let s₃ := s₂.setReg 2 t
  have hex₃ : Exec w (.assign 2 (.read inArr (.const 2))) s₂ s₃ 3 :=
    .assign (by simp [s₂, s₁, Expr.eval, checkWord, hw2, hs₀, encAlg41CoreIn, t, ht_w])
  let L_hdr : List ℕ := [n, m, t]
  let L_head : List ℕ := List.ofFn (fun e => (x.G.head e).1)
  let L_tail : List ℕ := List.ofFn (fun e => (x.G.tail e).1)
  let L_Z : List ℕ := bitSetList x.Z
  let L_p : List ℕ := List.ofFn (fun z : Fin x.t => x.p z.1)
  let L_tau : List ℕ := List.ofFn (fun e => (x.τ e).1)
  -- 1. `readSliceProg` for `a_head`
  have hhead_w : ∀ u ∈ L_head, u < 2 ^ w := by
    intro u hu; rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩; exact Nat.lt_trans (x.G.head e).2 hn_w
  rcases readSliceProg_exec (w := w) (n := m) (off := 3) inArr a_head (.const 3) 1 10
      (by decide) (by decide)
      L_hdr L_head (L_tail ++ L_Z ++ L_p ++ L_tau)
      (by simp [L_hdr]) (by simp [L_head, m]) hhead_w hw1
      (by unfold alg41CoreSize at hsz_w; omega)
      (s := s₃)
      (by simp [Expr.eval, checkWord, hw3])
      (by simp [s₃, s₂, s₁, hs₀, encAlg41CoreIn, L_hdr, L_head, L_tail, L_Z, L_p, L_tau, n, m, t])
      (by simp [s₃, s₂, State.setReg]) with
    ⟨s₄, t₄, hex₄, ht₄, hhead₄, harr₄, hreg₄⟩
  -- 2. `readSliceProg` for `a_tail`
  have htail_w : ∀ u ∈ L_tail, u < 2 ^ w := by
    intro u hu; rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩; exact Nat.lt_trans (x.G.tail e).2 hn_w
  rcases readSliceProg_exec (w := w) (n := m) (off := 3 + m) inArr a_tail (.op .add (.const 3) (.reg 1)) 1 10
      (by decide) (by decide)
      (L_hdr ++ L_head) L_tail (L_Z ++ L_p ++ L_tau)
      (by simp [L_hdr, L_head, m]; omega) (by simp [L_tail, m]) htail_w hw1
      (by unfold alg41CoreSize at hsz_w; omega)
      (s := s₄)
      (by simp only [Expr.eval]; rw [hreg₄ 1 (by decide)]; simp [s₃, s₂, State.setReg, BinOp.eval, BinOp.raw,
        checkWord, hw3, hm_w, show 3 + m < 2 ^ w by unfold alg41CoreSize at hsz_w; omega])
      (by rw [harr₄ inArr (by decide)]; simp [s₃, s₂, s₁, hs₀, encAlg41CoreIn, L_hdr, L_head, L_tail, L_Z, L_p, L_tau, n, m, t])
      (by rw [hreg₄ 1 (by decide)]; simp [s₃, s₂, State.setReg]) with
    ⟨s₅, t₅, hex₅, ht₅, htail₅, harr₅, hreg₅⟩
  -- 3. `readSliceProg` for `a_Z`
  have hZ_w : ∀ u ∈ L_Z, u < 2 ^ w := by
    intro u hu; dsimp [L_Z] at hu; rcases List.getElem_of_mem hu with ⟨i, hi, rfl⟩
    have := getElem_bitSetList_le_one x.Z i hi; omega
  rcases readSliceProg_exec (w := w) (n := n) (off := 3 + 2 * m)
      inArr a_Z (.op .add (.const 3) (.op .mul (.const 2) (.reg 1))) 0 10
      (by decide) (by decide)
      (L_hdr ++ L_head ++ L_tail) L_Z (L_p ++ L_tau)
      (by simp [L_hdr, L_head, L_tail, m]; omega) (by simp [L_Z, length_bitSetList, n]) hZ_w hw1
      (by unfold alg41CoreSize at hsz_w; omega)
      (s := s₅)
      (by simp only [Expr.eval]; rw [hreg₅ 1 (by decide), hreg₄ 1 (by decide)];
          simp [s₃, s₂, State.setReg, BinOp.eval, BinOp.raw, checkWord, hw2, hw3, hm_w,
            show 2 * m < 2 ^ w by unfold alg41CoreSize at hsz_w; omega,
            show 3 + 2 * m < 2 ^ w by unfold alg41CoreSize at hsz_w; omega])
      (by rw [harr₅ inArr (by decide), harr₄ inArr (by decide)];
          simp [s₃, s₂, s₁, hs₀, encAlg41CoreIn, L_hdr, L_head, L_tail, L_Z, L_p, L_tau, n, m, t])
      (by rw [hreg₅ 0 (by decide), hreg₄ 0 (by decide)]; simp [s₃, s₂, s₁, State.setReg]) with
    ⟨s₆, t₆, hex₆, ht₆, hZ₆, harr₆, hreg₆⟩
  -- 4. `readSliceProg` for `a_p`
  have hp_w : ∀ u ∈ L_p, u < 2 ^ w := by
    intro u hu; rcases List.mem_ofFn.mp hu with ⟨z, rfl⟩; exact Nat.lt_trans (p_lt_t_of_core x z) ht_w
  rcases readSliceProg_exec (w := w) (n := t) (off := 3 + 2 * m + n) inArr a_p
      (.op .add (.op .add (.const 3) (.op .mul (.const 2) (.reg 1))) (.reg 0)) 2 10
      (by decide) (by decide)
      (L_hdr ++ L_head ++ L_tail ++ L_Z) L_p L_tau
      (by simp [L_hdr, L_head, L_tail, L_Z, length_bitSetList, n, m]; omega) (by simp [L_p, t]) hp_w hw1
      (by unfold alg41CoreSize at hsz_w; omega)
      (s := s₆)
      (by simp only [Expr.eval];
          rw [hreg₆ 1 (by decide), hreg₅ 1 (by decide), hreg₄ 1 (by decide),
              hreg₆ 0 (by decide), hreg₅ 0 (by decide), hreg₄ 0 (by decide)];
          simp [s₃, s₂, s₁, State.setReg, BinOp.eval, BinOp.raw, checkWord, hw2, hw3, hm_w, hn_w,
            show 2 * m < 2 ^ w by unfold alg41CoreSize at hsz_w; omega,
            show 3 + 2 * m < 2 ^ w by unfold alg41CoreSize at hsz_w; omega,
            show 3 + 2 * m + n < 2 ^ w by unfold alg41CoreSize at hsz_w; omega])
      (by rw [harr₆ inArr (by decide), harr₅ inArr (by decide), harr₄ inArr (by decide)];
          simp [s₃, s₂, s₁, hs₀, encAlg41CoreIn, L_hdr, L_head, L_tail, L_Z, L_p, L_tau, n, m, t])
      (by rw [hreg₆ 2 (by decide), hreg₅ 2 (by decide), hreg₄ 2 (by decide)]; simp [s₃]) with
    ⟨s₇, t₇, hex₇, ht₇, hp₇, harr₇, hreg₇⟩
  -- 5. `readSliceProg` for `a_tau`
  have htau_w : ∀ u ∈ L_tau, u < 2 ^ w := by
    intro u hu; rcases List.mem_ofFn.mp hu with ⟨e, rfl⟩; exact Nat.lt_trans (x.τ e).2 ht_w
  rcases readSliceProg_exec (w := w) (n := m) (off := 3 + 2 * m + n + t) inArr a_tau
      (.op .add (.op .add (.op .add (.const 3) (.op .mul (.const 2) (.reg 1))) (.reg 0)) (.reg 2)) 1 10
      (by decide) (by decide)
      (L_hdr ++ L_head ++ L_tail ++ L_Z ++ L_p) L_tau []
      (by simp [L_hdr, L_head, L_tail, L_Z, L_p, length_bitSetList, n, m, t]; omega)
      (by simp [L_tau, m]) htau_w hw1
      (by unfold alg41CoreSize at hsz_w; omega)
      (s := s₇)
      (by simp only [Expr.eval];
          rw [hreg₇ 1 (by decide), hreg₆ 1 (by decide), hreg₅ 1 (by decide), hreg₄ 1 (by decide),
              hreg₇ 0 (by decide), hreg₆ 0 (by decide), hreg₅ 0 (by decide), hreg₄ 0 (by decide),
              hreg₇ 2 (by decide), hreg₆ 2 (by decide), hreg₅ 2 (by decide), hreg₄ 2 (by decide)];
          simp [s₃, s₂, s₁, State.setReg, BinOp.eval, BinOp.raw, checkWord, hw2, hw3, hm_w, hn_w, ht_w,
            show 2 * m < 2 ^ w by unfold alg41CoreSize at hsz_w; omega,
            show 3 + 2 * m < 2 ^ w by unfold alg41CoreSize at hsz_w; omega,
            show 3 + 2 * m + n < 2 ^ w by unfold alg41CoreSize at hsz_w; omega,
            show 3 + 2 * m + n + t < 2 ^ w by unfold alg41CoreSize at hsz_w; omega])
      (by rw [harr₇ inArr (by decide), harr₆ inArr (by decide), harr₅ inArr (by decide), harr₄ inArr (by decide)];
          simp [s₃, s₂, s₁, hs₀, encAlg41CoreIn, L_hdr, L_head, L_tail, L_Z, L_p, L_tau, n, m, t])
      (by rw [hreg₇ 1 (by decide), hreg₆ 1 (by decide), hreg₅ 1 (by decide), hreg₄ 1 (by decide)];
          simp [s₃, s₂, State.setReg]) with
    ⟨s₈, t₈, hex₈, ht₈, htau₈, harr₈, hreg₈⟩
  -- Extract registers and arrays at `s₈`
  have hr0_8 : s₈.regs 0 = n := by
    rw [hreg₈ 0 (by decide), hreg₇ 0 (by decide), hreg₆ 0 (by decide), hreg₅ 0 (by decide), hreg₄ 0 (by decide)]
    simp [s₃, s₂, s₁, State.setReg]
  have hr1_8 : s₈.regs 1 = m := by
    rw [hreg₈ 1 (by decide), hreg₇ 1 (by decide), hreg₆ 1 (by decide), hreg₅ 1 (by decide), hreg₄ 1 (by decide)]
    simp [s₃, s₂, State.setReg]
  have hr2_8 : s₈.regs 2 = t := by
    rw [hreg₈ 2 (by decide), hreg₇ 2 (by decide), hreg₆ 2 (by decide), hreg₅ 2 (by decide), hreg₄ 2 (by decide)]
    simp [s₃]
  have hhead₈ : s₈.arrs a_head = L_head := by
    rw [harr₈ a_head (by decide), harr₇ a_head (by decide), harr₆ a_head (by decide), harr₅ a_head (by decide)]
    exact hhead₄
  have htail₈ : s₈.arrs a_tail = L_tail := by
    rw [harr₈ a_tail (by decide), harr₇ a_tail (by decide), harr₆ a_tail (by decide)]
    exact htail₅
  have hZ₈ : s₈.arrs a_Z = L_Z := by
    rw [harr₈ a_Z (by decide), harr₇ a_Z (by decide)]
    exact hZ₆
  have hp₈ : s₈.arrs a_p = L_p := by
    rw [harr₈ a_p (by decide)]
    exact hp₇
  -- 6. `edgeScanProg`
  let s₈_1 := s₈.setArr a_tot (List.replicate n 0)
  have hex_e1 : Exec w (.alloc a_tot (.reg 0)) s₈ s₈_1 (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr0_8, hn_w])
  let s₈_2 := s₈_1.setArr a_edge (List.replicate t 0)
  have hex_e2 : Exec w (.alloc a_edge (.reg 2)) s₈_1 s₈_2 (1 + t) :=
    .alloc (by simp [s₈_1, Expr.eval, checkWord, hr2_8, ht_w])
  let s₈_3 := s₈_2.setReg 10 0
  have hex_e3 : Exec w (.assign 10 (.const 0)) s₈_2 s₈_3 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have htot_init : List.replicate n 0 = List.ofFn (incCountAt x.G 0) := by
    apply List.ext_getElem (by simp [n])
    intro i _ _; simp [incCountAt]
  have hedge_init : List.replicate t 0 = List.ofFn (leafEdgeAt x.τ 0) := by
    apply List.ext_getElem (by simp [t])
    intro i _ _; simp [leafEdgeAt]
  rcases edgeScanLoop_exec x hw1 hn_w hm1_w ht_w m 0 (by omega) (s := s₈_3)
      (by simp [s₈_3, s₈_2, s₈_1, State.setReg, hr0_8, n])
      (by simp [s₈_3, s₈_2, s₈_1, State.setReg, hr1_8, m])
      (by simp [s₈_3, s₈_2, s₈_1, State.setReg, hr2_8, t])
      (by simp [s₈_3])
      (by simp [s₈_3, s₈_2, s₈_1, hhead₈, L_head])
      (by simp [s₈_3, s₈_2, s₈_1, htail₈, L_tail])
      (by simp [s₈_3, s₈_2, s₈_1, htau₈, L_tau])
      (by simp [s₈_3, s₈_2, s₈_1, htot_init])
      (by simp [s₈_3, s₈_2, hedge_init]) with
    ⟨s₉, t₉, hex₉, ht₉, htot₉, hedge₉, harr₉, hreg₉⟩
  have hex_edge : Exec w edgeScanProg s₈ s₉ ((1 + n) + ((1 + t) + (2 + t₉))) :=
    .seq hex_e1 (.seq hex_e2 (.seq hex_e3 hex₉))
  -- 7. `capInitProg`
  have hr0_9 : s₉.regs 0 = n := by rw [hreg₉ 0 (by decide)]; simp [s₈_3, s₈_2, s₈_1, State.setReg, hr0_8]
  have hr1_9 : s₉.regs 1 = m := by rw [hreg₉ 1 (by decide)]; simp [s₈_3, s₈_2, s₈_1, State.setReg, hr1_8]
  have hr2_9 : s₉.regs 2 = t := by rw [hreg₉ 2 (by decide)]; simp [s₈_3, s₈_2, s₈_1, State.setReg, hr2_8]
  let s₉_1 := s₉.setArr a_cap (List.replicate n 0)
  have hex_c1 : Exec w (.alloc a_cap (.reg 0)) s₉ s₉_1 (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr0_9, hn_w])
  let s₉_2 := s₉_1.setReg 10 0
  have hex_c2 : Exec w (.assign 10 (.const 0)) s₉_1 s₉_2 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hcap_init :
      List.replicate n 0 = List.ofFn (fun v : Fin x.G.numVerts => if v.1 < 0 then capVal x.G x.Z v else 0) := by
    apply List.ext_getElem (by simp [n])
    intro i _ _; simp
  rcases capInitLoop_exec x hw1 hn_w hm1_w n 0 (by omega) (s := s₉_2)
      (by simp [s₉_2, s₉_1, State.setReg, hr0_9, n])
      (by simp [s₉_2, s₉_1, State.setReg, hr1_9, m])
      (by simp [s₉_2])
      (by simp [s₉_2, s₉_1]; rw [harr₉ a_Z (by decide) (by decide)]; simp [s₈_3, s₈_2, s₈_1, hZ₈, L_Z])
      (by simp [s₉_2, s₉_1, htot₉])
      (by simp [s₉_2, s₉_1, hcap_init]) with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hcap₁₀, harr₁₀, hreg₁₀⟩
  have hex_cap : Exec w capInitProg s₉ s₁₀ ((1 + n) + (2 + t₁₀)) :=
    .seq hex_c1 (.seq hex_c2 hex₁₀)
  -- 8. `childScanProg`
  have hr2_10 : s₁₀.regs 2 = t := by rw [hreg₁₀ 2 (by decide)]; simp [s₉_2, s₉_1, State.setReg, hr2_9]
  let s₁₀_1 := s₁₀.setArr a_degC (List.replicate t 0)
  have hex_ch1 : Exec w (.alloc a_degC (.reg 2)) s₁₀ s₁₀_1 (1 + t) :=
    .alloc (by simp [Expr.eval, checkWord, hr2_10, ht_w])
  let s₁₀_2 := s₁₀_1.setReg 10 (3 * t)
  have hex_ch2 : Exec w (.assign 10 (.op .mul (.const 3) (.reg 2))) s₁₀_1 s₁₀_2 4 :=
    .assign (by simp [s₁₀_1, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw3, hr2_10, ht_w, ht3_w])
  let s₁₀_3 := s₁₀_2.setArr a_ch (List.replicate (3 * t) 0)
  have hex_ch3 : Exec w (.alloc a_ch (.reg 10)) s₁₀_2 s₁₀_3 (1 + 3 * t) :=
    .alloc (by simp [s₁₀_2, Expr.eval, checkWord, ht3_w])
  let s₁₀_4 := s₁₀_3.setReg 10 1
  have hex_ch4 : Exec w (.assign 10 (.const 1)) s₁₀_3 s₁₀_4 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  have hdegC_init : List.replicate t 0 = List.ofFn (fun z : Fin x.t => (childrenUpTo x.p z.1 1).length) := by
    apply List.ext_getElem (by simp [t])
    intro i _ _; simp
  have hch_init :
      List.replicate (3 * t) 0 =
        List.ofFn (fun idx : Fin (3 * x.t) => (childrenUpTo x.p (idx.1 / 3) 1).getD (idx.1 % 3) 0) := by
    apply List.ext_getElem (by simp [t])
    intro i _ _; simp
  have ht_pos : 1 ≤ x.t := x.ht
  rcases childScanLoop_exec x hw3 ht3_w (t - 1) 1 (le_refl 1) (by omega) (s := s₁₀_4)
      (by simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1, State.setReg, hr2_10, t])
      (by simp [s₁₀_4])
      (by simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1];
          rw [harr₁₀ a_p (by decide)]; simp [s₉_2, s₉_1];
          rw [harr₉ a_p (by decide) (by decide)]; simp [s₈_3, s₈_2, s₈_1, hp₈, L_p])
      (by simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1, hdegC_init])
      (by simp [s₁₀_4, s₁₀_3, hch_init]) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hdegC₁₁, hch₁₁, harr₁₁, hreg₁₁⟩
  have hex_child : Exec w childScanProg s₁₀ s₁₁ ((1 + t) + (4 + ((1 + 3 * t) + (2 + t₁₁)))) :=
    .seq hex_ch1 (.seq hex_ch2 (.seq hex_ch3 (.seq hex_ch4 hex₁₁)))
  dsimp [Expr.cost] at ht₄ ht₅ ht₆ ht₇ ht₈
  refine ⟨s₁₁,
    3 + (3 + (3 + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + (((1 + n) + ((1 + t) + (2 + t₉))) +
      (((1 + n) + (2 + t₁₀)) + ((1 + t) + (4 + ((1 + 3 * t) + (2 + t₁₁))))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex_edge (.seq hex_cap hex_child))))))))),
    by unfold alg41CoreSize; dsimp [n, m, t] at *; omega,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdegC₁₁, hch₁₁⟩
  · rw [hreg₁₁ 0 (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1, State.setReg]
    rw [hreg₁₀ 0 (by decide)]; simp [s₉_2, s₉_1, State.setReg, hr0_9, n]
  · rw [hreg₁₁ 1 (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1, State.setReg]
    rw [hreg₁₀ 1 (by decide)]; simp [s₉_2, s₉_1, State.setReg, hr1_9, m]
  · rw [hreg₁₁ 2 (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1, State.setReg, hr2_10, t]
  · rw [harr₁₁ a_head (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1]
    rw [harr₁₀ a_head (by decide)]; simp [s₉_2, s₉_1]
    rw [harr₉ a_head (by decide) (by decide)]; simp [s₈_3, s₈_2, s₈_1, hhead₈, L_head]
  · rw [harr₁₁ a_tail (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1]
    rw [harr₁₀ a_tail (by decide)]; simp [s₉_2, s₉_1]
    rw [harr₉ a_tail (by decide) (by decide)]; simp [s₈_3, s₈_2, s₈_1, htail₈, L_tail]
  · rw [harr₁₁ a_Z (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1]
    rw [harr₁₀ a_Z (by decide)]; simp [s₉_2, s₉_1]
    rw [harr₉ a_Z (by decide) (by decide)]; simp [s₈_3, s₈_2, s₈_1, hZ₈, L_Z]
  · rw [harr₁₁ a_p (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1]
    rw [harr₁₀ a_p (by decide)]; simp [s₉_2, s₉_1]
    rw [harr₉ a_p (by decide) (by decide)]; simp [s₈_3, s₈_2, s₈_1, hp₈, L_p]
  · rw [harr₁₁ a_tau (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1]
    rw [harr₁₀ a_tau (by decide)]; simp [s₉_2, s₉_1]
    rw [harr₉ a_tau (by decide) (by decide)]; simp [s₈_3, s₈_2, s₈_1, htau₈, L_tau]
  · rw [harr₁₁ a_tot (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1]
    rw [harr₁₀ a_tot (by decide)]; simp [s₉_2, s₉_1, htot₉]
  · rw [harr₁₁ a_edge (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1]
    rw [harr₁₀ a_edge (by decide)]; simp [s₉_2, s₉_1, hedge₉]
  · rw [harr₁₁ a_cap (by decide) (by decide)]; simp [s₁₀_4, s₁₀_3, s₁₀_2, s₁₀_1, hcap₁₀]

end GraphMinor.Compute
