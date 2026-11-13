module

public import GraphMinor.GM02.Valency
public import GraphMinor.Minor.Basic
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import GraphMinor.GM02.ValencyIso

/-!
# Splitting a vertex

For II (4.8) the paper says (page 320): "We 'split' every vertex of $H$ with
valency $\ge 4$ into two adjacent vertices of valency $\ge 3$, repeatedly, in
all possible ways."

Splitting a vertex is the reverse of contracting an edge. So we say that `L`
comes from `K` by one split (`IsSplitStep K L`) when `L` has an edge `f` with
two distinct ends `x` and `y`, both of valency at least three, and `K` is
isomorphic to the graph obtained from `L` by contracting `f`. The merged
vertex then has valency `d(x) + d(y) - 2 ≥ 4` (`valency_mergeEdge_self`). A
split of `H` (`IsSplitOf H J`) is a graph obtained from a copy of `H` by
finitely many such steps.

This file proves the two facts about splits that (4.8) needs.

- A split of `H` has `H` as a minor (`IsSplitOf.isIsoMinor`), since
  contracting an edge gives a minor.
- A split of `H` has at most `|V(H)| + 2|E(H)|` vertices and at most
  `3|E(H)|` edges (`IsSplitOf.ncard_le`). Each step adds one vertex and one
  edge. It raises the sum of the valencies by two, and the sum of the numbers
  `min(d(v), 3)` by three. The second sum is at most the first, so the number
  of steps is at most the sum of the valencies of `H`, which is `2|E(H)|`.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Classical

universe u v u' v'

variable {α : Type u} {β : Type v}

/-- The vertex map that sends `y` to `x` and fixes every other vertex. -/
noncomputable def mergeMap (x y : α) (z : α) : α := if z = y then x else z

/-- The graph obtained from `L` by contracting the edge `f` with ends `x` and
`y`: the vertex `y` is identified with `x`, and `f` is deleted. Other edges
between `x` and `y` become loops. -/
noncomputable def mergeEdge (L : Graph α β) (f : β) (x y : α) : Graph α β :=
  (L.map (mergeMap x y)).deleteEdges {f}

/-- Graph Minors II, (4.8), page 320: one split. `L` comes from `K` by
splitting a vertex into two adjacent vertices `x` and `y` of valency at least
three: contracting the new edge `f` between them gives a copy of `K`. -/
def IsSplitStep (K L : Graph α β) : Prop :=
  ∃ f x y, L.IsLink f x y ∧ x ≠ y ∧ 3 ≤ valency L x ∧ 3 ≤ valency L y ∧
    Nonempty (Iso K (mergeEdge L f x y))

/-- Graph Minors II, (4.8), page 320: `J` is obtained from `H` by splitting
vertices repeatedly. -/
def IsSplitOf {α' : Type u'} {β' : Type v'} (H : Graph α' β') (J : Graph α β) : Prop :=
  ∃ J₀ : Graph α β, Nonempty (Iso H J₀) ∧ Relation.ReflTransGen IsSplitStep J₀ J

/-! ### The contracted graph -/

theorem mergeMap_eq_left_iff {x y z : α} : mergeMap x y z = x ↔ z = x ∨ z = y := by
  unfold mergeMap
  by_cases hz : z = y
  · simp [hz]
  · simp [hz]

theorem mergeMap_eq_of_ne {x y z v : α} (hvx : v ≠ x) (hvy : v ≠ y) :
    mergeMap x y z = v ↔ z = v := by
  unfold mergeMap
  by_cases hz : z = y
  · subst hz
    simp only [↓reduceIte]
    exact ⟨fun h => (hvx h.symm).elim, fun h => (hvy h.symm).elim⟩
  · simp [hz]

theorem mergeMap_of_ne {x y z : α} (hz : z ≠ y) : mergeMap x y z = z := by
  simp [mergeMap, hz]

@[simp] theorem mergeMap_right (x y : α) : mergeMap x y y = x := by simp [mergeMap]

theorem mergeEdge_isLink {L : Graph α β} {f e : β} {x y a b : α} :
    (mergeEdge L f x y).IsLink e a b ↔
      e ≠ f ∧ ∃ a₀ b₀, L.IsLink e a₀ b₀ ∧ mergeMap x y a₀ = a ∧ mergeMap x y b₀ = b := by
  simp only [mergeEdge, deleteEdges_isLink, map_isLink, mem_singleton_iff]
  constructor
  · rintro ⟨⟨a₀, b₀, h, rfl, rfl⟩, he⟩
    exact ⟨he, a₀, b₀, h, rfl, rfl⟩
  · rintro ⟨he, a₀, b₀, h, rfl, rfl⟩
    exact ⟨⟨a₀, b₀, h, rfl, rfl⟩, he⟩

theorem mergeEdge_edgeSet (L : Graph α β) (f : β) (x y : α) :
    E(mergeEdge L f x y) = E(L) \ {f} := by
  simp [mergeEdge]

theorem mergeEdge_vertexSet {L : Graph α β} {f : β} {x y : α} (hf : L.IsLink f x y)
    (hxy : x ≠ y) : V(mergeEdge L f x y) = V(L) \ {y} := by
  simp only [mergeEdge, vertexSet_deleteEdges, vertexSet_map]
  ext z
  constructor
  · rintro ⟨z₀, hz₀, rfl⟩
    by_cases h : z₀ = y
    · subst h
      simp only [mergeMap_right]
      exact ⟨hf.left_mem, hxy⟩
    · rw [mergeMap_of_ne h]
      exact ⟨hz₀, h⟩
  · rintro ⟨hz, hzy⟩
    exact ⟨z, hz, mergeMap_of_ne hzy⟩

theorem mergeEdge_inc {L : Graph α β} {f e : β} {x y a : α} :
    (mergeEdge L f x y).Inc e a ↔ e ≠ f ∧ ∃ a₀, L.Inc e a₀ ∧ mergeMap x y a₀ = a := by
  constructor
  · rintro ⟨b, h⟩
    obtain ⟨he, a₀, b₀, h', rfl, rfl⟩ := mergeEdge_isLink.1 h
    exact ⟨he, a₀, h'.inc_left, rfl⟩
  · rintro ⟨he, a₀, ⟨b₀, h⟩, rfl⟩
    exact ⟨mergeMap x y b₀, mergeEdge_isLink.2 ⟨he, a₀, b₀, h, rfl, rfl⟩⟩

theorem notMem_edgeSet_mergeEdge (L : Graph α β) (f : β) (x y : α) :
    f ∉ E(mergeEdge L f x y) := by
  rw [mergeEdge_edgeSet]
  exact fun h => h.2 rfl

/-! ### Valency after contracting an edge -/

theorem ite_mergeMap_eq_of_ne {x y v a : α} (hvx : v ≠ x) (hvy : v ≠ y) :
    (if v = mergeMap x y a then 1 else 0) = (if v = a then 1 else 0) := by
  unfold mergeMap
  by_cases hay : a = y
  · subst hay
    simp [hvx, hvy]
  · simp [hay]

theorem ite_mergeMap_eq_self {x y a : α} (hxy : x ≠ y) :
    (if x = mergeMap x y a then 1 else 0) =
      (if x = a then 1 else 0) + (if y = a then 1 else 0) := by
  unfold mergeMap
  by_cases hay : a = y
  · subst hay
    simp [hxy]
  · simp [hay, Ne.symm hay]

theorem valencyWeight_of_notMem {G : Graph α β} {e : β} (he : e ∉ E(G)) (x : α) :
    valencyWeight G e x = 0 := by
  unfold valencyWeight
  have h1 : ¬ G.Inc e x := fun h => he h.edge_mem
  have h2 : ¬ G.IsLoopAt e x := fun h => he h.edge_mem
  simp [h1, h2]

/-- Valency as a sum over any finite set of edge names that contains all
edges. -/
theorem valency_eq_sum_of_subset (G : Graph α β) {S : Finset β} (hS : E(G) ⊆ S) (x : α) :
    valency G x = ∑ e ∈ S, valencyWeight G e x := by
  have hE : E(G).Finite := S.finite_toSet.subset hS
  rw [valency_eq_sum G hE x]
  apply Finset.sum_subset
  · intro e he
    exact hS ((hE.mem_toFinset).1 he)
  · intro e _ he
    exact valencyWeight_of_notMem (fun h => he ((hE.mem_toFinset).2 h)) x

theorem valencyWeight_mergeEdge_of_ne {L : Graph α β} {f : β} {x y : α}
    (hf : L.IsLink f x y) (e : β) {v : α} (hvx : v ≠ x) (hvy : v ≠ y) :
    valencyWeight (mergeEdge L f x y) e v = valencyWeight L e v := by
  by_cases hef : e = f
  · subst hef
    rw [valencyWeight_of_notMem (notMem_edgeSet_mergeEdge L e x y), valencyWeight_eq_endpoints hf]
    simp [hvx, hvy]
  by_cases he : e ∈ E(L)
  · obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
    have hM : (mergeEdge L f x y).IsLink e (mergeMap x y a) (mergeMap x y b) :=
      mergeEdge_isLink.2 ⟨hef, a, b, hab, rfl, rfl⟩
    rw [valencyWeight_eq_endpoints hM, valencyWeight_eq_endpoints hab,
      ite_mergeMap_eq_of_ne hvx hvy, ite_mergeMap_eq_of_ne hvx hvy]
  · rw [valencyWeight_of_notMem he, valencyWeight_of_notMem]
    simpa [mergeEdge_edgeSet] using fun h => (he h).elim

theorem valencyWeight_mergeEdge_self {L : Graph α β} {f : β} {x y : α}
    (hxy : x ≠ y) {e : β} (hef : e ≠ f) :
    valencyWeight (mergeEdge L f x y) e x = valencyWeight L e x + valencyWeight L e y := by
  by_cases he : e ∈ E(L)
  · obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
    have hM : (mergeEdge L f x y).IsLink e (mergeMap x y a) (mergeMap x y b) :=
      mergeEdge_isLink.2 ⟨hef, a, b, hab, rfl, rfl⟩
    rw [valencyWeight_eq_endpoints hM, valencyWeight_eq_endpoints hab,
      valencyWeight_eq_endpoints hab]
    rw [ite_mergeMap_eq_self hxy, ite_mergeMap_eq_self hxy]
    omega
  · rw [valencyWeight_of_notMem he, valencyWeight_of_notMem he, valencyWeight_of_notMem]
    simpa [mergeEdge_edgeSet] using fun h => (he h).elim

/-- Contracting `f` fixes the valency of every vertex other than its ends. -/
theorem valency_mergeEdge_of_ne {L : Graph α β} (hE : E(L).Finite) {f : β} {x y : α}
    (hf : L.IsLink f x y) {v : α} (hvx : v ≠ x) (hvy : v ≠ y) :
    valency (mergeEdge L f x y) v = valency L v := by
  have hS : E(mergeEdge L f x y) ⊆ (hE.toFinset : Set β) := by
    rw [mergeEdge_edgeSet, hE.coe_toFinset]
    exact sdiff_subset
  rw [valency_eq_sum_of_subset _ hS, valency_eq_sum_of_subset L (by rw [hE.coe_toFinset]) v]
  exact Finset.sum_congr rfl fun e _ => valencyWeight_mergeEdge_of_ne hf e hvx hvy

/-- The merged vertex has valency `d(x) + d(y) - 2`. -/
theorem valency_mergeEdge_self {L : Graph α β} (hE : E(L).Finite) {f : β} {x y : α}
    (hf : L.IsLink f x y) (hxy : x ≠ y) :
    valency (mergeEdge L f x y) x + 2 = valency L x + valency L y := by
  have hS : E(mergeEdge L f x y) ⊆ (hE.toFinset : Set β) := by
    rw [mergeEdge_edgeSet, hE.coe_toFinset]
    exact sdiff_subset
  have hfS : f ∈ hE.toFinset := (hE.mem_toFinset).2 hf.edge_mem
  rw [valency_eq_sum_of_subset _ hS, valency_eq_sum_of_subset L (by rw [hE.coe_toFinset]) x,
    valency_eq_sum_of_subset L (by rw [hE.coe_toFinset]) y, ← Finset.sum_add_distrib,
    ← Finset.add_sum_erase _ _ hfS, ← Finset.add_sum_erase _ _ hfS,
    valencyWeight_of_notMem (notMem_edgeSet_mergeEdge L f x y),
    Finset.sum_congr rfl fun e he => valencyWeight_mergeEdge_self hxy (Finset.ne_of_mem_erase he),
    valencyWeight_eq_endpoints hf, valencyWeight_eq_endpoints hf]
  simp [hxy, Ne.symm hxy]
  omega

/-! ### A split has the original graph as a minor -/

/-- The branch sets of the contraction model: `{x, y}` for the merged vertex,
and `{v}` for every other vertex. -/
noncomputable def mergeBranch (x y v : α) : Set α := if v = x then {x, y} else {v}

theorem mem_mergeBranch {x y v z : α} (hv : v ≠ y) :
    z ∈ mergeBranch x y v ↔ mergeMap x y z = v := by
  unfold mergeBranch
  by_cases hvx : v = x
  · subst hvx
    simp only [↓reduceIte, mem_insert_iff, mem_singleton_iff]
    exact mergeMap_eq_left_iff.symm
  · simp only [hvx, ↓reduceIte, mem_singleton_iff]
    exact (mergeMap_eq_of_ne hvx hv).symm

/-- Contracting an edge gives a minor. -/
theorem isIsoMinor_mergeEdge {L : Graph α β} (hV : V(L).Finite) (hE : E(L).Finite)
    {f : β} {x y : α} (hf : L.IsLink f x y) (hxy : x ≠ y) :
    IsIsoMinor (mergeEdge L f x y) L := by
  let M := mergeEdge L f x y
  have hVM : V(M) = V(L) \ {y} := mergeEdge_vertexSet hf hxy
  have hEM : E(M) = E(L) \ {f} := mergeEdge_edgeSet L f x y
  have hne : ∀ v ∈ V(M), v ≠ y := fun v hv => (hVM ▸ hv).2
  have hmodel : IsMinorModel M L (mergeBranch x y) id := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      exact ⟨v, (mem_mergeBranch (hne v hv)).2 (mergeMap_of_ne (hne v hv))⟩
    · intro v hv z hz
      rw [mem_mergeBranch (hne v hv)] at hz
      have hvL := (hVM ▸ hv).1
      by_cases hzy : z = y
      · exact hzy ▸ hf.right_mem
      · rw [mergeMap_of_ne hzy] at hz
        exact hz ▸ hvL
    · intro e he
      exact (hEM ▸ he).1
    · intro v₁ hv₁ v₂ hv₂ hne'
      rw [Set.disjoint_left]
      intro z h₁ h₂
      rw [mem_mergeBranch (hne v₁ hv₁)] at h₁
      rw [mem_mergeBranch (hne v₂ hv₂)] at h₂
      exact hne' (h₁.symm.trans h₂)
    · exact Set.injOn_id _
    · intro v hv e he
      rw [mergeEdge_inc]
      constructor
      · rintro ⟨-, a₀, ha₀, rfl⟩
        exact ⟨a₀, (mem_mergeBranch (hne _ hv)).2 rfl, ha₀⟩
      · rintro ⟨a₀, ha₀, hinc⟩
        exact ⟨(hEM ▸ he).2, a₀, hinc, (mem_mergeBranch (hne v hv)).1 ha₀⟩
    · intro v hv e he
      have hef : e ≠ f := (hEM ▸ he).2
      constructor
      · intro hloop z hz
        rw [mem_mergeBranch (hne v hv)]
        obtain ⟨w, hzw⟩ := hz
        obtain ⟨-, a₀, b₀, hab, ha, hb⟩ := mergeEdge_isLink.1 (show M.IsLink e v v from hloop)
        rcases hzw.left_eq_or_eq hab with rfl | rfl
        · exact ha
        · exact hb
      · intro hall
        obtain ⟨a₀, b₀, hab⟩ := exists_isLink_of_mem_edgeSet (hEM ▸ he).1
        have ha := (mem_mergeBranch (hne v hv)).1 (hall a₀ hab.inc_left)
        have hb := (mem_mergeBranch (hne v hv)).1 (hall b₀ hab.inc_right)
        exact mergeEdge_isLink.2 ⟨hef, a₀, b₀, hab, ha, hb⟩
    · intro v hv
      by_cases hvx : v = x
      · subst hvx
        refine ⟨Graph.banana v y {f}, ?_, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · intro z hz
            simp only [vertexSet_banana, mem_insert_iff, mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact hf.left_mem
            · exact hf.right_mem
          · intro e a b hab
            simp only [banana_isLink, mem_singleton_iff] at hab
            obtain ⟨he, h⟩ := hab
            refine ⟨?_, ?_⟩
            · rw [he]
              rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hf
              · exact hf.symm
            · rintro ⟨e', he', heq⟩
              have he'f : e' = f := heq.trans he
              subst he'f
              exact (hEM ▸ he').2 rfl
        · simp [mergeBranch]
        · refine ⟨⟨v, by simp⟩, ?_⟩
          have hadj : (Graph.banana v y {f}).Adj v y := ⟨f, by simp⟩
          intro a ha b hb
          simp only [vertexSet_banana, mem_insert_iff, mem_singleton_iff] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.single hadj
          · exact Relation.ReflTransGen.single hadj.symm
          · exact Relation.ReflTransGen.refl
      · refine ⟨Graph.noEdge {v} β, ?_, ?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · intro z hz
            simp only [vertexSet_noEdge, mem_singleton_iff] at hz
            subst hz
            exact (hVM ▸ hv).1
          · intro e a b hab
            simp at hab
        · simp [mergeBranch, hvx]
        · refine ⟨⟨v, rfl⟩, ?_⟩
          intro a ha b hb
          simp only [vertexSet_noEdge, mem_singleton_iff] at ha hb
          subst ha hb
          exact Relation.ReflTransGen.refl
  have hVM' : V(M).Finite := hVM ▸ hV.sdiff
  have hEM' : E(M).Finite := hEM ▸ hE.sdiff
  exact isIsoMinor_of_isMinorModel M L hVM' hEM' hV hE _ _ hmodel

theorem IsSplitStep.finite {K L : Graph α β} (h : IsSplitStep K L)
    (hV : V(K).Finite) (hE : E(K).Finite) : V(L).Finite ∧ E(L).Finite := by
  obtain ⟨f, x, y, hf, hxy, -, -, ⟨φ⟩⟩ := h
  have hVM : V(mergeEdge L f x y).Finite := by
    let : Finite V(K) := hV.to_subtype
    exact Set.finite_coe_iff.1 (Finite.of_equiv V(K) φ.vertexEquiv)
  have hEM : E(mergeEdge L f x y).Finite := by
    let : Finite E(K) := hE.to_subtype
    exact Set.finite_coe_iff.1 (Finite.of_equiv E(K) φ.edgeEquiv)
  rw [mergeEdge_vertexSet hf hxy] at hVM
  rw [mergeEdge_edgeSet] at hEM
  refine ⟨(hVM.insert y).subset ?_, (hEM.insert f).subset ?_⟩
  · intro z hz
    by_cases hzy : z = y
    · exact Or.inl hzy
    · exact Or.inr ⟨hz, hzy⟩
  · intro e he
    by_cases hef : e = f
    · exact Or.inl hef
    · exact Or.inr ⟨he, hef⟩

/-- A split of `H` has `H` as a minor. -/
theorem IsSplitOf.isIsoMinor {α' : Type u'} {β' : Type v'} {H : Graph α' β'}
    {J : Graph α β} (hVH : V(H).Finite) (hEH : E(H).Finite) (h : IsSplitOf H J) :
    V(J).Finite ∧ E(J).Finite ∧ IsIsoMinor H J := by
  obtain ⟨J₀, ⟨φ⟩, hchain⟩ := h
  induction hchain with
  | refl =>
    refine ⟨?_, ?_, φ.isIsoMinor_left (IsIsoMinor.refl J₀)⟩
    · let : Finite V(H) := hVH.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv V(H) φ.vertexEquiv)
    · let : Finite E(H) := hEH.to_subtype
      exact Set.finite_coe_iff.1 (Finite.of_equiv E(H) φ.edgeEquiv)
  | tail _ hstep ih =>
    obtain ⟨hV, hE, hm⟩ := ih
    obtain ⟨hV', hE'⟩ := hstep.finite hV hE
    obtain ⟨f, x, y, hf, hxy, -, -, ⟨ψ⟩⟩ := hstep
    exact ⟨hV', hE', hm.trans (ψ.isIsoMinor_left (isIsoMinor_mergeEdge hV' hE' hf hxy))⟩

/-! ### The size of a split -/

/-- The sum of the valencies. -/
noncomputable def valencySum (G : Graph α β) : ℕ := ∑ᶠ v ∈ V(G), valency G v

/-- The sum of the numbers `min(d(v), 3)`. -/
noncomputable def cappedValencySum (G : Graph α β) : ℕ := ∑ᶠ v ∈ V(G), min (valency G v) 3

theorem finsum_valency_iso {α' : Type u'} {β' : Type v'} {H : Graph α' β'} {G : Graph α β}
    (φ : Iso H G) (F : ℕ → ℕ) :
    ∑ᶠ v ∈ V(H), F (valency H v) = ∑ᶠ v ∈ V(G), F (valency G v) := by
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_set_coe_eq_finsum_mem,
    ← finsum_comp_equiv φ.vertexEquiv]
  exact finsum_congr fun v => by rw [valency_eq_of_iso φ v]

theorem ncard_eq_of_iso {α' : Type u'} {β' : Type v'} {H : Graph α' β'} {G : Graph α β}
    (φ : Iso H G) : V(H).ncard = V(G).ncard ∧ E(H).ncard = E(G).ncard := by
  constructor
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.vertexEquiv
  · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.edgeEquiv

/-- One split adds one vertex and one edge, raises the sum of the
valencies by two and the sum of the numbers `min(d(v), 3)` by three. -/
theorem IsSplitStep.counts {K L : Graph α β} (h : IsSplitStep K L)
    (hV : V(L).Finite) (hE : E(L).Finite) :
    V(L).ncard = V(K).ncard + 1 ∧ E(L).ncard = E(K).ncard + 1 ∧
      valencySum L = valencySum K + 2 ∧ cappedValencySum L = cappedValencySum K + 3 := by
  obtain ⟨f, x, y, hf, hxy, hx3, hy3, ⟨φ⟩⟩ := h
  have hyL : y ∈ V(L) := hf.right_mem
  have hxL : x ∈ V(L) := hf.left_mem
  let R : Set α := (V(L) \ {y}) \ {x}
  have hVM : V(mergeEdge L f x y) = V(L) \ {y} := mergeEdge_vertexSet hf hxy
  have hEM : E(mergeEdge L f x y) = E(L) \ {f} := mergeEdge_edgeSet L f x y
  have hself := valency_mergeEdge_self hE hf hxy
  have hrest : ∀ v ∈ R, valency (mergeEdge L f x y) v = valency L v := fun v hv =>
    valency_mergeEdge_of_ne hE hf hv.2 hv.1.2
  generalize mergeEdge L f x y = M at φ hVM hEM hself hrest
  obtain ⟨hcV, hcE⟩ := ncard_eq_of_iso φ
  have hD : valencySum K = valencySum M := finsum_valency_iso φ id
  have hC : cappedValencySum K = cappedValencySum M := finsum_valency_iso φ (fun n => min n 3)
  have hRfin : R.Finite := hV.sdiff.sdiff
  have hxR : x ∉ R := fun h => h.2 rfl
  have hyR : y ∉ insert x R := by
    rintro (h | h)
    · exact hxy h.symm
    · exact h.1.2 rfl
  have hLeq : V(L) = insert y (insert x R) := by
    ext z
    simp only [R, mem_insert_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · intro hz
      by_cases hzy : z = y
      · exact Or.inl hzy
      · by_cases hzx : z = x
        · exact Or.inr (Or.inl hzx)
        · exact Or.inr (Or.inr ⟨⟨hz, hzy⟩, hzx⟩)
    · rintro (rfl | rfl | ⟨⟨hz, -⟩, -⟩)
      · exact hyL
      · exact hxL
      · exact hz
  have hMeq : V(M) = insert x R := by
    rw [hVM]
    ext z
    simp only [R, mem_insert_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨hz, hzy⟩
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr ⟨⟨hz, hzy⟩, hzx⟩
    · rintro (rfl | ⟨⟨hz, hzy⟩, -⟩)
      · exact ⟨hxL, hxy⟩
      · exact ⟨hz, hzy⟩
  have hsumL : ∀ F : ℕ → ℕ, ∑ᶠ v ∈ V(L), F (valency L v) =
      F (valency L y) + (F (valency L x) + ∑ᶠ v ∈ R, F (valency L v)) := by
    intro F
    rw [hLeq, finsum_mem_insert _ hyR (hRfin.insert x), finsum_mem_insert _ hxR hRfin]
  have hsumM : ∀ F : ℕ → ℕ, ∑ᶠ v ∈ V(M), F (valency M v) =
      F (valency M x) + ∑ᶠ v ∈ R, F (valency L v) := by
    intro F
    rw [hMeq, finsum_mem_insert _ hxR hRfin]
    congr 1
    exact finsum_mem_congr rfl fun v hv => by rw [hrest v hv]
  have hVcard : V(L).ncard = V(M).ncard + 1 := by
    rw [hVM]
    exact (Set.ncard_sdiff_singleton_add_one hyL hV).symm
  have hEcard : E(L).ncard = E(M).ncard + 1 := by
    rw [hEM]
    exact (Set.ncard_sdiff_singleton_add_one hf.edge_mem hE).symm
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [hD]
    have h1 := hsumL id
    have h2 := hsumM id
    simp only [id] at h1 h2
    change ∑ᶠ v ∈ V(L), valency L v = ∑ᶠ v ∈ V(M), valency M v + 2
    omega
  · rw [hC]
    have h1 := hsumL (fun n => min n 3)
    have h2 := hsumM (fun n => min n 3)
    change ∑ᶠ v ∈ V(L), min (valency L v) 3 = ∑ᶠ v ∈ V(M), min (valency M v) 3 + 3
    have hm : min (valency M x) 3 = 3 := by omega
    have hxm : min (valency L x) 3 = 3 := by omega
    have hym : min (valency L y) 3 = 3 := by omega
    omega

/-- The capped sum is at most the sum. -/
theorem cappedValencySum_le (G : Graph α β) (hV : V(G).Finite) :
    cappedValencySum G ≤ valencySum G := by
  unfold cappedValencySum valencySum
  rw [finsum_mem_eq_finite_toFinset_sum _ hV, finsum_mem_eq_finite_toFinset_sum _ hV]
  exact Finset.sum_le_sum fun v _ => min_le_left _ _

theorem valencySum_eq (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite) :
    valencySum G = 2 * E(G).ncard := by
  unfold valencySum
  rw [finsum_mem_eq_finite_toFinset_sum _ hV]
  exact sum_valency G hV hE

/-- A split of `H` has at most `|V(H)| + 2|E(H)|` vertices and at most
`3|E(H)|` edges. -/
theorem IsSplitOf.ncard_le {α' : Type u'} {β' : Type v'} {H : Graph α' β'}
    {J : Graph α β} (hVH : V(H).Finite) (hEH : E(H).Finite) (h : IsSplitOf H J) :
    V(J).ncard ≤ V(H).ncard + 2 * E(H).ncard ∧ E(J).ncard ≤ 3 * E(H).ncard := by
  have hfin := h.isIsoMinor hVH hEH
  obtain ⟨J₀, ⟨φ⟩, hchain⟩ := h
  have hcount : ∀ K, Relation.ReflTransGen IsSplitStep J₀ K → ∃ s,
      V(K).ncard = V(H).ncard + s ∧ E(K).ncard = E(H).ncard + s ∧
      valencySum K = valencySum H + 2 * s ∧
      cappedValencySum K = cappedValencySum H + 3 * s := by
    intro K hK
    induction hK with
    | refl =>
      obtain ⟨hv, he⟩ := ncard_eq_of_iso φ
      exact ⟨0, hv.symm, he.symm, (finsum_valency_iso φ id).symm,
        (finsum_valency_iso φ (fun n => min n 3)).symm⟩
    | @tail K L hKL hstep ih =>
      have hK := IsSplitOf.isIsoMinor (J := K) hVH hEH ⟨J₀, ⟨φ⟩, hKL⟩
      obtain ⟨s, h1, h2, h3, h4⟩ := ih
      obtain ⟨hVL, hEL⟩ := hstep.finite hK.1 hK.2.1
      obtain ⟨c1, c2, c3, c4⟩ := hstep.counts hVL hEL
      exact ⟨s + 1, by omega, by omega, by omega, by omega⟩
  obtain ⟨s, h1, h2, h3, h4⟩ := hcount J hchain
  have hle := cappedValencySum_le J hfin.1
  have hH := valencySum_eq H hVH hEH
  omega

end GraphMinor.GM02
