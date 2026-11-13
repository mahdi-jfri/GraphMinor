module

public import GraphMinor.GM08.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card

/-!
# Graph Minors VIII, Section 2 (Part 1): Valency, Edge Contraction, and Proof of (2.3)

This file formalizes the valency and single-edge contraction identities on finite multigraphs and
proves **(2.3)** (`theorem_2_3`, page 259) of N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- `edgeContribution` and `vertexValency_eq_sum_edgeContribution`: decomposition of `vertexValency G v`
  as a sum over `e ∈ E(G)`, counting loops twice and non-loop incidences once.
- `sum_vertexValency_eq_two_mul_ncard_edgeSet`: the handshaking lemma $\sum_{v \in V(G)} \text{val}(v) = 2|E(G)|$.
- `vertexValency_contractEdgeInto_left` and `vertexValency_contractEdgeInto_other`: exact formulas
  for vertex valencies after contracting a non-loop edge $f$ with ends $u \ne v$ into $u$.
- `splitInvariantN_of_obtainedBySplittingVertex`: if $G_1$ is obtained from $G_2$ by splitting a
  vertex, then $N(G_1) + 1 = N(G_2)$, $|V(G_1)| = |V(G_2)| + 1$, and $|E(G_1)| = |E(G_2)| + 1$.
- `theorem_2_3`: (2.3) (page 259), for any finite graph $H$, $Z(H)$ is finite up to isomorphism.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Graph

universe u v u' v'

/-! ## 1. Edge contributions to vertex valency and the handshaking lemma -/

/-- The contribution of an edge $e$ to the valency of a vertex $v$ in $G$: $2$ if $e$ is a loop at
$v$, $1$ if $e$ is a non-loop incident with $v$, and $0$ otherwise. -/
noncomputable def edgeContribution {α : Type u} {β : Type v} (G : Graph α β) (e : β) (v : α) : ℕ :=
  open Classical in
  if G.IsLink e v v then 2 else if G.Inc e v then 1 else 0

/-- If `G.IsLink e x y`, then `edgeContribution G e w` is `(if w = x then 1 else 0) + (if w = y then 1 else 0)`. -/
theorem edgeContribution_eq_of_isLink {α : Type u} {β : Type v} {G : Graph α β}
    {e : β} {x y : α} (hl : G.IsLink e x y) (w : α) :
    edgeContribution G e w =
      (open Classical in (if w = x then 1 else 0) + (if w = y then 1 else 0)) := by
  classical
  unfold edgeContribution
  by_cases hloop : G.IsLink e w w
  · have hwx : w = x := (hloop.eq_and_eq_or_eq_and_eq hl).elim And.left And.right
    have hwy : w = y := (hloop.eq_and_eq_or_eq_and_eq hl).elim And.right And.left
    rw [ite_eq_left hloop, ite_eq_left hwx, ite_eq_left hwy]
  · rw [ite_eq_right hloop]
    by_cases hinc : G.Inc e w
    · rw [ite_eq_left hinc]
      rcases hinc.eq_or_eq_of_isLink hl with rfl | rfl
      · have hwy : w ≠ y := fun h => hloop (h ▸ hl)
        simp [hwy]
      · have hwx : w ≠ x := fun h => hloop (h ▸ hl.symm)
        simp [hwx]
    · rw [ite_eq_right hinc]
      have hwx : w ≠ x := fun h => hinc (h ▸ hl.inc_left)
      have hwy : w ≠ y := fun h => hinc (h ▸ hl.inc_right)
      simp [hwx, hwy]

/-- In any graph $G$, a non-loop incidence with $v$ is equivalent to `G.Inc e v ∧ ¬ G.IsLink e v v`. -/
private theorem exists_ne_isLink_iff_inc_and_not_loop {α : Type u} {β : Type v}
    (G : Graph α β) (e : β) (v : α) :
    (∃ w ≠ v, G.IsLink e v w) ↔ G.Inc e v ∧ ¬ G.IsLink e v v := by
  constructor
  · rintro ⟨w, hwne, hl⟩
    refine ⟨⟨w, hl⟩, fun hloop => hwne ?_⟩
    rcases hloop.eq_and_eq_or_eq_and_eq hl with ⟨_, h⟩ | ⟨h, _⟩
    · exact h.symm
    · exact h.symm
  · rintro ⟨⟨w, hl⟩, hnloop⟩
    exact ⟨w, fun h => hnloop (h ▸ hl), hl⟩

/-- For a graph $G$ with finite edge set, `vertexValency G v` is the sum of `edgeContribution G e v`
over $e \in E(G)$. -/
theorem vertexValency_eq_sum_edgeContribution {α : Type u} {β : Type v}
    {G : Graph α β} (hE : E(G).Finite) (v : α) :
    vertexValency G v = ∑ e ∈ hE.toFinset, edgeContribution G e v := by
  classical
  unfold vertexValency GM06.vertexValency edgeContribution
  have hS₁ : {e ∈ E(G) | ∃ w ≠ v, G.IsLink e v w} =
      ↑(hE.toFinset.filter (fun e => G.Inc e v ∧ ¬ G.IsLink e v v)) := by
    ext e
    simp [exists_ne_isLink_iff_inc_and_not_loop]
  have hS₂ : {e ∈ E(G) | G.IsLink e v v} =
      ↑(hE.toFinset.filter (fun e => G.IsLink e v v)) := by
    ext e
    simp
  rw [hS₁, hS₂, ncard_coe_finset, ncard_coe_finset, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hloop : G.IsLink e v v <;> by_cases hinc : G.Inc e v
  · rw [ite_eq_right (not_and_of_not_right _ (not_not.mpr hloop)),
      ite_eq_left hloop, ite_eq_left hloop]; rfl
  · rw [ite_eq_right (not_and_of_not_left _ hinc),
      ite_eq_left hloop, ite_eq_left hloop]; rfl
  · rw [ite_eq_left ⟨hinc, hloop⟩, ite_eq_right hloop, ite_eq_right hloop, ite_eq_left hinc]; rfl
  · rw [ite_eq_right (not_and_of_not_left _ hinc),
      ite_eq_right hloop, ite_eq_right hloop, ite_eq_right hinc]; rfl

/-- If `v ∉ V(G)` and `E(G).Finite`, then `vertexValency G v = 0`. -/
theorem vertexValency_eq_zero_of_notMem {α : Type u} {β : Type v}
    {G : Graph α β} (hE : E(G).Finite) {v : α} (hv : v ∉ V(G)) :
    vertexValency G v = 0 := by
  classical
  rw [vertexValency_eq_sum_edgeContribution hE v]
  refine Finset.sum_eq_zero fun e _ => ?_
  unfold edgeContribution
  have hninc : ¬ G.Inc e v := fun h => hv h.vertex_mem
  have hnloop : ¬ G.IsLink e v v := fun h => hv h.left_mem
  rw [ite_eq_right hnloop, ite_eq_right hninc]

/-- The handshaking lemma for finite multigraphs:
$\sum_{v \in V(G)} \text{val}(v) = 2 |E(G)|$. -/
theorem sum_vertexValency_eq_two_mul_ncard_edgeSet {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) :
    ∑ v ∈ hG.1.toFinset, vertexValency G v = 2 * E(G).ncard := by
  classical
  have hval : ∀ v ∈ hG.1.toFinset,
      vertexValency G v = ∑ e ∈ hG.2.toFinset, edgeContribution G e v :=
    fun v _ => vertexValency_eq_sum_edgeContribution hG.2 v
  rw [Finset.sum_congr rfl hval, Finset.sum_comm]
  have hedge : ∀ e ∈ hG.2.toFinset,
      (∑ v ∈ hG.1.toFinset, edgeContribution G e v) = 2 := by
    intro e he
    have heE : e ∈ E(G) := hG.2.mem_toFinset.mp he
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet heE
    have hcongr : ∀ v ∈ hG.1.toFinset,
        edgeContribution G e v = (if v = x then 1 else 0) + (if v = y then 1 else 0) :=
      fun v _ => edgeContribution_eq_of_isLink hl v
    rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib]
    have hx : x ∈ hG.1.toFinset := hG.1.mem_toFinset.mpr hl.left_mem
    have hy : y ∈ hG.1.toFinset := hG.1.mem_toFinset.mpr hl.right_mem
    simp [hx, hy]
  rw [Finset.sum_congr rfl hedge, Finset.sum_const, smul_eq_mul, mul_comm,
    ← ncard_coe_finset hG.2.toFinset, Finite.coe_toFinset]

/-! ## 2. Invariance of valency and $N(G)$ under graph isomorphism -/

/-- Graph isomorphisms preserve vertex valency. -/
theorem iso_vertexValency_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (φ : Iso H G)
    (hH : IsFiniteGraph H) (hG : IsFiniteGraph G) (v : V(H)) :
    vertexValency G (φ.vertexEquiv v).1 = vertexValency H v.1 := by
  classical
  rw [vertexValency_eq_sum_edgeContribution hG.2, vertexValency_eq_sum_edgeContribution hH.2]
  let ebij : ∀ e ∈ hH.2.toFinset, β := fun e he => (φ.edgeEquiv ⟨e, hH.2.mem_toFinset.mp he⟩).1
  refine (Finset.sum_bij ebij ?_ ?_ ?_ ?_).symm
  · intro e he
    exact hG.2.mem_toFinset.mpr (φ.edgeEquiv ⟨e, hH.2.mem_toFinset.mp he⟩).2
  · intro e₁ he₁ e₂ he₂ heq
    have hsub := φ.edgeEquiv.injective (Subtype.ext heq)
    exact congrArg Subtype.val hsub
  · intro f hf
    obtain ⟨⟨e, he⟩, hef⟩ := φ.edgeEquiv.surjective ⟨f, hG.2.mem_toFinset.mp hf⟩
    exact ⟨e, hH.2.mem_toFinset.mpr he, congrArg Subtype.val hef⟩
  · intro e he
    have heH : e ∈ E(H) := hH.2.mem_toFinset.mp he
    obtain ⟨x, y, hlH⟩ := exists_isLink_of_mem_edgeSet heH
    have hlG : G.IsLink (ebij e he) (φ.vertexEquiv ⟨x, hlH.left_mem⟩).1
        (φ.vertexEquiv ⟨y, hlH.right_mem⟩).1 :=
      (φ.isLink_iff ⟨e, heH⟩ ⟨x, hlH.left_mem⟩ ⟨y, hlH.right_mem⟩).1 hlH
    rw [edgeContribution_eq_of_isLink hlH v.1,
      edgeContribution_eq_of_isLink hlG (φ.vertexEquiv v).1]
    have hx_iff : (φ.vertexEquiv v).1 = (φ.vertexEquiv ⟨x, hlH.left_mem⟩).1 ↔ v.1 = x := by
      constructor
      · intro h
        exact congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext h))
      · intro h
        exact congrArg (fun u => (φ.vertexEquiv u).1) (Subtype.ext h)
    have hy_iff : (φ.vertexEquiv v).1 = (φ.vertexEquiv ⟨y, hlH.right_mem⟩).1 ↔ v.1 = y := by
      constructor
      · intro h
        exact congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext h))
      · intro h
        exact congrArg (fun u => (φ.vertexEquiv u).1) (Subtype.ext h)
    simp [hx_iff, hy_iff]

/-- Graph isomorphisms preserve `V(G).ncard` and `E(G).ncard`. -/
theorem iso_ncard_vertexSet_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (φ : Iso H G) :
    V(H).ncard = V(G).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr φ.vertexEquiv

theorem iso_ncard_edgeSet_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (φ : Iso H G) :
    E(H).ncard = E(G).ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr φ.edgeEquiv

/-- Graph isomorphisms preserve `(highValencyVerts G).ncard`. -/
theorem iso_ncard_highValencyVerts_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (φ : Iso H G)
    (hH : IsFiniteGraph H) (hG : IsFiniteGraph G) :
    (highValencyVerts H).ncard = (highValencyVerts G).ncard := by
  have heq : highValencyVerts G = (fun v : V(H) => (φ.vertexEquiv v).1) ''
      {v : V(H) | 3 ≤ vertexValency H v.1} := by
    ext w
    simp only [highValencyVerts, mem_ofPred_eq, mem_image, Subtype.exists]
    constructor
    · rintro ⟨hwG, hval⟩
      obtain ⟨⟨v, hvH⟩, hv_eq⟩ := φ.vertexEquiv.surjective ⟨w, hwG⟩
      have hw_eq : (φ.vertexEquiv ⟨v, hvH⟩).1 = w := congrArg Subtype.val hv_eq
      refine ⟨v, hvH, ?_, hw_eq⟩
      rw [← iso_vertexValency_eq φ hH hG ⟨v, hvH⟩, hw_eq]
      exact hval
    · rintro ⟨v, hvH, hval, rfl⟩
      refine ⟨(φ.vertexEquiv ⟨v, hvH⟩).2, ?_⟩
      rw [iso_vertexValency_eq φ hH hG ⟨v, hvH⟩]
      exact hval
  have hinj : Function.Injective (fun v : V(H) => (φ.vertexEquiv v).1) := by
    intro v₁ v₂ h
    exact φ.vertexEquiv.injective (Subtype.ext h)
  have hH_eq : highValencyVerts H = Subtype.val '' {v : V(H) | 3 ≤ vertexValency H v.1} := by
    ext v
    simp only [highValencyVerts, mem_ofPred_eq, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right]
    exact exists_prop.symm
  rw [heq, hH_eq, Set.ncard_image_of_injective _ hinj,
    Set.ncard_image_of_injective _ Subtype.val_injective]

/-- Graph isomorphisms preserve `splitInvariantN`. -/
theorem iso_splitInvariantN_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (φ : Iso H G)
    (hH : IsFiniteGraph H) (hG : IsFiniteGraph G) :
    splitInvariantN H = splitInvariantN G := by
  unfold splitInvariantN
  rw [iso_ncard_edgeSet_eq φ, iso_ncard_highValencyVerts_eq φ hH hG]

/-! ## 3. Single-edge contraction (`contractEdgeInto`) and valency formulas -/

/-- Vertex set of `contractEdgeInto G f u v` when `u ≠ v` and `G.IsLink f u v`. -/
theorem vertexSet_contractEdgeInto {α : Type u} {β : Type v}
    {G : Graph α β} {f : β} {u v : α} (hne : u ≠ v) (hl : G.IsLink f u v) :
    V(contractEdgeInto G f u v) = V(G) \ {v} := by
  classical
  ext x
  change x ∈ (fun y => if y = v then u else y) '' V(G) ↔ x ∈ V(G) \ {v}
  simp only [mem_image, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hyv : y = v
    · subst hyv
      simp [hl.left_mem, hne]
    · simp [hyv, hy]
  · rintro ⟨hx, hxv⟩
    exact ⟨x, hx, ite_eq_right hxv⟩

/-- Edge set of `contractEdgeInto G f u v`. -/
@[simp]
theorem edgeSet_contractEdgeInto {α : Type u} {β : Type v}
    (G : Graph α β) (f : β) (u v : α) :
    E(contractEdgeInto G f u v) = E(G) \ {f} := by
  classical
  simp [contractEdgeInto]

/-- Link characterization in `contractEdgeInto G f u v`. -/
theorem contractEdgeInto_isLink {α : Type u} {β : Type v}
    {G : Graph α β} {f : β} {u v : α} {e : β} {x y : α} :
    (contractEdgeInto G f u v).IsLink e x y ↔
      e ≠ f ∧ ∃ a b : α, G.IsLink e a b ∧
        (open Classical in (if a = v then u else a) = x ∧ (if b = v then u else b) = y) := by
  classical
  simp only [contractEdgeInto, deleteEdges_isLink, mem_singleton_iff, map_isLink, Relation.Map]
  tauto

/-- `contractEdgeInto` preserves `IsFiniteGraph`. -/
theorem isFiniteGraph_contractEdgeInto {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) (f : β) (u v : α) :
    IsFiniteGraph (contractEdgeInto G f u v) := by
  classical
  refine ⟨?_, ?_⟩
  · change ((fun x => if x = v then u else x) '' V(G)).Finite
    exact hG.1.image _
  · rw [edgeSet_contractEdgeInto]
    exact hG.2.sdiff

theorem ncard_vertexSet_contractEdgeInto {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) {f : β} {u v : α}
    (hne : u ≠ v) (hl : G.IsLink f u v) :
    V(contractEdgeInto G f u v).ncard + 1 = V(G).ncard := by
  rw [vertexSet_contractEdgeInto hne hl]
  exact ncard_sdiff_singleton_add_one hl.right_mem hG.1

theorem ncard_edgeSet_contractEdgeInto {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) {f : β} {u v : α}
    (hl : G.IsLink f u v) :
    E(contractEdgeInto G f u v).ncard + 1 = E(G).ncard := by
  rw [edgeSet_contractEdgeInto]
  exact ncard_sdiff_singleton_add_one hl.edge_mem hG.2

/-- Key valency identity at the merged vertex `u` after contracting a non-loop edge `f` linking
`u` and `v`:
$\text{val}_{G/f}(u) + 2 = \text{val}_G(u) + \text{val}_G(v)$. -/
theorem vertexValency_contractEdgeInto_left {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) {f : β} {u v : α}
    (hne : u ≠ v) (hl : G.IsLink f u v) :
    vertexValency (contractEdgeInto G f u v) u + 2 =
      vertexValency G u + vertexValency G v := by
  classical
  let G' := contractEdgeInto G f u v
  have hG' : IsFiniteGraph G' := isFiniteGraph_contractEdgeInto hG f u v
  rw [vertexValency_eq_sum_edgeContribution hG'.2 u,
    vertexValency_eq_sum_edgeContribution hG.2 u,
    vertexValency_eq_sum_edgeContribution hG.2 v,
    ← Finset.sum_add_distrib]
  have hfin_eq : hG'.2.toFinset = hG.2.toFinset.erase f := by
    ext e
    simp [G', edgeSet_contractEdgeInto, and_comm]
  have hf_mem : f ∈ hG.2.toFinset := hG.2.mem_toFinset.mpr hl.edge_mem
  rw [hfin_eq, ← Finset.sum_erase_add _ _ hf_mem]
  have hf_contrib : edgeContribution G f u + edgeContribution G f v = 2 := by
    rw [edgeContribution_eq_of_isLink hl u, edgeContribution_eq_of_isLink hl v]
    simp [hne, hne.symm]
  rw [hf_contrib]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have hef : e ≠ f := (Finset.mem_erase.mp he).1
  have heG : e ∈ E(G) := hG.2.mem_toFinset.mp (Finset.mem_erase.mp he).2
  obtain ⟨a, b, hl_e⟩ := exists_isLink_of_mem_edgeSet heG
  have hl_e' : G'.IsLink e (if a = v then u else a) (if b = v then u else b) := by
    rw [contractEdgeInto_isLink]
    exact ⟨hef, a, b, hl_e, rfl, rfl⟩
  rw [edgeContribution_eq_of_isLink hl_e' u,
    edgeContribution_eq_of_isLink hl_e u,
    edgeContribution_eq_of_isLink hl_e v]
  by_cases hav : a = v <;> by_cases hbv : b = v <;>
    by_cases hau : a = u <;> by_cases hbu : b = u <;>
    simp_all [eq_comm]

/-- Key valency identity at any other vertex `w ∉ {u, v}` after contracting `f` linking `u` and `v`:
$\text{val}_{G/f}(w) = \text{val}_G(w)$. -/
theorem vertexValency_contractEdgeInto_other {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) {f : β} {u v w : α}
    (hl : G.IsLink f u v) (hwu : w ≠ u) (hwv : w ≠ v) :
    vertexValency (contractEdgeInto G f u v) w = vertexValency G w := by
  classical
  let G' := contractEdgeInto G f u v
  have hG' : IsFiniteGraph G' := isFiniteGraph_contractEdgeInto hG f u v
  rw [vertexValency_eq_sum_edgeContribution hG'.2 w,
    vertexValency_eq_sum_edgeContribution hG.2 w]
  have hfin_eq : hG'.2.toFinset = hG.2.toFinset.erase f := by
    ext e
    simp [G', edgeSet_contractEdgeInto, and_comm]
  have hf_mem : f ∈ hG.2.toFinset := hG.2.mem_toFinset.mpr hl.edge_mem
  rw [hfin_eq, ← Finset.sum_erase_add _ _ hf_mem]
  have hf_contrib : edgeContribution G f w = 0 := by
    rw [edgeContribution_eq_of_isLink hl w]
    simp [hwu, hwv]
  rw [hf_contrib, add_zero]
  refine Finset.sum_congr rfl fun e he => ?_
  have hef : e ≠ f := (Finset.mem_erase.mp he).1
  have heG : e ∈ E(G) := hG.2.mem_toFinset.mp (Finset.mem_erase.mp he).2
  obtain ⟨a, b, hl_e⟩ := exists_isLink_of_mem_edgeSet heG
  have hl_e' : G'.IsLink e (if a = v then u else a) (if b = v then u else b) := by
    rw [contractEdgeInto_isLink]
    exact ⟨hef, a, b, hl_e, rfl, rfl⟩
  rw [edgeContribution_eq_of_isLink hl_e' w, edgeContribution_eq_of_isLink hl_e w]
  have haw : (w = if a = v then u else a) ↔ w = a := by
    by_cases hav : a = v <;> simp [hav, hwu, hwv]
  have hbw : (w = if b = v then u else b) ↔ w = b := by
    by_cases hbv : b = v <;> simp [hbv, hwu, hwv]
  simp [haw, hbw]

/-! ## 4. Proof of (2.3) (`theorem_2_3_proof`, page 259) -/

/-- In any finite graph $G$, $3 |V'| \le 2 |E(G)|$, where $V'$ is the set of vertices of valency
$\ge 3$ (`highValencyVerts G`). -/
theorem three_mul_ncard_highValencyVerts_le {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) :
    3 * (highValencyVerts G).ncard ≤ 2 * E(G).ncard := by
  classical
  have hsub : highValencyVerts G ⊆ V(G) := fun _ hv => hv.1
  have hfinV' : (highValencyVerts G).Finite := hG.1.subset hsub
  have hsub_fin : hfinV'.toFinset ⊆ hG.1.toFinset := by
    intro v hv
    exact hG.1.mem_toFinset.mpr (hsub (hfinV'.mem_toFinset.mp hv))
  calc
    3 * (highValencyVerts G).ncard
      = ∑ _v ∈ hfinV'.toFinset, 3 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm, ← ncard_coe_finset, Finite.coe_toFinset]
    _ ≤ ∑ v ∈ hfinV'.toFinset, vertexValency G v :=
        Finset.sum_le_sum fun v hv => (hfinV'.mem_toFinset.mp hv).2
    _ ≤ ∑ v ∈ hG.1.toFinset, vertexValency G v :=
        Finset.sum_le_sum_of_subset hsub_fin
    _ = 2 * E(G).ncard := sum_vertexValency_eq_two_mul_ncard_edgeSet hG

/-- When an edge $f$ linking $u \ne v$ with $\text{val}(u) \ge 3$ and $\text{val}(v) \ge 3$ is
contracted into $u$, `highValencyVerts G` is `insert v (highValencyVerts (contractEdgeInto G f u v))`
with $v \notin \text{highValencyVerts}(G/f)$. -/
theorem highValencyVerts_contractEdgeInto {α : Type u} {β : Type v}
    {G : Graph α β} (hG : IsFiniteGraph G) {f : β} {u v : α}
    (hne : u ≠ v) (hl : G.IsLink f u v)
    (hu : 3 ≤ vertexValency G u) (hv : 3 ≤ vertexValency G v) :
    highValencyVerts G = insert v (highValencyVerts (contractEdgeInto G f u v)) ∧
      v ∉ highValencyVerts (contractEdgeInto G f u v) := by
  have hval_u' : 3 ≤ vertexValency (contractEdgeInto G f u v) u := by
    have h := vertexValency_contractEdgeInto_left hG hne hl
    omega
  have hv_not : v ∉ highValencyVerts (contractEdgeInto G f u v) := by
    rintro ⟨hvV', _⟩
    rw [vertexSet_contractEdgeInto hne hl] at hvV'
    exact hvV'.2 rfl
  refine ⟨?_, hv_not⟩
  ext w
  simp only [highValencyVerts, mem_ofPred_eq, mem_insert_iff]
  by_cases hwv : w = v
  · subst hwv
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨hl.right_mem, hv⟩⟩
  · by_cases hwu : w = u
    · subst hwu
      have huV' : w ∈ V(contractEdgeInto G f w v) := by
        rw [vertexSet_contractEdgeInto hne hl]
        exact ⟨hl.left_mem, hne⟩
      exact ⟨fun _ => Or.inr ⟨huV', hval_u'⟩, fun _ => ⟨hl.left_mem, hu⟩⟩
    · have hwV_iff : w ∈ V(contractEdgeInto G f u v) ↔ w ∈ V(G) := by
        rw [vertexSet_contractEdgeInto hne hl]
        simp [hwv]
      have hval_w : vertexValency (contractEdgeInto G f u v) w = vertexValency G w :=
        vertexValency_contractEdgeInto_other hG hl hwu hwv
      rw [hwV_iff, hval_w]
      exact ⟨fun h => Or.inr h, fun h => h.resolve_left hwv⟩

/-- If $G_1$ is obtained from $G_2$ by splitting a vertex (`ObtainedBySplittingVertex G₁ G₂`), then
$N(G_1) + 1 = N(G_2)$, $|V(G_1)| = |V(G_2)| + 1$, and $|E(G_1)| = |E(G_2)| + 1$ (page 259). -/
theorem splitInvariantN_of_obtainedBySplittingVertex {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {G₁ : Graph α β} {G₂ : Graph α' β'}
    (hG₁ : IsFiniteGraph G₁) (hG₂ : IsFiniteGraph G₂)
    (hsplit : ObtainedBySplittingVertex G₁ G₂) :
    splitInvariantN G₁ + 1 = splitInvariantN G₂ ∧
      V(G₁).ncard = V(G₂).ncard + 1 ∧
      E(G₁).ncard = E(G₂).ncard + 1 := by
  obtain ⟨f, u, v, hne, hl, hu, hv, ⟨φ⟩⟩ := hsplit
  let G₂' := contractEdgeInto G₁ f u v
  have hG₂' : IsFiniteGraph G₂' := isFiniteGraph_contractEdgeInto hG₁ f u v
  have hV_card : V(G₁).ncard = V(G₂).ncard + 1 := by
    rw [iso_ncard_vertexSet_eq φ, ncard_vertexSet_contractEdgeInto hG₁ hne hl]
  have hE_card : E(G₁).ncard = E(G₂).ncard + 1 := by
    rw [iso_ncard_edgeSet_eq φ, ncard_edgeSet_contractEdgeInto hG₁ hl]
  obtain ⟨hV'_eq, hv_not⟩ := highValencyVerts_contractEdgeInto hG₁ hne hl hu hv
  have hfinV' : (highValencyVerts G₂').Finite := hG₂'.1.subset (fun _ h => h.1)
  have hV'_card : (highValencyVerts G₁).ncard = (highValencyVerts G₂).ncard + 1 := by
    rw [hV'_eq, Set.ncard_insert_of_notMem hv_not hfinV', iso_ncard_highValencyVerts_eq φ hG₂ hG₂']
  have hle₁ : 3 * (highValencyVerts G₁).ncard ≤ 2 * E(G₁).ncard :=
    three_mul_ncard_highValencyVerts_le hG₁
  have hle₂ : 3 * (highValencyVerts G₂).ncard ≤ 2 * E(G₂).ncard :=
    three_mul_ncard_highValencyVerts_le hG₂
  refine ⟨?_, hV_card, hE_card⟩
  unfold splitInvariantN
  omega

/-- Transport `IsFiniteGraph` along an isomorphism `Iso H G`. -/
theorem isFiniteGraph_of_iso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (φ : Iso H G) (hH : IsFiniteGraph H) :
    IsFiniteGraph G := by
  have : Finite V(H) := hH.1
  have : Finite E(H) := hH.2
  have : Finite V(G) := Finite.of_equiv V(H) φ.vertexEquiv
  have : Finite E(G) := Finite.of_equiv E(H) φ.edgeEquiv
  exact ⟨Set.toFinite V(G), Set.toFinite E(G)⟩

/-- If $G$ is obtained from $H$ by splitting vertices (`ObtainedBySplittingVertices G H`), then
$|V(G)| \le |V(H)| + N(H)$ and $|E(G)| \le |E(H)| + N(H)$. -/
theorem bounds_of_obtainedBySplittingVertices {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'}
    (_hG : IsFiniteGraph G) (hH : IsFiniteGraph H)
    (hsplit : ObtainedBySplittingVertices G H) :
    V(G).ncard ≤ V(H).ncard + splitInvariantN H ∧
      E(G).ncard ≤ E(H).ncard + splitInvariantN H := by
  obtain ⟨k, H_seq, ⟨φ₀⟩, hlast, hstep⟩ := hsplit
  have hseq : ∀ m : ℕ, (hm : m ≤ k) →
      IsFiniteGraph (H_seq ⟨m, Nat.lt_succ_of_le hm⟩) ∧
      splitInvariantN (H_seq ⟨m, Nat.lt_succ_of_le hm⟩) + m = splitInvariantN H ∧
      V(H_seq ⟨m, Nat.lt_succ_of_le hm⟩).ncard = V(H).ncard + m ∧
      E(H_seq ⟨m, Nat.lt_succ_of_le hm⟩).ncard = E(H).ncard + m := by
    intro m
    induction m with
    | zero =>
      intro hm
      have hfin₀ : IsFiniteGraph (H_seq 0) := isFiniteGraph_of_iso φ₀ hH
      refine ⟨hfin₀, ?_, ?_, ?_⟩
      · simpa using (iso_splitInvariantN_eq φ₀ hH hfin₀).symm
      · simpa using (iso_ncard_vertexSet_eq φ₀).symm
      · simpa using (iso_ncard_edgeSet_eq φ₀).symm
    | succ m ih =>
      intro hm
      obtain ⟨hfin_m, hN_m, hV_m, hE_m⟩ := ih (Nat.le_of_succ_le hm)
      have hsp : ObtainedBySplittingVertex
          (H_seq ⟨m + 1, Nat.lt_succ_of_le hm⟩)
          (H_seq ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩) := hstep ⟨m, hm⟩
      rcases hsp with ⟨f, u, v, hne, hl, hvu, hvv, ⟨ψ⟩⟩
      have hsp' : ObtainedBySplittingVertex
          (H_seq ⟨m + 1, Nat.lt_succ_of_le hm⟩)
          (H_seq ⟨m, Nat.lt_succ_of_le (Nat.le_of_succ_le hm)⟩) :=
        ⟨f, u, v, hne, hl, hvu, hvv, ⟨ψ⟩⟩
      have hfin_G₂' : IsFiniteGraph (contractEdgeInto (H_seq ⟨m + 1, Nat.lt_succ_of_le hm⟩) f u v) :=
        isFiniteGraph_of_iso ψ hfin_m
      have hfin_succ : IsFiniteGraph (H_seq ⟨m + 1, Nat.lt_succ_of_le hm⟩) := by
        classical
        refine ⟨?_, ?_⟩
        · refine (hfin_G₂'.1.union (finite_singleton v)).subset ?_
          intro x hx
          by_cases hxv : x = v
          · exact Or.inr hxv
          · left
            change x ∈ (fun y => if y = v then u else y) '' V(H_seq ⟨m + 1, Nat.lt_succ_of_le hm⟩)
            exact ⟨x, hx, ite_eq_right hxv⟩
        · refine (hfin_G₂'.2.union (finite_singleton f)).subset ?_
          intro e he
          by_cases hef : e = f
          · exact Or.inr hef
          · left
            rw [edgeSet_contractEdgeInto]
            exact ⟨he, hef⟩
      obtain ⟨hN_step, hV_step, hE_step⟩ :=
        splitInvariantN_of_obtainedBySplittingVertex hfin_succ hfin_m hsp'
      refine ⟨hfin_succ, by omega, by omega, by omega⟩
  obtain ⟨_, hN_k, hV_k, hE_k⟩ := hseq k le_rfl
  have hlast_eq : H_seq ⟨k, Nat.lt_succ_self k⟩ = G := hlast
  rw [hlast_eq] at hN_k hV_k hE_k
  omega

/-- Every class $C$ of finite graphs with bounded $|V(G)| \le M$ and $|E(G)| \le K$ is finite up to
isomorphism (`IsFiniteUpToIso C`). -/
theorem isFiniteUpToIso_of_bounded_ncard {α : Type u} {β : Type v}
    {C : Set (Graph α β)} (hfin : ∀ G ∈ C, IsFiniteGraph G)
    (M K : ℕ) (hV : ∀ G ∈ C, V(G).ncard ≤ M) (hE : ∀ G ∈ C, E(G).ncard ≤ K) :
    IsFiniteUpToIso C := by
  classical
  let Code := Fin (M + 1) × Fin (K + 1) × (Fin K → Fin M → Fin M → Bool)
  have hvC_le : ∀ G : C,
      @Fintype.card V(G.1) (hfin G.1 G.2).1.fintype ≤ M := by
    intro G
    let _ : Fintype V(G.1) := (hfin G.1 G.2).1.fintype
    have h1 : V(G.1).ncard = Fintype.card V(G.1) := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    have h2 := hV G.1 G.2
    omega
  have heC_le : ∀ G : C,
      @Fintype.card E(G.1) (hfin G.1 G.2).2.fintype ≤ K := by
    intro G
    let _ : Fintype E(G.1) := (hfin G.1 G.2).2.fintype
    have h1 : E(G.1).ncard = Fintype.card E(G.1) := by
      rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    have h2 := hE G.1 G.2
    omega
  let encode (G : C) : Code :=
    letI : Fintype V(G.1) := (hfin G.1 G.2).1.fintype
    letI : Fintype E(G.1) := (hfin G.1 G.2).2.fintype
    let vC := Fintype.card V(G.1)
    let eC := Fintype.card E(G.1)
    let ev : Fin vC ≃ V(G.1) := (Fintype.equivFin V(G.1)).symm
    let ee : Fin eC ≃ E(G.1) := (Fintype.equivFin E(G.1)).symm
    (⟨vC, Nat.lt_succ_of_le (hvC_le G)⟩, ⟨eC, Nat.lt_succ_of_le (heC_le G)⟩,
      fun i x y =>
        if hi : i.1 < eC then
          if hx : x.1 < vC then
            if hy : y.1 < vC then
              decide (G.1.IsLink (ee ⟨i.1, hi⟩).1 (ev ⟨x.1, hx⟩).1 (ev ⟨y.1, hy⟩).1)
            else false
          else false
        else false)
  have hiso_of_encode_eq : ∀ G₁ G₂ : C, encode G₁ = encode G₂ → Nonempty (Iso G₁.1 G₂.1) := by
    intro G₁ G₂ heq
    let _ : Fintype V(G₁.1) := (hfin G₁.1 G₁.2).1.fintype
    let _ : Fintype E(G₁.1) := (hfin G₁.1 G₁.2).2.fintype
    let _ : Fintype V(G₂.1) := (hfin G₂.1 G₂.2).1.fintype
    let _ : Fintype E(G₂.1) := (hfin G₂.1 G₂.2).2.fintype
    have hv_card : Fintype.card V(G₁.1) = Fintype.card V(G₂.1) :=
      congrArg (fun c : Code => c.1.1) heq
    have he_card : Fintype.card E(G₁.1) = Fintype.card E(G₂.1) :=
      congrArg (fun c : Code => c.2.1.1) heq
    have hrel_eq : (encode G₁).2.2 = (encode G₂).2.2 :=
      congrArg (fun c : Code => c.2.2) heq
    let ev₁ : Fin (Fintype.card V(G₁.1)) ≃ V(G₁.1) := (Fintype.equivFin V(G₁.1)).symm
    let ee₁ : Fin (Fintype.card E(G₁.1)) ≃ E(G₁.1) := (Fintype.equivFin E(G₁.1)).symm
    let ev₂ : Fin (Fintype.card V(G₂.1)) ≃ V(G₂.1) := (Fintype.equivFin V(G₂.1)).symm
    let ee₂ : Fin (Fintype.card E(G₂.1)) ≃ E(G₂.1) := (Fintype.equivFin E(G₂.1)).symm
    refine ⟨{
      vertexEquiv := ev₁.symm.trans ((finCongr hv_card).trans ev₂)
      edgeEquiv := ee₁.symm.trans ((finCongr he_card).trans ee₂)
      isLink_iff := fun e x y => by
        let i₁ := ee₁.symm e
        let x₁ := ev₁.symm x
        let y₁ := ev₁.symm y
        have hi₁_M : i₁.1 < K := Nat.lt_of_lt_of_le i₁.2 (heC_le G₁)
        have hx₁_M : x₁.1 < M := Nat.lt_of_lt_of_le x₁.2 (hvC_le G₁)
        have hy₁_M : y₁.1 < M := Nat.lt_of_lt_of_le y₁.2 (hvC_le G₁)
        have hval := congrFun (congrFun (congrFun hrel_eq ⟨i₁.1, hi₁_M⟩) ⟨x₁.1, hx₁_M⟩) ⟨y₁.1, hy₁_M⟩
        dsimp only [encode] at hval
        have hi₂ : i₁.1 < Fintype.card E(G₂.1) := he_card ▸ i₁.2
        have hx₂ : x₁.1 < Fintype.card V(G₂.1) := hv_card ▸ x₁.2
        have hy₂ : y₁.1 < Fintype.card V(G₂.1) := hv_card ▸ y₁.2
        rw [dite_eq_left i₁.2, dite_eq_left x₁.2, dite_eq_left y₁.2,
          dite_eq_left hi₂, dite_eq_left hx₂, dite_eq_left hy₂, decide_eq_decide] at hval
        have he₁_eq : ee₁ ⟨i₁.1, i₁.2⟩ = e := ee₁.apply_symm_apply e
        have hx₁_eq : ev₁ ⟨x₁.1, x₁.2⟩ = x := ev₁.apply_symm_apply x
        have hy₁_eq : ev₁ ⟨y₁.1, y₁.2⟩ = y := ev₁.apply_symm_apply y
        rw [he₁_eq, hx₁_eq, hy₁_eq] at hval
        exact hval
    }⟩
  let R := range encode
  have : Finite R := Set.toFinite R
  choose rep hrep using fun c : R => c.2
  let F : Set (Graph α β) := range (fun c : R => (rep c).1)
  refine ⟨F, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact (rep c).2
  · intro G hG
    let c : R := ⟨encode ⟨G, hG⟩, ⟨G, hG⟩, rfl⟩
    refine ⟨(rep c).1, ⟨c, rfl⟩, ?_⟩
    exact hiso_of_encode_eq ⟨G, hG⟩ (rep c) (hrep c).symm

/-- **Graph Minors VIII, (2.3)** (page 259):
"(2.3) *For any graph $H$, $Z(H)$ is finite up to isomorphism.*" -/
theorem theorem_2_3_proof {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} (hH : IsFiniteGraph H) :
    IsFiniteUpToIso (splitClass H : Set (Graph α β)) := by
  refine isFiniteUpToIso_of_bounded_ncard (fun _ hG => hG.1)
    (V(H).ncard + splitInvariantN H) (E(H).ncard + splitInvariantN H) ?_ ?_
  · intro G hG
    exact (bounds_of_obtainedBySplittingVertices hG.1 hH hG.2).1
  · intro G hG
    exact (bounds_of_obtainedBySplittingVertices hG.1 hH hG.2).2

end GraphMinor.GM08
