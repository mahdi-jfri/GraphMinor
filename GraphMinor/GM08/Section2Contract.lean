module

public import GraphMinor.GM08.Section2Valency
public import GraphMinor.Minor.Basic

/-!
# Graph Minors VIII, Section 2: Contraction and Topological Containment Helpers

Helper lemmas on edge contraction (`contract`, `contractEdgeInto`), acyclic contracted edge sets,
divalent vertex suppression (`ObtainedBySuppressingDivalent`), topological containment
(`IsTopologicallyContained`), and vertex/edge cardinality monotone bounds under minors, used in the
proofs of (2.1), (2.2), and the Kuratowski theorem for surfaces in `GraphMinor/GM08/Section2.lean`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Graph Set Relation

universe u v u' v' u'' v''

/-- The relation of adjacency along edges in $C$ in a graph $G$. -/
abbrev ContractAdj {α : Type u} {β : Type v} (G : Graph α β) (C : Set β) (x y : α) : Prop :=
  ∃ e ∈ C, G.IsLink e x y

/-- The $C$-component of a vertex $v$ in $G$. -/
abbrev contractComp {α : Type u} {β : Type v} (G : Graph α β) (C : Set β) (v : α) : Set α :=
  {w | ReflTransGen (ContractAdj G C) v w}

@[simp]
theorem vertexSet_contract {α : Type u} {β : Type v} (G : Graph α β) (C : Set β) :
    V(contract G C) = contractComp G C '' V(G) := by
  simp [contract]

@[simp]
theorem edgeSet_contract {α : Type u} {β : Type v} (G : Graph α β) (C : Set β) :
    E(contract G C) = E(G) \ C := by
  simp [contract]

theorem mem_vertexSet_contract {α : Type u} {β : Type v} {G : Graph α β} {C : Set β} {X : Set α} :
    X ∈ V(contract G C) ↔ ∃ v ∈ V(G), contractComp G C v = X := by
  simp [contract]

theorem mem_edgeSet_contract {α : Type u} {β : Type v} {G : Graph α β} {C : Set β} {e : β} :
    e ∈ E(contract G C) ↔ e ∈ E(G) ∧ e ∉ C := by
  simp [contract]

theorem contract_isLink {α : Type u} {β : Type v} (G : Graph α β) (C : Set β) (e : β) (X Y : Set α) :
    (contract G C).IsLink e X Y ↔ e ∉ C ∧ ∃ x y, G.IsLink e x y ∧ contractComp G C x = X ∧
      contractComp G C y = Y := by
  simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map]
  exact and_comm

theorem contractAdj_symm {α : Type u} {β : Type v} {G : Graph α β} {C : Set β} {x y : α}
    (h : ContractAdj G C x y) : ContractAdj G C y x := by
  obtain ⟨e, he, hl⟩ := h
  exact ⟨e, he, hl.symm⟩

theorem reflTransGen_contractAdj_symm {α : Type u} {β : Type v} {G : Graph α β} {C : Set β}
    {x y : α} (h : ReflTransGen (ContractAdj G C) x y) :
    ReflTransGen (ContractAdj G C) y x := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hstep ih => exact (ReflTransGen.single (contractAdj_symm hstep)).trans ih

theorem contractComp_eq_iff {α : Type u} {β : Type v} (G : Graph α β) (C : Set β) (x y : α) :
    contractComp G C x = contractComp G C y ↔ ReflTransGen (ContractAdj G C) x y := by
  constructor
  · intro h
    have hy : y ∈ contractComp G C y := ReflTransGen.refl
    rw [← h] at hy
    exact hy
  · intro hxy
    ext z
    simp only [contractComp, mem_ofPred_eq]
    exact ⟨fun hxz => (reflTransGen_contractAdj_symm hxy).trans hxz,
      fun hyz => hxy.trans hyz⟩

theorem contractComp_empty {α : Type u} {β : Type v} (G : Graph α β) (v : α) :
    contractComp G ∅ v = {v} := by
  ext w
  simp only [contractComp, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep _ =>
      obtain ⟨_, he, _⟩ := hstep
      exact False.elim (notMem_empty _ he)
  · rintro rfl
    exact ReflTransGen.refl

/-- Every graph $G$ is isomorphic to `contract G ∅`. -/
noncomputable def iso_contract_empty {α : Type u} {β : Type v} (G : Graph α β) :
    Iso G (contract G ∅) := by
  have hinj : Function.Injective (contractComp G ∅) := fun x y h => by
    simpa [contractComp_empty] using h
  refine
    { vertexEquiv :=
        (Equiv.Set.image _ _ hinj).trans
          (Equiv.subtypeEquivRight fun _ => by rw [vertexSet_contract])
      edgeEquiv := Equiv.subtypeEquivRight fun _ => by simp [contract]
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  simp [contract_isLink, contractComp_empty]

/-- Every subgraph $G' \le G$ is a minor of $G$. -/
theorem isIsoMinor_of_le {α : Type u} {β : Type v} {G' G : Graph α β} (hle : G' ≤ G) :
    IsIsoMinor G' G :=
  ⟨G', hle, ∅, empty_subset _, ⟨iso_contract_empty G'⟩⟩

/-- If $e \in E_1$ and its endpoints $u, v$ are connected by edges of $E_1 \setminus \{e\}$ in $G$,
then deleting $e$ and contracting $E_1 \setminus \{e\}$ produces the exact same graph as contracting
$E_1$ in $G$. -/
theorem contract_deleteEdges_singleton_of_connected {α : Type u} {β : Type v}
    (G : Graph α β) (E₁ : Set β) {e : β} {u v : α} (he : e ∈ E₁)
    (hl : G.IsLink e u v)
    (hconn : ReflTransGen (ContractAdj G (E₁ \ {e})) u v) :
    contract (G.deleteEdges {e}) (E₁ \ {e}) = contract G E₁ := by
  have hcomp : ∀ x : α,
      contractComp (G.deleteEdges {e}) (E₁ \ {e}) x = contractComp G E₁ x := by
    intro x
    ext y
    simp only [contractComp, mem_ofPred_eq]
    constructor
    · intro h
      induction h with
      | refl => exact ReflTransGen.refl
      | tail _ hstep ih =>
        obtain ⟨f, hf, hlf⟩ := hstep
        rw [deleteEdges_isLink] at hlf
        exact ih.tail ⟨f, hf.1, hlf.1⟩
    · intro h
      induction h with
      | refl => exact ReflTransGen.refl
      | tail _ hstep ih =>
        obtain ⟨f, hf, hlf⟩ := hstep
        by_cases hfe : f = e
        · subst hfe
          have hsub : ∀ a b, ReflTransGen (ContractAdj G (E₁ \ {f})) a b →
              ReflTransGen (ContractAdj (G.deleteEdges {f}) (E₁ \ {f})) a b := by
            intro a b hab
            induction hab with
            | refl => exact ReflTransGen.refl
            | tail _ hs ihs =>
              obtain ⟨g, hg, hlg⟩ := hs
              exact ihs.tail ⟨g, hg, by rw [deleteEdges_isLink]; exact ⟨hlg, hg.2⟩⟩
          rcases hlf.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ih.trans (hsub _ _ hconn)
          · exact ih.trans (hsub _ _ (reflTransGen_contractAdj_symm hconn))
        · exact ih.tail ⟨f, ⟨hf, hfe⟩, by rw [deleteEdges_isLink]; exact ⟨hlf, hfe⟩⟩
  have hmap : (G.deleteEdges {e}).map (contractComp (G.deleteEdges {e}) (E₁ \ {e})) =
      (G.map (contractComp G E₁)).deleteEdges {e} := by
    rw [funext hcomp]
    refine Graph.ext (by simp) fun f X Y => ?_
    constructor
    · rintro ⟨x, y, hl', rfl, rfl⟩
      rw [deleteEdges_isLink] at hl'
      rw [deleteEdges_isLink, map_isLink]
      exact ⟨⟨x, y, hl'.1, rfl, rfl⟩, hl'.2⟩
    · intro h
      rw [deleteEdges_isLink, map_isLink] at h
      obtain ⟨⟨x, y, hl', rfl, rfl⟩, hne⟩ := h
      exact ⟨x, y, by rw [deleteEdges_isLink]; exact ⟨hl', hne⟩, rfl, rfl⟩
  unfold contract
  change ((G.deleteEdges {e}).map (contractComp (G.deleteEdges {e}) (E₁ \ {e}))).deleteEdges (E₁ \ {e}) =
    (G.map (contractComp G E₁)).deleteEdges E₁
  rw [hmap, deleteEdges_deleteEdges, singleton_union, insert_sdiff_singleton,
    insert_eq_of_mem he]

/-- Under `contractEdgeInto G e u v` (for $e \in E_1$ and `G.IsLink e u v` with $u \ne v$),
reachability along $E_1$ in $G$ is equivalent to reachability along $E_1 \setminus \{e\}$ of the
projected vertices in `contractEdgeInto G e u v`. -/
theorem reflTransGen_contractEdgeInto_iff {α : Type u} {β : Type v}
    (G : Graph α β) (E₁ : Set β) {e : β} {u v : α}
    (he : e ∈ E₁) (hl : G.IsLink e u v) (hne : u ≠ v) (x y : α) :
    ReflTransGen (ContractAdj G E₁) x y ↔
      ReflTransGen (ContractAdj (contractEdgeInto G e u v) (E₁ \ {e}))
        (open Classical in if x = v then u else x)
        (open Classical in if y = v then u else y) := by
  classical
  let φ : α → α := fun z => if z = v then u else z
  have hφ_rel : ∀ z : α, ReflTransGen (ContractAdj G E₁) z (φ z) := by
    intro z
    dsimp [φ]
    by_cases hzv : z = v
    · subst hzv
      rw [ite_eq_left rfl]
      exact ReflTransGen.single ⟨e, he, hl.symm⟩
    · rw [ite_eq_right hzv]
  constructor
  · intro h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hstep ih =>
      obtain ⟨f, hf, hlf⟩ := hstep
      by_cases hfe : f = e
      · subst hfe
        rcases hlf.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        · simp only [ite_self, ite_true] at ih ⊢
          exact ih
      · refine ih.tail ⟨f, ⟨hf, hfe⟩, ?_⟩
        rw [contractEdgeInto_isLink]
        exact ⟨hfe, _, _, hlf, rfl, rfl⟩
  · intro h
    have h1 : ∀ a b : α,
        ReflTransGen (ContractAdj (contractEdgeInto G e u v) (E₁ \ {e})) a b →
        ReflTransGen (ContractAdj G E₁) a b := by
      intro a b hab
      induction hab with
      | refl => exact ReflTransGen.refl
      | tail _ hstep ih =>
        obtain ⟨f, hf, hlf⟩ := hstep
        rw [contractEdgeInto_isLink] at hlf
        obtain ⟨_, x₀, y₀, hlf₀, rfl, rfl⟩ := hlf
        have hstep₀ : ReflTransGen (ContractAdj G E₁) (φ x₀) (φ y₀) :=
          (reflTransGen_contractAdj_symm (hφ_rel x₀)).trans
            ((ReflTransGen.single ⟨f, hf.1, hlf₀⟩).trans (hφ_rel y₀))
        exact ih.trans hstep₀
    exact (hφ_rel x).trans ((h1 _ _ h).trans (reflTransGen_contractAdj_symm (hφ_rel y)))

/-- For $e \in E_1$, `G.IsLink e u v`, and $u \ne v$, the component of $\phi(x)$ in
`contractEdgeInto G e u v` along $E_1 \setminus \{e\}$ is `(contractComp G E₁ x) \ {v}`. -/
theorem contractComp_contractEdgeInto {α : Type u} {β : Type v}
    (G : Graph α β) (E₁ : Set β) {e : β} {u v : α}
    (he : e ∈ E₁) (hl : G.IsLink e u v) (hne : u ≠ v) (x : α) :
    contractComp (contractEdgeInto G e u v) (E₁ \ {e})
      (open Classical in if x = v then u else x) =
      (contractComp G E₁ x) \ {v} := by
  classical
  ext w
  simp only [contractComp, mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
  constructor
  · intro hw
    have hnotv : w ≠ v := by
      cases hw with
      | refl =>
        by_cases hxv : x = v
        · rw [ite_eq_left hxv]; exact hne
        · rw [ite_eq_right hxv]; exact hxv
      | tail _ hstep =>
        obtain ⟨f, _, hlf⟩ := hstep
        rw [contractEdgeInto_isLink] at hlf
        obtain ⟨_, x₀, y₀, _, _, hy₀⟩ := hlf
        rw [← hy₀]
        by_cases hyv : y₀ = v
        · rw [ite_eq_left hyv]; exact hne
        · rw [ite_eq_right hyv]; exact hyv
    rw [reflTransGen_contractEdgeInto_iff G E₁ he hl hne x w, ite_eq_right hnotv]
    exact ⟨hw, hnotv⟩
  · rintro ⟨hw, hnotv⟩
    rw [reflTransGen_contractEdgeInto_iff G E₁ he hl hne x w, ite_eq_right hnotv] at hw
    exact hw

/-- Contracting $E_1$ in $G$ is isomorphic to contracting $E_1 \setminus \{e\}$ in
`contractEdgeInto G e u v` whenever $e \in E_1$, `G.IsLink e u v`, and $u \ne v$. -/
noncomputable def iso_contract_contractEdgeInto {α : Type u} {β : Type v}
    (G : Graph α β) (E₁ : Set β) {e : β} {u v : α}
    (he : e ∈ E₁) (hl : G.IsLink e u v) (hne : u ≠ v) :
    Iso (contract G E₁) (contract (contractEdgeInto G e u v) (E₁ \ {e})) := by
  classical
  let G' := contractEdgeInto G e u v
  let E₁' := E₁ \ {e}
  let φ : α → α := fun z => if z = v then u else z
  have hcomp_v_iff_u : ∀ x : α, v ∈ contractComp G E₁ x ↔ u ∈ contractComp G E₁ x := by
    intro x
    simp only [contractComp, mem_ofPred_eq]
    exact ⟨fun hv => hv.tail ⟨e, he, hl.symm⟩, fun hu => hu.tail ⟨e, he, hl⟩⟩
  have hcomp_of_ne_v : ∀ y : α, y ≠ v →
      contractComp G' E₁' y = contractComp G E₁ y \ {v} := by
    intro y hyv
    have h := contractComp_contractEdgeInto G E₁ he hl hne y
    rwa [ite_eq_right hyv] at h
  have hto : ∀ X ∈ V(contract G E₁), X \ {v} ∈ V(contract G' E₁') := by
    rintro X hX
    rw [mem_vertexSet_contract] at hX ⊢
    obtain ⟨x, hx, rfl⟩ := hX
    refine ⟨φ x, ?_, contractComp_contractEdgeInto G E₁ he hl hne x⟩
    rw [vertexSet_contractEdgeInto hne hl, mem_sdiff, mem_singleton_iff]
    dsimp [φ]
    by_cases hxv : x = v
    · rw [ite_eq_left hxv]; exact ⟨hl.left_mem, hne⟩
    · rw [ite_eq_right hxv]; exact ⟨hx, hxv⟩
  have hinv : ∀ Y ∈ V(contract G' E₁'),
      (if u ∈ Y then Y ∪ {v} else Y) ∈ V(contract G E₁) := by
    rintro Y hY
    rw [mem_vertexSet_contract] at hY ⊢
    obtain ⟨y, hy, rfl⟩ := hY
    rw [vertexSet_contractEdgeInto hne hl, mem_sdiff, mem_singleton_iff] at hy
    refine ⟨y, hy.1, ?_⟩
    rw [hcomp_of_ne_v y hy.2]
    have hu_iff : u ∈ contractComp G E₁ y \ {v} ↔ v ∈ contractComp G E₁ y := by
      rw [mem_sdiff, mem_singleton_iff, and_iff_left hne, hcomp_v_iff_u]
    by_cases hvy : v ∈ contractComp G E₁ y
    · rw [ite_eq_left (hu_iff.mpr hvy), sdiff_union_self,
        union_eq_self_of_subset_right (singleton_subset_iff.mpr hvy)]
    · rw [ite_eq_right (mt hu_iff.mp hvy),
        sdiff_eq_left.mpr (disjoint_singleton_right.mpr hvy)]
  refine
    { vertexEquiv :=
        { toFun := fun X => ⟨X.1 \ {v}, hto X.1 X.2⟩
          invFun := fun Y => ⟨if u ∈ Y.1 then Y.1 ∪ {v} else Y.1, hinv Y.1 Y.2⟩
          left_inv := fun ⟨X, hX⟩ => by
            ext1
            rw [mem_vertexSet_contract] at hX
            obtain ⟨x, _, rfl⟩ := hX
            dsimp
            have hu_iff : u ∈ contractComp G E₁ x \ {v} ↔ v ∈ contractComp G E₁ x := by
              rw [mem_sdiff, mem_singleton_iff, and_iff_left hne, hcomp_v_iff_u]
            by_cases hvx : v ∈ contractComp G E₁ x
            · rw [ite_eq_left (hu_iff.mpr hvx), sdiff_union_self, union_eq_self_of_subset_right
                (singleton_subset_iff.mpr hvx)]
            · rw [ite_eq_right (mt hu_iff.mp hvx),
                sdiff_eq_left.mpr (disjoint_singleton_right.mpr hvx)]
          right_inv := fun ⟨Y, hY⟩ => by
            ext1
            dsimp
            have hnotv : v ∉ Y := by
              rw [mem_vertexSet_contract] at hY
              obtain ⟨y, hy, rfl⟩ := hY
              rw [vertexSet_contractEdgeInto hne hl, mem_sdiff, mem_singleton_iff] at hy
              rw [hcomp_of_ne_v y hy.2, mem_sdiff, mem_singleton_iff]
              exact fun h => h.2 rfl
            by_cases huY : u ∈ Y
            · rw [ite_eq_left huY, union_sdiff_right,
                sdiff_eq_left.mpr (disjoint_singleton_right.mpr hnotv)]
            · rw [ite_eq_right huY, sdiff_eq_left.mpr (disjoint_singleton_right.mpr hnotv)] }
      edgeEquiv := Equiv.subtypeEquivRight fun f => by
        rw [mem_edgeSet_contract, mem_edgeSet_contract, edgeSet_contractEdgeInto,
          mem_sdiff, mem_singleton_iff, mem_sdiff, mem_singleton_iff]
        exact ⟨fun ⟨hfG, hfE₁⟩ => ⟨⟨hfG, fun hfe => hfE₁ (hfe ▸ he)⟩, fun h => hfE₁ h.1⟩,
          fun ⟨⟨hfG, hfe⟩, hf'⟩ => ⟨hfG, fun hfE₁ => hf' ⟨hfE₁, hfe⟩⟩⟩
      isLink_iff := ?_ }
  rintro ⟨f, hf⟩ ⟨X, hX⟩ ⟨Y, hY⟩
  rw [contract_isLink, contract_isLink]
  simp only [Equiv.coe_fn_mk, Equiv.subtypeEquivRight_apply_coe]
  constructor
  · rintro ⟨hfE₁, x, y, hlf, rfl, rfl⟩
    have hfe : f ≠ e := fun h => hfE₁ (h ▸ he)
    refine ⟨fun h => hfE₁ h.1, φ x, φ y, ?_,
      contractComp_contractEdgeInto G E₁ he hl hne x,
      contractComp_contractEdgeInto G E₁ he hl hne y⟩
    rw [contractEdgeInto_isLink]
    exact ⟨hfe, x, y, hlf, rfl, rfl⟩
  · rintro ⟨hfE₁', a, b, hlf', ha, hb⟩
    rw [contractEdgeInto_isLink] at hlf'
    obtain ⟨hfe, x, y, hlf, rfl, rfl⟩ := hlf'
    refine ⟨fun hfE₁ => hfE₁' ⟨hfE₁, hfe⟩, x, y, hlf, ?_, ?_⟩
    · rw [mem_vertexSet_contract] at hX
      obtain ⟨x₀, _, rfl⟩ := hX
      have ha' : contractComp G' E₁' (φ x) = contractComp G' E₁' (φ x₀) :=
        ha.trans (contractComp_contractEdgeInto G E₁ he hl hne x₀).symm
      rw [contractComp_eq_iff] at ha' ⊢
      exact (reflTransGen_contractEdgeInto_iff G E₁ he hl hne x x₀).mpr ha'
    · rw [mem_vertexSet_contract] at hY
      obtain ⟨y₀, _, rfl⟩ := hY
      have hb' : contractComp G' E₁' (φ y) = contractComp G' E₁' (φ y₀) :=
        hb.trans (contractComp_contractEdgeInto G E₁ he hl hne y₀).symm
      rw [contractComp_eq_iff] at hb' ⊢
      exact (reflTransGen_contractEdgeInto_iff G E₁ he hl hne y y₀).mpr hb'

/-- Contracting a single non-loop edge $e$ via `contractEdgeInto G e u v` produces a minor of $G$. -/
theorem isIsoMinor_contractEdgeInto {α : Type u} {β : Type v}
    (G : Graph α β) {e : β} {u v : α} (hl : G.IsLink e u v) (hne : u ≠ v) :
    IsIsoMinor (contractEdgeInto G e u v) G := by
  refine ⟨G, le_rfl, {e}, singleton_subset_iff.mpr hl.edge_mem, ⟨?_⟩⟩
  have h1 := iso_contract_contractEdgeInto G {e} (mem_singleton e) hl hne
  rw [sdiff_self] at h1
  exact (iso_contract_empty (contractEdgeInto G e u v)).trans h1.symm

/-- An edge set $E_1$ in $G$ is acyclic (`IsAcyclicEdgeSet G E₁`) if no edge $e \in E_1$ has
its endpoints connected by a path of edges in $E_1 \setminus \{e\}$. -/
def IsAcyclicEdgeSet {α : Type u} {β : Type v} (G : Graph α β) (E₁ : Set β) : Prop :=
  ∀ e ∈ E₁, ∀ u v : α, G.IsLink e u v →
    ¬ ReflTransGen (ContractAdj G (E₁ \ {e})) u v

/-- Any edge in an acyclic edge set has distinct endpoints ($u \ne v$). -/
theorem ne_of_isAcyclicEdgeSet {α : Type u} {β : Type v} {G : Graph α β} {E₁ : Set β}
    (hacyc : IsAcyclicEdgeSet G E₁) {e : β} (he : e ∈ E₁) {u v : α} (hl : G.IsLink e u v) :
    u ≠ v := by
  rintro rfl
  exact hacyc e he u u hl ReflTransGen.refl

/-- Acyclicity of $E_1$ is preserved when contracting an edge $e \in E_1$ into `contractEdgeInto G e u v`. -/
theorem isAcyclicEdgeSet_contractEdgeInto {α : Type u} {β : Type v}
    {G : Graph α β} {E₁ : Set β} (hacyc : IsAcyclicEdgeSet G E₁)
    {e : β} (he : e ∈ E₁) {u v : α} (hl : G.IsLink e u v) :
    IsAcyclicEdgeSet (contractEdgeInto G e u v) (E₁ \ {e}) := by
  classical
  have hne : u ≠ v := ne_of_isAcyclicEdgeSet hacyc he hl
  intro f hf a b hlf hconn
  rw [contractEdgeInto_isLink] at hlf
  obtain ⟨hfe, x, y, hlfG, rfl, rfl⟩ := hlf
  have he_mem : e ∈ E₁ \ {f} := ⟨he, Ne.symm hfe⟩
  have hset : (E₁ \ {e}) \ {f} = (E₁ \ {f}) \ {e} := by
    ext g; simp only [mem_sdiff, mem_singleton_iff]; tauto
  rw [hset] at hconn
  have hconnG := (reflTransGen_contractEdgeInto_iff G (E₁ \ {f}) he_mem hl hne x y).mpr hconn
  exact hacyc f hf.1 x y hlfG hconnG

/-- If `vertexValency G v = 1` and `G.IsLink e u v` with $u \ne v$, then `contractEdgeInto G e u v`
is a subgraph of $G$ (`contractEdgeInto G e u v ≤ G`). -/
theorem contractEdgeInto_le_of_vertexValency_eq_one {α : Type u} {β : Type v}
    {G : Graph α β} (hfin : IsFiniteGraph G) {e : β} {u v : α}
    (hl : G.IsLink e u v) (hne : u ≠ v) (hval : vertexValency G v = 1) :
    contractEdgeInto G e u v ≤ G := by
  classical
  have hno_other : ∀ f ∈ E(G), f ≠ e → ¬ G.Inc f v := by
    intro f hf hfe hinc
    have hsum := vertexValency_eq_sum_edgeContribution hfin.2 v
    have he_mem : e ∈ hfin.2.toFinset := hfin.2.mem_toFinset.mpr hl.edge_mem
    have hf_mem : f ∈ hfin.2.toFinset := hfin.2.mem_toFinset.mpr hf
    have he_val : edgeContribution G e v = 1 := by
      rw [edgeContribution_eq_of_isLink hl v, ite_eq_right hne.symm, ite_eq_left rfl]
    have hf_val : 1 ≤ edgeContribution G f v := by
      obtain ⟨w, hlf⟩ := hinc
      rw [edgeContribution_eq_of_isLink hlf v, ite_eq_left rfl]
      omega
    have hle : edgeContribution G e v + edgeContribution G f v ≤
        ∑ g ∈ hfin.2.toFinset, edgeContribution G g v := by
      rw [← Finset.sum_erase_add _ _ he_mem]
      have hf_erase : f ∈ hfin.2.toFinset.erase e :=
        Finset.mem_erase.mpr ⟨hfe, hf_mem⟩
      rw [← Finset.sum_erase_add _ _ hf_erase]
      omega
    omega
  refine ⟨?_, ?_⟩
  · rw [vertexSet_contractEdgeInto hne hl]
    exact sdiff_subset
  · intro f x y hlf
    rw [contractEdgeInto_isLink] at hlf
    obtain ⟨hfe, x₀, y₀, hlfG, rfl, rfl⟩ := hlf
    have hx₀v : x₀ ≠ v := fun h => hno_other f hlfG.edge_mem hfe (h ▸ hlfG.inc_left)
    have hy₀v : y₀ ≠ v := fun h => hno_other f hlfG.edge_mem hfe (h ▸ hlfG.inc_right)
    rw [ite_eq_right hx₀v, ite_eq_right hy₀v]
    exact hlfG

/-- In a finite graph $G$, if $v$ has valency 2 and is incident with $e \ne f$ where
`G.IsLink e u v` and `G.Inc f v`, then $u \ne v$. -/
theorem ne_of_suppressDivalentStep {α : Type u} {β : Type v}
    {G : Graph α β} (hfin : IsFiniteGraph G) {e f : β} {u v : α}
    (hef : e ≠ f) (hl : G.IsLink e u v) (hf : G.Inc f v) (hval : vertexValency G v = 2) :
    u ≠ v := by
  classical
  rintro rfl
  have hsum := vertexValency_eq_sum_edgeContribution hfin.2 u
  have he_mem : e ∈ hfin.2.toFinset := hfin.2.mem_toFinset.mpr hl.edge_mem
  obtain ⟨w, hlf⟩ := hf
  have hf_mem : f ∈ hfin.2.toFinset.erase e :=
    Finset.mem_erase.mpr ⟨hef.symm, hfin.2.mem_toFinset.mpr hlf.edge_mem⟩
  have he_val : edgeContribution G e u = 2 := by
    rw [edgeContribution_eq_of_isLink hl u, ite_eq_left rfl]
  have hf_val : 1 ≤ edgeContribution G f u := by
    rw [edgeContribution_eq_of_isLink hlf u, ite_eq_left rfl]
    omega
  have hle : edgeContribution G e u + edgeContribution G f u ≤
      ∑ g ∈ hfin.2.toFinset, edgeContribution G g u := by
    rw [← Finset.sum_erase_add _ _ he_mem, ← Finset.sum_erase_add _ _ hf_mem]
    omega
  omega

/-- In a finite graph $G$, if `u ≠ v`, `G.IsLink e u v`, and `vertexValency G v = 2`, then
`SuppressDivalentStep G (contractEdgeInto G e u v)` holds. -/
theorem suppressDivalentStep_of_valency_two {α : Type u} {β : Type v}
    {G : Graph α β} (hfin : IsFiniteGraph G) {e : β} {u v : α}
    (hne : u ≠ v) (hl : G.IsLink e u v) (hval : vertexValency G v = 2) :
    SuppressDivalentStep G (contractEdgeInto G e u v) := by
  classical
  have hsum := vertexValency_eq_sum_edgeContribution hfin.2 v
  have he_mem : e ∈ hfin.2.toFinset := hfin.2.mem_toFinset.mpr hl.edge_mem
  have he_val : edgeContribution G e v = 1 := by
    rw [edgeContribution_eq_of_isLink hl v, ite_eq_right hne.symm, ite_eq_left rfl]
  have hrest_sum : ∑ f ∈ hfin.2.toFinset.erase e, edgeContribution G f v = 1 := by
    rw [← Finset.sum_erase_add _ _ he_mem] at hsum
    omega
  obtain ⟨f, hf_mem, hf_ne_zero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ f ∈ hfin.2.toFinset.erase e, edgeContribution G f v ≠ 0)
  have hfe : f ≠ e := (Finset.mem_erase.mp hf_mem).1
  have hfE : f ∈ E(G) := hfin.2.mem_toFinset.mp (Finset.mem_erase.mp hf_mem).2
  obtain ⟨x, y, hlf⟩ := exists_isLink_of_mem_edgeSet hfE
  have hf_inc : G.Inc f v := by
    by_contra hninc
    have hxv : v ≠ x := fun h => hninc (h ▸ hlf.inc_left)
    have hyv : v ≠ y := fun h => hninc (h ▸ hlf.inc_right)
    rw [edgeContribution_eq_of_isLink hlf v, ite_eq_right hxv, ite_eq_right hyv] at hf_ne_zero
    exact hf_ne_zero rfl
  exact ⟨e, f, u, v, hfe.symm, hl, hf_inc, hval, rfl⟩

/-- Every `SuppressDivalentStep G₁ G₂` on a finite graph $G_1$ preserves finiteness and gives
`IsIsoMinor G₂ G₁`. -/
theorem isFiniteGraph_and_isIsoMinor_of_suppressDivalentStep {α : Type u} {β : Type v}
    {G₁ G₂ : Graph α β} (hfin₁ : IsFiniteGraph G₁) (h : SuppressDivalentStep G₁ G₂) :
    IsFiniteGraph G₂ ∧ IsIsoMinor G₂ G₁ := by
  obtain ⟨e, f, u, v, hef, hl, hf, hval, rfl⟩ := h
  have hne : u ≠ v := ne_of_suppressDivalentStep hfin₁ hef hl hf hval
  exact ⟨isFiniteGraph_contractEdgeInto hfin₁ e u v, isIsoMinor_contractEdgeInto G₁ hl hne⟩

/-- If `ObtainedBySuppressingDivalent G₀ G'` and $G_0$ is finite, then $G'$ is finite and
`IsIsoMinor G' G₀`. -/
theorem isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent {α : Type u} {β : Type v}
    {G₀ G' : Graph α β} (hfin₀ : IsFiniteGraph G₀)
    (h : ObtainedBySuppressingDivalent G₀ G') :
    IsFiniteGraph G' ∧ IsIsoMinor G' G₀ := by
  induction h with
  | refl => exact ⟨hfin₀, IsIsoMinor.refl G₀⟩
  | tail _ hstep ih =>
    obtain ⟨hfin_mid, hmin_mid⟩ := ih
    obtain ⟨hfin', hmin'⟩ := isFiniteGraph_and_isIsoMinor_of_suppressDivalentStep hfin_mid hstep
    exact ⟨hfin', hmin'.trans hmin_mid⟩

/-- If $H$ is topologically contained in a finite graph $G$ (`IsTopologicallyContained H G`),
then $H$ is a minor of $G$ (`IsIsoMinor H G`). -/
theorem isIsoMinor_of_isTopologicallyContained {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (hfinG : IsFiniteGraph G)
    (h : IsTopologicallyContained H G) :
    IsIsoMinor H G := by
  obtain ⟨G₀, hle, G', hsup, ⟨φ⟩⟩ := h
  have hfin₀ : IsFiniteGraph G₀ :=
    ⟨hfinG.1.subset hle.vertexSet_mono, hfinG.2.subset hle.edgeSet_mono⟩
  obtain ⟨_, hmin⟩ := isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfin₀ hsup
  exact (φ.isIsoMinor_left hmin).trans (isIsoMinor_of_le hle)

/-- `IsTopologicallyContained` is reflexive. -/
theorem isTopologicallyContained_refl {α : Type u} {β : Type v} (G : Graph α β) :
    IsTopologicallyContained G G :=
  ⟨G, le_rfl, G, ReflTransGen.refl, ⟨Iso.refl G⟩⟩

/-- `IsTopologicallyContained` is invariant under isomorphism on the left. -/
theorem isTopologicallyContained_of_iso_left {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {α'' : Type u''} {β'' : Type v''}
    {H₁ : Graph α' β'} {H₂ : Graph α'' β''} {G : Graph α β}
    (φ : Iso H₁ H₂) (h : IsTopologicallyContained H₂ G) :
    IsTopologicallyContained H₁ G := by
  obtain ⟨G₀, hle, G', hsup, ⟨ψ⟩⟩ := h
  exact ⟨G₀, hle, G', hsup, ⟨φ.trans ψ⟩⟩

/-- If $K_2 \le G_2$ where `SuppressDivalentStep G₁ G₂` on a finite graph $G_1$, and
`ObtainedBySuppressingDivalent K₂ K'`, then there exists $K_1 \le G_1$ with
`ObtainedBySuppressingDivalent K₁ K'`. -/
theorem exists_le_obtainedBySuppressingDivalent_of_step {α : Type u} {β : Type v}
    {G₁ G₂ K₂ K' : Graph α β}
    (hfin₁ : IsFiniteGraph G₁) (hstep : SuppressDivalentStep G₁ G₂)
    (hK₂_le : K₂ ≤ G₂) (hsup : ObtainedBySuppressingDivalent K₂ K') :
    ∃ K₁ ≤ G₁, ObtainedBySuppressingDivalent K₁ K' := by
  classical
  obtain ⟨f, f_other, u, v, hef_other, hlf, hf_other, hval, rfl⟩ := hstep
  have hne : u ≠ v := ne_of_suppressDivalentStep hfin₁ hef_other hlf hf_other hval
  let G₁' := contractEdgeInto G₁ f u v
  have hV_G₁' : V(G₁') = V(G₁) \ {v} := vertexSet_contractEdgeInto hne hlf
  have hv_notMem_K₂ : v ∉ V(K₂) := by
    intro hv
    have hv' := hK₂_le.vertexSet_mono hv
    rw [hV_G₁', mem_sdiff, mem_singleton_iff] at hv'
    exact hv'.2 rfl
  have hf_notMem_K₂ : f ∉ E(K₂) := by
    intro hf
    have hf' := hK₂_le.edgeSet_mono hf
    rw [edgeSet_contractEdgeInto, mem_sdiff, mem_singleton_iff] at hf'
    exact hf'.2 rfl
  by_cases hinc : ∃ g ∈ E(K₂), G₁.Inc g v
  · obtain ⟨g, hgK₂, hginc⟩ := hinc
    have hgf : g ≠ f := fun h => hf_notMem_K₂ (h ▸ hgK₂)
    have hg_unique : edgeContribution G₁ g v = 1 ∧
        ∀ e ∈ E(G₁), e ≠ f → e ≠ g → ¬ G₁.Inc e v := by
      have hsum := vertexValency_eq_sum_edgeContribution hfin₁.2 v
      have hf_mem : f ∈ hfin₁.2.toFinset := hfin₁.2.mem_toFinset.mpr hlf.edge_mem
      have hgG₁ : g ∈ E(G₁) := by
        have hg' := hK₂_le.edgeSet_mono hgK₂
        rw [edgeSet_contractEdgeInto] at hg'
        exact hg'.1
      have hg_mem : g ∈ hfin₁.2.toFinset := hfin₁.2.mem_toFinset.mpr hgG₁
      have hf_val : edgeContribution G₁ f v = 1 := by
        rw [edgeContribution_eq_of_isLink hlf v, ite_eq_right hne.symm, ite_eq_left rfl]
      have hg_ge : 1 ≤ edgeContribution G₁ g v := by
        obtain ⟨w, hlg⟩ := hginc
        rw [edgeContribution_eq_of_isLink hlg v, ite_eq_left rfl]
        omega
      have hg_erase : g ∈ hfin₁.2.toFinset.erase f :=
        Finset.mem_erase.mpr ⟨hgf, hg_mem⟩
      have hsplit_sum : vertexValency G₁ v =
          edgeContribution G₁ f v + edgeContribution G₁ g v +
            ∑ e ∈ (hfin₁.2.toFinset.erase f).erase g, edgeContribution G₁ e v := by
        rw [hsum, ← Finset.sum_erase_add _ _ hf_mem, ← Finset.sum_erase_add _ _ hg_erase]
        omega
      refine ⟨by omega, ?_⟩
      intro e heG₁ hef heg heinc
      have he_mem : e ∈ (hfin₁.2.toFinset.erase f).erase g :=
        Finset.mem_erase.mpr ⟨heg, Finset.mem_erase.mpr ⟨hef, hfin₁.2.mem_toFinset.mpr heG₁⟩⟩
      have he_ge : 1 ≤ edgeContribution G₁ e v := by
        obtain ⟨w, hle⟩ := heinc
        rw [edgeContribution_eq_of_isLink hle v, ite_eq_left rfl]
        omega
      have hle_sum : edgeContribution G₁ e v ≤
          ∑ e' ∈ (hfin₁.2.toFinset.erase f).erase g, edgeContribution G₁ e' v := by
        rw [← Finset.sum_erase_add _ _ he_mem]
        omega
      omega
    obtain ⟨w, hlg⟩ := hginc
    have hwv : w ≠ v := by
      rintro rfl
      have h1 := hg_unique.1
      rw [edgeContribution_eq_of_isLink hlg w, ite_eq_left rfl] at h1
      omega
    obtain ⟨a, b, hlgK₂⟩ := exists_isLink_of_mem_edgeSet hgK₂
    have hlgG₁' : G₁'.IsLink g a b := hlgK₂.mono hK₂_le
    rw [contractEdgeInto_isLink] at hlgG₁'
    obtain ⟨_, x₀, y₀, hlg₀, rfl, rfl⟩ := hlgG₁'
    have hu_mem_K₂ : u ∈ V(K₂) := by
      rcases hlg₀.eq_and_eq_or_eq_and_eq hlg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h := hlgK₂.left_mem
        rwa [ite_eq_left rfl] at h
      · have h := hlgK₂.right_mem
        rwa [ite_eq_left rfl] at h
    have hw_mem_K₂ : w ∈ V(K₂) := by
      rcases hlg₀.eq_and_eq_or_eq_and_eq hlg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h := hlgK₂.right_mem
        rwa [ite_eq_right hwv] at h
      · have h := hlgK₂.left_mem
        rwa [ite_eq_right hwv] at h
    let K₁ : Graph α β := (G₁.induce (V(K₂) ∪ {v})).restrict (E(K₂) ∪ {f})
    have hK₁_le : K₁ ≤ G₁ := restrict_le.trans (G₁.induce_le <|
      union_subset (hK₂_le.vertexSet_mono.trans (by rw [hV_G₁']; exact sdiff_subset))
        (singleton_subset_iff.mpr hlf.right_mem))
    have hlf_K₁ : K₁.IsLink f u v := by
      dsimp [K₁]
      rw [restrict_isLink, induce_isLink]
      exact ⟨Or.inr (mem_singleton f), hlf, Or.inl hu_mem_K₂, Or.inr (mem_singleton v)⟩
    have hlg_K₁ : K₁.IsLink g v w := by
      dsimp [K₁]
      rw [restrict_isLink, induce_isLink]
      exact ⟨Or.inl hgK₂, hlg, Or.inr (mem_singleton v), Or.inl hw_mem_K₂⟩
    have hfin_K₁ : IsFiniteGraph K₁ :=
      ⟨hfin₁.1.subset hK₁_le.vertexSet_mono, hfin₁.2.subset hK₁_le.edgeSet_mono⟩
    have hval_K₁ : vertexValency K₁ v = 2 := by
      rw [vertexValency_eq_sum_edgeContribution hfin_K₁.2 v]
      have hf_mem : f ∈ hfin_K₁.2.toFinset := hfin_K₁.2.mem_toFinset.mpr hlf_K₁.edge_mem
      have hg_mem : g ∈ hfin_K₁.2.toFinset.erase f :=
        Finset.mem_erase.mpr ⟨hgf, hfin_K₁.2.mem_toFinset.mpr hlg_K₁.edge_mem⟩
      rw [← Finset.sum_erase_add _ _ hf_mem, ← Finset.sum_erase_add _ _ hg_mem]
      have hf_c : edgeContribution K₁ f v = 1 := by
        rw [edgeContribution_eq_of_isLink hlf_K₁ v, ite_eq_right hne.symm, ite_eq_left rfl]
      have hg_c : edgeContribution K₁ g v = 1 := by
        rw [edgeContribution_eq_of_isLink hlg_K₁ v, ite_eq_left rfl, ite_eq_right hwv.symm]
      have hrest_zero : ∑ e ∈ (hfin_K₁.2.toFinset.erase f).erase g, edgeContribution K₁ e v = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        have heg : e ≠ g := (Finset.mem_erase.mp he).1
        have hef : e ≠ f := (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).1
        have heK₁ : e ∈ E(K₁) := hfin_K₁.2.mem_toFinset.mp (Finset.mem_erase.mp (Finset.mem_erase.mp he).2).2
        have hninc : ¬ K₁.Inc e v := fun hincK₁ =>
          hg_unique.2 e (hK₁_le.edgeSet_mono heK₁) hef heg (hincK₁.mono hK₁_le)
        have hnloop : ¬ K₁.IsLink e v v := fun hl => hninc hl.inc_left
        unfold edgeContribution
        rw [ite_eq_right hnloop, ite_eq_right hninc]
      omega
    have hcontract_eq : contractEdgeInto K₁ f u v = K₂ := by
      refine Graph.ext ?_ fun e x y => ?_
      · rw [vertexSet_contractEdgeInto hne hlf_K₁]
        have hVK₁ : V(K₁) = V(K₂) ∪ {v} := rfl
        rw [hVK₁, union_sdiff_right, sdiff_eq_left.mpr (disjoint_singleton_right.mpr hv_notMem_K₂)]
      · rw [contractEdgeInto_isLink]
        constructor
        · rintro ⟨hef, x₁, y₁, hlK₁, rfl, rfl⟩
          dsimp [K₁] at hlK₁
          rw [restrict_isLink, induce_isLink] at hlK₁
          obtain ⟨he_mem, hlG₁, _, _⟩ := hlK₁
          have heK₂ : e ∈ E(K₂) := by
            rcases he_mem with h | h
            · exact h
            · exact False.elim (hef (mem_singleton_iff.mp h))
          obtain ⟨a', b', hlK₂'⟩ := exists_isLink_of_mem_edgeSet heK₂
          have hlG₁'' : G₁'.IsLink e a' b' := hlK₂'.mono hK₂_le
          have hlG₁' : G₁'.IsLink e (if x₁ = v then u else x₁) (if y₁ = v then u else y₁) := by
            rw [contractEdgeInto_isLink]
            exact ⟨hef, x₁, y₁, hlG₁, rfl, rfl⟩
          rcases hlG₁'.eq_and_eq_or_eq_and_eq hlG₁'' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact hlK₂'
          · rw [h1, h2]; exact hlK₂'.symm
        · intro hlK₂
          have hef : e ≠ f := fun h => hf_notMem_K₂ (h ▸ hlK₂.edge_mem)
          have hlG₁' : G₁'.IsLink e x y := hlK₂.mono hK₂_le
          rw [contractEdgeInto_isLink] at hlG₁'
          obtain ⟨_, x₁, y₁, hlG₁, rfl, rfl⟩ := hlG₁'
          have hx₁_mem : x₁ ∈ V(K₂) ∪ {v} := by
            by_cases hxv : x₁ = v
            · exact Or.inr (mem_singleton_iff.mpr hxv)
            · left
              have h := hlK₂.left_mem
              rwa [ite_eq_right hxv] at h
          have hy₁_mem : y₁ ∈ V(K₂) ∪ {v} := by
            by_cases hyv : y₁ = v
            · exact Or.inr (mem_singleton_iff.mpr hyv)
            · left
              have h := hlK₂.right_mem
              rwa [ite_eq_right hyv] at h
          have hlK₁ : K₁.IsLink e x₁ y₁ := by
            dsimp [K₁]
            rw [restrict_isLink, induce_isLink]
            exact ⟨Or.inl hlK₂.edge_mem, hlG₁, hx₁_mem, hy₁_mem⟩
          exact ⟨hef, x₁, y₁, hlK₁, rfl, rfl⟩
    have hstep_K₁ : SuppressDivalentStep K₁ K₂ :=
      ⟨f, g, u, v, hgf.symm, hlf_K₁, hlg_K₁.inc_left, hval_K₁, hcontract_eq.symm⟩
    exact ⟨K₁, hK₁_le, ReflTransGen.head hstep_K₁ hsup⟩
  · push Not at hinc
    have hK₂_le_G₁ : K₂ ≤ G₁ := by
      refine ⟨hK₂_le.vertexSet_mono.trans (by rw [hV_G₁']; exact sdiff_subset), ?_⟩
      intro e x y hlK₂
      have hlG₁' : G₁'.IsLink e x y := hlK₂.mono hK₂_le
      rw [contractEdgeInto_isLink] at hlG₁'
      obtain ⟨_, x₀, y₀, hlG₁, rfl, rfl⟩ := hlG₁'
      have hx₀v : x₀ ≠ v := fun h => hinc e hlK₂.edge_mem (h ▸ hlG₁.inc_left)
      have hy₀v : y₀ ≠ v := fun h => hinc e hlK₂.edge_mem (h ▸ hlG₁.inc_right)
      rw [ite_eq_right hx₀v, ite_eq_right hy₀v]
      exact hlG₁
    exact ⟨K₂, hK₂_le_G₁, hsup⟩

/-- Composing `ObtainedBySuppressingDivalent G₀ G'` with a subgraph $K_0 \le G'$ and
`ObtainedBySuppressingDivalent K₀ K'` yields $G_{00} \le G_0$ with
`ObtainedBySuppressingDivalent G₀₀ K'`. -/
theorem exists_le_obtainedBySuppressingDivalent_trans {α : Type u} {β : Type v}
    {G₀ G' K₀ K' : Graph α β}
    (hfin₀ : IsFiniteGraph G₀) (h₁ : ObtainedBySuppressingDivalent G₀ G')
    (hK₀_le : K₀ ≤ G') (h₂ : ObtainedBySuppressingDivalent K₀ K') :
    ∃ G₀₀ ≤ G₀, ObtainedBySuppressingDivalent G₀₀ K' := by
  induction h₁ generalizing K₀ with
  | refl => exact ⟨K₀, hK₀_le, h₂⟩
  | tail hprev hstep ih =>
    obtain ⟨hfin_mid, _⟩ :=
      isFiniteGraph_and_isIsoMinor_of_obtainedBySuppressingDivalent hfin₀ hprev
    obtain ⟨K₁, hK₁_le, hsup₁⟩ :=
      exists_le_obtainedBySuppressingDivalent_of_step hfin_mid hstep hK₀_le h₂
    exact ih hK₁_le hsup₁

/-- Two graphs $G' \le G$ with identical vertex and edge sets are equal ($G' = G$). -/
theorem eq_of_le_of_vertexSet_eq_of_edgeSet_eq {α : Type u} {β : Type v}
    {G' G : Graph α β} (hle : G' ≤ G) (hV : V(G') = V(G)) (hE : E(G') = E(G)) :
    G' = G := by
  refine Graph.ext hV fun e x y => ?_
  constructor
  · exact fun hl => hl.mono hle
  · intro hl
    have he' : e ∈ E(G') := hE ▸ hl.edge_mem
    obtain ⟨x', y', hl'⟩ := exists_isLink_of_mem_edgeSet he'
    rcases (hl'.mono hle).eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hl'
    · exact hl'.symm

/-- If $G$ is a finite graph and $H$ is a minor of $G$ (`IsIsoMinor H G`), then $H$ is finite and
$|V(H)| \le |V(G)|$ and $|E(H)| \le |E(G)|$. -/
theorem ncard_le_of_isIsoMinor {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (hfin : IsFiniteGraph G) (h : IsIsoMinor H G) :
    IsFiniteGraph H ∧ V(H).ncard ≤ V(G).ncard ∧ E(H).ncard ≤ E(G).ncard := by
  obtain ⟨G', hle, C, _, ⟨φ⟩⟩ := h
  have hfinG' : IsFiniteGraph G' :=
    ⟨hfin.1.subset hle.vertexSet_mono, hfin.2.subset hle.edgeSet_mono⟩
  have hfinC : IsFiniteGraph (contract G' C) := by
    refine ⟨?_, ?_⟩
    · rw [vertexSet_contract]
      exact hfinG'.1.image _
    · rw [edgeSet_contract]
      exact hfinG'.2.sdiff
  have hfinH : IsFiniteGraph H := isFiniteGraph_of_iso φ.symm hfinC
  have hVH : V(H).ncard ≤ V(G).ncard := by
    rw [iso_ncard_vertexSet_eq φ, vertexSet_contract]
    exact (ncard_image_le hfinG'.1).trans (ncard_le_ncard hle.vertexSet_mono hfin.1)
  have hEH : E(H).ncard ≤ E(G).ncard := by
    rw [iso_ncard_edgeSet_eq φ, edgeSet_contract]
    exact (ncard_le_ncard sdiff_subset hfinG'.2).trans (ncard_le_ncard hle.edgeSet_mono hfin.2)
  exact ⟨hfinH, hVH, hEH⟩

/-- If $G$ is a finite graph, $H$ is a minor of $G$, and $|V(H)| + |E(H)| = |V(G)| + |E(G)|$,
then $H$ is isomorphic to $G$ (`Nonempty (Iso H G)`). -/
theorem iso_of_isIsoMinor_of_ncard_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (hfin : IsFiniteGraph G) (h : IsIsoMinor H G)
    (heq : V(H).ncard + E(H).ncard = V(G).ncard + E(G).ncard) :
    Nonempty (Iso H G) := by
  obtain ⟨_, hVH_le, hEH_le⟩ := ncard_le_of_isIsoMinor hfin h
  have hVH_eq : V(H).ncard = V(G).ncard := by omega
  have hEH_eq : E(H).ncard = E(G).ncard := by omega
  obtain ⟨G', hle, C, hC, ⟨φ⟩⟩ := h
  have hfinG' : IsFiniteGraph G' :=
    ⟨hfin.1.subset hle.vertexSet_mono, hfin.2.subset hle.edgeSet_mono⟩
  have hEC : (E(G') \ C).ncard = E(G).ncard := by
    have h1 := iso_ncard_edgeSet_eq φ
    rw [edgeSet_contract] at h1
    omega
  have hEG'_le : E(G').ncard ≤ E(G).ncard := ncard_le_ncard hle.edgeSet_mono hfin.2
  have hdiff_le : (E(G') \ C).ncard ≤ E(G').ncard := ncard_le_ncard sdiff_subset hfinG'.2
  have hdiff_eq : E(G') \ C = E(G') :=
    eq_of_subset_of_ncard_le sdiff_subset (by omega) hfinG'.2
  have hC_empty : C = ∅ := by
    ext e
    simp only [mem_empty_iff_false, iff_false]
    intro heC
    have heG' : e ∈ E(G') := hC heC
    rw [← hdiff_eq, mem_sdiff] at heG'
    exact heG'.2 heC
  have hEG'_eq : E(G') = E(G) :=
    eq_of_subset_of_ncard_le hle.edgeSet_mono (by omega) hfin.2
  have hVG'_eq : V(G') = V(G) := by
    have h1 := iso_ncard_vertexSet_eq φ
    rw [vertexSet_contract] at h1
    have h2 : (contractComp G' C '' V(G')).ncard ≤ V(G').ncard := ncard_image_le hfinG'.1
    have h3 : V(G').ncard ≤ V(G).ncard := ncard_le_ncard hle.vertexSet_mono hfin.1
    exact eq_of_subset_of_ncard_le hle.vertexSet_mono (by omega) hfin.1
  have hG'_eq : G' = G := eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle hVG'_eq hEG'_eq
  subst hG'_eq hC_empty
  exact ⟨φ.trans (iso_contract_empty _).symm⟩

/-- Any proper minor $H$ of a finite graph $G$ (`IsProperMinor H G`) is finite and satisfies
$|V(H)| + |E(H)| < |V(G)| + |E(G)|$. -/
theorem ncard_lt_of_isProperMinor {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G : Graph α β} (hfin : IsFiniteGraph G) (h : IsProperMinor H G) :
    IsFiniteGraph H ∧ V(H).ncard + E(H).ncard < V(G).ncard + E(G).ncard := by
  obtain ⟨hfinH, hVH, hEH⟩ := ncard_le_of_isIsoMinor hfin h.1
  refine ⟨hfinH, ?_⟩
  by_contra hnotlt
  have heq : V(H).ncard + E(H).ncard = V(G).ncard + E(G).ncard := by omega
  obtain ⟨φ⟩ := iso_of_isIsoMinor_of_ncard_eq hfin h.1 heq
  exact h.2 ⟨φ⟩

end GraphMinor.GM08
