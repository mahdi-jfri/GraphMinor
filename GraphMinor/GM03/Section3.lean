module

public import GraphMinor.GM03.Section3a

/-!
# Graph Minors III, Section 3 (Part 2): Sleeve Unions (3.8–3.10)

This file completes Section 3 of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64 (pages 58–59):
- `theorem_3_8`, (3.8): identifying the central circle of an $r \times s$ cylinder with $r$
  vertices $v_1, \dots, v_r$ of $H$ forces $v_1, \dots, v_r$ into a single bag of a
  tree-decomposition of $H$ of width $\le w$.
- `theorem_3_9`, (3.9): if $G$ is the sleeve union of $G_1, G_2$, then $G_1, G_2$ are isomorphic
  to proper minors of $G$.
- `theorem_3_10`, (3.10): if $G$ is the sleeve union of $G_1, G_2$, then the tree-width of $G$ is
  the maximum of the tree-widths of $G_1, G_2$.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Relation Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM16 GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-- Pulling back a tree-decomposition `(T, Y)` of `G` along an isomorphism `φS : Iso S₀ S'` onto a
subgraph `S' ≤ G` gives a tree-decomposition of `S₀`. -/
private lemma isTreeDecomposition_comap_iso_of_le
    {α₁ : Type u₁} {β₁ : Type v₁} {α₀ : Type u₂} {β₀ : Type v₂} {ι : Type w}
    {G S' : Graph α₁ β₁} {S₀ : Graph α₀ β₀} {T : SimpleGraph ι} {Y : ι → Set α₁}
    (hTD : IsTreeDecomposition G T Y) (hS' : S' ≤ G) (φS : Iso S₀ S') :
    IsTreeDecomposition S₀ T
      (fun t ↦ {p : α₀ | ∃ hp : p ∈ V(S₀), (φS.vertexEquiv ⟨p, hp⟩).1 ∈ Y t}) :=
  { isTree := hTD.isTree
    bag_subset := fun _ _ hp ↦ hp.1
    iUnion_bags := by
      ext p
      rw [mem_iUnion]
      refine ⟨fun ⟨_, hp, _⟩ ↦ hp, fun hp ↦ ?_⟩
      have hpG : (φS.vertexEquiv ⟨p, hp⟩).1 ∈ V(G) :=
        hS'.vertexSet_mono (φS.vertexEquiv ⟨p, hp⟩).2
      rw [← hTD.iUnion_bags, mem_iUnion] at hpG
      obtain ⟨t, hpt⟩ := hpG
      exact ⟨t, hp, hpt⟩
    edge_in_bag := fun ⦃e p q⦄ hl ↦ by
      have hl' : S'.IsLink (φS.edgeEquiv ⟨e, hl.edge_mem⟩).1
          (φS.vertexEquiv ⟨p, hl.left_mem⟩).1 (φS.vertexEquiv ⟨q, hl.right_mem⟩).1 :=
        (φS.isLink_iff ⟨e, hl.edge_mem⟩ ⟨p, hl.left_mem⟩ ⟨q, hl.right_mem⟩).mp hl
      obtain ⟨t, hpt, hqt⟩ := hTD.edge_in_bag (hl'.mono hS')
      exact ⟨t, ⟨hl.left_mem, hpt⟩, ⟨hl.right_mem, hqt⟩⟩
    inter_subset_on_path := fun ⦃_ _ _⦄ hpath _ ⟨⟨hp, h₁⟩, ⟨_, h₂⟩⟩ ↦
      ⟨hp, hTD.inter_subset_on_path hpath ⟨h₁, h₂⟩⟩ }

/-- If `P ≤ S₀` is a connected subgraph and `φS : Iso S₀ S'` with `S' ≤ G`, then the induced
subgraph `G.induce (Subtype.val '' (φS.vertexEquiv '' {p : V(S₀) | p.1 ∈ V(P)}))` is a connected
subgraph of `G`. -/
private lemma isGraphConnected_induce_image_of_iso
    {α₁ : Type u₁} {β₁ : Type v₁} {α₀ : Type u₂} {β₀ : Type v₂}
    {G S' : Graph α₁ β₁} {S₀ P : Graph α₀ β₀}
    (hS' : S' ≤ G) (φS : Iso S₀ S') (hP_le : P ≤ S₀) (hP_conn : IsGraphConnected P) :
    G.induce {x : α₁ | ∃ (p : α₀) (hp : p ∈ V(P)),
        (φS.vertexEquiv ⟨p, hP_le.vertexSet_mono hp⟩).1 = x} ≤ G ∧
      IsGraphConnected (G.induce {x : α₁ | ∃ (p : α₀) (hp : p ∈ V(P)),
        (φS.vertexEquiv ⟨p, hP_le.vertexSet_mono hp⟩).1 = x}) := by
  let U : Set α₁ := {x : α₁ | ∃ (p : α₀) (hp : p ∈ V(P)),
    (φS.vertexEquiv ⟨p, hP_le.vertexSet_mono hp⟩).1 = x}
  have hU_sub : U ⊆ V(G) := by
    rintro x ⟨p, hpP, rfl⟩
    exact hS'.vertexSet_mono (φS.vertexEquiv ⟨p, hP_le.vertexSet_mono hpP⟩).2
  refine ⟨G.induce_le hU_sub, ?_⟩
  obtain ⟨p₀, hp₀⟩ := hP_conn.1
  refine ⟨⟨(φS.vertexEquiv ⟨p₀, hP_le.vertexSet_mono hp₀⟩).1, p₀, hp₀, rfl⟩, ?_⟩
  rintro x ⟨p, hpP, rfl⟩ y ⟨q, hqP, rfl⟩
  obtain ⟨W⟩ := hP_conn.2 p hpP q hqP
  have hwalk : ∀ {a b : α₀} (W : GraphWalk P a b) (ha : a ∈ V(P)) (hb : b ∈ V(P)),
      Nonempty (GraphWalk (G.induce U)
        (φS.vertexEquiv ⟨a, hP_le.vertexSet_mono ha⟩).1
        (φS.vertexEquiv ⟨b, hP_le.vertexSet_mono hb⟩).1) := by
    intro a b W
    induction W with
    | @nil a ha =>
      intro _ _
      exact ⟨.nil ⟨a, ha, rfl⟩⟩
    | @cons a b c e hl W' ih =>
      intro _ hc
      obtain ⟨W'_G⟩ := ih hl.right_mem hc
      have hl_S₀ : S₀.IsLink e a b := hl.mono hP_le
      have hl_S' : S'.IsLink (φS.edgeEquiv ⟨e, hl_S₀.edge_mem⟩).1
          (φS.vertexEquiv ⟨a, hl_S₀.left_mem⟩).1
          (φS.vertexEquiv ⟨b, hl_S₀.right_mem⟩).1 :=
        (φS.isLink_iff ⟨e, hl_S₀.edge_mem⟩ ⟨a, hl_S₀.left_mem⟩ ⟨b, hl_S₀.right_mem⟩).mp hl_S₀
      have hl_ind : (G.induce U).IsLink (φS.edgeEquiv ⟨e, hl_S₀.edge_mem⟩).1
          (φS.vertexEquiv ⟨a, hl_S₀.left_mem⟩).1
          (φS.vertexEquiv ⟨b, hl_S₀.right_mem⟩).1 :=
        ⟨hl_S'.mono hS', ⟨a, hl.left_mem, rfl⟩, ⟨b, hl.right_mem, rfl⟩⟩
      exact ⟨.cons hl_ind W'_G⟩
  exact hwalk W hpP hqP

/-- **The strengthened Graph Minors III, (3.8)**, as Graph Minors VIII, Section 11 (page 273)
states it: "If $G$ has a tree-decomposition $(T, (Y_t : t \in V(T)))$ of width $\le w$, then $H$ has a
tree-decomposition $(T, (X_t : t \in V(T)))$ of width $\le w$ such that $Y_t \cap V(H) \subseteq X_t$
for every $t \in V(T)$, and $\{v_1, \dots, v_r\} \subseteq X_{t_0}$ for some $t_0 \in V(T)$." VIII says
that "The proof given in [7] serves as well to prove this strengthened form", and this is that proof.
Here the identification of III is given by its parts: `H` is a copy `H'` of itself inside `G` by
`φH`, so `Y_t ∩ V(H)` means the vertices `u` of `H` with `φH u ∈ Y_t`. -/
theorem theorem_3_8_strong {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {ι : Type w} [Fintype ι]
    {r : ℕ} {G : Graph α₁ β₁} {H : Graph α₂ β₂} (hVG : V(G).Finite)
    (s : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s) (v : Fin r → α₂)
    (hv_inj : Function.Injective v) (hv : ∀ i : Fin r, v i ∈ V(H))
    {H' S' : Graph α₁ β₁} (φH : Iso H H') (φS : Iso (cylinderGraph r s) S')
    (hSep : IsGraphSeparation G H' S')
    (hinter : V(H') ∩ V(S') = Set.range (fun i : Fin r => (φH.vertexEquiv ⟨v i, hv i⟩).1))
    (hident : ∀ i : Fin r,
      (φS.vertexEquiv ⟨(i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩), Set.mem_univ _⟩).1 =
        (φH.vertexEquiv ⟨v i, hv i⟩).1)
    {T : SimpleGraph ι} {Y : ι → Set α₁} (hTD : IsTreeDecomposition G T Y) {w' : ℕ}
    (hw : TreeDecompHasWidthLE Y w') :
    ∃ (X : ι → Set α₂) (t₀ : ι), IsTreeDecomposition H T X ∧ TreeDecompHasWidthLE X w' ∧
      (∀ t u (hu : u ∈ V(H)), (φH.vertexEquiv ⟨u, hu⟩).1 ∈ Y t → u ∈ X t) ∧
      Set.range v ⊆ X t₀ := by
  classical
  have hTD_S0 := isTreeDecomposition_comap_iso_of_le hTD hSep.2.1 φS
  let Y_S : ι → Set (Fin r × Fin s) :=
    fun t ↦ {p : Fin r × Fin s | (φS.vertexEquiv ⟨p, Set.mem_univ _⟩).1 ∈ Y t}
  have hTD_S : IsTreeDecomposition (cylinderGraph r s) T Y_S := by
    convert hTD_S0 using 2
    ext p
    simp [Y_S, cylinderGraph]
  obtain ⟨t₀, P, hP_disj, hP_path⟩ := theorem_3_7_proof r s hs hr hTD_S
  let j_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  have hex_end : ∀ k : Fin r, ∃ i : Fin r,
      (Y_S t₀ ∩ V(P k)).Nonempty ∧ (i, j_last) ∈ V(P k) ∧
      P k ≤ cylinderGraph r s ∧ IsGraphConnected (P k) := by
    intro k
    obtain ⟨u_k, hu_k, v_k, hv_k, hPk⟩ := hP_path k
    have hu_mem : u_k ∈ V(P k) := hPk.left_mem
    have hv_mem : v_k ∈ V(P k) := hPk.right_mem
    have hv_eq : v_k = (v_k.1, j_last) := Prod.ext rfl hv_k
    have hPk_conn : IsGraphConnected (P k) := by
      refine ⟨⟨u_k, hu_mem⟩, fun x hx y hy ↦ ?_⟩
      obtain ⟨Q, hQP, ⟨_, W_Q, _, _, _⟩, _⟩ := hPk.exists_subpath hx hy
      obtain ⟨W_P, _, _⟩ := exists_walk_up_of_le hQP W_Q
      exact ⟨W_P⟩
    exact ⟨v_k.1, ⟨u_k, hu_k, hu_mem⟩, hv_eq ▸ hv_mem, hPk.le, hPk_conn⟩
  choose σ hσ_Y₀ hσ_end hP_le hP_conn using hex_end
  have hσ_inj : Function.Injective σ := by
    intro k₁ k₂ heq
    by_contra hne
    exact Set.disjoint_left.mp (hP_disj hne) (hσ_end k₁) (heq ▸ hσ_end k₂)
  have hσ_bij : Function.Bijective σ :=
    (Fintype.bijective_iff_injective_and_card σ).mpr ⟨hσ_inj, rfl⟩
  let eσ : Fin r ≃ Fin r := Equiv.ofBijective σ hσ_bij
  let P' : Fin r → Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)) :=
    fun i ↦ P (eσ.symm i)
  have hP'_end : ∀ i : Fin r, (i, j_last) ∈ V(P' i) := by
    intro i
    have h := hσ_end (eσ.symm i)
    change (eσ (eσ.symm i), j_last) ∈ V(P' i) at h
    simpa using h
  have hP'_Y₀ : ∀ i : Fin r, (Y_S t₀ ∩ V(P' i)).Nonempty := fun i ↦ hσ_Y₀ (eσ.symm i)
  have hP'_le : ∀ i : Fin r, P' i ≤ cylinderGraph r s := fun i ↦ hP_le (eσ.symm i)
  have hP'_conn : ∀ i : Fin r, IsGraphConnected (P' i) := fun i ↦ hP_conn (eσ.symm i)
  have hP'_disj : Pairwise (fun i₁ i₂ : Fin r ↦ Disjoint V(P' i₁) V(P' i₂)) :=
    fun _ _ hne ↦ hP_disj (eσ.symm.injective.ne hne)
  let U : α₂ → Set α₁ := fun u ↦
    if hu : u ∈ V(H) then
      if hr_mem : ∃ i : Fin r, v i = u then
        let i := hr_mem.choose
        {x : α₁ | ∃ p ∈ V(P' i), (φS.vertexEquiv ⟨p, Set.mem_univ _⟩).1 = x}
      else
        {(φH.vertexEquiv ⟨u, hu⟩).1}
    else ∅
  let Z : α₂ → Graph α₁ β₁ := fun u ↦ G.induce (U u)
  have hφH_mem_U : ∀ u (hu : u ∈ V(H)), (φH.vertexEquiv ⟨u, hu⟩).1 ∈ U u := by
    intro u hu
    dsimp [U]
    rw [dite_eq_left hu]
    split_ifs with hr_mem
    · let i := hr_mem.choose
      have hi : v i = u := hr_mem.choose_spec
      refine ⟨(i, j_last), hP'_end i, ?_⟩
      exact (hident i).trans (congrArg Subtype.val (congrArg φH.vertexEquiv (Subtype.ext hi)))
    · rfl
  have hZ_le_conn : ∀ u ∈ V(H), Z u ≤ G ∧ IsGraphConnected (Z u) := by
    intro u hu
    dsimp [Z, U]
    rw [dite_eq_left hu]
    split_ifs with hr_mem
    · convert isGraphConnected_induce_image_of_iso hSep.2.1 φS (hP'_le hr_mem.choose)
        (hP'_conn hr_mem.choose) using 3 <;>
        · ext x; exact ⟨fun ⟨p, hp, h⟩ ↦ ⟨p, hp, h⟩, fun ⟨p, hp, h⟩ ↦ ⟨p, hp, h⟩⟩
    · have hu_G : (φH.vertexEquiv ⟨u, hu⟩).1 ∈ V(G) :=
        hSep.1.vertexSet_mono (φH.vertexEquiv ⟨u, hu⟩).2
      refine ⟨G.induce_le (singleton_subset_iff.mpr hu_G), ⟨(φH.vertexEquiv ⟨u, hu⟩).1, rfl⟩, ?_⟩
      rintro x rfl y rfl
      exact ⟨.nil rfl⟩
  have hZ_disj : ∀ u₁ ∈ V(H), ∀ u₂ ∈ V(H), u₁ ≠ u₂ → Disjoint V(Z u₁) V(Z u₂) := by
    intro u₁ hu₁ u₂ hu₂ hne
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ?_
    change x ∈ U u₁ at hx₁
    change x ∈ U u₂ at hx₂
    dsimp [U] at hx₁ hx₂
    rw [dite_eq_left hu₁] at hx₁
    rw [dite_eq_left hu₂] at hx₂
    split_ifs at hx₁ hx₂ with h₁ h₂ h₂
    · obtain ⟨p₁, hp₁, rfl⟩ := hx₁
      obtain ⟨p₂, hp₂, heq⟩ := hx₂
      have hp_eq : p₁ = p₂ :=
        congrArg Subtype.val (φS.vertexEquiv.injective (Subtype.ext heq.symm))
      subst hp_eq
      have hi_eq : h₁.choose = h₂.choose := by
        by_contra hi_ne
        exact Set.disjoint_left.mp (hP'_disj hi_ne) hp₁ hp₂
      rw [← h₁.choose_spec, ← h₂.choose_spec, hi_eq]
    · obtain ⟨p₁, _, rfl⟩ := hx₁
      rw [mem_singleton_iff] at hx₂
      have hx_inter : (φH.vertexEquiv ⟨u₂, hu₂⟩).1 ∈ V(H') ∩ V(S') :=
        ⟨(φH.vertexEquiv ⟨u₂, hu₂⟩).2, hx₂ ▸ (φS.vertexEquiv ⟨p₁, Set.mem_univ _⟩).2⟩
      rw [hinter, mem_range] at hx_inter
      obtain ⟨i, hi⟩ := hx_inter
      have : v i = u₂ := congrArg Subtype.val (φH.vertexEquiv.injective (Subtype.ext hi))
      exact (h₂ ⟨i, this⟩).elim
    · obtain ⟨p₂, _, rfl⟩ := hx₂
      rw [mem_singleton_iff] at hx₁
      have hx_inter : (φH.vertexEquiv ⟨u₁, hu₁⟩).1 ∈ V(H') ∩ V(S') :=
        ⟨(φH.vertexEquiv ⟨u₁, hu₁⟩).2, hx₁ ▸ (φS.vertexEquiv ⟨p₂, Set.mem_univ _⟩).2⟩
      rw [hinter, mem_range] at hx_inter
      obtain ⟨i, hi⟩ := hx_inter
      have : v i = u₁ := congrArg Subtype.val (φH.vertexEquiv.injective (Subtype.ext hi))
      exact (h₁ ⟨i, this⟩).elim
    · rw [mem_singleton_iff] at hx₁ hx₂
      have heq := hx₁.symm.trans hx₂
      exact congrArg Subtype.val (φH.vertexEquiv.injective (Subtype.ext heq))
  have hZ_edge : ∀ ⦃e : β₂⦄ ⦃u w : α₂⦄, H.IsLink e u w →
      ∃ t : ι, (Y t ∩ V(Z u)).Nonempty ∧ (Y t ∩ V(Z w)).Nonempty := by
    intro e u w₀ hl
    have hl' : H'.IsLink (φH.edgeEquiv ⟨e, hl.edge_mem⟩).1
        (φH.vertexEquiv ⟨u, hl.left_mem⟩).1 (φH.vertexEquiv ⟨w₀, hl.right_mem⟩).1 :=
      (φH.isLink_iff ⟨e, hl.edge_mem⟩ ⟨u, hl.left_mem⟩ ⟨w₀, hl.right_mem⟩).mp hl
    obtain ⟨t, hut, hwt⟩ := hTD.edge_in_bag (hl'.mono hSep.1)
    exact ⟨t, ⟨_, hut, hφH_mem_U u hl.left_mem⟩, ⟨_, hwt, hφH_mem_U w₀ hl.right_mem⟩⟩
  have ⟨hTD_H, hw_H⟩ := isTreeDecomposition_of_connected_subgraphs hVG hTD Z
    (fun u hu ↦ (hZ_le_conn u hu).1) (fun u hu ↦ (hZ_le_conn u hu).2) hZ_disj hZ_edge
  refine ⟨fun t ↦ {u ∈ V(H) | (Y t ∩ V(Z u)).Nonempty}, t₀, hTD_H, hw_H w' hw,
    fun t u hu hut => ⟨hu, _, hut, hφH_mem_U u hu⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  refine ⟨hv i, ?_⟩
  obtain ⟨p, hpY₀, hpP'⟩ := hP'_Y₀ i
  refine ⟨(φS.vertexEquiv ⟨p, Set.mem_univ _⟩).1, hpY₀, ?_⟩
  change (φS.vertexEquiv ⟨p, Set.mem_univ _⟩).1 ∈ U (v i)
  dsimp [U]
  rw [dite_eq_left (hv i)]
  have hr_ex : ∃ i' : Fin r, v i' = v i := ⟨i, rfl⟩
  rw [dite_eq_left hr_ex]
  have hi_eq : hr_ex.choose = i := hv_inj hr_ex.choose_spec
  exact ⟨p, hi_eq.symm ▸ hpP', rfl⟩

/-- Graph Minors III, (3.8) (page 58):
"(3.8) *With $S, C_1, \dots, C_s$ as before, let $V(C_s) = \{u_1, \dots, u_r\}$. Let $H$ be another
graph, vertex-disjoint from $S$, and let $v_1, \dots, v_r$ be distinct vertices of $H$. Construct
$G$ by making the identifications $u_1 = v_1, \dots, u_r = v_r$. If $G$ has tree-width $\le w$,
then $H$ has a tree-decomposition $(T, \mathcal{X})$ where $\mathcal{X} = (X_t : t \in V(T))$ say,
of width $\le w$, such that $\{v_1, \dots, v_r\} \subseteq X_{t_0}$ for some $t_0 \in V(T)$.*" -/
theorem theorem_3_8_proof {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {r : ℕ} {G : Graph α₁ β₁} {H : Graph α₂ β₂} (hVG : V(G).Finite)
    (s : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s) (v : Fin r → α₂)
    (hId : IsCylinderIdentification G H s hs v) {w : ℕ} (htw : TreeWidthLE G w) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (X : ι → Set α₂) (t₀ : ι),
      IsTreeDecomposition H T X ∧ TreeDecompHasWidthLE X w ∧ Set.range v ⊆ X t₀ := by
  rw [treeWidthLE_iff_exists_isTreeDecomposition] at htw
  obtain ⟨ι, hfin, T, Y, hTD, hw⟩ := htw
  let _ : Fintype ι := hfin
  obtain ⟨hv_inj, hv, H', S', φH, φS, hSep, hinter, hident⟩ := hId
  obtain ⟨X, t₀, hX, hXw, -, hX₀⟩ :=
    theorem_3_8_strong hVG s hs hr v hv_inj hv φH φS hSep hinter hident hTD hw
  exact ⟨ι, hfin, T, X, t₀, hX, hXw, hX₀⟩

/-- Helper for `(3.9)`: one side of a sleeve union is isomorphic to a proper minor of `G`. -/
private lemma isIsoProperMinor_of_sleeve_side
    {α : Type u} {β : Type v} {α₁ : Type u₁} {β₁ : Type v₁}
    {r s : ℕ} {G H₁ H₂ : Graph α β} {G₁ : Graph α₁ β₁}
    (hs : 0 < s) (v : Fin r → α)
    (hSep : IsGraphSeparation G H₁ H₂)
    (_hv_inj : Function.Injective v)
    (hinter : V(H₁) ∩ V(H₂) = Set.range v)
    (hMinor : IsProperMinorWithMap (cylinderGraph r s) H₂ v
      (fun i ↦ (i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)))
    (hId : IsCylinderIdentification G₁ H₁ s hs v) :
    IsIsoProperMinor G₁ G := by
  classical
  let u_cyl : Fin r → Fin r × Fin s := fun i ↦ (i, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)
  obtain ⟨H₂', hH₂'_le, C₂, hC₂_sub, hnot_eq, φ_cyl, hmap⟩ := hMinor
  obtain ⟨_, hv_H₁, H₁', S₁', φH, φS, hSep₁, hinter₁, hident₁⟩ := hId
  have hH₂'_G : H₂' ≤ G := hH₂'_le.trans hSep.2.1
  let G' : Graph α β := subgraphUnion G H₁ H₂'
  have hG'_le : G' ≤ G := subgraphUnion_le hSep.1 hH₂'_G
  have hC₂_G' : C₂ ⊆ E(G') := by
    rw [edgeSet_subgraphUnion hSep.1 hH₂'_G]
    exact hC₂_sub.trans subset_union_right
  have hDisj_E : Disjoint E(H₁) E(H₂') :=
    hSep.2.2.2.2.mono_right hH₂'_le.edgeSet_mono
  let compRel (H : Graph α β) (x y : α) : Prop := ∃ e ∈ C₂, H.IsLink e x y
  let compSet (H : Graph α β) (x : α) : Set α := {y | Relation.ReflTransGen (compRel H) x y}
  have hV_contract : ∀ H : Graph α β, V(contract H C₂) = compSet H '' V(H) := by
    intro H; simp [contract, compSet, compRel]
  have hE_contract : ∀ H : Graph α β, E(contract H C₂) = E(H) \ C₂ := by
    intro H; simp [contract, Graph.edgeSet_deleteEdges, Graph.edgeSet_map]
  have hL_contract : ∀ (H : Graph α β) (e : β) (X Y : Set α),
      (contract H C₂).IsLink e X Y ↔
        e ∉ C₂ ∧ ∃ x y, H.IsLink e x y ∧ compSet H x = X ∧ compSet H y = Y := by
    intro H e X Y
    simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map, compSet, compRel, and_comm]
  have hG'_isLink : ∀ (e : β) (x y : α), G'.IsLink e x y ↔ H₁.IsLink e x y ∨ H₂'.IsLink e x y :=
    fun _ _ _ ↦ GM09.subgraphUnion_isLink hSep.1 hH₂'_G
  have hcompRel_eq : compRel G' = compRel H₂' := by
    ext x y
    dsimp [compRel]
    refine exists_congr fun e ↦ and_congr_right fun heC ↦ ?_
    rw [hG'_isLink]
    have he_not_H₁ : e ∉ E(H₁) :=
      fun he₁ ↦ Set.disjoint_left.mp hDisj_E he₁ (hC₂_sub heC)
    exact ⟨fun h ↦ h.resolve_left fun hl₁ ↦ he_not_H₁ hl₁.edge_mem, Or.inr⟩
  have hcompSet_eq : ∀ x : α, compSet G' x = compSet H₂' x := by
    intro x
    simp only [compSet, hcompRel_eq]
  have hcomp_symm : ∀ a b, Relation.ReflTransGen (compRel H₂') a b →
      Relation.ReflTransGen (compRel H₂') b a := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hst ih =>
      obtain ⟨e, heC, hl⟩ := hst
      exact Relation.ReflTransGen.head ⟨e, heC, hl.symm⟩ ih
  have hcomp_eq_of_mem : ∀ {x y : α}, y ∈ compSet H₂' x → compSet H₂' x = compSet H₂' y := by
    intro x y hxy
    ext z
    exact ⟨fun hxz ↦ (hcomp_symm x y hxy).trans hxz, fun hyz ↦ hxy.trans hyz⟩
  have hcomp_sub_H₂' : ∀ {x : α}, x ∈ V(H₂') → compSet H₂' x ⊆ V(H₂') := by
    intro x hx y hxy
    induction hxy with
    | refl => exact hx
    | tail _ hst _ => obtain ⟨_, _, hl⟩ := hst; exact hl.right_mem
  have hcomp_singleton_of_not_mem : ∀ {x : α}, x ∉ V(H₂') → compSet H₂' x = {x} := by
    intro x hx
    ext y
    simp only [compSet, mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun hxy ↦ ?_, fun h ↦ h ▸ .refl⟩
    induction hxy with
    | refl => rfl
    | tail _ hst ih =>
      subst ih
      obtain ⟨_, _, hl⟩ := hst
      exact (hx hl.left_mem).elim
  have hv_comp : ∀ i : Fin r,
      v i ∈ V(H₂') ∧ compSet H₂' (v i) = (φ_cyl.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).1 := by
    intro i
    obtain ⟨_, hvi_mem⟩ := hmap i
    have hZ_mem : (φ_cyl.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).1 ∈ compSet H₂' '' V(H₂') :=
      hV_contract H₂' ▸ (φ_cyl.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).2
    obtain ⟨w, hw, hw_eq⟩ := hZ_mem
    have hvi_comp : v i ∈ compSet H₂' w := by rw [hw_eq]; exact hvi_mem
    exact ⟨hcomp_sub_H₂' hw hvi_comp, (hcomp_eq_of_mem hvi_comp).symm.trans hw_eq⟩
  have hnot_eq_G' : ¬ (G' = G ∧ C₂ = ∅) := by
    rintro ⟨hG'_eq, hC₂_emp⟩
    refine hnot_eq ⟨?_, hC₂_emp⟩
    refine (Compatible.of_le_le hH₂'_le le_rfl).ext ?_ ?_
    · refine Subset.antisymm hH₂'_le.vertexSet_mono fun x hx₂ ↦ ?_
      have hxG : x ∈ V(G) := hSep.2.1.vertexSet_mono hx₂
      rw [← hG'_eq, vertexSet_subgraphUnion] at hxG
      rcases hxG with hx₁ | hx₂'
      · have hx_inter : x ∈ V(H₁) ∩ V(H₂) := ⟨hx₁, hx₂⟩
        rw [hinter, mem_range] at hx_inter
        obtain ⟨i, rfl⟩ := hx_inter
        exact (hv_comp i).1
      · exact hx₂'
    · refine Subset.antisymm hH₂'_le.edgeSet_mono fun e he₂ ↦ ?_
      have heG : e ∈ E(G) := hSep.2.1.edgeSet_mono he₂
      rw [← hG'_eq, edgeSet_subgraphUnion hSep.1 hH₂'_G] at heG
      rcases heG with he₁ | he₂'
      · exact (Set.disjoint_left.mp hSep.2.2.2.2 he₁ he₂).elim
      · exact he₂'
  refine ⟨G', hG'_le, C₂, hC₂_G', hnot_eq_G', ⟨?_⟩⟩
  have hu_H₁'_of_not_S₁' : ∀ {u : α₁}, u ∈ V(G₁) → u ∉ V(S₁') → u ∈ V(H₁') := by
    intro u hu huS
    rw [← hSep₁.2.2.1, mem_union] at hu
    exact hu.resolve_right huS
  let toV_set (u : α₁) (hu : u ∈ V(G₁)) : Set α :=
    if huS : u ∈ V(S₁') then
      (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u, huS⟩)).1
    else
      compSet H₂' (φH.vertexEquiv.symm ⟨u, hu_H₁'_of_not_S₁' hu huS⟩).1
  have htoV_S₁' : ∀ {u : α₁} (hu : u ∈ V(G₁)) (huS : u ∈ V(S₁')),
      toV_set u hu = (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u, huS⟩)).1 := by
    intro u _ huS
    dsimp [toV_set]
    rw [dite_eq_left huS]
  have htoV_H₁' : ∀ {u : α₁} (hu : u ∈ V(G₁)) (huH : u ∈ V(H₁')),
      toV_set u hu = compSet H₂' (φH.vertexEquiv.symm ⟨u, huH⟩).1 := by
    intro u hu huH
    dsimp [toV_set]
    split_ifs with huS
    · have hu_inter : u ∈ V(H₁') ∩ V(S₁') := ⟨huH, huS⟩
      rw [hinter₁, mem_range] at hu_inter
      obtain ⟨i, hi⟩ := hu_inter
      have hsymm_H : φH.vertexEquiv.symm ⟨u, huH⟩ = ⟨v i, hv_H₁ i⟩ := by
        apply φH.vertexEquiv.injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext hi.symm
      have hsymm_S : φS.vertexEquiv.symm ⟨u, huS⟩ = ⟨u_cyl i, Set.mem_univ _⟩ := by
        apply φS.vertexEquiv.injective
        rw [Equiv.apply_symm_apply]
        exact Subtype.ext (hi.symm.trans (hident₁ i).symm)
      have h1 := congrArg (fun p : V(cylinderGraph r s) ↦ (φ_cyl.vertexEquiv p).1) hsymm_S
      have h2 := congrArg (fun p : V(H₁) ↦ compSet H₂' p.1) hsymm_H
      exact h1.trans ((hv_comp i).2.symm.trans h2.symm)
    · rfl
  have htoV_mem : ∀ (u : α₁) (hu : u ∈ V(G₁)), toV_set u hu ∈ V(contract G' C₂) := by
    intro u hu
    rw [hV_contract G', mem_image]
    by_cases huS : u ∈ V(S₁')
    · rw [htoV_S₁' hu huS]
      have hmem : (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u, huS⟩)).1 ∈ compSet H₂' '' V(H₂') :=
        hV_contract H₂' ▸ (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u, huS⟩)).2
      obtain ⟨w, hw, hw_eq⟩ := hmem
      exact ⟨w, Or.inr hw, (hcompSet_eq w).trans hw_eq⟩
    · have huH := hu_H₁'_of_not_S₁' hu huS
      rw [htoV_H₁' hu huH]
      exact ⟨(φH.vertexEquiv.symm ⟨u, huH⟩).1, Or.inl (φH.vertexEquiv.symm ⟨u, huH⟩).2,
        hcompSet_eq _⟩
  have htoV_inj : ∀ {u₁ u₂ : α₁} (hu₁ : u₁ ∈ V(G₁)) (hu₂ : u₂ ∈ V(G₁)),
      toV_set u₁ hu₁ = toV_set u₂ hu₂ → u₁ = u₂ := by
    intro u₁ u₂ hu₁ hu₂ heq
    by_cases hu₁S : u₁ ∈ V(S₁') <;> by_cases hu₂S : u₂ ∈ V(S₁')
    · rw [htoV_S₁' hu₁ hu₁S, htoV_S₁' hu₂ hu₂S] at heq
      have h1 := φ_cyl.vertexEquiv.injective (Subtype.ext heq)
      have h2 := φS.vertexEquiv.symm.injective h1
      exact congrArg Subtype.val h2
    · exfalso
      have hu₂H := hu_H₁'_of_not_S₁' hu₂ hu₂S
      let x₂ := (φH.vertexEquiv.symm ⟨u₂, hu₂H⟩).1
      have hx₂_not_H₂' : x₂ ∉ V(H₂') := by
        intro hx₂_H₂'
        have hx₂_inter : x₂ ∈ V(H₁) ∩ V(H₂) :=
          ⟨(φH.vertexEquiv.symm ⟨u₂, hu₂H⟩).2, hH₂'_le.vertexSet_mono hx₂_H₂'⟩
        rw [hinter, mem_range] at hx₂_inter
        obtain ⟨i, hi⟩ := hx₂_inter
        have hu₂_eq : u₂ = (φH.vertexEquiv ⟨v i, hv_H₁ i⟩).1 := by
          have : ⟨x₂, (φH.vertexEquiv.symm ⟨u₂, hu₂H⟩).2⟩ = (⟨v i, hv_H₁ i⟩ : V(H₁)) :=
            Subtype.ext hi.symm
          have h := congrArg (fun p ↦ (φH.vertexEquiv p).1) this
          simpa [x₂] using h
        rw [hu₂_eq, ← hident₁ i] at hu₂S
        exact hu₂S (φS.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).2
      have hsub₁ : toV_set u₁ hu₁ ⊆ V(H₂') := by
        rw [htoV_S₁' hu₁ hu₁S]
        have hmem : (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u₁, hu₁S⟩)).1 ∈ compSet H₂' '' V(H₂') :=
          hV_contract H₂' ▸ (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u₁, hu₁S⟩)).2
        obtain ⟨w, hw, hw_eq⟩ := hmem
        exact hw_eq ▸ hcomp_sub_H₂' hw
      have hx₂_in : x₂ ∈ toV_set u₂ hu₂ := by
        rw [htoV_H₁' hu₂ hu₂H]
        exact Relation.ReflTransGen.refl
      exact hx₂_not_H₂' (hsub₁ (heq.symm ▸ hx₂_in))
    · exfalso
      have hu₁H := hu_H₁'_of_not_S₁' hu₁ hu₁S
      let x₁ := (φH.vertexEquiv.symm ⟨u₁, hu₁H⟩).1
      have hx₁_not_H₂' : x₁ ∉ V(H₂') := by
        intro hx₁_H₂'
        have hx₁_inter : x₁ ∈ V(H₁) ∩ V(H₂) :=
          ⟨(φH.vertexEquiv.symm ⟨u₁, hu₁H⟩).2, hH₂'_le.vertexSet_mono hx₁_H₂'⟩
        rw [hinter, mem_range] at hx₁_inter
        obtain ⟨i, hi⟩ := hx₁_inter
        have hu₁_eq : u₁ = (φH.vertexEquiv ⟨v i, hv_H₁ i⟩).1 := by
          have : ⟨x₁, (φH.vertexEquiv.symm ⟨u₁, hu₁H⟩).2⟩ = (⟨v i, hv_H₁ i⟩ : V(H₁)) :=
            Subtype.ext hi.symm
          have h := congrArg (fun p ↦ (φH.vertexEquiv p).1) this
          simpa [x₁] using h
        rw [hu₁_eq, ← hident₁ i] at hu₁S
        exact hu₁S (φS.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).2
      have hsub₂ : toV_set u₂ hu₂ ⊆ V(H₂') := by
        rw [htoV_S₁' hu₂ hu₂S]
        have hmem : (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u₂, hu₂S⟩)).1 ∈ compSet H₂' '' V(H₂') :=
          hV_contract H₂' ▸ (φ_cyl.vertexEquiv (φS.vertexEquiv.symm ⟨u₂, hu₂S⟩)).2
        obtain ⟨w, hw, hw_eq⟩ := hmem
        exact hw_eq ▸ hcomp_sub_H₂' hw
      have hx₁_in : x₁ ∈ toV_set u₁ hu₁ := by
        rw [htoV_H₁' hu₁ hu₁H]
        exact Relation.ReflTransGen.refl
      exact hx₁_not_H₂' (hsub₂ (heq ▸ hx₁_in))
    · have hu₁H := hu_H₁'_of_not_S₁' hu₁ hu₁S
      have hu₂H := hu_H₁'_of_not_S₁' hu₂ hu₂S
      let x₁ := (φH.vertexEquiv.symm ⟨u₁, hu₁H⟩).1
      let x₂ := (φH.vertexEquiv.symm ⟨u₂, hu₂H⟩).1
      have hx₁_not_H₂' : x₁ ∉ V(H₂') := by
        intro hx₁_H₂'
        have hx₁_inter : x₁ ∈ V(H₁) ∩ V(H₂) :=
          ⟨(φH.vertexEquiv.symm ⟨u₁, hu₁H⟩).2, hH₂'_le.vertexSet_mono hx₁_H₂'⟩
        rw [hinter, mem_range] at hx₁_inter
        obtain ⟨i, hi⟩ := hx₁_inter
        have hu₁_eq : u₁ = (φH.vertexEquiv ⟨v i, hv_H₁ i⟩).1 := by
          have : ⟨x₁, (φH.vertexEquiv.symm ⟨u₁, hu₁H⟩).2⟩ = (⟨v i, hv_H₁ i⟩ : V(H₁)) :=
            Subtype.ext hi.symm
          have h := congrArg (fun p ↦ (φH.vertexEquiv p).1) this
          simpa [x₁] using h
        rw [hu₁_eq, ← hident₁ i] at hu₁S
        exact hu₁S (φS.vertexEquiv ⟨u_cyl i, Set.mem_univ _⟩).2
      rw [htoV_H₁' hu₁ hu₁H, htoV_H₁' hu₂ hu₂H, hcomp_singleton_of_not_mem hx₁_not_H₂'] at heq
      have hx₁_mem : x₁ ∈ compSet H₂' x₂ := heq ▸ mem_singleton x₁
      have hx_eq : x₁ = x₂ := by
        by_contra hne
        have hx₂_not_H₂' : x₂ ∉ V(H₂') :=
          fun hx₂ ↦ hx₁_not_H₂' (hcomp_sub_H₂' hx₂ hx₁_mem)
        rw [hcomp_singleton_of_not_mem hx₂_not_H₂', mem_singleton_iff] at hx₁_mem
        exact hne hx₁_mem
      have hsymm := φH.vertexEquiv.symm.injective (Subtype.ext hx_eq)
      exact congrArg Subtype.val hsymm
  have htoV_surj : Function.Surjective
      (fun u : V(G₁) ↦ (⟨toV_set u.1 u.2, htoV_mem u.1 u.2⟩ : V(contract G' C₂))) := by
    rintro ⟨Z, hZ⟩
    have hZ' : Z ∈ compSet G' '' V(G') := hV_contract G' ▸ hZ
    obtain ⟨w, hw, rfl⟩ := hZ'
    rcases hw with hw₁ | hw₂
    · let u := (φH.vertexEquiv ⟨w, hw₁⟩).1
      have huH : u ∈ V(H₁') := (φH.vertexEquiv ⟨w, hw₁⟩).2
      have huG₁ : u ∈ V(G₁) := hSep₁.1.vertexSet_mono huH
      refine ⟨⟨u, huG₁⟩, Subtype.ext ?_⟩
      dsimp
      rw [htoV_H₁' huG₁ huH, hcompSet_eq]
      simp [u]
    · have hZ₂ : compSet H₂' w ∈ V(contract H₂' C₂) := by
        rw [hV_contract H₂', mem_image]
        exact ⟨w, hw₂, rfl⟩
      let p := φ_cyl.vertexEquiv.symm ⟨compSet H₂' w, hZ₂⟩
      let u := (φS.vertexEquiv p).1
      have huS : u ∈ V(S₁') := (φS.vertexEquiv p).2
      have huG₁ : u ∈ V(G₁) := hSep₁.2.1.vertexSet_mono huS
      refine ⟨⟨u, huG₁⟩, Subtype.ext ?_⟩
      dsimp
      rw [htoV_S₁' huG₁ huS, hcompSet_eq]
      change (φ_cyl.vertexEquiv (φS.vertexEquiv.symm (φS.vertexEquiv p))).1 = compSet H₂' w
      rw [Equiv.symm_apply_apply]
      change (φ_cyl.vertexEquiv (φ_cyl.vertexEquiv.symm ⟨compSet H₂' w, hZ₂⟩)).1 = compSet H₂' w
      rw [Equiv.apply_symm_apply]
  let vEquiv : V(G₁) ≃ V(contract G' C₂) :=
    Equiv.ofBijective (fun u ↦ ⟨toV_set u.1 u.2, htoV_mem u.1 u.2⟩)
      ⟨fun u₁ u₂ h ↦ Subtype.ext (htoV_inj u₁.2 u₂.2 (Subtype.ext_iff.mp h)), htoV_surj⟩
  have he_H₁'_of_not_S₁' : ∀ {e : β₁}, e ∈ E(G₁) → e ∉ E(S₁') → e ∈ E(H₁') := by
    intro e he heS
    rw [← hSep₁.2.2.2.1, mem_union] at he
    exact he.resolve_right heS
  let toE_val (e : β₁) (he : e ∈ E(G₁)) : β :=
    if heS : e ∈ E(S₁') then
      (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e, heS⟩)).1
    else
      (φH.edgeEquiv.symm ⟨e, he_H₁'_of_not_S₁' he heS⟩).1
  have htoE_S₁' : ∀ {e : β₁} (he : e ∈ E(G₁)) (heS : e ∈ E(S₁')),
      toE_val e he = (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e, heS⟩)).1 := by
    intro e _ heS
    dsimp [toE_val]
    rw [dite_eq_left heS]
  have htoE_H₁' : ∀ {e : β₁} (he : e ∈ E(G₁)) (heH : e ∈ E(H₁')),
      toE_val e he = (φH.edgeEquiv.symm ⟨e, heH⟩).1 := by
    intro e _ heH
    have heS : e ∉ E(S₁') := Set.disjoint_left.mp hSep₁.2.2.2.2 heH
    dsimp [toE_val]
    rw [dite_eq_right heS]
  have htoE_mem : ∀ (e : β₁) (he : e ∈ E(G₁)), toE_val e he ∈ E(contract G' C₂) := by
    intro e he
    rw [hE_contract G', edgeSet_subgraphUnion hSep.1 hH₂'_G, mem_sdiff, mem_union]
    by_cases heS : e ∈ E(S₁')
    · rw [htoE_S₁' he heS]
      have hmem : (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e, heS⟩)).1 ∈ E(H₂') \ C₂ :=
        hE_contract H₂' ▸ (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e, heS⟩)).2
      exact ⟨Or.inr hmem.1, hmem.2⟩
    · have heH := he_H₁'_of_not_S₁' he heS
      rw [htoE_H₁' he heH]
      have hmem := (φH.edgeEquiv.symm ⟨e, heH⟩).2
      exact ⟨Or.inl hmem, fun heC ↦ Set.disjoint_left.mp hDisj_E hmem (hC₂_sub heC)⟩
  have htoE_inj : ∀ {e₁ e₂ : β₁} (he₁ : e₁ ∈ E(G₁)) (he₂ : e₂ ∈ E(G₁)),
      toE_val e₁ he₁ = toE_val e₂ he₂ → e₁ = e₂ := by
    intro e₁ e₂ he₁ he₂ heq
    by_cases he₁S : e₁ ∈ E(S₁') <;> by_cases he₂S : e₂ ∈ E(S₁')
    · rw [htoE_S₁' he₁ he₁S, htoE_S₁' he₂ he₂S] at heq
      have h1 := φ_cyl.edgeEquiv.injective (Subtype.ext heq)
      have h2 := φS.edgeEquiv.symm.injective h1
      exact congrArg Subtype.val h2
    · exfalso
      have he₂H := he_H₁'_of_not_S₁' he₂ he₂S
      rw [htoE_S₁' he₁ he₁S, htoE_H₁' he₂ he₂H] at heq
      have hmem₁ : (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e₁, he₁S⟩)).1 ∈ E(H₂') \ C₂ :=
        hE_contract H₂' ▸ (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e₁, he₁S⟩)).2
      have hmem₂ := (φH.edgeEquiv.symm ⟨e₂, he₂H⟩).2
      exact Set.disjoint_left.mp hDisj_E (heq ▸ hmem₂) hmem₁.1
    · exfalso
      have he₁H := he_H₁'_of_not_S₁' he₁ he₁S
      rw [htoE_H₁' he₁ he₁H, htoE_S₁' he₂ he₂S] at heq
      have hmem₂ : (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e₂, he₂S⟩)).1 ∈ E(H₂') \ C₂ :=
        hE_contract H₂' ▸ (φ_cyl.edgeEquiv (φS.edgeEquiv.symm ⟨e₂, he₂S⟩)).2
      have hmem₁ := (φH.edgeEquiv.symm ⟨e₁, he₁H⟩).2
      exact Set.disjoint_left.mp hDisj_E (heq.symm ▸ hmem₁) hmem₂.1
    · have he₁H := he_H₁'_of_not_S₁' he₁ he₁S
      have he₂H := he_H₁'_of_not_S₁' he₂ he₂S
      rw [htoE_H₁' he₁ he₁H, htoE_H₁' he₂ he₂H] at heq
      have h1 := φH.edgeEquiv.symm.injective (Subtype.ext heq)
      exact congrArg Subtype.val h1
  have htoE_surj : Function.Surjective
      (fun e : E(G₁) ↦ (⟨toE_val e.1 e.2, htoE_mem e.1 e.2⟩ : E(contract G' C₂))) := by
    rintro ⟨e₀, he₀⟩
    have he₀' : e₀ ∈ (E(H₁) ∪ E(H₂')) \ C₂ := by
      rwa [hE_contract G', edgeSet_subgraphUnion hSep.1 hH₂'_G] at he₀
    rcases he₀'.1 with he₁ | he₂
    · let e := (φH.edgeEquiv ⟨e₀, he₁⟩).1
      have heH : e ∈ E(H₁') := (φH.edgeEquiv ⟨e₀, he₁⟩).2
      have heG₁ : e ∈ E(G₁) := hSep₁.1.edgeSet_mono heH
      refine ⟨⟨e, heG₁⟩, Subtype.ext ?_⟩
      dsimp
      rw [htoE_H₁' heG₁ heH]
      simp [e]
    · have he_c : e₀ ∈ E(contract H₂' C₂) := by
        rw [hE_contract H₂', mem_sdiff]
        exact ⟨he₂, he₀'.2⟩
      let e_cyl := φ_cyl.edgeEquiv.symm ⟨e₀, he_c⟩
      let e := (φS.edgeEquiv e_cyl).1
      have heS : e ∈ E(S₁') := (φS.edgeEquiv e_cyl).2
      have heG₁ : e ∈ E(G₁) := hSep₁.2.1.edgeSet_mono heS
      refine ⟨⟨e, heG₁⟩, Subtype.ext ?_⟩
      dsimp
      rw [htoE_S₁' heG₁ heS]
      change (φ_cyl.edgeEquiv (φS.edgeEquiv.symm (φS.edgeEquiv e_cyl))).1 = e₀
      rw [Equiv.symm_apply_apply]
      change (φ_cyl.edgeEquiv (φ_cyl.edgeEquiv.symm ⟨e₀, he_c⟩)).1 = e₀
      rw [Equiv.apply_symm_apply]
  let eEquiv : E(G₁) ≃ E(contract G' C₂) :=
    Equiv.ofBijective (fun e ↦ ⟨toE_val e.1 e.2, htoE_mem e.1 e.2⟩)
      ⟨fun e₁ e₂ h ↦ Subtype.ext (htoE_inj e₁.2 e₂.2 (Subtype.ext_iff.mp h)), htoE_surj⟩
  refine
    { vertexEquiv := vEquiv
      edgeEquiv := eEquiv
      isLink_iff := fun ⟨e, he⟩ ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩ ↦ ?_ }
  change G₁.IsLink e u₁ u₂ ↔
    (contract G' C₂).IsLink (toE_val e he) (toV_set u₁ hu₁) (toV_set u₂ hu₂)
  by_cases heS : e ∈ E(S₁')
  · rw [htoE_S₁' he heS]
    have hG₁_iff_S₁' : G₁.IsLink e u₁ u₂ ↔ S₁'.IsLink e u₁ u₂ :=
      (hSep₁.2.1.isLink_iff heS).symm
    rw [hG₁_iff_S₁']
    let e_cyl := φS.edgeEquiv.symm ⟨e, heS⟩
    have he_c_mem : (φ_cyl.edgeEquiv e_cyl).1 ∈ E(H₂') \ C₂ :=
      hE_contract H₂' ▸ (φ_cyl.edgeEquiv e_cyl).2
    have hnot_H₁ : (φ_cyl.edgeEquiv e_cyl).1 ∉ E(H₁) :=
      fun h₁ ↦ Set.disjoint_left.mp hDisj_E h₁ he_c_mem.1
    have hcontract_iff :
        (contract G' C₂).IsLink (φ_cyl.edgeEquiv e_cyl).1 (toV_set u₁ hu₁) (toV_set u₂ hu₂) ↔
        (contract H₂' C₂).IsLink (φ_cyl.edgeEquiv e_cyl).1 (toV_set u₁ hu₁) (toV_set u₂ hu₂) := by
      rw [hL_contract G', hL_contract H₂']
      refine and_congr_right fun _ ↦ exists₂_congr fun x y ↦ ?_
      rw [hG'_isLink, hcompSet_eq x, hcompSet_eq y]
      exact and_congr_left fun _ ↦
        ⟨fun h ↦ h.resolve_left fun hl₁ ↦ hnot_H₁ hl₁.edge_mem, Or.inr⟩
    rw [hcontract_iff]
    constructor
    · intro hlS
      have hu₁S : u₁ ∈ V(S₁') := hlS.left_mem
      have hu₂S : u₂ ∈ V(S₁') := hlS.right_mem
      rw [htoV_S₁' hu₁ hu₁S, htoV_S₁' hu₂ hu₂S]
      have hl_cyl : (cylinderGraph r s).IsLink e_cyl.1
          (φS.vertexEquiv.symm ⟨u₁, hu₁S⟩).1 (φS.vertexEquiv.symm ⟨u₂, hu₂S⟩).1 := by
        have hlS_eq : S₁'.IsLink (φS.edgeEquiv e_cyl).1
            (φS.vertexEquiv (φS.vertexEquiv.symm ⟨u₁, hu₁S⟩)).1
            (φS.vertexEquiv (φS.vertexEquiv.symm ⟨u₂, hu₂S⟩)).1 := by
          simp only [e_cyl, Equiv.apply_symm_apply]
          exact hlS
        exact (φS.isLink_iff e_cyl (φS.vertexEquiv.symm ⟨u₁, hu₁S⟩)
          (φS.vertexEquiv.symm ⟨u₂, hu₂S⟩)).mpr hlS_eq
      exact (φ_cyl.isLink_iff e_cyl (φS.vertexEquiv.symm ⟨u₁, hu₁S⟩)
        (φS.vertexEquiv.symm ⟨u₂, hu₂S⟩)).mp hl_cyl
    · intro hl_c
      obtain ⟨p₁, hp₁⟩ := φ_cyl.vertexEquiv.surjective ⟨toV_set u₁ hu₁, hl_c.left_mem⟩
      obtain ⟨p₂, hp₂⟩ := φ_cyl.vertexEquiv.surjective ⟨toV_set u₂ hu₂, hl_c.right_mem⟩
      have hl_cyl : (cylinderGraph r s).IsLink e_cyl.1 p₁.1 p₂.1 := by
        have h := (φ_cyl.isLink_iff e_cyl p₁ p₂).mpr
        rw [hp₁, hp₂] at h
        exact h hl_c
      have hlS : S₁'.IsLink e (φS.vertexEquiv p₁).1 (φS.vertexEquiv p₂).1 := by
        have h := (φS.isLink_iff e_cyl p₁ p₂).mp hl_cyl
        simpa [e_cyl] using h
      have hu₁_eq : u₁ = (φS.vertexEquiv p₁).1 := by
        have hp₁G₁ : (φS.vertexEquiv p₁).1 ∈ V(G₁) :=
          hSep₁.2.1.vertexSet_mono (φS.vertexEquiv p₁).2
        apply htoV_inj hu₁ hp₁G₁
        rw [htoV_S₁' hp₁G₁ (φS.vertexEquiv p₁).2, Equiv.symm_apply_apply]
        exact (congrArg Subtype.val hp₁).symm
      have hu₂_eq : u₂ = (φS.vertexEquiv p₂).1 := by
        have hp₂G₁ : (φS.vertexEquiv p₂).1 ∈ V(G₁) :=
          hSep₁.2.1.vertexSet_mono (φS.vertexEquiv p₂).2
        apply htoV_inj hu₂ hp₂G₁
        rw [htoV_S₁' hp₂G₁ (φS.vertexEquiv p₂).2, Equiv.symm_apply_apply]
        exact (congrArg Subtype.val hp₂).symm
      exact hu₁_eq.symm ▸ hu₂_eq.symm ▸ hlS
  · have heH := he_H₁'_of_not_S₁' he heS
    rw [htoE_H₁' he heH]
    have hG₁_iff_H₁' : G₁.IsLink e u₁ u₂ ↔ H₁'.IsLink e u₁ u₂ :=
      (hSep₁.1.isLink_iff heH).symm
    rw [hG₁_iff_H₁']
    let e₀ := φH.edgeEquiv.symm ⟨e, heH⟩
    have he₀_not_H₂' : e₀.1 ∉ E(H₂') :=
      fun h₂ ↦ Set.disjoint_left.mp hDisj_E e₀.2 h₂
    have he₀_not_C₂ : e₀.1 ∉ C₂ := fun hc ↦ he₀_not_H₂' (hC₂_sub hc)
    rw [hL_contract G']
    constructor
    · intro hlH'
      have hu₁H : u₁ ∈ V(H₁') := hlH'.left_mem
      have hu₂H : u₂ ∈ V(H₁') := hlH'.right_mem
      rw [htoV_H₁' hu₁ hu₁H, htoV_H₁' hu₂ hu₂H]
      have hlH : H₁.IsLink e₀.1
          (φH.vertexEquiv.symm ⟨u₁, hu₁H⟩).1 (φH.vertexEquiv.symm ⟨u₂, hu₂H⟩).1 := by
        have hlH'_eq : H₁'.IsLink (φH.edgeEquiv e₀).1
            (φH.vertexEquiv (φH.vertexEquiv.symm ⟨u₁, hu₁H⟩)).1
            (φH.vertexEquiv (φH.vertexEquiv.symm ⟨u₂, hu₂H⟩)).1 := by
          simp only [e₀, Equiv.apply_symm_apply]
          exact hlH'
        exact (φH.isLink_iff e₀ (φH.vertexEquiv.symm ⟨u₁, hu₁H⟩)
          (φH.vertexEquiv.symm ⟨u₂, hu₂H⟩)).mpr hlH'_eq
      refine ⟨he₀_not_C₂, _, _, (hG'_isLink _ _ _).mpr (Or.inl hlH), ?_, ?_⟩
      · exact hcompSet_eq _
      · exact hcompSet_eq _
    · rintro ⟨_, x, y, hlG', hx_eq, hy_eq⟩
      have hlH : H₁.IsLink e₀.1 x y :=
        ((hG'_isLink _ _ _).mp hlG').resolve_right fun hl₂ ↦ he₀_not_H₂' hl₂.edge_mem
      have hlH' : H₁'.IsLink e
          (φH.vertexEquiv ⟨x, hlH.left_mem⟩).1 (φH.vertexEquiv ⟨y, hlH.right_mem⟩).1 := by
        have h := (φH.isLink_iff e₀ ⟨x, hlH.left_mem⟩ ⟨y, hlH.right_mem⟩).mp hlH
        simpa [e₀] using h
      have hu₁_eq : u₁ = (φH.vertexEquiv ⟨x, hlH.left_mem⟩).1 := by
        have hu₁' : (φH.vertexEquiv ⟨x, hlH.left_mem⟩).1 ∈ V(G₁) :=
          hSep₁.1.vertexSet_mono (φH.vertexEquiv ⟨x, hlH.left_mem⟩).2
        apply htoV_inj hu₁ hu₁'
        rw [htoV_H₁' hu₁' (φH.vertexEquiv ⟨x, hlH.left_mem⟩).2, Equiv.symm_apply_apply]
        exact hx_eq.symm.trans (hcompSet_eq x)
      have hu₂_eq : u₂ = (φH.vertexEquiv ⟨y, hlH.right_mem⟩).1 := by
        have hu₂' : (φH.vertexEquiv ⟨y, hlH.right_mem⟩).1 ∈ V(G₁) :=
          hSep₁.1.vertexSet_mono (φH.vertexEquiv ⟨y, hlH.right_mem⟩).2
        apply htoV_inj hu₂ hu₂'
        rw [htoV_H₁' hu₂' (φH.vertexEquiv ⟨y, hlH.right_mem⟩).2, Equiv.symm_apply_apply]
        exact hy_eq.symm.trans (hcompSet_eq y)
      exact hu₁_eq.symm ▸ hu₂_eq.symm ▸ hlH'

/-- Graph Minors III, (3.9) (page 59):
"(3.9) *If $G$ is the sleeve union of $G_1, G_2$ then $G_1, G_2$ are both isomorphic to proper
minors of $G$.*" -/
theorem theorem_3_9_proof {α : Type u} {β : Type v} {α₁ : Type u₁} {β₁ : Type v₁}
    {α₂ : Type u₂} {β₂ : Type v₂}
    {G : Graph α β} {G₁ : Graph α₁ β₁} {G₂ : Graph α₂ β₂}
    (hSU : IsSleeveUnion G G₁ G₂) :
    IsIsoProperMinor G₁ G ∧ IsIsoProperMinor G₂ G := by
  obtain ⟨H₁, H₂, r, v, hSep, hv_inj, hinter, hMinor₁, hMinor₂, hId₁, hId₂⟩ := hSU
  let s : ℕ := max 1 ((r + 1) / 2)
  have hs : 0 < s := Nat.le_max_left 1 ((r + 1) / 2)
  exact ⟨isIsoProperMinor_of_sleeve_side hs v hSep hv_inj hinter hMinor₁ hId₁,
    isIsoProperMinor_of_sleeve_side hs v (IsGraphSeparation.symm hSep) hv_inj
      (inter_comm V(H₂) V(H₁) ▸ hinter) hMinor₂ hId₂⟩

/-! ## Gluing two trees `T₁` and `T₂` along a bridge `(Sum.inl t₁, Sum.inr t₂)` for (3.10) -/

/-- The tree on `ι₁ ⊕ ι₂` formed from `T₁ : SimpleGraph ι₁` and `T₂ : SimpleGraph ι₂` by adding an
edge joining `Sum.inl t₁` and `Sum.inr t₂` (Graph Minors III, proof of `(3.10)`, page 59). -/
private def sumBridgeTree {ι₁ ι₂ : Type*} (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂)
    (t₁ : ι₁) (t₂ : ι₂) : SimpleGraph (ι₁ ⊕ ι₂) where
  Adj p q :=
    match p, q with
    | Sum.inl s₁, Sum.inl s₂ => T₁.Adj s₁ s₂
    | Sum.inr s₁, Sum.inr s₂ => T₂.Adj s₁ s₂
    | Sum.inl s₁, Sum.inr s₂ => s₁ = t₁ ∧ s₂ = t₂
    | Sum.inr s₂, Sum.inl s₁ => s₁ = t₁ ∧ s₂ = t₂
  symm := ⟨fun p q h ↦ by
    cases p <;> cases q
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨fun p h ↦ by
    cases p
    · exact T₁.loopless.irrefl _ h
    · exact T₂.loopless.irrefl _ h⟩

private theorem sumBridgeTree_adj_bridge_left {ι₁ ι₂ : Type*}
    (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂) (t₁ : ι₁) (t₂ : ι₂) :
    (sumBridgeTree T₁ T₂ t₁ t₂).Adj (Sum.inl t₁) (Sum.inr t₂) :=
  ⟨rfl, rfl⟩

private theorem sumBridgeTree_adj_bridge_right {ι₁ ι₂ : Type*}
    (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂) (t₁ : ι₁) (t₂ : ι₂) :
    (sumBridgeTree T₁ T₂ t₁ t₂).Adj (Sum.inr t₂) (Sum.inl t₁) :=
  ⟨rfl, rfl⟩

private abbrev embedInlHom {ι₁ ι₂ : Type*} (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂)
    (t₁ : ι₁) (t₂ : ι₂) : T₁ →g sumBridgeTree T₁ T₂ t₁ t₂ where
  toFun := Sum.inl
  map_rel' h := h

private abbrev embedInrHom {ι₁ ι₂ : Type*} (T₁ : SimpleGraph ι₁) (T₂ : SimpleGraph ι₂)
    (t₁ : ι₁) (t₂ : ι₂) : T₂ →g sumBridgeTree T₁ T₂ t₁ t₂ where
  toFun := Sum.inr
  map_rel' h := h

private noncomputable def sumBridgePath {ι₁ ι₂ : Type*} {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    (hT₁ : T₁.IsTree) (hT₂ : T₂.IsTree) (t₁ : ι₁) (t₂ : ι₂) :
    ∀ u v : ι₁ ⊕ ι₂, (sumBridgeTree T₁ T₂ t₁ t₂).Walk u v
  | Sum.inl s₁, Sum.inl s₂ =>
    (treePath hT₁ s₁ s₂).map (embedInlHom T₁ T₂ t₁ t₂)
  | Sum.inr s₁, Sum.inr s₂ =>
    (treePath hT₂ s₁ s₂).map (embedInrHom T₁ T₂ t₁ t₂)
  | Sum.inl s₁, Sum.inr s₂ =>
    ((treePath hT₁ s₁ t₁).map (embedInlHom T₁ T₂ t₁ t₂)).append
      (Walk.cons (sumBridgeTree_adj_bridge_left T₁ T₂ t₁ t₂)
        ((treePath hT₂ t₂ s₂).map (embedInrHom T₁ T₂ t₁ t₂)))
  | Sum.inr s₁, Sum.inl s₂ =>
    ((treePath hT₂ s₁ t₂).map (embedInrHom T₁ T₂ t₁ t₂)).append
      (Walk.cons (sumBridgeTree_adj_bridge_right T₁ T₂ t₁ t₂)
        ((treePath hT₁ t₁ s₂).map (embedInlHom T₁ T₂ t₁ t₂)))

private lemma sumBridgePath_isPath {ι₁ ι₂ : Type*} {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    (hT₁ : T₁.IsTree) (hT₂ : T₂.IsTree) (t₁ : ι₁) (t₂ : ι₂)
    (u v : ι₁ ⊕ ι₂) : (sumBridgePath hT₁ hT₂ t₁ t₂ u v).IsPath := by
  rcases u with s₁ | s₁ <;> rcases v with s₂ | s₂
  · exact (treePath_isPath hT₁ s₁ s₂).map Sum.inl_injective
  · dsimp [sumBridgePath]
    have hp1 := (treePath_isPath hT₁ s₁ t₁).map (f := embedInlHom T₁ T₂ t₁ t₂) Sum.inl_injective
    have hp2 := (treePath_isPath hT₂ t₂ s₂).map (f := embedInrHom T₁ T₂ t₁ t₂) Sum.inr_injective
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons, List.nodup_append']
    refine ⟨hp1.support_nodup, hp2.support_nodup, fun x hx1 hx2 ↦ ?_⟩
    rw [Walk.support_map, List.mem_map] at hx1 hx2
    obtain ⟨_, _, rfl⟩ := hx1
    obtain ⟨_, _, heq⟩ := hx2
    cases heq
  · dsimp [sumBridgePath]
    have hp1 := (treePath_isPath hT₂ s₁ t₂).map (f := embedInrHom T₁ T₂ t₁ t₂) Sum.inr_injective
    have hp2 := (treePath_isPath hT₁ t₁ s₂).map (f := embedInlHom T₁ T₂ t₁ t₂) Sum.inl_injective
    rw [Walk.isPath_def, Walk.support_append, Walk.support_cons, List.tail_cons, List.nodup_append']
    refine ⟨hp1.support_nodup, hp2.support_nodup, fun x hx1 hx2 ↦ ?_⟩
    rw [Walk.support_map, List.mem_map] at hx1 hx2
    obtain ⟨_, _, rfl⟩ := hx1
    obtain ⟨_, _, heq⟩ := hx2
    cases heq
  · exact (treePath_isPath hT₂ s₁ s₂).map Sum.inr_injective

private lemma sumDisjoint_isAcyclic {ι₁ ι₂ : Type*} {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    (hT₁ : T₁.IsAcyclic) (hT₂ : T₂.IsAcyclic) :
    (T₁.map Function.Embedding.inl ⊔ T₂.map Function.Embedding.inr).IsAcyclic := by
  let G₀ := T₁.map Function.Embedding.inl ⊔ T₂.map Function.Embedding.inr
  have hwalk_inl : ∀ {u v : ι₁ ⊕ ι₂} (w : G₀.Walk u v) (s₁ : ι₁),
      u = Sum.inl s₁ →
      ∃ s₂ : ι₁, v = Sum.inl s₂ ∧ ∃ w₁ : T₁.Walk s₁ s₂,
        w.support = w₁.support.map Sum.inl := by
    intro u v w
    induction w with
    | nil =>
      intro s₁ hu
      subst hu
      exact ⟨s₁, rfl, .nil, rfl⟩
    | @cons a b c hadj p ih =>
      intro s₁ ha
      subst ha
      rcases hadj with ⟨_, x, y, hxy, hax, hby⟩ | ⟨_, x, y, _, hax, _⟩
      · cases Sum.inl.inj hax
        subst hby
        obtain ⟨s₂, rfl, w₁, hw₁⟩ := ih y rfl
        exact ⟨s₂, rfl, .cons hxy w₁, by simp [hw₁]⟩
      · cases hax
  have hwalk_inr : ∀ {u v : ι₁ ⊕ ι₂} (w : G₀.Walk u v) (s₁ : ι₂),
      u = Sum.inr s₁ →
      ∃ s₂ : ι₂, v = Sum.inr s₂ ∧ ∃ w₂ : T₂.Walk s₁ s₂,
        w.support = w₂.support.map Sum.inr := by
    intro u v w
    induction w with
    | nil =>
      intro s₁ hu
      subst hu
      exact ⟨s₁, rfl, .nil, rfl⟩
    | @cons a b c hadj p ih =>
      intro s₁ ha
      subst ha
      rcases hadj with ⟨_, x, y, _, hax, _⟩ | ⟨_, x, y, hxy, hax, hby⟩
      · cases hax
      · cases Sum.inr.inj hax
        subst hby
        obtain ⟨s₂, rfl, w₂, hw₂⟩ := ih y rfl
        exact ⟨s₂, rfl, .cons hxy w₂, by simp [hw₂]⟩
  rw [isAcyclic_iff_subsingleton_path]
  intro u v
  refine ⟨fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ Subtype.ext ?_⟩
  cases u with
  | inl s₁ =>
    obtain ⟨s₂, rfl, p₁, hp₁⟩ := hwalk_inl p s₁ rfl
    obtain ⟨_, hveq, q₁, hq₁⟩ := hwalk_inl q s₁ rfl
    cases Sum.inl.inj hveq
    have hp₁_path : p₁.IsPath := by
      rw [Walk.isPath_def]
      have h := hp.support_nodup
      rw [hp₁] at h
      exact h.of_map _
    have hq₁_path : q₁.IsPath := by
      rw [Walk.isPath_def]
      have h := hq.support_nodup
      rw [hq₁] at h
      exact h.of_map _
    have heq : p₁ = q₁ :=
      Subtype.ext_iff.mp ((hT₁.subsingleton_path s₁ s₂).elim ⟨p₁, hp₁_path⟩ ⟨q₁, hq₁_path⟩)
    apply Walk.ext_support
    rw [hp₁, hq₁, heq]
  | inr s₁ =>
    obtain ⟨s₂, rfl, p₂, hp₂⟩ := hwalk_inr p s₁ rfl
    obtain ⟨_, hveq, q₂, hq₂⟩ := hwalk_inr q s₁ rfl
    cases Sum.inr.inj hveq
    have hp₂_path : p₂.IsPath := by
      rw [Walk.isPath_def]
      have h := hp.support_nodup
      rw [hp₂] at h
      exact h.of_map _
    have hq₂_path : q₂.IsPath := by
      rw [Walk.isPath_def]
      have h := hq.support_nodup
      rw [hq₂] at h
      exact h.of_map _
    have heq : p₂ = q₂ :=
      Subtype.ext_iff.mp ((hT₂.subsingleton_path s₁ s₂).elim ⟨p₂, hp₂_path⟩ ⟨q₂, hq₂_path⟩)
    apply Walk.ext_support
    rw [hp₂, hq₂, heq]

private lemma sumBridgeTree_isTree {ι₁ ι₂ : Type*} {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    (hT₁ : T₁.IsTree) (hT₂ : T₂.IsTree) (t₁ : ι₁) (t₂ : ι₂) :
    (sumBridgeTree T₁ T₂ t₁ t₂).IsTree where
  connected :=
    { preconnected := fun u v ↦ (sumBridgePath hT₁ hT₂ t₁ t₂ u v).reachable
      nonempty := ⟨Sum.inl t₁⟩ }
  isAcyclic := by
    let G₀ := T₁.map Function.Embedding.inl ⊔ T₂.map Function.Embedding.inr
    have hEq : sumBridgeTree T₁ T₂ t₁ t₂ = G₀ ⊔ SimpleGraph.edge (Sum.inl t₁) (Sum.inr t₂) := by
      ext p q
      cases p <;> cases q <;>
        simp [sumBridgeTree, G₀, SimpleGraph.map_adj, SimpleGraph.edge_adj, eq_comm, and_comm]
    have hnreach : ¬ G₀.Reachable (Sum.inl t₁) (Sum.inr t₂) := by
      rintro ⟨w⟩
      have hwalk_inl : ∀ {u v : ι₁ ⊕ ι₂} (w : G₀.Walk u v) (s₁ : ι₁),
          u = Sum.inl s₁ → ∃ s₂ : ι₁, v = Sum.inl s₂ := by
        intro u v w
        induction w with
        | nil =>
          intro s₁ hu
          exact ⟨s₁, hu⟩
        | @cons a b c hadj p ih =>
          intro s₁ ha
          subst ha
          rcases hadj with ⟨_, x, y, _, hax, hby⟩ | ⟨_, x, y, _, hax, _⟩
          · exact ih y hby.symm
          · cases hax
      obtain ⟨_, h⟩ := hwalk_inl w t₁ rfl
      cases h
    rw [hEq]
    exact (sumDisjoint_isAcyclic hT₁.isAcyclic hT₂.isAcyclic).sup_edge_of_not_reachable hnreach

private lemma treePath_sumBridgeTree_eq {ι₁ ι₂ : Type*} {T₁ : SimpleGraph ι₁} {T₂ : SimpleGraph ι₂}
    (hT₁ : T₁.IsTree) (hT₂ : T₂.IsTree) (t₁ : ι₁) (t₂ : ι₂) (u v : ι₁ ⊕ ι₂) :
    treePath (sumBridgeTree_isTree hT₁ hT₂ t₁ t₂) u v = sumBridgePath hT₁ hT₂ t₁ t₂ u v :=
  (eq_treePath (sumBridgeTree_isTree hT₁ hT₂ t₁ t₂) (sumBridgePath hT₁ hT₂ t₁ t₂ u v)
    (sumBridgePath_isPath hT₁ hT₂ t₁ t₂ u v)).symm

/-- If `H` is finite and `G` is obtained from `H` and an `r × s` cylinder by cylinder
identification, then `V(G)` is finite. -/
private lemma finite_vertexSet_of_isCylinderIdentification
    {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {r : ℕ} {G : Graph α₁ β₁} {H : Graph α₂ β₂} (hVH : V(H).Finite)
    (s : ℕ) (hs : 0 < s) (v : Fin r → α₂)
    (hId : IsCylinderIdentification G H s hs v) :
    V(G).Finite := by
  obtain ⟨_, _, H', S', φH, φS, hSep, _, _⟩ := hId
  rw [← hSep.2.2.1]
  have : Finite ↥V(H) := hVH.to_subtype
  have : Finite ↥V(H') := Finite.of_equiv ↥V(H) φH.vertexEquiv
  have : Finite ↥V(cylinderGraph r s) := inferInstanceAs (Finite ↥(Set.univ : Set (Fin r × Fin s)))
  have : Finite ↥V(S') := Finite.of_equiv ↥V(cylinderGraph r s) φS.vertexEquiv
  exact (Set.toFinite V(H')).union (Set.toFinite V(S'))

/-- Graph Minors III, (3.10) (page 59):
"(3.10) *If $G$ is the sleeve union of $G_1, G_2$ then the tree-width of $G$ is the maximum of the
tree-widths of $G_1, G_2$.*" -/
theorem theorem_3_10_proof {α : Type u} {β : Type v} {α₁ : Type u₁} {β₁ : Type v₁}
    {α₂ : Type u₂} {β₂ : Type v₂}
    {G : Graph α β} {G₁ : Graph α₁ β₁} {G₂ : Graph α₂ β₂}
    (hVG : V(G).Finite) (hSU : IsSleeveUnion G G₁ G₂) (w : ℕ) :
    TreeWidthLE G w ↔ TreeWidthLE G₁ w ∧ TreeWidthLE G₂ w := by
  constructor
  · intro htw
    obtain ⟨⟨G₁', h₁_le, C₁, hC₁, _, hIso₁⟩, ⟨G₂', h₂_le, C₂, hC₂, _, hIso₂⟩⟩ :=
      theorem_3_9_proof hSU
    exact ⟨treeWidthLE_of_isIsoMinor hVG ⟨G₁', h₁_le, C₁, hC₁, hIso₁⟩ htw,
      treeWidthLE_of_isIsoMinor hVG ⟨G₂', h₂_le, C₂, hC₂, hIso₂⟩ htw⟩
  · rintro ⟨htw₁, htw₂⟩
    obtain ⟨H₁, H₂, r, v, hSep, hv_inj, hinter, _, _, hId₁, hId₂⟩ := hSU
    let s : ℕ := max 1 ((r + 1) / 2)
    have hs : 0 < s := Nat.le_max_left 1 ((r + 1) / 2)
    have hr : r ≤ 2 * s := by dsimp [s]; omega
    have hVG₁ : V(G₁).Finite :=
      finite_vertexSet_of_isCylinderIdentification (hVG.subset hSep.1.vertexSet_mono) s hs v hId₁
    have hVG₂ : V(G₂).Finite :=
      finite_vertexSet_of_isCylinderIdentification (hVG.subset hSep.2.1.vertexSet_mono) s hs v hId₂
    obtain ⟨ι₁, hfin₁, T₁, X₁, t₁, hTD₁, hw₁, hsub₁⟩ :=
      theorem_3_8_proof hVG₁ s hs hr v hId₁ htw₁
    obtain ⟨ι₂, hfin₂, T₂, X₂, t₂, hTD₂, hw₂, hsub₂⟩ :=
      theorem_3_8_proof hVG₂ s hs hr v hId₂ htw₂
    let _ : Fintype ι₁ := hfin₁
    let _ : Fintype ι₂ := hfin₂
    rw [treeWidthLE_iff_exists_isTreeDecomposition]
    let T := sumBridgeTree T₁ T₂ t₁ t₂
    let X : ι₁ ⊕ ι₂ → Set α := Sum.elim X₁ X₂
    refine ⟨ι₁ ⊕ ι₂, inferInstance, T, X, ?_, ?_⟩
    · refine
        { isTree := sumBridgeTree_isTree hTD₁.isTree hTD₂.isTree t₁ t₂
          bag_subset := by
            rintro (s₁ | s₂)
            · exact (hTD₁.bag_subset s₁).trans hSep.1.vertexSet_mono
            · exact (hTD₂.bag_subset s₂).trans hSep.2.1.vertexSet_mono
          iUnion_bags := by
            ext x
            rw [mem_iUnion, Sum.exists]
            simp only [X, Sum.elim_inl, Sum.elim_inr, ← mem_iUnion,
              hTD₁.iUnion_bags, hTD₂.iUnion_bags, ← mem_union, hSep.2.2.1]
          edge_in_bag := by
            intro e u₁ u₂ hl
            have heG : e ∈ E(G) := hl.edge_mem
            rw [← hSep.2.2.2.1, mem_union] at heG
            rcases heG with he₁ | he₂
            · obtain ⟨s₁, hu₁, hu₂⟩ := hTD₁.edge_in_bag ((hSep.1.isLink_iff he₁).mpr hl)
              exact ⟨Sum.inl s₁, hu₁, hu₂⟩
            · obtain ⟨s₂, hu₁, hu₂⟩ := hTD₂.edge_in_bag ((hSep.2.1.isLink_iff he₂).mpr hl)
              exact ⟨Sum.inr s₂, hu₁, hu₂⟩
          inter_subset_on_path := ?_ }
      intro p₁ p' p₂ hpath x ⟨hx₁, hx₂⟩
      have hTree := sumBridgeTree_isTree hTD₁.isTree hTD₂.isTree t₁ t₂
      rw [onTreePath_iff_mem_treePath hTree,
        treePath_sumBridgeTree_eq hTD₁.isTree hTD₂.isTree t₁ t₂] at hpath
      cases p₁ with
      | inl s₁ =>
        cases p₂ with
        | inl s₂ =>
          dsimp [sumBridgePath] at hpath
          rw [Walk.support_map, List.mem_map] at hpath
          obtain ⟨s', hs', rfl⟩ := hpath
          rw [← onTreePath_iff_mem_treePath hTD₁.isTree] at hs'
          exact hTD₁.inter_subset_on_path hs' ⟨hx₁, hx₂⟩
        | inr s₂ =>
          have hx_inter : x ∈ V(H₁) ∩ V(H₂) :=
            ⟨hTD₁.bag_subset s₁ hx₁, hTD₂.bag_subset s₂ hx₂⟩
          rw [hinter] at hx_inter
          have hxt₁ : x ∈ X₁ t₁ := hsub₁ hx_inter
          have hxt₂ : x ∈ X₂ t₂ := hsub₂ hx_inter
          dsimp [sumBridgePath] at hpath
          rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append,
            Walk.support_map, Walk.support_map, List.mem_map, List.mem_map] at hpath
          rcases hpath with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩
          · rw [← onTreePath_iff_mem_treePath hTD₁.isTree] at hs'
            exact hTD₁.inter_subset_on_path hs' ⟨hx₁, hxt₁⟩
          · rw [← onTreePath_iff_mem_treePath hTD₂.isTree] at hs'
            exact hTD₂.inter_subset_on_path hs' ⟨hxt₂, hx₂⟩
      | inr s₁ =>
        cases p₂ with
        | inl s₂ =>
          have hx_inter : x ∈ V(H₁) ∩ V(H₂) :=
            ⟨hTD₁.bag_subset s₂ hx₂, hTD₂.bag_subset s₁ hx₁⟩
          rw [hinter] at hx_inter
          have hxt₁ : x ∈ X₁ t₁ := hsub₁ hx_inter
          have hxt₂ : x ∈ X₂ t₂ := hsub₂ hx_inter
          dsimp [sumBridgePath] at hpath
          rw [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append,
            Walk.support_map, Walk.support_map, List.mem_map, List.mem_map] at hpath
          rcases hpath with ⟨s', hs', rfl⟩ | ⟨s', hs', rfl⟩
          · rw [← onTreePath_iff_mem_treePath hTD₂.isTree] at hs'
            exact hTD₂.inter_subset_on_path hs' ⟨hx₁, hxt₂⟩
          · rw [← onTreePath_iff_mem_treePath hTD₁.isTree] at hs'
            exact hTD₁.inter_subset_on_path hs' ⟨hxt₁, hx₂⟩
        | inr s₂ =>
          dsimp [sumBridgePath] at hpath
          rw [Walk.support_map, List.mem_map] at hpath
          obtain ⟨s', hs', rfl⟩ := hpath
          rw [← onTreePath_iff_mem_treePath hTD₂.isTree] at hs'
          exact hTD₂.inter_subset_on_path hs' ⟨hx₁, hx₂⟩
    · rintro (s₁ | s₂)
      · exact hw₁ s₁
      · exact hw₂ s₂

end GraphMinor.GM03
