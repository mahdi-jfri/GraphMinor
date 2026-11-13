module

public import GraphMinor.GM05.SeriesParallelDefs
import GraphMinor.Minor.Basic
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Graph Minors V, (1.3): taking a minor does not increase tree-width

For a minor model, replace each bag by the branch sets meeting it. Disjoint
branch sets cannot increase its size. A connected branch set meets every bag
on the path between two bags that it meets, which gives the path condition.
The case of an empty ambient edge type is handled by singleton bags.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set Graph Relation

variable {α β α' β' ι : Type*}

private lemma onTreePath_triangle {T : SimpleGraph ι} {a b c q : ι}
    (h : OnTreePath T a b c) : OnTreePath T a q c ∨ OnTreePath T q b c := by
  classical
  by_cases h₁ : OnTreePath T a q c
  · exact Or.inl h₁
  · change ¬ ∀ p : T.Walk a q, p.IsPath → c ∈ p.support at h₁
    push Not at h₁
    obtain ⟨p, hp, hpc⟩ := h₁
    right
    intro r hr
    have hc := GM10.mem_support_of_onTreePath h (p.append r)
    exact (Walk.mem_support_append_iff p r).mp hc |>.resolve_left hpc

private lemma bag_meets_reachable [Fintype ι]
    {G K : Graph α β} (hKG : K ≤ G)
    {T : SimpleGraph ι} {χ : ι → Set α}
    (htd : IsTreeDecomposition (simpleShadow G) T χ)
    {x y : α} (hxK : x ∈ V(K)) (hxy : ReflTransGen K.Adj x y) :
    ∀ {a b c}, x ∈ χ a → y ∈ χ b → OnTreePath T a b c →
      ∃ z ∈ V(K), z ∈ χ c := by
  induction hxy with
  | refl =>
    intro a b c hx hy hp
    exact ⟨x, hxK, htd.inter_subset hp ⟨hx, hy⟩⟩
  | @tail y z hxy hyz ih =>
    intro a b c hx hz hp
    by_cases he : y = z
    · subst z
      exact ih hx hz hp
    · have hGyz : G.Adj y z := Graph.Adj.mono hKG hyz
      obtain ⟨q, hqy, hqz⟩ := htd.adj_mem ⟨he, hGyz⟩
      rcases onTreePath_triangle (q := q) hp with hpa | hpb
      · exact ih hx hqy hpa
      · exact ⟨z, hyz.right_mem, htd.inter_subset hpb ⟨hqz, hz⟩⟩

private lemma width_from_model {H : Graph α' β'} {G : Graph α β}
    (hVG : V(G).Finite) {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) {w : ℕ}
    (hw : TreeWidthLE (simpleShadow G) w) : TreeWidthLE (simpleShadow H) w := by
  classical
  obtain ⟨ι, _, T, χ, htd, hwidth⟩ := hw
  have hcover : (⋃ t, χ t) = V(G) := htd.iUnion_eq
  let χ' : ι → Set α' := fun t ↦ {v | v ∈ V(H) ∧ (ηv v ∩ χ t).Nonempty}
  have htd' : IsTreeDecomposition (simpleShadow H) T χ' := by
    refine ⟨htd.isTree, ?_, ?_, ?_⟩
    · ext v
      simp only [mem_iUnion, χ', mem_ofPred_eq]
      constructor
      · rintro ⟨t, hv, _⟩
        exact hv
      · intro hv
        obtain ⟨x, hx⟩ := hm.vertex_nonempty v hv
        have hxG := hm.vertex_subset v hv hx
        rw [← hcover] at hxG
        obtain ⟨t, ht⟩ := mem_iUnion.mp hxG
        exact ⟨t, hv, x, hx, ht⟩
    · intro v u hvu
      obtain ⟨hne, e, he⟩ := hvu
      have hv := he.left_mem
      have hu := he.right_mem
      obtain ⟨x, hx, hxe⟩ := (hm.inc_iff v hv e he.edge_mem).mp he.inc_left
      obtain ⟨y, hy, hye⟩ := (hm.inc_iff u hu e he.edge_mem).mp he.inc_right
      have hxy : x ≠ y := by
        intro heq
        exact Set.disjoint_left.mp (hm.vertex_disjoint v hv u hu hne) hx (heq ▸ hy)
      have hyother : y = hxe.other := hye.eq_of_isLink_of_ne_left hxe.isLink_other hxy.symm
      have hl : G.IsLink (ηe e) x y := hyother.symm ▸ hxe.isLink_other
      obtain ⟨t, hxt, hyt⟩ := htd.adj_mem ⟨hxy, hl.adj⟩
      exact ⟨t, ⟨hv, x, hx, hxt⟩, ⟨hu, y, hy, hyt⟩⟩
    · intro a c b hp v hv
      obtain ⟨hvH, x, hxv, hxa⟩ := hv.1
      obtain ⟨_, y, hyv, hyb⟩ := hv.2
      obtain ⟨K, hK, hKV, hconn⟩ := hm.connected v hvH
      have hxK : x ∈ V(K) := hKV.symm ▸ hxv
      have hyK : y ∈ V(K) := hKV.symm ▸ hyv
      obtain ⟨z, hzK, hzc⟩ := bag_meets_reachable
        (hK.trans Graph.deleteEdges_le) htd hxK (hconn.2 x hxK y hyK) hxa hyb hp
      exact ⟨hvH, z, hKV ▸ hzK, hzc⟩
  refine treeWidthLE_of_isTreeDecomposition htd' ?_
  intro t
  have hχfin : (χ t).Finite := hVG.subset (by
    rw [← hcover]
    exact subset_iUnion χ t)
  let : Finite (χ t) := hχfin.to_subtype
  let f : χ' t → χ t := fun v ↦
    ⟨v.2.2.choose, v.2.2.choose_spec.2⟩
  have hf : Function.Injective f := by
    intro v u heq
    apply Subtype.ext
    by_contra hne
    have hd := hm.vertex_disjoint v.1 v.2.1 u.1 u.2.1 hne
    have hx := v.2.2.choose_spec.1
    have hy := u.2.2.choose_spec.1
    have he := congrArg Subtype.val heq
    change v.2.2.choose = u.2.2.choose at he
    exact Set.disjoint_left.mp hd hx (by rw [he]; exact hy)
  have hle : (χ' t).ncard ≤ (χ t).ncard := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_le_card_of_injective f hf
  exact hle.trans (hwidth t)

/-- An edgeless finite graph has width zero. Singleton bags are indexed by
the leaves of a star, with an empty bag at its centre. -/
theorem treeWidthLE_zero_of_no_adj {G : (⊤ : SimpleGraph α).Subgraph}
    (hfin : G.verts.Finite) (hadj : ∀ x y, ¬ G.Adj x y) : TreeWidthLE G 0 := by
  classical
  let : Fintype G.verts := hfin.fintype
  let χ : Option G.verts → Set α := fun t ↦ t.elim ∅ (fun v ↦ {v.1})
  have htd : IsTreeDecomposition G (starGraph (none : Option G.verts)) χ := by
    refine ⟨isTree_starGraph _, ?_, ?_, ?_⟩
    · ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨t, ht⟩
        cases t with
        | none => exact ht.elim
        | some v => exact ht ▸ v.2
      · intro hx
        exact ⟨some ⟨x, hx⟩, rfl⟩
    · intro x y hxy
      exact (hadj x y hxy).elim
    · intro a c b hp x hx
      cases a with
      | none => exact hx.1.elim
      | some a =>
        cases b with
        | none => exact hx.2.elim
        | some b =>
          have hab : a = b := Subtype.ext (hx.1.symm.trans hx.2)
          subst b
          have hc := GM10.onTreePath_self_iff.mp hp
          exact hc ▸ hx.1
  apply treeWidthLE_of_isTreeDecomposition htd
  intro t
  cases t <;> simp [χ]

/-- A minor model transfers a width bound to the minor. The empty ambient
edge type is treated separately, so no inhabitance condition is needed. -/
theorem treeWidthLE_of_minor {H : Graph α' β'} {G : Graph α β}
    (hVH : V(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hminor : IsIsoMinor H G) {w : ℕ} (hw : TreeWidthLE (simpleShadow G) w) :
    TreeWidthLE (simpleShadow H) w := by
  classical
  cases isEmpty_or_nonempty β with
  | inl hβ =>
    let : IsEmpty β := hβ
    obtain ⟨G', hG', C, hC, ⟨e⟩⟩ := hminor
    have hno : ∀ x y, ¬ (simpleShadow H).Adj x y := by
      rintro x y ⟨_, f, hf⟩
      exact isEmptyElim (e.edgeEquiv ⟨f, hf.edge_mem⟩).1
    obtain ⟨ι, _, T, χ, htd, hwidth⟩ := treeWidthLE_zero_of_no_adj hVH hno
    exact ⟨ι, inferInstance, T, χ, htd, fun t ↦ (hwidth t).trans (by omega)⟩
  | inr hβ =>
    let : Nonempty β := hβ
    obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor hVG hEG hminor
    exact width_from_model hVG hm hw

/-- A finite graph has a decomposition attaining its natural-valued
`treeWidth`: there is always a one-bag decomposition, so the infimum is attained. -/
theorem treeWidthLE_treeWidth {G : (⊤ : SimpleGraph α).Subgraph}
    (_hfin : G.verts.Finite) : TreeWidthLE G (treeWidth G) := by
  have htd : IsTreeDecomposition G (⊥ : SimpleGraph Unit) (fun _ ↦ G.verts) := by
    refine ⟨IsTree.of_subsingleton, iUnion_const _, ?_, ?_⟩
    · intro x y hxy
      exact ⟨(), hxy.fst_mem, hxy.snd_mem⟩
    · intro a c b hp
      exact inter_subset_left
  have hex : ∃ w, TreeWidthLE G w :=
    ⟨G.verts.ncard, treeWidthLE_of_isTreeDecomposition htd (fun _ ↦ Nat.le_succ _)⟩
  exact Nat.sInf_mem hex

/-- Graph Minors V, (1.3), page 93:
"If $H$ is a minor of $G$ then the tree-width of $H$ is no greater than the tree-width of $G$."
A minor model transfers bags without increasing their sizes. -/
theorem theorem_1_3_proof {H : Graph α' β'} {G : Graph α β}
    (hVH : V(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hminor : IsIsoMinor H G) :
    treeWidth (simpleShadow H) ≤ treeWidth (simpleShadow G) :=
  Nat.sInf_le (treeWidthLE_of_minor hVH hVG hEG hminor (treeWidthLE_treeWidth hVG))

end GraphMinor.GM05
