module

public import GraphMinor.GM10.Section4Minors
public import GraphMinor.Minor.Basic

/-!
# Choosing a vertex to represent a contracted connected set

For the local reductions in Graph Minors X, (4.2), page 165, it is useful
to contract an edge while retaining one of its ends as the vertex name.
We identify this graph with the minor defined by connected vertex sets.
-/

public section

namespace GraphMinor.GM10

open Graph SimpleGraph Hypergraph Relation

universe u v

variable {α : Type u} {β : Type v}

/-- Any subgraph `H ≤ G` is isomorphic to a minor of `G`. -/
theorem isIsoMinor_of_le {H G : Graph α β} (hHG : H ≤ G) : IsIsoMinor H G := by
  obtain ⟨H', hH', C, hC, hIso⟩ := IsIsoMinor.refl H
  exact ⟨H', hH'.trans hHG, C, hC, hIso⟩

/-- If `U ⊆ V(G)` contains `u₀`, and `C₀ ⊆ E(G)` is a set of edges with both ends in `U` that
connects `U` to `u₀`, then contracting `U` into `u₀` via `(G.map f).deleteEdges C₀`
(where `f z = if z ∈ U then u₀ else z`) gives a graph isomorphic to `contract G C₀`, and hence
isomorphic to a minor of `G`. -/
theorem isIsoMinor_map_deleteEdges {G : Graph α β} {U : Set α} {u₀ : α} {C₀ : Set β}
    (hU : U ⊆ V(G)) (hu₀ : u₀ ∈ U) (hC₀ : C₀ ⊆ E(G))
    (hC₀_ends : ∀ e ∈ C₀, ∀ x y, G.IsLink e x y → x ∈ U ∧ y ∈ U)
    (hC₀_conn : ∀ x ∈ U, ReflTransGen (fun a b ↦ ∃ e ∈ C₀, G.IsLink e a b) u₀ x) :
    letI := Classical.propDecidable
    IsIsoMinor ((G.map (fun z ↦ if z ∈ U then u₀ else z)).deleteEdges C₀) G := by
  classical
  let f (z : α) : α := if z ∈ U then u₀ else z
  let G' := (G.map f).deleteEdges C₀
  have hsymm : ∀ {a b : α},
      ReflTransGen (fun x y ↦ ∃ e ∈ C₀, G.IsLink e x y) a b →
      ReflTransGen (fun x y ↦ ∃ e ∈ C₀, G.IsLink e x y) b a := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih =>
      rcases hstep with ⟨e, heC₀, hl⟩
      exact (ReflTransGen.single ⟨e, heC₀, hl.symm⟩).trans ih
  have hcomp_of_mem : ∀ z ∈ U, contractComp G C₀ z = U := by
    intro z hz
    ext w
    simp only [contractComp, Set.mem_ofPred_eq]
    constructor
    · intro hzw
      induction hzw with
      | refl => exact hz
      | tail _ hstep _ =>
        rcases hstep with ⟨e, heC₀, hl⟩
        exact (hC₀_ends e heC₀ _ _ hl).2
    · intro hw
      exact (hsymm (hC₀_conn z hz)).trans (hC₀_conn w hw)
  have hcomp_of_notMem : ∀ z ∉ U, contractComp G C₀ z = {z} := by
    intro z hz
    ext w
    simp only [contractComp, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hzw
      induction hzw with
      | refl => rfl
      | tail _ hstep ih =>
        subst ih
        rcases hstep with ⟨e, heC₀, hl⟩
        exact (hz (hC₀_ends e heC₀ _ _ hl).1).elim
    · rintro rfl
      exact ReflTransGen.refl
  have hcomp_f : ∀ z : α, contractComp G C₀ (f z) = contractComp G C₀ z := by
    intro z
    dsimp [f]
    split_ifs with hz
    · rw [hcomp_of_mem u₀ hu₀, hcomp_of_mem z hz]
    · rfl
  have hVG' : V(G') = (V(G) \ U) ∪ {u₀} := by
    change f '' V(G) = (V(G) \ U) ∪ {u₀}
    ext x
    simp only [Set.mem_image, Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff, f]
    constructor
    · rintro ⟨z, hzG, rfl⟩
      split_ifs with hzU
      · exact Or.inr rfl
      · exact Or.inl ⟨hzG, hzU⟩
    · rintro (⟨hxG, hxU⟩ | hx_eq)
      · refine ⟨x, hxG, ?_⟩
        simp [hxU]
      · refine ⟨u₀, hU hu₀, ?_⟩
        rw [hx_eq]
        simp [hu₀]
  have hinj : Set.InjOn (contractComp G C₀) V(G') := by
    intro x hx y hy hxy
    rw [hVG'] at hx hy
    rcases hx with ⟨_, hxU⟩ | hx_eq <;> rcases hy with ⟨_, hyU⟩ | hy_eq
    · rw [hcomp_of_notMem x hxU, hcomp_of_notMem y hyU] at hxy
      exact Set.singleton_injective hxy
    · rw [hcomp_of_notMem x hxU, hy_eq, hcomp_of_mem u₀ hu₀] at hxy
      have hu_mem : u₀ ∈ ({x} : Set α) := hxy ▸ hu₀
      rw [Set.mem_singleton_iff] at hu_mem
      exact (hxU (hu_mem ▸ hu₀)).elim
    · rw [hx_eq, hcomp_of_mem u₀ hu₀, hcomp_of_notMem y hyU] at hxy
      have hu_mem : u₀ ∈ ({y} : Set α) := hxy ▸ hu₀
      rw [Set.mem_singleton_iff] at hu_mem
      exact (hyU (hu_mem ▸ hu₀)).elim
    · rw [hx_eq, hy_eq]
  have himg_eq : contractComp G C₀ '' V(G') = V(contract G C₀) := by
    change contractComp G C₀ '' (f '' V(G)) = contractComp G C₀ '' V(G)
    rw [← Set.image_comp]
    have hcomp_eq : contractComp G C₀ ∘ f = contractComp G C₀ := funext hcomp_f
    rw [hcomp_eq]
  refine ⟨G, le_rfl, C₀, hC₀, ⟨?_⟩⟩
  refine
    { vertexEquiv :=
        (Equiv.Set.imageOfInjOn (contractComp G C₀) V(G') hinj).trans
          (Equiv.subtypeEquivRight fun X ↦ by rw [himg_eq])
      edgeEquiv := Equiv.refl _
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩
  change G'.IsLink e x y ↔ (contract G C₀).IsLink e (contractComp G C₀ x) (contractComp G C₀ y)
  simp only [G', contract, deleteEdges_isLink, map_isLink, Relation.Map, contractComp]
  refine and_congr_left fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨a, b, hab, (hcomp_f a).symm, (hcomp_f b).symm⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    have hfa : f a ∈ V(G') := ⟨a, hab.left_mem, rfl⟩
    have hfb : f b ∈ V(G') := ⟨b, hab.right_mem, rfl⟩
    have hx_eq : f a = x := hinj hfa hx ((hcomp_f a).trans ha)
    have hy_eq : f b = y := hinj hfb hy ((hcomp_f b).trans hb)
    exact ⟨a, b, hab, hx_eq, hy_eq⟩

/-- Special case of `isIsoMinor_map_deleteEdges` for contracting a single link `e₀` with ends
`u₀ ≠ v₀` (`f z = if z = u₀ then v₀ else z`). -/
theorem isIsoMinor_contractSingleEdge {G : Graph α β} {e₀ : β} {u₀ v₀ : α}
    (he₀ : G.IsLink e₀ u₀ v₀) (hne : u₀ ≠ v₀) :
    letI := Classical.propDecidable
    IsIsoMinor ((G.map (fun z ↦ if z = u₀ then v₀ else z)).deleteEdges {e₀}) G := by
  classical
  have hU : ({v₀, u₀} : Set α) ⊆ V(G) := by
    rintro x (rfl | rfl)
    · exact he₀.right_mem
    · exact he₀.left_mem
  have hvU : v₀ ∈ ({v₀, u₀} : Set α) := Set.mem_insert v₀ {u₀}
  have hC₀ : ({e₀} : Set β) ⊆ E(G) := Set.singleton_subset_iff.2 he₀.edge_mem
  have hC₀_ends : ∀ e ∈ ({e₀} : Set β), ∀ x y, G.IsLink e x y →
      x ∈ ({v₀, u₀} : Set α) ∧ y ∈ ({v₀, u₀} : Set α) := by
    rintro e rfl x y hxy
    rcases he₀.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
  have hC₀_conn : ∀ x ∈ ({v₀, u₀} : Set α),
      ReflTransGen (fun a b ↦ ∃ e ∈ ({e₀} : Set β), G.IsLink e a b) v₀ x := by
    rintro x (rfl | rfl)
    · exact ReflTransGen.refl
    · exact ReflTransGen.single ⟨e₀, Set.mem_singleton e₀, he₀.symm⟩
  have hminor := isIsoMinor_map_deleteEdges hU hvU hC₀ hC₀_ends hC₀_conn
  convert hminor using 3
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hzu : z = u₀
  · subst hzu
    simp
  · by_cases hzv : z = v₀
    · subst hzv
      simp
    · simp [hzu, hzv]

end GraphMinor.GM10
