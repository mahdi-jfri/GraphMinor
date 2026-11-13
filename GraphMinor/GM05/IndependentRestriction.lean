module

public import GraphMinor.GM05.ChordalDefs

/-!
# Restricting independent selections to an induced graph

The induction in Graph Minors V, (8.5), deletes vertices and sometimes
omits one of the independent sets. These lemmas transfer independent sets
and their intersection counts between an induced graph and its original
graph, using the inclusion map on vertices.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V I : Type*} {G : SimpleGraph V} {U : Set V}

/-- Inclusion into the ambient graph preserves independence of a set in
an induced graph. -/
theorem indepSet_image_induce {X : Set U} (hX : (G.induce U).IsIndepSet X) :
    G.IsIndepSet (Subtype.val '' X) := by
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ hne hab
  exact hX ha hb (fun he ↦ hne (congrArg Subtype.val he)) hab

/-- Intersection counts are unchanged by including a selected set from
an induced graph into its ambient graph. -/
theorem ncard_image_val_inter (X : Set U) (Z : Set V) :
    (Subtype.val '' X ∩ Z).ncard = (X ∩ {x : U | x.1∈Z}).ncard := by
  have he : Subtype.val '' (X ∩ {x : U | x.1∈Z}) = Subtype.val '' X ∩ Z := by
    ext x
    constructor
    · rintro ⟨a,⟨ha,haz⟩,rfl⟩
      exact ⟨⟨a,ha,rfl⟩,haz⟩
    · rintro ⟨⟨a,ha,rfl⟩,haz⟩
      exact ⟨a,⟨ha,haz⟩,rfl⟩
  rw [←he,ncard_image_of_injective _ Subtype.val_injective]

/-- If a set lies inside the induced vertex set, restricting it changes
neither its cardinality nor its graph-theoretic independence. -/
theorem restrict_independent_set {Z : Set V} (hZ : G.IsIndepSet Z) (hZU : Z⊆U) :
    (G.induce U).IsIndepSet {x : U | x.1∈Z} ∧
      ({x : U | x.1∈Z} : Set U).ncard=Z.ncard := by
  constructor
  · intro x hx y hy hxy hadj
    exact hZ hx hy (fun he ↦ hxy (Subtype.ext he)) hadj
  · rw [ncard_subtype]
    change (Z∩U).ncard=Z.ncard
    rw [inter_eq_left.mpr hZU]

/-- Restriction of pairwise disjoint sets preserves pairwise disjointness. -/
theorem disjoint_restrict (Z : I → Set V)
    (hdisj : Pairwise (fun i j ↦ Disjoint (Z i) (Z j))) :
    Pairwise (fun i j ↦ Disjoint {x : U | x.1∈Z i} {x : U | x.1∈Z j}) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  exact Set.disjoint_left.mp (hdisj hij) hx hy

/-- A selected subset of the restricted union maps back into the original
union, including when there are no color classes. -/
theorem image_subset_iUnion {Z : I → Set V} {X : Set U}
    (hX : X⊆⋃ i, {x : U | x.1∈Z i}) : Subtype.val '' X ⊆ ⋃ i,Z i := by
  rintro x ⟨a,ha,rfl⟩
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hX ha)
  exact mem_iUnion.mpr ⟨i,hi⟩

end GraphMinor.GM05
