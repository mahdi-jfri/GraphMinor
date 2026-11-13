module

public import GraphMinor.GM08.Section18CutCount
public import GraphMinor.GM08.Section18Induction
import GraphMinor.GM08.Section14

/-!
# Labels in two universes: (18.3) and (6.1)

The induction of (18.3) runs on grafts whose vertex and edge labels lie in one
universe (`ClassCWellRooted`). The statements (18.3) and (6.1) on pages 286
and 263 put no such condition on the labels. We move a graft with labels in
`α` and `β` to the labels `ULift α` and `ULift β`, which lie in one universe
(`Graft.ulift`). The moved graft is isomorphic to the original one, so it lies
in the same classes `𝒞(h, k)`, and simulation passes through isomorphisms
(`isGraftSimulatedIn_of_isGraftIso_map`). This gives (18.3) and (6.1) for all
label universes from the `X₂` case of the cut counts.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Graph GraphMinor.Surface

universe u v w u' v' r s

/-- An isomorphism gives a simulation, for grafts with different label types.
The maps `gv` and `g` only give values to labels that are not vertices or edges. -/
theorem isGraftSimulatedIn_of_isGraftIso_map {α : Type u} {β : Type v} {α' : Type u'}
    {β' : Type v'} {Y : Graft α' β'} {X : Graft α β} (gv : α' → α) (g : β' → β)
    (h : IsGraftIso Y X) :
    IsGraftSimulatedIn Y X := by
  classical
  obtain ⟨φ, hT⟩ := h
  let ηv : α' → Set α := fun u => if hu : u ∈ V(Y.G) then {(φ.vertexEquiv ⟨u, hu⟩).1} else ∅
  let ηe : β' → β := fun e => if he : e ∈ E(Y.G) then (φ.edgeEquiv ⟨e, he⟩).1 else g e
  have hηv_eq : ∀ {u : α'} (hu : u ∈ V(Y.G)), ηv u = {(φ.vertexEquiv ⟨u, hu⟩).1} :=
    fun hu => by simp [ηv, hu]
  have hηe_eq : ∀ {e : β'} (he : e ∈ E(Y.G)), ηe e = (φ.edgeEquiv ⟨e, he⟩).1 :=
    fun he => by simp [ηe, he]
  refine ⟨ηv, ηe, ?_, ?_, ?_⟩
  · refine {
      vertex_nonempty := fun u hu => by
        rw [hηv_eq hu]
        exact singleton_nonempty _
      vertex_subset := fun u hu x hx => by
        rw [hηv_eq hu, mem_singleton_iff] at hx
        exact hx ▸ (φ.vertexEquiv ⟨u, hu⟩).2
      edge_mem := fun e he => by
        rw [hηe_eq he]
        exact (φ.edgeEquiv ⟨e, he⟩).2
      vertex_disjoint := fun u₁ hu₁ u₂ hu₂ hne => by
        rw [hηv_eq hu₁, hηv_eq hu₂, disjoint_singleton]
        intro heq
        apply hne
        have hsub : φ.vertexEquiv ⟨u₁, hu₁⟩ = φ.vertexEquiv ⟨u₂, hu₂⟩ := Subtype.ext heq
        exact congrArg Subtype.val (φ.vertexEquiv.injective hsub)
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
        rw [hηe_eq he₁, hηe_eq he₂] at heq
        have hsub : φ.edgeEquiv ⟨e₁, he₁⟩ = φ.edgeEquiv ⟨e₂, he₂⟩ := Subtype.ext heq
        exact congrArg Subtype.val (φ.edgeEquiv.injective hsub)
      inc_iff := fun u hu e he => by
        rw [hηv_eq hu, hηe_eq he]
        simp only [mem_singleton_iff, exists_eq_left]
        constructor
        · rintro ⟨w, hlink⟩
          have hw : w ∈ V(Y.G) := hlink.right_mem
          have hlink' := (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨w, hw⟩).mp hlink
          exact hlink'.inc_left
        · rintro ⟨x, hlink'⟩
          have hx : x ∈ V(X.G) := hlink'.right_mem
          let w := φ.vertexEquiv.symm ⟨x, hx⟩
          have hlink : Y.G.IsLink e u w.1 := by
            have := (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ w).mpr
              (by simpa [w] using hlink')
            exact this
          exact hlink.inc_left
      isLoopAt_iff := fun u hu e he => by
        rw [hηv_eq hu, hηe_eq he]
        simp only [mem_singleton_iff]
        constructor
        · intro hloop x ⟨y, hl⟩
          have hl_loop : X.G.IsLink (φ.edgeEquiv ⟨e, he⟩).1
              (φ.vertexEquiv ⟨u, hu⟩).1 (φ.vertexEquiv ⟨u, hu⟩).1 :=
            (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨u, hu⟩).mp hloop
          rcases hl.eq_and_eq_or_eq_and_eq hl_loop with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
        · intro hall
          have heX : (φ.edgeEquiv ⟨e, he⟩).1 ∈ E(X.G) := (φ.edgeEquiv ⟨e, he⟩).2
          obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet heX
          have hx := hall x hl.inc_left
          have hy := hall y hl.inc_right
          subst hx hy
          exact (φ.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨u, hu⟩).mpr hl
      connected := fun u hu => by
        let x₀ := (φ.vertexEquiv ⟨u, hu⟩).1
        have hx₀_mem : x₀ ∈ V(X.G.deleteEdges (ηe '' E(Y.G))) := (φ.vertexEquiv ⟨u, hu⟩).2
        let K := (X.G.deleteEdges (ηe '' E(Y.G))).induce {x₀}
        have hK_le : K ≤ X.G.deleteEdges (ηe '' E(Y.G)) :=
          (X.G.deleteEdges (ηe '' E(Y.G))).induce_le (singleton_subset_iff.mpr hx₀_mem)
        have hVK : V(K) = ηv u := by
          rw [vertexSet_induce, hηv_eq hu]
        refine ⟨K, hK_le, hVK, ⟨x₀, by simp [K]⟩, ?_⟩
        intro a ha b hb
        rw [vertexSet_induce, mem_singleton_iff] at ha hb
        subst ha hb
        exact Relation.ReflTransGen.refl }
  · have hbij : Set.BijOn (fun u => if hu : u ∈ V(Y.G) then (φ.vertexEquiv ⟨u, hu⟩).1 else gv u)
        Y.T X.T := by
      refine ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ heq => ?_, fun x hx => ?_⟩
      · have huV : u ∈ V(Y.G) := Y.T_subset hu
        simp only [huV, ↓reduceDIte]
        exact (hT ⟨u, huV⟩).mp hu
      · have hu₁V : u₁ ∈ V(Y.G) := Y.T_subset hu₁
        have hu₂V : u₂ ∈ V(Y.G) := Y.T_subset hu₂
        simp only [hu₁V, hu₂V, ↓reduceDIte] at heq
        exact congrArg Subtype.val (φ.vertexEquiv.injective (Subtype.ext heq))
      · have hxV : x ∈ V(X.G) := X.T_subset hx
        let u := φ.vertexEquiv.symm ⟨x, hxV⟩
        have huT : u.1 ∈ Y.T := (hT u).mpr (by simpa [u] using hx)
        refine ⟨u.1, huT, ?_⟩
        simp [u, u.2]
    exact (Set.BijOn.ncard_eq hbij).symm
  · intro u hu
    have huV : u ∈ V(Y.G) := Y.T_subset hu
    refine ⟨(φ.vertexEquiv ⟨u, huV⟩).1, ?_, (hT ⟨u, huV⟩).mp hu⟩
    rw [hηv_eq huV]
    exact mem_singleton _


/-- Move the labels of a graft to `ULift`. -/
noncomputable def Graft.ulift {α : Type u} {β : Type v} (X : Graft α β) : Graft (ULift.{r} α) (ULift.{s} β) where
  G := relabelGraphBy X.G (Equiv.Set.image ULift.up V(X.G) ULift.up_injective)
    (Equiv.Set.image ULift.up E(X.G) ULift.up_injective)
  T := ULift.up '' X.T
  T_subset := image_mono X.T_subset
  finite_G := ⟨X.finite_G.1.image _, X.finite_G.2.image _⟩

/-- A graft is isomorphic to its moved copy. -/
theorem isGraftIso_ulift {α : Type u} {β : Type v} (X : Graft α β) :
    IsGraftIso X (Graft.ulift.{u, v, r, s} X) := by
  refine ⟨relabelGraphByIso X.G (Equiv.Set.image ULift.up V(X.G) ULift.up_injective)
    (Equiv.Set.image ULift.up E(X.G) ULift.up_injective), fun x => ?_⟩
  change x.1 ∈ X.T ↔ ULift.up x.1 ∈ ULift.up '' X.T
  exact ULift.up_injective.mem_set_image.symm

/-- **Moving labels keeps well-rootedness.** If the moved copies of the members
of `𝒜` lie in a well-rooted class, then `𝒜` is well-rooted. -/
theorem isWellRootedGraftClass_of_ulift {α : Type u} {β : Type v} {𝒜 : Set (Graft α β)}
    {𝒜' : Set (Graft (ULift.{r} α) (ULift.{s} β))} (h' : IsWellRootedGraftClass 𝒜')
    (hmem : ∀ X ∈ 𝒜, Graft.ulift.{u, v, r, s} X ∈ 𝒜') : IsWellRootedGraftClass 𝒜 := by
  intro X hX
  obtain ⟨i, j, hij, hs⟩ := h' (fun n => Graft.ulift.{u, v, r, s} (X n)) fun n => hmem _ (hX n)
  exact ⟨i, j, hij, ((isGraftSimulatedIn_of_isGraftIso_map ULift.up ULift.up (isGraftIso_ulift (X i))).trans
    hs).trans (isGraftSimulatedIn_of_isGraftIso_map ULift.down ULift.down (isGraftIso_ulift (X j)).symm)⟩

/-- **(18.3) from the `X₂` case of the cut counts**, for labels in any
universes. -/
theorem theorem_18_3_of_X2 (hX2 : X2CutCountStatement.{w}) : Theorem183Statement.{u, v, w} := by
  intro α β h k
  have hw := classCWellRooted_of_cutCount.{max u v, w} (cutCountStatement_of_X2 hX2) h k
    (ULift.{v} α) (ULift.{u} β)
  exact isWellRootedGraftClass_of_ulift hw fun X hX => mem_classC_of_isGraftIso (isGraftIso_ulift X) hX

/-- **(6.1) from (18.3).** A class of bounded index that embeds in a surface
`Σ` lies in `𝒞(g(Σ), k)`. -/
theorem theorem_6_1_of_183 (h183 : Theorem183Statement.{u, v, w}) :
    Theorem61Statement.{u, v, w} := by
  intro α β 𝒜 ⟨k, hk⟩ ⟨S, tS, hS, hemb⟩
  have hw := h183 α β (surfaceComplexity S) k
  intro X hX
  exact hw X fun n => ⟨S, tS, hS, le_rfl, hk _ (hX n), hemb _ (hX n)⟩

end GraphMinor.GM08
