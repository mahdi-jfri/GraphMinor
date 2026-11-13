module

public import GraphMinor.GM02.Termination

/-!
# Terminations on the actual vertex type

Recursive induced graphs use a subset of their parent's ambient vertices.
Attach the stated vertex-membership proof to each termination endpoint.
This gives the same termination on the actual vertex subtype, with the
same pairs and index after forgetting the attached proofs. No new paths
or feasibility information are included in this conversion.
-/

@[expose] public section
namespace GraphMinor.GM02
open Set Classical
universe u

private theorem mem_attachWith {α : Type u} {S : Set α} {p : Sym2 α}
    (h : ∀ a ∈ p, a ∈ S) (a : S) : a ∈ p.attachWith h ↔ a.val ∈ p := by
  change a ∈ p.pmap Subtype.mk h ↔ a.val ∈ p
  rw [Sym2.mem_pmap_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    have heval : a.val = b := congrArg Subtype.val he
    exact heval ▸ hb
  · intro ha
    exact ⟨a.val, ha, Subtype.ext rfl⟩

/-- Regard a termination as a termination of its actual vertex subtype. -/
noncomputable def Termination.onVertices {α : Type u} {S : Set α}
    (A : Termination S) : Termination (Set.univ : Set S) where
  pairs := A.pairs.attach.image (fun p => p.val.attachWith (A.vertex_mem p.val p.property))
  not_diag := by
    intro p hp hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hp
    have hdiag := hd.map (f := Subtype.val)
    rw [Sym2.attachWith_map_subtypeVal] at hdiag
    exact A.not_diag q.val q.property hdiag
  vertex_mem := fun _ _ _ _ => Set.mem_univ _
  disjoint := by
    intro p hp q hq hpq
    obtain ⟨p₀, _, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨q₀, _, rfl⟩ := Finset.mem_image.1 hq
    have hpq₀ : p₀.val ≠ q₀.val := by
      intro he
      have he' : p₀ = q₀ := Subtype.ext he
      subst q₀
      exact hpq rfl
    apply Set.disjoint_left.2
    intro a hap haq
    exact Set.disjoint_left.1 (A.disjoint p₀.val p₀.property q₀.val q₀.property hpq₀)
      ((mem_attachWith _ a).1 hap) ((mem_attachWith _ a).1 haq)

/-- The converted pairs are exactly the original pairs after forgetting
endpoint membership proofs. -/
theorem Termination.mem_onVertices_pairs {α : Type u} {S : Set α} (A : Termination S)
    (p : Sym2 S) : p ∈ A.onVertices.pairs ↔ p.map Subtype.val ∈ A.pairs := by
  constructor
  · intro hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hp
    simpa only [Sym2.attachWith_map_subtypeVal] using q.property
  · intro hp
    apply Finset.mem_image.2
    let q : {q // q ∈ A.pairs} := ⟨p.map Subtype.val, hp⟩
    refine ⟨q, Finset.mem_attach _ _, ?_⟩
    apply Sym2.map.injective Subtype.val_injective
    exact Sym2.attachWith_map_subtypeVal _

/-- Restricting the ambient type does not change the number of terminal pairs. -/
theorem Termination.onVertices_index {α : Type u} {S : Set α} (A : Termination S) :
    A.onVertices.index = A.index := by
  have hinj : Function.Injective (fun p : {p // p ∈ A.pairs} =>
      p.val.attachWith (A.vertex_mem p.val p.property)) := by
    intro p q h
    apply Subtype.ext
    simpa only [Sym2.attachWith_map_subtypeVal] using congrArg (Sym2.map Subtype.val) h
  simp only [Termination.index, Termination.onVertices, Finset.card_image_of_injective _ hinj,
    Finset.card_attach]

end GraphMinor.GM02
