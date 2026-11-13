module

public import GraphMinor.GM02.Termination

/-!
# Changing the vertex representation of a termination

An induced termination may be recorded in its parent's ambient type.
First regard the same endpoint pairs as a termination of the smaller
vertex set when they all lie there. An injective change of vertex names
then maps each pair and preserves disjointness and the index. These are
the representation changes used in the recursive calls of II (3.2).
-/

@[expose] public section
namespace GraphMinor.GM02
open Set Classical
universe u u'

/-- Change only the containing vertex set, retaining every terminal pair. -/
def Termination.rebase {α : Type u} {S T : Set α} (A : Termination S)
    (h : A.support ⊆ T) : Termination T where
  pairs := A.pairs
  not_diag := A.not_diag
  vertex_mem := fun p hp _ ha => h (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, ha⟩⟩)
  disjoint := A.disjoint

/-- Changing the containing vertex set does not change the support. -/
theorem Termination.rebase_support {α : Type u} {S T : Set α} (A : Termination S)
    (h : A.support ⊆ T) : (A.rebase h).support = A.support := rfl

/-- Changing the containing vertex set does not change the index. -/
theorem Termination.rebase_index {α : Type u} {S T : Set α} (A : Termination S)
    (h : A.support ⊆ T) : (A.rebase h).index = A.index := rfl

/-- Rename endpoints along an injective vertex map. -/
noncomputable def Termination.mapEmbedding {α : Type u} {α' : Type u'} {S : Set α}
    (A : Termination S) (f : α ↪ α') : Termination (f '' S) where
  pairs := A.pairs.image (Sym2.map f)
  not_diag := by
    intro p hp hd
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact A.not_diag q hq ((Sym2.isDiag_map f.injective).1 hd)
  vertex_mem := by
    intro p hp a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := Sym2.mem_map.1 ha
    exact ⟨b, A.vertex_mem q hq b hb, rfl⟩
  disjoint := by
    intro p hp q hq hpq
    obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.1 hq
    have hpq₀ : p₀ ≠ q₀ := fun h => hpq (congrArg (Sym2.map f) h)
    apply Set.disjoint_left.2
    intro a hap haq
    obtain ⟨b, hb, rfl⟩ := Sym2.mem_map.1 hap
    obtain ⟨c, hc, hcb⟩ := Sym2.mem_map.1 haq
    have heq : c = b := f.injective hcb
    exact Set.disjoint_left.1 (A.disjoint p₀ hp₀ q₀ hq₀ hpq₀) hb (heq ▸ hc)

/-- Renaming endpoint pairs does not change the number of pairs. -/
theorem Termination.mapEmbedding_index {α : Type u} {α' : Type u'} {S : Set α}
    (A : Termination S) (f : α ↪ α') : (A.mapEmbedding f).index = A.index := by
  exact Finset.card_image_of_injective _ (Sym2.map.injective f.injective)

/-- The support is exactly the image of the original support under the naming map. -/
theorem Termination.mapEmbedding_support {α : Type u} {α' : Type u'} {S : Set α}
    (A : Termination S) (f : α ↪ α') : (A.mapEmbedding f).support = f '' A.support := by
  ext a
  constructor
  · intro ha
    obtain ⟨p, hpa⟩ := Set.mem_iUnion.1 ha
    obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hpa
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨b, hb, rfl⟩ := Sym2.mem_map.1 hap
    exact ⟨b, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hb⟩⟩, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨p, hpa⟩ := Set.mem_iUnion.1 hb
    obtain ⟨hp, hbp⟩ := Set.mem_iUnion.1 hpa
    exact Set.mem_iUnion.2 ⟨p.map f, Set.mem_iUnion.2
      ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, Sym2.mem_map.2 ⟨b, hbp, rfl⟩⟩⟩

/-- Renaming endpoint pairs by a bijection and its inverse recovers all
original pairs, independently of the two containing-set types. -/
theorem Termination.mapEquiv_symm_pairs {α : Type u} {α' : Type u'} {S : Set α}
    (A : Termination S) (e : α ≃ α') :
    ((A.mapEmbedding e.toEmbedding).mapEmbedding e.symm.toEmbedding).pairs = A.pairs := by
  change (A.pairs.image (Sym2.map e)).image (Sym2.map e.symm) = A.pairs
  rw [Finset.image_image]
  have hmap : (fun p : Sym2 α => (p.map e).map e.symm) = fun p => p := by
    funext p
    induction p using Sym2.inductionOn with
    | hf a b =>
      change s(e.symm (e a), e.symm (e b)) = s(a, b)
      rw [e.symm_apply_apply, e.symm_apply_apply]
  simp only [Function.comp_def, hmap, Finset.image_id']

end GraphMinor.GM02
