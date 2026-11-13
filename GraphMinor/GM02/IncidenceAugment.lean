module

public import GraphMinor.GM02.TreeDecomposition
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Adding vertices on host edges while retaining the old edges

Keep the old host adjacency and add one vertex for each edge in a chosen
set. Its neighbors are exactly the original ends of that edge. Retaining
the old adjacency ensures that those ends still occur together in a
bag, so the new vertex can be put in a leaf bag of size at most three.
The incidence graph needed by the corrected split test is a subgraph.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Old host vertices and the selected host-edge vertices. -/
def incidenceAugmentVertices {α : Type u} {β : Type v} (G : Graph α β) (S : Set β) : Set (α ⊕ β) :=
  Sum.inl '' V(G) ∪ Sum.inr '' S

/-- Retain original adjacency and attach each selected edge vertex to its original ends. -/
def incidenceAugmentAdj {α : Type u} {β : Type v} (G : Graph α β) (S : Set β) :
    (α ⊕ β) → (α ⊕ β) → Prop
  | Sum.inl a, Sum.inl b => a ≠ b ∧ G.Adj a b
  | Sum.inl a, Sum.inr e => e ∈ S ∧ G.Inc e a
  | Sum.inr e, Sum.inl a => e ∈ S ∧ G.Inc e a
  | Sum.inr _, Sum.inr _ => False

/-- The simple adjacency graph of the augmentation. -/
def incidenceAugmentSimpleGraph {α : Type u} {β : Type v} (G : Graph α β) (S : Set β) :
    SimpleGraph (α ⊕ β) where
  Adj := incidenceAugmentAdj G S
  symm := ⟨by
    intro a b h
    rcases a with a | e <;> rcases b with b | f
    · exact ⟨h.1.symm, h.2.symm⟩
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨by
    intro a h
    rcases a with a | e
    · exact h.1 rfl
    · exact h⟩

/-- The augmentation, with only actual old vertices and selected edge vertices retained. -/
def incidenceAugment {α : Type u} {β : Type v} (G : Graph α β) (S : Set β) :
    Graph (α ⊕ β) (Sym2 (α ⊕ β)) :=
  (Graph.ofSimpleGraph (incidenceAugmentSimpleGraph G S)).induce (incidenceAugmentVertices G S)

/-- Links in an induced simple graph have their canonical unordered edge name. -/
theorem ofSimpleGraph_induce_isLink_iff {A : Type*} (F : SimpleGraph A) (X : Set A)
    (e : Sym2 A) (a b : A) :
    ((Graph.ofSimpleGraph F).induce X).IsLink e a b ↔
      e = s(a, b) ∧ a ∈ X ∧ b ∈ X ∧ F.Adj a b := by
  rw [Graph.induce_isLink, Graph.ofSimpleGraph_isLink]
  constructor
  · rintro ⟨⟨rfl, he⟩, ha, hb⟩
    exact ⟨rfl, ha, hb, by simpa using he⟩
  · rintro ⟨rfl, ha, hb, hab⟩
    exact ⟨⟨rfl, by simpa using hab⟩, ha, hb⟩

/-- The augmentation's links use its explicit adjacency and vertex set. -/
theorem incidenceAugment_isLink_iff {α : Type u} {β : Type v} (G : Graph α β) (S : Set β)
    (e : Sym2 (α ⊕ β)) (a b : α ⊕ β) :
    (incidenceAugment G S).IsLink e a b ↔ e = s(a, b) ∧
      a ∈ incidenceAugmentVertices G S ∧ b ∈ incidenceAugmentVertices G S ∧
      incidenceAugmentAdj G S a b :=
  ofSimpleGraph_induce_isLink_iff _ _ _ _ _

end GraphMinor.GM02
