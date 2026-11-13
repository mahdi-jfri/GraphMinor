module

public import GraphMinor.GM01.FullPaths

/-!
# Actual-edge path families and vertex separators

Every shadow path lifts to an actual-edge path with the same vertex sequence.
This transfers separation in both directions. Lifting each competitor also
shows that uniqueness of actual-edge families implies uniqueness in the
shadow. The reverse uniqueness implication is neither used nor asserted.
-/

@[expose] public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- Paths from one set to another, Graph Minors I, Section 1, page 41. -/
def Path.IsFromTo (P : Path α β) (G : Graph α β) (A B : Set α) : Prop :=
  P.IsIn G ∧ P.toPath.first ∈ A ∧ P.toPath.last ∈ B

/-- Disjoint actual-edge paths, Graph Minors I, Section 2, page 44. -/
def IsDisjointPathFamily (G : Graph α β) (A B : Set α)
    {m : ℕ} (P : Fin m → Path α β) : Prop :=
  (∀ i, (P i).IsFromTo G A B) ∧ Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts

/-- Uniqueness concerns the set of actual-edge paths, including the choice
of each parallel edge, Graph Minors I, (2.5), page 44. -/
def IsUniqueDisjointPathFamily (G : Graph α β) (A B : Set α)
    {m : ℕ} (P : Fin m → Path α β) : Prop :=
  IsDisjointPathFamily G A B P ∧
    ∀ Q : Fin m → Path α β, IsDisjointPathFamily G A B Q → Set.range Q = Set.range P

/-- A separator meets every actual-edge path between the two sets,
Graph Minors I, Section 1, page 41. -/
def Separates (G : Graph α β) (X A B : Set α) : Prop :=
  ∀ P : Path α β, P.IsFromTo G A B → ¬ Disjoint P.verts X

/-- Forgetting edge choices preserves a disjoint path family. -/
theorem IsDisjointPathFamily.shadow {G : Graph α β} {A B : Set α}
    {m : ℕ} {P : Fin m → Path α β} (h : IsDisjointPathFamily G A B P) :
    GM01.IsDisjointPathFamily (simpleShadow G) A B (fun i ↦ (P i).toPath) :=
  ⟨fun i ↦ ⟨Path.isIn_shadow (h.1 i).1, (h.1 i).2⟩, h.2⟩

/-- Every competing shadow family lifts, so uniqueness of actual-edge
families implies uniqueness of their vertex sequences. -/
theorem IsUniqueDisjointPathFamily.shadow {G : Graph α β} {A B : Set α}
    {m : ℕ} {P : Fin m → Path α β} (h : IsUniqueDisjointPathFamily G A B P) :
    GM01.IsUniqueDisjointPathFamily (simpleShadow G) A B (fun i ↦ (P i).toPath) := by
  classical
  refine ⟨h.1.shadow, ?_⟩
  intro Q hQ
  have hlift : ∀ i, ∃ R : Path α β, R.IsIn G ∧ R.toPath = Q i :=
    fun i ↦ Path.exists_lift (hQ.1 i).1
  choose R hR hRQ using hlift
  have hfam : IsDisjointPathFamily G A B R := by
    refine ⟨fun i ↦ ⟨hR i, ?_⟩, ?_⟩
    · rw [hRQ i]
      exact (hQ.1 i).2
    · intro i j hij
      change Disjoint (R i).toPath.verts (R j).toPath.verts
      rw [hRQ i, hRQ j]
      exact hQ.2 hij
  have heq := h.2 R hfam
  ext Q₀
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := heq ▸ (Set.mem_range_self i : R i ∈ Set.range R)
    exact ⟨j, (congrArg Path.toPath hj).trans (hRQ i)⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := heq.symm ▸ (Set.mem_range_self i : P i ∈ Set.range P)
    exact ⟨j, (hRQ j).symm.trans (congrArg Path.toPath hj)⟩

/-- Vertex separation is unchanged by taking the shadow. -/
theorem separates_iff {G : Graph α β} {X A B : Set α} :
    Separates G X A B ↔ GM01.Separates (simpleShadow G) X A B := by
  constructor
  · intro h P hP
    obtain ⟨Q, hQ, hQP⟩ := Path.exists_lift hP.1
    have hsep := h Q ⟨hQ, hQP.symm ▸ hP.2⟩
    simpa only [Path.verts, hQP, GM01.Path.Avoids] using hsep
  · intro h P hP
    exact h P.toPath ⟨Path.isIn_shadow hP.1, hP.2⟩

end GraphMinor.GM01.Full
