module

public import GraphMinor.GM09.Basic
public import GraphMinor.Minor.Model
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.GM13.Section7WallModel

/-!
# The minor carried by a finite subdivision

The tail assertion in Graph Minors I, (4.1), page 55, retains an ordinary
comb minor inside a subdivision. We apply the proved construction from
`GM13.exists_isMinorModel_of_paths`: orient source edges by an injective
rank, retain all but the last edge of each replacing path in its earlier
branch, and use that last edge as the model edge. Here the paths are
indexed by actual source edges, so we extend them to unused labels and
supply the finite source rank explicitly.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- A finite simple source has an ordinary model in its subdivision.
This is the proved rank-oriented path contraction from GM13, applied to
the edge-indexed path data used in the proof of GM01 (4.1). -/
theorem exists_minorModel_of_finite_subdivision {α β ν : Type*} [Finite ν] [Nonempty β]
    {S : SimpleGraph ν} {G : Graph α β} (c : ν → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(G)) (P : S.edgeSet → Graph α β)
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f)) :
    ∃ (ηv : ν → Set α) (ηe : Sym2 ν → β),
      IsMinorModel (Graph.ofSimpleGraph S) G ηv ηe ∧
      ∀ e : S.edgeSet, ηe e.val ∈ E(P e) := by
  classical
  let : Fintype ν := Fintype.ofFinite ν
  let rk : ν → ℕ := fun v ↦ (Fintype.equivFin ν v).val
  have hrk : Injective rk := fun _ _ heq ↦ (Fintype.equivFin ν).injective (Fin.ext heq)
  let paths (e : Sym2 ν) : Graph α β := if he : e ∈ S.edgeSet then P ⟨e, he⟩ else Graph.noEdge ∅ β
  have hp : ∀ a b, S.Adj a b → IsGraphPathWithEnds G (paths s(a,b)) (c a) (c b) := by
    intro a b hab
    have he : s(a,b) ∈ S.edgeSet := hab
    simp only [paths, he, ↓reduceDIte]
    obtain ⟨a', b', heq, hPath, _⟩ := hPaths ⟨s(a,b), he⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hPath
    · exact hPath.symm
  have hpc : ∀ a b, S.Adj a b → V(paths s(a,b)) ∩ range c ⊆ {c a,c b} := by
    intro a b hab
    have he : s(a,b) ∈ S.edgeSet := hab
    simp only [paths, he, ↓reduceDIte]
    obtain ⟨a', b', heq, _, hRange⟩ := hPaths ⟨s(a,b), he⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hRange.subset
    · simpa only [pair_comm] using hRange.subset
  have hpv : ∀ e ∈ S.edgeSet, ∀ f ∈ S.edgeSet, e ≠ f →
      V(paths e) ∩ V(paths f) ⊆ range c := by
    intro e he f hf hne
    simpa only [paths, he, hf, ↓reduceDIte] using
      (hInter ⟨e, he⟩ ⟨f, hf⟩ (fun h ↦ hne (congrArg Subtype.val h))).1
  have hpe : ∀ e ∈ S.edgeSet, ∀ f ∈ S.edgeSet, e ≠ f →
      Disjoint E(paths e) E(paths f) := by
    intro e he f hf hne
    simpa only [paths, he, hf, ↓reduceDIte] using
      (hInter ⟨e, he⟩ ⟨f, hf⟩ (fun h ↦ hne (congrArg Subtype.val h))).2
  obtain ⟨ηv, ηe, hmodel, hchosen⟩ :=
    GraphMinor.GM13.exists_isMinorModel_of_paths rk hrk c hc hcentres paths hp hpc hpv hpe
  refine ⟨ηv, ηe, hmodel, ?_⟩
  intro e
  simpa only [paths, e.property, ↓reduceDIte] using hchosen e.val e.property

end GraphMinor.GM01
