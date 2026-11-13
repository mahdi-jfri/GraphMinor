module

public import GraphMinor.GM02.SideRunDisjoint
public import GraphMinor.GM02.FeasiblePathSupport
import Mathlib.Basic.Finite.Sigma
import Mathlib.Data.Set.Card

/-!
# The finite family of side pieces of an original linkage

For the forward construction in corrected II (2.9), index each maximal
side run by its original pair and its dart list. Every piece is a
nontrivial simple path and stays on its original path. Distinct pieces
of equal side color are vertex-disjoint, either by disjointness of the
original linkage or by the run-disjointness lemma within one path.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)

/-- A side piece is an original pair together with one maximal side run. -/
abbrev RunPieceIndex := Σ p : {p // p ∈ A.pairs},
  {r // r ∈ sideRuns H (P p).walk}

/-- There are finitely many original pairs and finitely many runs per path. -/
instance finite_runPieceIndex : Finite (RunPieceIndex A G H P) := by
  let _ (p : {p // p ∈ A.pairs}) : Finite {r // r ∈ sideRuns H (P p).walk} := by
    have hf : {r | r ∈ sideRuns H (P p).walk}.Finite :=
      ((sideRuns H (P p).walk).toFinset.finite_toSet).subset
        (fun _ hr => List.mem_toFinset.2 hr)
    exact hf.to_subtype
  exact inferInstance

/-- The side color of a piece. -/
noncomputable def RunPieceIndex.color (i : RunPieceIndex A G H P) : Bool :=
  separationEdgeColor H (i.2.val.head (coloredRun_ne_nil i.2.property))

/-- The prescribed endpoint pair of a side piece. -/
def RunPieceIndex.pair (i : RunPieceIndex A G H P) : Sym2 α :=
  s((i.2.val.head (coloredRun_ne_nil i.2.property)).fst,
    (i.2.val.getLast (coloredRun_ne_nil i.2.property)).snd)

/-- The actual path of a side piece. -/
noncomputable def RunPieceIndex.path (i : RunPieceIndex A G H P) :
    PairPath (pathGraph G) (i.pair A G H P) where
  start := (i.2.val.head (coloredRun_ne_nil i.2.property)).fst
  finish := (i.2.val.getLast (coloredRun_ne_nil i.2.property)).snd
  ends_eq := rfl
  walk := sideRunWalk (P i.1).walk i.2.val i.2.property
  isPath := sideRunWalk_isPath (P i.1).walk (P i.1).isPath i.2.val i.2.property

private theorem path_ends_ne {F : SimpleGraph α} {a b : α}
    (p : F.Walk a b) (hp : p.IsPath) (hn : ¬p.Nil) : a ≠ b := by
  intro hab
  subst b
  exact hn (Walk.isPath_iff_nil.1 hp)

/-- Every side piece has two different endpoints. -/
theorem RunPieceIndex.pair_not_diag (i : RunPieceIndex A G H P) :
    ¬(i.pair A G H P).IsDiag := by
  apply mt Sym2.mk_isDiag_iff.1
  exact path_ends_ne _ (sideRunWalk_isPath _ (P i.1).isPath _ i.2.property)
    (sideRunWalk_not_nil _ _ i.2.property)

/-- A piece stays within the original path from which it was cut. -/
theorem RunPieceIndex.vertices_subset (i : RunPieceIndex A G H P) :
    (i.path A G H P).vertices ⊆ (P i.1).vertices :=
  (sideRunWalk_isSubwalk (P i.1).walk i.2.val i.2.property).support_subset

/-- Distinct equal-color pieces of a feasible original family are disjoint. -/
theorem RunPieceIndex.same_color_disjoint
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
    (i j : RunPieceIndex A G H P) (hne : i ≠ j)
    (hc : i.color A G H P = j.color A G H P) :
    Disjoint (i.path A G H P).vertices (j.path A G H P).vertices := by
  by_cases hpq : i.1 = j.1
  · rcases i with ⟨p, r⟩
    rcases j with ⟨q, s⟩
    change p = q at hpq
    subst q
    have hrs : r.val ≠ s.val := by
      intro heq
      have hsub : r = s := Subtype.ext heq
      exact hne (congrArg (fun t => (⟨p, t⟩ : RunPieceIndex A G H P)) hsub)
    exact sideRunWalk_same_color_disjoint (P p).walk (P p).isPath
      r.val s.val r.property s.property hrs hc
  · exact (hP i.1 j.1 hpq).mono (i.vertices_subset A G H P) (j.vertices_subset A G H P)

end GraphMinor.GM02
