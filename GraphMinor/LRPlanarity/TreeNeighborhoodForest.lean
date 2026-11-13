module

public import GraphMinor.LRPlanarity.Defs
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Forest facts for the leaf attachment order

Part IV, Section 7b of the planarity note builds the neighborhood one leaf
at a time. Along a parent edge the search depth increases by one. Hence
ancestor paths increase depth, every vertex has a root ancestor, and a
maximum-depth descendant has no child. These facts justify the finite
rooted-tree order used by the geometric construction.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Search depth cannot decrease along an ancestor path. -/
theorem ancestor_depth_le {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v) : T.depth u ≤ T.depth v := by
  induction h with
  | refl => exact le_rfl
  | @tail w v hpath hparent ih =>
    rw [(hT.2.1 w v hparent).2]
    exact ih.trans (Nat.le_succ _)

/-- Search depth strictly increases between distinct comparable vertices. -/
theorem strict_ancestor_depth_lt {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) {u v : Fin N} (h : T.Ancestor u v) (hne : u ≠ v) :
    T.depth u < T.depth v := by
  cases h with
  | refl => exact (hne rfl).elim
  | @tail w v hpath hparent =>
    rw [(hT.2.1 w v hparent).2]
    exact (ancestor_depth_le hT hpath).trans_lt (Nat.lt_succ_self _)

/-- Every search vertex is below a root. Recursing to its parent strictly
reduces its depth. -/
theorem exists_root_ancestor {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (v : Fin N) :
    ∃ root, T.parent root = none ∧ T.Ancestor root v := by
  suffices ∀ n, ∀ v : Fin N, T.depth v = n →
      ∃ root, T.parent root = none ∧ T.Ancestor root v by
    exact this _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv
    cases hparent : T.parent v with
    | none => exact ⟨v, hparent, Relation.ReflTransGen.refl⟩
    | some u =>
      have hdepth := (hT.2.1 u v hparent).2
      have hlt : T.depth u < n := by
        rw [← hv, hdepth]
        exact Nat.lt_succ_self _
      obtain ⟨root, hroot, hanc⟩ := ih _ hlt u rfl
      exact ⟨root, hroot, hanc.tail hparent⟩

/-- Part IV, Section 7b: a maximum-depth descendant supplies a leaf for the
finite leaf-attachment induction. -/
theorem exists_maximal_depth_leaf {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (root : Fin N) :
    ∃ leaf, T.Ancestor root leaf ∧ ∀ w, T.parent w ≠ some leaf := by
  classical
  obtain ⟨leaf, hleaf, hmax⟩ := Set.exists_min_image (β := ℕᵒᵈ) {v | T.Ancestor root v} (fun v => (T.depth v : ℕᵒᵈ))
    (Set.toFinite _) ⟨root, Relation.ReflTransGen.refl⟩
  refine ⟨leaf, hleaf, ?_⟩
  intro w hparent
  have hrootw : T.Ancestor root w := hleaf.tail hparent
  have hle := hmax w hrootw
  change T.depth w ≤ T.depth leaf at hle
  rw [(hT.2.1 leaf w hparent).2] at hle
  exact Nat.not_succ_le_self _ hle

end GraphMinor.LRPlanarity
