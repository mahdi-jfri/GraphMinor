module

public import GraphMinor.Thomason.OneMissedSamples
public import GraphMinor.Thomason.RootConnection
import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega

/-!
# Connecting a sample with at most one vertex missed by its root

The root is one of the selected vertices. Every vertex of the sample
missed by the root must occur at an exceptional coordinate of its tail.
The coordinate count therefore bounds the actual missed vertices, even
when values repeat. One common neighbour suffices if this count is at
most one.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Adding the first coordinate adds its value to the sample's vertex set. -/
theorem sampleVertices_cons {m : ℕ} (a : V) (f : Fin m → V) :
    sampleVertices (Fin.cons a f) = insert a (sampleVertices f) := by
  ext v
  simp [sampleVertices, Fin.exists_fin_succ, eq_comm]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each selected vertex missed by the root is the value of an
exceptional coordinate. Repeated coordinates do not increase this count. -/
theorem card_missed_by_root_sample_le (a : V) {m : ℕ} (f : Fin m → V) (A : Finset V)
    (hA : undominatedVertices G {a} ⊆ A) :
    (sampleVertices (Fin.cons a f) ∩ undominatedVertices G {a}).card ≤
      (sampleBadPositions A f).card := by
  have hsub : sampleVertices (Fin.cons a f) ∩ undominatedVertices G {a} ⊆
      (sampleBadPositions A f).image f := by
    intro y hy
    obtain ⟨hyY, hymiss⟩ := mem_inter.mp hy
    rw [sampleVertices_cons] at hyY
    rcases mem_insert.mp hyY with heq | hyf
    · subst y
      have hnot : a ∉ undominatedVertices G {a} := by
        simp [undominatedVertices, dominatedVertices_singleton]
      exact (hnot hymiss).elim
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hyf
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hA hymiss⟩, rfl⟩
  exact (card_le_card hsub).trans card_image_le

/-- A rooted sample with at most one exceptional tail coordinate extends
to a connected vertex set by adding at most one vertex. -/
theorem exists_connected_oneMissed_sample (a : V) {m : ℕ} (f : Fin m → V) (A : Finset V)
    (hA : undominatedVertices G {a} ⊆ A) (hf : f ∈ oneBadSamples A m)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1) :
    ∃ X : Finset V, sampleVertices (Fin.cons a f) ⊆ X ∧ X.card ≤ m + 2 ∧
      (G.induce (X : Set V)).Connected := by
  let Y := sampleVertices (Fin.cons a f)
  have hroot : a ∈ Y := by
    rw [show Y = insert a (sampleVertices f) from sampleVertices_cons a f]
    exact mem_insert_self _ _
  obtain ⟨Z, hZcard, hconn⟩ := exists_connecting_set_from_root G Y a hroot hnear
  have hbad : (Y ∩ undominatedVertices G {a}).card ≤ 1 :=
    (card_missed_by_root_sample_le G a f A hA).trans (mem_filter.mp hf).2
  refine ⟨Y ∪ Z, subset_union_left, ?_, hconn⟩
  have hYcard : Y.card ≤ m + 1 := card_sampleVertices_le _
  exact (card_union_le _ _).trans (by omega)

end GraphMinor.Thomason
