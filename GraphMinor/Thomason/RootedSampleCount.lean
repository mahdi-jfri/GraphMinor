module

public import GraphMinor.Thomason.OneMissedSamples
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Counting rooted samples with one exceptional coordinate

For each possible root, fix an exceptional set of the same size. Split
the sample into its root and tail. The one-exception formula counts each
tail, and summing over roots gives the total candidate count.
-/

@[expose] public section
namespace GraphMinor.Thomason
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The tail has at most one exceptional coordinate relative to its root. -/
def rootedOneBadSamples (A : V → Finset V) (m : ℕ) : Finset (Fin (m + 1) → V) :=
  univ.filter (fun f => Fin.tail f ∈ oneBadSamples (A (f 0)) m)

private theorem rootedOneBadSamples_eq_image (A : V → Finset V) (m : ℕ) :
    rootedOneBadSamples A m =
      ((univ : Finset (V × (Fin m → V))).filter (fun p => p.2 ∈ oneBadSamples (A p.1) m)).image
        (fun p => Fin.cons p.1 p.2) := by
  ext f
  obtain ⟨⟨a, g⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (m + 1) => V)).surjective f
  change (Fin.cons a g : Fin (m + 1) → V) ∈ _ ↔ (Fin.cons a g : Fin (m + 1) → V) ∈ _
  constructor
  · intro hf
    have hg : g ∈ oneBadSamples (A a) m := by
      simpa only [rootedOneBadSamples, mem_filter, mem_univ, true_and,
        Fin.tail_cons, Fin.cons_zero] using hf
    exact mem_image.mpr ⟨(a, g), mem_filter.mpr ⟨mem_univ _, hg⟩, rfl⟩
  · intro hf
    obtain ⟨⟨b, h⟩, hmem, heq⟩ := mem_image.mp hf
    obtain ⟨hab, hhg⟩ := Fin.cons_inj.mp heq
    change b = a at hab
    change h = g at hhg
    subst b
    subst h
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    simpa only [Fin.tail_cons, Fin.cons_zero] using (mem_filter.mp hmem).2

private theorem card_root_tail_pairs (A : V → Finset V) (m : ℕ) :
    ((univ : Finset (V × (Fin m → V))).filter (fun p => p.2 ∈ oneBadSamples (A p.1) m)).card =
      ∑ a : V, (oneBadSamples (A a) m).card := by
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  simp only [sum_ite_mem, univ_inter]
  simp

/-- Constant-size exceptional sets give an exact count of rooted
samples that contain at most one exceptional tail coordinate. -/
theorem card_rootedOneBadSamples (A : V → Finset V) (m D : ℕ)
    (hA : ∀ a, (A a).card = D) :
    (rootedOneBadSamples A m).card = Fintype.card V *
      ((Fintype.card V - D) ^ m + m * D * (Fintype.card V - D) ^ (m - 1)) := by
  have hinj : Function.Injective (fun p : V × (Fin m → V) => (Fin.cons p.1 p.2 : Fin (m + 1) → V)) :=
    (Fin.consEquiv (fun _ : Fin (m + 1) => V)).injective
  rw [rootedOneBadSamples_eq_image, card_image_of_injective _ hinj, card_root_tail_pairs]
  simp [card_oneBadSamples, hA]

end GraphMinor.Thomason
