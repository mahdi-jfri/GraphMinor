module

public import GraphMinor.GM05.ConnectedTransfer
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Retaining edge counts when taking shadows

Parallel edges may disappear in a shadow, so edge-disjointness need not
survive. Instead, bound the sum of the shadows' neighbor counts by the
number of distinct incident edges of the host. Leaves with valency one
remain leaves of the shadow.
-/

@[expose] public section
namespace GraphMinor.GM05.Full
open Graph Set SimpleGraph
variable {α β : Type*}

/-- Valency counts each nonloop edge once and each loop twice, as used in
Graph Minors V (4.2), page 97. -/
noncomputable def valency (G : Graph α β) (x : α) : ℕ :=
  {e | G.Inc e x}.ncard + {e | G.IsLoopAt e x}.ncard

/-- A vertex of valency one, as in Graph Minors V (4.2), page 97.
Its sole incident edge is not a loop and has a unique other end. -/
def IsLeafOf (G : Graph α β) (x : α) : Prop :=
  ∃ e y, x ≠ y ∧ G.IsLink e x y ∧
    ∀ f z, G.IsLink f x z → f = e ∧ z = y

/-- A vertex of valency one stays a leaf after taking the shadow. -/
theorem IsLeafOf.shadow {G : Graph α β} {x : α} (h : IsLeafOf G x) :
    GM01.IsLeafOf (simpleShadow G) x := by
  obtain ⟨e, y, hne, hlink, hall⟩ := h
  refine ⟨hlink.left_mem, ?_⟩
  have heq : (simpleShadow G).neighborSet x = {y} := by
    ext z
    change (x ≠ z ∧ G.Adj x z) ↔ z = y
    constructor
    · rintro ⟨_, f, hf⟩
      exact (hall f z hf).2
    · rintro rfl
      exact ⟨hne, e, hlink⟩
  rw [heq, Set.ncard_singleton]

/-- Distinct edges used by edge-disjoint subgraphs pay for all their
shadow neighbors. This is the valency counting step of V (4.2), page 97. -/
theorem sum_shadow_neighbors_le_valency {G : Graph α β} {n : ℕ}
    (hV : V(G).Finite) (hE : E(G).Finite) (B : Fin n → Graph α β)
    (hle : ∀ j, B j ≤ G)
    (hd : Pairwise fun i j => Disjoint E(B i) E(B j)) (x : α) :
    ∑ j : Fin n, ((simpleShadow (B j)).neighborSet x).ncard ≤ valency G x := by
  classical
  let N : Fin n → Set α := fun j => (simpleShadow (B j)).neighborSet x
  have hN : ∀ j, (N j).Finite := fun j => hV.subset (by
    intro y hy
    exact (hle j).vertexSet_mono hy.2.right_mem)
  letI : ∀ j, Fintype (N j) := fun j => (hN j).fintype
  let I : Set β := {e | G.Inc e x}
  have hI : I.Finite := hE.subset (fun e he => he.edge_mem)
  letI : Fintype I := hI.fintype
  have hex : ∀ p : (Σ j : Fin n, N j), ∃ e, (B p.1).IsLink e x p.2.val := by
    intro p
    exact p.2.property.2
  choose f hf using hex
  let F : (Σ j : Fin n, N j) → I :=
    fun p => ⟨f p, ((hf p).mono (hle p.1)).inc_left⟩
  have hinj : Function.Injective F := by
    intro p q hpq
    have heq : f p = f q := congrArg Subtype.val hpq
    have hj : p.1 = q.1 := by
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) (hf p).edge_mem (heq.symm ▸ (hf q).edge_mem)
    cases p with
    | mk i y =>
      cases q with
      | mk j z =>
        dsimp only at hj
        subst j
        have hyz : y.val = z.val :=
          ((hf ⟨i, y⟩).mono (hle i)).right_unique
            (heq.symm ▸ (hf ⟨i, z⟩).mono (hle i))
        exact congrArg (Sigma.mk i) (Subtype.ext hyz)
  have hcard := Fintype.card_le_of_injective F hinj
  have hsum : Fintype.card (Σ j : Fin n, N j) =
      ∑ j : Fin n, (N j).ncard := by
    rw [Fintype.card_sigma]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hsum] at hcard
  have hi : Fintype.card I = I.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hi] at hcard
  exact hcard.trans (Nat.le_add_right _ _)

end GraphMinor.GM05.Full
