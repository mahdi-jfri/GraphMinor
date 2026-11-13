module

public import GraphMinor.Minor.Basic
import GraphMinor.GM02.PlanarWidthWitness
import Mathlib.Data.Fintype.Sets

/-!
# Finite lists of bounded graph patterns

The finite-pattern argument for II (4.8) needs only finitely many graphs of
bounded vertex and edge counts, up to isomorphism. Number the actual vertices
and edges independently, obtaining a graph on `Fin n` and `Fin m`. There are
finitely many such graphs for fixed bounds, since a graph is determined by
its vertex set and its incidence relation. Choose one numbered copy of each.
-/

public section

namespace GraphMinor.GM02

open Graph Set

/-- A graph with finite vertex and edge sets has a presentation on the two
finite types of those cardinalities. The isomorphism numbers the actual
vertices and edges independently. Isolated vertices and loops are kept. -/
theorem exists_fin_presentation {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    ∃ K : Graph (Fin V(G).ncard) (Fin E(G).ncard), Nonempty (Iso G K) := by
  classical
  let : Fintype V(G) := hV.fintype
  let : Fintype E(G) := hE.fintype
  let a : V(G) ≃ Fin V(G).ncard :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq])
  let b : E(G) ≃ Fin E(G).ncard :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq])
  let K : Graph (Fin V(G).ncard) (Fin E(G).ncard) := {
    vertexSet := Set.univ
    edgeSet := Set.univ
    IsLink := fun e x y => G.IsLink (b.symm e).val (a.symm x).val (a.symm y).val
    isLink_symm := by
      intro e _
      exact ⟨fun _ _ h => h.symm⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y z w h h'
      rcases h.left_eq_or_eq h' with heq | heq
      · exact Or.inl (a.symm.injective (Subtype.ext heq))
      · exact Or.inr (a.symm.injective (Subtype.ext heq))
    edge_mem_iff_exists_isLink := by
      intro e
      constructor
      · intro _
        obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet (b.symm e).property
        refine ⟨a ⟨x, hxy.left_mem⟩, a ⟨y, hxy.right_mem⟩, ?_⟩
        simpa only [Equiv.symm_apply_apply] using hxy
      · intro _
        trivial
    left_mem_of_isLink := fun _ _ _ _ => trivial }
  refine ⟨K, ⟨{
    vertexEquiv := a.trans (Equiv.Set.univ _).symm
    edgeEquiv := b.trans (Equiv.Set.univ _).symm
    isLink_iff := ?_ }⟩⟩
  intro e x y
  change G.IsLink e.val x.val y.val ↔
    G.IsLink (b.symm (b e)).val (a.symm (a x)).val (a.symm (a y)).val
  simp only [Equiv.symm_apply_apply]

private theorem finite_graph_type (α β : Type) [Finite α] [Finite β] : Finite (Graph α β) := by
  classical
  let code : Graph α β → Set α × (β → α → α → Prop) := fun G => (V(G), G.IsLink)
  apply Finite.of_injective code
  intro G H h
  apply Graph.ext (congrArg Prod.fst h)
  intro e a b
  have hc := congrArg (fun p : Set α × (β → α → α → Prop) => p.2 e a b) h
  exact iff_of_eq hc

/-- There are finitely many graph patterns of bounded vertex and edge
counts up to isomorphism. Each representative uses the recognition
program's standard vertex and edge types. No algorithmic input is involved
in this choice of a finite list. -/
theorem exists_finset_iso_cover (N M : ℕ) :
    ∃ B : Finset (Graph ℕ (ℕ × ℕ × ℕ)),
      ∀ {α β : Type*} (G : Graph α β), V(G).Finite → E(G).Finite →
        V(G).ncard ≤ N → E(G).ncard ≤ M →
          ∃ H ∈ B, Nonempty (Iso G H) := by
  classical
  let Code := Σ n : Fin (N + 1), Σ m : Fin (M + 1), Graph (Fin n.val) (Fin m.val)
  let : ∀ n : Fin (N + 1), ∀ m : Fin (M + 1), Finite (Graph (Fin n.val) (Fin m.val)) :=
    fun n m => finite_graph_type _ _
  let : Fintype Code := Fintype.ofFinite Code
  let rep : Code → Graph ℕ (ℕ × ℕ × ℕ) := fun c => (exists_numbered_iso c.2.2).choose
  have hrep : ∀ c : Code, Nonempty (Iso c.2.2 (rep c)) :=
    fun c => (exists_numbered_iso c.2.2).choose_spec
  refine ⟨Finset.univ.image rep, ?_⟩
  intro α β G hV hE hN hM
  obtain ⟨K, ⟨φ⟩⟩ := exists_fin_presentation G hV hE
  let c : Code := ⟨⟨V(G).ncard, Nat.lt_succ_of_le hN⟩,
    ⟨E(G).ncard, Nat.lt_succ_of_le hM⟩, K⟩
  obtain ⟨ψ⟩ := hrep c
  exact ⟨rep c, Finset.mem_image_of_mem rep (Finset.mem_univ c), ⟨φ.trans ψ⟩⟩

end GraphMinor.GM02
