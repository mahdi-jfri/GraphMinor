module

public import GraphMinor.HP25.Defs
public import GraphMinor.HP25.Web
import GraphMinor.HP25.CycleEdges

/-!
# From two disjoint paths to a crossing of a cycle

Humeau and Pous, Section 1.2 (pages 3–4), solve the two disjoint paths problem through the
following problem, for "a tuple $T$ of at least three vertices in a graph $G$": "TWO DISJOINT
PATHS OR WEB COMPLETION", with "**Input:** A graph with a tuple of distinct vertices." and
"**Output:** A crossing or a web completion." Section 5.1 (page 15) adds the edges between consecutive entries of the tuple:
"the edges $x_ix_{i+1}$ ($1\le i\le k-1$) and $x_kx_1$ are all safe for $T$ since they cannot be
used in a crossing. Hence we assume that $T$ induces a cycle $C$ in $G$."

For four distinct vertices `s₁, t₁, s₂, t₂` we take the tuple `T = s₁ s₂ t₁ t₂` and the graph
`G ⊔ frameGraph s₁ s₂ t₁ t₂`, which adds the four edges of the cycle `s₁ s₂ t₁ t₂ s₁`. We prove:
* `frame_isCycleList`: `T` is a cycle of the new graph;
* `isCrossed_of_paths`: two disjoint paths of `G`, from `s₁` to `t₁` and from `s₂` to `t₂`, form a
  crossing of `T` in the new graph;
* `exists_paths_of_isCrossing`: a crossing of `T` in the new graph is a pair of disjoint paths of
  `G` from `s₁` to `t₁` and from `s₂` to `t₂`, with the same vertex lists. A crossing of a tuple of
  length four joins its first entry to its third and its second to its fourth, and it uses no edge
  of the frame, since a `T`-path that uses an edge between two entries of `T` has these entries as
  its ends, and the ends of a crossing path are not consecutive.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {V : Type*}

/-- The four edges of the cycle `s₁ s₂ t₁ t₂ s₁`. -/
def frameGraph (s₁ s₂ t₁ t₂ : V) : SimpleGraph V :=
  edge s₁ s₂ ⊔ edge s₂ t₁ ⊔ edge t₁ t₂ ⊔ edge t₂ s₁

variable {G : SimpleGraph V} {s₁ t₁ s₂ t₂ : V}

/-- An edge of the frame joins two entries of `s₁ s₂ t₁ t₂` other than the pairs `s₁ t₁` and
`s₂ t₂`. -/
theorem frameGraph_adj {x y : V} (h : (frameGraph s₁ s₂ t₁ t₂).Adj x y) :
    x ≠ y ∧ ((x = s₁ ∧ y = s₂) ∨ (x = s₂ ∧ y = s₁) ∨ (x = s₂ ∧ y = t₁) ∨ (x = t₁ ∧ y = s₂) ∨
      (x = t₁ ∧ y = t₂) ∨ (x = t₂ ∧ y = t₁) ∨ (x = t₂ ∧ y = s₁) ∨ (x = s₁ ∧ y = t₂)) := by
  simp only [frameGraph, sup_adj, edge_adj] at h
  refine ⟨?_, ?_⟩ <;> rcases h with ((h | h) | h) | h <;> [exact h.2; exact h.2; exact h.2;
    exact h.2; skip; skip; skip; skip]
  · rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  · rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

/-- The tuple `s₁ s₂ t₁ t₂` is a cycle of `G ⊔ frameGraph s₁ s₂ t₁ t₂`. -/
theorem frame_isCycleList (h₁ : s₁ ≠ t₁) (h₂ : s₁ ≠ s₂) (h₃ : s₁ ≠ t₂) (h₄ : t₁ ≠ s₂)
    (h₅ : t₁ ≠ t₂) (h₆ : s₂ ≠ t₂) :
    IsCycleList (G ⊔ frameGraph s₁ s₂ t₁ t₂) [s₁, s₂, t₁, t₂] := by
  refine ⟨by simp, by simp [*, Ne.symm h₄], ?_⟩
  intro p hp
  have hrot : [s₁, s₂, t₁, t₂].rotate 1 = [s₂, t₁, t₂, s₁] := rfl
  rw [hrot] at hp
  simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  simp only [frameGraph, sup_adj, edge_adj]
  rcases hp with rfl | rfl | rfl | rfl <;>
    simp [*, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₄, Ne.symm h₅, Ne.symm h₆]

/-- Two disjoint paths of `G`, from `s₁` to `t₁` and from `s₂` to `t₂`, form a crossing of
`s₁ s₂ t₁ t₂` in `G ⊔ frameGraph s₁ s₂ t₁ t₂`. -/
theorem isCrossing_of_paths {P₁ : G.Walk s₁ t₁} {P₂ : G.Walk s₂ t₂} (hP₁ : P₁.IsPath)
    (hP₂ : P₂.IsPath) (hd : List.Disjoint P₁.support P₂.support) :
    IsCrossing (G ⊔ frameGraph s₁ s₂ t₁ t₂) [s₁, s₂, t₁, t₂] (P₁.mapLe le_sup_left)
      (P₂.mapLe le_sup_left) := by
  have hs₂ : s₂ ∉ P₁.support := fun h => hd h P₂.start_mem_support
  have ht₂ : t₂ ∉ P₁.support := fun h => hd h P₂.end_mem_support
  have hs₁ : s₁ ∉ P₂.support := fun h => hd P₁.start_mem_support h
  have ht₁ : t₁ ∉ P₂.support := fun h => hd P₁.end_mem_support h
  refine ⟨⟨0, 1, 2, 3, by omega, by omega, by omega, rfl, rfl, rfl, rfl⟩, ⟨hP₁.mapLe _, by simp,
    by simp, ?_⟩, ⟨hP₂.mapLe _, by simp, by simp, ?_⟩, ?_⟩
  · intro x hx hxs hxt
    rw [support_mapLe] at hx
    have : x ≠ s₂ := fun e => hs₂ (e ▸ hx)
    have : x ≠ t₂ := fun e => ht₂ (e ▸ hx)
    simp_all
  · intro x hx hxs hxt
    rw [support_mapLe] at hx
    have : x ≠ s₁ := fun e => hs₁ (e ▸ hx)
    have : x ≠ t₁ := fun e => ht₁ (e ▸ hx)
    simp_all
  · simpa [support_mapLe] using hd

/-- A path of `G ⊔ frameGraph s₁ s₂ t₁ t₂` that is a `T`-path for `T = s₁ s₂ t₁ t₂` and whose ends
are not joined by an edge of the frame uses no edge of the frame, so it is a path of `G` with the
same vertex list. -/
theorem exists_walk_of_tPath {x y : V} {p : (G ⊔ frameGraph s₁ s₂ t₁ t₂).Walk x y}
    (hp : IsTPath (G ⊔ frameGraph s₁ s₂ t₁ t₂) [s₁, s₂, t₁, t₂] p)
    (hxy : ¬ (frameGraph s₁ s₂ t₁ t₂).Adj x y) :
    ∃ q : G.Walk x y, q.IsPath ∧ q.support = p.support := by
  have hsub : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
    intro e hep
    induction e using Sym2.ind with
    | _ u v =>
      have hadj := p.adj_of_mem_edges hep
      rcases (sup_adj _ _ _ _).1 hadj with h | h
      · exact h
      · exfalso
        obtain ⟨huv, hcases⟩ := frameGraph_adj h
        have hu : u ∈ [s₁, s₂, t₁, t₂] := by
          rcases hcases with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
            ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
        have hv : v ∈ [s₁, s₂, t₁, t₂] := by
          rcases hcases with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
            ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
        rcases ends_of_mem_edges hp hep hu hv huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy h
        · exact hxy h.symm
  exact ⟨p.transfer G hsub, hp.1.transfer hsub, Walk.support_transfer _ _⟩

/-- A crossing of `s₁ s₂ t₁ t₂` in `G ⊔ frameGraph s₁ s₂ t₁ t₂` joins `s₁` to `t₁` and `s₂` to
`t₂`, and it gives two disjoint paths of `G` with the same vertex lists. -/
theorem exists_paths_of_isCrossing (h₁ : s₁ ≠ t₁) (h₂ : s₁ ≠ s₂) (h₃ : s₁ ≠ t₂) (h₄ : t₁ ≠ s₂)
    (h₅ : t₁ ≠ t₂) {a b c d : V}
    {Q : (G ⊔ frameGraph s₁ s₂ t₁ t₂).Walk a b} {R : (G ⊔ frameGraph s₁ s₂ t₁ t₂).Walk c d}
    (h : IsCrossing (G ⊔ frameGraph s₁ s₂ t₁ t₂) [s₁, s₂, t₁, t₂] Q R) :
    ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂), P₁.IsPath ∧ P₂.IsPath ∧
      List.Disjoint P₁.support P₂.support ∧
      P₁.support.map id = Q.support ∧ P₂.support.map id = R.support := by
  obtain ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hd⟩ := h
  have hslt : s < 4 := (List.getElem?_eq_some_iff.1 hs).1
  obtain rfl : i = 0 := by omega
  obtain rfl : r = 1 := by omega
  obtain rfl : j = 2 := by omega
  obtain rfl : s = 3 := by omega
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hr hj hs
  subst hi hr hj hs
  obtain ⟨q₁, hq₁, hs₁⟩ := exists_walk_of_tPath hQ fun hf => by
    obtain ⟨-, hc⟩ := frameGraph_adj hf
    rcases hc with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ |
      ⟨h, h'⟩ <;> simp_all
  obtain ⟨q₂, hq₂, hs₂⟩ := exists_walk_of_tPath hR fun hf => by
    obtain ⟨-, hc⟩ := frameGraph_adj hf
    rcases hc with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ |
      ⟨h, h'⟩ <;> simp_all
  exact ⟨q₁, q₂, hq₁, hq₂, by rw [hs₁, hs₂]; exact hd, by simp [hs₁], by simp [hs₂]⟩

/-- **The reduction of Section 1.2.** For four distinct vertices, `G` has two disjoint paths from
`s₁` to `t₁` and from `s₂` to `t₂` exactly when `s₁ s₂ t₁ t₂` is crossed in
`G ⊔ frameGraph s₁ s₂ t₁ t₂`. -/
theorem isCrossed_frame_iff (h₁ : s₁ ≠ t₁) (h₂ : s₁ ≠ s₂) (h₃ : s₁ ≠ t₂) (h₄ : t₁ ≠ s₂)
    (h₅ : t₁ ≠ t₂) :
    IsCrossed (G ⊔ frameGraph s₁ s₂ t₁ t₂) [s₁, s₂, t₁, t₂] ↔
      ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂), P₁.IsPath ∧ P₂.IsPath ∧
        List.Disjoint P₁.support P₂.support := by
  constructor
  · rintro ⟨a, b, c, d, Q, R, h⟩
    obtain ⟨P₁, P₂, hP₁, hP₂, hd, -⟩ := exists_paths_of_isCrossing h₁ h₂ h₃ h₄ h₅ h
    exact ⟨P₁, P₂, hP₁, hP₂, hd⟩
  · rintro ⟨P₁, P₂, hP₁, hP₂, hd⟩
    exact ⟨_, _, _, _, _, _, isCrossing_of_paths hP₁ hP₂ hd⟩

end GraphMinor.Compute.TwoPaths
