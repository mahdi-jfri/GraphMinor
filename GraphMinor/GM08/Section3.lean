module

public import GraphMinor.GM08.Defs

/-!
# Graph Minors VIII, Section 3: Well-Quasi-Orders (pages 259–260)

This file formalizes Section 3 of N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- `theorem_3_1`: (3.1) (page 259), every countable sequence in a well-quasi-order has an infinite
  monotone subsequence $q_{i_1} \le q_{i_2} \le \dots$ ($i_1 < i_2 < \dots$).
- `theorem_3_2`: (3.2) (page 260), if $\mathbf{Q}_1$ and $\mathbf{Q}_2$ are well-quasi-orders, so is
  $\mathbf{Q}_1 \times \mathbf{Q}_2$.
- `theorem_3_3`: (3.3) (page 260, Higman's lemma), if $\mathbf{Q}$ is a well-quasi-order, so is
  $\mathbf{Q}^{<\omega}$.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation

universe u v

/-- Bridge between `IsWellQuasiOrder le` and Mathlib's `(univ : Set Q).PartiallyWellOrderedOn le`. -/
theorem partiallyWellOrderedOn_univ_iff_isWellQuasiOrder {Q : Type u} {le : Q → Q → Prop}
    (hqo : IsQuasiOrder le) :
    (univ : Set Q).PartiallyWellOrderedOn le ↔ IsWellQuasiOrder le := by
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
  refine ⟨fun h => ⟨hqo, fun q => ?_⟩, fun h f _ => ?_⟩
  · obtain ⟨i, j, hij, hle⟩ := h q (fun _ => mem_univ _)
    exact ⟨i, j, hij, hle⟩
  · exact h.2 f

/-- Every quasi-order `IsQuasiOrder le` provides an `IsPreorder Q le` instance. -/
theorem isPreorder_of_isQuasiOrder {Q : Type u} {le : Q → Q → Prop}
    (hqo : IsQuasiOrder le) : IsPreorder Q le where
  refl := hqo.1
  trans := hqo.2

/-- **Graph Minors VIII, (3.1)** (page 259):
"(3.1) *If $\mathbf{Q} = (Q, \le)$ is a well-quasi-order then every countable sequence
$q_1, q_2, \dots$ of members of $Q$ has a countable subsequence $q_{i_1}, q_{i_2}, \dots$ (where
$i_1 < i_2 < \dots$) such that $q_{i_1} \le q_{i_2} \le \dots$.*" -/
theorem theorem_3_1_proof {Q : Type u} {le : Q → Q → Prop}
    (hQ : IsWellQuasiOrder le) (q : ℕ → Q) :
    ∃ φ : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → le (q (φ m)) (q (φ n)) := by
  have : IsPreorder Q le := isPreorder_of_isQuasiOrder hQ.1
  have hpwo : (univ : Set Q).PartiallyWellOrderedOn le :=
    (partiallyWellOrderedOn_univ_iff_isWellQuasiOrder hQ.1).mpr hQ
  exact hpwo.exists_monotone_subseq (fun _ => mem_univ _)

/-- Consecutive-step formulation of **Graph Minors VIII, (3.1)** (page 259):
there exists a strictly increasing sequence $i_0 < i_1 < \dots$ such that $q_{i_k} \le q_{i_{k+1}}$
for all $k \in \mathbb{N}$ (and more generally $q_{i_m} \le q_{i_n}$ for all $m \le n$). -/
theorem theorem_3_1_consecutive {Q : Type u} {le : Q → Q → Prop}
    (hQ : IsWellQuasiOrder le) (q : ℕ → Q) :
    ∃ idx : ℕ → ℕ, StrictMono idx ∧ ∀ k : ℕ, le (q (idx k)) (q (idx (k + 1))) := by
  obtain ⟨φ, hφ⟩ := theorem_3_1_proof hQ q
  exact ⟨φ, φ.strictMono, fun k => hφ k (k + 1) (Nat.le_succ k)⟩

/-- **Graph Minors VIII, (3.2)** (page 260):
"(3.2) *If $\mathbf{Q}_1$ and $\mathbf{Q}_2$ are well-quasi-orders, so is
$\mathbf{Q}_1 \times \mathbf{Q}_2$.*" -/
theorem theorem_3_2_proof {Q₁ : Type u} {Q₂ : Type v}
    {le₁ : Q₁ → Q₁ → Prop} {le₂ : Q₂ → Q₂ → Prop}
    (hQ₁ : IsWellQuasiOrder le₁) (hQ₂ : IsWellQuasiOrder le₂) :
    IsWellQuasiOrder (prodLE le₁ le₂) := by
  refine ⟨⟨fun p => ⟨hQ₁.1.1 p.1, hQ₂.1.1 p.2⟩,
    fun p q r hpq hqr => ⟨hQ₁.1.2 p.1 q.1 r.1 hpq.1 hqr.1, hQ₂.1.2 p.2 q.2 r.2 hpq.2 hqr.2⟩⟩, ?_⟩
  intro seq
  obtain ⟨φ, hφ⟩ := theorem_3_1_proof hQ₁ (fun n => (seq n).1)
  obtain ⟨i, j, hij, hle₂⟩ := hQ₂.2 (fun n => (seq (φ n)).2)
  exact ⟨φ i, φ j, φ.strictMono hij, hφ i j hij.le, hle₂⟩

/-- **Graph Minors VIII, (3.3)** (page 260, Higman's lemma):
"(3.3) *If $\mathbf{Q}$ is a well-quasi-order then so is $\mathbf{Q}^{<\omega}$.*" -/
theorem theorem_3_3_proof {Q : Type u} {le : Q → Q → Prop}
    (hQ : IsWellQuasiOrder le) :
    IsWellQuasiOrder (seqLE le) := by
  have : IsPreorder Q le := isPreorder_of_isQuasiOrder hQ.1
  have hpreL : IsPreorder (List Q) (List.SublistForall₂ le) := ⟨⟩
  have hqo : IsQuasiOrder (seqLE le) := ⟨hpreL.refl, hpreL.trans⟩
  have hpwo : (univ : Set Q).PartiallyWellOrderedOn le :=
    (partiallyWellOrderedOn_univ_iff_isWellQuasiOrder hQ.1).mpr hQ
  have hpwoL := hpwo.partiallyWellOrderedOn_sublistForall₂
  refine ⟨hqo, fun q => ?_⟩
  rw [Set.partiallyWellOrderedOn_iff_exists_lt] at hpwoL
  obtain ⟨i, j, hij, hle⟩ := hpwoL q (fun _ _ _ => mem_univ _)
  exact ⟨i, j, hij, hle⟩

end GraphMinor.GM08
