module

public import GraphMinor.Compute.Cited
public import GraphMinor.Compute.Parse
public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.MultiDigraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# Graph Minors XIII, Algorithm (8.1) on the Word RAM

This file formalizes Algorithm (8.1) from Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110 (Section 8, page 93):

> **(8.1) Algorithm.**
> *Input:* A society $(G, \Omega)$.
> *Output:* A cross in $(G, \Omega)$ if one exists.
> *Running time:* $O(v\varepsilon)$.
>
> *Description:* We assume that $|\bar{\Omega}| \ge 4$, for otherwise no cross exists. Let $H$ be
> the cubic graph formed by two vertex-disjoint circuits $C_1, C_2$, both of length $|\bar{\Omega}|$,
> and for $1 \le i \le |\bar{\Omega}|$ an edge joining the $i$th vertices of $C_1$ and $C_2$.
> Identify $V(C_2)$ with $\bar{\Omega}$, in order, and let $s_1, s_2, t_1, t_2$ be distinct vertices
> of $C_1$, in order. We apply an algorithm of Shiloach [27] to find two paths of $G \cup H$,
> vertex-disjoint, joining $s_1, t_1$ and $s_2, t_2$, respectively, if they exist. If we find two
> such paths it is easy to derive a cross in $(G, \Omega)$; and if there are not two such paths it
> is easy to see that $(G, \Omega)$ has no cross. (Since Shiloach's algorithm has running time
> $O(v\varepsilon)$, so does (8.1).)

## Main definitions and theorems

* `Alg81Input`, `CrossesInOmega`, `IsCrossInSociety`, `CrossWitness`, `HasCrossInSociety`:
  societies `(G, Ω)` and crosses in `(G, Ω)`.
* `auxGraph81`: the auxiliary simple graph `G ∪ H` on `Fin (n + |Ω̄|)` where `V(C₂)` is identified
  with `Ω̄` in cyclic order and `V(C₁)` consists of the new vertices `n + i` (`0 ≤ i < |Ω̄|`), with
  terminals `s₁ = n + 0`, `s₂ = n + 1`, `t₁ = n + 2`, `t₂ = n + 3`.
* `cross_of_auxGraph81_paths`: the first claim of (8.1) ("If we find two such paths it is easy to
  derive a cross in $(G, \Omega)$").
* `not_hasCross_of_no_auxGraph81_paths`: the second claim of (8.1) ("if there are not two such
  paths it is easy to see that $(G, \Omega)$ has no cross").
* `algorithm_8_1`: Word RAM implementation of Algorithm (8.1) running in time `O(vε)` assuming
  `Shiloach80Statement`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Societies, Cyclic Order on `Ω̄`, and Crosses -/

/-- Problem size `v(G) · ε(G) = (|V(G)| + 1) · (|E(G)| + |V(G)| + 1)` for GM XIII Section 8
(where `v(G) = |V(G)| + 1` on page 66 and `ε(G) = |E(G)| + |V(G)| + 1` on page 71). -/
def societySize (n m : ℕ) : ℕ :=
  (n + 1) * (m + n + 1)

/-- Input to GM XIII Algorithm (8.1): a society `(G, Ω)` represented by a finite simple graph
`G : SimpleGraph (Fin n)` and a duplicate-free list `omega : List (Fin n)` giving the cyclic order
of `Ω̄ ⊆ V(G)`. -/
structure Alg81Input where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input simple graph `G` on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidability of adjacency in `G`. -/
  [decAdj : DecidableRel G.Adj]
  /-- Cyclic order of `Ω̄ ⊆ V(G)` as a duplicate-free list of vertices. -/
  omega : List (Fin n)
  /-- The vertices of `Ω̄` listed in `omega` are pairwise distinct. -/
  nodup_omega : omega.Nodup

attribute [instance] Alg81Input.decAdj

/-- Problem size `v(G) · ε(G)` for an `Alg81Input`. -/
def alg81Size (x : Alg81Input) : ℕ :=
  societySize x.n x.G.edgeFinset.card

/-- Flat Word RAM input encoding of a society `x : Alg81Input` in `inArr`:
`encGraph x.G ++ [x.omega.length] ++ x.omega.map Fin.val`. -/
def encAlg81In (x : Alg81Input) : List ℕ :=
  encGraph x.G ++ [x.omega.length] ++ x.omega.map Fin.val

theorem length_omega_le_n {n : ℕ} {omega : List (Fin n)} (hnodup : omega.Nodup) :
    omega.length ≤ n := by
  simpa using hnodup.length_le_card

/-- Four vertices `p₁, q₁, p₂, q₂` occur in `omega` in the cyclic order `(p₁, q₁, p₂, q₂)` or its
reverse `(p₁, q₂, p₂, q₁)` (GM XIII page 93): there exist strictly increasing indices
`0 ≤ i₁ < i₂ < i₃ < i₄ < omega.length` such that `(omega[i₁], omega[i₃])` are the ends of one path
and `(omega[i₂], omega[i₄])` are the ends of the other path. -/
def CrossesInOmega {n : ℕ} (omega : List (Fin n)) (p₁ q₁ p₂ q₂ : Fin n) : Prop :=
  ∃ (i₁ i₂ i₃ i₄ : ℕ) (h₁ : i₁ < i₂) (h₂ : i₂ < i₃) (h₃ : i₃ < i₄) (h₄ : i₄ < omega.length),
    (((omega[i₁] = p₁ ∧ omega[i₃] = p₂) ∨ (omega[i₁] = p₂ ∧ omega[i₃] = p₁)) ∧
      ((omega[i₂] = q₁ ∧ omega[i₄] = q₂) ∨ (omega[i₂] = q₂ ∧ omega[i₄] = q₁))) ∨
    (((omega[i₁] = q₁ ∧ omega[i₃] = q₂) ∨ (omega[i₁] = q₂ ∧ omega[i₃] = q₁)) ∧
      ((omega[i₂] = p₁ ∧ omega[i₄] = p₂) ∨ (omega[i₂] = p₂ ∧ omega[i₄] = p₁)))

theorem CrossesInOmega.four_le_length {n : ℕ} {omega : List (Fin n)} {p₁ q₁ p₂ q₂ : Fin n}
    (h : CrossesInOmega omega p₁ q₁ p₂ q₂) : 4 ≤ omega.length := by
  rcases h with ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, _⟩
  omega

theorem CrossesInOmega.mem_omega {n : ℕ} {omega : List (Fin n)} {p₁ q₁ p₂ q₂ : Fin n}
    (h : CrossesInOmega omega p₁ q₁ p₂ q₂) :
    p₁ ∈ omega ∧ q₁ ∈ omega ∧ p₂ ∈ omega ∧ q₂ ∈ omega := by
  rcases h with ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, hcases⟩
  have hm₁ : omega[i₁] ∈ omega := List.getElem_mem (by omega)
  have hm₂ : omega[i₂] ∈ omega := List.getElem_mem (by omega)
  have hm₃ : omega[i₃] ∈ omega := List.getElem_mem (by omega)
  have hm₄ : omega[i₄] ∈ omega := List.getElem_mem h₄
  rcases hcases with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨hm₁, hm₂, hm₃, hm₄⟩
  · exact ⟨hm₁, hm₄, hm₃, hm₂⟩
  · exact ⟨hm₃, hm₂, hm₁, hm₄⟩
  · exact ⟨hm₃, hm₄, hm₁, hm₂⟩
  · exact ⟨hm₂, hm₁, hm₄, hm₃⟩
  · exact ⟨hm₄, hm₁, hm₂, hm₃⟩
  · exact ⟨hm₂, hm₃, hm₄, hm₁⟩
  · exact ⟨hm₄, hm₃, hm₂, hm₁⟩

theorem CrossesInOmega.symm_pq {n : ℕ} {omega : List (Fin n)} {p₁ q₁ p₂ q₂ : Fin n}
    (h : CrossesInOmega omega p₁ q₁ p₂ q₂) :
    CrossesInOmega omega q₁ p₁ q₂ p₂ := by
  rcases h with ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, hcases⟩
  exact ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, hcases.symm⟩

theorem CrossesInOmega.swap_p {n : ℕ} {omega : List (Fin n)} {p₁ q₁ p₂ q₂ : Fin n}
    (h : CrossesInOmega omega p₁ q₁ p₂ q₂) :
    CrossesInOmega omega p₂ q₁ p₁ q₂ := by
  rcases h with ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, ⟨hp, hq⟩ | ⟨hq, hp⟩⟩
  · exact ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, Or.inl ⟨hp.symm, hq⟩⟩
  · exact ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, Or.inr ⟨hq, hp.symm⟩⟩

theorem CrossesInOmega.swap_q {n : ℕ} {omega : List (Fin n)} {p₁ q₁ p₂ q₂ : Fin n}
    (h : CrossesInOmega omega p₁ q₁ p₂ q₂) :
    CrossesInOmega omega p₁ q₂ p₂ q₁ := by
  exact (h.symm_pq.swap_p).symm_pq

/-- If `(p₁, p₂)` crosses `(q₁, q₂)` in `omega`, then for any vertex `w ∈ omega` with `w ≠ q₁` and
`w ≠ q₂`, either `(p₁, w)` crosses `(q₁, q₂)` or `(w, p₂)` crosses `(q₁, q₂)`. -/
theorem crossesInOmega_split {n : ℕ} {omega : List (Fin n)}
    {p₁ q₁ p₂ q₂ w : Fin n}
    (hcross : CrossesInOmega omega p₁ q₁ p₂ q₂)
    (hw : w ∈ omega) (hwq₁ : w ≠ q₁) (hwq₂ : w ≠ q₂) :
    CrossesInOmega omega p₁ q₁ w q₂ ∨ CrossesInOmega omega w q₁ p₂ q₂ := by
  rcases List.mem_iff_getElem.mp hw with ⟨j, hj, hget_j⟩
  rcases hcross with ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, ⟨hp, hq⟩ | ⟨hq, hp⟩⟩
  · have hj_ne2 : j ≠ i₂ := by
      rintro rfl
      rcases hq with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd (hget_j.symm.trans h) (by tauto)
    have hj_ne4 : j ≠ i₄ := by
      rintro rfl
      rcases hq with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd (hget_j.symm.trans h) (by tauto)
    rcases Nat.lt_trichotomy j i₂ with hj2 | rfl | hj2
    · -- j < i₂ < i₃ < i₄: (omega[j], omega[i₃]) crosses (q₁, q₂)
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨j, i₂, i₃, i₄, hj2, h₂, h₃, h₄, Or.inl ⟨Or.inl ⟨hget_j, rfl⟩, hq⟩⟩
      · exact Or.inl ⟨j, i₂, i₃, i₄, hj2, h₂, h₃, h₄, Or.inl ⟨Or.inr ⟨hget_j, rfl⟩, hq⟩⟩
    · exact absurd rfl hj_ne2
    · rcases Nat.lt_trichotomy j i₄ with hj4 | rfl | hj4
      · -- i₁ < i₂ < j < i₄: (omega[i₁], omega[j]) crosses (q₁, q₂)
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨i₁, i₂, j, i₄, h₁, hj2, hj4, h₄, Or.inl ⟨Or.inl ⟨rfl, hget_j⟩, hq⟩⟩
        · exact Or.inr ⟨i₁, i₂, j, i₄, h₁, hj2, hj4, h₄, Or.inl ⟨Or.inr ⟨rfl, hget_j⟩, hq⟩⟩
      · exact absurd rfl hj_ne4
      · -- i₂ < i₃ < i₄ < j: (omega[i₃], omega[j]) crosses (q₁, q₂)
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨i₂, i₃, i₄, j, h₂, h₃, hj4, hj, Or.inr ⟨hq, Or.inr ⟨rfl, hget_j⟩⟩⟩
        · exact Or.inl ⟨i₂, i₃, i₄, j, h₂, h₃, hj4, hj, Or.inr ⟨hq, Or.inl ⟨rfl, hget_j⟩⟩⟩
  · have hj_ne1 : j ≠ i₁ := by
      rintro rfl
      rcases hq with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd (hget_j.symm.trans h) (by tauto)
    have hj_ne3 : j ≠ i₃ := by
      rintro rfl
      rcases hq with ⟨_, h⟩ | ⟨_, h⟩ <;> exact absurd (hget_j.symm.trans h) (by tauto)
    rcases Nat.lt_trichotomy j i₁ with hj1 | rfl | hj1
    · -- j < i₁ < i₂ < i₃: (omega[j], omega[i₂]) crosses (q₁, q₂)
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨j, i₁, i₂, i₃, hj1, h₁, h₂, by omega, Or.inl ⟨Or.inr ⟨hget_j, rfl⟩, hq⟩⟩
      · exact Or.inr ⟨j, i₁, i₂, i₃, hj1, h₁, h₂, by omega, Or.inl ⟨Or.inl ⟨hget_j, rfl⟩, hq⟩⟩
    · exact absurd rfl hj_ne1
    · rcases Nat.lt_trichotomy j i₃ with hj3 | rfl | hj3
      · -- i₁ < j < i₃ < i₄: (omega[j], omega[i₄]) crosses (q₁, q₂)
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr ⟨i₁, j, i₃, i₄, hj1, hj3, h₃, h₄, Or.inr ⟨hq, Or.inl ⟨hget_j, rfl⟩⟩⟩
        · exact Or.inl ⟨i₁, j, i₃, i₄, hj1, hj3, h₃, h₄, Or.inr ⟨hq, Or.inr ⟨hget_j, rfl⟩⟩⟩
      · exact absurd rfl hj_ne3
      · -- i₁ < i₂ < i₃ < j: (omega[i₂], omega[j]) crosses (q₁, q₂)
        rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨i₁, i₂, i₃, j, h₁, h₂, hj3, hj, Or.inr ⟨hq, Or.inl ⟨rfl, hget_j⟩⟩⟩
        · exact Or.inr ⟨i₁, i₂, i₃, j, h₁, h₂, hj3, hj, Or.inr ⟨hq, Or.inr ⟨rfl, hget_j⟩⟩⟩

/-- A cross in a society `(G, omega)` (GM XIII page 93): two vertex-disjoint simple paths
`P : G.Walk p₁ p₂` and `Q : G.Walk q₁ q₂` whose ends `p₁, q₁, p₂, q₂ ∈ omega` cross in `omega`. -/
def IsCrossInSociety {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (p₁ p₂ q₁ q₂ : Fin n) (P : G.Walk p₁ p₂) (Q : G.Walk q₁ q₂) : Prop :=
  P.IsPath ∧ Q.IsPath ∧
  List.Disjoint P.support Q.support ∧
  CrossesInOmega omega p₁ q₁ p₂ q₂

/-- Bundled witness of a cross in `(G, omega)`. -/
structure CrossWitness {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n)) where
  /-- First endpoint of `P`. -/
  p₁ : Fin n
  /-- Second endpoint of `P`. -/
  p₂ : Fin n
  /-- First endpoint of `Q`. -/
  q₁ : Fin n
  /-- Second endpoint of `Q`. -/
  q₂ : Fin n
  /-- First path `P` of the cross. -/
  P : G.Walk p₁ p₂
  /-- Second path `Q` of the cross. -/
  Q : G.Walk q₁ q₂

/-- Validity predicate for a `CrossWitness`. -/
def CrossWitness.IsValid {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (c : CrossWitness G omega) : Prop :=
  IsCrossInSociety G omega c.p₁ c.p₂ c.q₁ c.q₂ c.P c.Q

/-- Existence of a cross in `(G, omega)`. -/
def HasCrossInSociety {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n)) : Prop :=
  ∃ (p₁ p₂ q₁ q₂ : Fin n) (P : G.Walk p₁ p₂) (Q : G.Walk q₁ q₂),
    IsCrossInSociety G omega p₁ p₂ q₁ q₂ P Q

/-- If `|Ω̄| < 4`, then `(G, Ω)` has no cross (GM XIII page 93:
"We assume that $|\bar{\Omega}| \ge 4$, for otherwise no cross exists."). -/
theorem not_hasCross_of_lt_four {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (hlt : omega.length < 4) : ¬ HasCrossInSociety G omega := by
  rintro ⟨p₁, p₂, q₁, q₂, P, Q, _, _, _, hcross⟩
  have hge := hcross.four_le_length
  omega

/-- Trimming one path of a cross: given a cross `(P, Q)` in `(G, omega)`, there is a subpath `P'`
of `P` with endpoints `p'₁, p'₂ ∈ omega` and no internal vertices in `omega` such that `(P', Q)`
is still a cross in `(G, omega)`. -/
theorem exists_trimmed_left_of_cross {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {p₁ p₂ q₁ q₂ : Fin n} (P : G.Walk p₁ p₂) (Q : G.Walk q₁ q₂)
    (hcross : IsCrossInSociety G omega p₁ p₂ q₁ q₂ P Q) :
    ∃ (p'₁ p'₂ : Fin n) (P' : G.Walk p'₁ p'₂),
      IsCrossInSociety G omega p'₁ p'₂ q₁ q₂ P' Q ∧
      (∀ x ∈ P'.support, x ∈ Q.support → False) ∧
      (∀ x ∈ P'.support, x ∈ omega → x = p'₁ ∨ x = p'₂) := by
  suffices h : ∀ (L : ℕ) (a b : Fin n) (W : G.Walk a b),
      W.length ≤ L →
      IsCrossInSociety G omega a b q₁ q₂ W Q →
      ∃ (p'₁ p'₂ : Fin n) (P' : G.Walk p'₁ p'₂),
        IsCrossInSociety G omega p'₁ p'₂ q₁ q₂ P' Q ∧
        (∀ x ∈ P'.support, x ∈ Q.support → False) ∧
        (∀ x ∈ P'.support, x ∈ omega → x = p'₁ ∨ x = p'₂) by
    exact h P.length p₁ p₂ P le_rfl hcross
  intro L
  induction L with
  | zero =>
    intro a b W hlen hW
    rcases hW with ⟨hpath, hQ, hdisj, hc⟩
    exact ⟨a, b, W, ⟨hpath, hQ, hdisj, hc⟩, hdisj, fun x hx _ => by
      cases W with
      | nil => left; simpa using hx
      | cons _ _ => simp at hlen⟩
  | succ L ih =>
    intro a b W hlen hW
    rcases hW with ⟨hpath, hQ, hdisj, hc⟩
    by_cases hint : ∃ w ∈ W.support, w ∈ omega ∧ w ≠ a ∧ w ≠ b
    · rcases hint with ⟨w, hw_sup, hw_om, hwa, hwb⟩
      rcases Walk.mem_support_iff_exists_append.mp hw_sup with ⟨W₁, W₂, rfl⟩
      have hpath₁ : W₁.IsPath := hpath.of_append_left
      have hpath₂ : W₂.IsPath := hpath.of_append_right
      have hlen_sum : (W₁.append W₂).length = W₁.length + W₂.length := Walk.length_append W₁ W₂
      have hlen₁_pos : 0 < W₁.length := by
        cases W₁ with
        | nil => exact absurd rfl hwa
        | cons _ _ => simp
      have hlen₂_pos : 0 < W₂.length := by
        cases W₂ with
        | nil => exact absurd rfl hwb.symm
        | cons _ _ => simp
      have hdisj₁ : List.Disjoint W₁.support Q.support :=
        fun x hx₁ hxQ => hdisj (W₁.support_subset_support_append_left W₂ hx₁) hxQ
      have hdisj₂ : List.Disjoint W₂.support Q.support :=
        fun x hx₂ hxQ => hdisj (W₁.support_subset_support_append_right W₂ hx₂) hxQ
      have hw_not_Q : w ∉ Q.support := fun hwQ => hdisj hw_sup hwQ
      have hwq₁ : w ≠ q₁ := fun h => hw_not_Q (h ▸ Walk.start_mem_support Q)
      have hwq₂ : w ≠ q₂ := fun h => hw_not_Q (h ▸ Walk.end_mem_support Q)
      rcases crossesInOmega_split hc hw_om hwq₁ hwq₂ with hc₁ | hc₂
      · exact ih a w W₁ (by omega) ⟨hpath₁, hQ, hdisj₁, hc₁⟩
      · exact ih w b W₂ (by omega) ⟨hpath₂, hQ, hdisj₂, hc₂⟩
    · refine ⟨a, b, W, ⟨hpath, hQ, hdisj, hc⟩, hdisj, fun x hx hx_om => ?_⟩
      by_cases hxa : x = a
      · exact Or.inl hxa
      · by_cases hxb : x = b
        · exact Or.inr hxb
        · exfalso
          exact hint ⟨x, hx, hx_om, hxa, hxb⟩

/-- Trimming both paths of a cross: if `HasCrossInSociety G omega`, then there is a cross `(P, Q)`
in `(G, omega)` such that neither `P` nor `Q` has any internal vertex in `omega`. -/
theorem exists_trimmed_cross_of_hasCross {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (h : HasCrossInSociety G omega) :
    ∃ (p₁ p₂ q₁ q₂ : Fin n) (P : G.Walk p₁ p₂) (Q : G.Walk q₁ q₂),
      IsCrossInSociety G omega p₁ p₂ q₁ q₂ P Q ∧
      (∀ x ∈ P.support, x ∈ omega → x = p₁ ∨ x = p₂) ∧
      (∀ y ∈ Q.support, y ∈ omega → y = q₁ ∨ y = q₂) := by
  rcases h with ⟨p₁, p₂, q₁, q₂, P, Q, hcross⟩
  rcases exists_trimmed_left_of_cross P Q hcross with ⟨p'₁, p'₂, P', hcross', _, htrimP⟩
  have hcross_symm : IsCrossInSociety G omega q₁ q₂ p'₁ p'₂ Q P' :=
    ⟨hcross'.2.1, hcross'.1, hcross'.2.2.1.symm, hcross'.2.2.2.symm_pq⟩
  rcases exists_trimmed_left_of_cross Q P' hcross_symm with ⟨q'₁, q'₂, Q', hcross'', _, htrimQ⟩
  exact ⟨p'₁, p'₂, q'₁, q'₂, P', Q',
    ⟨hcross''.2.1, hcross''.1, hcross''.2.2.1.symm, hcross''.2.2.2.symm_pq⟩,
    htrimP, htrimQ⟩

/-! ### Section 2: The Auxiliary Graph `G ∪ H` (`auxGraph81`) -/

/-- Adjacency predicate for the auxiliary graph `G ∪ H` in GM XIII (8.1) (page 93) on
`Fin (n + omega.length)`:
- Vertices `< n` are the vertices of `G`, with `V(C₂)` identified with `omega[0], …, omega[k - 1]`
  in cyclic order (`k = omega.length`).
- Vertices `n + i` (`0 ≤ i < k`) are the vertices of `C₁` in cyclic order.
- Two distinct vertices `x, y : Fin (n + k)` are adjacent in `auxGraph81 G omega` if and only if
  they are joined by an edge of `G`, a cycle edge of `C₁`, a rung joining `n + i` and `omega[i]`,
  or a cycle edge of `C₂` joining `omega[i]` and `omega[(i + 1) % k]`. -/
def AuxGraph81Adj {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (x y : Fin (n + omega.length)) : Prop :=
  x ≠ y ∧
  ((∃ (hx : x.1 < n) (hy : y.1 < n), G.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩) ∨
   (∃ i : Fin omega.length,
      (x.1 = n + i.1 ∧ y.1 = n + (i.1 + 1) % omega.length) ∨
      (y.1 = n + i.1 ∧ x.1 = n + (i.1 + 1) % omega.length)) ∨
   (∃ i : Fin omega.length,
      (x.1 = n + i.1 ∧ y.1 = (omega[i]).1) ∨
      (y.1 = n + i.1 ∧ x.1 = (omega[i]).1)) ∨
   (∃ (i : Fin omega.length) (hpos : 0 < omega.length),
      (x.1 = (omega[i]).1 ∧ y.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos)).1) ∨
      (y.1 = (omega[i]).1 ∧ x.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos)).1)))

theorem AuxGraph81Adj.symm {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {x y : Fin (n + omega.length)} (h : AuxGraph81Adj G omega x y) :
    AuxGraph81Adj G omega y x := by
  rcases h with ⟨hne, ⟨hx, hy, hadj⟩ | ⟨i, h1⟩ | ⟨i, h2⟩ | ⟨i, hpos, h3⟩⟩
  · exact ⟨hne.symm, Or.inl ⟨hy, hx, hadj.symm⟩⟩
  · exact ⟨hne.symm, Or.inr (Or.inl ⟨i, h1.symm⟩)⟩
  · exact ⟨hne.symm, Or.inr (Or.inr (Or.inl ⟨i, h2.symm⟩))⟩
  · exact ⟨hne.symm, Or.inr (Or.inr (Or.inr ⟨i, hpos, h3.symm⟩))⟩

def auxGraph81 {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n)) :
    SimpleGraph (Fin (n + omega.length)) where
  Adj := AuxGraph81Adj G omega
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

instance instDecidableRelAuxGraph81Adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (omega : List (Fin n)) : DecidableRel (auxGraph81 G omega).Adj :=
  fun x y => by change Decidable (AuxGraph81Adj G omega x y); unfold AuxGraph81Adj; infer_instance

/-- Embed a vertex `u : Fin n` of `G` into `Fin (n + k)`. -/
def inGVert {n : ℕ} (k : ℕ) (u : Fin n) : Fin (n + k) :=
  ⟨u.1, by omega⟩

theorem inGVert_injective {n : ℕ} (k : ℕ) : Function.Injective (inGVert (n := n) k) := by
  intro a b h
  exact Fin.ext (Fin.mk.inj_iff.mp h)

/-- The `i`-th vertex `n + i` of `C₁` in `Fin (n + k)`. -/
def c1Vert (n k : ℕ) (i : ℕ) (hi : i < k) : Fin (n + k) :=
  ⟨n + i, by omega⟩

/-- Terminal `s₁ = c₁(0) = n + 0` on `C₁`. -/
def s1Vert (n k : ℕ) (hk : 4 ≤ k) : Fin (n + k) :=
  c1Vert n k 0 (by omega)

/-- Terminal `s₂ = c₁(1) = n + 1` on `C₁`. -/
def s2Vert (n k : ℕ) (hk : 4 ≤ k) : Fin (n + k) :=
  c1Vert n k 1 (by omega)

/-- Terminal `t₁ = c₁(2) = n + 2` on `C₁`. -/
def t1Vert (n k : ℕ) (hk : 4 ≤ k) : Fin (n + k) :=
  c1Vert n k 2 (by omega)

/-- Terminal `t₂ = c₁(3) = n + 3` on `C₁`. -/
def t2Vert (n k : ℕ) (hk : 4 ≤ k) : Fin (n + k) :=
  c1Vert n k 3 (by omega)

theorem adj_auxGraph81_of_adj_G {n : ℕ} {G : SimpleGraph (Fin n)} (omega : List (Fin n))
    {u v : Fin n} (hadj : G.Adj u v) :
    (auxGraph81 G omega).Adj (inGVert omega.length u) (inGVert omega.length v) := by
  refine ⟨fun h => G.ne_of_adj hadj (inGVert_injective omega.length h), Or.inl ⟨u.2, v.2, hadj⟩⟩

/-- Lift a walk `W : G.Walk u v` in `G` to `(auxGraph81 G omega).Walk`. -/
def liftWalkToAux81 {n : ℕ} {G : SimpleGraph (Fin n)} (omega : List (Fin n))
    {u v : Fin n} : G.Walk u v →
      (auxGraph81 G omega).Walk (inGVert omega.length u) (inGVert omega.length v)
  | .nil => .nil
  | .cons hadj rest => .cons (adj_auxGraph81_of_adj_G omega hadj) (liftWalkToAux81 omega rest)

@[simp]
theorem support_liftWalkToAux81 {n : ℕ} {G : SimpleGraph (Fin n)} (omega : List (Fin n))
    {u v : Fin n} (W : G.Walk u v) :
    (liftWalkToAux81 omega W).support = W.support.map (inGVert omega.length) := by
  induction W with
  | nil => rfl
  | cons _ _ ih => simp [liftWalkToAux81, ih]

theorem isPath_liftWalkToAux81 {n : ℕ} {G : SimpleGraph (Fin n)} (omega : List (Fin n))
    {u v : Fin n} {W : G.Walk u v} (hW : W.IsPath) :
    (liftWalkToAux81 omega W).IsPath := by
  rw [Walk.isPath_def, support_liftWalkToAux81]
  exact hW.support_nodup.map (inGVert_injective omega.length)

/-! ### Section 3: Easy Claim 2 (`not_hasCross_of_no_auxGraph81_paths`) -/

theorem mod_lt_two_mul {a k : ℕ} (h : a < k + k) :
    a % k = if a < k then a else a - k := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

/-- Shifted index `(d + 2) % k` corresponding to distance `d < k` along the cycle starting at `2`. -/
def idxOfDist (k d : ℕ) (hd : d < k) : Fin k :=
  ⟨(d + 2) % k, Nat.mod_lt _ (by omega)⟩

theorem idxOfDist_val {k d : ℕ} (hk : 2 ≤ k) (hd : d < k) :
    (idxOfDist k d hd).1 = if d + 2 < k then d + 2 else d + 2 - k := by
  simp only [idxOfDist]
  exact mod_lt_two_mul (by omega)

theorem idxOfDist_injective {k d₁ d₂ : ℕ} (hk : 2 ≤ k) (hd₁ : d₁ < k) (hd₂ : d₂ < k)
    (h : idxOfDist k d₁ hd₁ = idxOfDist k d₂ hd₂) : d₁ = d₂ := by
  have hval : (idxOfDist k d₁ hd₁).1 = (idxOfDist k d₂ hd₂).1 := Fin.mk.inj_iff.mp h
  rw [idxOfDist_val hk hd₁, idxOfDist_val hk hd₂] at hval
  split_ifs at hval <;> omega

theorem idxOfDist_succ_mod {k d : ℕ} (hk : 2 ≤ k) (hd : d + 1 < k) :
    ((idxOfDist k d (by omega)).1 + 1) % k = (idxOfDist k (d + 1) hd).1 := by
  have hlt : (idxOfDist k d (by omega)).1 < k := (idxOfDist k d (by omega)).2
  rw [mod_lt_two_mul (by omega), idxOfDist_val hk (by omega), idxOfDist_val hk hd]
  split_ifs <;> omega

/-- Top-track vertex `c₁((d + 2) % k)` at distance `d` from `t₁ = c₁(2)`. -/
abbrev topAt (n : ℕ) (omega : List (Fin n)) (d : ℕ) (hd : d < omega.length) :
    Fin (n + omega.length) :=
  c1Vert n omega.length (idxOfDist omega.length d hd).1 (idxOfDist omega.length d hd).2

/-- Bottom-track vertex `omega[(d + 2) % k]` at distance `d` from `omega[2]`. -/
abbrev botAt (n : ℕ) (omega : List (Fin n)) (d : ℕ) (hd : d < omega.length) :
    Fin (n + omega.length) :=
  inGVert omega.length (omega[idxOfDist omega.length d hd])

theorem topAt_eq_t1Vert (n : ℕ) (omega : List (Fin n)) (hk : 4 ≤ omega.length) :
    topAt n omega 0 (by omega) = t1Vert n omega.length hk := by
  ext
  simp only [topAt, t1Vert, c1Vert, idxOfDist_val (by omega : 2 ≤ omega.length)]
  split_ifs <;> omega

theorem topAt_eq_t2Vert (n : ℕ) (omega : List (Fin n)) (hk : 4 ≤ omega.length) :
    topAt n omega 1 (by omega) = t2Vert n omega.length hk := by
  ext
  simp only [topAt, t2Vert, c1Vert, idxOfDist_val (by omega : 2 ≤ omega.length)]
  split_ifs <;> omega

theorem topAt_eq_s1Vert (n : ℕ) (omega : List (Fin n)) (hk : 4 ≤ omega.length) :
    topAt n omega (omega.length - 2) (by omega) = s1Vert n omega.length hk := by
  ext
  simp only [topAt, s1Vert, c1Vert, idxOfDist_val (by omega : 2 ≤ omega.length)]
  split_ifs <;> omega

theorem topAt_eq_s2Vert (n : ℕ) (omega : List (Fin n)) (hk : 4 ≤ omega.length) :
    topAt n omega (omega.length - 1) (by omega) = s2Vert n omega.length hk := by
  ext
  simp only [topAt, s2Vert, c1Vert, idxOfDist_val (by omega : 2 ≤ omega.length)]
  split_ifs <;> omega

theorem topAt_injective {n : ℕ} {omega : List (Fin n)} (hk : 2 ≤ omega.length) {d₁ d₂ : ℕ}
    (hd₁ : d₁ < omega.length) (hd₂ : d₂ < omega.length)
    (h : topAt n omega d₁ hd₁ = topAt n omega d₂ hd₂) : d₁ = d₂ := by
  have h1 : (idxOfDist omega.length d₁ hd₁).1 = (idxOfDist omega.length d₂ hd₂).1 := by
    have := Fin.mk.inj_iff.mp h
    omega
  exact idxOfDist_injective hk hd₁ hd₂ (Fin.ext h1)

theorem botAt_injective {n : ℕ} {omega : List (Fin n)} (hnodup : omega.Nodup)
    (hk : 2 ≤ omega.length) {d₁ d₂ : ℕ}
    (hd₁ : d₁ < omega.length) (hd₂ : d₂ < omega.length)
    (h : botAt n omega d₁ hd₁ = botAt n omega d₂ hd₂) : d₁ = d₂ := by
  have h1 : omega[idxOfDist omega.length d₁ hd₁] = omega[idxOfDist omega.length d₂ hd₂] :=
    inGVert_injective omega.length h
  have h2 : (idxOfDist omega.length d₁ hd₁).1 = (idxOfDist omega.length d₂ hd₂).1 :=
    (List.Nodup.getElem_inj_iff hnodup).mp h1
  exact idxOfDist_injective hk hd₁ hd₂ (Fin.ext h2)

theorem topAt_ne_botAt {n : ℕ} {omega : List (Fin n)} {d₁ d₂ : ℕ}
    (hd₁ : d₁ < omega.length) (hd₂ : d₂ < omega.length) :
    topAt n omega d₁ hd₁ ≠ botAt n omega d₂ hd₂ := by
  intro h
  have hval := Fin.mk.inj_iff.mp h
  have hlt : (omega[idxOfDist omega.length d₂ hd₂]).1 < n := (omega[idxOfDist omega.length d₂ hd₂]).2
  omega

theorem topAt_ne_inGVert {n : ℕ} {omega : List (Fin n)} {d : ℕ} (hd : d < omega.length)
    (u : Fin n) : topAt n omega d hd ≠ inGVert omega.length u := by
  intro h
  have hval := Fin.mk.inj_iff.mp h
  have hlt : u.1 < n := u.2
  omega

theorem botAt_ne_inGVert_of_not_mem {n : ℕ} {omega : List (Fin n)} {d : ℕ}
    (hd : d < omega.length) {u : Fin n} (hu : u ∉ omega) :
    botAt n omega d hd ≠ inGVert omega.length u := by
  intro h
  have h1 : omega[idxOfDist omega.length d hd] = u := inGVert_injective omega.length h
  exact hu (h1 ▸ List.getElem_mem _)

theorem adj_topAt_succ {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (d : ℕ) (hd : d + 1 < omega.length) :
    (auxGraph81 G omega).Adj (topAt n omega d (by omega)) (topAt n omega (d + 1) hd) := by
  refine ⟨fun h => ?_, Or.inr (Or.inl ⟨idxOfDist omega.length d (by omega), Or.inl ⟨rfl, ?_⟩⟩)⟩
  · have := topAt_injective (by omega) (by omega) hd h
    omega
  · simp only [topAt, c1Vert, idxOfDist_succ_mod (by omega) hd]

theorem adj_botAt_succ {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (hnodup : omega.Nodup) (d : ℕ) (hd : d + 1 < omega.length) :
    (auxGraph81 G omega).Adj (botAt n omega d (by omega)) (botAt n omega (d + 1) hd) := by
  refine ⟨fun h => ?_, Or.inr (Or.inr (Or.inr ⟨idxOfDist omega.length d (by omega), by omega, Or.inl ⟨rfl, ?_⟩⟩))⟩
  · have := botAt_injective hnodup (by omega) (by omega) hd h
    omega
  · simp only [botAt, inGVert, Fin.getElem_fin, idxOfDist_succ_mod (by omega) hd]

theorem adj_topAt_botAt {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (d : ℕ) (hd : d < omega.length) :
    (auxGraph81 G omega).Adj (topAt n omega d hd) (botAt n omega d hd) :=
  ⟨topAt_ne_botAt hd hd, Or.inr (Or.inr (Or.inl ⟨idxOfDist omega.length d hd, Or.inl ⟨rfl, rfl⟩⟩))⟩

/-- Walk along `C₁` from `topAt a` to `topAt b` (`a ≤ b < omega.length`). -/
def topWalk {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (a b : ℕ) (hab : a ≤ b) (hb : b < omega.length) :
    (auxGraph81 G omega).Walk (topAt n omega a (by omega)) (topAt n omega b hb) :=
  if h : a = b then
    Walk.nil.copy rfl (by subst h; rfl)
  else
    Walk.cons (adj_topAt_succ G omega a (by omega))
      (topWalk G omega (a + 1) b (by omega) hb)
termination_by b - a

theorem mem_support_topWalk {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {a b : ℕ} (hab : a ≤ b) (hb : b < omega.length) {x : Fin (n + omega.length)}
    (hx : x ∈ (topWalk G omega a b hab hb).support) :
    ∃ d, a ≤ d ∧ d ≤ b ∧ ∃ hd : d < omega.length, x = topAt n omega d hd := by
  unfold topWalk at hx
  split_ifs at hx with h
  · subst h
    simp only [Walk.support_copy, Walk.support_nil, List.mem_singleton] at hx
    exact ⟨a, le_rfl, le_rfl, hb, hx⟩
  · simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx_rest
    · exact ⟨a, le_rfl, hab, by omega, rfl⟩
    · rcases mem_support_topWalk (by omega) hb hx_rest with ⟨d, had, hdb, hd, rfl⟩
      exact ⟨d, by omega, hdb, hd, rfl⟩
termination_by b - a

/-- Walk along `C₂` from `botAt a` to `botAt b` (`a ≤ b < omega.length`). -/
def botWalk {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n)) (hnodup : omega.Nodup)
    (a b : ℕ) (hab : a ≤ b) (hb : b < omega.length) :
    (auxGraph81 G omega).Walk (botAt n omega a (by omega)) (botAt n omega b hb) :=
  if h : a = b then
    Walk.nil.copy rfl (by subst h; rfl)
  else
    Walk.cons (adj_botAt_succ G omega hnodup a (by omega))
      (botWalk G omega hnodup (a + 1) b (by omega) hb)
termination_by b - a

theorem mem_support_botWalk {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hnodup : omega.Nodup) {a b : ℕ} (hab : a ≤ b) (hb : b < omega.length)
    {x : Fin (n + omega.length)}
    (hx : x ∈ (botWalk G omega hnodup a b hab hb).support) :
    ∃ d, a ≤ d ∧ d ≤ b ∧ ∃ hd : d < omega.length, x = botAt n omega d hd := by
  unfold botWalk at hx
  split_ifs at hx with h
  · subst h
    simp only [Walk.support_copy, Walk.support_nil, List.mem_singleton] at hx
    exact ⟨a, le_rfl, le_rfl, hb, hx⟩
  · simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx_rest
    · exact ⟨a, le_rfl, hab, by omega, rfl⟩
    · rcases mem_support_botWalk hnodup (by omega) hb hx_rest with ⟨d, had, hdb, hd, rfl⟩
      exact ⟨d, by omega, hdb, hd, rfl⟩
termination_by b - a

/-- Classification of vertices in the first routed walk `W₁` (joining `s₁` and `t₁`). -/
def InWalk1Class {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (d₀ d₂ : ℕ) {u₀ u₂ : Fin n} (P : G.Walk u₀ u₂) (x : Fin (n + omega.length)) : Prop :=
  (∃ d, (d = 0 ∨ (d₂ ≤ d ∧ d ≤ omega.length - 2)) ∧
    ∃ hd : d < omega.length, x = topAt n omega d hd) ∨
  (∃ d, (d ≤ d₀ ∨ d = d₂) ∧
    ∃ hd : d < omega.length, x = botAt n omega d hd) ∨
  (∃ u ∈ P.support, u ∉ omega ∧ x = inGVert omega.length u)

/-- Classification of vertices in the second routed walk `W₂` (joining `s₂` and `t₂`). -/
def InWalk2Class {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n))
    (d₁ d₃ : ℕ) {u₁ u₃ : Fin n} (Q : G.Walk u₁ u₃) (x : Fin (n + omega.length)) : Prop :=
  (∃ d, ((1 ≤ d ∧ d ≤ d₁) ∨ d = omega.length - 1) ∧
    ∃ hd : d < omega.length, x = topAt n omega d hd) ∨
  (∃ d, (d = d₁ ∨ (d₃ ≤ d ∧ d ≤ omega.length - 1)) ∧
    ∃ hd : d < omega.length, x = botAt n omega d hd) ∨
  (∃ u ∈ Q.support, u ∉ omega ∧ x = inGVert omega.length u)

theorem inWalk1Class_disjoint_inWalk2Class {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hnodup : omega.Nodup) {d₀ d₁ d₂ d₃ : ℕ}
    (hd01 : d₀ < d₁) (hd12 : d₁ < d₂) (hd23 : d₂ < d₃) (hd3k : d₃ < omega.length)
    {u₀ u₂ u₁ u₃ : Fin n} {P : G.Walk u₀ u₂} {Q : G.Walk u₁ u₃}
    (hdisj : List.Disjoint P.support Q.support)
    {x : Fin (n + omega.length)}
    (h1 : InWalk1Class G omega d₀ d₂ P x) (h2 : InWalk2Class G omega d₁ d₃ Q x) : False := by
  rcases h1 with ⟨da, hda, hda_lt, rfl⟩ | ⟨da, hda, hda_lt, rfl⟩ | ⟨ua, huaP, hua_om, rfl⟩
  · rcases h2 with ⟨db, hdb, hdb_lt, heq⟩ | ⟨db, _, hdb_lt, heq⟩ | ⟨ub, _, _, heq⟩
    · have := topAt_injective (by omega) hda_lt hdb_lt heq
      omega
    · exact topAt_ne_botAt hda_lt hdb_lt heq
    · exact topAt_ne_inGVert hda_lt ub heq
  · rcases h2 with ⟨db, _, hdb_lt, heq⟩ | ⟨db, hdb, hdb_lt, heq⟩ | ⟨ub, _, hub_om, heq⟩
    · exact topAt_ne_botAt hdb_lt hda_lt heq.symm
    · have := botAt_injective hnodup (by omega) hda_lt hdb_lt heq
      omega
    · exact botAt_ne_inGVert_of_not_mem hda_lt hub_om heq
  · rcases h2 with ⟨db, _, hdb_lt, heq⟩ | ⟨db, _, hdb_lt, heq⟩ | ⟨ub, hubQ, _, heq⟩
    · exact topAt_ne_inGVert hdb_lt ua heq.symm
    · exact botAt_ne_inGVert_of_not_mem hdb_lt hua_om heq.symm
    · have := inGVert_injective omega.length heq
      subst this
      exact hdisj huaP hubQ

theorem mem_support_append {V : Type*} {G : SimpleGraph V} {u v w x : V}
    {W₁ : G.Walk u v} {W₂ : G.Walk v w} (hx : x ∈ (W₁.append W₂).support) :
    x ∈ W₁.support ∨ x ∈ W₂.support := by
  rw [Walk.support_append] at hx
  rcases List.mem_append.mp hx with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (List.mem_of_mem_tail h2)

theorem mem_support_cons {V : Type*} {G : SimpleGraph V} {u v w x : V}
    {h : G.Adj u v} {W : G.Walk v w} (hx : x ∈ (Walk.cons h W).support) :
    x = u ∨ x ∈ W.support := by
  rw [Walk.support_cons, List.mem_cons] at hx
  exact hx

@[simp]
theorem mem_support_reverse {V : Type*} {G : SimpleGraph V} {u v x : V} (W : G.Walk u v) :
    x ∈ W.reverse.support ↔ x ∈ W.support := by
  rw [Walk.support_reverse, List.mem_reverse]

/-- Given four ordered `distFrom2` positions `d₀ < d₁ < d₂ < d₃ < omega.length` and trimmed
disjoint paths `P` (between `botAt d₀` and `botAt d₂`) and `Q` (between `botAt d₁` and `botAt d₃`),
construct two vertex-disjoint paths in `auxGraph81 G omega` joining `(s₁, t₁)` and `(s₂, t₂)`. -/
theorem auxGraph81_paths_of_dist_ordered {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hnodup : omega.Nodup) (hk : 4 ≤ omega.length)
    {d₀ d₁ d₂ d₃ : ℕ} (hd01 : d₀ < d₁) (hd12 : d₁ < d₂) (hd23 : d₂ < d₃) (hd3k : d₃ < omega.length)
    (P : G.Walk (omega[idxOfDist omega.length d₀ (by omega)])
                (omega[idxOfDist omega.length d₂ (by omega)]))
    (Q : G.Walk (omega[idxOfDist omega.length d₁ (by omega)])
                (omega[idxOfDist omega.length d₃ hd3k]))
    (hdisj : List.Disjoint P.support Q.support)
    (htrimP : ∀ x ∈ P.support, x ∈ omega →
      x = omega[idxOfDist omega.length d₀ (by omega)] ∨
      x = omega[idxOfDist omega.length d₂ (by omega)])
    (htrimQ : ∀ y ∈ Q.support, y ∈ omega →
      y = omega[idxOfDist omega.length d₁ (by omega)] ∨
      y = omega[idxOfDist omega.length d₃ hd3k]) :
    ∃ (R₁ : (auxGraph81 G omega).Walk (s1Vert n omega.length hk) (t1Vert n omega.length hk))
      (R₂ : (auxGraph81 G omega).Walk (s2Vert n omega.length hk) (t2Vert n omega.length hk)),
      R₁.IsPath ∧ R₂.IsPath ∧ List.Disjoint R₁.support R₂.support := by
  have hd0k : d₀ < omega.length := by omega
  have hd1k : d₁ < omega.length := by omega
  have hd2k : d₂ < omega.length := by omega
  have hk0 : 0 < omega.length := by omega
  have hk1 : omega.length - 1 < omega.length := by omega
  have hk2 : omega.length - 2 < omega.length := by omega
  -- Construct walk W₁ from topAt (k - 2) to topAt 0:
  let W₁ : (auxGraph81 G omega).Walk (s1Vert n omega.length hk) (t1Vert n omega.length hk) :=
    (((topWalk G omega d₂ (omega.length - 2) (by omega) hk2).reverse.append
      (Walk.cons (adj_topAt_botAt G omega d₂ hd2k)
        ((liftWalkToAux81 omega P).reverse.append
          ((botWalk G omega hnodup 0 d₀ (Nat.zero_le _) hd0k).reverse.append
            (Walk.cons (adj_topAt_botAt G omega 0 hk0).symm Walk.nil))))).copy
      (topAt_eq_s1Vert n omega hk) (topAt_eq_t1Vert n omega hk))
  -- Construct walk W₂ from topAt (k - 1) to topAt 1:
  let W₂ : (auxGraph81 G omega).Walk (s2Vert n omega.length hk) (t2Vert n omega.length hk) :=
    ((Walk.cons (adj_topAt_botAt G omega (omega.length - 1) hk1)
      ((botWalk G omega hnodup d₃ (omega.length - 1) (by omega) hk1).reverse.append
        ((liftWalkToAux81 omega Q).reverse.append
          (Walk.cons (adj_topAt_botAt G omega d₁ hd1k).symm
            (topWalk G omega 1 d₁ (by omega) hd1k).reverse)))).copy
      (topAt_eq_s2Vert n omega hk) (topAt_eq_t2Vert n omega hk))
  have hW₁_class : ∀ x ∈ W₁.support, InWalk1Class G omega d₀ d₂ P x := by
    intro x hx
    rw [Walk.support_copy] at hx
    rcases mem_support_append hx with hx | hx
    · rw [mem_support_reverse] at hx
      rcases mem_support_topWalk (by omega) hk2 hx with ⟨d, hd_lo, hd_hi, hd, rfl⟩
      exact Or.inl ⟨d, Or.inr ⟨hd_lo, hd_hi⟩, hd, rfl⟩
    · rcases mem_support_cons hx with rfl | hx
      · exact Or.inl ⟨d₂, Or.inr ⟨le_rfl, by omega⟩, hd2k, rfl⟩
      · rcases mem_support_append hx with hx | hx
        · rw [mem_support_reverse, support_liftWalkToAux81, List.mem_map] at hx
          rcases hx with ⟨u, huP, rfl⟩
          by_cases huom : u ∈ omega
          · rcases htrimP u huP huom with rfl | rfl
            · exact Or.inr (Or.inl ⟨d₀, Or.inl le_rfl, hd0k, rfl⟩)
            · exact Or.inr (Or.inl ⟨d₂, Or.inr rfl, hd2k, rfl⟩)
          · exact Or.inr (Or.inr ⟨u, huP, huom, rfl⟩)
        · rcases mem_support_append hx with hx | hx
          · rw [mem_support_reverse] at hx
            rcases mem_support_botWalk hnodup (Nat.zero_le _) hd0k hx with ⟨d, _, hd_hi, hd, rfl⟩
            exact Or.inr (Or.inl ⟨d, Or.inl hd_hi, hd, rfl⟩)
          · rcases mem_support_cons hx with rfl | hx
            · exact Or.inr (Or.inl ⟨0, Or.inl (Nat.zero_le _), hk0, rfl⟩)
            · rw [Walk.support_nil, List.mem_singleton] at hx
              subst hx
              exact Or.inl ⟨0, Or.inl rfl, hk0, rfl⟩
  have hW₂_class : ∀ x ∈ W₂.support, InWalk2Class G omega d₁ d₃ Q x := by
    intro x hx
    rw [Walk.support_copy] at hx
    rcases mem_support_cons hx with rfl | hx
    · exact Or.inl ⟨omega.length - 1, Or.inr rfl, hk1, rfl⟩
    · rcases mem_support_append hx with hx | hx
      · rw [mem_support_reverse] at hx
        rcases mem_support_botWalk hnodup (by omega) hk1 hx with ⟨d, hd_lo, hd_hi, hd, rfl⟩
        exact Or.inr (Or.inl ⟨d, Or.inr ⟨hd_lo, hd_hi⟩, hd, rfl⟩)
      · rcases mem_support_append hx with hx | hx
        · rw [mem_support_reverse, support_liftWalkToAux81, List.mem_map] at hx
          rcases hx with ⟨u, huQ, rfl⟩
          by_cases huom : u ∈ omega
          · rcases htrimQ u huQ huom with rfl | rfl
            · exact Or.inr (Or.inl ⟨d₁, Or.inl rfl, hd1k, rfl⟩)
            · exact Or.inr (Or.inl ⟨d₃, Or.inr ⟨le_rfl, by omega⟩, hd3k, rfl⟩)
          · exact Or.inr (Or.inr ⟨u, huQ, huom, rfl⟩)
        · rcases mem_support_cons hx with rfl | hx
          · exact Or.inr (Or.inl ⟨d₁, Or.inl rfl, hd1k, rfl⟩)
          · rw [mem_support_reverse] at hx
            rcases mem_support_topWalk (by omega) hd1k hx with ⟨d, hd_lo, hd_hi, hd, rfl⟩
            exact Or.inl ⟨d, Or.inl ⟨hd_lo, hd_hi⟩, hd, rfl⟩
  refine ⟨(W₁.toPath : (auxGraph81 G omega).Walk _ _),
    (W₂.toPath : (auxGraph81 G omega).Walk _ _),
    W₁.toPath.isPath, W₂.toPath.isPath, fun x hx₁ hx₂ => ?_⟩
  exact inWalk1Class_disjoint_inWalk2Class hnodup hd01 hd12 hd23 hd3k hdisj
    (hW₁_class x (W₁.support_toPath_subset_support hx₁))
    (hW₂_class x (W₂.support_toPath_subset_support hx₂))

/-- Helper: if `p₁, p₂, q₁, q₂` are matched to `omega[i₀], omega[i₂]` and `omega[i₁], omega[i₃]`,
orient `P` and `Q` to go from `omega[i₀]` to `omega[i₂]` and `omega[i₁]` to `omega[i₃]`. -/
theorem exists_oriented_trimmed_paths {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {p₁ p₂ q₁ q₂ u₀ u₁ u₂ u₃ : Fin n}
    (P : G.Walk p₁ p₂) (Q : G.Walk q₁ q₂)
    (hdisj : List.Disjoint P.support Q.support)
    (htrimP : ∀ x ∈ P.support, x ∈ omega → x = p₁ ∨ x = p₂)
    (htrimQ : ∀ y ∈ Q.support, y ∈ omega → y = q₁ ∨ y = q₂)
    (hp : (u₀ = p₁ ∧ u₂ = p₂) ∨ (u₀ = p₂ ∧ u₂ = p₁))
    (hq : (u₁ = q₁ ∧ u₃ = q₂) ∨ (u₁ = q₂ ∧ u₃ = q₁)) :
    ∃ (P' : G.Walk u₀ u₂) (Q' : G.Walk u₁ u₃),
      List.Disjoint P'.support Q'.support ∧
      (∀ x ∈ P'.support, x ∈ omega → x = u₀ ∨ x = u₂) ∧
      (∀ y ∈ Q'.support, y ∈ omega → y = u₁ ∨ y = u₃) := by
  have hP' : ∃ P' : G.Walk u₀ u₂,
      (∀ x ∈ P'.support, x ∈ P.support) ∧
      (∀ x ∈ P'.support, x ∈ omega → x = u₀ ∨ x = u₂) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨P, fun _ hx => hx, htrimP⟩
    · refine ⟨P.reverse, fun x hx => by simpa using hx, fun x hx hx_om => ?_⟩
      have hx' : x ∈ P.support := by simpa using hx
      exact (htrimP x hx' hx_om).symm
  have hQ' : ∃ Q' : G.Walk u₁ u₃,
      (∀ y ∈ Q'.support, y ∈ Q.support) ∧
      (∀ y ∈ Q'.support, y ∈ omega → y = u₁ ∨ y = u₃) := by
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Q, fun _ hy => hy, htrimQ⟩
    · refine ⟨Q.reverse, fun y hy => by simpa using hy, fun y hy hy_om => ?_⟩
      have hy' : y ∈ Q.support := by simpa using hy
      exact (htrimQ y hy' hy_om).symm
  rcases hP' with ⟨P', hP'_sub, hP'_trim⟩
  rcases hQ' with ⟨Q', hQ'_sub, hQ'_trim⟩
  exact ⟨P', Q', fun x hxP hxQ => hdisj (hP'_sub x hxP) (hQ'_sub x hxQ), hP'_trim, hQ'_trim⟩

/-- If `(G, omega)` has a cross and `omega.Nodup`, then `auxGraph81 G omega` has two
vertex-disjoint paths joining `(s₁, t₁)` and `(s₂, t₂)`. -/
theorem auxGraph81_paths_of_hasCross {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hnodup : omega.Nodup) (hk : 4 ≤ omega.length) (hcross : HasCrossInSociety G omega) :
    ∃ (R₁ : (auxGraph81 G omega).Walk (s1Vert n omega.length hk) (t1Vert n omega.length hk))
      (R₂ : (auxGraph81 G omega).Walk (s2Vert n omega.length hk) (t2Vert n omega.length hk)),
      R₁.IsPath ∧ R₂.IsPath ∧ List.Disjoint R₁.support R₂.support := by
  rcases exists_trimmed_cross_of_hasCross hcross with
    ⟨p₁, p₂, q₁, q₂, P, Q, ⟨_, _, hdisj, hcr⟩, htrimP, htrimQ⟩
  rcases hcr with ⟨i₀, i₁, i₂, i₃, hi01, hi12, hi23, hi3k, halt⟩
  -- Convert indices i₀ < i₁ < i₂ < i₃ < k into d₀ < d₁ < d₂ < d₃ < k with idxOfDist = cyclic shift:
  have hshift : ∃ (d₀ d₁ d₂ d₃ : ℕ) (hd01 : d₀ < d₁) (hd12 : d₁ < d₂)
      (hd23 : d₂ < d₃) (hd3k : d₃ < omega.length),
      ((omega[idxOfDist omega.length d₀ (by omega)] = p₁ ∧
        omega[idxOfDist omega.length d₂ (by omega)] = p₂) ∨
       (omega[idxOfDist omega.length d₀ (by omega)] = p₂ ∧
        omega[idxOfDist omega.length d₂ (by omega)] = p₁)) ∧
      ((omega[idxOfDist omega.length d₁ (by omega)] = q₁ ∧
        omega[idxOfDist omega.length d₃ hd3k] = q₂) ∨
       (omega[idxOfDist omega.length d₁ (by omega)] = q₂ ∧
        omega[idxOfDist omega.length d₃ hd3k] = q₁)) ∨
      ((omega[idxOfDist omega.length d₀ (by omega)] = q₁ ∧
        omega[idxOfDist omega.length d₂ (by omega)] = q₂) ∨
       (omega[idxOfDist omega.length d₀ (by omega)] = q₂ ∧
        omega[idxOfDist omega.length d₂ (by omega)] = q₁)) ∧
      ((omega[idxOfDist omega.length d₁ (by omega)] = p₁ ∧
        omega[idxOfDist omega.length d₃ hd3k] = p₂) ∨
       (omega[idxOfDist omega.length d₁ (by omega)] = p₂ ∧
        omega[idxOfDist omega.length d₃ hd3k] = p₁)) := by
    by_cases h0 : 2 ≤ i₀
    · refine ⟨i₀ - 2, i₁ - 2, i₂ - 2, i₃ - 2, by omega, by omega, by omega, by omega, ?_⟩
      have e0 : (idxOfDist omega.length (i₀ - 2) (by omega)).1 = i₀ := by
        rw [idxOfDist_val (by omega)]; split_ifs <;> omega
      have e1 : (idxOfDist omega.length (i₁ - 2) (by omega)).1 = i₁ := by
        rw [idxOfDist_val (by omega)]; split_ifs <;> omega
      have e2 : (idxOfDist omega.length (i₂ - 2) (by omega)).1 = i₂ := by
        rw [idxOfDist_val (by omega)]; split_ifs <;> omega
      have e3 : (idxOfDist omega.length (i₃ - 2) (by omega)).1 = i₃ := by
        rw [idxOfDist_val (by omega)]; split_ifs <;> omega
      simpa only [Fin.getElem_fin, e0, e1, e2, e3] using halt
    · by_cases h1 : 2 ≤ i₁
      · refine ⟨i₁ - 2, i₂ - 2, i₃ - 2, i₀ + omega.length - 2,
          by omega, by omega, by omega, by omega, ?_⟩
        have e0 : (idxOfDist omega.length (i₁ - 2) (by omega)).1 = i₁ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        have e1 : (idxOfDist omega.length (i₂ - 2) (by omega)).1 = i₂ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        have e2 : (idxOfDist omega.length (i₃ - 2) (by omega)).1 = i₃ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        have e3 : (idxOfDist omega.length (i₀ + omega.length - 2) (by omega)).1 = i₀ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        simp only [Fin.getElem_fin, e0, e1, e2, e3]
        rcases halt with ⟨hp, hq⟩ | ⟨hq, hp⟩
        · exact Or.inr ⟨hq, hp.symm.imp And.symm And.symm⟩
        · exact Or.inl ⟨hp, hq.symm.imp And.symm And.symm⟩
      · refine ⟨i₂ - 2, i₃ - 2, i₀ + omega.length - 2, i₁ + omega.length - 2,
          by omega, by omega, by omega, by omega, ?_⟩
        have e0 : (idxOfDist omega.length (i₂ - 2) (by omega)).1 = i₂ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        have e1 : (idxOfDist omega.length (i₃ - 2) (by omega)).1 = i₃ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        have e2 : (idxOfDist omega.length (i₀ + omega.length - 2) (by omega)).1 = i₀ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        have e3 : (idxOfDist omega.length (i₁ + omega.length - 2) (by omega)).1 = i₁ := by
          rw [idxOfDist_val (by omega)]; split_ifs <;> omega
        simp only [Fin.getElem_fin, e0, e1, e2, e3]
        rcases halt with ⟨hp, hq⟩ | ⟨hq, hp⟩
        · exact Or.inl ⟨hp.symm.imp And.symm And.symm, hq.symm.imp And.symm And.symm⟩
        · exact Or.inr ⟨hq.symm.imp And.symm And.symm, hp.symm.imp And.symm And.symm⟩
  rcases hshift with ⟨d₀, d₁, d₂, d₃, hd01, hd12, hd23, hd3k, hmatch | hmatch⟩
  · rcases exists_oriented_trimmed_paths P Q hdisj htrimP htrimQ hmatch.1 hmatch.2 with
      ⟨P', Q', hdisj', htrimP', htrimQ'⟩
    exact auxGraph81_paths_of_dist_ordered hnodup hk hd01 hd12 hd23 hd3k P' Q' hdisj' htrimP' htrimQ'
  · rcases exists_oriented_trimmed_paths Q P hdisj.symm htrimQ htrimP hmatch.1 hmatch.2 with
      ⟨P', Q', hdisj', htrimP', htrimQ'⟩
    exact auxGraph81_paths_of_dist_ordered hnodup hk hd01 hd12 hd23 hd3k P' Q' hdisj' htrimP' htrimQ'

/-- **GM XIII (8.1), Easy Claim 2 (page 93)**:
"and if there are not two such paths it is easy to see that $(G, \Omega)$ has no cross." -/
theorem not_hasCross_of_no_auxGraph81_paths {n : ℕ} {G : SimpleGraph (Fin n)}
    {omega : List (Fin n)} (hnodup : omega.Nodup) (hk : 4 ≤ omega.length)
    (hno : ¬ ∃ (R₁ : (auxGraph81 G omega).Walk (s1Vert n omega.length hk) (t1Vert n omega.length hk))
               (R₂ : (auxGraph81 G omega).Walk (s2Vert n omega.length hk) (t2Vert n omega.length hk)),
               R₁.IsPath ∧ R₂.IsPath ∧ List.Disjoint R₁.support R₂.support) :
    ¬ HasCrossInSociety G omega :=
  fun hcross => hno (auxGraph81_paths_of_hasCross hnodup hk hcross)

/-! ### Section 4: Easy Claim 1 (`cross_of_auxGraph81_paths`) -/

/-- Cyclic distance `(i + k - 2) % k` from index `2` in `0 .. k - 1`. -/
def distFrom2 (k i : ℕ) : ℕ :=
  (i + k - 2) % k

theorem distFrom2_eq_if {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) :
    distFrom2 k i = if i < 2 then i + k - 2 else i - 2 := by
  simp only [distFrom2]
  rw [mod_lt_two_mul (by omega)]
  split_ifs <;> omega

theorem distFrom2_lt {k i : ℕ} (hk : 0 < k) : distFrom2 k i < k :=
  Nat.mod_lt _ hk

theorem distFrom2_injective {k i j : ℕ} (hk : 2 ≤ k) (hi : i < k) (hj : j < k)
    (h : distFrom2 k i = distFrom2 k j) : i = j := by
  rw [distFrom2_eq_if hk hi, distFrom2_eq_if hk hj] at h
  split_ifs at h <;> omega

theorem distFrom2_succ_mod {k i : ℕ} (hk : 2 ≤ k) (hi : i < k) (hne1 : i ≠ 1) :
    distFrom2 k ((i + 1) % k) = distFrom2 k i + 1 := by
  have hmod : (i + 1) % k < k := Nat.mod_lt _ (by omega)
  rw [distFrom2_eq_if hk hmod, distFrom2_eq_if hk hi, mod_lt_two_mul (by omega)]
  split_ifs <;> omega

theorem idxOf_getElem_of_nodup {α : Type*} [BEq α] [LawfulBEq α] {l : List α}
    (hnodup : l.Nodup) (i : Fin l.length) : l.idxOf l[i] = i.1 := by
  have hlt : l.idxOf l[i] < l.length := List.idxOf_lt_length_of_mem (List.getElem_mem i.2)
  have heq : l[l.idxOf l[i]]'hlt = l[i.1]'i.2 := List.getElem_idxOf hlt
  exact (List.Nodup.getElem_inj_iff hnodup).mp heq

/-- Whether a vertex `x : Fin (n + omega.length)` of `auxGraph81 G omega` belongs to `V(H)`
(either `n ≤ x.1`, that is, `x ∈ V(C₁)`, or `x.1 < n` and `⟨x.1, _⟩ ∈ omega`, that is, `x ∈ V(C₂)`).
-/
def isHVert (n : ℕ) (omega : List (Fin n)) (x : Fin (n + omega.length)) : Bool :=
  if h : x.1 < n then decide (⟨x.1, h⟩ ∈ omega) else true

/-- Cyclic position in `{0, …, k - 1}` (measured from index `2` via `distFrom2`) of a vertex
`x : Fin (n + omega.length)`. -/
def posH (n : ℕ) (omega : List (Fin n)) (x : Fin (n + omega.length)) : ℕ :=
  if h : x.1 < n then
    distFrom2 omega.length (omega.idxOf ⟨x.1, h⟩)
  else
    distFrom2 omega.length (x.1 - n)

/-- Linear index in `{0, …, 2k - 1}` of `x : Fin (n + omega.length)`:
`2 * posH x` if `x ∈ V(C₁)` (`n ≤ x.1`), and `2 * posH x + 1` if `x.1 < n`. -/
def idx2 (n : ℕ) (omega : List (Fin n)) (x : Fin (n + omega.length)) : ℕ :=
  if x.1 < n then 2 * posH n omega x + 1 else 2 * posH n omega x

/-- Comparison boolean `cmpIdx2(x, y) = decide (idx2 x < idx2 y)`. -/
def cmpIdx2 (n : ℕ) (omega : List (Fin n)) (x y : Fin (n + omega.length)) : Bool :=
  decide (idx2 n omega x < idx2 n omega y)

theorem idx2_injective_of_isHVert {n : ℕ} {omega : List (Fin n)} (hk : 2 ≤ omega.length)
    {x y : Fin (n + omega.length)} (hx : isHVert n omega x = true) (hy : isHVert n omega y = true)
    (heq : idx2 n omega x = idx2 n omega y) : x = y := by
  simp only [idx2] at heq
  split_ifs at heq with hxl hyl hyl
  · have hpos : posH n omega x = posH n omega y := by omega
    simp only [posH, hxl, hyl, ↓reduceDIte] at hpos
    simp only [isHVert, hxl, ↓reduceDIte, decide_eq_true_eq] at hx
    simp only [isHVert, hyl, ↓reduceDIte, decide_eq_true_eq] at hy
    have hix : omega.idxOf ⟨x.1, hxl⟩ < omega.length := List.idxOf_lt_length_of_mem hx
    have hiy : omega.idxOf ⟨y.1, hyl⟩ < omega.length := List.idxOf_lt_length_of_mem hy
    have hidx_eq : omega.idxOf ⟨x.1, hxl⟩ = omega.idxOf ⟨y.1, hyl⟩ :=
      distFrom2_injective hk hix hiy hpos
    have hfin_eq : (⟨x.1, hxl⟩ : Fin n) = ⟨y.1, hyl⟩ := by
      rw [← List.getElem_idxOf hix, ← List.getElem_idxOf hiy]
      congr 1
    exact Fin.ext (Fin.mk.inj_iff.mp hfin_eq)
  · omega
  · omega
  · have hpos : posH n omega x = posH n omega y := by omega
    simp only [posH, hxl, hyl, ↓reduceDIte] at hpos
    have hsub := distFrom2_injective hk (by omega) (by omega) hpos
    exact Fin.ext (by omega)

/-- An `H`-segment in `auxGraph81 G omega`: a simple path between two distinct vertices of `V(H)`
whose internal vertices are all outside `V(H)`. -/
structure HSegment {n : ℕ} (G : SimpleGraph (Fin n)) (omega : List (Fin n)) where
  u : Fin (n + omega.length)
  v : Fin (n + omega.length)
  walk : (auxGraph81 G omega).Walk u v
  hne : u ≠ v
  isPath : walk.IsPath
  hu : isHVert n omega u = true
  hv : isHVert n omega v = true
  hinternal : ∀ x ∈ walk.support, isHVert n omega x = true → x = u ∨ x = v

/-- Reverse an `HSegment`. -/
def HSegment.reverse {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s : HSegment G omega) : HSegment G omega where
  u := s.v
  v := s.u
  walk := s.walk.reverse
  hne := s.hne.symm
  isPath := s.isPath.reverse
  hu := s.hv
  hv := s.hu
  hinternal := fun x hx hH => (s.hinternal x (by simpa using hx) hH).symm

/-- `S` occurs as a contiguous subwalk of `W` (`W = W₁.append (S.append W₂)`). -/
def IsSubwalkOf {V : Type*} {G : SimpleGraph V} {a b u v : V}
    (W : G.Walk a b) (S : G.Walk u v) : Prop :=
  ∃ (W₁ : G.Walk a u) (W₂ : G.Walk v b), W = W₁.append (S.append W₂)

theorem IsSubwalkOf.refl {V : Type*} {G : SimpleGraph V} {a b : V} (W : G.Walk a b) :
    IsSubwalkOf W W :=
  ⟨.nil, .nil, by simp⟩

theorem IsSubwalkOf.append_left {V : Type*} {G : SimpleGraph V} {a w b u v : V}
    {W₁ : G.Walk a w} (W₂ : G.Walk w b) {S : G.Walk u v} (h : IsSubwalkOf W₁ S) :
    IsSubwalkOf (W₁.append W₂) S := by
  rcases h with ⟨U₁, U₂, rfl⟩
  exact ⟨U₁, U₂.append W₂, by simp [Walk.append_assoc]⟩

theorem IsSubwalkOf.append_right {V : Type*} {G : SimpleGraph V} {a w b u v : V}
    (W₁ : G.Walk a w) {W₂ : G.Walk w b} {S : G.Walk u v} (h : IsSubwalkOf W₂ S) :
    IsSubwalkOf (W₁.append W₂) S := by
  rcases h with ⟨U₁, U₂, rfl⟩
  exact ⟨W₁.append U₁, U₂, by simp [Walk.append_assoc]⟩

theorem IsSubwalkOf.support_subset {V : Type*} {G : SimpleGraph V} {a b u v : V}
    {W : G.Walk a b} {S : G.Walk u v} (h : IsSubwalkOf W S) :
    ∀ x ∈ S.support, x ∈ W.support := by
  rcases h with ⟨U₁, U₂, rfl⟩
  intro x hx
  exact U₁.support_subset_support_append_right _ (S.support_subset_support_append_left U₂ hx)

/-- Decompose any simple path in `auxGraph81 G omega` between distinct vertices `a, b ∈ V(H)`
into a list of `HSegment`s that are subwalks of `W` and whose endpoint increments
telescope under `bne`. -/
theorem exists_hsegments_of_path_aux {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)} :
    ∀ (L : ℕ) (a b : Fin (n + omega.length)) (W : (auxGraph81 G omega).Walk a b),
      W.length ≤ L → a ≠ b → W.IsPath →
      isHVert n omega a = true → isHVert n omega b = true →
      ∃ segs : List (HSegment G omega),
        (∀ s ∈ segs, IsSubwalkOf W s.walk) ∧
        (∀ g : Fin (n + omega.length) → Bool,
          segs.foldr (fun s acc => bne (bne (g s.u) (g s.v)) acc) false = bne (g a) (g b))
  | 0, a, b, W, hlen, hab, _, _, _ => by
    cases W with
    | nil => exact absurd rfl hab
    | cons _ _ => simp at hlen
  | L + 1, a, b, W, hlen, hab, hpath, ha, hb => by
    by_cases hint : ∃ w ∈ W.support, isHVert n omega w = true ∧ w ≠ a ∧ w ≠ b
    · rcases hint with ⟨w, hw_sup, hw_H, hwa, hwb⟩
      rcases Walk.mem_support_iff_exists_append.mp hw_sup with ⟨W₁, W₂, rfl⟩
      have hpath₁ : W₁.IsPath := hpath.of_append_left
      have hpath₂ : W₂.IsPath := hpath.of_append_right
      have hlen_sum : (W₁.append W₂).length = W₁.length + W₂.length := Walk.length_append W₁ W₂
      have hlen₁_pos : 0 < W₁.length := by
        cases W₁ with
        | nil => exact absurd rfl hwa
        | cons _ _ => simp
      have hlen₂_pos : 0 < W₂.length := by
        cases W₂ with
        | nil => exact absurd rfl hwb.symm
        | cons _ _ => simp
      rcases exists_hsegments_of_path_aux L a w W₁ (by omega) hwa.symm hpath₁ ha hw_H with
        ⟨segs₁, hsub₁, hfold₁⟩
      rcases exists_hsegments_of_path_aux L w b W₂ (by omega) hwb hpath₂ hw_H hb with
        ⟨segs₂, hsub₂, hfold₂⟩
      refine ⟨segs₁ ++ segs₂, ?_, ?_⟩
      · intro s hs
        rcases List.mem_append.mp hs with hs₁ | hs₂
        · exact (hsub₁ s hs₁).append_left W₂
        · exact (hsub₂ s hs₂).append_right W₁
      · intro g
        have h_init : ∀ ( init : Bool) (xs : List (HSegment G omega)),
            xs.foldr (fun s acc => bne (bne (g s.u) (g s.v)) acc) init =
              bne (xs.foldr (fun s acc => bne (bne (g s.u) (g s.v)) acc) false) init := by
          intro init xs
          induction xs with
          | nil => simp
          | cons s rest ih =>
            simp only [List.foldr_cons, ih]
            cases bne (g s.u) (g s.v) <;>
              cases rest.foldr (fun s acc => bne (bne (g s.u) (g s.v)) acc) false <;>
              cases init <;> rfl
        rw [List.foldr_append, h_init, hfold₁ g, hfold₂ g]
        cases g a <;> cases g w <;> cases g b <;> rfl
    · let seg : HSegment G omega :=
        { u := a
          v := b
          walk := W
          hne := hab
          isPath := hpath
          hu := ha
          hv := hb
          hinternal := fun x hx hH => by
            by_cases hxa : x = a
            · exact Or.inl hxa
            · by_cases hxb : x = b
              · exact Or.inr hxb
              · exfalso
                exact hint ⟨x, hx, hH, hxa, hxb⟩ }
      refine ⟨[seg], ?_, ?_⟩
      · intro s hs
        simp only [List.mem_singleton] at hs
        subst hs
        exact IsSubwalkOf.refl W
      · intro g
        simp [seg]

theorem exists_hsegments_of_path_subwalk {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {a b : Fin (n + omega.length)} (W : (auxGraph81 G omega).Walk a b)
    (hab : a ≠ b) (hpath : W.IsPath)
    (ha : isHVert n omega a = true) (hb : isHVert n omega b = true) :
    ∃ segs : List (HSegment G omega),
      (∀ s ∈ segs, IsSubwalkOf W s.walk) ∧
      (∀ g : Fin (n + omega.length) → Bool,
        segs.foldr (fun s acc => bne (bne (g s.u) (g s.v)) acc) false = bne (g a) (g b)) :=
  exists_hsegments_of_path_aux W.length a b W le_rfl hab hpath ha hb

theorem exists_hsegments_of_path {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {a b : Fin (n + omega.length)} (W : (auxGraph81 G omega).Walk a b)
    (hab : a ≠ b) (hpath : W.IsPath)
    (ha : isHVert n omega a = true) (hb : isHVert n omega b = true) :
    ∃ segs : List (HSegment G omega),
      (∀ s ∈ segs, ∀ x ∈ s.walk.support, x ∈ W.support) ∧
      (∀ g : Fin (n + omega.length) → Bool,
        segs.foldr (fun s acc => bne (bne (g s.u) (g s.v)) acc) false = bne (g a) (g b)) := by
  rcases exists_hsegments_of_path_subwalk W hab hpath ha hb with ⟨segs, hsub, hfold⟩
  exact ⟨segs, fun s hs => (hsub s hs).support_subset, hfold⟩

/-- Whether both endpoints of an `HSegment` lie on `C₁` (`n ≤ u.1 ∧ n ≤ v.1`). -/
def isTopSeg {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s : HSegment G omega) : Bool :=
  decide (n ≤ s.u.1 ∧ n ≤ s.v.1)

/-- Whether both endpoints of an `HSegment` lie in `omega` (`u.1 < n ∧ v.1 < n`). -/
def isBotSeg {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s : HSegment G omega) : Bool :=
  decide (s.u.1 < n ∧ s.v.1 < n)

/-- Every neighbor in `auxGraph81 G omega` of a vertex `x` on `C₁` (`n ≤ x.1`) belongs to `V(H)`. -/
theorem isHVert_of_adj_of_ge {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {x w : Fin (n + omega.length)} (hx : n ≤ x.1) (hadj : (auxGraph81 G omega).Adj x w) :
    isHVert n omega w = true := by
  rcases hadj with ⟨_, ⟨hxl, _, _⟩ | ⟨i, h1⟩ | ⟨i, h2⟩ | ⟨i, hpos, h3⟩⟩
  · omega
  · have hw : n ≤ w.1 := by rcases h1 with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
    simp [isHVert, show ¬ w.1 < n by omega]
  · rcases h2 with ⟨_, hw⟩ | ⟨_, hx_eq⟩
    · have hwl : w.1 < n := by rw [hw]; exact (omega[i]).2
      have hmem : (⟨w.1, hwl⟩ : Fin n) ∈ omega := by
        have heq : (⟨w.1, hwl⟩ : Fin n) = omega[i] := Fin.ext hw
        rw [heq]
        exact List.getElem_mem i.2
      simp [isHVert, hwl, hmem]
    · have : x.1 < n := by rw [hx_eq]; exact (omega[i]).2
      omega
  · rcases h3 with ⟨hx_eq, _⟩ | ⟨_, hx_eq⟩
    · have : x.1 < n := by rw [hx_eq]; exact (omega[i]).2
      omega
    · have : x.1 < n := by
        rw [hx_eq]
        exact (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos)).2
      omega

/-- If an `HSegment` has `n ≤ s.u.1`, its endpoints `s.u` and `s.v` are adjacent in `auxGraph81`. -/
theorem adj_of_hsegment_of_ge_left {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s : HSegment G omega) : n ≤ s.u.1 → (auxGraph81 G omega).Adj s.u s.v := by
  rcases s with ⟨u, v, walk, hne, _, _, _, hinternal⟩
  intro hu
  cases walk with
  | nil => exact absurd rfl hne
  | @cons _ w _ hadj rest =>
    have hw_H : isHVert n omega w = true := isHVert_of_adj_of_ge hu hadj
    have hw_sup : w ∈ (Walk.cons hadj rest).support := by
      simp [Walk.start_mem_support]
    rcases hinternal w hw_sup hw_H with rfl | rfl
    · exact absurd rfl hadj.1
    · exact hadj

/-- If an `HSegment` is not a bottom segment (`n ≤ s.u.1 ∨ n ≤ s.v.1`), its endpoints are adjacent
in `auxGraph81 G omega`. -/
theorem adj_of_hsegment_of_not_isBot {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s : HSegment G omega) (h : n ≤ s.u.1 ∨ n ≤ s.v.1) :
    (auxGraph81 G omega).Adj s.u s.v := by
  rcases h with hu | hv
  · exact adj_of_hsegment_of_ge_left s hu
  · exact (adj_of_hsegment_of_ge_left s.reverse hv).symm

theorem bne_decide_eq_false_iff {p q : Prop} [Decidable p] [Decidable q] :
    bne (decide p) (decide q) = false ↔ (p ↔ q) := by
  cases Decidable.em p <;> cases Decidable.em q <;> simp [*]

/-- For a top segment (`isTopSeg s = true`) that does not contain both `s₂ = c₁(1)` and `t₁ = c₁(2)`,
`{posH s.u, posH s.v} = {d, d + 1}` for some `d`, so `cmpIdx2` does not change across `(s.u, s.v)`
with respect to any `y ∉ {s.u, s.v}` on `C₁` (`n ≤ y.1`). -/
theorem bne_cmpIdx2_of_isTopSeg {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hk : 4 ≤ omega.length) (s : HSegment G omega) (htop : isTopSeg s = true)
    (hno_wrap : ¬ (s2Vert n omega.length hk ∈ s.walk.support ∧
                   t1Vert n omega.length hk ∈ s.walk.support))
    {y : Fin (n + omega.length)} (hy : n ≤ y.1) (hyu : y ≠ s.u) (hyv : y ≠ s.v) :
    bne (cmpIdx2 n omega s.u y) (cmpIdx2 n omega s.v y) = false ∧
    bne (cmpIdx2 n omega y s.u) (cmpIdx2 n omega y s.v) = false := by
  simp only [isTopSeg, decide_eq_true_eq] at htop
  rcases htop with ⟨hu_ge, hv_ge⟩
  have hadj := adj_of_hsegment_of_ge_left s hu_ge
  rcases hadj with ⟨_, ⟨hxl, _, _⟩ | ⟨i, h1⟩ | ⟨i, h2⟩ | ⟨i, hpos, h3⟩⟩
  · omega
  · have hi_ne1 : i.1 ≠ 1 := by
      intro hi1
      apply hno_wrap
      have h_s2_t1 : (s.u = s2Vert n omega.length hk ∧ s.v = t1Vert n omega.length hk) ∨
          (s.v = s2Vert n omega.length hk ∧ s.u = t1Vert n omega.length hk) := by
        rcases h1 with ⟨hu_i, hv_i⟩ | ⟨hv_i, hu_i⟩
        · left
          constructor
          · ext; simp only [s2Vert, c1Vert]; omega
          · ext; simp only [t1Vert, c1Vert]; rw [hv_i, hi1, Nat.mod_eq_of_lt (by omega)]
        · right
          constructor
          · ext; simp only [s2Vert, c1Vert]; omega
          · ext; simp only [t1Vert, c1Vert]; rw [hu_i, hi1, Nat.mod_eq_of_lt (by omega)]
      rcases h_s2_t1 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨h1' ▸ Walk.start_mem_support s.walk, h2' ▸ Walk.end_mem_support s.walk⟩
      · exact ⟨h1' ▸ Walk.end_mem_support s.walk, h2' ▸ Walk.start_mem_support s.walk⟩
    have hsucc : distFrom2 omega.length ((i.1 + 1) % omega.length) =
        distFrom2 omega.length i.1 + 1 :=
      distFrom2_succ_mod (by omega) i.2 hi_ne1
    have hpos_uv : (posH n omega s.u = distFrom2 omega.length i.1 ∧
                    posH n omega s.v = distFrom2 omega.length i.1 + 1) ∨
                   (posH n omega s.v = distFrom2 omega.length i.1 ∧
                    posH n omega s.u = distFrom2 omega.length i.1 + 1) := by
      simp only [posH, show ¬ s.u.1 < n by omega, show ¬ s.v.1 < n by omega, ↓reduceDIte]
      rcases h1 with ⟨hu_i, hv_i⟩ | ⟨hv_i, hu_i⟩
      · left
        have e1 : s.u.1 - n = i.1 := by omega
        have e2 : s.v.1 - n = (i.1 + 1) % omega.length := by omega
        rw [e1, e2, hsucc]
        exact ⟨rfl, rfl⟩
      · right
        have e1 : s.v.1 - n = i.1 := by omega
        have e2 : s.u.1 - n = (i.1 + 1) % omega.length := by omega
        rw [e1, e2, hsucc]
        exact ⟨rfl, rfl⟩
    have hy_ne_pos_u : posH n omega y ≠ posH n omega s.u := by
      intro heq
      apply hyu
      apply idx2_injective_of_isHVert (by omega)
      · simp [isHVert, show ¬ y.1 < n by omega]
      · exact s.hu
      · simp [idx2, show ¬ y.1 < n by omega, show ¬ s.u.1 < n by omega, heq]
    have hy_ne_pos_v : posH n omega y ≠ posH n omega s.v := by
      intro heq
      apply hyv
      apply idx2_injective_of_isHVert (by omega)
      · simp [isHVert, show ¬ y.1 < n by omega]
      · exact s.hv
      · simp [idx2, show ¬ y.1 < n by omega, show ¬ s.v.1 < n by omega, heq]
    simp only [cmpIdx2, idx2, show ¬ s.u.1 < n by omega,
      show ¬ s.v.1 < n by omega, show ¬ y.1 < n by omega, ↓reduceIte,
      bne_decide_eq_false_iff]
    rcases hpos_uv with ⟨hpu, hpv⟩ | ⟨hpv, hpu⟩ <;> constructor <;> omega
  · rcases h2 with ⟨_, h⟩ | ⟨_, h⟩
    · have : s.v.1 < n := by rw [h]; exact (omega[i]).2
      omega
    · have : s.u.1 < n := by rw [h]; exact (omega[i]).2
      omega
  · rcases h3 with ⟨h, _⟩ | ⟨_, h⟩
    · have : s.u.1 < n := by rw [h]; exact (omega[i]).2
      omega
    · have : s.u.1 < n := by
        rw [h]
        exact (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos)).2
      omega

/-- For a rung segment (`isTopSeg s = false` and `isBotSeg s = false`), `{idx2 s.u, idx2 s.v} =
{2 * d, 2 * d + 1}` for some `d`, so `cmpIdx2` does not change across `(s.u, s.v)` with respect to
any `y ∉ {s.u, s.v}` in `V(H)`. -/
theorem bne_cmpIdx2_of_rungSeg {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hnodup : omega.Nodup) (hk : 2 ≤ omega.length) (s : HSegment G omega)
    (hnot_top : isTopSeg s = false) (hnot_bot : isBotSeg s = false)
    {y : Fin (n + omega.length)} (hy : isHVert n omega y = true) (hyu : y ≠ s.u) (hyv : y ≠ s.v) :
    bne (cmpIdx2 n omega s.u y) (cmpIdx2 n omega s.v y) = false ∧
    bne (cmpIdx2 n omega y s.u) (cmpIdx2 n omega y s.v) = false := by
  simp only [isTopSeg, decide_eq_false_iff_not] at hnot_top
  simp only [isBotSeg, decide_eq_false_iff_not] at hnot_bot
  have h_or : n ≤ s.u.1 ∨ n ≤ s.v.1 := by omega
  have hadj := adj_of_hsegment_of_not_isBot s h_or
  rcases hadj with ⟨_, ⟨hxl, hyl, _⟩ | ⟨i, h1⟩ | ⟨i, h2⟩ | ⟨i, hpos, h3⟩⟩
  · exfalso; exact hnot_bot ⟨hxl, hyl⟩
  · exfalso; apply hnot_top; rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;> omega
  · have hidx2_uv : (idx2 n omega s.u = 2 * distFrom2 omega.length i.1 ∧
                     idx2 n omega s.v = 2 * distFrom2 omega.length i.1 + 1) ∨
                    (idx2 n omega s.v = 2 * distFrom2 omega.length i.1 ∧
                     idx2 n omega s.u = 2 * distFrom2 omega.length i.1 + 1) := by
      rcases h2 with ⟨hu_i, hv_i⟩ | ⟨hv_i, hu_i⟩
      · left
        have hul : ¬ s.u.1 < n := by omega
        have hvl : s.v.1 < n := by rw [hv_i]; exact (omega[i]).2
        have hv_fin : (⟨s.v.1, hvl⟩ : Fin n) = omega[i] := Fin.ext hv_i
        simp only [idx2, posH, hul, hvl, ↓reduceIte, ↓reduceDIte,
          hv_fin, idxOf_getElem_of_nodup hnodup i]
        have esub : s.u.1 - n = i.1 := by omega
        simp [esub]
      · right
        have hvl : ¬ s.v.1 < n := by omega
        have hul : s.u.1 < n := by rw [hu_i]; exact (omega[i]).2
        have hu_fin : (⟨s.u.1, hul⟩ : Fin n) = omega[i] := Fin.ext hu_i
        simp only [idx2, posH, hvl, hul, ↓reduceIte, ↓reduceDIte,
          hu_fin, idxOf_getElem_of_nodup hnodup i]
        have esub : s.v.1 - n = i.1 := by omega
        simp [esub]
    have hy_ne_u : idx2 n omega y ≠ idx2 n omega s.u :=
      fun heq => hyu (idx2_injective_of_isHVert hk hy s.hu heq)
    have hy_ne_v : idx2 n omega y ≠ idx2 n omega s.v :=
      fun heq => hyv (idx2_injective_of_isHVert hk hy s.hv heq)
    simp only [cmpIdx2, bne_decide_eq_false_iff]
    rcases hidx2_uv with ⟨hiu, hiv⟩ | ⟨hiv, hiu⟩ <;> constructor <;> omega
  · exfalso
    apply hnot_bot
    rcases h3 with ⟨hu_i, hv_i⟩ | ⟨hv_i, hu_i⟩
    · exact ⟨by rw [hu_i]; exact (omega[i]).2,
        by rw [hv_i]; exact (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos)).2⟩
    · exact ⟨by rw [hu_i]; exact (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos)).2,
        by rw [hv_i]; exact (omega[i]).2⟩

/-- 2D increment of `cmpIdx2` across two segments `s₁` and `s₂`. -/
def deltaSeg {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s₁ s₂ : HSegment G omega) : Bool :=
  bne (bne (cmpIdx2 n omega s₁.u s₂.u) (cmpIdx2 n omega s₁.v s₂.u))
      (bne (cmpIdx2 n omega s₁.u s₂.v) (cmpIdx2 n omega s₁.v s₂.v))

theorem deltaSeg_symm_form {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s₁ s₂ : HSegment G omega) :
    deltaSeg s₁ s₂ =
      bne (bne (cmpIdx2 n omega s₁.u s₂.u) (cmpIdx2 n omega s₁.u s₂.v))
          (bne (cmpIdx2 n omega s₁.v s₂.u) (cmpIdx2 n omega s₁.v s₂.v)) := by
  simp only [deltaSeg]
  cases cmpIdx2 n omega s₁.u s₂.u <;> cases cmpIdx2 n omega s₁.v s₂.u <;>
    cases cmpIdx2 n omega s₁.u s₂.v <;> cases cmpIdx2 n omega s₁.v s₂.v <;> rfl

/-- Pointwise decomposition of `deltaSeg s₁ s₂` into `isTopSeg s₁`, `isTopSeg s₂`, and
`isBotSeg s₁ && isBotSeg s₂` for disjoint segments `s₁, s₂` avoiding wrap-around on `C₁`. -/
theorem deltaSeg_decomp_pointwise {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hnodup : omega.Nodup) (hk : 4 ≤ omega.length) (s₁ s₂ : HSegment G omega)
    (hdisj : List.Disjoint s₁.walk.support s₂.walk.support)
    (hno_wrap₁ : ¬ (s2Vert n omega.length hk ∈ s₁.walk.support ∧
                    t1Vert n omega.length hk ∈ s₁.walk.support)) :
    deltaSeg s₁ s₂ =
      bne (bne (isTopSeg s₁ && deltaSeg s₁ s₂) (isTopSeg s₂ && deltaSeg s₁ s₂))
          (isBotSeg s₁ && isBotSeg s₂ && deltaSeg s₁ s₂) := by
  have hu2_ne_u1 : s₂.u ≠ s₁.u :=
    fun h => hdisj (Walk.start_mem_support s₁.walk) (h ▸ Walk.start_mem_support s₂.walk)
  have hu2_ne_v1 : s₂.u ≠ s₁.v :=
    fun h => hdisj (Walk.end_mem_support s₁.walk) (h ▸ Walk.start_mem_support s₂.walk)
  have hv2_ne_u1 : s₂.v ≠ s₁.u :=
    fun h => hdisj (Walk.start_mem_support s₁.walk) (h ▸ Walk.end_mem_support s₂.walk)
  have hv2_ne_v1 : s₂.v ≠ s₁.v :=
    fun h => hdisj (Walk.end_mem_support s₁.walk) (h ▸ Walk.end_mem_support s₂.walk)
  by_cases ht1 : isTopSeg s₁ = true
  · have hb1 : isBotSeg s₁ = false := by
      simp only [isTopSeg, decide_eq_true_eq] at ht1
      simp only [isBotSeg, decide_eq_false_iff_not]; omega
    by_cases ht2 : isTopSeg s₂ = true
    · simp only [isTopSeg, decide_eq_true_eq] at ht2
      have h_u2 := (bne_cmpIdx2_of_isTopSeg hk s₁ ht1 hno_wrap₁ ht2.1 hu2_ne_u1 hu2_ne_v1).1
      have h_v2 := (bne_cmpIdx2_of_isTopSeg hk s₁ ht1 hno_wrap₁ ht2.2 hv2_ne_u1 hv2_ne_v1).1
      have hdel : deltaSeg s₁ s₂ = false := by simp [deltaSeg, h_u2, h_v2]
      simp [hdel]
    · simp only [Bool.not_eq_true] at ht2
      simp [ht1, hb1, ht2]
  · simp only [Bool.not_eq_true] at ht1
    by_cases hb1 : isBotSeg s₁ = true
    · by_cases ht2 : isTopSeg s₂ = true
      · have hb2 : isBotSeg s₂ = false := by
          simp only [isTopSeg, decide_eq_true_eq] at ht2
          simp only [isBotSeg, decide_eq_false_iff_not]; omega
        simp [ht1, hb1, ht2, hb2]
      · simp only [Bool.not_eq_true] at ht2
        by_cases hb2 : isBotSeg s₂ = true
        · simp [ht1, hb1, ht2, hb2]
        · simp only [Bool.not_eq_true] at hb2
          have h_u1 := (bne_cmpIdx2_of_rungSeg hnodup (by omega) s₂ ht2 hb2
            s₁.hu hu2_ne_u1.symm hv2_ne_u1.symm).2
          have h_v1 := (bne_cmpIdx2_of_rungSeg hnodup (by omega) s₂ ht2 hb2
            s₁.hv hu2_ne_v1.symm hv2_ne_v1.symm).2
          have hdel : deltaSeg s₁ s₂ = false := by
            rw [deltaSeg_symm_form, h_u1, h_v1]
            rfl
          simp [hdel]
    · simp only [Bool.not_eq_true] at hb1
      have h_u2 := (bne_cmpIdx2_of_rungSeg hnodup (by omega) s₁ ht1 hb1
        s₂.hu hu2_ne_u1 hu2_ne_v1).1
      have h_v2 := (bne_cmpIdx2_of_rungSeg hnodup (by omega) s₁ ht1 hb1
        s₂.hv hv2_ne_u1 hv2_ne_v1).1
      have hdel : deltaSeg s₁ s₂ = false := by simp [deltaSeg, h_u2, h_v2]
      simp [hdel]

/-- Double XOR sum over `L₁ × L₂`. -/
def xorSum2 {α β : Type*} (h : α → β → Bool) (L₁ : List α) (L₂ : List β) : Bool :=
  L₁.foldr (fun a acc => bne (L₂.foldr (fun b acc₂ => bne (h a b) acc₂) false) acc) false

theorem foldr_bne_eq_false_of_forall {α : Type*} (f : α → Bool) (L : List α)
    (h : ∀ x ∈ L, f x = false) :
    L.foldr (fun x acc => bne (f x) acc) false = false := by
  induction L with
  | nil => rfl
  | cons x rest ih =>
    simp [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem xorSum2_eq_true_implies_exists {α β : Type*} (h : α → β → Bool) (L₁ : List α) (L₂ : List β)
    (htrue : xorSum2 h L₁ L₂ = true) :
    ∃ a ∈ L₁, ∃ b ∈ L₂, h a b = true := by
  by_contra hno
  have hzero : xorSum2 h L₁ L₂ = false := by
    apply foldr_bne_eq_false_of_forall
    intro a ha
    apply foldr_bne_eq_false_of_forall
    intro b hb
    exact Bool.eq_false_iff.mpr (fun ht => hno ⟨a, ha, b, hb, ht⟩)
  rw [hzero] at htrue
  contradiction

theorem foldr_bne_bne {α : Type*} (f₁ f₂ : α → Bool) (L : List α) :
    L.foldr (fun x acc => bne (bne (f₁ x) (f₂ x)) acc) false =
      bne (L.foldr (fun x acc => bne (f₁ x) acc) false)
          (L.foldr (fun x acc => bne (f₂ x) acc) false) := by
  induction L with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.foldr_cons, ih]
    cases f₁ x <;> cases f₂ x <;>
      cases rest.foldr (fun x acc => bne (f₁ x) acc) false <;>
      cases rest.foldr (fun x acc => bne (f₂ x) acc) false <;> rfl

theorem xorSum2_bne {α β : Type*} (h₁ h₂ : α → β → Bool) (L₁ : List α) (L₂ : List β) :
    xorSum2 (fun a b => bne (h₁ a b) (h₂ a b)) L₁ L₂ =
      bne (xorSum2 h₁ L₁ L₂) (xorSum2 h₂ L₁ L₂) := by
  unfold xorSum2
  rw [← foldr_bne_bne]
  congr 1
  funext a acc
  rw [foldr_bne_bne]

theorem foldr_bne_and_const {α : Type*} (c : Bool) (f : α → Bool) (L : List α) :
    L.foldr (fun x acc => bne (c && f x) acc) false =
      (c && L.foldr (fun x acc => bne (f x) acc) false) := by
  induction L with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldr_cons, ih]
    cases c <;> cases f x <;> cases rest.foldr (fun x acc => bne (f x) acc) false <;> rfl

theorem xorSum2_congr_on {α β : Type*} {h₁ h₂ : α → β → Bool} {L₁ : List α} {L₂ : List β}
    (heq : ∀ a ∈ L₁, ∀ b ∈ L₂, h₁ a b = h₂ a b) :
    xorSum2 h₁ L₁ L₂ = xorSum2 h₂ L₁ L₂ := by
  induction L₁ with
  | nil => rfl
  | cons a rest ih =>
    simp only [xorSum2, List.foldr_cons]
    congr 1
    · clear ih
      have ha : a ∈ a :: rest := List.mem_cons_self
      revert ha
      induction L₂ with
      | nil => intro _; rfl
      | cons b rest₂ ih₂ =>
        intro ha
        simp only [List.foldr_cons, heq a ha b List.mem_cons_self]
        congr 1
        exact ih₂ (fun a' ha' b' hb' => heq a' ha' b' (List.mem_cons_of_mem _ hb')) ha
    · exact ih (fun a' ha' b' hb' => heq a' (List.mem_cons_of_mem _ ha') b' hb')

/-- Given a bottom segment `s` whose endpoints `u₀, v₀ ∈ omega` are not consecutive on `C₂`,
every edge of `s.walk` is an edge of `G`, so `s.walk` projects to a simple path in `G`. -/
def projWalkToG {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)} :
    ∀ {a b : Fin (n + omega.length)} (W : (auxGraph81 G omega).Walk a b)
      (hV : ∀ x ∈ W.support, x.1 < n)
      (_hE : ∀ ⦃x y : Fin (n + omega.length)⦄ (hx : x.1 < n) (hy : y.1 < n),
        x ∈ W.support → y ∈ W.support → (auxGraph81 G omega).Adj x y → G.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩),
      G.Walk ⟨a.1, hV a (Walk.start_mem_support W)⟩ ⟨b.1, hV b (Walk.end_mem_support W)⟩
  | _, _, .nil, _, _ => .nil
  | a, _, .cons (v := c) hadj rest, hV, hE =>
    .cons
      (hE (hV a (by simp)) (hV c (by simp [Walk.start_mem_support]))
        (by simp) (by simp [Walk.start_mem_support]) hadj)
      (projWalkToG rest
        (fun x hx => hV x (by simp [hx]))
        (fun x y hx hy hxW hyW hadj' => hE hx hy (by simp [hxW]) (by simp [hyW]) hadj'))

theorem map_support_projWalkToG {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {a b : Fin (n + omega.length)} (W : (auxGraph81 G omega).Walk a b)
    (hV : ∀ x ∈ W.support, x.1 < n)
    (hE : ∀ ⦃x y : Fin (n + omega.length)⦄ (hx : x.1 < n) (hy : y.1 < n),
      x ∈ W.support → y ∈ W.support → (auxGraph81 G omega).Adj x y → G.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩) :
    (projWalkToG W hV hE).support.map (inGVert omega.length) = W.support := by
  induction W with
  | nil => simp [projWalkToG, inGVert]
  | cons hadj rest ih =>
    simp only [projWalkToG, Walk.support_cons, List.map_cons, ih]
    rfl

theorem isPath_projWalkToG {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {a b : Fin (n + omega.length)} {W : (auxGraph81 G omega).Walk a b} (hpath : W.IsPath)
    (hV : ∀ x ∈ W.support, x.1 < n)
    (hE : ∀ ⦃x y : Fin (n + omega.length)⦄ (hx : x.1 < n) (hy : y.1 < n),
      x ∈ W.support → y ∈ W.support → (auxGraph81 G omega).Adj x y → G.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩) :
    (projWalkToG W hV hE).IsPath := by
  rw [Walk.isPath_def]
  have hmap := map_support_projWalkToG W hV hE
  have hnodup : ((projWalkToG W hV hE).support.map (inGVert omega.length)).Nodup := by
    rw [hmap]
    exact hpath.support_nodup
  exact List.Nodup.of_map _ hnodup

theorem mem_support_of_mem_projWalkToG {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {a b : Fin (n + omega.length)} (W : (auxGraph81 G omega).Walk a b)
    (hV : ∀ x ∈ W.support, x.1 < n)
    (hE : ∀ ⦃x y : Fin (n + omega.length)⦄ (hx : x.1 < n) (hy : y.1 < n),
      x ∈ W.support → y ∈ W.support → (auxGraph81 G omega).Adj x y → G.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩)
    {u : Fin n} (hu : u ∈ (projWalkToG W hV hE).support) :
    inGVert omega.length u ∈ W.support := by
  rw [← map_support_projWalkToG W hV hE]
  exact List.mem_map_of_mem hu

/-- Any bottom `HSegment` whose endpoints do not have consecutive `posH` modulo `k` projects
to a simple path in `G`. -/
def botSegToGPath {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hk : 4 ≤ omega.length) (s : HSegment G omega)
    (hu : s.u.1 < n) (hv : s.v.1 < n)
    (hno_c2 : ∀ i : Fin omega.length,
      ¬ ((s.u.1 = (omega[i]).1 ∧
          s.v.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1) ∨
         (s.v.1 = (omega[i]).1 ∧
          s.u.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1))) :
    G.Walk ⟨s.u.1, hu⟩ ⟨s.v.1, hv⟩ :=
  have hV : ∀ x ∈ s.walk.support, x.1 < n := by
    intro x hx
    by_contra hge
    have hH : isHVert n omega x = true := by simp [isHVert, hge]
    rcases s.hinternal x hx hH with rfl | rfl <;> omega
  have hE : ∀ ⦃x y : Fin (n + omega.length)⦄ (hx : x.1 < n) (hy : y.1 < n),
      x ∈ s.walk.support → y ∈ s.walk.support → (auxGraph81 G omega).Adj x y →
      G.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
    intro x y hx hy hxW hyW hadj
    rcases hadj with ⟨hne, ⟨hx', hy', hadjG⟩ | ⟨i, h1⟩ | ⟨i, h2⟩ | ⟨i, hpos, h3⟩⟩
    · exact hadjG
    · exfalso; rcases h1 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · exfalso; rcases h2 with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · exfalso
      have hxH : isHVert n omega x = true := by
        simp only [isHVert, hx, ↓reduceDIte, decide_eq_true_eq]
        rcases h3 with ⟨hx_i, _⟩ | ⟨_, hx_i⟩
        · have heq : (⟨x.1, hx⟩ : Fin n) = omega[i] := Fin.ext hx_i
          rw [heq]; exact List.getElem_mem i.2
        · have heq : (⟨x.1, hx⟩ : Fin n) =
              omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos) := Fin.ext hx_i
          rw [heq]; exact List.getElem_mem _
      have hyH : isHVert n omega y = true := by
        simp only [isHVert, hy, ↓reduceDIte, decide_eq_true_eq]
        rcases h3 with ⟨_, hy_i⟩ | ⟨hy_i, _⟩
        · have heq : (⟨y.1, hy⟩ : Fin n) =
              omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ hpos) := Fin.ext hy_i
          rw [heq]; exact List.getElem_mem _
        · have heq : (⟨y.1, hy⟩ : Fin n) = omega[i] := Fin.ext hy_i
          rw [heq]; exact List.getElem_mem i.2
      rcases s.hinternal x hxW hxH with rfl | rfl <;>
        rcases s.hinternal y hyW hyH with rfl | rfl
      · exact hne rfl
      · exact hno_c2 i h3
      · exact hno_c2 i h3.symm
      · exact hne rfl
  projWalkToG s.walk hV hE

theorem isPath_botSegToGPath {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hk : 4 ≤ omega.length) (s : HSegment G omega)
    (hu : s.u.1 < n) (hv : s.v.1 < n)
    (hno_c2 : ∀ i : Fin omega.length,
      ¬ ((s.u.1 = (omega[i]).1 ∧
          s.v.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1) ∨
         (s.v.1 = (omega[i]).1 ∧
          s.u.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1))) :
    (botSegToGPath hk s hu hv hno_c2).IsPath := by
  unfold botSegToGPath
  exact isPath_projWalkToG s.isPath _ _

theorem mem_support_of_mem_botSegToGPath {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hk : 4 ≤ omega.length) (s : HSegment G omega)
    (hu : s.u.1 < n) (hv : s.v.1 < n)
    (hno_c2 : ∀ i : Fin omega.length,
      ¬ ((s.u.1 = (omega[i]).1 ∧
          s.v.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1) ∨
         (s.v.1 = (omega[i]).1 ∧
          s.u.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1)))
    {u : Fin n} (hu_mem : u ∈ (botSegToGPath hk s hu hv hno_c2).support) :
    inGVert omega.length u ∈ s.walk.support := by
  unfold botSegToGPath at hu_mem
  exact mem_support_of_mem_projWalkToG s.walk _ _ hu_mem

/-- If `CrossesInOmega omega p₁ q₁ p₂ q₂` and `omega.Nodup`, then `p₁` and `p₂` are not
consecutive along `C₂`. -/
theorem CrossesInOmega.not_adj_c2 {n : ℕ} {omega : List (Fin n)} (hnodup : omega.Nodup)
    (hk : 4 ≤ omega.length) {p₁ q₁ p₂ q₂ : Fin n} (h : CrossesInOmega omega p₁ q₁ p₂ q₂)
    (i : Fin omega.length) :
    ¬ ((p₁.1 = (omega[i]).1 ∧
        p₂.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1) ∨
       (p₂.1 = (omega[i]).1 ∧
        p₁.1 = (omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))).1)) := by
  rcases h with ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, hcases⟩
  have h_nonconsec : ∀ (a c : ℕ) (ha : a < omega.length) (hc : c < omega.length),
      (a = i₁ ∧ c = i₃ ∨ a = i₂ ∧ c = i₄) →
      ¬ ((a = i.1 ∧ c = (i.1 + 1) % omega.length) ∨
         (c = i.1 ∧ a = (i.1 + 1) % omega.length)) := by
    intro a c ha hc hac hcon
    have hi : i.1 < omega.length := i.2
    rw [mod_lt_two_mul (by omega)] at hcon
    split_ifs at hcon <;> omega
  intro hc2
  have hp : (p₁ = omega[i] ∧ p₂ = omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))) ∨
            (p₂ = omega[i] ∧ p₁ = omega[(i.1 + 1) % omega.length]'(Nat.mod_lt _ (by omega))) := by
    rcases hc2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
    · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
  rcases hcases with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, _⟩ | ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · apply h_nonconsec i₁ i₃ (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩)
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩
    · exact Or.inr ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩
  · apply h_nonconsec i₁ i₃ (by omega) (by omega) (Or.inl ⟨rfl, rfl⟩)
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩
    · exact Or.inl ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩
  · apply h_nonconsec i₂ i₄ (by omega) h₄ (Or.inr ⟨rfl, rfl⟩)
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩
    · exact Or.inr ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩
  · apply h_nonconsec i₂ i₄ (by omega) h₄ (Or.inr ⟨rfl, rfl⟩)
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩
    · exact Or.inl ⟨(List.Nodup.getElem_inj_iff hnodup).mp h1, (List.Nodup.getElem_inj_iff hnodup).mp h2⟩

theorem cmpIdx2_eq_posH_lt {n : ℕ} {omega : List (Fin n)} {x y : Fin (n + omega.length)}
    (hx : x.1 < n) (hy : y.1 < n) :
    cmpIdx2 n omega x y = decide (posH n omega x < posH n omega y) := by
  simp only [cmpIdx2, idx2, hx, hy, ↓reduceIte, decide_eq_decide]
  omega

theorem posH_ne_of_ne_of_lt {n : ℕ} {omega : List (Fin n)} (hk : 2 ≤ omega.length)
    {x y : Fin (n + omega.length)} (hx : x.1 < n) (hy : y.1 < n)
    (hxH : isHVert n omega x = true) (hyH : isHVert n omega y = true) (hne : x ≠ y) :
    posH n omega x ≠ posH n omega y := by
  intro heq
  apply hne
  apply idx2_injective_of_isHVert hk hxH hyH
  simp [idx2, hx, hy, heq]

theorem alt_of_bne_lt {dp₁ dp₂ dq₁ dq₂ : ℕ}
    (h11 : dp₁ ≠ dq₁) (h21 : dp₂ ≠ dq₁) (h12 : dp₁ ≠ dq₂) (h22 : dp₂ ≠ dq₂)
    (h : bne (bne (decide (dp₁ < dq₁)) (decide (dp₂ < dq₁)))
             (bne (decide (dp₁ < dq₂)) (decide (dp₂ < dq₂))) = true) :
    (dp₁ < dq₁ ∧ dq₁ < dp₂ ∧ dp₂ < dq₂) ∨
    (dp₁ < dq₂ ∧ dq₂ < dp₂ ∧ dp₂ < dq₁) ∨
    (dp₂ < dq₁ ∧ dq₁ < dp₁ ∧ dp₁ < dq₂) ∨
    (dp₂ < dq₂ ∧ dq₂ < dp₁ ∧ dp₁ < dq₁) ∨
    (dq₁ < dp₁ ∧ dp₁ < dq₂ ∧ dq₂ < dp₂) ∨
    (dq₂ < dp₁ ∧ dp₁ < dq₁ ∧ dq₁ < dp₂) ∨
    (dq₁ < dp₂ ∧ dp₂ < dq₂ ∧ dq₂ < dp₁) ∨
    (dq₂ < dp₂ ∧ dp₂ < dq₁ ∧ dq₁ < dp₁) := by
  revert h
  cases h_a : decide (dp₁ < dq₁) <;> cases h_b : decide (dp₂ < dq₁) <;>
    cases h_c : decide (dp₁ < dq₂) <;> cases h_d : decide (dp₂ < dq₂) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at * <;>
    intro h <;> try contradiction
  all_goals omega

theorem crosses_of_distFrom2_lt {n : ℕ} {omega : List (Fin n)} (hk : 4 ≤ omega.length)
    {ia ib ic id : ℕ} (hia : ia < omega.length) (hib : ib < omega.length)
    (hic : ic < omega.length) (hid : id < omega.length)
    (hab : distFrom2 omega.length ia < distFrom2 omega.length ib)
    (hbc : distFrom2 omega.length ib < distFrom2 omega.length ic)
    (hcd : distFrom2 omega.length ic < distFrom2 omega.length id) :
    CrossesInOmega omega (omega[ia]'hia) (omega[ib]'hib) (omega[ic]'hic) (omega[id]'hid) := by
  rw [distFrom2_eq_if (by omega) hia, distFrom2_eq_if (by omega) hib] at hab
  rw [distFrom2_eq_if (by omega) hib, distFrom2_eq_if (by omega) hic] at hbc
  rw [distFrom2_eq_if (by omega) hic, distFrom2_eq_if (by omega) hid] at hcd
  by_cases hd2 : 2 ≤ id
  · refine ⟨ia, ib, ic, id, ?_, ?_, ?_, hid, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩⟩ <;>
      (split_ifs at hab hbc hcd <;> omega)
  · by_cases hc2 : 2 ≤ ic
    · refine ⟨id, ia, ib, ic, ?_, ?_, ?_, hic, Or.inr ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩⟩ <;>
        (split_ifs at hab hbc hcd <;> omega)
    · refine ⟨ic, id, ia, ib, ?_, ?_, ?_, hib, Or.inl ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩⟩ <;>
        (split_ifs at hab hbc hcd <;> omega)

/-- If two disjoint bottom segments `s₁, s₂` have `deltaSeg s₁ s₂ = true`, then their endpoints
cross in `omega`. -/
theorem crosses_of_deltaSeg_bot {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hk : 4 ≤ omega.length) (s₁ s₂ : HSegment G omega)
    (hdisj : List.Disjoint s₁.walk.support s₂.walk.support)
    (hu₁ : s₁.u.1 < n) (hv₁ : s₁.v.1 < n) (hu₂ : s₂.u.1 < n) (hv₂ : s₂.v.1 < n)
    (hdel : deltaSeg s₁ s₂ = true) :
    CrossesInOmega omega ⟨s₁.u.1, hu₁⟩ ⟨s₂.u.1, hu₂⟩ ⟨s₁.v.1, hv₁⟩ ⟨s₂.v.1, hv₂⟩ := by
  have hp₁_om : (⟨s₁.u.1, hu₁⟩ : Fin n) ∈ omega := by
    have := s₁.hu; simp only [isHVert, hu₁, ↓reduceDIte, decide_eq_true_eq] at this; exact this
  have hp₂_om : (⟨s₁.v.1, hv₁⟩ : Fin n) ∈ omega := by
    have := s₁.hv; simp only [isHVert, hv₁, ↓reduceDIte, decide_eq_true_eq] at this; exact this
  have hq₁_om : (⟨s₂.u.1, hu₂⟩ : Fin n) ∈ omega := by
    have := s₂.hu; simp only [isHVert, hu₂, ↓reduceDIte, decide_eq_true_eq] at this; exact this
  have hq₂_om : (⟨s₂.v.1, hv₂⟩ : Fin n) ∈ omega := by
    have := s₂.hv; simp only [isHVert, hv₂, ↓reduceDIte, decide_eq_true_eq] at this; exact this
  have hip₁ : omega.idxOf ⟨s₁.u.1, hu₁⟩ < omega.length := List.idxOf_lt_length_of_mem hp₁_om
  have hip₂ : omega.idxOf ⟨s₁.v.1, hv₁⟩ < omega.length := List.idxOf_lt_length_of_mem hp₂_om
  have hiq₁ : omega.idxOf ⟨s₂.u.1, hu₂⟩ < omega.length := List.idxOf_lt_length_of_mem hq₁_om
  have hiq₂ : omega.idxOf ⟨s₂.v.1, hv₂⟩ < omega.length := List.idxOf_lt_length_of_mem hq₂_om
  have hne11 : posH n omega s₁.u ≠ posH n omega s₂.u :=
    posH_ne_of_ne_of_lt (by omega) hu₁ hu₂ s₁.hu s₂.hu
      (fun h => hdisj (Walk.start_mem_support s₁.walk)
        (by rw [h]; exact Walk.start_mem_support s₂.walk))
  have hne21 : posH n omega s₁.v ≠ posH n omega s₂.u :=
    posH_ne_of_ne_of_lt (by omega) hv₁ hu₂ s₁.hv s₂.hu
      (fun h => hdisj (Walk.end_mem_support s₁.walk)
        (by rw [h]; exact Walk.start_mem_support s₂.walk))
  have hne12 : posH n omega s₁.u ≠ posH n omega s₂.v :=
    posH_ne_of_ne_of_lt (by omega) hu₁ hv₂ s₁.hu s₂.hv
      (fun h => hdisj (Walk.start_mem_support s₁.walk)
        (by rw [h]; exact Walk.end_mem_support s₂.walk))
  have hne22 : posH n omega s₁.v ≠ posH n omega s₂.v :=
    posH_ne_of_ne_of_lt (by omega) hv₁ hv₂ s₁.hv s₂.hv
      (fun h => hdisj (Walk.end_mem_support s₁.walk)
        (by rw [h]; exact Walk.end_mem_support s₂.walk))
  have hdel' : bne (bne (decide (posH n omega s₁.u < posH n omega s₂.u))
                        (decide (posH n omega s₁.v < posH n omega s₂.u)))
                   (bne (decide (posH n omega s₁.u < posH n omega s₂.v))
                        (decide (posH n omega s₁.v < posH n omega s₂.v))) = true := by
    simpa only [deltaSeg, cmpIdx2_eq_posH_lt hu₁ hu₂, cmpIdx2_eq_posH_lt hv₁ hu₂,
      cmpIdx2_eq_posH_lt hu₁ hv₂, cmpIdx2_eq_posH_lt hv₁ hv₂] using hdel
  have h_alt := alt_of_bne_lt hne11 hne21 hne12 hne22 hdel'
  simp only [posH, hu₁, hv₁, hu₂, hv₂, ↓reduceDIte] at h_alt
  have ep₁ : omega[omega.idxOf ⟨s₁.u.1, hu₁⟩]'hip₁ = ⟨s₁.u.1, hu₁⟩ := List.getElem_idxOf hip₁
  have ep₂ : omega[omega.idxOf ⟨s₁.v.1, hv₁⟩]'hip₂ = ⟨s₁.v.1, hv₁⟩ := List.getElem_idxOf hip₂
  have eq₁ : omega[omega.idxOf ⟨s₂.u.1, hu₂⟩]'hiq₁ = ⟨s₂.u.1, hu₂⟩ := List.getElem_idxOf hiq₁
  have eq₂ : omega[omega.idxOf ⟨s₂.v.1, hv₂⟩]'hiq₂ = ⟨s₂.v.1, hv₂⟩ := List.getElem_idxOf hiq₂
  rcases h_alt with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have := crosses_of_distFrom2_lt hk hip₁ hiq₁ hip₂ hiq₂ h1 h2 h3
    rwa [ep₁, ep₂, eq₁, eq₂] at this
  · have := (crosses_of_distFrom2_lt hk hip₁ hiq₂ hip₂ hiq₁ h1 h2 h3).swap_q
    rwa [ep₁, ep₂, eq₁, eq₂] at this
  · have := (crosses_of_distFrom2_lt hk hip₂ hiq₁ hip₁ hiq₂ h1 h2 h3).swap_p
    rwa [ep₁, ep₂, eq₁, eq₂] at this
  · have := (crosses_of_distFrom2_lt hk hip₂ hiq₂ hip₁ hiq₁ h1 h2 h3).swap_p.swap_q
    rwa [ep₁, ep₂, eq₁, eq₂] at this
  · have := (crosses_of_distFrom2_lt hk hiq₁ hip₁ hiq₂ hip₂ h1 h2 h3).symm_pq
    rwa [ep₁, ep₂, eq₁, eq₂] at this
  · have := (crosses_of_distFrom2_lt hk hiq₂ hip₁ hiq₁ hip₂ h1 h2 h3).symm_pq.swap_q
    rwa [ep₁, ep₂, eq₁, eq₂] at this
  · have := (crosses_of_distFrom2_lt hk hiq₁ hip₂ hiq₂ hip₁ h1 h2 h3).symm_pq.swap_p
    rwa [ep₁, ep₂, eq₁, eq₂] at this
  · have := (crosses_of_distFrom2_lt hk hiq₂ hip₂ hiq₁ hip₁ h1 h2 h3).symm_pq.swap_p.swap_q
    rwa [ep₁, ep₂, eq₁, eq₂] at this

/-- **GM XIII (8.1), Easy Claim 1 (page 93)**:
"If we find two such paths it is easy to derive a cross in $(G, \Omega)$" -/
theorem cross_of_auxGraph81_paths {n : ℕ} {G : SimpleGraph (Fin n)}
    {omega : List (Fin n)} (hnodup : omega.Nodup) (hk : 4 ≤ omega.length)
    (R₁ : (auxGraph81 G omega).Walk (s1Vert n omega.length hk) (t1Vert n omega.length hk))
    (R₂ : (auxGraph81 G omega).Walk (s2Vert n omega.length hk) (t2Vert n omega.length hk))
    (hpath₁ : R₁.IsPath) (hpath₂ : R₂.IsPath)
    (hdisj : List.Disjoint R₁.support R₂.support) :
    HasCrossInSociety G omega := by
  have hs₁_ne_t₁ : s1Vert n omega.length hk ≠ t1Vert n omega.length hk := by
    intro h; have := Fin.mk.inj_iff.mp h; omega
  have hs₂_ne_t₂ : s2Vert n omega.length hk ≠ t2Vert n omega.length hk := by
    intro h; have := Fin.mk.inj_iff.mp h; omega
  have hs₁_H : isHVert n omega (s1Vert n omega.length hk) = true := by
    simp [isHVert, s1Vert, c1Vert]
  have ht₁_H : isHVert n omega (t1Vert n omega.length hk) = true := by
    simp [isHVert, t1Vert, c1Vert]
  have hs₂_H : isHVert n omega (s2Vert n omega.length hk) = true := by
    simp [isHVert, s2Vert, c1Vert]
  have ht₂_H : isHVert n omega (t2Vert n omega.length hk) = true := by
    simp [isHVert, t2Vert, c1Vert]
  rcases exists_hsegments_of_path R₁ hs₁_ne_t₁ hpath₁ hs₁_H ht₁_H with ⟨segs₁, hsub₁, hfold₁⟩
  rcases exists_hsegments_of_path R₂ hs₂_ne_t₂ hpath₂ hs₂_H ht₂_H with ⟨segs₂, hsub₂, hfold₂⟩
  -- 1. Total 2D XOR sum of deltaSeg over segs₁ × segs₂ is true:
  have h_tot : xorSum2 deltaSeg segs₁ segs₂ = true := by
    have h_inner : ∀ s₁ : HSegment G omega,
        segs₂.foldr (fun s₂ acc => bne (deltaSeg s₁ s₂) acc) false =
          bne (bne (cmpIdx2 n omega s₁.u (s2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.v (s2Vert n omega.length hk)))
              (bne (cmpIdx2 n omega s₁.u (t2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.v (t2Vert n omega.length hk))) := by
      intro s₁
      exact hfold₂ (fun y => bne (cmpIdx2 n omega s₁.u y) (cmpIdx2 n omega s₁.v y))
    have h_outer_eq : ∀ s₁ : HSegment G omega,
        bne (bne (cmpIdx2 n omega s₁.u (s2Vert n omega.length hk))
                 (cmpIdx2 n omega s₁.v (s2Vert n omega.length hk)))
            (bne (cmpIdx2 n omega s₁.u (t2Vert n omega.length hk))
                 (cmpIdx2 n omega s₁.v (t2Vert n omega.length hk))) =
          bne (bne (cmpIdx2 n omega s₁.u (s2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.u (t2Vert n omega.length hk)))
              (bne (cmpIdx2 n omega s₁.v (s2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.v (t2Vert n omega.length hk))) := by
      intro s₁
      cases cmpIdx2 n omega s₁.u (s2Vert n omega.length hk) <;>
        cases cmpIdx2 n omega s₁.v (s2Vert n omega.length hk) <;>
        cases cmpIdx2 n omega s₁.u (t2Vert n omega.length hk) <;>
        cases cmpIdx2 n omega s₁.v (t2Vert n omega.length hk) <;> rfl
    unfold xorSum2
    simp only [h_inner, h_outer_eq]
    rw [hfold₁ (fun x => bne (cmpIdx2 n omega x (s2Vert n omega.length hk))
                             (cmpIdx2 n omega x (t2Vert n omega.length hk)))]
    -- Evaluate idx2 at s1Vert, t1Vert, s2Vert, t2Vert:
    have hi_s1 : idx2 n omega (s1Vert n omega.length hk) = 2 * (omega.length - 2) := by
      simp [idx2, posH, s1Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 0 < omega.length)]
    have hi_t1 : idx2 n omega (t1Vert n omega.length hk) = 0 := by
      simp [idx2, posH, t1Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 2 < omega.length)]
    have hi_s2 : idx2 n omega (s2Vert n omega.length hk) = 2 * (omega.length - 1) := by
      simp [idx2, posH, s2Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 1 < omega.length)]
      omega
    have hi_t2 : idx2 n omega (t2Vert n omega.length hk) = 2 := by
      simp [idx2, posH, t2Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 3 < omega.length)]
    simp only [cmpIdx2, hi_s1, hi_t1, hi_s2, hi_t2]
    have c1 : decide (2 * (omega.length - 2) < 2 * (omega.length - 1)) = true :=
      decide_eq_true (by omega)
    have c2 : decide (2 * (omega.length - 2) < 2) = false :=
      decide_eq_false (by omega)
    have c3 : decide (0 < 2 * (omega.length - 1)) = true :=
      decide_eq_true (by omega)
    have c4 : decide (0 < 2) = true :=
      decide_eq_true (by omega)
    rw [c1, c2, c3, c4]
    rfl
  -- 2. Sum of isTopSeg s₁ && deltaSeg s₁ s₂ is false:
  have h_top1 : xorSum2 (fun s₁ s₂ => isTopSeg s₁ && deltaSeg s₁ s₂) segs₁ segs₂ = false := by
    apply foldr_bne_eq_false_of_forall
    intro s₁ hs₁
    rw [foldr_bne_and_const]
    by_cases ht1 : isTopSeg s₁ = true
    · rw [ht1, Bool.true_and]
      unfold deltaSeg
      rw [hfold₂ (fun y => bne (cmpIdx2 n omega s₁.u y) (cmpIdx2 n omega s₁.v y))]
      have hno_wrap₁ : ¬ (s2Vert n omega.length hk ∈ s₁.walk.support ∧
                          t1Vert n omega.length hk ∈ s₁.walk.support) := by
        intro ⟨h_in, _⟩
        exact hdisj (hsub₁ s₁ hs₁ _ h_in) (Walk.start_mem_support R₂)
      have hs₂_ne_u1 : s2Vert n omega.length hk ≠ s₁.u :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.u (Walk.start_mem_support s₁.walk))
          (h ▸ Walk.start_mem_support R₂)
      have hs₂_ne_v1 : s2Vert n omega.length hk ≠ s₁.v :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.v (Walk.end_mem_support s₁.walk))
          (h ▸ Walk.start_mem_support R₂)
      have ht₂_ne_u1 : t2Vert n omega.length hk ≠ s₁.u :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.u (Walk.start_mem_support s₁.walk))
          (h ▸ Walk.end_mem_support R₂)
      have ht₂_ne_v1 : t2Vert n omega.length hk ≠ s₁.v :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.v (Walk.end_mem_support s₁.walk))
          (h ▸ Walk.end_mem_support R₂)
      have h_s2 := (bne_cmpIdx2_of_isTopSeg hk s₁ ht1 hno_wrap₁
        (by simp [s2Vert, c1Vert]) hs₂_ne_u1 hs₂_ne_v1).1
      have h_t2 := (bne_cmpIdx2_of_isTopSeg hk s₁ ht1 hno_wrap₁
        (by simp [t2Vert, c1Vert]) ht₂_ne_u1 ht₂_ne_v1).1
      rw [h_s2, h_t2]
      rfl
    · simp only [Bool.not_eq_true] at ht1
      simp [ht1]
  -- 3. Sum of isTopSeg s₂ && deltaSeg s₁ s₂ is false:
  have h_top2 : xorSum2 (fun s₁ s₂ => isTopSeg s₂ && deltaSeg s₁ s₂) segs₁ segs₂ = false := by
    have h_swap : ∀ (L₂ : List (HSegment G omega)),
        (∀ s₂ ∈ L₂, s₂ ∈ segs₂) →
        xorSum2 (fun s₁ s₂ => isTopSeg s₂ && deltaSeg s₁ s₂) segs₁ L₂ = false := by
      intro L₂ hsubL₂
      induction L₂ with
      | nil =>
        unfold xorSum2
        exact foldr_bne_eq_false_of_forall _ _ (fun _ _ => rfl)
      | cons s₂ rest ih =>
        have h_eq : xorSum2 (fun s₁ b => isTopSeg b && deltaSeg s₁ b) segs₁ (s₂ :: rest) =
            bne (segs₁.foldr (fun s₁ acc => bne (isTopSeg s₂ && deltaSeg s₁ s₂) acc) false)
                (xorSum2 (fun s₁ b => isTopSeg b && deltaSeg s₁ b) segs₁ rest) := by
          unfold xorSum2
          simp only [List.foldr_cons]
          exact foldr_bne_bne _ _ segs₁
        rw [h_eq, ih (fun b hb => hsubL₂ b (List.mem_cons_of_mem _ hb)), Bool.bne_false]
        rw [foldr_bne_and_const]
        by_cases ht2 : isTopSeg s₂ = true
        · rw [ht2, Bool.true_and]
          have h_symm_fold :
              segs₁.foldr (fun s₁ acc => bne (deltaSeg s₁ s₂) acc) false =
                segs₁.foldr (fun s₁ acc =>
                  bne (bne (bne (cmpIdx2 n omega s₁.u s₂.u) (cmpIdx2 n omega s₁.u s₂.v))
                           (bne (cmpIdx2 n omega s₁.v s₂.u) (cmpIdx2 n omega s₁.v s₂.v))) acc) false := by
            congr 1
            funext s₁ acc
            rw [deltaSeg_symm_form]
          rw [h_symm_fold, hfold₁ (fun x => bne (cmpIdx2 n omega x s₂.u) (cmpIdx2 n omega x s₂.v))]
          have hs₂_mem : s₂ ∈ segs₂ := hsubL₂ s₂ List.mem_cons_self
          have hno_wrap₂ : ¬ (s2Vert n omega.length hk ∈ s₂.walk.support ∧
                              t1Vert n omega.length hk ∈ s₂.walk.support) := by
            intro ⟨_, h_in⟩
            exact hdisj (Walk.end_mem_support R₁) (hsub₂ s₂ hs₂_mem _ h_in)
          have hs₁_ne_u2 : s1Vert n omega.length hk ≠ s₂.u :=
            fun h => hdisj (Walk.start_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.u (Walk.start_mem_support s₂.walk))
          have hs₁_ne_v2 : s1Vert n omega.length hk ≠ s₂.v :=
            fun h => hdisj (Walk.start_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.v (Walk.end_mem_support s₂.walk))
          have ht₁_ne_u2 : t1Vert n omega.length hk ≠ s₂.u :=
            fun h => hdisj (Walk.end_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.u (Walk.start_mem_support s₂.walk))
          have ht₁_ne_v2 : t1Vert n omega.length hk ≠ s₂.v :=
            fun h => hdisj (Walk.end_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.v (Walk.end_mem_support s₂.walk))
          have h_s1 := (bne_cmpIdx2_of_isTopSeg hk s₂ ht2 hno_wrap₂
            (by simp [s1Vert, c1Vert]) hs₁_ne_u2 hs₁_ne_v2).2
          have h_t1 := (bne_cmpIdx2_of_isTopSeg hk s₂ ht2 hno_wrap₂
            (by simp [t1Vert, c1Vert]) ht₁_ne_u2 ht₁_ne_v2).2
          rw [h_s1, h_t1]
          rfl
        · simp only [Bool.not_eq_true] at ht2
          simp [ht2]
    exact h_swap segs₂ (fun _ h => h)
  -- 4. Combine via deltaSeg_decomp_pointwise:
  have h_bot_sum : xorSum2 (fun s₁ s₂ => isBotSeg s₁ && isBotSeg s₂ && deltaSeg s₁ s₂) segs₁ segs₂ = true := by
    have h_congr : xorSum2 deltaSeg segs₁ segs₂ =
        xorSum2 (fun s₁ s₂ =>
          bne (bne (isTopSeg s₁ && deltaSeg s₁ s₂) (isTopSeg s₂ && deltaSeg s₁ s₂))
              (isBotSeg s₁ && isBotSeg s₂ && deltaSeg s₁ s₂)) segs₁ segs₂ := by
      apply xorSum2_congr_on
      intro s₁ hs₁ s₂ hs₂
      have hdisj_s : List.Disjoint s₁.walk.support s₂.walk.support :=
        fun x hx₁ hx₂ => hdisj (hsub₁ s₁ hs₁ x hx₁) (hsub₂ s₂ hs₂ x hx₂)
      have hno_wrap₁ : ¬ (s2Vert n omega.length hk ∈ s₁.walk.support ∧
                          t1Vert n omega.length hk ∈ s₁.walk.support) :=
        fun ⟨h_in, _⟩ => hdisj (hsub₁ s₁ hs₁ _ h_in) (Walk.start_mem_support R₂)
      exact deltaSeg_decomp_pointwise hnodup hk s₁ s₂ hdisj_s hno_wrap₁
    rw [h_congr, xorSum2_bne, xorSum2_bne, h_top1, h_top2] at h_tot
    simpa using h_tot
  rcases xorSum2_eq_true_implies_exists _ segs₁ segs₂ h_bot_sum with ⟨s₁, hs₁, s₂, hs₂, h_both⟩
  simp only [Bool.and_eq_true] at h_both
  rcases h_both with ⟨⟨hb1, hb2⟩, hdel⟩
  simp only [isBotSeg, decide_eq_true_eq] at hb1 hb2
  have hdisj_s : List.Disjoint s₁.walk.support s₂.walk.support :=
    fun x hx₁ hx₂ => hdisj (hsub₁ s₁ hs₁ x hx₁) (hsub₂ s₂ hs₂ x hx₂)
  have hcross := crosses_of_deltaSeg_bot hk s₁ s₂ hdisj_s hb1.1 hb1.2 hb2.1 hb2.2 hdel
  have hno_c2_1 := hcross.not_adj_c2 hnodup hk
  have hno_c2_2 := hcross.symm_pq.not_adj_c2 hnodup hk
  refine ⟨⟨s₁.u.1, hb1.1⟩, ⟨s₁.v.1, hb1.2⟩, ⟨s₂.u.1, hb2.1⟩, ⟨s₂.v.1, hb2.2⟩,
    botSegToGPath hk s₁ hb1.1 hb1.2 hno_c2_1,
    botSegToGPath hk s₂ hb2.1 hb2.2 hno_c2_2,
    isPath_botSegToGPath hk s₁ hb1.1 hb1.2 hno_c2_1,
    isPath_botSegToGPath hk s₂ hb2.1 hb2.2 hno_c2_2,
    fun u huP huQ => ?_, hcross⟩
  have hx₁ : inGVert omega.length u ∈ s₁.walk.support :=
    mem_support_of_mem_botSegToGPath hk s₁ hb1.1 hb1.2 hno_c2_1 huP
  have hx₂ : inGVert omega.length u ∈ s₂.walk.support :=
    mem_support_of_mem_botSegToGPath hk s₂ hb2.1 hb2.2 hno_c2_2 huQ
  exact hdisj (hsub₁ s₁ hs₁ _ hx₁) (hsub₂ s₂ hs₂ _ hx₂)

/-! ### Section 5: Walk Slicing, `prevH` Index Tracking, and Pure Walk Reader `decGWalk` -/

/-- Read a vertex index list `l : List ℕ` into an optional walk in `G : SimpleGraph (Fin n)`.
This function only reads `l` and checks vertex bounds and adjacency in `G`. -/
def decGWalk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List ℕ → Option (Σ u v : Fin n, G.Walk u v)
  | [] => none
  | [u] =>
    if hu : u < n then
      some ⟨⟨u, hu⟩, ⟨u, hu⟩, .nil⟩
    else
      none
  | u :: v :: rest =>
    match decGWalk G (v :: rest) with
    | some ⟨v', w', W⟩ =>
      if hu : u < n then
        if hadj : G.Adj ⟨u, hu⟩ v' then
          some ⟨⟨u, hu⟩, w', .cons hadj W⟩
        else
          none
      else
        none
    | none => none

theorem decGWalk_support_map {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (W : G.Walk u v) :
    decGWalk G (W.support.map Fin.val) = some ⟨u, v, W⟩ := by
  induction W with
  | @nil u =>
    simp [decGWalk, u.2]
  | @cons u v w hadj rest ih =>
    cases rest with
    | nil =>
      simp only [Walk.support_cons, Walk.support_nil, List.map_cons, List.map_nil] at ih ⊢
      simp [decGWalk, u.2, v.2, hadj]
    | cons hadj' rest' =>
      simp only [Walk.support_cons, List.map_cons] at ih ⊢
      simp [decGWalk, ih, u.2, hadj]

theorem support_append_drop_length {V : Type*} {G : SimpleGraph V} {x y z : V}
    (U : G.Walk x y) (W : G.Walk y z) :
    (U.append W).support.drop U.length = W.support := by
  induction U with
  | nil => simp
  | cons _ U' ih => simp [Walk.cons_append, Walk.support_cons, Walk.length_cons, ih]

theorem support_append_take_length {V : Type*} {G : SimpleGraph V} {x y z : V}
    (U : G.Walk x y) (W : G.Walk y z) :
    (U.append W).support.take (U.length + 1) = U.support := by
  induction U with
  | nil => cases W <;> simp
  | cons _ U' ih => simp [Walk.cons_append, Walk.support_cons, Walk.length_cons, ih]

theorem getElem_support_zero {V : Type*} {G : SimpleGraph V} {x y : V}
    (W : G.Walk x y) :
    W.support[0]'(by rw [Walk.length_support]; omega) = x := by
  cases W <;> rfl

theorem getElem_support_length {V : Type*} {G : SimpleGraph V} {x y : V}
    (W : G.Walk x y) :
    W.support[W.length]'(by rw [Walk.length_support]; omega) = y := by
  induction W with
  | nil => rfl
  | cons _ W' ih =>
    simp only [Walk.support_cons, Walk.length_cons, List.getElem_cons_succ]
    exact ih

theorem exists_splitWalkAt {V : Type*} {G : SimpleGraph V} :
    ∀ {x y : V} (W : G.Walk x y) (k : ℕ) (hk : k ≤ W.length),
      ∃ (z : V) (W₁ : G.Walk x z) (W₂ : G.Walk z y),
        z = W.support[k]'(by rw [Walk.length_support]; omega) ∧
        W = W₁.append W₂ ∧ W₁.length = k
  | _, _, W, 0, _ =>
    ⟨_, .nil, W, (getElem_support_zero W).symm, by simp, rfl⟩
  | _, _, .nil, k + 1, hk => by simp at hk
  | _, _, .cons hadj W', k + 1, hk => by
    rcases exists_splitWalkAt W' k (by simp at hk; omega) with ⟨z, W₁', W₂', hz, hW', hlen'⟩
    refine ⟨z, .cons hadj W₁', W₂', ?_, ?_, by simp [hlen']⟩
    · simpa [Walk.support_cons] using hz
    · simp [Walk.cons_append, hW']

/-- Index of the most recent `V(H)` vertex in `L` at or before index `k`. -/
def prevH (n : ℕ) (omega : List (Fin n)) (L : List (Fin (n + omega.length))) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if hk : k + 1 < L.length then
      if isHVert n omega (L[k + 1]'hk) then k + 1 else prevH n omega L k
    else
      prevH n omega L k

theorem prevH_le (n : ℕ) (omega : List (Fin n)) (L : List (Fin (n + omega.length))) (k : ℕ) :
    prevH n omega L k ≤ k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    unfold prevH
    split_ifs <;> omega

theorem prevH_lt_length {n : ℕ} {omega : List (Fin n)} {L : List (Fin (n + omega.length))}
    (h0 : 0 < L.length) (k : ℕ) :
    prevH n omega L k < L.length := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    unfold prevH
    split_ifs with hk
    · exact hk
    · exact ih
    · exact ih

theorem prevH_isHVert {n : ℕ} {omega : List (Fin n)} {L : List (Fin (n + omega.length))}
    (h0 : 0 < L.length) (ha : isHVert n omega (L[0]'h0) = true) (k : ℕ) :
    isHVert n omega (L[prevH n omega L k]'(prevH_lt_length h0 k)) = true := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    unfold prevH
    split_ifs with hk hH
    · exact hH
    · exact ih
    · exact ih

theorem prevH_internal {n : ℕ} {omega : List (Fin n)} {L : List (Fin (n + omega.length))}
    (k : ℕ) (hk : k < L.length) :
    ∀ c (hc : c < L.length), prevH n omega L k < c → c ≤ k →
      isHVert n omega (L[c]'hc) = false := by
  induction k with
  | zero =>
    intro c _ hgt hle
    simp [prevH] at hgt
    omega
  | succ k ih =>
    intro c hc hgt hle
    unfold prevH at hgt
    simp only [hk, ↓reduceDIte] at hgt
    split_ifs at hgt with hH
    · omega
    · rcases Nat.lt_or_eq_of_le hle with hlt | rfl
      · exact ih (by omega) c hc hgt (by omega)
      · exact Bool.eq_false_iff.mpr hH

theorem prevH_eq_of_segment {n : ℕ} {omega : List (Fin n)} {L : List (Fin (n + omega.length))}
    (h0 : 0 < L.length) (ha0 : isHVert n omega (L[0]'h0) = true)
    {a k : ℕ} (hak : a ≤ k) (hk : k < L.length)
    (ha : isHVert n omega (L[a]'(by omega)) = true)
    (hint : ∀ c (hc : c < L.length), a < c → c ≤ k → isHVert n omega (L[c]'hc) = false) :
    prevH n omega L k = a := by
  have hp_le : prevH n omega L k ≤ k := prevH_le n omega L k
  have hp_H : isHVert n omega (L[prevH n omega L k]'(prevH_lt_length h0 k)) = true :=
    prevH_isHVert h0 ha0 k
  have hp_int := prevH_internal k hk
  rcases Nat.lt_trichotomy (prevH n omega L k) a with hlt | heq | hgt
  · have hfalse := hp_int a (by omega) hlt hak
    rw [ha] at hfalse
    contradiction
  · exact heq
  · have hfalse := hint (prevH n omega L k) (prevH_lt_length h0 k) hgt hp_le
    rw [hp_H] at hfalse
    contradiction

theorem exists_subwalk_slice {V : Type*} {G : SimpleGraph V} {x y : V}
    (W : G.Walk x y) {a b : ℕ} (hab : a ≤ b) (hb : b < W.support.length) :
    ∃ (u v : V) (S : G.Walk u v),
      u = W.support[a]'(by omega) ∧
      v = W.support[b]'hb ∧
      IsSubwalkOf W S ∧
      S.length = b - a ∧
      (W.support.drop a).take (b + 1 - a) = S.support := by
  have ha_len : a ≤ W.length := by rw [Walk.length_support] at hb; omega
  rcases exists_splitWalkAt W a ha_len with ⟨u, W₁, W_rest, hu_eq, hW₁, hlen₁⟩
  have hdrop : W.support.drop a = W_rest.support := by
    rw [hW₁, ← hlen₁, support_append_drop_length]
  have hlen_rest : W_rest.length = W.length - a := by
    have := congrArg Walk.length hW₁
    rw [Walk.length_append, hlen₁] at this
    omega
  have hba_le : b - a ≤ W_rest.length := by
    rw [Walk.length_support] at hb; omega
  rcases exists_splitWalkAt W_rest (b - a) hba_le with ⟨v, S₀, W₂, hv_eq, hW_rest, hlenS₀⟩
  have h_end_eq : v = W.support[b]'hb := by
    have h1 : W_rest.support[b - a]?.getD x = W.support[b]'hb := by
      rw [← hdrop, List.getElem?_drop, show a + (b - a) = b by omega,
        List.getElem?_eq_getElem hb, Option.getD_some]
    have h2 : W_rest.support[b - a]?.getD x = v := by
      rw [List.getElem?_eq_getElem (by rw [Walk.length_support]; omega),
        Option.getD_some]
      exact hv_eq.symm
    exact h2.symm.trans h1
  refine ⟨u, v, S₀, hu_eq, h_end_eq, ⟨W₁, W₂, by rw [hW₁, hW_rest]⟩, hlenS₀, ?_⟩
  rw [hdrop, hW_rest, show b + 1 - a = S₀.length + 1 by omega, support_append_take_length]

theorem exists_hsegment_of_slice {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {x₀ y₀ : Fin (n + omega.length)} (W : (auxGraph81 G omega).Walk x₀ y₀)
    (hpath : W.IsPath) {a b : ℕ} (hab : a < b) (hb : b < W.support.length)
    (ha_H : isHVert n omega (W.support[a]'(by omega)) = true)
    (hb_H : isHVert n omega (W.support[b]'hb) = true)
    (hint : ∀ c (hc : c < W.support.length), a < c → c < b →
      isHVert n omega (W.support[c]'hc) = false) :
    ∃ (s : HSegment G omega),
      s.u = W.support[a]'(by omega) ∧
      s.v = W.support[b]'hb ∧
      IsSubwalkOf W s.walk ∧
      (W.support.drop a).take (b + 1 - a) = s.walk.support := by
  rcases exists_subwalk_slice W (Nat.le_of_lt hab) hb with ⟨u, v, S, hu_eq, hv_eq, hsub, _, hslice⟩
  have hnodup : W.support.Nodup := hpath.support_nodup
  have hne : u ≠ v := by
    rw [hu_eq, hv_eq]
    intro heq
    have := (hnodup.getElem_inj_iff).mp heq
    omega
  have hS_path : S.IsPath := by
    rcases hsub with ⟨W₁, W₂, hW_eq⟩
    rw [hW_eq] at hpath
    exact hpath.of_append_right.of_append_left
  refine ⟨{
    u := u
    v := v
    walk := S
    hne := hne
    isPath := hS_path
    hu := hu_eq ▸ ha_H
    hv := hv_eq ▸ hb_H
    hinternal := fun x hx hH => by
      rw [← hslice] at hx
      rcases List.mem_iff_getElem.mp hx with ⟨i, hi, hget⟩
      simp only [List.length_take, List.length_drop, List.getElem_take, List.getElem_drop] at hi hget
      have hc_lt : a + i < W.support.length := by omega
      by_cases hi0 : i = 0
      · subst hi0; left; rw [hu_eq]; simpa using hget.symm
      · by_cases hib : a + i = b
        · right; rw [hv_eq]; simp only [← hget, hib]
        · exfalso
          have hfalse := hint (a + i) hc_lt (by omega) (by omega)
          rw [hget] at hfalse
          rw [hH] at hfalse
          contradiction
  }, hu_eq, hv_eq, hsub, hslice⟩

theorem subwalk_hsegment_prevH {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {x₀ y₀ : Fin (n + omega.length)} (W : (auxGraph81 G omega).Walk x₀ y₀)
    (hpath : W.IsPath)
    (ha0 : isHVert n omega (W.support[0]'(by rw [Walk.length_support]; omega)) = true)
    (s : HSegment G omega) (hsub : IsSubwalkOf W s.walk) :
    ∃ (k : ℕ) (hk : k < W.length),
      prevH n omega W.support k = W.support.idxOf s.u ∧
      prevH n omega W.support k < k + 1 ∧
      W.support[prevH n omega W.support k]'(prevH_lt_length (by rw [Walk.length_support]; omega) k) = s.u ∧
      W.support[k + 1]'(by rw [Walk.length_support]; omega) = s.v ∧
      (W.support.drop (prevH n omega W.support k)).take (k + 1 + 1 - prevH n omega W.support k) =
        s.walk.support := by
  rcases hsub with ⟨W₁, W₂, hW⟩
  have hS_pos : 0 < s.walk.length := by
    rcases s with ⟨u, v, walk, hne, _, _, _, _⟩
    cases walk with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  let a := W₁.length
  let k := W₁.length + s.walk.length - 1
  have hk_add : k + 1 = a + s.walk.length := by dsimp [k, a]; omega
  have hW_len : W.length = a + s.walk.length + W₂.length := by
    rw [hW, Walk.length_append, Walk.length_append]
    dsimp [a]
    omega
  have hk_lt_len : k < W.length := by omega
  have hk_lt_sup : k < W.support.length := by rw [Walk.length_support]; omega
  have hk1_lt_sup : k + 1 < W.support.length := by rw [Walk.length_support]; omega
  have ha_lt_sup : a < W.support.length := by rw [Walk.length_support]; omega
  have hdrop : W.support.drop a = (s.walk.append W₂).support := by
    rw [hW, support_append_drop_length]
  have hslice : (W.support.drop a).take (k + 1 + 1 - a) = s.walk.support := by
    rw [hdrop, show k + 1 + 1 - a = s.walk.length + 1 by omega, support_append_take_length]
  have hget_a : W.support[a]'ha_lt_sup = s.u := by
    have h1 : (W.support.drop a)[0]?.getD x₀ = W.support[a]'ha_lt_sup := by
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem ha_lt_sup, Option.getD_some]
    have h2 : (s.walk.append W₂).support[0]?.getD x₀ = s.u := by
      rw [List.getElem?_eq_getElem (by rw [Walk.length_support]; omega),
        Option.getD_some, getElem_support_zero]
    rw [hdrop] at h1
    exact h1.symm.trans h2
  have hget_k1 : W.support[k + 1]'hk1_lt_sup = s.v := by
    have h1 : ((W.support.drop a).take (k + 1 + 1 - a))[s.walk.length]?.getD x₀ =
        W.support[k + 1]'hk1_lt_sup := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        ← hk_add, List.getElem?_eq_getElem hk1_lt_sup, Option.getD_some]
    have h2 : s.walk.support[s.walk.length]?.getD x₀ = s.v := by
      rw [List.getElem?_eq_getElem (by rw [Walk.length_support]; omega),
        Option.getD_some, getElem_support_length]
    rw [hslice] at h1
    exact h1.symm.trans h2
  have hnodup : W.support.Nodup := hpath.support_nodup
  have hint : ∀ c (hc : c < W.support.length), a < c → c ≤ k →
      isHVert n omega (W.support[c]'hc) = false := by
    intro c hc hgt hle
    by_contra htrue
    simp only [Bool.not_eq_false] at htrue
    have hc_mem : W.support[c]'hc ∈ s.walk.support := by
      rw [← hslice]
      have hidx : c - a < ((W.support.drop a).take (k + 1 + 1 - a)).length := by
        simp; omega
      have heq : ((W.support.drop a).take (k + 1 + 1 - a))[c - a]'hidx = W.support[c]'hc := by
        simp [List.getElem_take, List.getElem_drop, show a + (c - a) = c by omega]
      rw [← heq]
      exact List.getElem_mem hidx
    rcases s.hinternal (W.support[c]'hc) hc_mem htrue with h_eq_u | h_eq_v
    · rw [← hget_a] at h_eq_u
      have := (hnodup.getElem_inj_iff).mp h_eq_u
      omega
    · rw [← hget_k1] at h_eq_v
      have := (hnodup.getElem_inj_iff).mp h_eq_v
      omega
  have hprev_eq : prevH n omega W.support k = a :=
    prevH_eq_of_segment (by rw [Walk.length_support]; omega) ha0 (by omega) hk_lt_sup
      (by rw [hget_a]; exact s.hu) hint
  have hidxOf : W.support.idxOf s.u = a := by
    rw [← hget_a]
    exact idxOf_getElem_of_nodup hnodup ⟨a, ha_lt_sup⟩
  refine ⟨k, hk_lt_len, by rw [hprev_eq, hidxOf], by omega, ?_, hget_k1, ?_⟩
  · simp only [hprev_eq, hget_a]
  · simp only [hprev_eq, hslice]

/-- Word RAM table entry for vertex `u < n + omega.length`:
`1 + distFrom2 omega.length (omega.idxOf ⟨u, hu⟩)` if `u < n` and `⟨u, hu⟩ ∈ omega`, and `0`
otherwise. -/
def omegaPosVal (n : ℕ) (omega : List (Fin n)) (u : ℕ) : ℕ :=
  if hu : u < n then
    if ⟨u, hu⟩ ∈ omega then
      1 + distFrom2 omega.length (omega.idxOf ⟨u, hu⟩)
    else
      0
  else
    0

theorem omegaPosVal_le (n : ℕ) (omega : List (Fin n)) (u : ℕ) :
    omegaPosVal n omega u ≤ omega.length := by
  unfold omegaPosVal
  split_ifs with hu hmem
  · have hpos : 0 < omega.length := List.length_pos_of_mem hmem
    have hlt := distFrom2_lt (i := omega.idxOf ⟨u, hu⟩) hpos
    omega
  · omega
  · omega

theorem omegaPosVal_pos_iff {n : ℕ} {omega : List (Fin n)} (u : Fin (n + omega.length)) :
    0 < omegaPosVal n omega u.1 ↔ u.1 < n ∧ isHVert n omega u = true := by
  unfold omegaPosVal isHVert
  split_ifs with hu hmem
  · simp [hu, hmem]
  · simp [hu, hmem]
  · simp [hu]

theorem omegaPosVal_eq_succ_posH {n : ℕ} {omega : List (Fin n)} {u : Fin (n + omega.length)}
    (hu : u.1 < n) (hH : isHVert n omega u = true) :
    omegaPosVal n omega u.1 = 1 + posH n omega u := by
  have hmem : (⟨u.1, hu⟩ : Fin n) ∈ omega := by
    simpa [isHVert, hu] using hH
  simp [omegaPosVal, posH, hu, hmem]

theorem isHVert_iff_omegaPosVal_add_sub {n : ℕ} {omega : List (Fin n)}
    (u : Fin (n + omega.length)) :
    omegaPosVal n omega u.1 + (1 - (if u.1 < n then 1 else 0)) ≠ 0 ↔
      isHVert n omega u = true := by
  by_cases hu : u.1 < n
  · by_cases hmem : (⟨u.1, hu⟩ : Fin n) ∈ omega <;>
      simp [omegaPosVal, isHVert, hu, hmem]
  · simp [omegaPosVal, isHVert, hu]

/-- Word RAM arithmetic evaluation of `deltaSeg` on four position values `p₁, p₂, q₁, q₂`. -/
def deltaPosVal (p₁ p₂ q₁ q₂ : ℕ) : ℕ :=
  let c11 := if p₁ < q₁ then 1 else 0
  let c21 := if p₂ < q₁ then 1 else 0
  let c12 := if p₁ < q₂ then 1 else 0
  let c22 := if p₂ < q₂ then 1 else 0
  let e1 := if c11 = c21 then 1 else 0
  let e2 := if c12 = c22 then 1 else 0
  1 - (if e1 = e2 then 1 else 0)

theorem deltaPosVal_le_one (p₁ p₂ q₁ q₂ : ℕ) : deltaPosVal p₁ p₂ q₁ q₂ ≤ 1 := by
  dsimp [deltaPosVal]; omega

theorem deltaPosVal_bool_eq (b11 b21 b12 b22 : Bool) :
    (1 -
      if
        (if (if b11 = true then 1 else 0) = (if b21 = true then 1 else 0) then 1 else 0) =
          (if (if b12 = true then 1 else 0) = (if b22 = true then 1 else 0) then 1 else 0) then
        1
      else 0) =
    if ((b11 != b21) != (b12 != b22)) = true then 1 else 0 := by
  cases b11 <;> cases b21 <;> cases b12 <;> cases b22 <;> rfl

theorem deltaPosVal_eq_deltaSeg {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (s₁ s₂ : HSegment G omega)
    (hu₁ : s₁.u.1 < n) (hv₁ : s₁.v.1 < n) (hu₂ : s₂.u.1 < n) (hv₂ : s₂.v.1 < n) :
    deltaPosVal (omegaPosVal n omega s₁.u.1) (omegaPosVal n omega s₁.v.1)
      (omegaPosVal n omega s₂.u.1) (omegaPosVal n omega s₂.v.1) =
        if deltaSeg s₁ s₂ then 1 else 0 := by
  rw [omegaPosVal_eq_succ_posH hu₁ s₁.hu, omegaPosVal_eq_succ_posH hv₁ s₁.hv,
    omegaPosVal_eq_succ_posH hu₂ s₂.hu, omegaPosVal_eq_succ_posH hv₂ s₂.hv]
  have h11 : (1 + posH n omega s₁.u < 1 + posH n omega s₂.u) ↔
      cmpIdx2 n omega s₁.u s₂.u = true := by
    rw [cmpIdx2_eq_posH_lt hu₁ hu₂, decide_eq_true_iff]; omega
  have h21 : (1 + posH n omega s₁.v < 1 + posH n omega s₂.u) ↔
      cmpIdx2 n omega s₁.v s₂.u = true := by
    rw [cmpIdx2_eq_posH_lt hv₁ hu₂, decide_eq_true_iff]; omega
  have h12 : (1 + posH n omega s₁.u < 1 + posH n omega s₂.v) ↔
      cmpIdx2 n omega s₁.u s₂.v = true := by
    rw [cmpIdx2_eq_posH_lt hu₁ hv₂, decide_eq_true_iff]; omega
  have h22 : (1 + posH n omega s₁.v < 1 + posH n omega s₂.v) ↔
      cmpIdx2 n omega s₁.v s₂.v = true := by
    rw [cmpIdx2_eq_posH_lt hv₁ hv₂, decide_eq_true_iff]; omega
  dsimp [deltaPosVal, deltaSeg]
  simp only [h11, h21, h12, h22]
  exact deltaPosVal_bool_eq _ _ _ _

/-- Word RAM boolean test (as `0` or `1`) on segment endpoint indices `(a₁, b₁, a₂, b₂)`. -/
def segPairTestVal (n : ℕ) (omega : List (Fin n)) (l₁ l₂ : List ℕ) (a₁ b₁ a₂ b₂ : ℕ) : ℕ :=
  let p₁ := omegaPosVal n omega (l₁.getD a₁ 0)
  let p₂ := omegaPosVal n omega (l₁.getD b₁ 0)
  let q₁ := omegaPosVal n omega (l₂.getD a₂ 0)
  let q₂ := omegaPosVal n omega (l₂.getD b₂ 0)
  ((if 0 < p₁ then 1 else 0) *
    ((if 0 < p₂ then 1 else 0) *
      ((if 0 < q₁ then 1 else 0) *
        (if 0 < q₂ then 1 else 0)))) *
    deltaPosVal p₁ p₂ q₁ q₂

theorem segPairTestVal_le_one (n : ℕ) (omega : List (Fin n)) (l₁ l₂ : List ℕ) (a₁ b₁ a₂ b₂ : ℕ) :
    segPairTestVal n omega l₁ l₂ a₁ b₁ a₂ b₂ ≤ 1 := by
  dsimp [segPairTestVal]
  have hd := deltaPosVal_le_one
    (omegaPosVal n omega (l₁.getD a₁ 0))
    (omegaPosVal n omega (l₁.getD b₁ 0))
    (omegaPosVal n omega (l₂.getD a₂ 0))
    (omegaPosVal n omega (l₂.getD b₂ 0))
  split_ifs <;> omega

/-- Predicate stating that `(a₁, b₁)` and `(a₂, b₂)` slice `R₁` and `R₂` into bottom `HSegment`s
`s₁, s₂` with `deltaSeg s₁ s₂ = true`. -/
def IsGoodSegPair {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {x₁ y₁ x₂ y₂ : Fin (n + omega.length)}
    (R₁ : (auxGraph81 G omega).Walk x₁ y₁)
    (R₂ : (auxGraph81 G omega).Walk x₂ y₂)
    (a₁ b₁ a₂ b₂ : ℕ) : Prop :=
  ∃ (s₁ s₂ : HSegment G omega),
    a₁ < b₁ ∧ b₁ < R₁.support.length ∧
    a₂ < b₂ ∧ b₂ < R₂.support.length ∧
    IsSubwalkOf R₁ s₁.walk ∧
    IsSubwalkOf R₂ s₂.walk ∧
    (R₁.support.drop a₁).take (b₁ + 1 - a₁) = s₁.walk.support ∧
    (R₂.support.drop a₂).take (b₂ + 1 - a₂) = s₂.walk.support ∧
    isBotSeg s₁ = true ∧ isBotSeg s₂ = true ∧ deltaSeg s₁ s₂ = true

theorem isGoodSegPair_of_segPairTestVal {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    {x₁ y₁ x₂ y₂ : Fin (n + omega.length)}
    (R₁ : (auxGraph81 G omega).Walk x₁ y₁)
    (R₂ : (auxGraph81 G omega).Walk x₂ y₂)
    (hpath₁ : R₁.IsPath) (hpath₂ : R₂.IsPath)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < R₁.length) (hk₂ : k₂ < R₂.length)
    (htest : segPairTestVal n omega (R₁.support.map Fin.val) (R₂.support.map Fin.val)
      (prevH n omega R₁.support k₁) (k₁ + 1) (prevH n omega R₂.support k₂) (k₂ + 1) ≠ 0) :
    IsGoodSegPair R₁ R₂ (prevH n omega R₁.support k₁) (k₁ + 1)
      (prevH n omega R₂.support k₂) (k₂ + 1) := by
  let a₁ := prevH n omega R₁.support k₁
  let b₁ := k₁ + 1
  let a₂ := prevH n omega R₂.support k₂
  let b₂ := k₂ + 1
  have hb₁_lt : b₁ < R₁.support.length := by rw [Walk.length_support]; omega
  have hb₂_lt : b₂ < R₂.support.length := by rw [Walk.length_support]; omega
  have ha₁_lt : a₁ < b₁ := Nat.lt_succ_of_le (prevH_le n omega R₁.support k₁)
  have ha₂_lt : a₂ < b₂ := Nat.lt_succ_of_le (prevH_le n omega R₂.support k₂)
  have hget_a₁ : (R₁.support.map Fin.val).getD a₁ 0 = (R₁.support[a₁]'(by omega)).1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    simp
  have hget_b₁ : (R₁.support.map Fin.val).getD b₁ 0 = (R₁.support[b₁]'hb₁_lt).1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    simp
  have hget_a₂ : (R₂.support.map Fin.val).getD a₂ 0 = (R₂.support[a₂]'(by omega)).1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    simp
  have hget_b₂ : (R₂.support.map Fin.val).getD b₂ 0 = (R₂.support[b₂]'hb₂_lt).1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
    simp
  dsimp [segPairTestVal] at htest
  rw [hget_a₁, hget_b₁, hget_a₂, hget_b₂] at htest
  have hp₁_pos : 0 < omegaPosVal n omega (R₁.support[a₁]'(by omega)).1 := by
    by_contra h; simp [h] at htest
  have hp₂_pos : 0 < omegaPosVal n omega (R₁.support[b₁]'hb₁_lt).1 := by
    by_contra h; simp [h] at htest
  have hq₁_pos : 0 < omegaPosVal n omega (R₂.support[a₂]'(by omega)).1 := by
    by_contra h; simp [h] at htest
  have hq₂_pos : 0 < omegaPosVal n omega (R₂.support[b₂]'hb₂_lt).1 := by
    by_contra h; simp [h] at htest
  obtain ⟨hu₁_lt, hu₁_H⟩ := (omegaPosVal_pos_iff (R₁.support[a₁]'(by omega))).mp hp₁_pos
  obtain ⟨hv₁_lt, hv₁_H⟩ := (omegaPosVal_pos_iff (R₁.support[b₁]'hb₁_lt)).mp hp₂_pos
  obtain ⟨hu₂_lt, hu₂_H⟩ := (omegaPosVal_pos_iff (R₂.support[a₂]'(by omega))).mp hq₁_pos
  obtain ⟨hv₂_lt, hv₂_H⟩ := (omegaPosVal_pos_iff (R₂.support[b₂]'hb₂_lt)).mp hq₂_pos
  rcases exists_hsegment_of_slice R₁ hpath₁ ha₁_lt hb₁_lt hu₁_H hv₁_H
      (fun c hc hgt hlt => prevH_internal k₁ (by omega) c hc hgt (by omega)) with
    ⟨s₁, hs₁_u, hs₁_v, hsub₁, hslice₁⟩
  rcases exists_hsegment_of_slice R₂ hpath₂ ha₂_lt hb₂_lt hu₂_H hv₂_H
      (fun c hc hgt hlt => prevH_internal k₂ (by omega) c hc hgt (by omega)) with
    ⟨s₂, hs₂_u, hs₂_v, hsub₂, hslice₂⟩
  have hs₁_u_lt : s₁.u.1 < n := hs₁_u ▸ hu₁_lt
  have hs₁_v_lt : s₁.v.1 < n := hs₁_v ▸ hv₁_lt
  have hs₂_u_lt : s₂.u.1 < n := hs₂_u ▸ hu₂_lt
  have hs₂_v_lt : s₂.v.1 < n := hs₂_v ▸ hv₂_lt
  simp only [← hs₁_u, ← hs₁_v, ← hs₂_u, ← hs₂_v,
    deltaPosVal_eq_deltaSeg s₁ s₂ hs₁_u_lt hs₁_v_lt hs₂_u_lt hs₂_v_lt] at htest
  have hdel : deltaSeg s₁ s₂ = true := by
    revert htest; cases deltaSeg s₁ s₂ <;> simp
  refine ⟨s₁, s₂, ha₁_lt, hb₁_lt, ha₂_lt, hb₂_lt, hsub₁, hsub₂, hslice₁, hslice₂,
    by simp [isBotSeg, hs₁_u_lt, hs₁_v_lt],
    by simp [isBotSeg, hs₂_u_lt, hs₂_v_lt], hdel⟩

theorem exists_segPairTestVal_of_auxGraph81_paths {n : ℕ} {G : SimpleGraph (Fin n)}
    {omega : List (Fin n)} (hnodup : omega.Nodup) (hk : 4 ≤ omega.length)
    (R₁ : (auxGraph81 G omega).Walk (s1Vert n omega.length hk) (t1Vert n omega.length hk))
    (R₂ : (auxGraph81 G omega).Walk (s2Vert n omega.length hk) (t2Vert n omega.length hk))
    (hpath₁ : R₁.IsPath) (hpath₂ : R₂.IsPath)
    (hdisj : List.Disjoint R₁.support R₂.support) :
    ∃ k₁ < R₁.length, ∃ k₂ < R₂.length,
      segPairTestVal n omega (R₁.support.map Fin.val) (R₂.support.map Fin.val)
        (prevH n omega R₁.support k₁) (k₁ + 1) (prevH n omega R₂.support k₂) (k₂ + 1) = 1 := by
  have hs₁_ne_t₁ : s1Vert n omega.length hk ≠ t1Vert n omega.length hk := by
    intro h; have := Fin.mk.inj_iff.mp h; omega
  have hs₂_ne_t₂ : s2Vert n omega.length hk ≠ t2Vert n omega.length hk := by
    intro h; have := Fin.mk.inj_iff.mp h; omega
  have hs₁_H : isHVert n omega (s1Vert n omega.length hk) = true := by
    simp [isHVert, s1Vert, c1Vert]
  have ht₁_H : isHVert n omega (t1Vert n omega.length hk) = true := by
    simp [isHVert, t1Vert, c1Vert]
  have hs₂_H : isHVert n omega (s2Vert n omega.length hk) = true := by
    simp [isHVert, s2Vert, c1Vert]
  have ht₂_H : isHVert n omega (t2Vert n omega.length hk) = true := by
    simp [isHVert, t2Vert, c1Vert]
  rcases exists_hsegments_of_path_subwalk R₁ hs₁_ne_t₁ hpath₁ hs₁_H ht₁_H with
    ⟨segs₁, hsub₁', hfold₁⟩
  rcases exists_hsegments_of_path_subwalk R₂ hs₂_ne_t₂ hpath₂ hs₂_H ht₂_H with
    ⟨segs₂, hsub₂', hfold₂⟩
  have hsub₁ : ∀ s ∈ segs₁, ∀ x ∈ s.walk.support, x ∈ R₁.support :=
    fun s hs => (hsub₁' s hs).support_subset
  have hsub₂ : ∀ s ∈ segs₂, ∀ x ∈ s.walk.support, x ∈ R₂.support :=
    fun s hs => (hsub₂' s hs).support_subset
  have h_tot : xorSum2 deltaSeg segs₁ segs₂ = true := by
    have h_inner : ∀ s₁ : HSegment G omega,
        segs₂.foldr (fun s₂ acc => bne (deltaSeg s₁ s₂) acc) false =
          bne (bne (cmpIdx2 n omega s₁.u (s2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.v (s2Vert n omega.length hk)))
              (bne (cmpIdx2 n omega s₁.u (t2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.v (t2Vert n omega.length hk))) :=
      fun s₁ => hfold₂ (fun y => bne (cmpIdx2 n omega s₁.u y) (cmpIdx2 n omega s₁.v y))
    have h_outer_eq : ∀ s₁ : HSegment G omega,
        bne (bne (cmpIdx2 n omega s₁.u (s2Vert n omega.length hk))
                 (cmpIdx2 n omega s₁.v (s2Vert n omega.length hk)))
            (bne (cmpIdx2 n omega s₁.u (t2Vert n omega.length hk))
                 (cmpIdx2 n omega s₁.v (t2Vert n omega.length hk))) =
          bne (bne (cmpIdx2 n omega s₁.u (s2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.u (t2Vert n omega.length hk)))
              (bne (cmpIdx2 n omega s₁.v (s2Vert n omega.length hk))
                   (cmpIdx2 n omega s₁.v (t2Vert n omega.length hk))) := by
      intro s₁
      cases cmpIdx2 n omega s₁.u (s2Vert n omega.length hk) <;>
        cases cmpIdx2 n omega s₁.v (s2Vert n omega.length hk) <;>
        cases cmpIdx2 n omega s₁.u (t2Vert n omega.length hk) <;>
        cases cmpIdx2 n omega s₁.v (t2Vert n omega.length hk) <;> rfl
    unfold xorSum2
    simp only [h_inner, h_outer_eq]
    rw [hfold₁ (fun x => bne (cmpIdx2 n omega x (s2Vert n omega.length hk))
                             (cmpIdx2 n omega x (t2Vert n omega.length hk)))]
    have hi_s1 : idx2 n omega (s1Vert n omega.length hk) = 2 * (omega.length - 2) := by
      simp [idx2, posH, s1Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 0 < omega.length)]
    have hi_t1 : idx2 n omega (t1Vert n omega.length hk) = 0 := by
      simp [idx2, posH, t1Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 2 < omega.length)]
    have hi_s2 : idx2 n omega (s2Vert n omega.length hk) = 2 * (omega.length - 1) := by
      simp [idx2, posH, s2Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 1 < omega.length)]
      omega
    have hi_t2 : idx2 n omega (t2Vert n omega.length hk) = 2 := by
      simp [idx2, posH, t2Vert, c1Vert,
        distFrom2_eq_if (by omega : 2 ≤ omega.length) (by omega : 3 < omega.length)]
    simp only [cmpIdx2, hi_s1, hi_t1, hi_s2, hi_t2]
    have c1 : decide (2 * (omega.length - 2) < 2 * (omega.length - 1)) = true :=
      decide_eq_true (by omega)
    have c2 : decide (2 * (omega.length - 2) < 2) = false :=
      decide_eq_false (by omega)
    have c3 : decide (0 < 2 * (omega.length - 1)) = true :=
      decide_eq_true (by omega)
    have c4 : decide (0 < 2) = true :=
      decide_eq_true (by omega)
    rw [c1, c2, c3, c4]
    rfl
  have h_top1 : xorSum2 (fun s₁ s₂ => isTopSeg s₁ && deltaSeg s₁ s₂) segs₁ segs₂ = false := by
    apply foldr_bne_eq_false_of_forall
    intro s₁ hs₁
    rw [foldr_bne_and_const]
    by_cases ht1 : isTopSeg s₁ = true
    · rw [ht1, Bool.true_and]
      unfold deltaSeg
      rw [hfold₂ (fun y => bne (cmpIdx2 n omega s₁.u y) (cmpIdx2 n omega s₁.v y))]
      have hno_wrap₁ : ¬ (s2Vert n omega.length hk ∈ s₁.walk.support ∧
                          t1Vert n omega.length hk ∈ s₁.walk.support) :=
        fun ⟨h_in, _⟩ => hdisj (hsub₁ s₁ hs₁ _ h_in) (Walk.start_mem_support R₂)
      have hs₂_ne_u1 : s2Vert n omega.length hk ≠ s₁.u :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.u (Walk.start_mem_support s₁.walk))
          (h ▸ Walk.start_mem_support R₂)
      have hs₂_ne_v1 : s2Vert n omega.length hk ≠ s₁.v :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.v (Walk.end_mem_support s₁.walk))
          (h ▸ Walk.start_mem_support R₂)
      have ht₂_ne_u1 : t2Vert n omega.length hk ≠ s₁.u :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.u (Walk.start_mem_support s₁.walk))
          (h ▸ Walk.end_mem_support R₂)
      have ht₂_ne_v1 : t2Vert n omega.length hk ≠ s₁.v :=
        fun h => hdisj (hsub₁ s₁ hs₁ s₁.v (Walk.end_mem_support s₁.walk))
          (h ▸ Walk.end_mem_support R₂)
      have h_s2 := (bne_cmpIdx2_of_isTopSeg hk s₁ ht1 hno_wrap₁
        (by simp [s2Vert, c1Vert]) hs₂_ne_u1 hs₂_ne_v1).1
      have h_t2 := (bne_cmpIdx2_of_isTopSeg hk s₁ ht1 hno_wrap₁
        (by simp [t2Vert, c1Vert]) ht₂_ne_u1 ht₂_ne_v1).1
      rw [h_s2, h_t2]
      rfl
    · simp only [Bool.not_eq_true] at ht1
      simp [ht1]
  have h_top2 : xorSum2 (fun s₁ s₂ => isTopSeg s₂ && deltaSeg s₁ s₂) segs₁ segs₂ = false := by
    have h_swap : ∀ (L₂ : List (HSegment G omega)),
        (∀ s₂ ∈ L₂, s₂ ∈ segs₂) →
        xorSum2 (fun s₁ s₂ => isTopSeg s₂ && deltaSeg s₁ s₂) segs₁ L₂ = false := by
      intro L₂ hsubL₂
      induction L₂ with
      | nil =>
        unfold xorSum2
        exact foldr_bne_eq_false_of_forall _ _ (fun _ _ => rfl)
      | cons s₂ rest ih =>
        have h_eq : xorSum2 (fun s₁ b => isTopSeg b && deltaSeg s₁ b) segs₁ (s₂ :: rest) =
            bne (segs₁.foldr (fun s₁ acc => bne (isTopSeg s₂ && deltaSeg s₁ s₂) acc) false)
                (xorSum2 (fun s₁ b => isTopSeg b && deltaSeg s₁ b) segs₁ rest) := by
          unfold xorSum2
          simp only [List.foldr_cons]
          exact foldr_bne_bne _ _ segs₁
        rw [h_eq, ih (fun b hb => hsubL₂ b (List.mem_cons_of_mem _ hb)), Bool.bne_false]
        rw [foldr_bne_and_const]
        by_cases ht2 : isTopSeg s₂ = true
        · rw [ht2, Bool.true_and]
          have h_symm_fold :
              segs₁.foldr (fun s₁ acc => bne (deltaSeg s₁ s₂) acc) false =
                segs₁.foldr (fun s₁ acc =>
                  bne (bne (bne (cmpIdx2 n omega s₁.u s₂.u) (cmpIdx2 n omega s₁.u s₂.v))
                           (bne (cmpIdx2 n omega s₁.v s₂.u) (cmpIdx2 n omega s₁.v s₂.v))) acc) false := by
            congr 1; funext s₁ acc; rw [deltaSeg_symm_form]
          rw [h_symm_fold, hfold₁ (fun x => bne (cmpIdx2 n omega x s₂.u) (cmpIdx2 n omega x s₂.v))]
          have hs₂_mem : s₂ ∈ segs₂ := hsubL₂ s₂ List.mem_cons_self
          have hno_wrap₂ : ¬ (s2Vert n omega.length hk ∈ s₂.walk.support ∧
                              t1Vert n omega.length hk ∈ s₂.walk.support) :=
            fun ⟨_, h_in⟩ => hdisj (Walk.end_mem_support R₁) (hsub₂ s₂ hs₂_mem _ h_in)
          have hs₁_ne_u2 : s1Vert n omega.length hk ≠ s₂.u :=
            fun h => hdisj (Walk.start_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.u (Walk.start_mem_support s₂.walk))
          have hs₁_ne_v2 : s1Vert n omega.length hk ≠ s₂.v :=
            fun h => hdisj (Walk.start_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.v (Walk.end_mem_support s₂.walk))
          have ht₁_ne_u2 : t1Vert n omega.length hk ≠ s₂.u :=
            fun h => hdisj (Walk.end_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.u (Walk.start_mem_support s₂.walk))
          have ht₁_ne_v2 : t1Vert n omega.length hk ≠ s₂.v :=
            fun h => hdisj (Walk.end_mem_support R₁)
              (h ▸ hsub₂ s₂ hs₂_mem s₂.v (Walk.end_mem_support s₂.walk))
          have h_s1 := (bne_cmpIdx2_of_isTopSeg hk s₂ ht2 hno_wrap₂
            (by simp [s1Vert, c1Vert]) hs₁_ne_u2 hs₁_ne_v2).2
          have h_t1 := (bne_cmpIdx2_of_isTopSeg hk s₂ ht2 hno_wrap₂
            (by simp [t1Vert, c1Vert]) ht₁_ne_u2 ht₁_ne_v2).2
          rw [h_s1, h_t1]
          rfl
        · simp only [Bool.not_eq_true] at ht2
          simp [ht2]
    exact h_swap segs₂ (fun _ h => h)
  have h_bot_sum : xorSum2 (fun s₁ s₂ => isBotSeg s₁ && isBotSeg s₂ && deltaSeg s₁ s₂) segs₁ segs₂ = true := by
    have h_congr : xorSum2 deltaSeg segs₁ segs₂ =
        xorSum2 (fun s₁ s₂ =>
          bne (bne (isTopSeg s₁ && deltaSeg s₁ s₂) (isTopSeg s₂ && deltaSeg s₁ s₂))
              (isBotSeg s₁ && isBotSeg s₂ && deltaSeg s₁ s₂)) segs₁ segs₂ := by
      apply xorSum2_congr_on
      intro s₁ hs₁ s₂ hs₂
      have hdisj_s : List.Disjoint s₁.walk.support s₂.walk.support :=
        fun x hx₁ hx₂ => hdisj (hsub₁ s₁ hs₁ x hx₁) (hsub₂ s₂ hs₂ x hx₂)
      have hno_wrap₁ : ¬ (s2Vert n omega.length hk ∈ s₁.walk.support ∧
                          t1Vert n omega.length hk ∈ s₁.walk.support) :=
        fun ⟨h_in, _⟩ => hdisj (hsub₁ s₁ hs₁ _ h_in) (Walk.start_mem_support R₂)
      exact deltaSeg_decomp_pointwise hnodup hk s₁ s₂ hdisj_s hno_wrap₁
    rw [h_congr, xorSum2_bne, xorSum2_bne, h_top1, h_top2] at h_tot
    simpa using h_tot
  rcases xorSum2_eq_true_implies_exists _ segs₁ segs₂ h_bot_sum with ⟨s₁, hs₁, s₂, hs₂, h_both⟩
  simp only [Bool.and_eq_true] at h_both
  rcases h_both with ⟨⟨hb1, hb2⟩, hdel⟩
  simp only [isBotSeg, decide_eq_true_eq] at hb1 hb2
  have ha0_1 : isHVert n omega (R₁.support[0]'(by rw [Walk.length_support]; omega)) = true := by
    rw [getElem_support_zero]; exact hs₁_H
  have ha0_2 : isHVert n omega (R₂.support[0]'(by rw [Walk.length_support]; omega)) = true := by
    rw [getElem_support_zero]; exact hs₂_H
  rcases subwalk_hsegment_prevH R₁ hpath₁ ha0_1 s₁ (hsub₁' s₁ hs₁) with
    ⟨k₁, hk₁_lt, _, hprev1_lt, hget_u₁, hget_v₁, _⟩
  rcases subwalk_hsegment_prevH R₂ hpath₂ ha0_2 s₂ (hsub₂' s₂ hs₂) with
    ⟨k₂, hk₂_lt, _, hprev2_lt, hget_u₂, hget_v₂, _⟩
  refine ⟨k₁, hk₁_lt, k₂, hk₂_lt, ?_⟩
  have hgetD_a₁ : (R₁.support.map Fin.val).getD (prevH n omega R₁.support k₁) 0 = s₁.u.1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Walk.length_support]; omega)]
    simp [hget_u₁]
  have hgetD_b₁ : (R₁.support.map Fin.val).getD (k₁ + 1) 0 = s₁.v.1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Walk.length_support]; omega)]
    simp [hget_v₁]
  have hgetD_a₂ : (R₂.support.map Fin.val).getD (prevH n omega R₂.support k₂) 0 = s₂.u.1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Walk.length_support]; omega)]
    simp [hget_u₂]
  have hgetD_b₂ : (R₂.support.map Fin.val).getD (k₂ + 1) 0 = s₂.v.1 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Walk.length_support]; omega)]
    simp [hget_v₂]
  dsimp [segPairTestVal]
  rw [hgetD_a₁, hgetD_b₁, hgetD_a₂, hgetD_b₂]
  have hp₁ : 0 < omegaPosVal n omega s₁.u.1 := (omegaPosVal_pos_iff s₁.u).mpr ⟨hb1.1, s₁.hu⟩
  have hp₂ : 0 < omegaPosVal n omega s₁.v.1 := (omegaPosVal_pos_iff s₁.v).mpr ⟨hb1.2, s₁.hv⟩
  have hq₁ : 0 < omegaPosVal n omega s₂.u.1 := (omegaPosVal_pos_iff s₂.u).mpr ⟨hb2.1, s₂.hu⟩
  have hq₂ : 0 < omegaPosVal n omega s₂.v.1 := (omegaPosVal_pos_iff s₂.v).mpr ⟨hb2.2, s₂.hv⟩
  simp [hp₁, hp₂, hq₁, hq₂,
    deltaPosVal_eq_deltaSeg s₁ s₂ hb1.1 hb1.2 hb2.1 hb2.2, hdel]

theorem crossWitness_of_isGoodSegPair {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (hnodup : omega.Nodup) (hk : 4 ≤ omega.length)
    {x₁ y₁ x₂ y₂ : Fin (n + omega.length)}
    {R₁ : (auxGraph81 G omega).Walk x₁ y₁}
    {R₂ : (auxGraph81 G omega).Walk x₂ y₂}
    (hdisj : List.Disjoint R₁.support R₂.support)
    {a₁ b₁ a₂ b₂ : ℕ}
    (hgood : IsGoodSegPair R₁ R₂ a₁ b₁ a₂ b₂) :
    ∃ w : CrossWitness G omega,
      w.IsValid ∧
      w.P.support.length = b₁ + 1 - a₁ ∧
      w.Q.support.length = b₂ + 1 - a₂ ∧
      w.P.support.map Fin.val = ((R₁.support.map Fin.val).drop a₁).take (b₁ + 1 - a₁) ∧
      w.Q.support.map Fin.val = ((R₂.support.map Fin.val).drop a₂).take (b₂ + 1 - a₂) := by
  rcases hgood with ⟨s₁, s₂, ha₁_lt, hb₁_lt, ha₂_lt, hb₂_lt,
    hsub₁, hsub₂, hslice₁, hslice₂, hb1, hb2, hdel⟩
  simp only [isBotSeg, decide_eq_true_eq] at hb1 hb2
  have hdisj_s : List.Disjoint s₁.walk.support s₂.walk.support :=
    fun x hx₁ hx₂ => hdisj (hsub₁.support_subset x hx₁) (hsub₂.support_subset x hx₂)
  have hcross := crosses_of_deltaSeg_bot hk s₁ s₂ hdisj_s hb1.1 hb1.2 hb2.1 hb2.2 hdel
  have hno_c2_1 := hcross.not_adj_c2 hnodup hk
  have hno_c2_2 := hcross.symm_pq.not_adj_c2 hnodup hk
  let P := botSegToGPath hk s₁ hb1.1 hb1.2 hno_c2_1
  let Q := botSegToGPath hk s₂ hb2.1 hb2.2 hno_c2_2
  have hP_map : P.support.map Fin.val = ((R₁.support.map Fin.val).drop a₁).take (b₁ + 1 - a₁) := by
    have h1 : (P.support.map (inGVert omega.length)).map Fin.val = s₁.walk.support.map Fin.val := by
      congr 1
      exact map_support_projWalkToG s₁.walk _ _
    simp only [List.map_map, Function.comp_def, inGVert] at h1
    rw [h1, ← hslice₁, List.map_take, List.map_drop]
  have hQ_map : Q.support.map Fin.val = ((R₂.support.map Fin.val).drop a₂).take (b₂ + 1 - a₂) := by
    have h1 : (Q.support.map (inGVert omega.length)).map Fin.val = s₂.walk.support.map Fin.val := by
      congr 1
      exact map_support_projWalkToG s₂.walk _ _
    simp only [List.map_map, Function.comp_def, inGVert] at h1
    rw [h1, ← hslice₂, List.map_take, List.map_drop]
  have hP_len : P.support.length = b₁ + 1 - a₁ := by
    have := congrArg List.length hP_map
    simp only [List.length_map, List.length_take, List.length_drop] at this
    omega
  have hQ_len : Q.support.length = b₂ + 1 - a₂ := by
    have := congrArg List.length hQ_map
    simp only [List.length_map, List.length_take, List.length_drop] at this
    omega
  refine ⟨⟨⟨s₁.u.1, hb1.1⟩, ⟨s₁.v.1, hb1.2⟩, ⟨s₂.u.1, hb2.1⟩, ⟨s₂.v.1, hb2.2⟩, P, Q⟩,
    ⟨isPath_botSegToGPath hk s₁ hb1.1 hb1.2 hno_c2_1,
     isPath_botSegToGPath hk s₂ hb2.1 hb2.2 hno_c2_2,
     fun u huP huQ => ?_, hcross⟩,
    hP_len, hQ_len, hP_map, hQ_map⟩
  have hx₁ : inGVert omega.length u ∈ s₁.walk.support :=
    mem_support_of_mem_botSegToGPath hk s₁ hb1.1 hb1.2 hno_c2_1 huP
  have hx₂ : inGVert omega.length u ∈ s₂.walk.support :=
    mem_support_of_mem_botSegToGPath hk s₂ hb2.1 hb2.2 hno_c2_2 huQ
  exact hdisj (hsub₁.support_subset _ hx₁) (hsub₂.support_subset _ hx₂)

end GraphMinor.Compute
